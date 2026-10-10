import OAI.Geometry.PlaneColoring.GraphRealization

namespace OAI

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
structure MarkedDisk where
  center : ℂ
  radius : ℝ
  core : Bool
namespace MarkedDisk
def ball (d : MarkedDisk) : Set ℂ := Metric.ball d.center d.radius
def closedBall (d : MarkedDisk) : Set ℂ := Metric.closedBall d.center d.radius
def noncoreCost (d : MarkedDisk) : ℝ := if d.core then 0 else d.radius
def Valid (L : Set ℂ) (d : MarkedDisk) : Prop :=
  0<d.radius ∧ (d.core=true → ∃x∈L,x∈d.ball)

lemma merge {a b : MarkedDisk} {L : Set ℂ} (ha : a.Valid L) (hb : b.Valid L)
    (hab : ¬Disjoint a.closedBall b.closedBall) {η : ℝ} (hη : 0<η) :
    ∃d : MarkedDisk, d.Valid L ∧ a.closedBall⊆d.ball ∧ b.closedBall⊆d.ball ∧
      d.radius≤a.radius+b.radius+η ∧ d.noncoreCost≤a.noncoreCost+b.noncoreCost+η ∧ d.core=(a.core || b.core) := by
  obtain ⟨z,hza,hzb⟩ := Set.not_disjoint_iff.mp hab
  have hd : dist a.center b.center≤a.radius+b.radius :=
    (dist_triangle a.center z b.center).trans (add_le_add (by simpa [closedBall,dist_comm] using hza) hzb)
  let t : ℝ := b.radius/(a.radius+b.radius)
  have hrs : 0<a.radius+b.radius := add_pos ha.1 hb.1
  have ht0 : 0≤t := (div_pos hb.1 hrs).le
  have ht1 : t≤1 := (div_le_one hrs).mpr (by linarith [ha.1])
  let c := AffineMap.lineMap a.center b.center t
  have hca : dist a.center c≤b.radius := by
    rw [dist_left_lineMap,Real.norm_of_nonneg ht0]
    calc t*dist a.center b.center ≤ t*(a.radius+b.radius) := mul_le_mul_of_nonneg_left hd ht0
         _ = b.radius := by dsimp [t]; field_simp
  have hcb : dist b.center c≤a.radius := by
    rw [dist_right_lineMap,Real.norm_of_nonneg (sub_nonneg.mpr ht1)]
    calc (1-t)*dist a.center b.center ≤ (1-t)*(a.radius+b.radius) :=
            mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr ht1)
         _ = a.radius := by dsimp [t]; field_simp; ring
  let d : MarkedDisk := ⟨c,a.radius+b.radius+η,a.core || b.core⟩
  have hA : a.closedBall⊆d.ball := by
    intro q hq
    have hq' : dist q a.center≤a.radius := hq
    change dist q c<a.radius+b.radius+η
    exact lt_of_le_of_lt (dist_triangle q a.center c) (by linarith)
  have hB : b.closedBall⊆d.ball := by
    intro q hq
    have hq' : dist q b.center≤b.radius := hq
    change dist q c<a.radius+b.radius+η
    exact lt_of_le_of_lt (dist_triangle q b.center c) (by linarith)
  refine ⟨d,⟨by dsimp [d]; linarith,?_⟩,hA,hB,le_refl _,?_,rfl⟩
  · intro hc
    have hc' : a.core=true ∨ b.core=true := by cases hca : a.core <;> cases hcb : b.core <;> simp_all [d]
    rcases hc' with hh|hh
    · obtain ⟨x,hx,hxa⟩ := ha.2 hh
      exact ⟨x,hx,hA (Metric.ball_subset_closedBall hxa)⟩
    · obtain ⟨x,hx,hxb⟩ := hb.2 hh
      exact ⟨x,hx,hB (Metric.ball_subset_closedBall hxb)⟩
  · dsimp [noncoreCost,d]
    cases a.core <;> cases b.core <;> simp <;> linarith [ha.1,hb.1]
end MarkedDisk
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
namespace MarkedDisk
lemma erased_pair_sum {D : Type*} [DecidableEq D] (S : Finset D) {a b : D}
    (ha : a∈S) (hb : b∈S) (hab : a≠b) (f : D → ℝ) :
    (∑x∈(S.erase a).erase b,f x)+f a+f b=∑x∈S,f x := by
  have h1 := Finset.sum_erase_add S f ha
  have h2 := Finset.sum_erase_add (S.erase a) f (Finset.mem_erase.mpr ⟨hab.symm,hb⟩)
  linarith
lemma merge_sum_bound {D : Type*} [DecidableEq D] (S : Finset D) {a b d : D}
    (ha : a∈S) (hb : b∈S) (hab : a≠b) (f : D → ℝ) {η : ℝ}
    (hd0 : 0≤f d) (hd : f d≤f a+f b+η) :
    (∑x∈insert d ((S.erase a).erase b),f x)≤(∑x∈S,f x)+η := by
  have hs := erased_pair_sum S ha hb hab f
  by_cases hmem : d∈(S.erase a).erase b
  · rw [Finset.insert_eq_of_mem hmem]
    linarith
  · rw [Finset.sum_insert hmem]
    linarith

/-- Finite disk merging with separate total and non-core radius budgets. Strict
containment at merges, and the retained core witness, are both included. -/
theorem separate (S : Finset MarkedDisk) {L : Set ℂ} (hS : ∀d∈S,d.Valid L)
    {η : ℝ} (hη : 0<η) : ∃T : Finset MarkedDisk,
      (∀d∈T,d.Valid L) ∧ (T : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall) ∧
      (∀d∈S,∃e∈T,d.ball⊆e.ball ∧ (d.core=true → e.core=true)) ∧
      (∑d∈T,d.radius)<(∑d∈S,d.radius)+η ∧
      (∑d∈T,d.noncoreCost)<(∑d∈S,d.noncoreCost)+η := by
  suffices hh : ∀n : ℕ, ∀S : Finset MarkedDisk, S.card=n →
      (∀d∈S,d.Valid L) → ∀η : ℝ,0<η → ∃T : Finset MarkedDisk,
      (∀d∈T,d.Valid L) ∧ (T : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall) ∧
      (∀d∈S,∃e∈T,d.ball⊆e.ball ∧ (d.core=true → e.core=true)) ∧
      (∑d∈T,d.radius)<(∑d∈S,d.radius)+η ∧
      (∑d∈T,d.noncoreCost)<(∑d∈S,d.noncoreCost)+η from hh _ S rfl hS η hη
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hn hS η hη
    by_cases hp : (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall)
    · exact ⟨S,hS,hp,fun d hd => ⟨d,hd,Subset.rfl,fun h => h⟩,
        lt_add_of_pos_right _ hη,lt_add_of_pos_right _ hη⟩
    · simp only [Set.Pairwise,Finset.mem_coe] at hp
      push Not at hp
      obtain ⟨a,ha,b,hb,hab,hd⟩ := hp
      obtain ⟨d,hdv,hda,hdb,hdr,hdc,hdcore⟩ := merge (hS a ha) (hS b hb) hd (half_pos hη)
      let R := (S.erase a).erase b
      let S' := insert d R
      have hR : ∀e∈R,e∈S := by intro e he; exact (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).2
      have hS' : ∀e∈S',e.Valid L := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl|he
        · exact hdv
        · exact hS e (hR e he)
      have hcard : S'.card<n := by
        have hc₁ := Finset.card_erase_add_one ha
        have hc₂ := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hab.symm,hb⟩)
        have hc₃ := Finset.card_insert_le d R
        change R.card+1=(S.erase a).card at hc₂
        dsimp only [S']
        omega
      obtain ⟨T,hT,hdis,hcov,hr,hc⟩ := ih S'.card hcard S' rfl hS' (η/2) (half_pos hη)
      refine ⟨T,hT,hdis,?_,?_,?_⟩
      · intro e he
        have he' : ∃f∈S',e.ball⊆f.ball ∧ (e.core=true → f.core=true) := by
          by_cases hea : e=a
          · subst e
            refine ⟨d,Finset.mem_insert_self _ _,fun _ hq => hda (Metric.ball_subset_closedBall hq),?_⟩
            intro ha
            rw [hdcore,ha]
            simp
          · by_cases heb : e=b
            · subst e
              refine ⟨d,Finset.mem_insert_self _ _,fun _ hq => hdb (Metric.ball_subset_closedBall hq),?_⟩
              intro hb
              rw [hdcore,hb]
              simp
            · exact ⟨e,Finset.mem_insert_of_mem (by simp [R,he,hea,heb]),Subset.rfl,fun h => h⟩
        obtain ⟨f,hf,hef,hcore⟩ := he'
        obtain ⟨g,hg,hfg,hcore'⟩ := hcov f hf
        exact ⟨g,hg,hef.trans hfg,fun hec => hcore' (hcore hec)⟩
      · have hb' := merge_sum_bound S ha hb hab radius hdv.1.le hdr
        change (∑x∈S',x.radius)≤(∑x∈S,x.radius)+η/2 at hb'
        linarith
      · have hdc0 : 0≤d.noncoreCost := by unfold noncoreCost; split_ifs <;> linarith [hdv.1]
        have hb' := merge_sum_bound S ha hb hab noncoreCost hdc0 hdc
        change (∑x∈S',x.noncoreCost)≤(∑x∈S,x.noncoreCost)+η/2 at hb'
        linarith
end MarkedDisk
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
lemma cone_dist (c : ℂ) {r : ℝ} (z : Metric.sphere c r) (t : unitInterval) :
    dist ((1-t.val) • (z.val-c)+c) c=(1-t.val)*r := by
  rw [dist_eq_norm,add_sub_cancel_right,norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr t.property.2)]
  rw [←dist_eq_norm,z.property]
def diskCone (c : ℂ) {r : ℝ} (hr : 0<r) :
    C(unitInterval × Metric.sphere c r, Metric.closedBall c r) where
  toFun p := ⟨(1-p.1.val) • (p.2.val-c)+c,by
    change dist ((1-p.1.val) • (p.2.val-c)+c) c≤r
    rw [cone_dist]
    nlinarith [p.1.property.1]⟩
  continuous_toFun := (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    ((continuous_subtype_val.comp continuous_snd).sub continuous_const)).add continuous_const).subtype_mk _
lemma diskCone_surjective (c : ℂ) {r : ℝ} (hr : 0<r) : Function.Surjective (diskCone c hr) := by
  intro q
  by_cases hq : q.val=c
  · obtain ⟨z,hz⟩ := (NormedSpace.sphere_nonempty (x:=c)).mpr hr.le
    refine ⟨(1,⟨z,hz⟩),?_⟩
    apply Subtype.ext
    simpa [diskCone] using hq.symm
  · let d := dist q.val c
    have hd : 0<d := dist_pos.mpr hq
    have hdr : d≤r := q.property
    let t : unitInterval := ⟨1-d/r,⟨by rw [sub_nonneg,div_le_one hr]; exact hdr,
      by linarith [div_nonneg hd.le hr.le]⟩⟩
    have hz : (r/d) • (q.val-c)+c∈Metric.sphere c r := by
      rw [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_right,norm_smul,Real.norm_of_nonneg (div_pos hr hd).le]
      rw [←dist_eq_norm]
      change r/d*d=r
      field_simp
    refine ⟨(t,⟨(r/d) • (q.val-c)+c,hz⟩),?_⟩
    apply Subtype.ext
    change (1-(1-d/r)) • (((r/d) • (q.val-c)+c)-c)+c=q.val
    rw [add_sub_cancel_right,smul_smul]
    have he : (1-(1-d/r))*(r/d)=1 := by field_simp; ring
    rw [he,one_smul,sub_add_cancel]
lemma diskCone_fiber (c : ℂ) {r : ℝ} (hr : 0<r)
    {p q : unitInterval × Metric.sphere c r} (he : diskCone c hr p=diskCone c hr q) :
    p=q ∨ (p.1=1 ∧ q.1=1) := by
  have hv := congrArg Subtype.val he
  have hd := congrArg (fun x : Metric.closedBall c r => dist x.val c) he
  change dist ((1-p.1.val) • (p.2.val-c)+c) c=dist ((1-q.1.val) • (q.2.val-c)+c) c at hd
  rw [cone_dist,cone_dist] at hd
  have ht : p.1=q.1 := Subtype.ext (by nlinarith)
  by_cases h1 : p.1=1
  · exact Or.inr ⟨h1,ht.symm.trans h1⟩
  · left
    apply Prod.ext ht
    have hneq : 1-p.1.val≠0 := by
      intro hh
      apply h1
      apply Subtype.ext
      change p.1.val=1
      linarith
    apply Subtype.ext
    change (1-p.1.val) • (p.2.val-c)+c=(1-q.1.val) • (q.2.val-c)+c at hv
    rw [←ht] at hv
    have hsub : p.2.val-c=q.2.val-c := (smul_right_injective ℂ hneq (add_right_cancel hv))
    exact sub_left_injective hsub

/-- A contraction genuinely extends arbitrary continuous sphere data across a disk. -/
theorem contractible_disk_extension {Y : Type u} [TopologicalSpace Y] [ContractibleSpace Y]
    (c : ℂ) {r : ℝ} (hr : 0<r) (f : C(Metric.sphere c r,Y)) :
    ∃g : C(Metric.closedBall c r,Y), ∀z : Metric.sphere c r,
      g ⟨z.val,Metric.sphere_subset_closedBall z.property⟩=f z := by
  let : CompactSpace (Metric.sphere c r) := isCompact_iff_compactSpace.mp (isCompact_sphere c r)
  obtain ⟨a,⟨H⟩⟩ := id_nullhomotopic Y
  let F : C(unitInterval × Metric.sphere c r,Y) := H.toContinuousMap.comp
    (ContinuousMap.prodMk ContinuousMap.fst (f.comp ContinuousMap.snd))
  have hf : Function.FactorsThrough F (diskCone c hr) := by
    intro p q he
    rcases diskCone_fiber c hr he with rfl|⟨hp,hq⟩
    · rfl
    · change H (p.1,f p.2)=H (q.1,f q.2)
      rw [hp,hq]
      exact (H.map_one_left (f p.2)).trans (H.map_one_left (f q.2)).symm
  have hquot := IsQuotientMap.of_surjective_continuous (diskCone_surjective c hr) (diskCone c hr).continuous
  refine ⟨hquot.lift F hf,?_⟩
  intro z
  have he : diskCone c hr (0,z)=⟨z.val,Metric.sphere_subset_closedBall z.property⟩ := by
    apply Subtype.ext
    simp [diskCone]
  rw [←he]
  have hh := DFunLike.congr_fun (hquot.lift_comp F hf) (0,z)
  change (hquot.lift F hf) (diskCone c hr (0,z))=H (0,f z) at hh
  exact hh.trans (H.map_zero_left _)
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
universe u
namespace EuclideanFiveColor
/-- Linear transfer of a leaf coordinate along its unique incident edge. -/
def graphLeafMove {V : Type u} (v w : V) (t : ℝ) (p : V → ℝ) : V → ℝ :=
  p+(t*p v) • (graphVertex w-graphVertex v)
lemma continuous_graphLeafMove {V : Type u} (v w : V) :
    Continuous (fun tp : ℝ × (V → ℝ) => graphLeafMove v w tp.1 tp.2) := by
  apply continuous_pi
  intro i
  change Continuous (fun tp : ℝ × (V → ℝ) => tp.2 i + (tp.1 * tp.2 v) * (graphVertex w i-graphVertex v i))
  fun_prop
@[simp] lemma graphLeafMove_zero {V : Type u} (v w : V) (p : V → ℝ) : graphLeafMove v w 0 p=p := by
  simp [graphLeafMove]
lemma graphLeafMove_of_zero {V : Type u} (v w : V) (p : V → ℝ) (hp : p v=0) (t : ℝ) :
    graphLeafMove v w t p=p := by simp [graphLeafMove,hp]
lemma graphLeafMove_edge {V : Type u} {v w : V} (hvw : v≠w) (t s : ℝ) :
    graphLeafMove v w t (graphEdgePoint v w s)=graphEdgePoint v w (s+t*(1-s)) := by
  ext i
  by_cases hi : i=v
  · subst i; simp [graphLeafMove,graphEdgePoint,graphVertex,hvw]; ring
  · by_cases hj : i=w
    · subst i; simp [graphLeafMove,graphEdgePoint,graphVertex,hvw,Ne.symm hvw]
    · simp [graphLeafMove,graphEdgePoint,graphVertex,hi,hj,hvw]
lemma graphLeafMove_vertex {V : Type u} {v w : V} (hvw : v≠w) (t : ℝ) :
    graphLeafMove v w t (graphVertex v)=graphEdgePoint v w t := by
  simpa using graphLeafMove_edge hvw t 0
lemma graphLeafMove_mem {V : Type u} {G : SimpleGraph V} {v w : V}
    (hvw : G.Adj v w) (hleaf : ∀i,G.Adj v i → i=w)
    {p : V → ℝ} (hp : p∈graphRealization G) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    graphLeafMove v w t p∈graphRealization G := by
  obtain ⟨a,b,hab,s,hs,rfl⟩ := hp
  by_cases ha : a=v
  · subst a
    by_cases hb : b=v
    · subst b
      rw [graphEdgePoint_self,graphLeafMove_vertex hvw.ne]
      exact graphEdgePoint_mem (.inr hvw) ht
    · have : b=w := hleaf b (hab.resolve_left (Ne.symm hb))
      subst b
      rw [graphLeafMove_edge hvw.ne]
      apply graphEdgePoint_mem (.inr hvw)
      constructor
      · nlinarith [hs.1,hs.2,ht.1,ht.2]
      · nlinarith [hs.1,hs.2,ht.1,ht.2]
  · by_cases hb : b=v
    · subst b
      have haw : a=w := hleaf a ((hab.resolve_left ha).symm)
      subst a
      rw [graphEdgePoint_swap,graphLeafMove_edge hvw.ne]
      apply graphEdgePoint_mem (.inr hvw)
      constructor <;> nlinarith [hs.1,hs.2,ht.1,ht.2]
    · rw [graphLeafMove_of_zero v w _ (by simp [graphEdgePoint,graphVertex,Ne.symm ha,Ne.symm hb])]
      exact graphEdgePoint_mem hab hs
lemma graphLeafMove_one_at {V : Type u} {v w : V} (hvw : v≠w) (p : V → ℝ) :
    graphLeafMove v w 1 p v=0 := by
  simp [graphLeafMove,graphVertex,hvw]

def graphDrop {V : Type u} (v : V) (p : V → ℝ) : {i : V // i≠v} → ℝ := fun i => p i

def graphLift {V : Type u} (v : V) (p : {i : V // i≠v} → ℝ) : V → ℝ :=
  fun i => if hi : i≠v then p ⟨i,hi⟩ else 0
lemma continuous_graphDrop {V : Type u} (v : V) : Continuous (graphDrop v) :=
  continuous_pi fun i => continuous_apply i.val
lemma continuous_graphLift {V : Type u} (v : V) : Continuous (graphLift v) := by
  apply continuous_pi
  intro i
  by_cases hi : i≠v
  · simpa [graphLift,hi] using (continuous_apply (⟨i,hi⟩ : {i : V // i≠v}))
  · simpa [graphLift,hi] using (continuous_const : Continuous (fun _ : ({i : V // i≠v} → ℝ) => (0:ℝ)))
@[simp] lemma graphLift_drop {V : Type u} (v : V) (p : V → ℝ) (hp : p v=0) :
    graphLift v (graphDrop v p)=p := by
  ext i
  by_cases hi : i=v
  · subst i; simp [graphLift,hp]
  · simp [graphLift,graphDrop,hi]
@[simp] lemma graphDrop_lift {V : Type u} (v : V) (p : {i : V // i≠v} → ℝ) :
    graphDrop v (graphLift v p)=p := by
  ext i; simp [graphDrop,graphLift,i.property]
lemma graphDrop_vertex {V : Type u} {v a : V} (ha : a≠v) :
    graphDrop v (graphVertex a)=graphVertex (⟨a,ha⟩ : {i : V // i≠v}) := by
  ext i; simp [graphDrop,graphVertex,Subtype.ext_iff]
lemma graphDrop_edge {V : Type u} {v a b : V} (ha : a≠v) (hb : b≠v) (t : ℝ) :
    graphDrop v (graphEdgePoint a b t)=graphEdgePoint (⟨a,ha⟩ : {i : V // i≠v}) ⟨b,hb⟩ t := by
  ext i; simp [graphDrop,graphEdgePoint,graphVertex,Subtype.ext_iff]
lemma graphLift_vertex {V : Type u} (v : V) (a : {i : V // i≠v}) :
    graphLift v (graphVertex a)=graphVertex a.val := by
  ext i
  by_cases hi : i=v
  · subst i; simp [graphLift,graphVertex,Ne.symm a.property]
  · simp [graphLift,graphVertex,hi,Subtype.ext_iff]
lemma graphLift_edge {V : Type u} (v : V) (a b : {i : V // i≠v}) (t : ℝ) :
    graphLift v (graphEdgePoint a b t)=graphEdgePoint a.val b.val t := by
  ext i
  by_cases hi : i=v
  · subst i; simp [graphLift,graphEdgePoint,graphVertex,Ne.symm a.property,Ne.symm b.property]
  · simp [graphLift,graphEdgePoint,graphVertex,hi,Subtype.ext_iff]
lemma graphLift_mem {V : Type u} {G : SimpleGraph V} (v : V) {p : {i : V // i≠v} → ℝ}
    (hp : p∈graphRealization (G.induce {i | i≠v})) : graphLift v p∈graphRealization G := by
  obtain ⟨a,b,hab,t,ht,rfl⟩ := hp
  rw [graphLift_edge]
  exact graphEdgePoint_mem (hab.imp (congrArg Subtype.val) id) ht
lemma graphDrop_mem {V : Type u} {G : SimpleGraph V} (v : V) {p : V → ℝ}
    (hp : p∈graphRealization G) (hz : p v=0) :
    graphDrop v p∈graphRealization (G.induce {i | i≠v}) := by
  obtain ⟨a,b,hab,t,ht,rfl⟩ := hp
  by_cases ha : a=v
  · subst a
    by_cases hb : b=v
    · subst b
      simp [graphEdgePoint,graphVertex] at hz
    · have he : t=1 := by
        have : 1-t=0 := by simpa [graphEdgePoint,graphVertex,Ne.symm hb] using hz
        linarith
      subst t
      rw [graphEdgePoint_one,graphDrop_vertex hb]
      exact graphVertex_mem _ _
  · by_cases hb : b=v
    · subst b
      have he : t=0 := by simpa [graphEdgePoint,graphVertex,Ne.symm ha] using hz
      subst t
      rw [graphEdgePoint_zero,graphDrop_vertex ha]
      exact graphVertex_mem _ _
    · rw [graphDrop_edge ha hb]
      exact graphEdgePoint_mem (hab.imp (fun h => Subtype.ext h) id) ht
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor

def graphLeafRetraction {V : Type u} {G : SimpleGraph V} {v w : V}
    (hvw : G.Adj v w) (hleaf : ∀i,G.Adj v i → i=w) :
    C(GraphSpace G, GraphSpace (G.induce {i | i≠v})) where
  toFun p := ⟨graphDrop v (graphLeafMove v w 1 p.val),
    graphDrop_mem v (graphLeafMove_mem hvw hleaf p.property (by norm_num))
      (graphLeafMove_one_at hvw.ne p.val)⟩
  continuous_toFun := (continuous_graphDrop v |>.comp
    ((continuous_graphLeafMove v w).comp (continuous_const.prodMk continuous_subtype_val))).subtype_mk _

def graphLeafInclusion {V : Type u} (G : SimpleGraph V) (v : V) :
    C(GraphSpace (G.induce {i | i≠v}), GraphSpace G) where
  toFun p := ⟨graphLift v p.val,graphLift_mem v p.property⟩
  continuous_toFun := ((continuous_graphLift v).comp continuous_subtype_val).subtype_mk _

def graphLeafHomotopy {V : Type u} {G : SimpleGraph V} {v w : V}
    (hvw : G.Adj v w) (hleaf : ∀i,G.Adj v i → i=w) :
    (ContinuousMap.id (GraphSpace G)).Homotopy
      ((graphLeafInclusion G v).comp (graphLeafRetraction hvw hleaf)) where
  toFun tp := ⟨graphLeafMove v w tp.1.val tp.2.val,
    graphLeafMove_mem hvw hleaf tp.2.property tp.1.property⟩
  continuous_toFun := ((continuous_graphLeafMove v w).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left p := by apply Subtype.ext; exact graphLeafMove_zero v w p.val
  map_one_left p := by
    apply Subtype.ext
    exact (graphLift_drop v _ (graphLeafMove_one_at hvw.ne p.val)).symm

private lemma graphTree_contractible_aux (n : ℕ) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), Fintype.card V=n →
      G.IsTree → ContractibleSpace (GraphSpace G) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V inst G hcard hG
    rcases subsingleton_or_nontrivial V with hSS|hNT
    · let := hSS
      obtain ⟨a⟩ := hG.nonempty
      let : Nonempty (GraphSpace G) := ⟨⟨graphVertex a,graphVertex_mem G a⟩⟩
      let : Subsingleton (GraphSpace G) := ⟨fun p q => Subtype.ext (by
        have hp := p.property
        have hq := q.property
        simp only [graphRealization_singleton G a,mem_singleton_iff] at hp hq
        exact hp.trans hq.symm)⟩
      infer_instance
    · let := hNT
      obtain ⟨v,hv⟩ := hG.exists_vert_degree_one_of_nontrivial
      obtain ⟨w,hvw,hleaf⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
      let W := {i : V // i≠v}
      let G' : SimpleGraph W := G.induce {i | i≠v}
      have hs : ({v}ᶜ : Set V)={i | i≠v} := by ext i; simp
      have hconn : G'.Connected := by
        have hh := hG.connected.induce_compl_singleton_of_degree_eq_one hv
        rwa [hs] at hh
      have hac : G'.IsAcyclic := hG.isAcyclic.induce _
      have hlt : Fintype.card W<n := by
        rw [←hcard]
        apply Fintype.card_lt_of_injective_not_surjective (Subtype.val : W → V) Subtype.val_injective
        intro hh
        obtain ⟨i,hi⟩ := hh v
        exact i.property hi
      let : ContractibleSpace (GraphSpace G') := ih _ hlt W G' rfl ⟨hconn,hac⟩
      have hn := ((id_nullhomotopic (GraphSpace G')).comp_left
        (graphLeafRetraction hvw hleaf)).comp_right (graphLeafInclusion G v)
      obtain ⟨a,ha⟩ := hn
      apply (contractible_iff_id_nullhomotopic _).mpr
      refine ⟨a,ContinuousMap.Homotopic.trans ⟨graphLeafHomotopy hvw hleaf⟩ ?_⟩
      simpa only [ContinuousMap.id_comp] using ha

/-- Genuine contraction of the geometric probability-simplex realization of a finite tree. -/
theorem graphTree_contractible {V : Type u} [Fintype V] {G : SimpleGraph V} (hG : G.IsTree) :
    ContractibleSpace (GraphSpace G) := graphTree_contractible_aux _ V G rfl hG
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
/-- Forest-valued boundary data extend through an actual spanning tree inside the
complete graph. Isolated labels and empty edge sets are retained. -/
theorem forest_disk_extension {V : Type u} [Fintype V] [Nonempty V]
    (c : ℂ) {r : ℝ} (hr : 0<r) (f : C(Metric.sphere c r,V → ℝ))
    {G : SimpleGraph V} (hG : G.IsAcyclic) (hf : ∀z,f z∈graphRealization G) :
    ∃g : C(Metric.closedBall c r,GraphSpace (⊤ : SimpleGraph V)), ∀z : Metric.sphere c r,
      (g ⟨z.val,Metric.sphere_subset_closedBall z.property⟩).val=f z := by
  obtain ⟨T,hGT,_,hT⟩ := SimpleGraph.connected_top.exists_isTree_le_of_le_of_isAcyclic
    (show G≤⊤ from le_top) hG
  let : ContractibleSpace (GraphSpace T) := graphTree_contractible hT
  let F : C(Metric.sphere c r,GraphSpace T) := ⟨fun z => ⟨f z,graphRealization_mono hGT (hf z)⟩,
    f.continuous.subtype_mk _⟩
  obtain ⟨g,hg⟩ := contractible_disk_extension c hr F
  let g' : C(Metric.closedBall c r,GraphSpace (⊤ : SimpleGraph V)) :=
    ⟨fun z => ⟨(g z).val,graphRealization_mono le_top (g z).property⟩,
      (continuous_subtype_val.comp g.continuous).subtype_mk _⟩
  exact ⟨g',fun z => congrArg Subtype.val (hg z)⟩
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u v w
namespace EuclideanFiveColor
/-- Finite closed-cover pasting, with the actual glued continuous map. -/
def closedCoverMap {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
    (S : ι → Set X) (hS : ∀i,IsClosed (S i)) (hc : ⋃i,S i=univ)
    (f : ∀i,C(S i,Y))
    (hf : ∀i j x (hi : x∈S i) (hj : x∈S j), f i ⟨x,hi⟩=f j ⟨x,hj⟩) : C(X,Y) where
  toFun := Set.liftCover S (fun i => f i) hf hc
  continuous_toFun := (locallyFinite_of_finite S).continuous hc hS (fun i => by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa +unfoldPartialApp only [Set.domRestrict,Set.liftCover_coe] using (f i).continuous)
@[simp] lemma closedCoverMap_apply {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
    (S : ι → Set X) (hS : ∀i,IsClosed (S i)) (hc : ⋃i,S i=univ)
    (f : ∀i,C(S i,Y))
    (hf : ∀i j x (hi : x∈S i) (hj : x∈S j), f i ⟨x,hi⟩=f j ⟨x,hj⟩)
    {i : ι} (x : S i) : closedCoverMap S hS hc f hf x=f i x := by
  change Set.liftCover S (fun i => f i) hf hc x=f i x
  exact Set.liftCover_coe x
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
def diskHoles (S : Finset MarkedDisk) : Set ℂ := ⋃d∈S,d.ball
def coreHoles (S : Finset MarkedDisk) : Set ℂ := ⋃d∈S,⋃(_ : d.core=true),d.ball
lemma diskHoles_open (S : Finset MarkedDisk) : IsOpen (diskHoles S) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball
lemma coreHoles_open (S : Finset MarkedDisk) : IsOpen (coreHoles S) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball
lemma mem_diskHoles {S : Finset MarkedDisk} {z : ℂ} : z∈diskHoles S ↔ ∃d∈S,z∈d.ball := by
  simp [diskHoles]
lemma mem_coreHoles {S : Finset MarkedDisk} {z : ℂ} : z∈coreHoles S ↔ ∃d∈S,d.core=true ∧ z∈d.ball := by
  simp only [coreHoles,mem_iUnion]
  aesop

/-- Finite closed pasting fills precisely the non-core holes, with actual continuous
tree extensions on their disks and no change outside the original open holes. -/
theorem fill_noncore_disks {V : Type u} [Fintype V] [Nonempty V]
    (Q : Set ℂ) (S : Finset MarkedDisk) (hr : ∀d∈S,0<d.radius)
    (hdis : (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall))
    (f : C(ℂ,V → ℝ))
    (hg : ∀z∈Q,z∉diskHoles S → f z∈graphRealization (⊤ : SimpleGraph V))
    (hb : ∀d∈S,d.core=false → (d.closedBall∩Q).Nonempty →
      ∃G : SimpleGraph V,G.IsAcyclic ∧ ∀z∈Metric.sphere d.center d.radius,f z∈graphRealization G) :
    ∃g : C(↥(Q \ coreHoles S),GraphSpace (⊤ : SimpleGraph V)),
      ∀z : ↥(Q \ coreHoles S),z.val∉diskHoles S → (g z).val=f z.val := by
  let D : Finset MarkedDisk := S.filter fun d => d.core=false ∧ (d.closedBall∩Q).Nonempty
  have hD (d : D) : d.val∈S ∧ d.val.core=false ∧ (d.val.closedBall∩Q).Nonempty :=
    Finset.mem_filter.mp d.property
  have hex (d : D) : ∃g : C(Metric.closedBall d.val.center d.val.radius,GraphSpace (⊤ : SimpleGraph V)),
      ∀z : Metric.sphere d.val.center d.val.radius,
        (g ⟨z.val,Metric.sphere_subset_closedBall z.property⟩).val=f z.val := by
    obtain ⟨G,hG,hf⟩ := hb d.val (hD d).1 (hD d).2.1 (hD d).2.2
    exact forest_disk_extension d.val.center (hr _ (hD d).1) (f.restrict _) hG (fun z => hf z.val z.property)
  choose g hg' using hex
  let X := Q \ coreHoles S
  let Z : Option D → Set X := fun i => match i with
    | none => {z | z.val∉diskHoles S}
    | some d => {z | z.val∈d.val.closedBall}
  have hZ : ∀i,IsClosed (Z i) := by
    intro i
    cases i with
    | none => exact (diskHoles_open S).isClosed_compl.preimage continuous_subtype_val
    | some d => exact Metric.isClosed_closedBall.preimage continuous_subtype_val
  have hcov : ⋃i,Z i=univ := by
    apply iUnion_eq_univ_iff.mpr
    intro z
    by_cases hz : z.val∈diskHoles S
    · obtain ⟨d,hd,hzd⟩ := mem_diskHoles.mp hz
      have hdf : d.core=false := by
        cases he : d.core
        · rfl
        · exact False.elim (z.property.2 (mem_coreHoles.mpr ⟨d,hd,he,hzd⟩))
      let d' : D := ⟨d,Finset.mem_filter.mpr ⟨hd,hdf,⟨z.val,Metric.ball_subset_closedBall hzd,z.property.1⟩⟩⟩
      exact ⟨some d',Metric.ball_subset_closedBall hzd⟩
    · exact ⟨none,hz⟩
  let f₀ : C(Z none,GraphSpace (⊤ : SimpleGraph V)) :=
    ⟨fun z => ⟨f z.val.val,hg z.val.val z.val.property.1 z.property⟩,
      (f.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩
  let ψ (d : D) : C(Z (some d),GraphSpace (⊤ : SimpleGraph V)) :=
    ⟨fun z => g d ⟨z.val.val,z.property⟩,
      (g d).continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
  let φ : ∀i,C(Z i,GraphSpace (⊤ : SimpleGraph V)) := fun i => match i with
    | none => f₀
    | some d => ψ d
  have hbd (d : D) (z : X) (h0 : z∈Z none) (h1 : z∈Z (some d)) :
      f₀ ⟨z,h0⟩=ψ d ⟨z,h1⟩ := by
    have hn : z.val∉d.val.ball := fun hz => h0 (mem_diskHoles.mpr ⟨d.val,(hD d).1,hz⟩)
    have hs : z.val∈Metric.sphere d.val.center d.val.radius := by
      change dist z.val d.val.center=d.val.radius
      exact le_antisymm h1 (le_of_not_gt hn)
    apply Subtype.ext
    exact (hg' d ⟨z.val,hs⟩).symm
  have hφ : ∀i j z (hi : z∈Z i) (hj : z∈Z j),φ i ⟨z,hi⟩=φ j ⟨z,hj⟩ := by
    intro i j z hi hj
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some d => exact hbd d z hi hj
    | some d =>
      cases j with
      | none => exact (hbd d z hj hi).symm
      | some e =>
        by_cases hde : d=e
        · subst e; rfl
        · exact False.elim (Set.disjoint_left.mp (hdis (hD d).1 (hD e).1
            (fun he => hde (Subtype.ext he))) hi hj)
  refine ⟨closedCoverMap Z hZ hcov φ hφ,?_⟩
  intro z hz
  change (closedCoverMap Z hZ hcov φ hφ z).val=f z.val
  rw [closedCoverMap_apply Z hZ hcov φ hφ (i:=none) ⟨z,hz⟩]
  rfl
end EuclideanFiveColor
end

end OAI
