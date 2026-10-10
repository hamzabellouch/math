import Mathlib
import OAI.Analysis.HardSphere.Geometry.StarOffsets

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
namespace HardSphere.Lattice
variable {A : Type*} [AddCommGroup A]

lemma double_avoiding_step (C : Finset Vertex) {x y : Vertex}
    (hx : x∉C) (hy : y∉C) (hxy : nearestStep x y) :
    withinReach nearestStep ((↑(thicken C))ᶜ) (doubleVertex x) (doubleVertex y) := by
  have hpos : ∀ u (i : Fin 3), u∉C → step u i∉C →
      withinReach nearestStep ((↑(thicken C))ᶜ) (doubleVertex u) (doubleVertex (step u i)) := by
    intro u i hu hui
    have hu' : doubleVertex u∉thicken C := by simpa only [double_mem_thicken_iff] using hu
    have hui' : doubleVertex (step u i)∉thicken C := by simpa only [double_mem_thicken_iff] using hui
    have hm := splitPoint_not_thicken C u i hu hui
    have hs : nearestStep (step (doubleVertex u) i) (doubleVertex (step u i)) := by
      rw [double_step]; exact nearestStep_step _ _
    exact (Relation.ReflTransGen.single ⟨hu',hm,nearestStep_step _ i⟩).tail ⟨hm,hui',hs⟩
  obtain ⟨i,hi|hi⟩ := nearestStep_eq_step hxy
  · subst y; exact hpos x i hx hy
  · subst x; exact withinReach_symm (fun _ _ ↦ nearestStep_symm) (hpos y i hy hx)

lemma double_avoidingReach (C : Finset Vertex) {x y : Vertex}
    (h : avoidingReach C x y) :
    withinReach nearestStep ((↑(thicken C))ᶜ) (doubleVertex x) (doubleVertex y) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact .refl
  | single h => exact double_avoiding_step C h.1 h.2.1 h.2.2
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def roundBox (z : Vertex) : Set Vertex := {x | ∀ i, |2*x i-z i|≤1}

lemma roundBox_nonempty (z : Vertex) : (roundBox z).Nonempty := by
  refine ⟨fun i ↦ z i/2,fun i ↦ abs_le.mpr ?_⟩
  dsimp only
  constructor <;> omega

lemma roundBox_NNConnected (z : Vertex) : NNConnected (roundBox z) := by
  intro x hx y hy
  apply box_reach
  intro u hu i
  have hxi := abs_le.mp (hx i)
  have hyi := abs_le.mp (hy i)
  have hui := hu i
  apply abs_le.mpr
  constructor <;> omega

lemma roundBox_overlap {z w : Vertex} (hzw : ∀ i, |z i-w i|≤1) :
    (roundBox z ∩ roundBox w).Nonempty := by
  refine ⟨fun i ↦ max (z i) (w i)/2,?_,?_⟩ <;> intro i
  · have h := abs_le.mp (hzw i)
    dsimp only
    apply abs_le.mpr
    constructor <;> omega
  · have h := abs_le.mp (hzw i)
    dsimp only
    apply abs_le.mpr
    constructor <;> omega

lemma nearestStep_starBound {x y : Vertex} (h : nearestStep x y) :
    ∀ i, |x i-y i|≤1 := by
  obtain ⟨j,hj,hrest⟩ := h
  intro i
  by_cases hi : i=j
  · subst i; exact hj.le
  · rw [hrest i hi,sub_self,abs_zero]; omega

lemma roundBox_avoids (C : Finset Vertex) {z : Vertex} (hz : z∉thicken C) :
    roundBox z⊆((↑C : Set Vertex)ᶜ) := by
  intro x hx hxc
  apply hz
  apply (mem_thicken C z).mpr
  refine ⟨x,hxc,fun i ↦ ?_⟩
  rw [abs_sub_comm]
  exact hx i

lemma round_nearest_reach {D : Set Vertex} {z w x y : Vertex}
    (hz : roundBox z⊆D) (hw : roundBox w⊆D)
    (hzw : ∀ i, |z i-w i|≤1) (hx : x∈roundBox z) (hy : y∈roundBox w) :
    withinReach nearestStep D x y := by
  obtain ⟨m,hmz,hmw⟩ := roundBox_overlap hzw
  exact (withinReach_mono hz (roundBox_NNConnected z x hx m hmz)).trans
    (withinReach_mono hw (roundBox_NNConnected w m hmw y hy))

lemma round_avoidingReach (C : Finset Vertex) {z w : Vertex}
    (h : withinReach nearestStep ((↑(thicken C))ᶜ) z w)
    (hz : z∉thicken C) {x y : Vertex} (hx : x∈roundBox z) (hy : y∈roundBox w) :
    avoidingReach C x y := by
  induction h using Relation.ReflTransGen.trans_induction_on generalizing x y with
  | refl => exact withinReach_mono (roundBox_avoids C hz) (roundBox_NNConnected _ x hx y hy)
  | single h =>
    exact round_nearest_reach (roundBox_avoids C h.1) (roundBox_avoids C h.2.1)
      (nearestStep_starBound h.2.2) hx hy
  | @trans a b c hab hbc ih₁ ih₂ =>
    have hb : b∉thicken C := withinReach_end hz hab
    obtain ⟨m,hm⟩ := roundBox_nonempty b
    exact (ih₁ hz hx hm).trans (ih₂ hb hm hy)

lemma mem_round_double (x : Vertex) : x∈roundBox (doubleVertex x) := by
  intro i; simp [doubleVertex]

lemma round_component_exterior (C : Finset Vertex) {r z x : Vertex}
    (hr : r∈exterior C) (hz : z∈complementComponent (↑(thicken C)) (doubleVertex r))
    (hx : x∈roundBox z) : x∈exterior C := by
  apply exterior_of_reach C hr
  exact round_avoidingReach C hz.2 (by simpa only [double_mem_thicken_iff] using hr.1)
    (mem_round_double r) hx

lemma round_boundary_shell (C : Finset Vertex) {r z : Vertex} (hr : r∈exterior C)
    (hz : z∈nnBoundary (↑(thicken C)) (complementComponent (↑(thicken C)) (doubleVertex r))) :
    roundBox z⊆exteriorShell C := by
  intro x hx
  refine ⟨round_component_exterior C hr hz.1 hx,?_⟩
  obtain ⟨a,ha,haz⟩ := hz.2
  obtain ⟨c,hc,hca⟩ := (mem_thicken C a).mp ha
  refine ⟨c,hc,?_,?_⟩
  · intro he
    exact (round_component_exterior C hr hz.1 hx).1 (he ▸ hc)
  · intro i
    have ha' := abs_le.mp (hca i)
    have hz' := abs_le.mp (nearestStep_starBound haz i)
    have hx' := abs_le.mp (hx i)
    apply abs_le.mpr
    constructor <;> omega

lemma withinReach_first_entry {D A : Set Vertex} {x y : Vertex}
    (h : withinReach nearestStep D x y) (hxD : x∈D) (hx : x∉A) (hy : y∈A) :
    ∃ u v, withinReach nearestStep (D∩Aᶜ) x u ∧ u∈D ∧ u∉A ∧ v∈A ∧ nearestStep u v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact (hx hy).elim
  | @head z w hzw _ ih =>
    by_cases hw : w∈A
    · exact ⟨z,w,.refl,hxD,hx,hw,hzw.2.2⟩
    · obtain ⟨u,v,hu,huD,huA,hvA,huv⟩ := ih hzw.2.1 hw
      exact ⟨u,v,hu.head ⟨⟨hxD,hx⟩,⟨hzw.2.1,hw⟩,hzw.2.2⟩,huD,huA,hvA,huv⟩

lemma shell_covered_by_boundary (C : Finset Vertex) {r x : Vertex}
    (hr : r∈exterior C) (hx : x∈exteriorShell C) :
    ∃ z∈nnBoundary (↑(thicken C)) (complementComponent (↑(thicken C)) (doubleVertex r)),
      x∈roundBox z := by
  obtain ⟨c,hc,hcx⟩ := hx.2
  let m : Vertex := x+c
  let D : Set Vertex := {z | ∀ i, |z i-2*x i|≤1}
  have hstart : doubleVertex x∈D := by intro i; simp [doubleVertex]
  have hm : m∈thicken C := by
    apply (mem_thicken C m).mpr
    refine ⟨c,hc,fun i ↦ ?_⟩
    change |x i+c i-2*c i|≤1
    rw [show x i+c i-2*c i=x i-c i by ring,abs_sub_comm]
    exact hcx.2 i
  have hxnot : doubleVertex x∉thicken C := by simpa only [double_mem_thicken_iff] using hx.1.1
  have hp : withinReach nearestStep D (doubleVertex x) m := by
    apply box_reach
    intro z hz i
    have hi := abs_le.mp (hcx.2 i)
    have hz' := hz i
    change min (2*x i) (x i+c i)≤z i ∧ z i≤ max (2*x i) (x i+c i) at hz'
    apply abs_le.mpr
    constructor <;> omega
  obtain ⟨u,v,hu,huD,huA,hvA,huv⟩ := withinReach_first_entry hp hstart hxnot hm
  have hb : u∈complementComponent (↑(thicken C)) (doubleVertex r) := by
    refine ⟨huA,?_⟩
    exact (double_avoidingReach C (exterior_avoidingReach C hr hx.1)).trans
      (withinReach_mono (fun _ hz ↦ hz.2) hu)
  refine ⟨u,⟨hb,v,hvA,nearestStep_symm huv⟩,fun i ↦ ?_⟩
  rw [abs_sub_comm]
  exact huD i

lemma round_boundary_reach (C : Finset Vertex) {r z w : Vertex} (hr : r∈exterior C)
    (h : withinReach starStep
      (nnBoundary (↑(thicken C)) (complementComponent (↑(thicken C)) (doubleVertex r))) z w)
    (hz : z∈nnBoundary (↑(thicken C)) (complementComponent (↑(thicken C)) (doubleVertex r)))
    {x y : Vertex} (hx : x∈roundBox z) (hy : y∈roundBox w) :
    withinReach nearestStep (exteriorShell C) x y := by
  induction h using Relation.ReflTransGen.trans_induction_on generalizing x y with
  | refl => exact withinReach_mono (round_boundary_shell C hr hz) (roundBox_NNConnected _ x hx y hy)
  | single h =>
    exact round_nearest_reach (round_boundary_shell C hr h.1) (round_boundary_shell C hr h.2.1)
      h.2.2.2 hx hy
  | @trans a b c hab hbc ih₁ ih₂ =>
    have hb := withinReach_end hz hab
    obtain ⟨m,hm⟩ := roundBox_nonempty b
    exact (ih₁ hz hx hm).trans (ih₂ hb hm hy)

theorem exteriorShell_NNConnected (C : Finset Vertex) (hC : starConnected (↑C)) :
    NNConnected (exteriorShell C) := by
  intro x hx y hy
  obtain ⟨z,hz,hxz⟩ := shell_covered_by_boundary C hx.1 hx
  obtain ⟨w,hw,hyw⟩ := shell_covered_by_boundary C hx.1 hy
  have hc := nnBoundary_starConnected (thicken C).finite_toSet (thicken_NNConnected C hC)
    (complementComponent_spec (↑(thicken C)) (doubleVertex x))
  exact round_boundary_reach C hx.1 (hc z hz w hw) hz hxz hyw

lemma nearestStep_ne {x y : Vertex} (h : nearestStep x y) : x≠y := by
  intro he
  obtain ⟨i,hi,_⟩ := h
  simp [he] at hi

lemma nearestStep_star {x y : Vertex} (h : nearestStep x y) : starStep x y :=
  ⟨nearestStep_ne h,nearestStep_starBound h⟩

lemma mem_fill_of_mem (C : Finset Vertex) {x : Vertex} (hx : x∈C) : x∈fill C :=
  fun h ↦ h.1 hx

def detourRegion (Γ : Set Vertex) (Cs : Finset (Finset Vertex)) : Set Vertex :=
  {x | x∈Γ ∨ ∃ C∈Cs, x∈exteriorShell C}

def goodDetourRegion (Γ B : Set Vertex) (Cs : Finset (Finset Vertex)) : Set Vertex :=
  detourRegion Γ Cs ∩ Bᶜ

theorem good_detour_reach (Γ B : Set Vertex) (Cs : Finset (Finset Vertex))
    (hCs : ∀ C∈Cs, starConnected (↑C))
    (hbad : ∀ C∈Cs, (↑C : Set Vertex)⊆B)
    (hmax : ∀ C∈Cs, ∀ c∈C, ∀ x∈B, starStep c x → x∈C)
    (hcover : ∀ x∈Γ, x∈B → ∃ C∈Cs, x∈C)
    {v w : Vertex} (hvΓ : v∈Γ) (_hwΓ : w∈Γ)
    (hv : ∀ C∈Cs, v∈exterior C) (hw : ∀ C∈Cs, w∈exterior C)
    (hwalk : withinReach nearestStep Γ v w) :
    withinReach nearestStep (goodDetourRegion Γ B Cs) v w := by
  let D := goodDetourRegion Γ B Cs
  have hvGood : v∉B := by
    intro hvB
    obtain ⟨C,hC,hvC⟩ := hcover v hvΓ hvB
    exact (hv C hC).1 hvC
  have hvD : v∈D := ⟨Or.inl hvΓ,hvGood⟩
  let R : Set Vertex := {x | x∈D ∧ withinReach nearestStep D v x}
  have hvR : v∈R := ⟨hvD,.refl⟩
  have hstep : ∀ x∈R, ∀ y∈D, nearestStep x y → y∈R := by
    intro x hx y hy hxy
    exact ⟨hy,hx.2.tail ⟨hx.1,hy,hxy⟩⟩
  have hRext : ∀ C∈Cs, ∀ x∈R, x∈exterior C := by
    intro C hC x hx
    apply exterior_of_reach C (hv C hC)
    apply withinReach_mono (D := D) _ hx.2
    intro y hy hyC
    exact hy.2 (hbad C hC hyC)
  have hshellD : ∀ C∈Cs, exteriorShell C⊆D := by
    intro C hC x hx
    exact ⟨Or.inr ⟨C,hC,hx⟩,exteriorShell_good C B (hmax C hC) hx⟩
  let active : Finset Vertex → Prop := fun C ↦ ∃ z∈exteriorShell C, z∈R
  have hactive : ∀ C∈Cs, active C → exteriorShell C⊆R := by
    intro C hC hact x hx
    obtain ⟨z,hz,hzR⟩ := hact
    have hp := withinReach_mono (hshellD C hC) ((exteriorShell_NNConnected C (hCs C hC)) z hz x hx)
    exact ⟨hshellD C hC hx,hzR.2.trans hp⟩
  let E : Set Vertex := {x | x∈R ∨ ∃ C∈Cs, active C ∧ x∈fill C}
  have hE : ∀ x∈E, ∀ y∈Γ, nearestStep x y → y∈E := by
    intro x hx y hy hxy
    rcases hx with hx|⟨C,hC,hact,hxfill⟩
    · by_cases hyB : y∈B
      · obtain ⟨C,hC,hyC⟩ := hcover y hy hyB
        have hxshell : x∈exteriorShell C :=
          ⟨hRext C hC x hx,y,hyC,nearestStep_star (nearestStep_symm hxy)⟩
        exact Or.inr ⟨C,hC,⟨x,hxshell,hx⟩,mem_fill_of_mem C hyC⟩
      · exact Or.inl (hstep x hx y ⟨Or.inl hy,hyB⟩ hxy)
    · by_cases hyfill : y∈fill C
      · exact Or.inr ⟨C,hC,hact,hyfill⟩
      · have hyext : y∈exterior C := by simpa only [fill,Set.mem_compl_iff,not_not] using hyfill
        have hxC : x∈C := by
          by_contra hxC
          exact hxfill (exterior_of_reach C hyext (.single ⟨hyext.1,hxC,nearestStep_symm hxy⟩))
        have hyshell : y∈exteriorShell C := ⟨hyext,x,hxC,nearestStep_star hxy⟩
        exact Or.inl (hactive C hC hact hyshell)
  have hpE := withinReach_invariant (D := Γ) hE (show v∈E from Or.inl hvR) hwalk
  have hwE := withinReach_end (show v∈E from Or.inl hvR) hpE
  rcases hwE with hwR|⟨C,hC,_,hwfill⟩
  · exact hwR.2
  · exact (hwfill (hw C hC)).elim

def detourVertices (Γ : Finset Vertex) (Cs : Finset (Finset Vertex)) : Finset Vertex :=
  Γ ∪ Cs.biUnion (fun C ↦ (exteriorShell_finite C).toFinset)

lemma mem_detourVertices (Γ : Finset Vertex) (Cs : Finset (Finset Vertex)) (x : Vertex) :
    x∈detourVertices Γ Cs ↔ x∈detourRegion (↑Γ) Cs := by
  simp only [detourVertices,Finset.mem_union,Finset.mem_biUnion,Set.Finite.mem_toFinset,
    detourRegion,Set.mem_ofPred_eq,Finset.mem_coe]

lemma detourVertices_card_le (Γ : Finset Vertex) (Cs : Finset (Finset Vertex)) :
    (detourVertices Γ Cs).card≤Γ.card+26*∑ C∈Cs, C.card := by
  calc
    _ ≤ Γ.card+(Cs.biUnion (fun C ↦ (exteriorShell_finite C).toFinset)).card := Finset.card_union_le _ _
    _ ≤ Γ.card+∑ C∈Cs, (exteriorShell_finite C).toFinset.card := Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ Γ.card+∑ C∈Cs, 26*C.card := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro C _
      rw [← Set.ncard_eq_toFinset_card (exteriorShell C) (exteriorShell_finite C)]
      exact exteriorShell_card_le C
    _ = Γ.card+26*∑ C∈Cs, C.card := by rw [Finset.mul_sum]

def nearestGraph : SimpleGraph Vertex where
  Adj := nearestStep
  symm := ⟨by intro x y h; exact nearestStep_symm h⟩
  loopless := ⟨by intro x h; exact nearestStep_ne h rfl⟩

def restrictedNearestGraph (D : Set Vertex) : SimpleGraph Vertex where
  Adj x y := x∈D ∧ y∈D ∧ nearestStep x y
  symm := ⟨by intro x y h; exact ⟨h.2.1,h.1,nearestStep_symm h.2.2⟩⟩
  loopless := ⟨by intro x h; exact nearestStep_ne h.2.2 rfl⟩

lemma withinReach_simple_path {D : Set Vertex} {v w : Vertex} (hv : v∈D)
    (h : withinReach nearestStep D v w) :
    ∃ p : nearestGraph.Walk v w, p.IsPath ∧ ∀ x∈p.support, x∈D := by
  have hr : (restrictedNearestGraph D).Reachable v w :=
    (SimpleGraph.reachable_iff_reflTransGen v w).mpr h
  obtain ⟨q⟩ := hr
  let f : restrictedNearestGraph D →g nearestGraph :=
    ⟨id,fun {_ _} h ↦ h.2.2⟩
  have hs : ∀ {u z : Vertex} (p : (restrictedNearestGraph D).Walk u z),
      u∈D → ∀ x∈p.support, x∈D := by
    intro u z p
    induction p with
    | nil =>
      intro hu x hx
      simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hx
      subst x
      exact hu
    | @cons u v z huv p ih =>
      intro hu x hx
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact hu
      · exact ih huv.2.1 x hx
  refine ⟨q.toPath.val.map f,SimpleGraph.Walk.IsPath.map (fun _ _ h ↦ h) q.toPath.isPath,?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_map] at hx
  obtain ⟨y,hy,he⟩ := List.mem_map.mp hx
  change y=x at he
  subst x
  exact hs q.toPath.val hv y hy

theorem simple_good_detour (Γ B : Set Vertex) (Cs : Finset (Finset Vertex))
    (hCs : ∀ C∈Cs, starConnected (↑C))
    (hbad : ∀ C∈Cs, (↑C : Set Vertex)⊆B)
    (hmax : ∀ C∈Cs, ∀ c∈C, ∀ x∈B, starStep c x → x∈C)
    (hcover : ∀ x∈Γ, x∈B → ∃ C∈Cs, x∈C)
    (hmeet : ∀ C∈Cs, ∃ x∈Γ, x∈C)
    {v w : Vertex} (hvΓ : v∈Γ) (hwΓ : w∈Γ)
    (hv : ∀ C∈Cs, v∈exterior C) (hw : ∀ C∈Cs, w∈exterior C)
    (hwalk : withinReach nearestStep Γ v w) :
    ∃ p : nearestGraph.Walk v w, p.IsPath ∧
      ∀ x∈p.support, x∉B ∧ (x∈Γ ∨ ∃ C∈Cs, (∃ z∈Γ, z∈C) ∧ x∈exteriorShell C) := by
  have hvD : v∈goodDetourRegion Γ B Cs := by
    refine ⟨Or.inl hvΓ,?_⟩
    intro hvB
    obtain ⟨C,hC,hvC⟩ := hcover v hvΓ hvB
    exact (hv C hC).1 hvC
  obtain ⟨p,hp,hpD⟩ := withinReach_simple_path hvD
    (good_detour_reach Γ B Cs hCs hbad hmax hcover hvΓ hwΓ hv hw hwalk)
  refine ⟨p,hp,fun x hx ↦ ⟨(hpD x hx).2,?_⟩⟩
  rcases (hpD x hx).1 with hxΓ|⟨C,hC,hxC⟩
  · exact Or.inl hxΓ
  · exact Or.inr ⟨C,hC,hmeet C hC,hxC⟩

end HardSphere.Lattice

end

end OAI
