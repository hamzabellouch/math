import OAI.Combinatorics.HalvingLines.Recurrence

namespace OAI

open Filter Topology

namespace PlanarHalving.Perturbation
open Set

lemma orient_cycle (p q r : Point) : orient q r p=orient p q r := by unfold orient;ring

lemma orient_segment {p q z : Point} (hz : z∈segment ℝ p q) : orient p q z=0 := by
  rw [segment_eq_image] at hz
  obtain ⟨t,_,rfl⟩ := hz
  simp only [orient,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

lemma no_vertex_openSegment {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P)
    {i j : Fin n} (hij : i≠j) (v : Fin n) : P v∉openSegment ℝ (P i) (P j) := by
  intro hv
  have ho := orient_segment (openSegment_subset_segment ℝ _ _ hv)
  rcases (orient_zero_iff hP hij v).mp ho with rfl | rfl
  · exact hij (hP.1 (left_mem_openSegment_iff.mp hv))
  · exact hij (hP.1 (right_mem_openSegment_iff.mp hv))

lemma two_lines_intersection {p q r z : Point} (hd : orient p q r≠0)
    (hq : orient p q z=0) (hr : orient p r z=0) : z=p := by
  have hx : orient p q r*(z.1-p.1)=0 := by
    unfold orient at *
    linear_combination (r.1-p.1)*hq-(q.1-p.1)*hr
  have hy : orient p q r*(z.2-p.2)=0 := by
    unfold orient at *
    linear_combination (r.2-p.2)*hq-(q.2-p.2)*hr
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hd))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hd))

lemma slope_eq_orient_zero {p q r : Point} (hxq : p.1≠q.1) (hxr : p.1≠r.1)
    (hs : slope p q=slope p r) : orient p q r=0 := by
  rw [orient_eq_proj_diff _ _ _ hxq.symm]
  have he := Sweep.tied_projection p r hxr
  rw [← hs] at he
  change _*(Sweep.projection (slope p q) r-Sweep.projection (slope p q) p)=0
  rw [← he,sub_self,mul_zero]

noncomputable def intercept (p q : Point) : ℝ := p.2-slope p q*p.1
noncomputable def intersectionPoint (p q r s : Point) : Point :=
  let x := (intercept r s-intercept p q)/(slope p q-slope r s)
  (x,slope p q*x+intercept p q)

lemma orient_line_eq {p q z : Point} (hx : p.1≠q.1) (hz : orient p q z=0) :
    z.2=slope p q*z.1+intercept p q := by
  rw [orient_eq_proj_diff _ _ _ hx.symm] at hz
  have hh := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hx.symm)
  dsimp [intercept]
  linarith

lemma intersectionPoint_eq {p q r s z : Point} (hpq : p.1≠q.1) (hrs : r.1≠s.1)
    (hs : slope p q≠slope r s) (hzp : orient p q z=0) (hzr : orient r s z=0) :
    z=intersectionPoint p q r s := by
  have hp := orient_line_eq hpq hzp
  have hr := orient_line_eq hrs hzr
  have hx : z.1=(intercept r s-intercept p q)/(slope p q-slope r s) := by
    apply (eq_div_iff (sub_ne_zero.mpr hs)).mpr
    nlinarith only [hp,hr]
  apply Prod.ext
  · exact hx
  · change z.2=slope p q*((intercept r s-intercept p q)/(slope p q-slope r s))+intercept p q
    rw [← hx]
    exact hp

abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

noncomputable def edgeSlope {n : ℕ} (P : Fin n → Point) (e : Edge n) := slope (P e.val.1) (P e.val.2)
def onLine {n : ℕ} (P : Fin n → Point) (e : Edge n) (z : Point) := orient (P e.val.1) (P e.val.2) z=0

structure Regular {n : ℕ} (P : Fin n → Point) : Prop where
  general : GeneralPosition P
  xdistinct : ∀ i j, i≠j → (P i).1≠(P j).1
  slopes : Function.Injective (edgeSlope P)
  concurrent : ∀ e f g : Edge n, e≠f → g≠e → g≠f → ∀ z : Point,
    onLine P e z → onLine P f z → onLine P g z → ∃ v, P v=z

lemma Regular.generic {n : ℕ} {P : Fin n → Point} (hP : Regular P) : Generic P := by
  refine ⟨hP.general,hP.xdistinct,?_,?_⟩
  · intro i j a b hij hab hs
    have he : (⟨(i,j),hij⟩ : Edge n)=⟨(a,b),hab⟩ := hP.slopes hs
    exact Prod.mk.inj (congrArg Subtype.val he)
  · intro i j a b c d hij hab hcd hef hge hgf z hz₁ hz₂ hz₃
    obtain ⟨v,hv⟩ := hP.concurrent ⟨(i,j),hij⟩ ⟨(a,b),hab⟩ ⟨(c,d),hcd⟩
      (fun h => hef (congrArg Subtype.val h)) (fun h => hge (congrArg Subtype.val h))
      (fun h => hgf (congrArg Subtype.val h)) z
      (orient_segment (openSegment_subset_segment ℝ _ _ hz₁))
      (orient_segment (openSegment_subset_segment ℝ _ _ hz₂)) (orient_segment hz₃)
    rw [← hv] at hz₁
    exact no_vertex_openSegment hP.general hij.ne v hz₁

def newEdge {n : ℕ} (i : Fin n) : Edge (n+1) := ⟨(0,i.succ),Fin.succ_pos i⟩
def oldEdge {n : ℕ} (e : Edge n) : Edge (n+1) := ⟨(e.val.1.succ,e.val.2.succ),Fin.succ_lt_succ_iff.mpr e.property⟩

lemma newEdge_injective (n : ℕ) : Function.Injective (@newEdge n) := by
  intro i j he
  exact Fin.succ_inj.mp (congrArg (fun e => e.val.2) he)
lemma oldEdge_injective (n : ℕ) : Function.Injective (@oldEdge n) := by
  intro i j he
  apply Subtype.ext
  exact Prod.ext (Fin.succ_inj.mp (congrArg (fun e => e.val.1) he))
    (Fin.succ_inj.mp (congrArg (fun e => e.val.2) he))
lemma newEdge_ne_oldEdge {n : ℕ} (i : Fin n) (e : Edge n) : newEdge i≠oldEdge e := by
  intro he
  exact Fin.succ_ne_zero e.val.1 (congrArg (fun e => e.val.1) he).symm

lemma edge_cases {n : ℕ} (e : Edge (n+1)) :
    (∃ i, e=newEdge i) ∨ ∃ f, e=oldEdge f := by
  rcases e with ⟨⟨i,j⟩,hij⟩
  have hj : j≠0 := by intro h;subst j;exact (Fin.not_lt_zero i) hij
  obtain ⟨j,rfl⟩ := Fin.exists_succ_eq.mpr hj
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i,rfl⟩
  · exact Or.inl ⟨j,rfl⟩
  · exact Or.inr ⟨⟨(i,j),Fin.succ_lt_succ_iff.mp hij⟩,rfl⟩

@[simp] lemma edgeSlope_new {n : ℕ} (P : Fin n → Point) (p : Point) (i : Fin n) :
    edgeSlope (Fin.cons p P) (newEdge i)=slope p (P i) := by simp [edgeSlope,newEdge]
@[simp] lemma edgeSlope_old {n : ℕ} (P : Fin n → Point) (p : Point) (e : Edge n) :
    edgeSlope (Fin.cons p P) (oldEdge e)=edgeSlope P e := by simp [edgeSlope,oldEdge]
@[simp] lemma onLine_new {n : ℕ} (P : Fin n → Point) (p z : Point) (i : Fin n) :
    onLine (Fin.cons p P) (newEdge i) z ↔ orient p (P i) z=0 := by simp [onLine,newEdge]
@[simp] lemma onLine_old {n : ℕ} (P : Fin n → Point) (p z : Point) (e : Edge n) :
    onLine (Fin.cons p P) (oldEdge e) z ↔ onLine P e z := by simp [onLine,oldEdge]

end PlanarHalving.Perturbation
namespace PlanarHalving.Perturbation
open Set

lemma open_dense_affine (a b c : ℝ) (hab : a≠0 ∨ b≠0) :
    IsOpen {p : Point | a*p.1+b*p.2≠c} ∧ Dense {p : Point | a*p.1+b*p.2≠c} := by
  let L : Point →L[ℝ] ℝ := a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hL : L≠0 := by
    intro h
    have ha := congrArg (fun f : Point →L[ℝ] ℝ => f (1,0)) h
    have hb := congrArg (fun f : Point →L[ℝ] ℝ => f (0,1)) h
    change a*1+b*0=0 at ha
    change a*0+b*1=0 at hb
    norm_num at ha hb
    exact hab.elim (fun h => h ha) (fun h => h hb)
  have hd := (dense_compl_singleton c).preimage (L.isOpenMap_of_ne_zero hL)
  refine ⟨?_,?_⟩
  · exact isOpen_ne.preimage (by fun_prop : Continuous (fun p : Point => a*p.1+b*p.2))
  · change Dense {p : Point | a*p.1+b*p.2≠c} at hd
    exact hd

lemma open_dense_orient {p q : Point} (hpq : p≠q) :
    IsOpen {z : Point | orient p q z≠0} ∧ Dense {z : Point | orient p q z≠0} := by
  have hab : -(q.2-p.2)≠0 ∨ q.1-p.1≠0 := by
    by_contra! h
    apply hpq
    apply Prod.ext <;> linarith
  have he : {z : Point | orient p q z≠0}=
      {z : Point | -(q.2-p.2)*z.1+(q.1-p.1)*z.2≠(q.1-p.1)*p.2-(q.2-p.2)*p.1} := by
    ext z
    simp only [Set.mem_ofPred_eq,orient]
    constructor <;> intro hn he <;> apply hn <;> nlinarith only [he]
  rw [he]
  exact open_dense_affine _ _ _ hab

lemma open_dense_forall {ι : Sort*} [Finite ι] (p : ι → Point → Prop)
    (hU : ∀ i, IsOpen {x | p i x} ∧ Dense {x | p i x}) :
    IsOpen {x : Point | ∀ i, p i x} ∧ Dense {x : Point | ∀ i, p i x} := by
  simpa only [Set.ofPred_forall] using
    (show IsOpen (⋂ i, {x | p i x}) ∧ Dense (⋂ i, {x | p i x}) from
      ⟨isOpen_iInter_of_finite (fun i => (hU i).1),dense_iInter_of_isOpen (fun i => (hU i).1) (fun i => (hU i).2)⟩)

lemma open_dense_and {p q : Point → Prop}
    (hp : IsOpen {x | p x} ∧ Dense {x | p x}) (hq : IsOpen {x | q x} ∧ Dense {x | q x}) :
    IsOpen {x | p x ∧ q x} ∧ Dense {x | p x ∧ q x} :=
  ⟨hp.1.inter hq.1,hp.2.inter_of_isOpen_left hq.2 hp.1⟩

noncomputable def edgeMeet {n : ℕ} (P : Fin n → Point) (e f : Edge n) : Point :=
  intersectionPoint (P e.val.1) (P e.val.2) (P f.val.1) (P f.val.2)

def Fresh {n : ℕ} (P : Fin n → Point) (p : Point) : Prop :=
  (∀ i, p.1≠(P i).1) ∧
  (∀ i j, i≠j → orient (P i) (P j) p≠0) ∧
  (∀ i e, Sweep.projection (edgeSlope P e) p≠Sweep.projection (edgeSlope P e) (P i)) ∧
  (∀ i e f, edgeMeet P e f≠P i → orient (P i) (edgeMeet P e f) p≠0)

lemma fresh_open_dense {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P) :
    IsOpen {p | Fresh P p} ∧ Dense {p | Fresh P p} := by
  unfold Fresh
  apply open_dense_and
  · apply open_dense_forall
    intro i
    simpa only [one_mul,zero_mul,add_zero] using open_dense_affine 1 0 (P i).1 (Or.inl one_ne_zero)
  · apply open_dense_and
    · apply open_dense_forall
      intro i
      apply open_dense_forall
      intro j
      apply open_dense_forall
      intro hij
      exact open_dense_orient (fun h => hij (hP.1 h))
    · apply open_dense_and
      · apply open_dense_forall
        intro i
        apply open_dense_forall
        intro e
        simpa only [Sweep.projection,one_mul,sub_eq_add_neg,neg_mul,add_comm] using
          open_dense_affine (-(edgeSlope P e)) 1 ((P i).2-edgeSlope P e*(P i).1) (Or.inr one_ne_zero)
      · apply open_dense_forall
        intro i
        apply open_dense_forall
        intro e
        apply open_dense_forall
        intro f
        apply open_dense_forall
        intro hi
        exact open_dense_orient hi.symm

end PlanarHalving.Perturbation
namespace PlanarHalving.Perturbation
open Set
variable {n : ℕ} {P : Fin n → Point} {p : Point}

lemma Fresh.xdistinct (hP : Regular P) (hp : Fresh P p) :
    ∀ i j : Fin (n+1), i≠j → (Fin.cons (α := fun _ => Point) p P i).1≠(Fin.cons (α := fun _ => Point) p P j).1 := by
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i,rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j,rfl⟩
  · exact False.elim (hij rfl)
  · simpa only [Fin.cons_zero,Fin.cons_succ] using hp.1 j
  · simpa only [Fin.cons_zero,Fin.cons_succ] using (hp.1 i).symm
  · simpa only [Fin.cons_succ] using hP.xdistinct i j (fun h => hij (congrArg Fin.succ h))

lemma Fresh.general (hP : Regular P) (hp : Fresh P p) : GeneralPosition (Fin.cons (α := fun _ => Point) p P) := by
  refine ⟨?_,?_⟩
  · intro i j he
    by_contra hn
    exact hp.xdistinct hP i j hn (congrArg Prod.fst he)
  · intro i j l hij hjl hil
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i,rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j,rfl⟩
      · exact False.elim (hij rfl)
      · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l,rfl⟩
        · exact False.elim (hil rfl)
        · simp only [Fin.cons_zero,Fin.cons_succ]
          rw [← orient_cycle p (P j) (P l)]
          exact hp.2.1 j l (fun h => hjl (congrArg Fin.succ h))
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j,rfl⟩
      · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l,rfl⟩
        · exact False.elim (hjl rfl)
        · simp only [Fin.cons_zero,Fin.cons_succ]
          have he : orient (P i) p (P l)=-orient (P i) (P l) p := by unfold orient;ring
          rw [he]
          exact neg_ne_zero.mpr (hp.2.1 i l (fun h => hil (congrArg Fin.succ h)))
      · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l,rfl⟩
        · simpa only [Fin.cons_zero,Fin.cons_succ] using hp.2.1 i j (fun h => hij (congrArg Fin.succ h))
        · simpa only [Fin.cons_succ] using hP.general.2 i j l
            (fun h => hij (congrArg Fin.succ h)) (fun h => hjl (congrArg Fin.succ h))
            (fun h => hil (congrArg Fin.succ h))

lemma Fresh.slopes (hP : Regular P) (hp : Fresh P p) :
    Function.Injective (edgeSlope (Fin.cons (α := fun _ => Point) p P)) := by
  intro e f hs
  rcases edge_cases e with ⟨i,rfl⟩ | ⟨e,rfl⟩ <;>
    rcases edge_cases f with ⟨j,rfl⟩ | ⟨f,rfl⟩
  · simp only [edgeSlope_new] at hs
    apply congrArg newEdge
    by_contra hij
    have ho : orient p (P i) (P j)≠0 := by
      rw [← orient_cycle p (P i) (P j)]
      exact hp.2.1 i j hij
    exact ho (slope_eq_orient_zero (hp.1 i) (hp.1 j) hs)
  · simp only [edgeSlope_new,edgeSlope_old] at hs
    have ht := Sweep.tied_projection p (P i) (hp.1 i)
    rw [hs] at ht
    exact False.elim (hp.2.2.1 i f ht)
  · simp only [edgeSlope_new,edgeSlope_old] at hs
    have ht := Sweep.tied_projection p (P j) (hp.1 j)
    rw [← hs] at ht
    exact False.elim (hp.2.2.1 j e ht)
  · simp only [edgeSlope_old] at hs
    exact congrArg oldEdge (hP.slopes hs)

lemma Fresh.two_new {i j : Fin n} (hp : Fresh P p) (hij : i≠j) {z : Point}
    (hi : orient p (P i) z=0) (hj : orient p (P j) z=0) :
    ∃ v : Fin (n+1), Fin.cons (α := fun _ => Point) p P v=z := by
  have ho : orient p (P i) (P j)≠0 := by
    rw [← orient_cycle p (P i) (P j)]
    exact hp.2.1 i j hij
  exact ⟨0,(two_lines_intersection ho hi hj).symm⟩

lemma Fresh.one_new (hP : Regular P) (hp : Fresh P p) (i : Fin n) {e f : Edge n}
    (hef : e≠f) {z : Point} (hi : orient p (P i) z=0) (he : onLine P e z) (hf : onLine P f z) :
    ∃ v : Fin (n+1), Fin.cons (α := fun _ => Point) p P v=z := by
  have hz : z=edgeMeet P e f := intersectionPoint_eq
    (hP.xdistinct _ _ e.property.ne) (hP.xdistinct _ _ f.property.ne)
    (fun h => hef (hP.slopes h)) he hf
  by_cases hzi : z=P i
  · exact ⟨i.succ,hzi.symm⟩
  · have hn := hp.2.2.2 i e f (by rw [← hz];exact hzi)
    rw [← hz,orient_cycle p (P i) z] at hn
    exact False.elim (hn hi)

lemma Fresh.regular (hP : Regular P) (hp : Fresh P p) : Regular (Fin.cons (α := fun _ => Point) p P) := by
  refine ⟨hp.general hP,hp.xdistinct hP,hp.slopes hP,?_⟩
  intro e f g hef hge hgf z he hf hg
  rcases edge_cases e with ⟨i,rfl⟩ | ⟨e,rfl⟩
  · rcases edge_cases f with ⟨j,rfl⟩ | ⟨f,rfl⟩
    · exact hp.two_new (fun h => hef (congrArg newEdge h)) ((onLine_new P p z i).mp he) ((onLine_new P p z j).mp hf)
    · rcases edge_cases g with ⟨l,rfl⟩ | ⟨g,rfl⟩
      · exact hp.two_new (fun h => hge (congrArg newEdge h.symm)) ((onLine_new P p z i).mp he) ((onLine_new P p z l).mp hg)
      · exact hp.one_new hP i (fun h => hgf (congrArg oldEdge h.symm))
          ((onLine_new P p z i).mp he) ((onLine_old P p z f).mp hf) ((onLine_old P p z g).mp hg)
  · rcases edge_cases f with ⟨j,rfl⟩ | ⟨f,rfl⟩
    · rcases edge_cases g with ⟨l,rfl⟩ | ⟨g,rfl⟩
      · exact hp.two_new (fun h => hgf (congrArg newEdge h.symm)) ((onLine_new P p z j).mp hf) ((onLine_new P p z l).mp hg)
      · exact hp.one_new hP j (fun h => hge (congrArg oldEdge h.symm))
          ((onLine_new P p z j).mp hf) ((onLine_old P p z e).mp he) ((onLine_old P p z g).mp hg)
    · rcases edge_cases g with ⟨l,rfl⟩ | ⟨g,rfl⟩
      · exact hp.one_new hP l (fun h => hef (congrArg oldEdge h))
          ((onLine_new P p z l).mp hg) ((onLine_old P p z e).mp he) ((onLine_old P p z f).mp hf)
      · obtain ⟨v,hv⟩ := hP.concurrent e f g (fun h => hef (congrArg oldEdge h))
          (fun h => hge (congrArg oldEdge h)) (fun h => hgf (congrArg oldEdge h)) z
          ((onLine_old P p z e).mp he) ((onLine_old P p z f).mp hf) ((onLine_old P p z g).mp hg)
        exact ⟨v.succ,hv⟩

end PlanarHalving.Perturbation
namespace PlanarHalving.Perturbation
open Set

lemma regular_empty (P : Fin 0 → Point) : Regular P := by
  constructor
  · constructor
    · intro i;exact Fin.elim0 i
    · intro i;exact Fin.elim0 i
  · intro i;exact Fin.elim0 i
  · intro e;exact Fin.elim0 e.val.1
  · intro e;exact Fin.elim0 e.val.1

lemma regular_approx (n : ℕ) {ε : ℝ} (hε : 0<ε) : ∀ P : Fin n → Point,
    ∃ Q : Fin n → Point, Regular Q ∧ ∀ i, dist (Q i) (P i)<ε := by
  induction n with
  | zero =>
    intro P
    exact ⟨P,regular_empty P,fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro P
    obtain ⟨Q,hQ,hclose⟩ := ih (fun i => P i.succ)
    obtain ⟨p,hp,hpclose⟩ := (fresh_open_dense hQ.general).2.exists_mem_open Metric.isOpen_ball
      (show (Metric.ball (P 0) ε).Nonempty from ⟨P 0,Metric.mem_ball_self hε⟩)
    refine ⟨Fin.cons p Q,hp.regular hQ,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hpclose
    · exact hclose j

lemma dense_regular (n : ℕ) : Dense {P : Fin n → Point | Regular P} := by
  apply Metric.dense_iff.mpr
  intro P ε hε
  obtain ⟨Q,hQ,hclose⟩ := regular_approx n hε P
  exact ⟨Q,(dist_pi_lt_iff hε).mpr hclose,hQ⟩

lemma dense_generic (n : ℕ) : Dense {P : Fin n → Point | Generic P} :=
  (dense_regular n).mono (fun _ hp => hp.generic)

lemma generic_same_sides {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P) :
    ∃ Q : Fin n → Point, Generic Q ∧ ∀ i j l,
      (0<orient (P i) (P j) (P l) ↔ 0<orient (Q i) (Q j) (Q l)) := by
  let U : Set (Fin n → Point) := {Q | ∀ i j l, orient (P i) (P j) (P l)≠0 →
    0<orient (P i) (P j) (P l)*orient (Q i) (Q j) (Q l)}
  have hU : IsOpen U := by
    dsimp only [U]
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro l
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt continuous_const (by unfold orient;fun_prop)
  have hPU : P∈U := by
    intro i j l hn
    exact mul_self_pos.mpr hn
  obtain ⟨Q,hQ,hQU⟩ := (dense_generic n).exists_mem_open hU ⟨P,hPU⟩
  refine ⟨Q,hQ,?_⟩
  intro i j l
  by_cases hij : i=j
  · subst j;simp [orient]
  by_cases hjl : j=l
  · subst l;simp
  by_cases hil : i=l
  · subst l;simp
  have hprod := hQU i j l (hP.2 i j l hij hjl hil)
  rcases mul_pos_iff.mp hprod with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · exact iff_of_true hp hq
  · exact iff_of_false (not_lt_of_ge hp.le) (not_lt_of_ge hq.le)

lemma generic_same_halvingCount {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P) :
    ∃ Q : Fin n → Point, Generic Q ∧ halvingCount P=halvingCount Q := by
  classical
  obtain ⟨Q,hQ,hsides⟩ := generic_same_sides hP
  have hcount (i j : Fin n) : sideCount P i j=sideCount Q i j := by
    unfold sideCount
    apply congrArg Finset.card
    exact Finset.filter_congr (fun l _ => hsides i j l)
  refine ⟨Q,hQ,?_⟩
  unfold halvingCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro ij _
  rw [hcount,hcount]

end PlanarHalving.Perturbation

end OAI
