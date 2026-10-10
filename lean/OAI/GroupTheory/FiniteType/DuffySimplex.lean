import Mathlib
import OAI.GroupTheory.FiniteType.SingularSphereCycle

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace DuffySimplex
abbrev Std (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n+1))

def cone {n : ℕ} (t : I) (s : Std n) : Std (n+1) where
  weights := Finsupp.equivFunOnFinite.symm (Fin.cons (t:ℝ) (fun i => (1-t:ℝ)*s.weights i))
  nonneg := by
    intro i
    induction i using Fin.cases with
    | zero => exact t.2.1
    | succ i => exact mul_nonneg (sub_nonneg.mpr t.2.2) (s.weights_nonneg i)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i : Fin (n+2), Fin.cons (t:ℝ) (fun i => (1-t:ℝ)*s.weights i) i = 1
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,← Finset.mul_sum,s.total_of_fintype,mul_one]
    ring

@[simp] lemma cone_zero {n : ℕ} (t : I) (s : Std n) : (cone t s).weights 0 = t := rfl
@[simp] lemma cone_succ {n : ℕ} (t : I) (s : Std n) (i : Fin (n+1)) :
    (cone t s).weights i.succ = (1-t:ℝ)*s.weights i := rfl

lemma continuous_cone (n : ℕ) : Continuous (fun z : I × Std n => cone z.1 z.2) := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff.mpr
  apply continuous_pi
  intro i
  induction i using Fin.cases with
  | zero => exact continuous_subtype_val.comp continuous_fst
  | succ i =>
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp continuous_snd)

def toSimplex : ∀ n, C((Fin n → I),Std n)
  | 0 => ContinuousMap.const _ (Convexity.StdSimplex.single (0 : Fin 1))
  | n+1 => ⟨fun t => cone (t 0) (toSimplex n (fun i => t i.succ)),
      by
        have h : Continuous (fun t : Fin (n+1) → I =>
            (t 0,toSimplex n (fun i => t i.succ))) :=
          (continuous_apply 0).prodMk ((toSimplex n).continuous.comp
            (continuous_pi (fun i => continuous_apply i.succ)))
        exact (continuous_cone n).comp h⟩

@[simp] lemma toSimplex_succ_zero (n : ℕ) (t : Fin (n+1) → I) :
    (toSimplex (n+1) t).weights 0 = t 0 := rfl
@[simp] lemma toSimplex_succ_succ (n : ℕ) (t : Fin (n+1) → I) (i : Fin (n+1)) :
    (toSimplex (n+1) t).weights i.succ =
      (1-t 0:ℝ)*(toSimplex n (fun j => t j.succ)).weights i := rfl

lemma simplex_coordinate_le_one {n : ℕ} (s : Std n) (i : Fin (n+1)) : s.weights i ≤ 1 := by
  have h := Finset.single_le_sum (fun j _ => s.weights_nonneg j) (Finset.mem_univ i)
  rwa [s.total_of_fintype] at h

lemma tail_sum {n : ℕ} (s : Std (n+1)) : ∑ i : Fin (n+1), s.weights i.succ = 1-s.weights 0 := by
  have h := s.total_of_fintype
  rw [Fin.sum_univ_succ] at h
  linarith

def tail {n : ℕ} (s : Std (n+1)) (h : s.weights 0 ≠ 1) : Std n where
  weights := Finsupp.equivFunOnFinite.symm (fun i => s.weights i.succ/(1-s.weights 0))
  nonneg := by
    intro i
    exact div_nonneg (s.weights_nonneg _) (sub_nonneg.mpr (simplex_coordinate_le_one s 0))
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i : Fin (n+1), s.weights i.succ/(1-s.weights 0) = 1
    rw [← Finset.sum_div,tail_sum,div_self (sub_ne_zero.mpr (Ne.symm h))]

lemma cone_tail {n : ℕ} (s : Std (n+1)) (h : s.weights 0 ≠ 1) :
    cone ⟨s.weights 0,s.weights_nonneg 0,simplex_coordinate_le_one s 0⟩ (tail s h) = s := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    change (1-s.weights 0)*(s.weights i.succ/(1-s.weights 0)) = s.weights i.succ
    exact mul_div_cancel₀ _ (sub_ne_zero.mpr (Ne.symm h))

lemma coordinate_zero_of_head_one {n : ℕ} (s : Std (n+1)) (h : s.weights 0 = 1)
    (i : Fin (n+1)) : s.weights i.succ = 0 := by
  have ht := tail_sum s
  rw [h,sub_self] at ht
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => s.weights_nonneg j.succ)).mp ht i (Finset.mem_univ i)

lemma cone_one {n : ℕ} (s : Std (n+1)) (h : s.weights 0 = 1) (v : Std n) :
    cone 1 v = s := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  induction i using Fin.cases with
  | zero => exact h.symm
  | succ i => simp [coordinate_zero_of_head_one s h i]

lemma surjective (n : ℕ) : Function.Surjective (toSimplex n) := by
  induction n with
  | zero =>
    intro s
    exact ⟨Fin.elim0,Subsingleton.elim _ _⟩
  | succ n ih =>
    intro s
    by_cases h : s.weights 0 = 1
    · refine ⟨Fin.cons 1 (fun _ => 0),?_⟩
      exact cone_one s h _
    · obtain ⟨v,hv⟩ := ih (tail s h)
      refine ⟨Fin.cons ⟨s.weights 0,s.weights_nonneg _,simplex_coordinate_le_one s 0⟩ v,?_⟩
      change cone _ (toSimplex n v) = s
      rw [hv]
      exact cone_tail s h

lemma isQuotientMap (n : ℕ) : IsQuotientMap (toSimplex n) :=
  IsQuotientMap.of_surjective_continuous (surjective n) (toSimplex n).continuous

lemma boundary_iff : ∀ n (t : Fin n → I),
    (∃ i, (toSimplex n t).weights i = 0) ↔ t ∈ Cube.boundary (Fin n)
  | 0, t => by simp [toSimplex,Cube.boundary]
  | n+1, t => by
    constructor
    · rintro ⟨i,hi⟩
      induction i using Fin.cases with
      | zero => exact ⟨0,Or.inl (Subtype.ext hi)⟩
      | succ i =>
        rw [toSimplex_succ_succ,mul_eq_zero] at hi
        rcases hi with h | h
        · exact ⟨0,Or.inr (Subtype.ext (sub_eq_zero.mp h).symm)⟩
        · obtain ⟨j,hj⟩ := (boundary_iff n (fun j => t j.succ)).mp ⟨i,h⟩
          exact ⟨j.succ,hj⟩
    · rintro ⟨i,hi⟩
      induction i using Fin.cases with
      | zero =>
        rcases hi with h | h
        · exact ⟨0,by simp [h]⟩
        · refine ⟨(0 : Fin (n+1)).succ,?_⟩
          rw [toSimplex_succ_succ,h]
          simp
      | succ i =>
        obtain ⟨j,hj⟩ := (boundary_iff n (fun j => t j.succ)).mpr ⟨i,hi⟩
        exact ⟨j.succ,by simp [hj]⟩

lemma injective_off_boundary : ∀ n {v w : Fin n → I},
    toSimplex n v = toSimplex n w → v ∉ Cube.boundary (Fin n) → v = w
  | 0, v, w, h, hv => Subsingleton.elim _ _
  | n+1, v, w, h, hv => by
    have h₀ : v 0 = w 0 := Subtype.ext (congrArg (fun s : Std (n+1) => s.weights 0) h)
    have hneq : (1-v 0:ℝ) ≠ 0 := by
      intro hz
      apply hv
      exact ⟨0,Or.inr (Subtype.ext (sub_eq_zero.mp hz).symm)⟩
    have htail : toSimplex n (fun i => v i.succ) = toSimplex n (fun i => w i.succ) := by
      apply Convexity.StdSimplex.ext
      apply Finsupp.ext
      intro i
      have hi := congrArg (fun s : Std (n+1) => s.weights i.succ) h
      simp only [toSimplex_succ_succ,← h₀] at hi
      exact mul_left_cancel₀ hneq hi
    have hv' : (fun i => v i.succ) ∉ Cube.boundary (Fin n) := by
      rintro ⟨i,hi⟩
      exact hv ⟨i.succ,hi⟩
    have hh := injective_off_boundary n htail hv'
    funext i
    induction i using Fin.cases with
    | zero => exact h₀
    | succ i => exact congrFun hh i

end DuffySimplex

namespace DuffyBased
open DuffySimplex
open Set Topology
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ} {x : X}

def loop (f : BasedSimplex.Space n X x) : GenLoop (Fin n) X x :=
  ⟨f.1.comp (toSimplex n),fun v hv => f.2 _ ((boundary_iff n v).mpr hv)⟩

lemma loop_fiber (p : GenLoop (Fin n) X x) {v w : Fin n → I}
    (h : toSimplex n v = toSimplex n w) : p v = p w := by
  by_cases hv : v ∈ Cube.boundary (Fin n)
  · have hw : w ∈ Cube.boundary (Fin n) :=
      (boundary_iff n w).mp (h ▸ (boundary_iff n v).mpr hv)
    exact (p.2 v hv).trans (p.2 w hw).symm
  · exact congrArg p (injective_off_boundary n h hv)

def ofLoop (p : GenLoop (Fin n) X x) : BasedSimplex.Space n X x :=
  ⟨(isQuotientMap n).lift p.1 (fun _ _ h => loop_fiber p h),by
    intro s hs
    obtain ⟨t,rfl⟩ := surjective n s
    have he := DFunLike.congr_fun ((isQuotientMap n).lift_comp p.1
      (fun _ _ h => loop_fiber p h)) t
    exact he.trans (p.2 t ((boundary_iff n t).mp hs))⟩

@[simp] theorem ofLoop_apply (p : GenLoop (Fin n) X x) (v : Fin n → I) :
    ofLoop p (toSimplex n v) = p v :=
  DFunLike.congr_fun ((isQuotientMap n).lift_comp p.1 (fun _ _ h => loop_fiber p h)) v

@[simp] theorem loop_ofLoop (p : GenLoop (Fin n) X x) : loop (ofLoop p) = p := by
  ext v
  exact ofLoop_apply p v

@[simp] theorem ofLoop_loop (f : BasedSimplex.Space n X x) : ofLoop (loop f) = f := by
  ext s
  obtain ⟨v,rfl⟩ := surjective n s
  exact ofLoop_apply (loop f) v

def equiv (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :
    BasedSimplex.Space n X x ≃ GenLoop (Fin n) X x where
  toFun := loop
  invFun := ofLoop
  left_inv := ofLoop_loop
  right_inv := loop_ofLoop

def homotopy {f g : BasedSimplex.Space n X x}
    (H : f.1.HomotopyRel g.1 (BasedSimplex.Boundary n)) :
    (loop f).1.HomotopyRel (loop g).1 (Cube.boundary (Fin n)) where
  toHomotopy :=
  { toFun := fun z => H (z.1,toSimplex n z.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk ((toSimplex n).continuous.comp continuous_snd))
    map_zero_left := fun v => H.apply_zero (toSimplex n v)
    map_one_left := fun v => H.apply_one (toSimplex n v) }
  prop' := fun t v hv => H.eq_fst t ((boundary_iff n v).mpr hv)

def cylinder (n : ℕ) : C(I × (Fin n → I), I × Std n) :=
  ⟨fun z => (z.1,toSimplex n z.2),
    continuous_fst.prodMk ((toSimplex n).continuous.comp continuous_snd)⟩

lemma cylinder_quotient (n : ℕ) : IsQuotientMap (cylinder n) :=
  IsQuotientMap.of_surjective_continuous (by
    rintro ⟨t,s⟩
    obtain ⟨v,rfl⟩ := surjective n s
    exact ⟨(t,v),rfl⟩) (cylinder n).continuous

lemma homotopy_fiber {f g : BasedSimplex.Space n X x}
    (H : (loop f).1.HomotopyRel (loop g).1 (Cube.boundary (Fin n)))
    (v w : I × (Fin n → I)) (h : cylinder n v = cylinder n w) : H v = H w := by
  have ht : v.1 = w.1 := congrArg (fun z : I × Std n => z.1) h
  have hvw : toSimplex n v.2 = toSimplex n w.2 := congrArg Prod.snd h
  by_cases hv : v.2 ∈ Cube.boundary (Fin n)
  · have hw := (boundary_iff n w.2).mp (hvw ▸ (boundary_iff n v.2).mpr hv)
    exact (H.eq_fst _ hv).trans ((loop_fiber (loop f) hvw).trans (H.eq_fst _ hw).symm)
  · exact congrArg H (Prod.ext ht (injective_off_boundary n hvw hv))

def homotopyOfLoop {f g : BasedSimplex.Space n X x}
    (H : (loop f).1.HomotopyRel (loop g).1 (Cube.boundary (Fin n))) :
    f.1.HomotopyRel g.1 (BasedSimplex.Boundary n) := by
  let K : C(I × Std n,X) := (cylinder_quotient n).lift H.toContinuousMap (homotopy_fiber H)
  have hK (t : I) (v : Fin n → I) : K (t,toSimplex n v) = H (t,v) :=
    DFunLike.congr_fun ((cylinder_quotient n).lift_comp H.toContinuousMap (homotopy_fiber H)) (t,v)
  refine
  { toHomotopy :=
    { toContinuousMap := K
      map_zero_left := ?_
      map_one_left := ?_ }
    prop' := ?_ }
  · intro s
    obtain ⟨v,rfl⟩ := surjective n s
    exact (hK 0 v).trans (H.apply_zero v)
  · intro s
    obtain ⟨v,rfl⟩ := surjective n s
    exact (hK 1 v).trans (H.apply_one v)
  · intro t s hs
    obtain ⟨v,rfl⟩ := surjective n s
    exact (hK t v).trans (H.eq_fst t ((boundary_iff n v).mp hs))

def homotopyClass (f : BasedSimplex.Space n X x) : HomotopyGroup.Pi n X x :=
  Quotient.mk _ (loop f)

lemma class_eq_iff (f g : BasedSimplex.Space n X x) :
    homotopyClass f = homotopyClass g ↔ Nonempty (f.1.HomotopyRel g.1 (BasedSimplex.Boundary n)) := by
  constructor
  · intro h
    obtain ⟨H⟩ := Quotient.exact h
    exact ⟨homotopyOfLoop H⟩
  · rintro ⟨H⟩
    exact Quotient.sound ⟨homotopy H⟩

end DuffyBased

end

end OAI
