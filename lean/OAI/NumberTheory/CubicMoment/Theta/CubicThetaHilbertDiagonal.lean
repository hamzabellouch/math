import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace OAI

/-! Bounded diagonal operators on the square-summable cusp modes. The
finite-mode truncations retain the full radial Hilbert space in each mode. -/
noncomputable section
open scoped BigOperators ENNReal NNReal
open Filter Topology
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

variable {ι H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

private lemma diagonal_mem (T : ι → H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : lp (fun _ : ι => H) 2) :
    Memℓp (fun i => T i (x i)) 2 := by
  apply (((C:ℂ) • x).property).mono'
  intro i
  change ‖T i (x i)‖ ≤ ‖(C:ℂ) • x i‖
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]
  exact (T i).le_opNorm (x i) |>.trans
    (mul_le_mul_of_nonneg_right (hT i) (_root_.norm_nonneg _))

private lemma diagonal_norm (T : ι → H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (x y : lp (fun _ : ι => H) 2)
    (hy : ∀ i, y i=T i (x i)) : ‖y‖ ≤ C*‖x‖ := by
  calc
    ‖y‖ ≤ ‖(C:ℂ) • x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      rw [hy i]
      change ‖T i (x i)‖ ≤ ‖(C:ℂ) • x i‖
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]
      exact (T i).le_opNorm (x i) |>.trans
        (mul_le_mul_of_nonneg_right (hT i) (_root_.norm_nonneg _))
    _ = _ := by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]

def cubicThetaHilbertDiagonal (T : ι → H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) :
    lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => T i (x i), diagonal_mem T hC hT x⟩
      map_add' := fun x y => by ext i; exact (T i).map_add (x i) (y i)
      map_smul' := fun c x => by ext i; exact (T i).map_smul c (x i) }
    C (fun x => diagonal_norm T hC hT x _ (fun _ => rfl))

lemma cubicThetaHilbertDiagonal_apply (T : ι → H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : lp (fun _ : ι => H) 2) (i : ι) :
    cubicThetaHilbertDiagonal T hC hT x i=T i (x i) := rfl

lemma cubicThetaHilbertDiagonal_norm (T : ι → H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) : ‖cubicThetaHilbertDiagonal T hC hT‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (fun x => diagonal_norm T hC hT x _ (fun _ => rfl))

def cubicThetaHilbertFiniteDiagonal (T : ι → H →L[ℂ] H) (s : Finset ι) :
    lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2 := by
  classical
  exact ∑ i ∈ s, (lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 i).comp ((T i).comp (lp.evalCLM ℂ (fun _ : ι => H) 2 i))

lemma cubicThetaHilbertFiniteDiagonal_apply (T : ι → H →L[ℂ] H)
    (s : Finset ι) (x : lp (fun _ : ι => H) 2) (i : ι) :
    cubicThetaHilbertFiniteDiagonal T s x i=if i∈s then T i (x i) else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cubicThetaHilbertFiniteDiagonal]
  | @insert j s hj ih =>
    have hs : cubicThetaHilbertFiniteDiagonal T (insert j s)=
        (lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 j).comp
          ((T j).comp (lp.evalCLM ℂ (fun _ : ι => H) 2 j))+
        cubicThetaHilbertFiniteDiagonal T s := by
      simp only [cubicThetaHilbertFiniteDiagonal,Finset.sum_insert hj]
    rw [hs]
    change lp.single (E:=fun _ : ι => H) 2 j (T j (x j)) i+cubicThetaHilbertFiniteDiagonal T s x i=_
    rw [ih]
    by_cases hi : i=j
    · subst i
      simp [hj]
    · simp [lp.single_apply,hi]


lemma cubicThetaHilbertFiniteDiagonal_compact (T : ι → H →L[ℂ] H)
    (hT : ∀ i, IsCompactOperator (T i)) (s : Finset ι) :
    IsCompactOperator (cubicThetaHilbertFiniteDiagonal T s) := by
  classical
  apply (compactOperator (RingHom.id ℂ) _ _).sum_mem
  intro i hi
  exact ((hT i).comp_clm (lp.evalCLM ℂ (fun _ : ι => H) 2 i)).clm_comp (lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 i)

lemma cubicThetaHilbertDiagonal_tail_norm (T : ι → H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (s : Finset ι) {B : ℝ} (hB : 0 ≤ B)
    (hsmall : ∀ i, i∉s → ‖T i‖ ≤ B) :
    ‖cubicThetaHilbertDiagonal T hC hT-cubicThetaHilbertFiniteDiagonal T s‖ ≤ B := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro x
  calc
    _ ≤ ‖(B:ℂ) • x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      change ‖cubicThetaHilbertDiagonal T hC hT x i-cubicThetaHilbertFiniteDiagonal T s x i‖ ≤ ‖(B:ℂ) • x i‖
      rw [cubicThetaHilbertDiagonal_apply,cubicThetaHilbertFiniteDiagonal_apply]
      split_ifs with hi
      · simp
      · rw [sub_zero,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
        exact (T i).le_opNorm (x i) |>.trans
          (mul_le_mul_of_nonneg_right (hsmall i hi) (_root_.norm_nonneg _))
    _ = _ := by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]

end CubicFirstMoment

end

end OAI
