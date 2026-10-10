import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactGlobalUpdate

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

lemma orthogonal_dotProduct {Q : Mat3} (hQ : Q ∈ orthogonalFrames) (v w : Coord3) :
    (Q *ᵥ v) ⬝ᵥ (Q *ᵥ w) = v ⬝ᵥ w := by
  rw [show Q = Qᵀᵀ by simp, dotProduct_transpose_mulVec]
  rw [transpose_transpose, mulVec_mulVec, hQ.1, one_mulVec]
  exact dotProduct_comm _ _

lemma conjugateDiagonal_quadratic (Q : Mat3) (d : DiagonalTriple) (v : Coord3) :
    v ⬝ᵥ ((Q * diagonal d * Qᵀ) *ᵥ v) =
      ∑ i, d i * (Qᵀ *ᵥ v) i ^ 2 := by
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  rw [show Q = Qᵀᵀ by simp, dotProduct_transpose_mulVec]
  simp only [transpose_transpose, mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma matrixFiniteLaminate_quadratic_bounds {a b : ℝ} (ha : 0 < a)
    {A : Symmetric3} (hA : A ∈ matrixFiniteLaminate a b) (v : Coord3) :
    a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A.val *ᵥ v) ∧
      v ⬝ᵥ (A.val *ᵥ v) ≤ b * (v ⬝ᵥ v) := by
  obtain ⟨Q,hQ,d,hd,he⟩ := hA
  have hsq : ∑ i, (Qᵀ *ᵥ v) i ^ 2 = v ⬝ᵥ v := by
    simpa only [dotProduct,pow_two] using orthogonal_dotProduct ⟨by simpa using hQ.2,by simpa using hQ.1⟩ v v
  rw [he,conjugateDiagonal_quadratic,← hsq]
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hd.bounds ha i).1.le (sq_nonneg _)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hd.bounds ha i).2.le (sq_nonneg _)

lemma matrixFiniteLaminate_flux_bound {a b : ℝ} (ha : 0 < a)
    {A : Symmetric3} (hA : A ∈ matrixFiniteLaminate a b) (v : Coord3) :
    (A.val *ᵥ v) ⬝ᵥ (A.val *ᵥ v) ≤ b^2 * (v ⬝ᵥ v) := by
  obtain ⟨Q,hQ,d,hd,he⟩ := hA
  rw [he,← mulVec_mulVec,← mulVec_mulVec,orthogonal_dotProduct hQ]
  have hv := orthogonal_dotProduct (Q := Qᵀ) ⟨by simpa using hQ.2,by simpa using hQ.1⟩ v v
  rw [← hv]
  simp only [dotProduct,mulVec_diagonal,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hdi := hd.bounds ha i
  have hs : (d i)^2 ≤ b^2 := pow_le_pow_left₀ (ha.le.trans hdi.1.le) hdi.2.le 2
  nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ((Qᵀ *ᵥ v) i))]

abbrev FieldVector := EuclideanSpace ℝ (Fin 3 × Fin 2)

def fieldVector (E : Matrix (Fin 3) (Fin 2) ℝ) : FieldVector :=
  WithLp.toLp 2 (fun ij => E ij.1 ij.2)

lemma fieldVector_inner (E F : Matrix (Fin 3) (Fin 2) ℝ) :
    inner ℝ (fieldVector E) (fieldVector F) = ∑ j, E.col j ⬝ᵥ F.col j := by
  simp only [fieldVector,PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [col_apply]
  ring

lemma fieldVector_add (E F : Matrix (Fin 3) (Fin 2) ℝ) :
    fieldVector (E+F) = fieldVector E+fieldVector F := rfl

lemma fieldVector_smul (c : ℝ) (E : Matrix (Fin 3) (Fin 2) ℝ) :
    fieldVector (c • E) = c • fieldVector E := rfl

lemma fieldVector_quadratic_bounds {a b : ℝ} (ha : 0 < a)
    {A : Symmetric3} (hA : A ∈ matrixFiniteLaminate a b)
    (E : Matrix (Fin 3) (Fin 2) ℝ) :
    a * ‖fieldVector E‖^2 ≤ inner ℝ (fieldVector E) (fieldVector (A.val*E)) ∧
      inner ℝ (fieldVector E) (fieldVector (A.val*E)) ≤ b * ‖fieldVector E‖^2 := by
  rw [← real_inner_self_eq_norm_sq,fieldVector_inner,fieldVector_inner]
  change a * (∑ j, E.col j ⬝ᵥ E.col j) ≤ ∑ j, E.col j ⬝ᵥ (A.val *ᵥ E.col j) ∧
    (∑ j, E.col j ⬝ᵥ (A.val *ᵥ E.col j)) ≤ b * (∑ j, E.col j ⬝ᵥ E.col j)
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (matrixFiniteLaminate_quadratic_bounds ha hA (E.col j)).1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (matrixFiniteLaminate_quadratic_bounds ha hA (E.col j)).2

lemma fieldVector_flux_bound {a b : ℝ} (ha : 0 < a)
    {A : Symmetric3} (hA : A ∈ matrixFiniteLaminate a b)
    (E : Matrix (Fin 3) (Fin 2) ℝ) :
    ‖fieldVector (A.val*E)‖^2 ≤ b^2 * ‖fieldVector E‖^2 := by
  rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,fieldVector_inner,fieldVector_inner]
  change (∑ j, (A.val *ᵥ E.col j) ⬝ᵥ (A.val *ᵥ E.col j)) ≤ b^2 * (∑ j, E.col j ⬝ᵥ E.col j)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => matrixFiniteLaminate_flux_bound ha hA (E.col j)

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem assemble_global_corrections
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {I : Type*} [Fintype I] [DecidableEq I]
    (O : I → Set Coord3) (hO : ∀ i, IsOpen (O i))
    (hd : Pairwise (fun i j => Disjoint (O i) (O j)))
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (R : ∀ i, CompactGlobalUpdate μ (O i) u A) :
    ∃ (du : Coord3 → Fin 2 → ℝ) (dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) du ∧ HasCompactSupport du ∧ tsupport du ⊆ ⋃ i, O i ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) dF ∧ HasCompactSupport dF ∧ tsupport dF ⊆ ⋃ i, O i ∧
      (∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
        (∫ x, fderiv ℝ ψ x ((dF x).col j) ∂μ) = 0) ∧
      (∀ i, EqOn du (R i).du (O i) ∧ EqOn dF (R i).dF (O i) ∧
        ∀ x ∈ O i,
          fderiv ℝ (fun y => u y+du y) x = fderiv ℝ (fun y => u y+(R i).du y) x) ∧
      (∀ x ∉ ⋃ i, O i, du x = 0 ∧ dF x = 0) := by
  let du : Coord3 → Fin 2 → ℝ := fun x => ∑ i, (R i).du x
  let dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun x => ∑ i, (R i).dF x
  have heu : ∀ i, EqOn du (R i).du (O i) :=
    supported_sum_eq_on O hd (fun i => (R i).du) (fun i => (R i).support_du)
  have heF : ∀ i, EqOn dF (R i).dF (O i) :=
    supported_sum_eq_on O hd (fun i => (R i).dF) (fun i => (R i).support_dF)
  have hcdu : HasCompactSupport du := by
    simpa only [du, ← Finset.sum_apply] using
      (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => (R i).compact_du))
  have hcdF : HasCompactSupport dF := by
    simpa only [dF, ← Finset.sum_apply] using
      (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => (R i).compact_dF))
  refine ⟨du, dF, ContDiff.sum (fun i _ => (R i).smooth_du),
    hcdu,
    (tsupport_finite_sum_subset _).trans (iUnion_mono (fun i => (R i).support_du)),
    ContDiff.sum (fun i _ => (R i).smooth_dF),
    hcdF,
    (tsupport_finite_sum_subset _).trans (iUnion_mono (fun i => (R i).support_dF)), ?_, ?_, ?_⟩
  · exact finite_sum_cauchy_preserving μ (fun i => (R i).dF)
      (fun i => (R i).smooth_dF) (fun i => (R i).compact_dF) (fun i => (R i).cauchy_dF)
  · intro i
    refine ⟨heu i, heF i, ?_⟩
    intro x hx
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(hO i).mem_nhds hx] with y hy
    rw [heu i hy]
  · intro x hx
    exact ⟨supported_sum_eq_zero_off O _ (fun i => (R i).support_du) hx,
      supported_sum_eq_zero_off O _ (fun i => (R i).support_dF) hx⟩

end ScalarConductivity

end

end OAI
