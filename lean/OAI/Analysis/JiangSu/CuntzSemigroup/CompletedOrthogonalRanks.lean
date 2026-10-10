import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.CuntzDenseMaps
import OAI.Analysis.JiangSu.TraceCone.MatrixBlockNorm
import OAI.Analysis.JiangSu.CStarAlgebras.CompletedRootRank

namespace OAI

noncomputable section


namespace Pureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal

section Unital
variable {E : Type*} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

lemma positive_nnrpow_nat_succ (a : E) (ha : 0 ≤ a) (n : ℕ) :
    CFC.nnrpow a ((n : ℝ≥0) + 1) = a ^ (n + 1) := by
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_add, pow_one, CFC.nnrpow_eq_pow] using CFC.nnrpow_one a ha
  | succ n ih =>
    have he : ((n + 1 : ℕ) : ℝ≥0) + 1 = ((n : ℝ≥0) + 1) + 1 := by
      simp only [Nat.cast_add, Nat.cast_one]
    rw [he, CFC.nnrpow_eq_pow, CFC.nnrpow_add (by positivity) (by positivity), CFC.nnrpow_one a ha]
    rw [← CFC.nnrpow_eq_pow, ih]
    exact (pow_succ a (n + 1)).symm

lemma positive_nnrpow_mem_hereditary (a : E) (ha : 0 ≤ a) (r : ℝ≥0) :
    CFC.nnrpow a r ∈ hereditaryCarrier a := by
  change CFC.nnrpow a r ∈ hereditarySubalgebra a ha
  rw [CFC.nnrpow_eq_pow, CFC.nnrpow_eq_cfcₙ_real a r ha]
  exact cfcₙ_mem _ (show a ∈ hereditarySubalgebra a ha from self_mem_hereditary a ha)

omit [PartialOrder E] [StarOrderedRing E] in
lemma orthogonal_add_pow_succ (a b : E) (hab : a * b = 0) (hba : b * a = 0) (n : ℕ) :
    (a + b) ^ (n + 1) = a ^ (n + 1) + b ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (a + b) (n + 1), ih, add_mul, mul_add, mul_add]
    have h1 : a ^ (n + 1) * b = 0 := by rw [pow_succ, mul_assoc, hab, mul_zero]
    have h2 : b ^ (n + 1) * a = 0 := by rw [pow_succ, mul_assoc, hba, mul_zero]
    rw [h1, h2, add_zero, zero_add, ← pow_succ, ← pow_succ]

lemma positive_reciprocal_power_add (a b : E) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a * b = 0) (j : ℕ) :
    CFC.nnrpow (a + b) (((j : ℝ≥0) + 1)⁻¹) =
      CFC.nnrpow a (((j : ℝ≥0) + 1)⁻¹) + CFC.nnrpow b (((j : ℝ≥0) + 1)⁻¹) := by
  let r : ℝ≥0 := ((j : ℝ≥0) + 1)⁻¹
  have hp : CFC.nnrpow a r * CFC.nnrpow b r = 0 :=
    hereditary_mul_eq_zero (positive_nnrpow_mem_hereditary a ha r)
      (positive_nnrpow_mem_hereditary b hb r) hab
  have hpa : 0 ≤ CFC.nnrpow a r := CFC.nnrpow_nonneg
  have hpb : 0 ≤ CFC.nnrpow b r := CFC.nnrpow_nonneg
  have hq : CFC.nnrpow b r * CFC.nnrpow a r = 0 := by
    simpa only [star_mul, hpa.star_eq, hpb.star_eq, star_zero] using congrArg star hp
  apply (CFC.nnrpow_inv_eq (a + b) _ (by positivity : (j : ℝ≥0) + 1 ≠ 0)
    (add_nonneg ha hb) (add_nonneg CFC.nnrpow_nonneg CFC.nnrpow_nonneg)).mpr
  rw [← CFC.nnrpow_eq_pow, positive_nnrpow_nat_succ _ (add_nonneg CFC.nnrpow_nonneg CFC.nnrpow_nonneg)]
  change (CFC.nnrpow a r + CFC.nnrpow b r) ^ (j + 1) = a + b
  rw [orthogonal_add_pow_succ _ _ hp hq j,
    ← positive_nnrpow_nat_succ _ hpa j, ← positive_nnrpow_nat_succ _ hpb j]
  simp only [r, CFC.nnrpow_eq_pow, CFC.nnrpow_nnrpow,
    inv_mul_cancel₀ (by positivity : (j : ℝ≥0) + 1 ≠ 0), CFC.nnrpow_one a ha, CFC.nnrpow_one b hb]
end Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completed_reciprocal_power_add (a b : CornerCompletion A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a * b = 0) (j : ℕ) :
    CFC.nnrpow (a + b) (((j : ℝ≥0) + 1)⁻¹) =
      CFC.nnrpow a (((j : ℝ≥0) + 1)⁻¹) + CFC.nnrpow b (((j : ℝ≥0) + 1)⁻¹) := by
  let φ := Unitization.inrNonUnitalStarAlgHom ℂ (CornerCompletion A)
  apply Unitization.inr_injective (R := ℂ)
  change φ (CFC.nnrpow (a + b) _) = φ (CFC.nnrpow a _ + CFC.nnrpow b _)
  rw [map_add, ← nonUnital_nnrpow_map φ Unitization.continuous_inr _ (add_nonneg ha hb) _ (by positivity),
    map_add, ← nonUnital_nnrpow_map φ Unitization.continuous_inr a ha _ (by positivity),
    ← nonUnital_nnrpow_map φ Unitization.continuous_inr b hb _ (by positivity)]
  exact positive_reciprocal_power_add _ _ (Unitization.inr_nonneg_iff.mpr ha)
    (Unitization.inr_nonneg_iff.mpr hb) (by rw [← Unitization.inr_mul, hab, Unitization.inr_zero]) j

theorem completedRootRank_add_orthogonal (τ : TracialState A) (a b : CornerCompletion A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = 0) :
    completedRootRank τ (a + b) = completedRootRank τ a + completedRootRank τ b := by
  apply tendsto_nhds_unique (completed_root_trace_tendsto_rank τ (a + b) (add_nonneg ha hb))
  convert (completed_root_trace_tendsto_rank τ a ha).add (completed_root_trace_tendsto_rank τ b hb) using 1
  funext j
  rw [completed_reciprocal_power_add a b ha hb hab j]
  exact completedDiagonalWeight_add τ (CFC.nnrpow a (((j : ℝ≥0) + 1)⁻¹))
    (CFC.nnrpow b (((j : ℝ≥0) + 1)⁻¹)) CFC.nnrpow_nonneg CFC.nnrpow_nonneg

end Pureness


namespace TraceCone
open Filter Topology
open scoped ENNReal NNReal CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma nonunital_reciprocal_power_add (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a*b=0) (j : ℕ) :
    CFC.nnrpow (a+b) (((j:ℝ≥0)+1)⁻¹)=
      CFC.nnrpow a (((j:ℝ≥0)+1)⁻¹)+CFC.nnrpow b (((j:ℝ≥0)+1)⁻¹) := by
  let φ := Unitization.inrNonUnitalStarAlgHom ℂ A
  apply Unitization.inr_injective (R := ℂ)
  change φ (CFC.nnrpow (a+b) _)=φ (CFC.nnrpow a _+CFC.nnrpow b _)
  rw [map_add, ← Pureness.nonUnital_nnrpow_map φ Unitization.continuous_inr _ (add_nonneg ha hb) _ (by positivity),
    map_add, ← Pureness.nonUnital_nnrpow_map φ Unitization.continuous_inr a ha _ (by positivity),
    ← Pureness.nonUnital_nnrpow_map φ Unitization.continuous_inr b hb _ (by positivity)]
  exact Pureness.positive_reciprocal_power_add _ _ (Unitization.inr_nonneg_iff.mpr ha)
    (Unitization.inr_nonneg_iff.mpr hb) (by rw [← Unitization.inr_mul,hab,Unitization.inr_zero]) j

namespace ExtendedTrace
lemma rank_add_orthogonal (τ : ExtendedTrace A) (a b : Positive A)
    (hab : a.1*b.1=0) : τ.rank (Positive.add a b)=τ.rank a+τ.rank b := by
  apply tendsto_nhds_unique (τ.tendsto_roots_rank_all (Positive.add a b))
  convert (τ.tendsto_roots_rank_all a).add (τ.tendsto_roots_rank_all b) using 1
  funext j
  have he : Positive.power (Positive.rootExponent j) (Positive.add a b)=
      Positive.add (Positive.power (Positive.rootExponent j) a) (Positive.power (Positive.rootExponent j) b) := by
    apply Subtype.ext
    simpa only [Positive.power,Positive.add,Positive.rootExponent,one_div] using
      nonunital_reciprocal_power_add a.1 b.1 a.2 b.2 hab j
  rw [he,τ.map_add]

@[simp] lemma rank_zero_positive (τ : ExtendedTrace A) : τ.rank Positive.zero=0 := by
  apply tendsto_nhds_unique (τ.tendsto_roots_rank_all Positive.zero)
  convert (tendsto_const_nhds (x := (0:ℝ≥0∞)) : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0)) using 1
  funext j
  have he : Positive.power (Positive.rootExponent j) (Positive.zero (A := A))=Positive.zero := by
    apply Subtype.ext
    exact CFC.zero_nnrpow
  rw [he,τ.map_zero]

lemma rank_matrixBlockPositive (τ : ExtendedTrace (MatrixLimit A)) (a b : Positive (MatrixLimit A)) :
    τ.rank (matrixBlockPositive a b)=τ.rank a+τ.rank b := by
  have he : matrixBlockPositive a b=Positive.add (Positive.map matrixEven a) (Positive.map matrixOdd b) := rfl
  rw [he,τ.rank_add_orthogonal _ _ (matrixEven_mul_matrixOdd a.1 b.1)]
  have hp (r : Fin 2) : τ.rank (Positive.map (matrixParity r) a)=τ.rank a :=
    congrArg τ.cuntzRank (matrixParity_cuntzClass r a)
  have hq (r : Fin 2) : τ.rank (Positive.map (matrixParity r) b)=τ.rank b :=
    congrArg τ.cuntzRank (matrixParity_cuntzClass r b)
  rw [show τ.rank (Positive.map matrixEven a)=τ.rank a by simpa [matrixParity] using hp 0,
      show τ.rank (Positive.map matrixOdd b)=τ.rank b by simpa [matrixParity] using hq 1]

def stabilizedCuntzRank (τ : ExtendedTrace (MatrixLimit A)) : CuntzClass (MatrixLimit A) →+ ℝ≥0∞ where
  toFun := τ.cuntzRank
  map_zero' := τ.rank_zero_positive
  map_add' x y := by
    induction x using Quotient.inductionOn with | h a =>
    induction y using Quotient.inductionOn with | h b =>
    exact τ.rank_matrixBlockPositive a b

@[simp] lemma stabilizedCuntzRank_mk (τ : ExtendedTrace (MatrixLimit A)) (a : Positive (MatrixLimit A)) :
    τ.stabilizedCuntzRank (CuntzClass.mk a)=τ.rank a := rfl

lemma stabilizedCuntzRank_monotone (τ : ExtendedTrace (MatrixLimit A)) : Monotone τ.stabilizedCuntzRank :=
  τ.cuntzRank.monotone
end ExtendedTrace
end TraceCone

end

end OAI
