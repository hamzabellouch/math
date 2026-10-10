import OAI.Probability.InvariantIsing.Cavity.CavityHaarSides
import OAI.Probability.InvariantIsing.Cavity.CavitySphereAverage
import OAI.Probability.InvariantIsing.Cavity.CavitySpinIsometry

namespace OAI

/-! A deterministic permutation of field sites preserves the physical Haar mean. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
namespace InvariantIsing

def fieldSitePermutation {N : ℕ} (p : Equiv.Perm (Fin N)) : Orthogonal N :=
  ⟨p.permMatrix ℝ, permutationMatrix_orthogonal p⟩

lemma spinVector_fieldSitePermutation {N : ℕ} (p : Equiv.Perm (Fin N)) (σ : Spin N) :
    spinVector (cavitySignedSpinPermutation p (fun _ => false) σ)=
      matrixRotation (fieldSitePermutation p) (spinVector σ) := by
  ext i
  change spinValue (σ (p i))=((p.permMatrix ℝ)*ᵥ (spinVector σ).ofLp) i
  rw [Matrix.permMatrix_mulVec]
  rfl

lemma rotatedPressure_fieldSitePermutation {N : ℕ} (p : Equiv.Perm (Fin N))
    (eig c : Fin N → ℝ) (U : Orthogonal N) :
    rotatedPressure eig (matrixRotation (U*(fieldSitePermutation p)⁻¹)) (fun i => c (p i))=
      rotatedPressure eig (matrixRotation U) c := by
  let e := cavitySignedSpinPermutation p (fun _ => false)
  have he (σ : Spin N) :
      rotatedEnergy eig (matrixRotation (U*(fieldSitePermutation p)⁻¹)) (e σ)=
        rotatedEnergy eig (matrixRotation U) σ := by
    have hv : matrixRotation (U*(fieldSitePermutation p)⁻¹) (spinVector (e σ))=
        matrixRotation U (spinVector σ) := by
      rw [spinVector_fieldSitePermutation, ← cavity_matrixRotation_mul_apply]
      simp only [inv_mul_cancel_right]
    simp only [rotatedEnergy,hv]
  have hc (σ : Spin N) : fieldEnergy (fun i => c (p i)) (e σ)=fieldEnergy c σ := by
    change (∑ i, c (p i)*spinValue (σ (p i)))=∑ i, c i*spinValue (σ i)
    exact Equiv.sum_comp p (fun i => c i*spinValue (σ i))
  let H := fun σ => Real.exp (rotatedEnergy eig (matrixRotation (U*(fieldSitePermutation p)⁻¹)) σ+
    fieldEnergy (fun i => c (p i)) σ)
  have hh : (∑ σ, H σ)=∑ σ, Real.exp (rotatedEnergy eig (matrixRotation U) σ+fieldEnergy c σ) := by
    rw [← Equiv.sum_comp e H]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [H]
    rw [he,hc]
  exact congrArg (fun x => (N : ℝ)⁻¹*Real.log ((Fintype.card (Spin N) : ℝ)⁻¹*x)) hh

lemma physical_meanPressure_field_permutation {N : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (p : Equiv.Perm (Fin N)) (eig c : Fin N → ℝ) :
    (∫ V, rotatedPressure eig (matrixRotation V⁻¹) (fun i => c (p i)) ∂μ)=
      ∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ := by
  let : μ.IsMulLeftInvariant := cavity_right_probability_left μ
  rw [← integral_mul_left_eq_self
    (fun V => rotatedPressure eig (matrixRotation V⁻¹) (fun i => c (p i)))
    (fieldSitePermutation p)]
  apply integral_congr_ae
  filter_upwards [] with V
  simp only [mul_inv_rev]
  exact rotatedPressure_fieldSitePermutation p eig c V⁻¹

end InvariantIsing

end

end OAI
