import OAI.NumberTheory.JointDickman.Counting.CountingModelMean

namespace OAI

/-! # A pointwise bound for discarding a short initial interval -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem kernelCutNorm_le_of_lagEnvelope {M T : ℕ} (hM : 0 < M) (hT : 0 < T)
    {D : ℝ} (hD : 0 ≤ D) (K : Fin M → Fin M → ℝ)
    (hK : ∀ i k, |K i k| ≤ lagEnvelope T D i k) :
    kernelCutNorm K ≤ 2*D*Real.exp 24 := by
  apply (kernelCutNorm_le_absolute_mass K).trans
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  unfold kernelAbsoluteMass
  simp only [Fintype.card_fin]
  apply (div_le_iff₀ hMr).mpr
  calc
    _ ≤ ∑ i : Fin M, ∑ k : Fin M, lagEnvelope T D i k :=
      sum_le_sum (fun i _ => sum_le_sum (fun k _ => hK i k))
    _ ≤ ∑ _i : Fin M, 2*D*Real.exp 24 := sum_le_sum (fun i _ => lagEnvelope_row_sum hT hD i)
    _ = _ := by simp; ring

theorem counting_model_uniform_energy_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2))
    (D : (Fin 4 →₀ ℕ) → ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M u : ℕ) (τ C σ : ℝ),
      0 < T → 0 < M → Real.log (T : ℝ) ≤ (B : ℝ)/10 → η*T ≤ H → |σ| ≤ 3 →
      ∀ z : Fin M → ℂ, (∀ i, ‖z i‖ ≤ 2) →
      |(complexEnergy (countingArithmeticKernel singularSeries P m B L T H M u τ C c D σ) z).re|/(M : ℝ) ≤ K := by
  obtain ⟨V,hV,hbound⟩ := countingPrimeKernel_bounded hM hMP P m hm c hc D
  obtain ⟨R,hR,hroot⟩ := independentRootMean_bounded hM
  let E := R*V/η
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨32*E*Real.exp 24,by positivity,?_⟩
  filter_upwards [hbound,hroot] with B hb hr
  intro L T H M u τ C σ hT hMp hlog hH hσ z hz
  apply (complexEnergy_re_cutNorm_le M _ z hz).trans
  have hcut : kernelCutNorm (countingArithmeticKernel singularSeries P m B L T H M u τ C c D σ) ≤
      2*E*Real.exp 24 := by
    apply kernelCutNorm_le_of_lagEnvelope hMp hT hE
    intro i k
    exact countingSiteModel_uniform_envelope hMP P m B L T H M τ C c D hT hη hV
      (hr L τ C) hH (fun j _ _ => hb j T σ (by exact_mod_cast hT) hlog hσ) i k _ _
  exact (mul_le_mul_of_nonneg_left hcut (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring)

end JointDickman

end OAI
