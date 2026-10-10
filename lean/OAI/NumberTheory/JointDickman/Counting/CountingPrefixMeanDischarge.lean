import OAI.NumberTheory.JointDickman.Counting.CountingPrefixMean
import OAI.NumberTheory.JointDickman.Counting.CountingModelMeanDischarge

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem counting_model_prefix_mean_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2)) (D : (Fin 4 →₀ ℕ) → ℕ)
    {η K : ℝ} (hη : 0 < η) (hK : 0 < K)
    (scale : ℕ → ℝ) (T H R M : ℕ → ℕ) (L : ℕ) (τ C : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hRT : Tendsto (fun B => (R B : ℝ)/(T B : ℝ)) atTop (𝓝 0))
    (hvalid : ∀ᶠ B in atTop, 0 < T B ∧ Real.log (T B) ≤ (B : ℝ)/10 ∧ η*T B ≤ H B)
    (hMpos : ∀ᶠ B in atTop, 0 < M B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ (σ : ℕ → ℝ), (∀ u, |σ u| ≤ 3) →
      let z := fun k => binLabel (fun j : Fin (J-1) => primeBin (scale n) J (j.val+1)) ζ k-μ
      (∑ u ∈ range ⌊K*T B*scale n⌋₊,
        |(complexEnergy (countingArithmeticKernel singularSeries P m B L
          (T B) (H B) (M B) u τ C c D (σ u))
          (fun i => z (u+(i.val+1)))).re|/(M B : ℝ))/(T B*scale n) < ε := by
  let f := fun (B n : ℕ) (σ : ℕ → ℝ) (u : ℕ) =>
    |(complexEnergy (countingArithmeticKernel singularSeries P m B L
      (T B) (H B) (M B) u τ C c D (σ u))
      (fun i => binLabel (fun j : Fin (J-1) => primeBin (scale n) J (j.val+1)) ζ
        (u+(i.val+1))-μ)).re|/(M B : ℝ)
  obtain ⟨V,hV,hbound⟩ := counting_model_uniform_energy_bound hM hMP P m hm c hc D hη
  obtain ⟨W,hW,hroot⟩ := independentRootMean_bounded hM
  have hcap : ∀ᶠ B in atTop, ∀ n σ, (∀ u, |σ u| ≤ 3) → ∀ u, f B n σ u ≤ V := by
    filter_upwards [hbound,hvalid,hMpos] with B hb hv hp
    intro n σ hσ u
    exact hb L (T B) (H B) (M B) u τ C (σ u) hv.1 hp hv.2.1 hv.2.2 (hσ u) _
      (fun i => norm_centered_binLabel_le_two _ ζ hζ μ hμ _)
  have hlocal (a : ℝ) (ha : 0 < a) := counting_model_energy_mean_proved hKMT hM hSD hSW hMP
    hJ ζ hζ μ hμ hmean P m hm c hc D hη (fun B => a*((T B : ℝ)+1)) scale T H R M L τ C
    (fun B => by positivity) hscale hR hRT hvalid hMpos hW.le (hroot.mono fun _ h => h L τ C)
  exact prefix_mean_from_scaled_intervals T scale (hvalid.mono fun _ h => h.1) hscale f hK hV
    (fun _ _ _ _ _ => by dsimp [f]; positivity) hcap hlocal

end JointDickman

end OAI
