import OAI.MeasureTheory.Falconer.Slicing.GaussianLocalBand
import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceMean
import OAI.MeasureTheory.Falconer.Slicing.GaussianRowDimension

namespace OAI

/-! # Positive band mass on uniformly controlled Gaussian row parameters -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

def gaussianRowNeighborhood (B : Fin h → Space (n+1)) (ε : ℝ) :
    Set (Fin h → Space (n+1)) := {A | ∀ i, ‖A i-B i‖ ≤ ε}

theorem gaussianRowNeighborhood_measurable (B : Fin h → Space (n+1)) (ε : ℝ) :
    MeasurableSet (gaussianRowNeighborhood B ε) := by
  simp only [gaussianRowNeighborhood,ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

theorem gaussianRows_controlled_band_lower (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1) {w : Space (n+1)} (hw : ‖w‖ = 1)
    {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hwB : ∀ i, |inner ℝ w (B i)| ≤ ρ) :
    ENNReal.ofReal ((gaussianLocalBandConstant n ρ*r)^h) ≤
      gaussianRows (n+1) h ({A | ∀ i, |inner ℝ w (A i)| ≤ r} ∩
        gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))) := by
  have he : {A : Fin h → Space (n+1) | ∀ i, |inner ℝ w (A i)| ≤ r} ∩
      gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)) =
      Set.pi univ (fun i => {x | ‖x-B i‖ ≤ (n+1:ℝ)*(2*ρ) ∧ |inner ℝ w x| ≤ r}) := by
    ext A
    simp only [mem_inter_iff,mem_ofPred_eq,gaussianRowNeighborhood,mem_pi,mem_univ,true_implies]
    constructor
    · rintro ⟨ha,hb⟩ i
      exact ⟨hb i,ha i⟩
    · intro ha
      exact ⟨fun i => (ha i).2,fun i => (ha i).1⟩
  rw [he,gaussianRows,Measure.pi_pi]
  calc
    _ = ∏ _ : Fin h, ENNReal.ofReal (gaussianLocalBandConstant n ρ*r) := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow]
      unfold gaussianLocalBandConstant gaussianVolumeNormalization
      positivity
    _ ≤ _ := Finset.prod_le_prod (fun i _ => gaussian_local_band_lower hw (hB i) hr hrρ hρ (hwB i))

theorem direction_band_first_moment {d : ℕ}
    (γ : Measure (Fin h → Space d)) [SFinite γ]
    (ν : Measure (Sphere d)) [SFinite ν] (r : ℝ) :
    (∫⁻ A : Fin h → Space d, ν (gaussianDirectionBand A r) ∂γ) =
      ∫⁻ w : Sphere d, γ {A | ∀ i, |inner ℝ (w:Space d) (A i)| ≤ r} ∂ν := by
  let S : Set ((Fin h → Space d) × Sphere d) :=
    {p | ∀ i, |inner ℝ (p.2:Space d) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall]
    exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  exact (Measure.prod_apply hS).symm.trans (Measure.prod_apply_symm hS)

theorem gaussian_controlled_direction_mean_lower (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1) (ν : Measure (Sphere (n+1))) [SFinite ν]
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ) :
    ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*ν univ ≤
      ∫⁻ A : Fin h → Space (n+1), gaussianDirectionMass ν r A
        ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))) := by
  simp only [gaussianDirectionMass]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,direction_band_first_moment]
  have hl : ENNReal.ofReal ((gaussianLocalBandConstant n ρ*r)^h)*ν univ ≤
      ∫⁻ w : Sphere (n+1), ((gaussianRows (n+1) h).restrict
        (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))))
        {A | ∀ i, |inner ℝ (w:Space (n+1)) (A i)| ≤ r} ∂ν := by
    rw [← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [hwB] with w hw
    rw [Measure.restrict_apply]
    · exact gaussianRows_controlled_band_lower B hB (sphere_norm w) hr.le hrρ hρ hw
    · simp only [ofPred_forall]
      exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  calc
    _ = ENNReal.ofReal (r^(-(h:ℝ)))*
        (ENNReal.ofReal ((gaussianLocalBandConstant n ρ*r)^h)*ν univ) := by
      rw [← mul_assoc,gaussian_band_normalization hr]
      unfold gaussianLocalBandConstant gaussianVolumeNormalization
      positivity
    _ ≤ _ := mul_le_mul_right hl _

end Falconer

end OAI
