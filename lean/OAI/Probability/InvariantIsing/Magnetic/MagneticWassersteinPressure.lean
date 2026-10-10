import OAI.Probability.InvariantIsing.Magnetic.MagneticWassersteinPhysical
import OAI.Probability.InvariantIsing.Pressure.PhysicalPressureConcentration

namespace OAI

/-! Theorem7.1 for general W1 field laws, with mean and almost-sure convergence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem limiting_wasserstein_field_pressure
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (hU : ∀ N, Measurable (U N))
    (hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν))
    (field : (N : ℕ) → Fin N → ℝ) (ξ : ProbabilityMeasure ℝ)
    (hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ))
    (hw : Tendsto (fun k => fieldWassersteinOne (empiricalSpectralLaw (Nat.succ_pos k) (field (k+1))) ξ)
      atTop (𝓝 0)) :
    Tendsto (fun N => ∫ ω, rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (field N) ∂P)
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ)) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (field N))
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ)) := by
  refine ⟨physical_mean_wasserstein_field_pressure_tendsto hhaar hgauss hpub P U hU hHaar eig ν a b
    hcompact hbound ha hb hno hweak field ξ hξ hw,?_⟩
  have hab : a ≤ b := (hbound ha).2
  let clip := fun N (i : Fin N) => spectralClip a b (eig N i)
  have hcmean := physical_mean_wasserstein_field_pressure_tendsto hhaar hgauss hpub P U hU hHaar clip ν a b
    hcompact hbound ha hb (fun ε hε => Eventually.of_forall (fun N i => by
      have hh := spectralClip_mem hab (eig N i)
      constructor <;> linarith [hh.1,hh.2]))
    (spectral_clip_empirical_tendsto eig ν a b hbound hweak) field ξ hξ hw
  let K := |a|+|b|+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hclip N i : |clip N i| ≤ K := by
    have hh := spectralClip_mem hab (eig N i)
    rw [abs_le]
    dsimp [K]
    constructor <;> linarith [hh.1,hh.2,neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b]
  have hconc := ae_physical_pressure_sub_mean_tendsto_zero hhaar P
    (fun n => U (n+3)) (fun n => hU (n+3)) (fun n => hHaar (n+3))
    (fun n => clip (n+3)) (fun n => field (n+3)) K hK (fun n => hclip (n+3))
  have hη := (spectralExcess_tendsto eig a b hno).comp (tendsto_add_atTop_nat 3)
  filter_upwards [hconc] with ω hω
  have hclim := hω.add (hcmean.comp (tendsto_add_atTop_nat 3))
  have hd : Tendsto (fun n => rotatedPressure (eig (n+3)) (matrixRotation (U (n+3) ω)⁻¹)
      (field (n+3))-
      rotatedPressure (clip (n+3)) (matrixRotation (U (n+3) ω)⁻¹) (field (n+3)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (by simpa only [zero_div] using hη.div_const 2)
    intro n
    rw [Real.norm_eq_abs,abs_sub_comm]
    exact abs_rotatedPressure_sub_le (by omega) (clip (n+3)) (eig (n+3))
      (matrixRotation (U (n+3) ω)⁻¹) (field (n+3))
      (spectralExcess (eig (n+3)) a b)
      (fun i => spectralClip_close hab (spectralExcess_nonneg _ _ _) (spectralExcess_bounds _ _ _ i))
  apply (tendsto_add_atTop_iff_nat 3).mp
  have hh := hclim.add hd
  convert hh using 1
  · funext n
    dsimp only [Function.comp_apply]
    ring
  · simp only [zero_add,add_zero]

end InvariantIsing

end

end OAI
