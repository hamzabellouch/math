import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicFirstStructuredMoment
import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers

namespace OAI

/-! First structured moments on finitely many fixed output scales,
with the original logarithmically varying coordinate weights retained. -/
noncomputable section
open Set Filter
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ']

theorem first_scaled_structured_moment (hpub : PrimitiveResidueHeckeInput)
    (hperiod : CubicSupplementaryPeriodicity)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (σ : κ' → ℝ) (hσ : ∀ k, 0 < σ k)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ T : ℝ,
      ∀ (r : γ) (N : ℝ) (X : ι → ℝ) (v e : Eisenstein) (u : ℝ) (P Q : Finset Eisenstein),
      T ≤ L r → (L r)^(1-δ) ≤ N → N ≤ (L r)^(1+δ) →
      (∀ i, (2*L r)^c < X i) → (∀ i, X i ≤ L r) → v ≠ 0 → e ≠ 0 →
      norm v ≤ (L r)^δ → norm e ≤ (L r)^δ → |u| ≤ (L r)^(9/25:ℝ) →
      (∀ a ∈ P, gramDyad N a) → (∀ b ∈ Q, primary b ∧ norm b ≤ (L r)^δ) →
      ∀ k, (∑ b ∈ Q, ∑ a ∈ P,
        ‖structuredPrimeMoment a b v e u (W r) X V (σ k*L r)‖^2) ≤ (L r)^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,hraw⟩ := first_common_structured_exponents
    (γ := γ) (ι := ι) hpub hperiod (c := c/2) (by positivity) (by linarith)
    V hV hposV hsmV hVlo hVhi hVnorm hGI hGQ
  refine ⟨κ/2,by positivity,by linarith,ε/4,by positivity,?_⟩
  intro L W hL hW hWlo
  let s := ε/(16*((Fintype.card ι:ℝ)+1))
  have hs : 0 < s := by dsimp [s]; positivity
  let U : γ → ι → ℝ → ℂ := fun r i x => ((L r^(-s):ℝ):ℂ)*W r i x
  have hU : UniformLogWeights (fun z : γ × ι => U z.1 z.2) := by
    have heq : (fun z : γ × ι => U z.1 z.2) =
        normalizedLogWeight (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) s := by
      funext z x
      simp only [U,normalizedLogWeight,Complex.real_smul]
    rw [heq]
    exact hW.normalize hs
  obtain ⟨T₀,hbound⟩ := hraw U hU (fun r i x hx => by simp only [U,hWlo r i x hx,mul_zero])
  obtain ⟨T,hdata⟩ := eventually_atTop.mp (eventually_all.mpr (fun k =>
    eventually_fixed_scale_moment_bounds (hσ k) hκ hc hε T₀))
  have hsd : 2*(s*(Fintype.card ι:ℝ)) ≤ (ε/2)/2 := by
    have heq : s*(16*((Fintype.card ι:ℝ)+1)) = ε := by dsimp [s]; field_simp
    nlinarith
  refine ⟨max 1 T,?_⟩
  intro r N X v e u P Q hT hNlo hNhi hXlo hXhi hv he hvY heY hu hP hQ k
  have hY1 : 1 ≤ L r := hL r
  have hYp : 0 < L r := zero_lt_one.trans_le hY1
  have hd := hdata (L r) ((le_max_right _ _).trans hT) k
  have hb := hbound r (σ k*L r) N X v e u P Q hd.threshold hd.log_bound
    (hd.first_window.1.trans hNlo) (hNhi.trans hd.first_window.2)
    (fun i => hd.lower_bound.trans_lt (hXlo i)) (fun i => (hXhi i).trans hd.upper_bound)
    hv he (hvY.trans hd.small_bound) (heY.trans hd.small_bound)
    (hu.trans hd.height_bound) hP
    (fun b hb => ⟨(hQ b hb).1,(hQ b hb).2.trans hd.small_bound⟩)
  have hm : (∑ z ∈ Q ×ˢ P,
      ‖structuredPrimeMoment z.2 z.1 v e u (U r) X V (σ k*L r)‖^2) ≤ (L r)^(7/3-ε/2) := by
    have hb' : (∑ z ∈ Q ×ˢ P,
        ‖structuredPrimeMoment z.2 z.1 v e u (U r) X V (σ k*L r)‖^2) ≤ (σ k*L r)^(7/3-ε) := by
      simpa only [Finset.sum_product] using hb
    exact hb'.trans hd.saving_bound
  have hh := normalized_energy_transfer (Q ×ˢ P)
    (fun z => structuredPrimeMoment z.2 z.1 v e u (W r) X V (σ k*L r))
    (fun z => structuredPrimeMoment z.2 z.1 v e u (U r) X V (σ k*L r)) hY1
    (fun z _ => structuredPrimeMoment_log_scaling_base z.2 z.1 v e u (W r) X V
      (σ k*L r) hYp s) hm hsd
  have heq : ε/2/2 = ε/4 := by ring
  simpa only [Finset.sum_product,heq] using hh

end CubicFirstMoment

end

end OAI
