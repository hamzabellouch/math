import OAI.NumberTheory.TotientAsymptotic.FullPrimeGrid
import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor
import OAI.NumberTheory.TotientAsymptotic.TailCofactor
import OAI.NumberTheory.TotientAsymptotic.Phase

namespace OAI

/-! The actual arithmetic mass has the required uniform cofactor envelope. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma P_tendsto : Tendsto P atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

lemma P_lt_self {H : ℕ} (hH : 2 ≤ H) : P H < H := by
  have hpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have h1 : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
  by_cases hlog : 0 ≤ Real.log (Real.log (H : ℝ))
  · have hp : (P H : ℝ) ≤ Real.log (Real.log (H : ℝ)) := Nat.floor_le hlog
    have hl := Real.log_le_self (Real.log_nonneg h1)
    have hh := Real.log_le_sub_one_of_pos hpos
    exact_mod_cast (show (P H : ℝ) < H by linarith)
  · have hp : P H=0 := Nat.floor_of_nonpos (le_of_lt (lt_of_not_ge hlog))
    omega

def fullPrimeFactor (C K : ℝ) (H : ℕ) : ℝ :=
  (1+bandPrimeError C (9/10) (P H))*Real.exp (simplexBoxTail 4 (P H))*
    projectedEnvelope K (P H)

lemma fullPrimeFactor_tendsto (C : ℝ) {K : ℝ} (hK : 0 < K) :
    Tendsto (fullPrimeFactor C K) atTop (nhds 0) := by
  have hb := (bandPrimeError_tendsto C (by norm_num : (0 : ℝ)<9/10)).comp P_tendsto
  have he := (Real.continuous_exp.tendsto (0 : ℝ)).comp
    ((simplexBoxTail_tendsto 4).comp P_tendsto)
  have hp := (summable_projectedEnvelope hK).tendsto_atTop_zero.comp P_tendsto
  have hh := (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hb).mul he).mul hp
  change Tendsto (fun H => (1+bandPrimeError C (9/10) (P H))*
    Real.exp (simplexBoxTail 4 (P H))*projectedEnvelope K (P H)) atTop (nhds 0)
  simpa only [Function.comp_def, add_zero, Real.exp_zero, one_mul, mul_zero] using hh

/-- The manuscript's mass upper estimate, for every weight bounded above by
one. Its only inputs are the published prime-box, renewal, and Mertens bounds. -/
theorem mass_upper (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput)
    (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ f : ℝ → ℝ, (∀ r, f r ≤ 1) →
        M x H f ≤ C*Real.exp ((4*(lam/rho))*cofactorScale H)*G x (m x) := by
  obtain ⟨C, hC, hcof⟩ := tail_cofactor_sum hmertens
  obtain ⟨Cp, hCp, hp⟩ := full_prime_mass_bound hbox
  obtain ⟨K, hK, hproj⟩ := uniform_projected_volume_bound hren
  refine ⟨C, hC, ?_⟩
  have hcut : ∀ᶠ H : ℕ in atTop, 4 ≤ lam*(P H : ℝ) := by
    exact ((tendsto_natCast_atTop_atTop.comp P_tendsto).const_mul_atTop lam_pos).eventually
      (eventually_ge_atTop (4 : ℝ))
  filter_upwards [eventually_ge_atTop 2, hcut,
    (fullPrimeFactor_tendsto Cp hK).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))]
      with H hH hcutH hfac
  have hPH := P_lt_self hH
  filter_upwards [theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)), inverse_scale_bound,
    hproj, m_tendsto.eventually (eventually_ge_atTop H)] with x hs hB hscale hpr hHm
  intro f hf
  have hL : 0 < L x H := by unfold L; omega
  have hPm : P H ≤ m x := hPH.le.trans hHm
  have hprime := hp hs.1 hcutH hB hscale hL
  have hG := (div_le_iff₀ (G_pos hB (m x))).mp (hpr (P H) hPm)
  have hcof' : (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹) ≤
      C*Real.exp ((4*(lam/rho))*cofactorScale H) := by
    have he : 4*(lam/rho)*(P H : ℝ)*(rho^(P H))⁻¹ =
        (4*(lam/rho))*cofactorScale H := by unfold cofactorScale; ring
    simpa only [he] using hcof H
  have hA : 0 ≤ (1+bandPrimeError Cp (9/10) (P H))*
      Real.exp (simplexBoxTail 4 (P H)) := mul_nonneg
    (by linarith [bandPrimeError_nonneg hCp.le (by norm_num : (0 : ℝ)<9/10) (P H)])
    (Real.exp_pos _).le
  calc
    _ ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ fullPrimeTuples x H, reciprocalShiftWeight p :=
      mass_le_cofactor_sum_mul_prime_sum hPH hHm hs f hf
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H))*
        ∑ p ∈ fullPrimeTuples x H, reciprocalShiftWeight p :=
      mul_le_mul_of_nonneg_right hcof'
        (Finset.sum_nonneg (fun p _ => reciprocalShiftWeight_nonneg p))
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H))*
        ((1+bandPrimeError Cp (9/10) (P H))*
          Real.exp (simplexBoxTail 4 (P H))*G x (L x H)) :=
      mul_le_mul_of_nonneg_left hprime (by positivity)
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H))*
        ((1+bandPrimeError Cp (9/10) (P H))*Real.exp (simplexBoxTail 4 (P H))*
          (projectedEnvelope K (P H)*G x (m x))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG hA) (by positivity)
    _ = (C*Real.exp ((4*(lam/rho))*cofactorScale H))*
        (fullPrimeFactor Cp K H*G x (m x)) := by unfold fullPrimeFactor; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_of_le_one_left (G_pos hB _).le hfac.le

end TotientAsymptotic

end

end OAI
