import OAI.NumberTheory.JointDickman.Analysis.CharacterPolynomialDistance
import OAI.NumberTheory.JointDickman.Amplification.HalaszMeanLimit
import OAI.NumberTheory.JointDickman.Counting.NearCofactorWindow

namespace OAI

/-! # Nonprincipal-character cancellation for the actual cofactor -/
namespace JointDickman
open Finset Filter TwoPointCorrelations PublishedInputs
open scoped Topology

theorem character_count_window {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (E : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (N : ℕ) (a : ℝ), 1 ≤ a → K ≤ ⌊(N:ℝ)/a⌋₊ →
      ∀ f : ArithmeticFunction ℂ, f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p : ℕ, p.Prime → p ∉ E → (p:ℝ) ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^c → f p = χ p) →
      ∀ Q P : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
      ∀ t : ℝ, |t| ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^2 →
        ‖mrtCofactorPolynomial P (mrtMissingCoefficient f Q) N a t‖ ≤ ε := by
  obtain ⟨C,D,X₀,hC,_,hbound⟩ := halasz_local_count_window
  have hMsmall : ∀ᶠ M : ℝ in atTop, C*distanceError M < ε/2 := (tendsto_distanceError.const_mul C).eventually
    (eventually_lt_nhds (by simpa using (show 0 < ε/2 by positivity)))
  obtain ⟨M,hM,hMsmall⟩ := ((eventually_ge_atTop (0:ℝ)).and hMsmall).exists
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n : ℕ => C*(Real.log (Real.log (n:ℝ))/Real.log n))
      atTop (𝓝 0) := by
    have hh := (log_power_div_power_tendsto_zero 1 (by norm_num : (0:ℝ)<1)).comp hlog
    simpa only [Function.comp_def,Real.rpow_one,mul_zero] using hh.const_mul C
  have hheight : ∀ᶠ n : ℕ in atTop, (Real.log n)^8 ≤ (n:ℝ) := by
    have hh := ((log_power_div_power_tendsto_zero 8 (by norm_num : (0:ℝ)<1)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
    filter_upwards [hh,eventually_ge_atTop 1] with n hn hn1
    simp only [Function.comp_def,Real.rpow_one,Real.rpow_ofNat] at hn
    exact (div_le_one (by exact_mod_cast (show 0<n by omega))).mp hn
  have hevent := (tendsto_natCast_atTop_atTop.eventually
    (character_agreement_distance_polynomial χ hχ hc hc1 E 3 (by norm_num) (2*M+D))).and
    ((herr.eventually (eventually_lt_nhds (show 0<ε/2 by positivity))).and
    ((hlog.eventually (eventually_ge_atTop 1)).and hheight))
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp hevent
  let K := max K₀ (max ⌈X₀⌉₊ 3)
  refine ⟨K,by dsimp [K]; omega,?_⟩
  intro N a ha hm f hf hfb heq Q P hQ hP t hthi
  let m := ⌊(N:ℝ)/a⌋₊
  let n := ⌊(2*N:ℝ)/a⌋₊
  have hm3 : 3 ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have ha0 : 0 < a := by linarith
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have hx : 2 ≤ (N:ℝ)/a := hm2.trans (Nat.floor_le (by positivity))
  obtain ⟨_,hmn,_⟩ := mrt_cofactor_window_ratio N ha0 hx
  change m ≤ n at hmn
  have hnK : K₀ ≤ n := (le_max_left _ _).trans (hm.trans hmn)
  obtain ⟨hdis,herrn,hlogn,hheightn⟩ := hK₀ n hnK
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hm3.trans hmn
  have hmX : X₀ ≤ (m:ℝ) := (Nat.le_ceil X₀).trans (by
    exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hm))
  have hdist : ∀ v : ℝ, |v-t| ≤ (Real.log (n:ℝ))^8 →
      2*M+D ≤ squaredDistance f (mrtArchimedeanTwist v) n := by
    intro v hv
    have hvhi : |v| ≤ (n:ℝ)^(3:ℝ) := by
      have htri' : |v| ≤ |v-t|+|t| := by
        calc
          _ = |(v-t)+t| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      rw [Real.rpow_ofNat]
      change |t| ≤ (n:ℝ)^2 at hthi
      nlinarith
    rw [halasz_distance_eq]
    exact hdis f hfb heq v hvhi
  have hb := hbound N a ha hmX f hf.1
    (fun x y _ _ hxy => hf.2 hxy) (fun n _ => hfb n) Q P hQ hP t M hM hdist
  apply hb.trans
  dsimp only [distanceError] at hMsmall
  change C*(Real.log (Real.log (n:ℝ))/Real.log n) < ε/2 at herrn
  change _ ≤ C*((M+1)*Real.exp (-M)+Real.log (Real.log (n:ℝ))/Real.log n) at hb
  linarith

end JointDickman

end OAI
