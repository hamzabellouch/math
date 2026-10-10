import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDamping
import OAI.NumberTheory.JointDickman.Analysis.ZetaContourBounds

namespace OAI

/-! # The total mass of damped prime reciprocals -/
namespace JointDickman
open Complex Finset

lemma dampedPrimeMass_le_log_zeta {σ : ℝ} (hσ : 1 < σ) :
    (∑' p : Nat.Primes, (p.val:ℝ)^(-σ)) ≤
      Real.log ‖riemannZeta (σ:ℂ)‖+primeEulerRemainderConstant := by
  let χ : DirichletCharacter ℂ 1 := 1
  have hs : 1 < (σ:ℂ).re := hσ
  have hlin : (primeCharacterLinearSum χ (σ:ℂ)).re =
      ∑' p : Nat.Primes, (p.val:ℝ)^(-σ) := by
    rw [primeCharacterLinearSum,Complex.re_tsum (primeCharacterLinearSum_summable χ hs)]
    apply tsum_congr
    intro p
    have hp := characterPrimePower_eq_phase χ σ 0 p
    have hpone : (p.val:ZMod 1) = 1 := Subsingleton.elim _ _
    simpa [characterPrimePhase,χ,hpone] using congrArg Complex.re hp
  have h := (abs_le.mp (primeCharacterLinearSum_re_error χ hs)).2
  rw [hlin] at h
  simpa using (show (∑' p : Nat.Primes, (p.val:ℝ)^(-σ)) ≤
    Real.log ‖χ.LFunction (σ:ℂ)‖+primeEulerRemainderConstant by linarith)

lemma dampedPrimeMass_log_bound : ∃ C : ℝ, ∀ X : ℝ, Real.exp 1 ≤ X →
    (∑' p : Nat.Primes, (p.val:ℝ)^(-(1+1/Real.log X))) ≤
      Real.log (Real.log X)+C := by
  obtain ⟨K,hK,hbound⟩ := zetaPole_compact_bound
  refine ⟨Real.log K+primeEulerRemainderConstant,?_⟩
  intro X hX
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog1 : 1 ≤ Real.log X := by
    simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hlog : 0 < Real.log X := by linarith
  let σ : ℝ := 1+1/Real.log X
  have hσ : 1 < σ := by dsimp [σ]; linarith [one_div_pos.mpr hlog]
  have hσ2 : σ ≤ 2 := by
    dsimp [σ]
    have := (div_le_one hlog).mpr hlog1
    linarith
  have hsne : (σ:ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re,Complex.one_re] at this
    linarith
  have hζ := hbound (σ:ℂ) (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0<σ)]; linarith) hsne
  have hnorm : ‖(σ:ℂ)-1‖ = 1/Real.log X := by
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by dsimp [σ]; positivity : 0<σ-1)]
    dsimp [σ]
    ring
  rw [hnorm] at hζ
  have hζ' : ‖riemannZeta (σ:ℂ)‖ ≤ K*Real.log X := by
    convert hζ using 1; field_simp
  have hz0 : 0 < ‖riemannZeta (σ:ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hσ)
  have hlogbound := Real.log_le_log hz0 hζ'
  rw [Real.log_mul hK.ne' hlog.ne'] at hlogbound
  have h := dampedPrimeMass_le_log_zeta hσ
  dsimp [σ] at h hlogbound
  linarith

lemma primeCutoff_mass_lower : ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
    Real.log (Real.log X)-C ≤ ∑ p ∈ primeCutoff X, (p.val:ℝ)⁻¹ := by
  obtain ⟨C,hC⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
  refine ⟨C,?_⟩
  intro X hX
  have h := (abs_le.mp (hC X hX)).1
  rw [primeCutoff_sum (fun p : ℕ => (p:ℝ)⁻¹),prime_filter_Icc_eq_Ioc]
  simp only [one_div] at h
  linarith

end JointDickman

end OAI
