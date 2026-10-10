import OAI.NumberTheory.CubicMoment.Estimates.NormSeries
import OAI.NumberTheory.CubicGram.PeriodicPoisson

namespace OAI

/-! A Poisson proof of the lattice approximation needed by the cubic profile. -/

noncomputable section
open scoped BigOperators SchwartzMap
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma traceLambda_normSq : Complex.normSq traceLambda = 3 := by
  rw [traceLambda_eq,Complex.normSq_mul,Complex.normSq_ofReal]
  norm_num [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]

/-- Rapid decay gives a uniform bound for the nonzero dual lattice. -/
theorem schwartz_dual_lattice_tail (F : 𝓢(ℂ,ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w ≠ 0 →
      ‖∑' h : Eisenstein, if h = 0 then 0 else traceFourier F ((h:ℂ)/w)‖ ≤
        C*(Complex.normSq w)^2 := by
  obtain ⟨D,hD,hdecay⟩ := (traceFourierSchwartz F).decay 4 0
  simp only [norm_iteratedFDeriv_zero,traceFourierSchwartz_apply] at hdecay
  let R := ∑' h : Eisenstein, (norm h)^(-(2:ℝ))
  have hR : 0 ≤ R := tsum_nonneg (fun h => Real.rpow_nonneg (norm_nonneg h) _)
  refine ⟨D*R+1,by positivity,?_⟩
  intro w hw
  have hwN : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have hs : Summable (fun h : Eisenstein => if h = 0 then (0:ℂ) else
      traceFourier F ((h:ℂ)/w)) := by
    apply (traceFourier_summable_eisenstein F w hw).norm.of_norm_bounded
    intro h
    by_cases hh : h = 0 <;> simp [hh]
  have hbound (h : Eisenstein) :
      ‖if h = 0 then (0:ℂ) else traceFourier F ((h:ℂ)/w)‖ ≤
        D*(Complex.normSq w)^2*(norm h)^(-(2:ℝ)) := by
    by_cases hh : h = 0
    · simp only [ite_eq_left hh,norm_zero]
      exact mul_nonneg (mul_nonneg hD.le (sq_nonneg _))
        (Real.rpow_nonneg (norm_nonneg h) _)
    · rw [ite_eq_right hh]
      have hn : 0 < norm h := norm_pos_of_ne_zero hh
      have he : ‖(h:ℂ)/w‖^4 = (norm h)^2/(Complex.normSq w)^2 := by
        rw [show (4:ℕ) = 2*2 by norm_num,pow_mul,← Complex.normSq_eq_norm_sq,
          Complex.normSq_div,div_pow]
        rfl
      have hd := hdecay ((h:ℂ)/w)
      rw [he] at hd
      rw [Real.rpow_neg hn.le,Real.rpow_ofNat]
      apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
      apply (div_le_iff₀ (sq_pos_of_pos hwN)).mp
      convert hd using 1
      ring
  calc
    _ ≤ ∑' h : Eisenstein, ‖if h = 0 then (0:ℂ) else traceFourier F ((h:ℂ)/w)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' h : Eisenstein, D*(Complex.normSq w)^2*(norm h)^(-(2:ℝ)) :=
      Summable.tsum_le_tsum hbound hs.norm
        ((summable_eisenstein_norm_rpow (s := 2) (by norm_num)).mul_left _)
    _ = D*R*(Complex.normSq w)^2 := by rw [tsum_mul_left]; dsimp [R]; ring
    _ ≤ (D*R+1)*(Complex.normSq w)^2 := by nlinarith [sq_nonneg (Complex.normSq w)]

lemma traceFourier_zero (F : ℂ → ℂ) : traceFourier F 0 = ∫ z : ℂ, F z := by
  simp [traceFourier,tracePair]

/-- The area-normalized lattice sum differs from its integral by O(s²).
This form is applied only to the fixed cubic Schwartz profile. -/
theorem schwartz_lattice_approximation (F : 𝓢(ℂ,ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s →
      ‖(∑' a : Eisenstein, F ((s:ℂ)*(a:ℂ))) -
        (2/(Real.sqrt 3*s^2):ℝ) • (∫ z : ℂ, F z)‖ ≤ C*s^2 := by
  obtain ⟨D,hD,hbound⟩ := schwartz_dual_lattice_tail F
  refine ⟨18*D/Real.sqrt 3,by positivity,?_⟩
  intro s hs
  have hsC : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hw : (s:ℂ)*traceLambda ≠ 0 := mul_ne_zero hsC traceLambda_ne_zero
  have hwN : Complex.normSq ((s:ℂ)*traceLambda) = 3*s^2 := by
    rw [Complex.normSq_mul,Complex.normSq_ofReal,traceLambda_normSq]
    ring
  have hp := poisson_eisenstein_coset F (s:ℂ) hsC 0
  simp [tracePair,Complex.normSq_ofReal] at hp
  simp only [← pow_two] at hp
  have ht := (traceFourier_summable_eisenstein F _ hw).tsum_eq_add_tsum_ite 0
  simp only [Eisenstein.coe_zero,zero_div,traceFourier_zero] at ht
  have hp' : (∑' a : Eisenstein, F ((s:ℂ)*(a:ℂ))) =
      (2/(Real.sqrt 3*s^2):ℝ) •
        (∑' h : Eisenstein, traceFourier F ((h:ℂ)/((s:ℂ)*traceLambda))) := by
    simpa only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_mul,
      Complex.ofReal_ofNat,Complex.ofReal_pow] using hp
  rw [hp',ht,smul_add,add_sub_cancel_left]
  rw [norm_smul,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (hbound _ hw) (by positivity)).trans_eq
  rw [hwN]
  field_simp
  ring

end CubicFirstMoment

end

end OAI
