import OAI.NumberTheory.CubicMoment.Angular.AngularLatticeProfile

namespace OAI

/-! Uniform-in-translate Poisson estimates. A smooth plane function with
zero area has a small sum on every scaled Eisenstein coset. -/
noncomputable section
open MeasureTheory
open scoped BigOperators SchwartzMap
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem schwartz_dual_lattice_weighted_tail (F : 𝓢(ℂ,ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w ≠ 0 → ∀ c : Eisenstein → ℂ, (∀ h, ‖c h‖ ≤ 1) →
      ‖∑' h : Eisenstein, if h = 0 then 0 else c h*traceFourier F ((h:ℂ)/w)‖ ≤
        C*(Complex.normSq w)^2 := by
  obtain ⟨D,hD,hdecay⟩ := (traceFourierSchwartz F).decay 4 0
  simp only [norm_iteratedFDeriv_zero,traceFourierSchwartz_apply] at hdecay
  let R := ∑' h : Eisenstein, (norm h)^(-(2:ℝ))
  have hR : 0 ≤ R := tsum_nonneg (fun h => Real.rpow_nonneg (norm_nonneg h) _)
  refine ⟨D*R+1,by positivity,?_⟩
  intro w hw c hc
  have hwN : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have hs : Summable (fun h : Eisenstein => if h = 0 then (0:ℂ) else
      c h*traceFourier F ((h:ℂ)/w)) := by
    apply (traceFourier_summable_eisenstein F w hw).norm.of_norm_bounded
    intro h
    by_cases hh : h = 0
    · simp only [hh,ite_true,norm_zero]
      exact _root_.norm_nonneg _
    · simp only [hh,ite_false,norm_mul]
      exact mul_le_of_le_one_left (_root_.norm_nonneg _) (hc h)
  have hbound (h : Eisenstein) :
      ‖if h = 0 then (0:ℂ) else c h*traceFourier F ((h:ℂ)/w)‖ ≤
        D*(Complex.normSq w)^2*(norm h)^(-(2:ℝ)) := by
    by_cases hh : h = 0
    · simp only [ite_eq_left hh,norm_zero]
      exact mul_nonneg (mul_nonneg hD.le (sq_nonneg _))
        (Real.rpow_nonneg (norm_nonneg h) _)
    · rw [ite_eq_right hh,norm_mul]
      apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (hc h)).trans
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
    _ ≤ ∑' h : Eisenstein, ‖if h = 0 then (0:ℂ) else c h*traceFourier F ((h:ℂ)/w)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' h : Eisenstein, D*(Complex.normSq w)^2*(norm h)^(-(2:ℝ)) :=
      Summable.tsum_le_tsum hbound hs.norm
        ((summable_eisenstein_norm_rpow (s := 2) (by norm_num)).mul_left _)
    _ = D*R*(Complex.normSq w)^2 := by rw [tsum_mul_left]; dsimp [R]; ring
    _ ≤ (D*R+1)*(Complex.normSq w)^2 := by nlinarith [sq_nonneg (Complex.normSq w)]


/-- No arithmetic cancellation is assumed: the zero frequency vanishes
by the actual area identity, and the rest is Schwartz Fourier decay. -/
theorem schwartz_zero_area_coset_bound (F : 𝓢(ℂ,ℂ))
    (hF : (∫ z : ℂ, F z) = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℂ, q ≠ 0 → ∀ z : ℂ,
      ‖∑' a : Eisenstein, F (z+q*(a:ℂ))‖ ≤ K*Complex.normSq q := by
  obtain ⟨C,hC,hbound⟩ := schwartz_dual_lattice_weighted_tail F
  refine ⟨18*C/Real.sqrt 3,by positivity,?_⟩
  intro q hq z
  have hN : 0 < Complex.normSq q := Complex.normSq_pos.mpr hq
  have hw : q*traceLambda ≠ 0 := mul_ne_zero hq traceLambda_ne_zero
  let c : Eisenstein → ℂ := fun h =>
    (Real.fourierChar (tracePair z ((h:ℂ)/(q*traceLambda))) : ℂ)
  have hc : ∀ h, ‖c h‖ ≤ 1 := by intro h; simp [c]
  have hzero : c 0*traceFourier F ((0:ℂ)/(q*traceLambda)) = 0 := by
    simp [traceFourier_zero,hF]
  have he : (∑' h : Eisenstein, c h*traceFourier F ((h:ℂ)/(q*traceLambda))) =
      ∑' h : Eisenstein, if h = 0 then (0:ℂ) else c h*traceFourier F ((h:ℂ)/(q*traceLambda)) := by
    apply tsum_congr
    intro h
    by_cases hh : h = 0
    · subst h
      simpa using hzero
    · simp only [hh,ite_false]
  rw [poisson_eisenstein_coset F q hq z]
  change ‖(2/(Real.sqrt 3*Complex.normSq q):ℝ) •
    (∑' h : Eisenstein, c h*traceFourier F ((h:ℂ)/(q*traceLambda)))‖ ≤ _
  rw [he,norm_smul,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (hbound _ hw c hc) (by positivity)).trans_eq
  rw [Complex.normSq_mul,traceLambda_normSq]
  field_simp
  ring

end CubicFirstMoment

end

end OAI
