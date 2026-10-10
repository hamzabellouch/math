import OAI.NumberTheory.CubicMoment.Angular.AngularWeightOperator
import OAI.NumberTheory.CubicMoment.Angular.AngularPrimaryLattice

namespace OAI

/-! The zero-area coset estimate with a constant chosen before the weight.
The common Fourier decay is derived by the continuous operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators SchwartzMap
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem schwartz_weighted_dual_bound (F : 𝓢(ℂ,ℂ)) {D : ℝ} (hD : 0 ≤ D)
    (hdecay : ∀ z : ℂ, ‖z‖^4*‖traceFourier F z‖ ≤ D)
    (w : ℂ) (hw : w ≠ 0) (c : Eisenstein → ℂ) (hc : ∀ h, ‖c h‖ ≤ 1) :
    ‖∑' h : Eisenstein, if h = 0 then 0 else c h*traceFourier F ((h:ℂ)/w)‖ ≤
      (D*(∑' h : Eisenstein, (norm h)^(-(2:ℝ)))+1)*(Complex.normSq w)^2 := by
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
      exact mul_nonneg (mul_nonneg hD (sq_nonneg _)) (Real.rpow_nonneg (norm_nonneg h) _)
    · rw [ite_eq_right hh,norm_mul]
      apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (hc h)).trans
      have hn : 0 < norm h := norm_pos_of_ne_zero hh
      have he : ‖(h:ℂ)/w‖^4 = (norm h)^2/(Complex.normSq w)^2 := by
        rw [show (4:ℕ) = 2*2 by norm_num,pow_mul,←Complex.normSq_eq_norm_sq,
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
    _ = D*(∑' h : Eisenstein, (norm h)^(-(2:ℝ)))*(Complex.normSq w)^2 := by
      rw [tsum_mul_left]
      ring
    _ ≤ _ := by nlinarith [sq_nonneg (Complex.normSq w)]

theorem UniformLogWeights.angular_coset_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ i q, q ≠ 0 → ∀ z : ℂ,
      ‖∑' a : Eisenstein, angularAnnulus ℓ (W i) (z+q*(a:ℂ))‖ ≤ K*Complex.normSq q := by
  obtain ⟨D,hD,hbound⟩ := h.angularFourier_seminorm ℓ 4 0
  let R := ∑' a : Eisenstein, (norm a)^(-(2:ℝ))
  have hR : 0 ≤ R := tsum_nonneg (fun a => Real.rpow_nonneg (norm_nonneg a) _)
  let C := D*R+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨18*C/Real.sqrt 3,by positivity,?_⟩
  intro i q hq z
  let F := angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i)
  have hd : ∀ w : ℂ, ‖w‖^4*‖traceFourier F w‖ ≤ D := by
    intro w
    have hh := SchwartzMap.le_seminorm ℝ 4 0 (traceFourierSchwartz F) w
    simp only [norm_iteratedFDeriv_zero,traceFourierSchwartz_apply] at hh
    exact hh.trans (hbound i)
  have hF : (∫ w : ℂ, F w) = 0 := integral_angularAnnulus_eq_zero hℓ (W i)
  have hN : 0 < Complex.normSq q := Complex.normSq_pos.mpr hq
  have hw : q*traceLambda ≠ 0 := mul_ne_zero hq traceLambda_ne_zero
  let c : Eisenstein → ℂ := fun a =>
    (Real.fourierChar (tracePair z ((a:ℂ)/(q*traceLambda))) : ℂ)
  have hc : ∀ a, ‖c a‖ ≤ 1 := by intro a; simp [c]
  have hzero : c 0*traceFourier F ((0:ℂ)/(q*traceLambda)) = 0 := by
    simp [traceFourier_zero,hF]
  have he : (∑' a : Eisenstein, c a*traceFourier F ((a:ℂ)/(q*traceLambda))) =
      ∑' a : Eisenstein, if a = 0 then (0:ℂ) else c a*traceFourier F ((a:ℂ)/(q*traceLambda)) := by
    apply tsum_congr
    intro a
    by_cases ha : a = 0
    · subst a
      simpa using hzero
    · simp only [ha,ite_false]
  change ‖∑' a : Eisenstein, F (z+q*(a:ℂ))‖ ≤ _
  rw [poisson_eisenstein_coset F q hq z]
  change ‖(2/(Real.sqrt 3*Complex.normSq q):ℝ) •
    (∑' a : Eisenstein,c a*traceFourier F ((a:ℂ)/(q*traceLambda)))‖ ≤ _
  rw [he,norm_smul,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (schwartz_weighted_dual_bound F hD.le hd _ hw c hc)
    (by positivity)).trans_eq
  rw [Complex.normSq_mul,traceLambda_normSq]
  dsimp [C,R]
  field_simp
  ring

theorem UniformLogWeights.primaryAngularLattice_decay {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ i Y, 0 < Y → ‖primaryAngularLattice ℓ (W i) Y‖ ≤ K/Y := by
  obtain ⟨C,hC,hbound⟩ := h.angular_coset_bound hℓ
  refine ⟨9*C,by positivity,?_⟩
  intro i Y hY
  let s : ℝ := 1/Real.sqrt Y
  have hs : 0 < s := by dsimp [s]; positivity
  have hq : (s:ℂ)*3 ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne') (by norm_num)
  have hn : Complex.normSq ((s:ℂ)*3) = 9/Y := by
    rw [Complex.normSq_mul,Complex.normSq_ofReal]
    norm_num
    dsimp [s]
    rw [one_div,←pow_two,inv_pow,Real.sq_sqrt hY.le]
    ring
  have he : primaryAngularLattice ℓ (W i) Y = ∑' u : PrimaryArgument,
      angularAnnulus ℓ (W i) ((s:ℂ)*(u:ℂ)) := by
    apply tsum_congr
    intro u
    exact (angularAnnulus_scaled ℓ (W i) hY u).symm
  rw [he,primary_scaled_coset]
  exact (hbound i _ hq _).trans_eq (by rw [hn]; ring)

end CubicFirstMoment

end

end OAI
