import OAI.NumberTheory.CubicMoment.Angular.AngularUniformPoisson
import OAI.NumberTheory.CubicMoment.Estimates.RadialCubing

namespace OAI

/-! The actual area term in primary radial lattice summation. The
nonzero dual frequencies are bounded by the existing Schwartz estimate. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators SchwartzMap
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma integral_normSq_profile (W : ℝ → ℂ) :
    (∫ z : ℂ, W (Complex.normSq z)) = (Real.pi:ℂ)*(∫ x in Ioi (0:ℝ), W x) := by
  simp_rw [Complex.normSq_eq_norm_sq]
  rw [complex_radial_integral (fun r => W (r^2))]
  have hsub := integral_comp_rpow_Ioi W (show (2:ℝ) ≠ 0 by norm_num)
  have hh : (2:ℂ)*(∫ r in Ioi (0:ℝ), (r:ℂ)*W (r^2)) = ∫ x in Ioi (0:ℝ), W x := by
    rw [←integral_const_mul,←hsub]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2),show (2:ℝ)-1 = 1 by norm_num,Real.rpow_one,Real.rpow_two,
      Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  linear_combination (Real.pi:ℂ)*hh

theorem UniformLogWeights.radial_coset_error {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i q, q ≠ 0 → ∀ z : ℂ,
      ‖(∑' a : Eisenstein, W i (Complex.normSq (z+q*(a:ℂ))))-
        (2/(Real.sqrt 3*Complex.normSq q):ℝ) • (∫ w : ℂ, W i (Complex.normSq w))‖ ≤
        K*Complex.normSq q := by
  obtain ⟨D,hD,hbound⟩ := h.angularFourier_seminorm 0 4 0
  let R := ∑' a : Eisenstein, (norm a)^(-(2:ℝ))
  have hR : 0 ≤ R := tsum_nonneg (fun a => Real.rpow_nonneg (norm_nonneg a) _)
  let C := D*R+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨18*C/Real.sqrt 3,by positivity,?_⟩
  intro i q hq z
  let F := angularAnnulusSchwartz 0 (W i) (h.compact i) (h.positive i) (h.smooth i)
  have hF (w : ℂ) : F w = W i (Complex.normSq w) := by simp [F,angularAnnulusSchwartz,angularAnnulus,angularPlanePhase]
  have hd : ∀ w : ℂ, ‖w‖^4*‖traceFourier F w‖ ≤ D := by
    intro w
    have hh := SchwartzMap.le_seminorm ℝ 4 0 (traceFourierSchwartz F) w
    simp only [norm_iteratedFDeriv_zero,traceFourierSchwartz_apply] at hh
    exact hh.trans (hbound i)
  have hN : 0 < Complex.normSq q := Complex.normSq_pos.mpr hq
  have hw : q*traceLambda ≠ 0 := mul_ne_zero hq traceLambda_ne_zero
  let c : Eisenstein → ℂ := fun a =>
    (Real.fourierChar (tracePair z ((a:ℂ)/(q*traceLambda))) : ℂ)
  have hc : ∀ a, ‖c a‖ ≤ 1 := by intro a; simp [c]
  have hs : Summable (fun a : Eisenstein => c a*traceFourier F ((a:ℂ)/(q*traceLambda))) := by
    apply (traceFourier_summable_eisenstein F _ hw).norm.of_norm_bounded
    intro a
    rw [norm_mul]
    exact mul_le_of_le_one_left (_root_.norm_nonneg _) (hc a)
  have hzero : c 0*traceFourier F (((0:Eisenstein):ℂ)/(q*traceLambda)) = ∫ w : ℂ, F w := by
    simp [c,traceFourier_zero,tracePair]
  simp_rw [←hF]
  rw [poisson_eisenstein_coset F q hq z]
  change ‖(2/(Real.sqrt 3*Complex.normSq q):ℝ) •
    (∑' a : Eisenstein, c a*traceFourier F ((a:ℂ)/(q*traceLambda)))-
    (2/(Real.sqrt 3*Complex.normSq q):ℝ) • (∫ w : ℂ, F w)‖ ≤ _
  rw [hs.tsum_eq_add_tsum_ite 0,hzero,smul_add,add_sub_cancel_left,norm_smul,
    Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (schwartz_weighted_dual_bound F hD.le hd _ hw c hc)
    (by positivity)).trans_eq
  rw [Complex.normSq_mul,traceLambda_normSq]
  dsimp [C,R]
  field_simp
  ring

def primaryRadialMain (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ((2*Real.pi*Y/(9*Real.sqrt 3):ℝ):ℂ)*(∫ x in Ioi (0:ℝ), W x)

theorem UniformLogWeights.primaryRadialLattice_error {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i Y, 0 < Y →
      ‖primaryAngularLattice 0 (W i) Y-primaryRadialMain (W i) Y‖ ≤ K/Y := by
  obtain ⟨C,hC,hbound⟩ := h.radial_coset_error
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
  have he : primaryAngularLattice 0 (W i) Y =
      ∑' u : PrimaryArgument, W i (Complex.normSq ((s:ℂ)*(u:ℂ))) := by
    apply tsum_congr
    intro u
    simpa only [angularAnnulus,angularPlanePhase,zpow_zero,one_mul] using
      (angularAnnulus_scaled 0 (W i) hY u).symm
  rw [he,primary_scaled_coset (fun z : ℂ => W i (Complex.normSq z)) (s:ℂ)]
  have hb := hbound i _ hq (s:ℂ)
  rw [hn,integral_normSq_profile] at hb
  have hm : (2/(Real.sqrt 3*(9/Y)):ℝ) • ((Real.pi:ℂ)*(∫ x in Ioi (0:ℝ), W i x)) =
      primaryRadialMain (W i) Y := by
    rw [Complex.real_smul,primaryRadialMain]
    push_cast
    field_simp
  rw [hm] at hb
  exact hb.trans_eq (by ring)

end CubicFirstMoment

end

end OAI
