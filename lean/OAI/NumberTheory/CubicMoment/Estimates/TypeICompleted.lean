import OAI.NumberTheory.CubicMoment.Transform.MetaplecticGrowthProvider
import OAI.NumberTheory.CubicMoment.Estimates.IdealEulerExclusion

namespace OAI

/-! The actual dyadic Type-I height mean, from the original smooth
Gauss sum. The residue and shifted integral are derived rather than
assumed. The estimate applies to one fixed smooth weight. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticSmoothSum_continuous (r : Eisenstein) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) {U : ℝ} (hU : 0 < U) :
    Continuous (metaplecticSmoothSum r W U) := by
  obtain ⟨B,_,hB⟩ := compactSupport_upper_cutoff W hW
  have hfin : {u : PrimaryArgument | norm u ≤ B*U}.Finite :=
    (finite_norm_le (B*U)).preimage Subtype.val_injective.injOn
  let S := hfin.toFinset
  have he (t : ℝ) : metaplecticSmoothSum r W U t =
      ∑ u ∈ S, (gauss (r*u)*(norm u:ℂ)^((t:ℂ)*Complex.I))*W (norm u/U) := by
    apply tsum_eq_sum
    intro u hu
    have huN : B*U < norm u := lt_of_not_ge (by simpa [S] using hu)
    rw [hB _ ((lt_div_iff₀ hU).mpr huN),mul_zero]
  have hc : Continuous (fun t : ℝ =>
      ∑ u ∈ S, (gauss (r*u)*(norm u:ℂ)^((t:ℂ)*Complex.I))*W (norm u/U)) := by
    apply continuous_finsetSum
    intro u hu
    have : NeZero (norm u:ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero (primary_ne_zero u.property)).ne'⟩
    exact (continuous_const.mul ((differentiable_const_cpow_of_neZero _).continuous.comp
      (Complex.continuous_ofReal.mul continuous_const))).mul continuous_const
  exact hc.congr (fun t => (he t).symm)

lemma dyadic_interval_decomposition_bound (f I P : ℝ → ℂ) (c : ℂ)
    (hI : Continuous I) (hP : Continuous P) (he : ∀ t, f t = c*I t+P t)
    {T H a b : ℝ} (hab : a ≤ b) (ha : -(2*T) ≤ a) (hb : b ≤ 2*T)
    (hPbound : ∀ t ∈ Icc a b, ‖P t‖ ≤ H) :
    (∫ t in a..b, ‖f t‖) ≤ ‖c‖*(∫ t in -(2*T)..(2*T), ‖I t‖)+(b-a)*H := by
  have hf : Continuous f := ((continuous_const.mul hI).add hP).congr (fun t => (he t).symm)
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab (hf.norm.intervalIntegrable _ _)
    (((continuous_const.mul hI.norm).add continuous_const).intervalIntegrable a b)
    (show ∀ t ∈ Icc a b, ‖f t‖ ≤ ‖c‖*‖I t‖+H from fun t ht => by
      rw [he t]
      exact (norm_add_le _ _).trans (by rw [norm_mul]; exact add_le_add le_rfl (hPbound t ht)))
  simp only [Pi.mul_apply,Pi.add_apply] at hm
  rw [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hm
  · have hsub := intervalIntegral.integral_mono_interval (μ := volume) ha hab hb
      (Filter.Eventually.of_forall (fun t => _root_.norm_nonneg (I t)))
      (hI.norm.intervalIntegrable (-(2*T)) (2*T))
    have hcn : 0 ≤ ‖c‖ := _root_.norm_nonneg c
    simp only [smul_eq_mul] at hm
    exact hm.trans (by nlinarith)
  · exact (continuous_const.mul hI.norm).intervalIntegrable _ _
  · exact continuous_const.intervalIntegrable _ _

lemma dyadic_decomposition_mean (f I P : ℝ → ℂ) (c : ℂ)
    (hI : Continuous I) (hP : Continuous P) (he : ∀ t, f t = c*I t+P t)
    {T H : ℝ} (hT : 0 < T) (hPbound : ∀ t : ℝ, T ≤ |t| → ‖P t‖ ≤ H) :
    ((∫ t in T..2*T, ‖f t‖)+(∫ t in -(2*T)..(-T), ‖f t‖))/T ≤
      2*‖c‖*((∫ t in -(2*T)..2*T, ‖I t‖)/T)+2*H := by
  have hp := dyadic_interval_decomposition_bound f I P c hI hP he
    (a := T) (b := 2*T) (by linarith) (by linarith) le_rfl (by
      intro t ht
      apply hPbound
      exact ht.1.trans (le_abs_self t))
  have hn := dyadic_interval_decomposition_bound f I P c hI hP he
    (a := -(2*T)) (b := -T) (by linarith) le_rfl (by linarith) (by
      intro t ht
      apply hPbound
      have := neg_le_abs t
      linarith [ht.2])
  apply (div_le_iff₀ hT).mpr
  have hcancel : (2*‖c‖*((∫ t in -(2*T)..2*T, ‖I t‖)/T)+2*H)*T =
      2*‖c‖*(∫ t in -(2*T)..2*T, ‖I t‖)+2*H*T := by field_simp
  rw [hcancel]
  linarith

/-- The actual zero-angular Type-I height estimate for one smooth
weight, uniform in the squarefree level and in U,T. The residue retains
its precise level decay. All analytic assumptions are published inputs. -/
theorem metaplectic_dyadic_height_of_published {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hGrowth : MetaplecticPolynomialGrowth F) (hHB : MetaplecticMeanSquare F)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1/12)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (D : ℕ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ U : ℝ, 1 ≤ U → ∀ T : ℝ, 1 ≤ T →
      ((∫ t in T..2*T, ‖metaplecticSmoothSum r W U t‖)+
       (∫ t in -(2*T)..(-T), ‖metaplecticSmoothSum r W U t‖))/T ≤
        C*U^(1/2+ε)*norm r^(1/4+2*ε)*Real.sqrt T+
        E*U^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D := by
  obtain ⟨C,hC,hmean⟩ := metaplectic_mellin_height_mean hF hHB hε hεsmall W hW hpos hsm
  obtain ⟨E,hE,hpole⟩ := metaplectic_mellin_pole_decay W hW hpos hsm D
  let c : ℂ := ((1/(2*Real.pi):ℝ):ℂ)
  have hc : c ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact one_div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  refine ⟨2*‖c‖*C,2*E,by positivity,by positivity,?_⟩
  intro r hr hs U hU T hT
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let I : ℝ → ℂ := fun t => ∫ v : ℝ,
    mellin W (((1/2+ε:ℝ):ℂ)+(v:ℂ)*Complex.I)*
      (U:ℂ)^(((1/2+ε:ℝ):ℂ)+(v:ℂ)*Complex.I)*
      F r (((1/2+ε:ℝ):ℂ)+((v-t):ℂ)*Complex.I)
  let P : ℝ → ℂ := fun t => metaplecticResidue r*
    (U:ℂ)^((5/6:ℝ)+(t:ℂ)*Complex.I)*mellin W ((5/6:ℝ)+(t:ℂ)*Complex.I)
  have he (t : ℝ) : metaplecticSmoothSum r W U t = c*I t+P t :=
    metaplectic_smooth_shift_of_polynomial hF hr hs (by linarith) (by linarith)
      (hGrowth r hr hs ε hε)
      W hW hpos hsm hU t
  have : NeZero (U:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hUp.ne'⟩
  have hPc : Continuous P := by
    have hm := (smooth_mellin_entire W hW hpos hsm.continuous).continuous
    have hu := (differentiable_const_cpow_of_neZero (U:ℂ)).continuous
    exact (continuous_const.mul (hu.comp (by fun_prop))).mul (hm.comp (by fun_prop))
  have hIc : Continuous I := by
    have hi (t : ℝ) : I t = c⁻¹*(metaplecticSmoothSum r W U t-P t) := by
      rw [he t,add_sub_cancel_right,← mul_assoc,inv_mul_cancel₀ hc,one_mul]
    exact (continuous_const.mul ((metaplecticSmoothSum_continuous r W hW hUp).sub hPc)).congr
      (fun t => (hi t).symm)
  let H : ℝ := E*U^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D
  have hrn : 0 ≤ norm r := norm_nonneg r
  have hpb (t : ℝ) (ht : T ≤ |t|) : ‖P t‖ ≤ H := by
    apply (hpole r hr U hUp t).trans
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hTp D)
      (pow_le_pow_left₀ hTp.le (by linarith [abs_nonneg t]) D)
  have hm : (∫ t in -(2*T)..(2*T), ‖I t‖)/T ≤
      C*U^(1/2+ε)*norm r^(1/4+2*ε)*Real.sqrt T := hmean r hr hs U hUp T hT
  have hd := dyadic_decomposition_mean (metaplecticSmoothSum r W U) I P c hIc hPc he hTp hpb
  apply hd.trans
  calc
    _ ≤ 2*‖c‖*(C*U^(1/2+ε)*norm r^(1/4+2*ε)*Real.sqrt T)+2*H := by
      exact add_le_add (mul_le_mul_of_nonneg_left hm
        (mul_nonneg (by norm_num) (_root_.norm_nonneg c))) le_rfl
    _ = _ := by dsimp [H]; ring

end CubicFirstMoment

end

end OAI
