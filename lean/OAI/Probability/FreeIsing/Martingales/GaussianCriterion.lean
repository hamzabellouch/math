import OAI.Probability.FreeIsing.Conditioning.InnovationConditionalMoments
import OAI.Probability.FreeIsing.Estimates.CharacteristicRecurrence
import OAI.Probability.FreeIsing.Martingales.CharacteristicStep

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem integral_complex_test_martingale_increment_eq_zero
    {Ω ι : Type*} [Preorder ι] [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {W : ι → Ω → ℝ} (hW : Martingale W F P)
    {s t : ι} (hst : s ≤ t) {Z : Ω → ℂ}
    (hZ : StronglyMeasurable[F s] Z) (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    (∫ ω, Z ω * ((W t ω - W s ω : ℝ) : ℂ) ∂P) = 0 := by
  have hi := InnovationConditionalMoments.integral_smul_eq_integral_condExp_smul
    (F.le s) ((hW.integrable t).sub (hW.integrable s)) hZ hbound
  have hz := martingale_increment_condExp_subfiltration hW (fun _ => le_rfl) hst
  have he : (∫ ω, (W t ω - W s ω) • Z ω ∂P) = 0 := by
    change (∫ ω, (W t - W s) ω • Z ω ∂P) = 0
    rw [hi]
    calc
      _ = ∫ _ω : Ω, (0 : ℂ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hz] with ω hω
        rw [hω, zero_smul]
      _ = 0 := by simp
  simpa only [Complex.real_smul, mul_comm] using he

theorem integral_phase_increment_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → ℂ) (A B C : Ω → ℝ) (u : ℝ) :
    (∫ ω, (Z ω * Complex.exp (((u * (B ω - A ω) : ℝ) : ℂ) * Complex.I)) *
      Complex.exp (((u * (C ω - B ω) : ℝ) : ℂ) * Complex.I) ∂P) =
    ∫ ω, Z ω * Complex.exp (((u * (C ω - A ω) : ℝ) : ℂ) * Complex.I) ∂P := by
  congr 1
  funext ω
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem condExp_eq_const_of_bounded_complex_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℂ} (hX : Integrable X P) (c : ℂ)
    (htest : ∀ Z : Ω → ℂ, StronglyMeasurable[m] Z →
      (∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) →
      (∫ ω, Z ω * X ω ∂P) = c * ∫ ω, Z ω ∂P) :
    P[X | m] =ᵐ[P] fun _ => c := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hX
  · intro A hA hfin
    exact (integrable_const c).integrableOn
  · intro A hA hfin
    let Z : Ω → ℂ := A.indicator (fun _ => 1)
    have hZm : StronglyMeasurable[m] Z := stronglyMeasurable_const.indicator hA
    have hZb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1 := Filter.Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ A <;> simp [Z, hω]
    have ht := htest Z hZm hZb
    have hleft : (∫ ω, Z ω * X ω ∂P) = ∫ ω in A, X ω ∂P := by
      change (∫ ω, A.indicator (fun _ => (1 : ℂ)) ω * X ω ∂P) = _
      simp only [← Set.indicator_mul_left, one_mul]
      exact integral_indicator (hm A hA)
    have hright : c * (∫ ω, Z ω ∂P) = ∫ ω in A, c ∂P := by
      dsimp [Z]
      rw [integral_indicator (hm A hA)]
      simp [Complex.real_smul, mul_comm]
    rw [hleft, hright] at ht
    exact ht.symm
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem integral_characteristic_eq_gaussian_of_martingale_moments_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} (hW : Martingale W F P) (q : ℝ) (hq : 0 ≤ q)
    {M : ℝ} (hM : 0 ≤ M)
    (hD2 : ∀ a b : ℝ≥0, a ≤ b →
      Integrable (fun ω => (W b ω - W a ω) ^ 2) P)
    (hD3 : ∀ a b : ℝ≥0, a ≤ b →
      Integrable (fun ω => |W b ω - W a ω| ^ 3) P)
    (hthird : ∀ a b : ℝ≥0, a ≤ b →
      (∫ ω, |W b ω - W a ω| ^ 3 ∂P) ≤
        M * (((b : ℝ) - a) * Real.sqrt ((b : ℝ) - a) + ((b : ℝ) - a) ^ 3))
    (hvariance : ∀ a b : ℝ≥0, a ≤ b → ∀ Y : Ω → ℂ,
      StronglyMeasurable[F a] Y → (∀ᵐ ω ∂P, ‖Y ω‖ ≤ 1) →
      ‖∫ ω, Y ω * (((W b ω - W a ω : ℝ) : ℂ) ^ 2 - ((q * ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ)) ∂P‖ ≤
        M * (((b : ℝ) - a) * Real.sqrt ((b : ℝ) - a) + ((b : ℝ) - a) ^ 2))
    (s T : ℝ≥0) (u : ℝ) (Z : Ω → ℂ)
    (hZ : StronglyMeasurable[F s] Z) (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    (∫ ω, Z ω * Complex.exp (((u * (W (s + T) ω - W s ω) : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp ((-(u ^ 2 / 2 * q) * (T : ℝ) : ℝ) : ℂ) * ∫ ω, Z ω ∂P := by
  let z : ℝ → ℂ := fun r => ∫ ω, Z ω *
    Complex.exp (((u * (W (s + r.toNNReal) ω - W s ω) : ℝ) : ℂ) * Complex.I) ∂P
  have hz0 : z 0 = ∫ ω, Z ω ∂P := by simp [z]
  have hzT : z (T : ℝ) = ∫ ω, Z ω *
      Complex.exp (((u * (W (s + T) ω - W s ω) : ℝ) : ℂ) * Complex.I) ∂P := by simp [z]
  have hfinal := ExponentialTaylor.eq_gaussian_mul_of_local_error z
    (c := u ^ 2 / 2 * q) (T := (T : ℝ))
    (A := (4 * |u| ^ 3 + u ^ 2 / 2) * M)
    (B := u ^ 2 / 2 * M + u ^ 4 * q ^ 2 / 4) (C := 4 * |u| ^ 3 * M)
    (by positivity) T.coe_nonneg (by positivity) (by positivity) (by positivity) ?_
  · simpa only [hz0, hzT] using hfinal
  intro a b ha hab hb
  let ta : ℝ≥0 := s + a.toNNReal
  let tb : ℝ≥0 := s + b.toNNReal
  have hb0 : 0 ≤ b := ha.trans hab
  have hst : s ≤ ta := le_add_of_nonneg_right (bot_le : 0 ≤ a.toNNReal)
  have hatb : ta ≤ tb := add_le_add le_rfl (Real.toNNReal_mono hab)
  have hreal : (ta : ℝ) ≤ (tb : ℝ) := hatb
  have hdiff : (tb : ℝ) - ta = b - a := by
    simp [ta, tb, Real.toNNReal_of_nonneg ha, Real.toNNReal_of_nonneg hb0]
  let Y : Ω → ℂ := fun ω => Z ω *
    Complex.exp (((u * (W ta ω - W s ω) : ℝ) : ℂ) * Complex.I)
  have hYm : StronglyMeasurable[F ta] Y := by
    let : MeasurableSpace Ω := F ta
    have hZm : Measurable Z := (hZ.mono (F.mono hst)).measurable
    have hWam : Measurable (W ta) := (hW.stronglyMeasurable ta).measurable
    have hWsm : Measurable (W s) := ((hW.stronglyMeasurable s).mono (F.mono hst)).measurable
    apply Measurable.stronglyMeasurable
    dsimp [Y]
    fun_prop
  have hYbound : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ 1 := by
    filter_upwards [hbound] with ω hω
    simpa only [Y, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using hω
  have hstep := norm_integral_weighted_characteristic_gaussian_step_all_mul P Y
    (fun ω => W tb ω - W ta ω) u (v := q * ((tb : ℝ) - (ta : ℝ))) (mul_nonneg hq (sub_nonneg.mpr hreal))
    ((hYm.mono (F.le ta)).aestronglyMeasurable) hYbound
    (((hW.stronglyMeasurable tb).mono (F.le tb)).measurable.sub
      (((hW.stronglyMeasurable ta).mono (F.le ta)).measurable))
    ((hW.integrable tb).sub (hW.integrable ta)) (hD2 ta tb hatb) (hD3 ta tb hatb)
    (integral_complex_test_martingale_increment_eq_zero P hW hatb hYm hYbound)
  have hphase : (∫ ω, Y ω *
      Complex.exp (((u * (W tb ω - W ta ω) : ℝ) : ℂ) * Complex.I) ∂P) = z b :=
    integral_phase_increment_identity P Z (W s) (W ta) (W tb) u
  have hya : (∫ ω, Y ω ∂P) = z a := rfl
  rw [hphase, hya, hdiff] at hstep
  have hexp : -((u ^ 2 * (q * (b - a)) : ℝ) : ℂ) / 2 =
      ((-(u ^ 2 / 2 * q) * (b - a) : ℝ) : ℂ) := by push_cast; ring
  rw [hexp] at hstep
  apply hstep.trans
  have ht := hthird ta tb hatb
  have hv := hvariance ta tb hatb Y hYm hYbound
  rw [hdiff] at ht hv
  calc
    _ ≤ 4 * |u| ^ 3 * (M * ((b - a) * Real.sqrt (b - a) + (b - a) ^ 3)) +
        (u ^ 2 / 2) * (M * ((b - a) * Real.sqrt (b - a) + (b - a) ^ 2)) +
        u ^ 4 * (q * (b - a)) ^ 2 / 4 := by gcongr
    _ = _ := by ring

theorem integral_characteristic_eq_gaussian_of_martingale_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} (hW : Martingale W F P)
    {M : ℝ} (hM : 0 ≤ M)
    (hD2 : ∀ a b : ℝ≥0, a ≤ b →
      Integrable (fun ω => (W b ω - W a ω) ^ 2) P)
    (hD3 : ∀ a b : ℝ≥0, a ≤ b →
      Integrable (fun ω => |W b ω - W a ω| ^ 3) P)
    (hthird : ∀ a b : ℝ≥0, a ≤ b →
      (∫ ω, |W b ω - W a ω| ^ 3 ∂P) ≤
        M * (((b : ℝ) - a) * Real.sqrt ((b : ℝ) - a) + ((b : ℝ) - a) ^ 3))
    (hvariance : ∀ a b : ℝ≥0, a ≤ b → ∀ Y : Ω → ℂ,
      StronglyMeasurable[F a] Y → (∀ᵐ ω ∂P, ‖Y ω‖ ≤ 1) →
      ‖∫ ω, Y ω * (((W b ω - W a ω : ℝ) : ℂ) ^ 2 - (((b : ℝ) - (a : ℝ) : ℝ) : ℂ)) ∂P‖ ≤
        M * (((b : ℝ) - a) * Real.sqrt ((b : ℝ) - a) + ((b : ℝ) - a) ^ 2))
    (s T : ℝ≥0) (u : ℝ) (Z : Ω → ℂ)
    (hZ : StronglyMeasurable[F s] Z) (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    (∫ ω, Z ω * Complex.exp (((u * (W (s + T) ω - W s ω) : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp ((-(u ^ 2 / 2) * (T : ℝ) : ℝ) : ℂ) * ∫ ω, Z ω ∂P := by
  simpa only [mul_one, one_mul] using
    integral_characteristic_eq_gaussian_of_martingale_moments_rate P hW 1
      (by norm_num) hM hD2 hD3 hthird
      (by simpa only [one_mul] using hvariance) s T u Z hZ hbound

theorem condExp_characteristic_eq_gaussian_of_martingale_moments_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} (hW : Martingale W F P) (q : ℝ) (hq : 0 ≤ q)
    {M : ℝ} (hM : 0 ≤ M)
    (hD2 : ∀ a b : ℝ≥0, a ≤ b →
      Integrable (fun ω => (W b ω - W a ω) ^ 2) P)
    (hD3 : ∀ a b : ℝ≥0, a ≤ b →
      Integrable (fun ω => |W b ω - W a ω| ^ 3) P)
    (hthird : ∀ a b : ℝ≥0, a ≤ b →
      (∫ ω, |W b ω - W a ω| ^ 3 ∂P) ≤
        M * (((b : ℝ) - a) * Real.sqrt ((b : ℝ) - a) + ((b : ℝ) - a) ^ 3))
    (hvariance : ∀ a b : ℝ≥0, a ≤ b → ∀ Y : Ω → ℂ,
      StronglyMeasurable[F a] Y → (∀ᵐ ω ∂P, ‖Y ω‖ ≤ 1) →
      ‖∫ ω, Y ω * (((W b ω - W a ω : ℝ) : ℂ) ^ 2 - ((q * ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ)) ∂P‖ ≤
        M * (((b : ℝ) - a) * Real.sqrt ((b : ℝ) - a) + ((b : ℝ) - a) ^ 2))
    (s T : ℝ≥0) (u : ℝ) :
    P[(fun ω => Complex.exp
      (((u * (W (s + T) ω - W s ω) : ℝ) : ℂ) * Complex.I)) | F s] =ᵐ[P]
      fun _ => Complex.exp ((-(u ^ 2 / 2 * q) * (T : ℝ) : ℝ) : ℂ) := by
  have hm : Measurable (fun ω => Complex.exp
      (((u * (W (s + T) ω - W s ω) : ℝ) : ℂ) * Complex.I)) := by
    have hs : Measurable (W s) := ((hW.stronglyMeasurable s).mono (F.le s)).measurable
    have ht : Measurable (W (s + T)) :=
      ((hW.stronglyMeasurable (s + T)).mono (F.le (s + T))).measurable
    fun_prop
  have hi : Integrable (fun ω => Complex.exp
      (((u * (W (s + T) ω - W s ω) : ℝ) : ℂ) * Complex.I)) P := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω =>
      le_of_eq (Complex.norm_exp_ofReal_mul_I (u * (W (s + T) ω - W s ω)))
  apply condExp_eq_const_of_bounded_complex_tests P (F.le s) hi
  intro Z hZ hbound
  exact integral_characteristic_eq_gaussian_of_martingale_moments_rate P hW q hq
    hM hD2 hD3 hthird hvariance s T u Z hZ hbound

end Problem367

end

end OAI
