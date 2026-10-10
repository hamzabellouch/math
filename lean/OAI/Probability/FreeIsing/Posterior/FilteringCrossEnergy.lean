import OAI.Probability.FreeIsing.Estimates.ProgressivePrimitiveFubini
import OAI.Probability.FreeIsing.Stochastic.SimpleIntegralIsometry

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

namespace Problem367.FilteringCrossEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem integral_test_condExp [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Q H : Ω → ℝ}
    (hQ : Integrable Q P) (hH : StronglyMeasurable[m] H)
    (hHQ : Integrable (H * Q) P) :
    (∫ ω, H ω * P[Q | m] ω ∂P) = ∫ ω, H ω * Q ω ∂P := by
  have hp := condExp_mul_of_stronglyMeasurable_left hH hHQ hQ
  calc
    _ = ∫ ω, P[H * Q | m] ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hp] with ω hω
      exact hω.symm
    _ = _ := integral_condExp hm

theorem integrable_bounded_mul {Q H : Ω → ℝ} {A : ℝ}
    (hQ : Integrable Q P) (hH : AEStronglyMeasurable H P)
    (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A) :
    Integrable (fun ω => H ω * Q ω) P := by
  apply hQ.bdd_mul hH
  simpa only [Real.norm_eq_abs] using hHb

theorem integral_test_covariance [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Q S H a : Ω → ℝ} {A C : ℝ}
    (hQ : Integrable Q P) (hQS : Integrable (fun ω => Q ω * S ω) P)
    (hH : StronglyMeasurable[m] H) (ha : StronglyMeasurable[m] a)
    (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A) (hab : ∀ᵐ ω ∂P, |a ω| ≤ C) :
    (∫ ω, H ω * (P[(fun ω => Q ω * S ω) | m] ω -
      P[Q | m] ω * a ω) ∂P) =
      (∫ ω, Q ω * H ω * S ω ∂P) - ∫ ω, Q ω * H ω * a ω ∂P := by
  let : MeasurableSpace Ω := mΩ
  have hHm : AEStronglyMeasurable[mΩ] H P := (hH.mono hm).aestronglyMeasurable
  have hHam : AEStronglyMeasurable[mΩ] (fun ω => H ω * a ω) P :=
    ((hH.mul ha).mono hm).aestronglyMeasurable
  have hHab : ∀ᵐ ω ∂P, |H ω * a ω| ≤ A * C := by
    filter_upwards [hHb, hab] with ω hHω haω
    rw [abs_mul]
    exact mul_le_mul hHω haω (abs_nonneg _) ((abs_nonneg _).trans hHω)
  have hHK := integrable_bounded_mul
    (integrable_condExp (m := m) (f := fun ω => Q ω * S ω)) hHm hHb
  have hHMa := integrable_bounded_mul (integrable_condExp (m := m) (f := Q)) hHam hHab
  have hHQS := integrable_bounded_mul hQS hHm hHb
  have hHaQ := integrable_bounded_mul hQ hHam hHab
  calc
    _ = (∫ ω, H ω * P[(fun ω => Q ω * S ω) | m] ω ∂P) -
        ∫ ω, (H ω * a ω) * P[Q | m] ω ∂P := by
      rw [← integral_sub hHK hHMa]
      congr 1
      funext ω
      ring
    _ = (∫ ω, H ω * (Q ω * S ω) ∂P) -
        ∫ ω, (H ω * a ω) * Q ω ∂P := by
      have he := integral_test_condExp hm hQ (hH.mul ha) hHaQ
      simp only [Pi.mul_apply] at he
      rw [integral_test_condExp hm hQS hH hHQS, he]
    _ = _ := by
      congr 1 <;> apply integral_congr_ae <;>
        exact Eventually.of_forall (fun ω => by ring)

theorem integrable_weighted_process [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ} {H : Ω → ℝ} {A C : ℝ}
    (hm : IsStronglyProgressive F m) (hH : StronglyMeasurable H)
    (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A)
    (hmb : ∀ r, ∀ᵐ ω ∂P, |m r ω| ≤ C) (s t : ℝ≥0) :
    Integrable (fun p : ℝ × Ω => H p.2 * m p.1.toNNReal p.2)
      ((volume.restrict (Ioc (s : ℝ) (t : ℝ))).prod P) := by
  apply integrable_bounded_mul
    (integrable_nnreal_process_interval_of_progressive_bounded hm C hmb s t)
    (hH.comp_measurable measurable_snd).aestronglyMeasurable
  exact Measure.quasiMeasurePreserving_snd.ae hHb

theorem integral_weighted_primitive_increment [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ} {H : Ω → ℝ} {A C : ℝ}
    (hm : IsStronglyProgressive F m) (hH : StronglyMeasurable H)
    (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A)
    (hmb : ∀ r, ∀ᵐ ω ∂P, |m r ω| ≤ C)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, H ω * (nnrealTimePrimitive m t ω - nnrealTimePrimitive m s ω) ∂P) =
      ∫ r in (s : ℝ)..(t : ℝ), ∫ ω, H ω * m r.toNNReal ω ∂P := by
  have hinc := nnrealTimePrimitive_increment_ae hst
    (integrable_nnreal_process_interval_of_progressive_bounded hm C hmb 0 s)
    (integrable_nnreal_process_interval_of_progressive_bounded hm C hmb s t)
  have hi := integrable_weighted_process hm hH hHb hmb s t
  calc
    _ = ∫ ω, H ω * (∫ r in (s : ℝ)..(t : ℝ), m r.toNNReal ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [hinc] with ω hω
      rw [show nnrealTimePrimitive m t ω - nnrealTimePrimitive m s ω = _ from hω]
    _ = ∫ ω, (∫ r in (s : ℝ)..(t : ℝ), H ω * m r.toNNReal ω) ∂P := by
      simp only [intervalIntegral.integral_const_mul]
    _ = _ := by
      simp only [intervalIntegral.integral_of_le (show (s : ℝ) ≤ (t : ℝ) from hst)]
      exact (integral_integral_swap (f := fun (r : ℝ) (ω : Ω) =>
        H ω * m r.toNNReal ω) hi).symm

theorem integral_bounded_mul_martingale_increment_eq_zero [IsFiniteMeasure P]
    {G : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) {s t : ℝ≥0} (hst : s ≤ t)
    {H : Ω → ℝ} {A : ℝ} (hH : StronglyMeasurable[G s] H)
    (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A) :
    (∫ ω, H ω * (B t ω - B s ω) ∂P) = 0 := by
  have hD : Integrable (B t - B s) P := (hB.integrable t).sub (hB.integrable s)
  exact SimpleIntegral.integral_mul_eq_zero_of_condExp_eq_zero (G.le s) hH hD
    (integrable_bounded_mul hD (hH.mono (G.le s)).aestronglyMeasurable hHb)
    (martingale_increment_condExp_subfiltration hB (fun _ => le_rfl) hst)

def innovation (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ) (m : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  B t ω + (t : ℝ) * S ω - nnrealTimePrimitive m t ω

theorem integral_latent_mul_innovation_increment [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ r, F r ≤ G r)
    {Q S H : Ω → ℝ} {A C D : ℝ} {s t : ℝ≥0} (hst : s ≤ t)
    (hQ : StronglyMeasurable[G s] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : Integrable S P) (hSb : ∀ᵐ ω ∂P, |S ω| ≤ C)
    (hH : StronglyMeasurable[F s] H) (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A)
    (hm : IsStronglyProgressive F m)
    (hpost : ∀ r, m r =ᵐ[P] P[S | F r]) :
    (∫ ω, Q ω * H ω * (innovation B S m t ω - innovation B S m s ω) ∂P) =
      ∫ r in (s : ℝ)..(t : ℝ), ∫ ω, H ω *
        (P[(fun ω => Q ω * S ω) | F r.toNNReal] ω -
          P[Q | F r.toNNReal] ω * m r.toNNReal ω) ∂P := by
  have hQm : StronglyMeasurable Q := hQ.mono (G.le s)
  have hQint : Integrable Q P := by
    apply Integrable.of_bound hQm.aestronglyMeasurable D
    simpa only [Real.norm_eq_abs] using hQb
  have hQH : StronglyMeasurable[G s] (fun ω => Q ω * H ω) :=
    hQ.mul (hH.mono (hFG s))
  have hQHm : StronglyMeasurable (fun ω => Q ω * H ω) := hQH.mono (G.le s)
  have hQHb : ∀ᵐ ω ∂P, |Q ω * H ω| ≤ D * A := by
    filter_upwards [hQb, hHb] with ω hq hh
    rw [abs_mul]
    exact mul_le_mul hq hh (abs_nonneg _) ((abs_nonneg _).trans hq)
  have hmb := posterior_version_ae_abs_le hpost hSb
  have hQS := integrable_bounded_mul hS hQm.aestronglyMeasurable hQb
  have hQHS := integrable_bounded_mul hS hQHm.aestronglyMeasurable hQHb
  have hnoise := integral_bounded_mul_martingale_increment_eq_zero hB hst hQH hQHb
  have hnoiseInt := integrable_bounded_mul
    ((hB.integrable t).sub (hB.integrable s)) hQHm.aestronglyMeasurable hQHb
  have hprimInt (u : ℝ≥0) : Integrable (nnrealTimePrimitive m u) P :=
    nnrealTimePrimitive_integrable
      (integrable_nnreal_process_interval_of_progressive_bounded hm C hmb 0 u)
  have hprimProd := integrable_bounded_mul ((hprimInt t).sub (hprimInt s))
    hQHm.aestronglyMeasurable hQHb
  have htime := integrable_weighted_process hm hQHm hQHb hmb s t
  have htimeInt : IntervalIntegrable
      (fun r : ℝ => ∫ ω, (Q ω * H ω) * m r.toNNReal ω ∂P) volume s t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (s : ℝ) ≤ (t : ℝ) from hst)).mpr htime.integral_prod_left
  calc
    _ = (∫ ω, (Q ω * H ω) * (B t ω - B s ω) +
          ((t : ℝ) - (s : ℝ)) * ((Q ω * H ω) * S ω) -
          (Q ω * H ω) * (nnrealTimePrimitive m t ω - nnrealTimePrimitive m s ω) ∂P) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => by unfold innovation; ring)
    _ = ((t : ℝ) - (s : ℝ)) * (∫ ω, Q ω * H ω * S ω ∂P) -
        ∫ r in (s : ℝ)..(t : ℝ), ∫ ω, (Q ω * H ω) * m r.toNNReal ω ∂P := by
      have hh := integral_sub
        (hnoiseInt.add (hQHS.const_mul ((t : ℝ) - (s : ℝ)))) hprimProd
      have ha := integral_add hnoiseInt (hQHS.const_mul ((t : ℝ) - (s : ℝ)))
      simp only [Pi.add_apply, Pi.sub_apply] at hh ha
      rw [hh, ha, integral_const_mul, hnoise, zero_add,
        integral_weighted_primitive_increment hm hQHm hQHb hmb hst]
    _ = ∫ r in (s : ℝ)..(t : ℝ),
        ((∫ ω, Q ω * H ω * S ω ∂P) - ∫ ω, Q ω * H ω * m r.toNNReal ω ∂P) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const htimeInt,
        intervalIntegral.integral_const, smul_eq_mul]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hsr : s ≤ r.toNNReal := by
        have hr' : (s : ℝ) ≤ r := (uIcc_of_le (show (s : ℝ) ≤ (t : ℝ) from hst) ▸ hr).1
        simpa using Real.toNNReal_mono hr'
      exact (integral_test_covariance (F.le r.toNNReal) hQint hQS
        (hH.mono (F.mono hsr)) (hm.stronglyAdapted r.toNNReal) hHb (hmb r.toNNReal)).symm

theorem integral_terminal_posterior_mul_increment [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W F P) {Q H : Ω → ℝ} {A D : ℝ}
    (hQ : Integrable Q P) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    {s t T : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    (hH : StronglyMeasurable[F s] H) (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A) :
    (∫ ω, P[Q | F T] ω * H ω * (W t ω - W s ω) ∂P) =
      ∫ ω, Q ω * H ω * (W t ω - W s ω) ∂P := by
  have hHm : AEStronglyMeasurable H P := (hH.mono (F.le s)).aestronglyMeasurable
  have hQHb : ∀ᵐ ω ∂P, |Q ω * H ω| ≤ D * A := by
    filter_upwards [hQb, hHb] with ω hq hh
    rw [abs_mul]
    exact mul_le_mul hq hh (abs_nonneg _) ((abs_nonneg _).trans hq)
  have hi := integrable_bounded_mul ((hW.integrable t).sub (hW.integrable s))
    (hQ.aestronglyMeasurable.mul hHm) hQHb
  have hm : StronglyMeasurable[F T] (fun ω => H ω * (W t ω - W s ω)) :=
    (hH.mono (F.mono (hst.trans htT))).mul
      (((hW.stronglyAdapted t).mono (F.mono htT)).sub
        ((hW.stronglyAdapted s).mono (F.mono (hst.trans htT))))
  have hip : Integrable ((fun ω => H ω * (W t ω - W s ω)) * Q) P := by
    change Integrable (fun ω => (H ω * (W t ω - W s ω)) * Q ω) P
    simpa only [Pi.mul_apply, Pi.sub_apply, mul_assoc, mul_comm, mul_left_comm] using hi
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    integral_test_condExp (F.le T) hQ hm hip

theorem integral_posterior_mul_innovation_increment [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ r, F r ≤ G r)
    {Q S H : Ω → ℝ} {A C D : ℝ} {s t T : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T)
    (hQ : StronglyMeasurable[G s] Q) (hQb : ∀ᵐ ω ∂P, |Q ω| ≤ D)
    (hS : Integrable S P) (hSb : ∀ᵐ ω ∂P, |S ω| ≤ C)
    (hX : StronglyAdapted F (fun r ω => B r ω + (r : ℝ) * S ω))
    (hH : StronglyMeasurable[F s] H) (hHb : ∀ᵐ ω ∂P, |H ω| ≤ A)
    (hm : IsStronglyProgressive F m)
    (hpost : ∀ r, m r =ᵐ[P] P[S | F r]) :
    (∫ ω, P[Q | F T] ω * H ω *
      (innovation B S m t ω - innovation B S m s ω) ∂P) =
      ∫ r in (s : ℝ)..(t : ℝ), ∫ ω, H ω *
        (P[(fun ω => Q ω * S ω) | F r.toNNReal] ω -
          P[Q | F r.toNNReal] ω * m r.toNNReal ω) ∂P := by
  have hQint : Integrable Q P := by
    apply Integrable.of_bound (hQ.mono (G.le s)).aestronglyMeasurable D
    simpa only [Real.norm_eq_abs] using hQb
  have hW : Martingale (innovation B S m) F P :=
    compensated_observation_martingale_of_bounded_signal hB hFG hS hX hm hpost C hSb
  rw [integral_terminal_posterior_mul_increment hW hQint hQb hst htT hH hHb]
  exact integral_latent_mul_innovation_increment hB hFG hst hQ hQb hS hSb hH hHb hm hpost

end Problem367.FilteringCrossEnergy

end

end OAI
