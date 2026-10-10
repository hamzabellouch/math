import OAI.MathematicalPhysics.Boltzmann.Branching.AeWindowPatching
import OAI.MathematicalPhysics.Boltzmann.Branching.DatumBounds
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum
import OAI.MathematicalPhysics.Boltzmann.Jets.JetProfiles
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

section

/-! # The integrable square of the cold annular time envelope -/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.AnnularEnvelope

theorem time_square_continuous {s T : ℝ} (hs : 0 < s) (_hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => s^2/(t+s)^2) (Icc 0 T) := by
  apply continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow 2)
  intro t ht
  apply pow_ne_zero
  change t+s ≠ 0
  linarith [ht.1]

theorem time_square_integral {s T : ℝ} (hs : 0 < s) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, s^2/(t+s)^2) = s-s^2/(T+s) := by
  have hi : IntervalIntegrable (fun t : ℝ => s^2/(t+s)^2) volume 0 T :=
    (time_square_continuous hs hT).intervalIntegrable_of_Icc hT
  have hd (t : ℝ) (ht : t ∈ uIcc 0 T) :
      HasDerivAt (fun t : ℝ => -(s^2)/(t+s)) (s^2/(t+s)^2) t := by
    have ht0 : 0 ≤ t := ((uIcc_of_le hT) ▸ ht).1
    have hn : t+s ≠ 0 := by linarith
    have ha : HasDerivAt (fun u : ℝ => u+s) 1 t := (hasDerivAt_id t).add_const s
    have hb : HasDerivAt (fun _ : ℝ => -(s^2)) 0 t := hasDerivAt_const t _
    simpa only [zero_mul,mul_one,zero_sub,neg_neg] using hb.fun_div ha hn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp only [zero_add]
  field_simp
  ring

theorem time_square_integral_le {s T : ℝ} (hs : 0 < s) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, s^2/(t+s)^2) ≤ s := by
  rw [time_square_integral hs hT]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by linarith))

theorem annular_square_summable {s₀ η T : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hT : 0 ≤ T) : Summable (fun j : ℕ =>
      ∫ t in (0:ℝ)..T, (DatumBounds.scale s₀ η j)^2/(t+DatumBounds.scale s₀ η j)^2) := by
  have hn (j : ℕ) : 0 ≤ ∫ t in (0:ℝ)..T,
      (DatumBounds.scale s₀ η j)^2/(t+DatumBounds.scale s₀ η j)^2 :=
    intervalIntegral.integral_nonneg hT (fun t _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hb (j : ℕ) : (∫ t in (0:ℝ)..T,
      (DatumBounds.scale s₀ η j)^2/(t+DatumBounds.scale s₀ η j)^2) ≤ DatumBounds.scale s₀ η j :=
    time_square_integral_le (DatumBounds.scale_pos hs₀ j) hT
  have hs : Summable (fun j : ℕ => DatumBounds.scale s₀ η j) := by
    simpa only [pow_one] using DatumBounds.summable_scale_pow s₀ hη 1 (by norm_num)
  exact Summable.of_nonneg_of_le hn hb hs


end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # Uniform short annular growth patches to all sufficiently late multiplicative windows -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.GrowthContradiction

theorem annular_to_late_growth (m : ℝ → ℝ≥0∞) {κ K A₀ L : ℝ}
    (hκ : 0 < κ) (hK : 0 < K) (hA₀ : 0 < A₀) (hbase : 15360*A₀ ≤ K)
    (hloc : ∀ b W : ℝ, 0 < b → 0 < W → W ≤ κ*b/200 → L+6*W < κ*b/2 →
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo b (b+W) → t ∈ Ioo b (b+W) →
        (8*κ*A₀/K)*s ≤ t-s → t-s ≤ (16*κ*A₀/K)*s → 6*m s ≤ m t) :
    ∃ R : ℝ, 0 < R ∧ let δ := 8*κ*A₀/K;
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, R < s →
        t ∈ Ioo ((1+δ)*s) ((1+2*δ)*s) → 6*m s ≤ m t := by
  let R := max 1 (4*L/κ)
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨R,hR,?_⟩
  dsimp only
  let δ := 8*κ*A₀/K
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : 2*δ < κ/200 := by
    rw [show 2*δ = 16*κ*A₀/K by dsimp [δ]; ring]
    apply (div_lt_iff₀ hK).mpr
    have hh := mul_le_mul_of_nonneg_left hbase hκ.le
    nlinarith [mul_pos hκ hK]
  have hlocal : ∀ b : ℚ, ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      R < (b:ℝ) → s ∈ Ioo (b:ℝ) ((1+κ/200)*(b:ℝ)) →
      t ∈ Ioo (b:ℝ) ((1+κ/200)*(b:ℝ)) →
      (δ*s ≤ t-s → t-s ≤ 2*δ*s → 6*m s ≤ m t) := by
    intro b
    by_cases hbR : R < (b:ℝ)
    · have hb : 0 < (b:ℝ) := hR.trans hbR
      let W := κ*(b:ℝ)/200
      have hW : 0 < W := by dsimp [W]; positivity
      have heq : (b:ℝ)+W = (1+κ/200)*(b:ℝ) := by dsimp [W]; ring
      have hcut : L+6*W < κ*(b:ℝ)/2 := by
        have hh : 4*L/κ < (b:ℝ) := (le_max_right _ _).trans_lt hbR
        have hh' := (div_lt_iff₀ hκ).mp hh
        dsimp [W]
        nlinarith [mul_pos hκ hb]
      have hh := hloc (b:ℝ) W hb hW le_rfl hcut
      filter_upwards [hh] with s hs
      filter_upwards [hs] with t ht
      intro _ hsw htw hlo hhi
      rw [← heq] at hsw htw
      apply ht hsw htw hlo
      simpa only [show 2*δ = 16*κ*A₀/K by dsimp [δ]; ring] using hhi
    · exact ae_of_all _ (fun _ => ae_of_all _ (fun _ h => False.elim (hbR h)))
  have hp := ae_patch_multiplicative_windows (div_pos hκ (by norm_num)) hlocal
  filter_upwards [hp] with s hs
  filter_upwards [hs] with t ht
  intro hRs htime
  have hspos : 0 < s := hR.trans hRs
  have hst : s < t := by nlinarith [mul_pos hδ hspos,htime.1]
  have htu : t < (1+κ/200)*s :=
    htime.2.trans (mul_lt_mul_of_pos_right (by linarith) hspos)
  apply ht hRs hst htu <;> nlinarith [htime.1,htime.2]

end BoltzmannNonuniqueness.GrowthContradiction

end

end

section

/-! # Disjoint radial annuli and their scale-uniform area bounds -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.AnnularEnvelope

def shell (s₀ η : ℝ) (j : ℕ) : Set Transverse :=
  {y | jetScale s₀ η j < ‖y‖ ∧ ‖y‖ < Real.exp η*jetScale s₀ η j}

theorem shell_measurable (s₀ η : ℝ) (j : ℕ) : MeasurableSet (shell s₀ η j) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

theorem shell_disjoint {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    {i j : ℕ} (hij : i ≠ j) : Disjoint (shell s₀ η i) (shell s₀ η j) := by
  apply disjoint_left.mpr
  intro y hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have ho := ordered_annuli hs₀ hη h
    exact not_lt_of_ge ho (hi.1.trans hj.2)
  · have ho := ordered_annuli hs₀ hη h
    exact not_lt_of_ge ho (hj.1.trans hi.2)

theorem shell_subset_ball (s₀ η : ℝ) (j : ℕ) :
    shell s₀ η j ⊆ ball 0 (Real.exp η*jetScale s₀ η j) := by
  intro y hy
  exact (mem_ball_zero_iff).mpr hy.2

theorem shell_finite (s₀ η : ℝ) (j : ℕ) : volume (shell s₀ η j) < ⊤ :=
  (measure_mono (shell_subset_ball s₀ η j)).trans_lt (measure_ball_lt_top ..)

theorem shell_area_le {s₀ η : ℝ} (hs₀ : 0 < s₀) (hηmax : η ≤ Real.log 2) (j : ℕ) :
    volume.real (shell s₀ η j) ≤ 4*Real.pi*(jetScale s₀ η j)^2 := by
  have hs : 0 ≤ jetScale s₀ η j := (DatumBounds.scale_pos hs₀ _).le
  have h := measureReal_mono (μ := (volume : Measure Transverse)) (shell_subset_ball s₀ η j)
  rw [TransverseDisk.disk_volume_real 0 (mul_nonneg (Real.exp_pos η).le hs)] at h
  have he : Real.exp η ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ) < 2)] using Real.exp_le_exp.mpr hηmax
  have hp := mul_le_mul_of_nonneg_right he hs
  have hsq : (Real.exp η*jetScale s₀ η j)^2 ≤ (2*jetScale s₀ η j)^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hp
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hsq Real.pi_pos.le])

def term (s₀ η : ℝ) (j : ℕ) (t : ℝ) (y : Transverse) : ℝ :=
  (shell s₀ η j).indicator (fun _ => 1/(t+jetScale s₀ η j)) y

def finiteEnvelope (s₀ η : ℝ) (s : Finset ℕ) (t : ℝ) (y : Transverse) : ℝ :=
  ∑ j ∈ s, term s₀ η j t y

theorem term_measurable (s₀ η : ℝ) (j : ℕ) :
    Measurable (fun u : ℝ × Transverse => term s₀ η j u.1 u.2) := by
  have he : (fun u : ℝ × Transverse => term s₀ η j u.1 u.2) =
      ((Prod.snd ⁻¹' shell s₀ η j).indicator (fun u => 1/(u.1+jetScale s₀ η j))) := by
    funext u
    by_cases h : u.2 ∈ shell s₀ η j <;> simp [term,h]
  rw [he]
  exact (measurable_const.div (measurable_fst.add_const _)).indicator
    ((shell_measurable s₀ η j).preimage measurable_snd)

theorem finiteEnvelope_square {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    (s : Finset ℕ) (t : ℝ) (y : Transverse) :
    (finiteEnvelope s₀ η s t y)^2 = ∑ j ∈ s, (term s₀ η j t y)^2 := by
  classical
  by_cases h : ∃ j ∈ s, y ∈ shell s₀ η j
  · obtain ⟨j,hj,hy⟩ := h
    have hz (k : ℕ) (_hk : k ∈ s) (hkj : k ≠ j) : term s₀ η k t y = 0 :=
      indicator_of_notMem (fun hk => (disjoint_left.mp (shell_disjoint hs₀ hη hkj)) hk hy) _
    have he : finiteEnvelope s₀ η s t y = term s₀ η j t y := Finset.sum_eq_single j hz (fun h => (h hj).elim)
    rw [he,Finset.sum_eq_single j]
    · intro k hk hkj
      rw [hz k hk hkj,zero_pow (by decide : (2:ℕ) ≠ 0)]
    · exact fun h => (h hj).elim
  · have hz (j : ℕ) (hj : j ∈ s) : term s₀ η j t y = 0 :=
      indicator_of_notMem (fun hy => h ⟨j,hj,hy⟩) _
    have he : finiteEnvelope s₀ η s t y = 0 := Finset.sum_eq_zero hz
    rw [he,zero_pow (by decide : (2:ℕ) ≠ 0)]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [hz j hj,zero_pow (by decide : (2:ℕ) ≠ 0)]

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # An integrable squared envelope for all finite annular truncations -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.AnnularEnvelope

def timeSpaceVolume (T : ℝ) : Measure (ℝ × Transverse) :=
  (volume.restrict (Icc (0:ℝ) T)).prod volume

theorem inverse_square_integrable {s T : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => 1/(t+s)^2) (Icc 0 T) := by
  apply ContinuousOn.integrableOn_compact (K := Icc 0 T) isCompact_Icc
  apply continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow 2)
  intro t ht
  apply pow_ne_zero
  change t+s ≠ 0
  linarith [ht.1]

theorem inverse_square_integral_le {s T : ℝ} (hs : 0 < s) (hT : 0 ≤ T) :
    (∫ t in Icc (0:ℝ) T, 1/(t+s)^2) ≤ 1/s := by
  have he : (∫ t in Icc (0:ℝ) T, 1/(t+s)^2)*s^2 =
      ∫ t in (0:ℝ)..T, s^2/(t+s)^2 := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hT,
      ← intervalIntegral.integral_mul_const]
    congr 1
    funext t
    ring
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hs)).mp
  calc
    s^2*(∫ t in Icc (0:ℝ) T, 1/(t+s)^2) =
        ∫ t in (0:ℝ)..T, s^2/(t+s)^2 := by rw [mul_comm,he]
    _ ≤ s := time_square_integral_le hs hT
    _ = s^2*(1/s) := by field_simp

theorem term_square_eq (s₀ η : ℝ) (j : ℕ) (u : ℝ × Transverse) :
    (term s₀ η j u.1 u.2)^2 =
      (1/(u.1+jetScale s₀ η j)^2)*((shell s₀ η j).indicator (fun _ => (1:ℝ)) u.2) := by
  by_cases h : u.2 ∈ shell s₀ η j <;> simp [term,h]

theorem term_square_integrable {s₀ η T : ℝ} (hs₀ : 0 < s₀) (j : ℕ) :
    Integrable (fun u : ℝ × Transverse => (term s₀ η j u.1 u.2)^2) (timeSpaceVolume T) := by
  have ht := inverse_square_integrable (T := T) (DatumBounds.scale_pos (η := η) hs₀ (j+1))
  have hy : Integrable ((shell s₀ η j).indicator (fun _ => (1:ℝ))) :=
    integrable_indicator_iff (shell_measurable s₀ η j) |>.mpr
      (integrableOn_const (shell_finite s₀ η j).ne)
  simpa only [term_square_eq,timeSpaceVolume,jetScale] using ht.mul_prod hy

theorem term_square_integral_le {s₀ η T : ℝ} (hs₀ : 0 < s₀) (hηmax : η ≤ Real.log 2)
    (hT : 0 ≤ T) (j : ℕ) :
    (∫ u : ℝ × Transverse, (term s₀ η j u.1 u.2)^2 ∂timeSpaceVolume T) ≤
      4*Real.pi*jetScale s₀ η j := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (j+1)
  simp only [term_square_eq,timeSpaceVolume]
  rw [integral_prod_mul (fun t : ℝ => 1/(t+jetScale s₀ η j)^2)
    ((shell s₀ η j).indicator (fun _ => (1:ℝ))),
    integral_indicator (shell_measurable s₀ η j),setIntegral_const,smul_eq_mul,mul_one]
  calc
    _ ≤ (1/jetScale s₀ η j)*(4*Real.pi*(jetScale s₀ η j)^2) :=
      mul_le_mul (inverse_square_integral_le hs hT) (shell_area_le hs₀ hηmax j)
        (measureReal_nonneg) (by positivity)
    _ = _ := by dsimp only [jetScale] at hs ⊢; field_simp

def squareEnvelope (s₀ η : ℝ) (u : ℝ × Transverse) : ℝ :=
  ∑' j : ℕ, (term s₀ η j u.1 u.2)^2

theorem term_square_summable {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    (u : ℝ × Transverse) : Summable (fun j : ℕ => (term s₀ η j u.1 u.2)^2) := by
  apply JetSeries.summable_single_support
  intro i j hij hi
  have hy : u.2 ∈ shell s₀ η i := by
    by_contra h
    exact hi (by simp [term,indicator_of_notMem h])
  have hj : u.2 ∉ shell s₀ η j := fun hj => (disjoint_left.mp (shell_disjoint hs₀ hη hij)) hy hj
  simp [term,indicator_of_notMem hj]

theorem term_square_integrals_summable {s₀ η T : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T) :
    Summable (fun j : ℕ => ∫ u : ℝ × Transverse, (term s₀ η j u.1 u.2)^2 ∂timeSpaceVolume T) := by
  have hbase : Summable (DatumBounds.scale s₀ η) := by
    simpa only [pow_one] using DatumBounds.summable_scale_pow s₀ hη 1 (by norm_num)
  have hshift : Summable (fun j : ℕ => DatumBounds.scale s₀ η (j+1)) :=
    (summable_nat_add_iff 1).mpr hbase
  have hs : Summable (fun j : ℕ => 4*Real.pi*jetScale s₀ η j) := hshift.mul_left _
  have hn (j : ℕ) : 0 ≤ ∫ u : ℝ × Transverse, (term s₀ η j u.1 u.2)^2 ∂timeSpaceVolume T :=
    integral_nonneg (fun u => sq_nonneg _)
  exact Summable.of_nonneg_of_le hn (term_square_integral_le hs₀ hηmax hT) hs

theorem squareEnvelope_integrable {s₀ η T : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T) :
    Integrable (squareEnvelope s₀ η) (timeSpaceVolume T) := by
  have hm (j : ℕ) : Measurable (fun u : ℝ × Transverse => (term s₀ η j u.1 u.2)^2) :=
    (term_measurable s₀ η j).pow_const 2
  have hi (j : ℕ) : Integrable (fun u : ℝ × Transverse => (term s₀ η j u.1 u.2)^2) (timeSpaceVolume T) :=
    term_square_integrable hs₀ j
  have hsum : Summable (fun j : ℕ => ∫ u : ℝ × Transverse, (term s₀ η j u.1 u.2)^2 ∂timeSpaceVolume T) :=
    term_square_integrals_summable hs₀ hη hηmax hT
  exact JetSeries.integrable_nonnegative_series (μ := timeSpaceVolume T)
    (f := fun j (u : ℝ × Transverse) => (term s₀ η j u.1 u.2)^2)
    hm hi (fun j u => sq_nonneg _) (term_square_summable hs₀.le hη.le) hsum

theorem finiteEnvelope_square_le {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    (s : Finset ℕ) (u : ℝ × Transverse) :
    (finiteEnvelope s₀ η s u.1 u.2)^2 ≤ squareEnvelope s₀ η u := by
  rw [finiteEnvelope_square hs₀ hη]
  exact (term_square_summable hs₀ hη u).sum_le_tsum s (fun j _ => sq_nonneg _)

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # Uniform integrability and vanishing scale tails of the annular square envelope -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

theorem finiteEnvelope_measurable (s₀ η : ℝ) (s : Finset ℕ) :
    Measurable (fun u : ℝ × Transverse => finiteEnvelope s₀ η s u.1 u.2) :=
  Finset.measurable_sum s (fun j _ => term_measurable s₀ η j)

theorem squareEnvelope_nonneg (s₀ η : ℝ) (u : ℝ × Transverse) :
    0 ≤ squareEnvelope s₀ η u := tsum_nonneg (fun _ => sq_nonneg _)

theorem finite_squares_uniformIntegrable {s₀ η T : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T) :
    UniformIntegrable (fun N (u : ℝ × Transverse) =>
      (finiteEnvelope s₀ η (Finset.range N) u.1 u.2)^2) 1 (timeSpaceVolume T) := by
  have hG := squareEnvelope_integrable hs₀ hη hηmax hT
  have hm (N : ℕ) : AEStronglyMeasurable (fun u : ℝ × Transverse =>
      (finiteEnvelope s₀ η (Finset.range N) u.1 u.2)^2) (timeSpaceVolume T) :=
    ((finiteEnvelope_measurable s₀ η (Finset.range N)).pow_const 2).aestronglyMeasurable
  have hb (N : ℕ) : ∀ᵐ u ∂timeSpaceVolume T,
      ‖(finiteEnvelope s₀ η (Finset.range N) u.1 u.2)^2‖ₑ ≤ ‖squareEnvelope s₀ η u‖ₑ := by
    filter_upwards [] with u
    apply enorm_le_iff_norm_le.mpr
    rw [Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg (squareEnvelope_nonneg s₀ η u)]
    exact finiteEnvelope_square_le hs₀.le hη.le _ u
  obtain ⟨hui,C,hC⟩ := (uniformIntegrable_const (ι := ℕ) (by norm_num : (1:ℝ≥0∞) ≤ 1)
    (by norm_num : (1:ℝ≥0∞) ≠ ⊤) (memLp_one_iff_integrable.mpr hG))
  exact ⟨hui.ae_mono hm hb,C,fun N => (eLpNorm_mono_enorm_ae (hm N) (hb N)).trans (hC N)⟩

theorem finite_squares_tendsto {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    (u : ℝ × Transverse) :
    Tendsto (fun N => (finiteEnvelope s₀ η (Finset.range N) u.1 u.2)^2)
      atTop (𝓝 (squareEnvelope s₀ η u)) := by
  simp_rw [finiteEnvelope_square hs₀ hη]
  exact (term_square_summable hs₀ hη u).hasSum.tendsto_sum_nat

/-- Discarding all sufficiently small scales makes the squared-envelope integral vanish. -/
theorem scale_tail_integral_tendsto {s₀ η T : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T) :
    Tendsto (fun N => ∫ u : ℝ × Transverse,
      squareEnvelope s₀ η u-(finiteEnvelope s₀ η (Finset.range N) u.1 u.2)^2
      ∂timeSpaceVolume T) atTop (𝓝 0) := by
  have hG := squareEnvelope_integrable hs₀ hη hηmax hT
  have hm (N : ℕ) : AEStronglyMeasurable (fun u : ℝ × Transverse =>
      squareEnvelope s₀ η u-(finiteEnvelope s₀ η (Finset.range N) u.1 u.2)^2) (timeSpaceVolume T) :=
    hG.aestronglyMeasurable.sub
      (((finiteEnvelope_measurable s₀ η (Finset.range N)).pow_const 2).aestronglyMeasurable)
  have hb (N : ℕ) : ∀ᵐ u ∂timeSpaceVolume T,
      ‖squareEnvelope s₀ η u-(finiteEnvelope s₀ η (Finset.range N) u.1 u.2)^2‖ ≤ squareEnvelope s₀ η u := by
    filter_upwards [] with u
    rw [Real.norm_of_nonneg (sub_nonneg.mpr (finiteEnvelope_square_le hs₀.le hη.le _ u))]
    exact sub_le_self _ (sq_nonneg _)
  have hl : ∀ᵐ u ∂timeSpaceVolume T,
      Tendsto (fun N => squareEnvelope s₀ η u-(finiteEnvelope s₀ η (Finset.range N) u.1 u.2)^2)
        atTop (𝓝 (0:ℝ)) := by
    filter_upwards [] with u
    simpa only [sub_self] using (finite_squares_tendsto hs₀.le hη.le u).const_sub (squareEnvelope s₀ η u)
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (squareEnvelope s₀ η) hm hG hb hl

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # Uniform integrability of affine annular moment envelopes in a finite cell -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

def cell (r : ℝ) : Set (ℝ × Transverse) := {u | u.2 ∈ Metric.ball 0 r}

def momentMajorant (s₀ η A B r : ℝ) (u : ℝ × Transverse) : ℝ :=
  2*A^2*(cell r).indicator (fun _ => (1:ℝ)) u+2*B^2*squareEnvelope s₀ η u

theorem momentMajorant_nonneg (s₀ η A B r : ℝ) (u : ℝ × Transverse) :
    0 ≤ momentMajorant s₀ η A B r u := by
  apply add_nonneg
  · apply mul_nonneg (by positivity)
    exact indicator_nonneg (fun _ _ => zero_le_one) u
  · exact mul_nonneg (by positivity) (squareEnvelope_nonneg s₀ η u)

theorem momentMajorant_integrable {s₀ η T : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T) (A B r : ℝ) :
    Integrable (momentMajorant s₀ η A B r) (timeSpaceVolume T) := by
  have ht : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Icc (0:ℝ) T)) :=
    integrableOn_const (measure_Icc_lt_top.ne)
  have hy : Integrable ((Metric.ball (0:Transverse) r).indicator (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_const (measure_ball_lt_top.ne))
  have hc : Integrable ((cell r).indicator (fun _ => (1:ℝ))) (timeSpaceVolume T) := by
    change Integrable ((cell r).indicator (fun _ => (1:ℝ)))
      ((volume.restrict (Icc (0:ℝ) T)).prod volume)
    convert ht.mul_prod hy using 1
    funext u
    by_cases h : u.2 ∈ Metric.ball (0:Transverse) r
    · rw [indicator_of_mem (show u ∈ cell r from h),indicator_of_mem h]
      norm_num
    · rw [indicator_of_notMem (show u ∉ cell r from h),indicator_of_notMem h]
      norm_num
  exact (hc.const_mul (2*A^2)).add
    ((squareEnvelope_integrable hs₀ hη hηmax hT).const_mul (2*B^2))

theorem affine_square_le {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    (A B r : ℝ) (s : Finset ℕ) (u : ℝ × Transverse) :
    (cell r).indicator (fun u => (A+B*finiteEnvelope s₀ η s u.1 u.2)^2) u ≤
      momentMajorant s₀ η A B r u := by
  have he := finiteEnvelope_square_le hs₀ hη s u
  by_cases hu : u ∈ cell r
  · simp only [indicator_of_mem hu,momentMajorant,mul_one]
    nlinarith [sq_nonneg (A-B*finiteEnvelope s₀ η s u.1 u.2),mul_nonneg (sq_nonneg B) (sub_nonneg.mpr he)]
  · rw [indicator_of_notMem hu]
    exact momentMajorant_nonneg s₀ η A B r u

theorem affine_squares_uniformIntegrable {s₀ η T : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T) (A B r : ℝ) :
    UniformIntegrable (fun N => (cell r).indicator (fun u : ℝ × Transverse =>
      (A+B*finiteEnvelope s₀ η (Finset.range N) u.1 u.2)^2)) 1 (timeSpaceVolume T) := by
  have hm (N : ℕ) : AEStronglyMeasurable ((cell r).indicator (fun u : ℝ × Transverse =>
      (A+B*finiteEnvelope s₀ η (Finset.range N) u.1 u.2)^2)) (timeSpaceVolume T) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ (measurableSet_ball.preimage measurable_snd)
    exact (measurable_const.add ((finiteEnvelope_measurable s₀ η _).const_mul B)).pow_const 2
  have hb (N : ℕ) : ∀ᵐ u ∂timeSpaceVolume T,
      ‖(cell r).indicator (fun u : ℝ × Transverse =>
        (A+B*finiteEnvelope s₀ η (Finset.range N) u.1 u.2)^2) u‖ₑ ≤
      ‖momentMajorant s₀ η A B r u‖ₑ := by
    filter_upwards [] with u
    apply enorm_le_iff_norm_le.mpr
    rw [Real.norm_of_nonneg (indicator_nonneg (fun _ _ => sq_nonneg _) u),
      Real.norm_of_nonneg (momentMajorant_nonneg s₀ η A B r u)]
    exact affine_square_le hs₀.le hη.le A B r _ u
  obtain ⟨hui,C,hC⟩ := uniformIntegrable_const (ι := ℕ) (by norm_num : (1:ℝ≥0∞) ≤ 1)
    (by norm_num : (1:ℝ≥0∞) ≠ ⊤)
    (memLp_one_iff_integrable.mpr (momentMajorant_integrable hs₀ hη hηmax hT A B r))
  exact ⟨hui.ae_mono hm hb,C,fun N => (eLpNorm_mono_enorm_ae (hm N) (hb N)).trans (hC N)⟩

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # The small spatial annuli disappear pointwise and in every integrable majorant -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

def tailRegion (s₀ η : ℝ) (J : ℕ) : Set (ℝ × Transverse) :=
  {u | ∃ j : ℕ, J ≤ j ∧ u.2 ∈ shell s₀ η j}

theorem tailRegion_measurable (s₀ η : ℝ) (J : ℕ) : MeasurableSet (tailRegion s₀ η J) := by
  have he : tailRegion s₀ η J = ⋃ j : ℕ, ⋃ (_ : J ≤ j), Prod.snd ⁻¹' shell s₀ η j := by
    ext u
    simp [tailRegion]
  rw [he]
  exact MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ =>
    (shell_measurable s₀ η j).preimage measurable_snd))

theorem eventually_outside_tail {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    (u : ℝ × Transverse) : ∀ᶠ J in atTop, u ∉ tailRegion s₀ η J := by
  classical
  by_cases h : ∃ j : ℕ, u.2 ∈ shell s₀ η j
  · obtain ⟨j,hj⟩ := h
    filter_upwards [eventually_ge_atTop (j+1)] with J hJ
    rintro ⟨k,hk,hku⟩
    have hne : j ≠ k := by omega
    exact (disjoint_left.mp (shell_disjoint hs₀ hη hne)) hj hku
  · exact Filter.Eventually.of_forall (fun J ⟨j,_,hj⟩ => h ⟨j,hj⟩)

theorem tail_integral_tendsto {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    {μ : Measure (ℝ × Transverse)} {G : ℝ × Transverse → ℝ} (hG : Integrable G μ) :
    Tendsto (fun J => ∫ u in tailRegion s₀ η J, G u ∂μ) atTop (𝓝 0) := by
  have hm (J) : AEStronglyMeasurable ((tailRegion s₀ η J).indicator G) μ :=
    hG.aestronglyMeasurable.indicator (tailRegion_measurable s₀ η J)
  have hb (J) : ∀ᵐ u ∂μ, ‖(tailRegion s₀ η J).indicator G u‖ ≤ ‖G u‖ :=
    ae_of_all _ (fun u => norm_indicator_le_norm_self G u)
  have ht : ∀ᵐ u ∂μ, Tendsto (fun J => (tailRegion s₀ η J).indicator G u) atTop (𝓝 0) := by
    filter_upwards [] with u
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_outside_tail hs₀ hη u] with J hJ
    exact (indicator_of_notMem hJ G).symm
  simpa only [integral_indicator (tailRegion_measurable s₀ η _),integral_zero] using
    tendsto_integral_of_dominated_convergence (fun u => ‖G u‖) hm hG.norm hb ht

theorem tail_lintegral_tendsto {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    {μ : Measure (ℝ × Transverse)} {G : ℝ × Transverse → ℝ} (hG : Integrable G μ)
    (hGn : ∀ u, 0 ≤ G u) :
    Tendsto (fun J => ∫⁻ u in tailRegion s₀ η J, ENNReal.ofReal (G u) ∂μ) atTop (𝓝 0) := by
  have he (J) : (∫⁻ u in tailRegion s₀ η J, ENNReal.ofReal (G u) ∂μ) =
      ENNReal.ofReal (∫ u in tailRegion s₀ η J, G u ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hG.restrict (ae_of_all _ hGn)).symm
  simp_rw [he]
  simpa only [Function.comp_def,ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tail_integral_tendsto hs₀ hη hG)

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # The disjoint annular envelope is bounded by inverse time -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.AnnularEnvelope

theorem finiteEnvelope_le_inv_time {s₀ η t : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    (ht : 0 < t) (s : Finset ℕ) (y : VelocityWeight.Transverse) :
    finiteEnvelope s₀ η s t y ≤ 1/t := by
  classical
  by_cases h : ∃ j ∈ s, y ∈ shell s₀ η j
  · obtain ⟨j,hj,hy⟩ := h
    have hz (k : ℕ) (_hk : k ∈ s) (hkj : k ≠ j) : term s₀ η k t y = 0 :=
      indicator_of_notMem (fun hk => (disjoint_left.mp (shell_disjoint hs₀ hη hkj)) hk hy) _
    have he : finiteEnvelope s₀ η s t y = term s₀ η j t y :=
      Finset.sum_eq_single j hz (fun h => (h hj).elim)
    rw [he,term,indicator_of_mem hy]
    exact one_div_le_one_div_of_le ht (le_add_of_nonneg_right
      (mul_nonneg hs₀ (Real.exp_pos _).le))
  · have hz (j : ℕ) (hj : j ∈ s) : term s₀ η j t y = 0 :=
      indicator_of_notMem (fun hy => h ⟨j,hj,hy⟩) _
    have he : finiteEnvelope s₀ η s t y = 0 := Finset.sum_eq_zero hz
    rw [he]
    exact (one_div_pos.mpr ht).le

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # The finite disjoint annular envelope retains its minimum scale -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.AnnularEnvelope

theorem finiteEnvelope_le_minimum_scale {s₀ η t : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η)
    (ht : 0 ≤ t) (N : ℕ) (y : VelocityWeight.Transverse) :
    finiteEnvelope s₀ η (Finset.range N) t y ≤ 1/(t+JetGeometry.jetScale s₀ η N) := by
  classical
  have hs : 0 < JetGeometry.jetScale s₀ η N := DatumBounds.scale_pos hs₀ _
  by_cases h : ∃ j ∈ Finset.range N, y ∈ shell s₀ η j
  · obtain ⟨j,hj,hy⟩ := h
    have hz (k : ℕ) (_hk : k ∈ Finset.range N) (hkj : k ≠ j) : term s₀ η k t y = 0 :=
      indicator_of_notMem (fun hk => (disjoint_left.mp (shell_disjoint hs₀.le hη hkj)) hk hy) _
    have he : finiteEnvelope s₀ η (Finset.range N) t y = term s₀ η j t y :=
      Finset.sum_eq_single j hz (fun h => (h hj).elim)
    rw [he,term,indicator_of_mem hy]
    apply one_div_le_one_div_of_le (add_pos_of_nonneg_of_pos ht hs)
    exact add_le_add le_rfl (JetGeometry.scale_antitone hs₀.le hη
      (Nat.add_le_add_right (Finset.mem_range.mp hj).le 1))
  · have hz (j : ℕ) (hj : j ∈ Finset.range N) : term s₀ η j t y = 0 :=
      indicator_of_notMem (fun hy => h ⟨j,hj,hy⟩) _
    have he : finiteEnvelope s₀ η (Finset.range N) t y = 0 := Finset.sum_eq_zero hz
    rw [he]
    exact (one_div_pos.mpr (add_pos_of_nonneg_of_pos ht hs)).le

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

end OAI
