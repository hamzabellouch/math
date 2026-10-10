import Mathlib
import OAI.Probability.SLELocalization.BoundaryDiffusion
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Reverse Loewner estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.ReverseLoewner
open LoewnerCutoff

lemma continuous_velocity {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun p : ℝ × ℂ => velocity ε p.1 p.2) :=
  (LoewnerCutoff.continuous_velocity hε).neg

lemma norm_velocity_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) (w : ℂ) :
    ‖velocity ε u w‖ ≤ 2 / ε := by
  simpa only [velocity,norm_neg] using LoewnerCutoff.norm_velocity_le hε u w

lemma exists_solution {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : ℝ → ℝ) (hU : ContinuousOn U (Icc 0 T)) (z : ℂ) :
    ∃ H : ℝ → ℂ, H 0 = z ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t := by
  let L : ℝ≥0 := ⟨2 / ε, by positivity⟩
  let K : ℝ≥0 := ⟨4 / ε^2, by positivity⟩
  let a : ℝ≥0 := ⟨(2 / ε) * T, mul_nonneg (by positivity) hT⟩
  have hp : IsPicardLindelof (fun t => velocity ε (U t))
      ⟨0, ⟨le_rfl, hT⟩⟩ z a 0 L K := by
    constructor
    · exact fun t _ => (velocity_lipschitz hε (U t)).lipschitzOnWith
    · intro w _
      have hc : ContinuousOn (fun t : ℝ => (U t, w)) (Icc 0 T) :=
        hU.prodMk continuousOn_const
      simpa only [Function.comp_def] using
        (continuous_velocity hε).comp_continuousOn hc
    · exact fun t _ w _ => norm_velocity_le hε (U t) w
    · dsimp [L, a]
      simp only [sub_zero, sub_self, max_eq_left hT]
      rfl
  exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

end SLEExactGauge.ReverseLoewner

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.ReverseLoewner
open LoewnerCutoff

lemma norm_velocity_driver_sub_le {ε : ℝ} (hε : 0 < ε) (u v : ℝ) (z : ℂ) :
    ‖velocity ε u z - velocity ε v z‖ ≤ (4 / ε^2) * |u-v| := by
  simpa only [velocity, neg_sub_neg, norm_sub_rev] using
    LoewnerCutoff.norm_velocity_driver_sub_le hε u v z

lemma derivWithin_right {ε T : ℝ} {U : ℝ → ℝ} {H : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt H (velocity ε (U t) (H t)) (Ici t) t :=
  (hH t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

lemma derivWithin_left {ε T : ℝ} {U : ℝ → ℝ} {H : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Ioc 0 T) :
    HasDerivWithinAt H (velocity ε (U t) (H t)) (Iic t) t :=
  (hH t ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht)

lemma solution_eq {ε T : ℝ} (hε : 0 < ε) {U : ℝ → ℝ} {H G : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, HasDerivWithinAt G (velocity ε (U t) (G t)) (Icc 0 T) t)
    (h0 : H 0 = G 0) : EqOn H G (Icc 0 T) := by
  apply ODE_solution_unique_of_mem_Icc_right
    (s := fun _ => univ) (fun t _ => (velocity_lipschitz hε (U t)).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hH) (fun _ ht => derivWithin_right hH ht)
    (fun _ _ => mem_univ _) (HasDerivWithinAt.continuousOn hG)
    (fun _ ht => derivWithin_right hG ht) (fun _ _ => mem_univ _) h0

lemma solution_dist_le {ε T D : ℝ} (hε : 0 < ε) (hD : 0 ≤ D)
    {U V : ℝ → ℝ} {H G : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, HasDerivWithinAt G (velocity ε (V t) (G t)) (Icc 0 T) t)
    (h0 : H 0 = G 0) (hUV : ∀ t ∈ Icc 0 T, |U t-V t| ≤ D)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (H t) (G t) ≤ D * Real.exp ((4 / ε^2) * T) := by
  let K : ℝ≥0 := ⟨4 / ε^2, by positivity⟩
  have hK : (0 : ℝ) < K := by change 0 < 4 / ε^2; positivity
  have hb (s : ℝ) (hs : s ∈ Ico 0 T) :
      dist (velocity ε (V s) (G s)) (velocity ε (U s) (G s)) ≤ (K : ℝ) * D := by
    rw [dist_eq_norm]
    calc
      _ ≤ (4 / ε^2) * |V s-U s| := norm_velocity_driver_sub_le hε _ _ _
      _ ≤ (K : ℝ) * D := by
        rw [abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (hUV s ⟨hs.1, hs.2.le⟩) hK.le
  have hh := dist_le_of_approx_trajectories_ODE
    (fun t => velocity_lipschitz hε (U t))
    (HasDerivWithinAt.continuousOn hH) (fun _ hs => derivWithin_right hH hs)
    (fun t _ => le_of_eq (dist_self (velocity ε (U t) (H t))))
    (HasDerivWithinAt.continuousOn hG) (fun _ hs => derivWithin_right hG hs)
    hb (le_of_eq (dist_eq_zero.2 h0)) t ht
  have he : gronwallBound 0 K (0 + (K : ℝ)*D) (t-0) =
      D * (Real.exp ((K : ℝ)*t)-1) := by
    simp only [gronwallBound, zero_add, sub_zero, ite_eq_right (ne_of_gt hK)]
    field_simp
    ring
  rw [he] at hh
  have hexp : Real.exp ((K : ℝ)*t) ≤ Real.exp ((K : ℝ)*T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK.le)
  apply hh.trans
  change D * (Real.exp ((4 / ε^2)*t)-1) ≤ D * Real.exp ((4 / ε^2)*T)
  change Real.exp ((4 / ε^2)*t) ≤ Real.exp ((4 / ε^2)*T) at hexp
  exact mul_le_mul_of_nonneg_left (by linarith) hD

end SLEExactGauge.ReverseLoewner

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.ReverseLoewner
open LoewnerCutoff
open scoped unitInterval

def solution {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) (z : ℂ) : ℝ → ℂ :=
  (exists_solution hε hT (extendDriver T U) (continuous_extendDriver T U).continuousOn z).choose

lemma solution_initial {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) (z : ℂ) :
    solution hε hT U z 0 = z :=
  (exists_solution hε hT (extendDriver T U)
    (continuous_extendDriver T U).continuousOn z).choose_spec.1

lemma solution_deriv {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) (z : ℂ) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt (solution hε hT U z)
      (velocity ε (extendDriver T U t) (solution hε hT U z t)) (Icc 0 T) t :=
  (exists_solution hε hT (extendDriver T U)
    (continuous_extendDriver T U).continuousOn z).choose_spec.2

def solutionPath {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) (z : ℂ) :
    C(Icc 0 T, ℂ) :=
  ⟨fun t => solution hε hT U z t,
    continuousOn_iff_continuous_domRestrict.1 (HasDerivWithinAt.continuousOn (solution_deriv hε hT U z))⟩

lemma solutionPath_lipschitz {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (z : ℂ) :
    LipschitzWith ⟨Real.exp ((4 / ε^2) * T), (Real.exp_pos _).le⟩
      (fun U : C(I, ℝ) => solutionPath hε hT U z) := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  apply (ContinuousMap.dist_le (mul_nonneg (Real.exp_pos _).le dist_nonneg)).2
  intro t
  have hUV (s : ℝ) (_hs : s ∈ Icc 0 T) :
      |extendDriver T U s-extendDriver T V s| ≤ dist U V := by
    exact (ContinuousMap.dist_apply_le_dist (f := U) (g := V)
      (projIcc 0 1 zero_le_one (s/T)))
  have hh := solution_dist_le hε dist_nonneg (solution_deriv hε hT U z)
    (solution_deriv hε hT V z)
    ((solution_initial hε hT U z).trans (solution_initial hε hT V z).symm)
    hUV t.property
  change dist (solution hε hT U z t) (solution hε hT V z t) ≤
    Real.exp ((4 / ε^2)*T) * dist U V
  simpa only [mul_comm] using hh

end SLEExactGauge.ReverseLoewner

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.ReverseLoewner
open LoewnerCutoff

def reverseCentered (U : C(I, ℝ)) : C(I, ℝ) :=
  ⟨fun q => U (unitInterval.symm q) - U 1,
    (U.continuous.comp unitInterval.continuous_symm).sub continuous_const⟩

lemma reverseCentered_lipschitz : LipschitzWith 2 reverseCentered := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  apply (ContinuousMap.dist_le (by positivity)).2
  intro q
  change dist (U (unitInterval.symm q)-U 1) (V (unitInterval.symm q)-V 1) ≤ (2:ℝ)*dist U V
  calc
    _ ≤ dist (U (unitInterval.symm q)) (V (unitInterval.symm q)) + dist (U 1) (V 1) := dist_sub_sub_le _ _ _ _
    _ ≤ dist U V + dist U V := add_le_add (ContinuousMap.dist_apply_le_dist _) (ContinuousMap.dist_apply_le_dist _)
    _ = _ := by ring

lemma extend_reverseCentered {T : ℝ} (hT : T ≠ 0) (U : C(I, ℝ)) (s : ℝ) :
    extendDriver T (reverseCentered U) s = extendDriver T U (T-s) - U 1 := by
  dsimp only [extendDriver,reverseCentered,ContinuousMap.coe_mk]
  rw [unitInterval.symm_projIcc]
  congr 2
  field_simp

lemma extend_end {T : ℝ} (hT : T ≠ 0) (U : C(I, ℝ)) : extendDriver T U T = U 1 := by
  simp only [extendDriver,div_self hT]
  congr 1
  exact Subtype.ext (by simp [projIcc])

def tipApprox {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) : ℂ :=
  solution hε hT (reverseCentered U) ((ε:ℂ)*Complex.I) T + (U 1 : ℂ)

lemma continuous_tipApprox {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
    Continuous (tipApprox hε hT) := by
  have hc : Continuous (fun U : C(I, ℝ) =>
      solutionPath hε hT (reverseCentered U) ((ε:ℂ)*Complex.I)) :=
    (solutionPath_lipschitz hε hT _).continuous.comp reverseCentered_lipschitz.continuous
  have he := (continuous_eval_const (⟨T,⟨hT,le_rfl⟩⟩ : Icc 0 T)).comp hc
  exact he.add (Complex.continuous_ofReal.comp (continuous_eval_const (1:I)))

lemma tipApprox_eq_inverse {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (hU : ContinuousOn driver (Icc 0 T)) (U : C(I, ℝ))
    (he : EqOn (extendDriver T U) driver (Icc 0 T)) :
    tipApprox hε hT.le U = f T ((driver T:ℂ)+(ε:ℂ)*Complex.I) := by
  let w : ℂ := (driver T:ℂ)+(ε:ℂ)*Complex.I
  have hw : w ∈ halfPlane := by simpa [w,halfPlane] using hε
  let z := f T w
  have hz : z ∈ localizationDomain γ T := h.2.2.2.2.2.2.2.2.1 T hT.le hw
  have hfinal : g T z = w := h.2.2.2.2.2.2.2.2.2.2.1 T hT.le _ hw
  have hend : (U 1:ℝ) = driver T := (extend_end hT.ne' U).symm.trans (he ⟨hT.le,le_rfl⟩)
  let H : ℝ → ℂ := fun s => g (T-s) z - (driver T:ℂ)
  have hH0 : H 0 = (ε:ℂ)*Complex.I := by simp [H,hfinal,w]
  have hheight (s : ℝ) (hs : s ∈ Icc 0 T) : ε ≤ (H s).im := by
    have hh := h.height_antitone hT.le hz (show T-s ∈ Icc 0 T by constructor <;> linarith [hs.1,hs.2])
      ⟨hT.le,le_rfl⟩ (by linarith [hs.1] : T-s ≤ T)
    simp only [hfinal,w,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] at hh
    simpa only [H,Complex.sub_im,Complex.ofReal_im,sub_zero] using hh
  have hHd (s : ℝ) (hs : s ∈ Icc 0 T) :
      HasDerivWithinAt H (velocity ε (extendDriver T (reverseCentered U) s) (H s)) (Icc 0 T) s := by
    have hst : T-s ∈ Icc 0 T := by constructor <;> linarith [hs.1,hs.2]
    have htder : HasDerivWithinAt (fun r : ℝ => T-r) (-1) (Icc 0 T) s := by
      simpa only [id_eq] using ((hasDerivAt_id s).const_sub T).hasDerivWithinAt
    have hd := (h.hasDerivWithinAt_eval hT.le hU hz hst).scomp s htder
      (show MapsTo (fun r : ℝ => T-r) (Icc 0 T) (Icc 0 T) from fun r hr => by constructor <;> linarith [hr.1,hr.2])
    have hd' := hd.sub_const (driver T : ℂ)
    apply hd'.congr_deriv
    rw [velocity,LoewnerCutoff.velocity_eq (hheight s hs),extend_reverseCentered hT.ne' U s,he hst,hend]
    dsimp only [H,Function.comp_def]
    simp only [neg_smul,one_smul]
    push_cast
    ring
  have hsol := solution_eq hε hHd (solution_deriv hε hT.le (reverseCentered U) ((ε:ℂ)*Complex.I))
    (hH0.trans (solution_initial hε hT.le (reverseCentered U) ((ε:ℂ)*Complex.I)).symm)
  have hendpoint := hsol ⟨hT.le,le_rfl⟩
  simp only [H,sub_self,h.initial z hz.1.1] at hendpoint
  dsimp only [tipApprox]
  rw [← hendpoint,hend]
  simp only [sub_add_cancel,z,w]

end SLEExactGauge.ReverseLoewner

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.CanonicalTrace
open ReverseLoewner

def height (n : ℕ) : ℝ := 1 / ((n:ℝ)+1)

lemma height_pos (n : ℕ) : 0 < height n := by unfold height; positivity

lemma height_tendsto : Tendsto height atTop (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · change Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp (tendsto_add_atTop_nat 1)
  · exact Filter.Eventually.of_forall height_pos

def value {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (sample : Ω) : ℂ :=
  if T = 0 then 0 else ContinuousDriver.selectedLimit 0
    (fun n => tipApprox (height_pos n) T.coe_nonneg (BrownianDriver.path B (Real.sqrt κ) T sample))

lemma measurable_past {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    @Measurable Ω ℂ (BrownianPredictable.pastSigma B T) (borel ℂ) (value κ B T) := by
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  let : MeasurableSpace Ω := BrownianPredictable.pastSigma B T
  change Measurable (fun sample => value κ B T sample)
  by_cases hT : T = 0
  · simp only [value,ite_eq_left hT]
    exact measurable_const
  · simp only [value,ite_eq_right hT]
    apply ContinuousDriver.measurable_selectedLimit
    intro n
    exact (continuous_tipApprox (height_pos n) T.coe_nonneg).measurable.comp
      (BrownianDriver.path_measurable_past B (Real.sqrt κ) T)

lemma aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) :
    AEMeasurable (value κ B T) P := by
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  change AEMeasurable (fun sample => value κ B T sample) P
  by_cases hT : T = 0
  · simp only [value,ite_eq_left hT]
    exact aemeasurable_const
  · simp only [value,ite_eq_right hT]
    apply ContinuousDriver.aemeasurable_selectedLimit
    intro n
    exact (continuous_tipApprox (height_pos n) T.coe_nonneg).measurable.comp_aemeasurable
      (BrownianDriver.path_aemeasurable hB (Real.sqrt κ) T)

lemma eq_source {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
    {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ * B t.toNNReal sample) γ g f)
    (hc : Continuous (fun t => B t sample)) (T : ℝ≥0) : value κ B T sample = γ T := by
  by_cases hT : T = 0
  · simpa [value,hT] using h.2.1.symm
  · simp only [value,ite_eq_right hT]
    apply ContinuousDriver.selectedLimit_eq
    have hTp : 0 < (T:ℝ) := lt_of_le_of_ne T.coe_nonneg (by exact_mod_cast Ne.symm hT)
    have he (n : ℕ) :
        tipApprox (height_pos n) T.coe_nonneg (BrownianDriver.path B (Real.sqrt κ) T sample) =
          f T ((Real.sqrt κ * B T sample:ℝ) + (height n:ℂ)*Complex.I) := by
      simpa only [Real.toNNReal_coe] using
        tipApprox_eq_inverse h (height_pos n) hTp
          ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn)
          (BrownianDriver.path B (Real.sqrt κ) T sample)
          (fun _ ht => BrownianDriver.extend_eq B (Real.sqrt κ) T sample hc ht)
    have ht := (h.2.2.2.2.2.2.2.2.2.2.2.2.2 T T.coe_nonneg).comp height_tendsto
    simpa only [Function.comp_def,he,Real.toNNReal_coe] using ht

end SLEExactGauge.CanonicalTrace

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge

theorem canonicalTraceFromBrownianPast {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (_hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample)) :
    ∃ Γ : ℝ≥0 → Ω → ℂ,
      (∀ t, @Measurable Ω ℂ (BrownianPredictable.pastSigma B t) (borel ℂ) (Γ t)) ∧
      (∀ t, AEMeasurable (Γ t) P) ∧
      ∀ᵐ sample ∂P, ∀ t : ℝ≥0, Γ t sample = γ sample t := by
  refine ⟨CanonicalTrace.value κ B, CanonicalTrace.measurable_past κ B,
    CanonicalTrace.aemeasurable κ hB, ?_⟩
  filter_upwards [hmaps,hB.cont] with sample hm hc
  exact CanonicalTrace.eq_source κ B sample hm hc

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen
open BoundaryFunctional

lemma source_point_reach {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) (hzero : driver 0=0)
    {ε T S : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (hS : 0 ≤ S) (hST : S ≤ T)
    (U : C(I, ℝ)) (hU : EqOn (extendDriver T U) driver (Icc 0 T))
    (x a β δ d y : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (haδ : a ≤ 2-4*δ) (hd : 0 < d) (hdx : d < δ*x) (hεx : 2*ε < x) (hy : δ*ε < y)
    (w : ℂ) (hw : w ∈ localizationDomain γ S) (hclose : dist w (x:ℂ) < d)
    (hwS : g S w=(driver S:ℂ)+(y:ℂ)*Complex.I) :
    reach U hε hT x β a ((δ/(4*d))^β) := by
  apply tip_forces_reach hε hT hS hST U (by rw [hU ⟨le_rfl,hT⟩,hzero]) x a β δ d y
    hβ hδ hδhalf haδ hd hdx hεx hy (fun t => g t w) (h.continuous_eval hS hw)
  · intro t ht
    rw [hU ⟨ht.1.le,ht.2.le.trans hST⟩]
    exact h.hasDerivAt_eval ht.1 (survivingDomain_mono ht.2.le hw)
  · rw [h.initial w hw.1.1]
    exact (dist_eq_norm w (x:ℂ) ▸ hclose).le
  · intro t ht
    have hh := h.height_antitone hS hw ht ⟨hS,le_rfl⟩ ht.2
    dsimp only at hh
    rw [hwS] at hh
    simpa using hh
  · rw [hwS,hU ⟨hS,hST⟩]
    simp

lemma source_hit_eventually_reach {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ : ℝ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω=0)
    (x a β δ d : ℝ) (hx : 0 < x) (hβ : 0 < β) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (haδ : a ≤ 2-4*δ) (hd : 0 < d) (hdx : d < δ*x)
    (hhit : ∃ t : ℝ, 0 ≤ t ∧ dist (γ ω t) (x:ℂ) < d) :
    ∀ᶠ n : ℕ in atTop, reach (BrownianDriver.path B (Real.sqrt κ) (n+1) ω)
      (CanonicalTrace.height_pos n) (n+1 : ℝ≥0).coe_nonneg x β a ((δ/(4*d))^β) := by
  obtain ⟨t,ht,hclose⟩ := hhit
  obtain ⟨w,y,hy,hwd,hw,hwS⟩ := inverse_tip_point h ht hclose
  have hsmall : ∀ᶠ n : ℕ in atTop, CanonicalTrace.height n < min (x/2) (y/δ) :=
    (CanonicalTrace.height_tendsto.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (lt_min (half_pos hx) (div_pos hy hδ)))
  have hlarge : ∀ᶠ n : ℕ in atTop, t ≤ ((n+1:ℝ≥0):ℝ) := by
    have hh : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa only [NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hh.eventually (eventually_ge_atTop t)
  filter_upwards [hsmall,hlarge] with n hn htn
  have hn' := lt_min_iff.mp hn
  have hxcut : 2*CanonicalTrace.height n < x := by linarith [hn'.1]
  have hycut : δ*CanonicalTrace.height n < y := by
    have hh := (lt_div_iff₀ hδ).mp hn'.2
    simpa only [mul_comm] using hh
  apply source_point_reach h (by simp [hb0]) (CanonicalTrace.height_pos n)
    (n+1:ℝ≥0).coe_nonneg ht htn (BrownianDriver.path B (Real.sqrt κ) (n+1) ω)
    (fun s hs => BrownianDriver.extend_eq B _ (n+1) ω hc hs)
    x a β δ d y hβ hδ hδhalf haδ hd hdx hxcut hycut w hw hwd hwS

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen
open BoundaryFunctional Swallowing

lemma initial_bound {β x ε : ℝ} (hβ : 0 ≤ β) (hx : 0 < x) :
    radial (-β) x ε ≤ x^(-β) := by
  have hh := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hx)
    (le_add_of_nonneg_right (sq_nonneg ε)) (show (-β)/2 ≤ 0 by linarith)
  change (x^2+ε^2)^((-β)/2) ≤ x^(-β)
  calc
    _ ≤ (x^2)^((-β)/2) := hh
    _ = x^(-β) := by
      rw [← Real.rpow_natCast_mul hx.le]
      congr 1
      ring

def uniformBudget {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β a x L : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  budget B κ β a (CanonicalTrace.height_pos n) (n+1) x L ω +
    (x^(-β)-radial (-β) x (CanonicalTrace.height n))

lemma uniformBudget_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ β a : ℝ)
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hba : κ*(β+1) ≤ 4+2*a)
    (x L : ℝ) (hx : 0 < x) (n : ℕ) :
    Integrable (uniformBudget B κ β a x L n) P ∧
      (∫ ω,uniformBudget B κ β a x L n ω ∂P)=x^(-β) ∧
      ∀ ω, 0 ≤ uniformBudget B κ β a x L n ω := by
  have hT : (0:ℝ)<((n+1:ℝ≥0):ℝ) := by positivity
  have hh := budget_mean hB κ β a hκ hβ ha hba (CanonicalTrace.height_pos n) (n+1) hT x L
  refine ⟨hh.1.add (integrable_const _),?_,?_⟩
  · change (∫ ω,budget B κ β a (CanonicalTrace.height_pos n) (n+1) x L ω+
      (x^(-β)-radial (-β) x (CanonicalTrace.height n)) ∂P)=_
    rw [integral_add hh.1 (integrable_const _),hh.2]
    simp
  · intro ω
    exact add_nonneg (budget_nonneg B κ β a (CanonicalTrace.height_pos n) (n+1) x L ω)
      (sub_nonneg.mpr (initial_bound hβ hx))

lemma uniformBudget_dominates {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β a x L : ℝ)
    (hβ : 0 ≤ β) (hx : 0 < x) (n : ℕ) (ω : Ω) :
    budget B κ β a (CanonicalTrace.height_pos n) (n+1) x L ω ≤ uniformBudget B κ β a x L n ω :=
  le_add_of_nonneg_right (sub_nonneg.mpr (initial_bound hβ hx))

lemma ratio_power_eq {x d δ β : ℝ} (hx : 0 < x) (hd : 0 < d) (hδ : 0 < δ) :
    x^(-β)/(δ/(4*d))^β = (4*d/(δ*x))^β := by
  rw [Real.rpow_neg hx.le,← Real.inv_rpow hx.le,← Real.div_rpow (inv_nonneg.mpr hx.le) (by positivity)]
  congr 1
  field_simp

theorem positive_real_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ β a δ : ℝ)
    (hκ : 0 ≤ κ) (hβ : 0 < β) (ha : 0 ≤ a) (hba : κ*(β+1) ≤ 4+2*a)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1/2) (haδ : a ≤ 2-4*δ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ ω ∂P, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) :
    P {ω | ∃ t : ℝ, 0 ≤ t ∧ dist (γ ω t) (x:ℂ) < d} ≤ ENNReal.ofReal ((4*d/(δ*x))^β) := by
  by_cases hdx : d < δ*x
  · let L : ℝ := (δ/(4*d))^β
    have hL : 0 < L := Real.rpow_pos_of_pos (by positivity) _
    have hm (n : ℕ) := uniformBudget_mean hB κ β a hκ hβ.le ha hba x L hx n
    have hE : ∀ᵐ ω ∂P, (∃ t : ℝ, 0 ≤ t ∧ dist (γ ω t) (x:ℂ) < d) →
        ∀ᶠ n : ℕ in atTop, L ≤ uniformBudget B κ β a x L n ω := by
      filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hh hc hb0
      intro hhit
      filter_upwards [source_hit_eventually_reach B κ γ g f ω hh hc hb0 x a β δ d hx hβ hδ hδhalf haδ hd hdx hhit] with n hn
      have hb := budget_dominates_reach B κ β a hκ hβ.le ha hba (CanonicalTrace.height_pos n)
        (n+1) (by positivity) x L ω hc hb0 hn
      exact hb.trans (uniformBudget_dominates B κ β a x L hβ.le hx n ω)
    have hh := measure_eventually_budget (uniformBudget B κ β a x L) (x^(-β)) L hL
      (fun n => (hm n).1) (fun n => (hm n).2.2) (fun n => (hm n).2.1) _ hE
    rwa [ratio_power_eq hx hd hδ] at hh
  · have hratio : 1 ≤ 4*d/(δ*x) := by
      rw [le_div_iff₀ (mul_pos hδ hx)]
      have hh : δ*x ≤ d := not_lt.1 hdx
      linarith
    have hp : 1 ≤ (4*d/(δ*x))^β := Real.one_le_rpow hratio hβ.le
    exact (prob_le_one).trans (by simpa using ENNReal.ofReal_le_ofReal hp)

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen
open BoundaryFunctional

def mirror (z : ℂ) : ℂ := -(starRingEnd ℂ) z

lemma mirror_im (z : ℂ) : (mirror z).im=z.im := by simp [mirror]

lemma mirror_re (z : ℂ) : (mirror z).re= -z.re := by simp [mirror]

lemma continuous_mirror : Continuous mirror := Complex.continuous_conj.neg

lemma mirror_dist_real (w : ℂ) (x : ℝ) : ‖mirror w-(x:ℂ)‖ = dist w ((-x:ℝ):ℂ) := by
  rw [dist_eq_norm]
  have he : mirror w-(x:ℂ) = -(starRingEnd ℂ) (w-((-x:ℝ):ℂ)) := by simp [mirror]; ring
  rw [he,norm_neg,Complex.norm_conj]

lemma mirror_ode {G : ℝ → ℂ} {t u : ℝ} (hG : HasDerivAt G (2/(G t-(u:ℂ))) t) :
    HasDerivAt (fun s => mirror (G s)) (2/(mirror (G t)-((-u:ℝ):ℂ))) t := by
  have hh := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hG).neg
  change HasDerivAt (fun s => -(starRingEnd ℂ) (G s)) (-(starRingEnd ℂ) (2/(G t-(u:ℂ)))) t at hh
  apply hh.congr_deriv
  simp only [map_div₀,map_ofNat,map_sub,Complex.conj_ofReal,Complex.ofReal_neg,mirror]
  rw [show -(starRingEnd ℂ) (G t)- -(u:ℂ) = -((starRingEnd ℂ) (G t)-(u:ℂ)) by ring,div_neg]

lemma negative_source_point_reach {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) (hzero : driver 0=0)
    {ε T S : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (hS : 0 ≤ S) (hST : S ≤ T)
    (U : C(I, ℝ)) (hU : EqOn (extendDriver T U) (fun s => -driver s) (Icc 0 T))
    (x a β δ d y : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (haδ : a ≤ 2-4*δ) (hd : 0 < d) (hdx : d < δ*x) (hεx : 2*ε < x) (hy : δ*ε < y)
    (w : ℂ) (hw : w ∈ localizationDomain γ S) (hclose : dist w ((-x:ℝ):ℂ) < d)
    (hwS : g S w=(driver S:ℂ)+(y:ℂ)*Complex.I) :
    reach U hε hT x β a ((δ/(4*d))^β) := by
  apply tip_forces_reach hε hT hS hST U (by rw [hU ⟨le_rfl,hT⟩]; simp [hzero]) x a β δ d y
    hβ hδ hδhalf haδ hd hdx hεx hy (fun t => mirror (g t w))
    (continuous_mirror.comp_continuousOn (h.continuous_eval hS hw))
  · intro t ht
    rw [hU ⟨ht.1.le,ht.2.le.trans hST⟩]
    exact mirror_ode (h.hasDerivAt_eval ht.1 (survivingDomain_mono ht.2.le hw))
  · rw [h.initial w hw.1.1,mirror_dist_real]
    exact hclose.le
  · intro t ht
    rw [mirror_im]
    have hh := h.height_antitone hS hw ht ⟨hS,le_rfl⟩ ht.2
    dsimp only at hh
    rw [hwS] at hh
    simpa using hh
  · rw [mirror_re,hwS,hU ⟨hS,hST⟩]
    simp

lemma negative_source_hit_eventually_reach {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ : ℝ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω=0)
    (x a β δ d : ℝ) (hx : 0 < x) (hβ : 0 < β) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (haδ : a ≤ 2-4*δ) (hd : 0 < d) (hdx : d < δ*x)
    (hhit : ∃ t : ℝ, 0 ≤ t ∧ dist (γ ω t) ((-x:ℝ):ℂ) < d) :
    ∀ᶠ n : ℕ in atTop, reach (BrownianDriver.path (-B) (Real.sqrt κ) (n+1) ω)
      (CanonicalTrace.height_pos n) (n+1 : ℝ≥0).coe_nonneg x β a ((δ/(4*d))^β) := by
  obtain ⟨t,ht,hclose⟩ := hhit
  obtain ⟨w,y,hy,hwd,hw,hwS⟩ := inverse_tip_point h ht hclose
  have hsmall : ∀ᶠ n : ℕ in atTop, CanonicalTrace.height n < min (x/2) (y/δ) :=
    (CanonicalTrace.height_tendsto.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (lt_min (half_pos hx) (div_pos hy hδ)))
  have hlarge : ∀ᶠ n : ℕ in atTop, t ≤ ((n+1:ℝ≥0):ℝ) := by
    have hh : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa only [NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hh.eventually (eventually_ge_atTop t)
  filter_upwards [hsmall,hlarge] with n hn htn
  have hn' := lt_min_iff.mp hn
  have hxcut : 2*CanonicalTrace.height n < x := by linarith [hn'.1]
  have hycut : δ*CanonicalTrace.height n < y := by
    have hh := (lt_div_iff₀ hδ).mp hn'.2
    simpa only [mul_comm] using hh
  apply negative_source_point_reach h (by simp [hb0]) (CanonicalTrace.height_pos n)
    (n+1:ℝ≥0).coe_nonneg ht htn (BrownianDriver.path (-B) (Real.sqrt κ) (n+1) ω)
    (fun s hs => by
      have he := BrownianDriver.extend_eq (-B) (Real.sqrt κ) (n+1) ω hc.neg hs
      change extendDriver ((n+1:ℝ≥0):ℝ) (BrownianDriver.path (-B) (Real.sqrt κ) (n+1) ω) s =
        Real.sqrt κ*(-B s.toNNReal ω) at he
      simpa only [mul_neg] using he)
    x a β δ d y hβ hδ hδhalf haδ hd hdx hxcut hycut w hw hwd hwS

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen
open BoundaryFunctional Swallowing

theorem negative_real_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ β a δ : ℝ)
    (hκ : 0 ≤ κ) (hβ : 0 < β) (ha : 0 ≤ a) (hba : κ*(β+1) ≤ 4+2*a)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1/2) (haδ : a ≤ 2-4*δ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ ω ∂P, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) :
    P {ω | ∃ t : ℝ, 0 ≤ t ∧ dist (γ ω t) ((-x:ℝ):ℂ) < d} ≤ ENNReal.ofReal ((4*d/(δ*x))^β) := by
  by_cases hdx : d < δ*x
  · let L : ℝ := (δ/(4*d))^β
    have hL : 0 < L := Real.rpow_pos_of_pos (by positivity) _
    have hm (n : ℕ) := uniformBudget_mean hB.neg κ β a hκ hβ.le ha hba x L hx n
    have hE : ∀ᵐ ω ∂P, (∃ t : ℝ, 0 ≤ t ∧ dist (γ ω t) ((-x:ℝ):ℂ) < d) →
        ∀ᶠ n : ℕ in atTop, L ≤ uniformBudget (-B) κ β a x L n ω := by
      filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hh hc hb0
      intro hhit
      filter_upwards [negative_source_hit_eventually_reach B κ γ g f ω hh hc hb0 x a β δ d hx hβ hδ hδhalf haδ hd hdx hhit] with n hn
      have hb := budget_dominates_reach (-B) κ β a hκ hβ.le ha hba (CanonicalTrace.height_pos n)
        (n+1) (by positivity) x L ω hc.neg (by simpa using congrArg Neg.neg hb0) hn
      exact hb.trans (uniformBudget_dominates (-B) κ β a x L hβ.le hx n ω)
    have hh := measure_eventually_budget (uniformBudget (-B) κ β a x L) (x^(-β)) L hL
      (fun n => (hm n).1) (fun n => (hm n).2.2) (fun n => (hm n).2.1) _ hE
    rwa [ratio_power_eq hx hd hδ] at hh
  · have hratio : 1 ≤ 4*d/(δ*x) := by
      rw [le_div_iff₀ (mul_pos hδ hx)]
      have hh : δ*x ≤ d := not_lt.1 hdx
      linarith
    have hp : 1 ≤ (4*d/(δ*x))^β := Real.one_le_rpow hratio hβ.le
    exact (prob_le_one).trans (by simpa using ENNReal.ofReal_le_ofReal hp)

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen

theorem real_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ β a δ : ℝ)
    (hκ : 0 ≤ κ) (hβ : 0 < β) (ha : 0 ≤ a) (hba : κ*(β+1) ≤ 4+2*a)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1/2) (haδ : a ≤ 2-4*δ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ ω ∂P, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    {x d : ℝ} (hx : 0 < |x|) (hd : 0 < d) :
    P {ω | ∃ t : ℝ, 0 ≤ t ∧ dist (γ ω t) (x:ℂ) < d} ≤ ENNReal.ofReal ((4*d/(δ*|x|))^β) := by
  rcases le_or_gt 0 x with hpos | hneg
  · rw [abs_of_nonneg hpos] at hx ⊢
    exact positive_real_bound hB κ β a δ hκ hβ ha hba hδ hδhalf haδ γ g f hmaps hx hd
  · have hh := negative_real_bound hB κ β a δ hκ hβ ha hba hδ hδhalf haδ γ g f hmaps (neg_pos.2 hneg) hd
    simpa only [neg_neg,abs_of_neg hneg] using hh

lemma annulus_real_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ β a δ : ℝ)
    (hκ : 0 ≤ κ) (hβ : 0 < β) (ha : 0 ≤ a) (hba : κ*(β+1) ≤ 4+2*a)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1/2) (haδ : a ≤ 2-4*δ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ ω ∂P, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    {x d : ℝ} (hx : 1/4 ≤ |x|) (hd : 0 < d) :
    P {ω | ∃ t : ℝ, 0 ≤ t ∧ dist (γ ω t) (x:ℂ) < d} ≤ ENNReal.ofReal ((16/δ)^β*d^β) := by
  have hxp : 0 < |x| := lt_of_lt_of_le (by norm_num) hx
  refine (real_bound hB κ β a δ hκ hβ ha hba hδ hδhalf haδ γ g f hmaps hxp hd).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hr : 4*d/(δ*|x|) ≤ (16/δ)*d := by
    rw [div_le_iff₀ (mul_pos hδ hxp)]
    have hh := mul_le_mul_of_nonneg_left hx (show 0 ≤ 16*d by positivity)
    field_simp
    nlinarith
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 4*d/(δ*|x|)) hr hβ.le
  rwa [Real.mul_rpow (by positivity : 0 ≤ 16/δ) hd.le] at hh

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.AngularBarrier

def lowerGamma (b s : ℝ) : ℝ := ∫ x in (0:ℝ)..s, Real.exp (-x)*x^(b-1)

def cdf (b s : ℝ) : ℝ := lowerGamma b s / Real.Gamma b

def pdf (b s : ℝ) : ℝ := Real.exp (-s)*s^(b-1)/Real.Gamma b

lemma integrable_kernel {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : 0 ≤ s) :
    IntervalIntegrable (fun x : ℝ => Real.exp (-x)*x^(b-1)) volume 0 s := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs]
  exact (Real.GammaIntegral_convergent hb).mono_set Ioc_subset_Ioi_self

lemma kernel_continuousAt (b : ℝ) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (fun x : ℝ => Real.exp (-x)*x^(b-1)) s :=
  Real.continuous_exp.continuousAt.comp continuousAt_neg |>.mul
    (continuousAt_id.rpow_const (Or.inl hs.ne'))

lemma lowerGamma_nonneg {b : ℝ} (_hb : 0 < b) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ lowerGamma b s := by
  apply intervalIntegral.integral_nonneg hs
  intro x hx
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx.1 _)

lemma cdf_nonneg {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ cdf b s :=
  div_nonneg (lowerGamma_nonneg hb hs) (Real.Gamma_pos_of_pos hb).le

lemma pdf_pos {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : 0 < s) : 0 < pdf b s :=
  div_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hs _)) (Real.Gamma_pos_of_pos hb)

lemma power_integral {b : ℝ} (hb : 0 < b) {s : ℝ} (_hs : 0 ≤ s) :
    (∫ x in (0:ℝ)..s, x^(b-1)) = s^b/b := by
  rw [integral_rpow (Or.inl (by linarith : -1 < b-1))]
  rw [show b-1+1 = b by ring, Real.zero_rpow hb.ne', sub_zero]

lemma cdf_le_power {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : 0 ≤ s) :
    cdf b s ≤ s^b/(b*Real.Gamma b) := by
  have hmono : lowerGamma b s ≤ ∫ x in (0:ℝ)..s, x^(b-1) := by
    apply intervalIntegral.integral_mono_on hs (integrable_kernel hb hs)
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < b-1))
    intro x hx
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.2 (neg_nonpos.2 hx.1)) (Real.rpow_nonneg hx.1 (b-1))
  rw [power_integral hb hs] at hmono
  have hh := div_le_div_of_nonneg_right hmono (Real.Gamma_pos_of_pos hb).le
  simpa only [cdf, div_div] using hh

lemma hasDerivAt_lowerGamma {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (lowerGamma b) (Real.exp (-s)*s^(b-1)) s := by
  apply intervalIntegral.integral_hasDerivAt_right (integrable_kernel hb hs.le)
  · exact (Real.measurable_exp.comp measurable_neg |>.mul
      (measurable_id.pow_const (b-1))).aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact kernel_continuousAt b hs

lemma hasDerivAt_cdf {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (cdf b) (pdf b s) s :=
  (hasDerivAt_lowerGamma hb hs).div_const (Real.Gamma b)

lemma deriv_cdf {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : 0 < s) :
    deriv (cdf b) s = pdf b s := (hasDerivAt_cdf hb hs).deriv

lemma hasDerivAt_pdf {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (pdf b) (pdf b s*((b-1)/s-1)) s := by
  have hd := (((hasDerivAt_neg s).exp).mul
    ((hasDerivAt_id s).rpow_const (p:=b-1) (Or.inl hs.ne'))).div_const (Real.Gamma b)
  apply hd.congr_deriv
  unfold pdf
  simp only [id_eq]
  rw [Real.rpow_sub_one hs.ne' (b-1)]
  field_simp
  ring

lemma lowerGamma_tendsto {b : ℝ} (hb : 0 < b) :
    Tendsto (lowerGamma b) atTop (𝓝 (Real.Gamma b)) := by
  rw [Real.Gamma_eq_integral hb]
  exact intervalIntegral_tendsto_integral_Ioi 0 (Real.GammaIntegral_convergent hb) tendsto_id

lemma cdf_tendsto {b : ℝ} (hb : 0 < b) : Tendsto (cdf b) atTop (𝓝 1) := by
  change Tendsto (fun s => lowerGamma b s / Real.Gamma b) atTop (𝓝 1)
  have hh := (lowerGamma_tendsto hb).div_const (Real.Gamma b)
  convert hh using 1
  rw [div_self (Real.Gamma_pos_of_pos hb).ne']

lemma power_mul {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    x^(b-1)*x = x^b := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x; simp [Real.zero_rpow hb.ne']
  · rw [← Real.rpow_add_one h.ne', sub_add_cancel]

lemma kernel_lower {b s x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    Real.exp (-s)*((1+s)*x^(b-1)-x^b) ≤ Real.exp (-x)*x^(b-1) := by
  have hh := Real.add_one_le_exp (s-x)
  have he : Real.exp (-s)*Real.exp (s-x) = Real.exp (-x) := by
    rw [← Real.exp_add]; congr 1; ring
  have hi := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hh (Real.exp_pos (-s)).le) (Real.rpow_nonneg hx (b-1))
  rw [he] at hi
  calc
    _ = Real.exp (-s)*(s-x+1)*x^(b-1) := by rw [← power_mul hb hx]; ring
    _ ≤ _ := hi

lemma lowerGamma_lower {b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s) :
    Real.exp (-s)*((1+s)*s^b/b-s^(b+1)/(b+1)) ≤ lowerGamma b s := by
  have hi₁ : IntervalIntegrable (fun x : ℝ => x^(b-1)) volume 0 s :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi₂ : IntervalIntegrable (fun x : ℝ => x^b) volume 0 s :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hh := intervalIntegral.integral_mono_on hs
    (((hi₁.const_mul (1+s)).sub hi₂).const_mul (Real.exp (-s)))
    (integrable_kernel hb hs) (fun x hx => kernel_lower hb hx.1 (s:=s))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hi₁.const_mul _) hi₂,
    intervalIntegral.integral_const_mul, power_integral hb hs] at hh
  have hi₂eq : (∫ x in (0:ℝ)..s, x^b) = s^(b+1)/(b+1) := by
    simpa only [add_sub_cancel_right] using power_integral (by linarith : 0 < b+1) hs
  rw [hi₂eq] at hh
  simpa only [lowerGamma, mul_div_assoc] using hh

lemma cdf_pdf_inequality {b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    s^2*pdf b s/(b+1) ≤ b*cdf b s-s*pdf b s := by
  have hl := lowerGamma_lower hb hs.le
  have hg : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
  have hbp : 0 < b+1 := by linarith
  rw [Real.rpow_add_one hs.ne' b] at hl
  have heq : s^b = s^(b-1)*s := (power_mul hb hs.le).symm
  rw [heq] at hl
  unfold cdf pdf
  apply (div_le_div_iff_of_pos_right hg).1
  have hh := mul_le_mul_of_nonneg_left hl hb.le
  field_simp [hb.ne', hbp.ne'] at hh ⊢
  nlinarith

lemma contDiffAt_pdf (n : WithTop ℕ∞) (b : ℝ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n (pdf b) s := by
  have he : ContDiffAt ℝ n (fun x : ℝ => Real.exp (-x)) s :=
    (contDiffAt_id.neg).exp
  have hp : ContDiffAt ℝ n (fun x : ℝ => x^(b-1)) s :=
    contDiffAt_id.rpow contDiffAt_const hs.ne'
  exact (he.mul hp).div_const _

lemma contDiffOn_cdf {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ContDiffOn ℝ (n+1) (cdf b) (Ioi 0) := by
  rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun s hs => (hasDerivAt_cdf hb hs).differentiableAt.differentiableWithinAt,
    ?_, ?_⟩
  · intro hn; simp at hn
  · have hh : ContDiffOn ℝ n (pdf b) (Ioi 0) :=
      fun s hs => (contDiffAt_pdf n b hs).contDiffWithinAt
    exact hh.congr (fun s hs => deriv_cdf hb hs)

lemma contDiffAt_cdf {b : ℝ} (hb : 0 < b) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n (cdf b) s := by
  have hh := (contDiffOn_cdf hb n).contDiffAt (isOpen_Ioi.mem_nhds hs)
  exact hh.of_le (by exact_mod_cast Nat.le_succ n)

def scale (l b t : ℝ) := (Real.exp (l*t)-1)/(2*(b+1))

def value (l b t q : ℝ) := Real.exp (l*b/2*t)*cdf b (q/scale l b t)

def valueQ (l b t q : ℝ) := Real.exp (l*b/2*t)*pdf b (q/scale l b t)/scale l b t

def valueQQ (l b t q : ℝ) := Real.exp (l*b/2*t)*pdf b (q/scale l b t)*
  ((b-1)/(q/scale l b t)-1)/(scale l b t)^2

def valueT (l b t q : ℝ) := l*b/2*value l b t q -
  Real.exp (l*b/2*t)*pdf b (q/scale l b t)*(q/scale l b t)*
    (l+l/(2*(b+1)*scale l b t))

lemma scale_pos {l b t : ℝ} (hl : 0 < l) (hb : 0 < b) (ht : 0 < t) :
    0 < scale l b t := by
  apply div_pos
  · exact sub_pos.2 (Real.one_lt_exp_iff.2 (mul_pos hl ht))
  · positivity

lemma hasDerivAt_scale (l b t : ℝ) :
    HasDerivAt (scale l b) (l*Real.exp (l*t)/(2*(b+1))) t := by
  apply (((((hasDerivAt_id t).const_mul l).exp).sub_const 1).div_const (2*(b+1))).congr_deriv
  simp only [id_eq]
  ring

lemma hasDerivAt_value_q {l b t q : ℝ} (hl : 0 < l) (hb : 0 < b)
    (ht : 0 < t) (hq : 0 < q) : HasDerivAt (value l b t) (valueQ l b t q) q := by
  have hs := scale_pos hl hb ht
  have hh := ((hasDerivAt_cdf hb (div_pos hq hs)).comp q
    ((hasDerivAt_id q).div_const (scale l b t))).const_mul (Real.exp (l*b/2*t))
  apply hh.congr_deriv
  dsimp only [valueQ]
  ring

lemma hasDerivAt_valueQ_q {l b t q : ℝ} (hl : 0 < l) (hb : 0 < b)
    (ht : 0 < t) (hq : 0 < q) : HasDerivAt (valueQ l b t) (valueQQ l b t q) q := by
  have hs := scale_pos hl hb ht
  have hh := (((hasDerivAt_pdf hb (div_pos hq hs)).comp q
    ((hasDerivAt_id q).div_const (scale l b t))).const_mul (Real.exp (l*b/2*t))).div_const (scale l b t)
  apply hh.congr_deriv
  dsimp only [valueQQ]
  ring

lemma hasDerivAt_value_t {l b t q : ℝ} (hl : 0 < l) (hb : 0 < b)
    (ht : 0 < t) (hq : 0 < q) :
    HasDerivAt (fun s => value l b s q) (valueT l b t q) t := by
  have hs := scale_pos hl hb ht
  have hbp : b+1 ≠ 0 := by positivity
  have hh := ((((hasDerivAt_id t).const_mul (l*b/2)).exp).mul
    ((hasDerivAt_cdf hb (div_pos hq hs)).comp t ((hasDerivAt_const t q).div (hasDerivAt_scale l b t) hs.ne')))
  apply hh.congr_deriv
  simp only [id_eq, Function.comp_def, Pi.div_apply]
  dsimp only [valueT, value]
  have he : Real.exp (l*t) = 2*(b+1)*scale l b t+1 := by unfold scale; field_simp; ring
  rw [he]
  field_simp
  ring

theorem supersolution {l b t q : ℝ} (hl : 0 < l) (hb : 0 < b)
    (ht : 0 < t) (hq : 0 < q) (hq1 : q ≤ 1) :
    l*q*(1-q)*valueQQ l b t q +
      l*((1-b)-(3/2-b)*q)*valueQ l b t q ≤ valueT l b t q := by
  let α := scale l b t
  let s := q/α
  let W := pdf b s
  let F := cdf b s
  have hα : 0 < α := scale_pos hl hb ht
  have hs : 0 < s := div_pos hq hα
  have hW : 0 ≤ W := (pdf_pos hb hs).le
  have hbp : 0 < b+1 := by linarith
  have hi : s^2*W/(b+1) ≤ b*F-s*W := cdf_pdf_inequality hb hs
  have hαs : α*s = q := by dsimp [s]; field_simp
  have hA : 0 ≤ 1-1/(2*(b+1)) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  have hrest : 0 ≤ l*(1-1/(2*(b+1)))*(1-q)*s*W/α := by
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hl.le hA) (sub_nonneg.2 hq1)) hs.le) hW) hα.le
  have hmain : 0 ≤ l/2*(b*F-s*W-s^2*W/(b+1)) := mul_nonneg (by positivity) (sub_nonneg.2 hi)
  have he : valueT l b t q - (l*q*(1-q)*valueQQ l b t q +
        l*((1-b)-(3/2-b)*q)*valueQ l b t q) =
      Real.exp (l*b/2*t) *
        (l/2*(b*F-s*W-s^2*W/(b+1)) + l*(1-1/(2*(b+1)))*(1-q)*s*W/α) := by
    dsimp only [valueT, value, valueQQ, valueQ]
    change l*b/2*(Real.exp (l*b/2*t)*F) - Real.exp (l*b/2*t)*W*s*
        (l+l/(2*(b+1)*α)) - (l*q*(1-q)*(Real.exp (l*b/2*t)*W*((b-1)/s-1)/α^2) +
        l*((1-b)-(3/2-b)*q)*(Real.exp (l*b/2*t)*W/α)) = _
    dsimp only [s]
    field_simp
    ring
  have hh : 0 ≤ valueT l b t q - (l*q*(1-q)*valueQQ l b t q +
      l*((1-b)-(3/2-b)*q)*valueQ l b t q) := by
    rw [he]
    exact mul_nonneg (Real.exp_pos _).le (add_nonneg hmain hrest)
  exact sub_nonneg.1 hh

lemma value_nonneg {l b t q : ℝ} (hl : 0 < l) (hb : 0 < b)
    (ht : 0 < t) (hq : 0 ≤ q) : 0 ≤ value l b t q :=
  mul_nonneg (Real.exp_pos _).le (cdf_nonneg hb (div_nonneg hq (scale_pos hl hb ht).le))

lemma contDiffAt_value {l b : ℝ} (hl : 0 < l) (hb : 0 < b) (n : ℕ)
    {v : ℝ × ℝ} (ht : 0 < v.1) (hq : 0 < v.2) :
    ContDiffAt ℝ n (fun v : ℝ × ℝ => value l b v.1 v.2) v := by
  have he : ContDiffAt ℝ n (fun v : ℝ × ℝ => Real.exp (l*b/2*v.1)) v := by fun_prop
  have ha : ContDiffAt ℝ n (fun v : ℝ × ℝ => scale l b v.1) v := by
    unfold scale; fun_prop
  have hs := scale_pos hl hb ht
  have hqf : ContDiffAt ℝ n (fun v : ℝ × ℝ => v.2/scale l b v.1) v :=
    contDiffAt_snd.div ha hs.ne'
  have hh := (contDiffAt_cdf hb n (div_pos hq hs)).comp v hqf
  dsimp only [Function.comp_def] at hh
  exact he.mul hh

lemma continuousAt_value {l b : ℝ} (hl : 0 < l) (hb : 0 < b)
    {v : ℝ × ℝ} (ht : 0 < v.1) (hq : 0 < v.2) :
    ContinuousAt (fun v : ℝ × ℝ => value l b v.1 v.2) v :=
  (contDiffAt_value hl hb 0 ht hq).continuousAt

lemma scale_tendsto {l b : ℝ} (hl : 0 < l) (hb : 0 < b) :
    Tendsto (scale l b) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · have hh : Continuous (scale l b) := by unfold scale; fun_prop
    simpa [scale] using (hh.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact scale_pos hl hb ht

lemma value_tendsto_zero_time {l b q : ℝ} (hl : 0 < l) (hb : 0 < b) (hq : 0 < q) :
    Tendsto (fun t => value l b t q) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hs : Tendsto (fun t => q/scale l b t) (𝓝[>] (0:ℝ)) atTop := by
    simpa only [div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_nhdsGT_zero.comp (scale_tendsto hl hb)).const_mul_atTop hq
  have he : Tendsto (fun t : ℝ => Real.exp (l*b/2*t)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hh : Continuous (fun t : ℝ => Real.exp (l*b/2*t)) := by fun_prop
    simpa using (hh.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  simpa only [value, one_mul, Function.comp_def] using he.mul ((cdf_tendsto hb).comp hs)

end SLEExactGauge.AngularBarrier

end

end

end OAI
