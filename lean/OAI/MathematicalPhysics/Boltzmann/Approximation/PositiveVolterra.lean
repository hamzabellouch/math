import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralBound
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Approximation.SurvivalVolterraIntegrable
import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicCoordinates
import OAI.MathematicalPhysics.Boltzmann.Branching.LogarithmicIteration
import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedKernelAction
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.MeasurableLIntegral

namespace OAI

section

/-! # Positive backward gain iteration on free kinetic characteristics -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

def flight (z : Published.KineticPhase) (s : ℝ) : Published.KineticPhase :=
  ((s,z.1.2-(z.1.1-s) • z.2),z.2)

def step (a : ℝ) (K : Kernel Published.KineticPhase Velocity)
    (f : Published.KineticPhase → ℝ≥0∞) (z : Published.KineticPhase) : ℝ≥0∞ :=
  ∫⁻ s in Ioc a z.1.1, ∫⁻ v, f ((flight z s).1,v) ∂K (flight z s)

theorem step_mono (a : ℝ) (K : Kernel Published.KineticPhase Velocity)
    {f g : Published.KineticPhase → ℝ≥0∞} (h : f ≤ g) : step a K f ≤ step a K g := by
  intro z
  exact lintegral_mono (fun _ => lintegral_mono (fun _ => h _))

theorem step_inner_measurable (K : Kernel Published.KineticPhase Velocity) [IsSFiniteKernel K]
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (z : Published.KineticPhase) :
    Measurable (fun s => ∫⁻ v, f ((flight z s).1,v) ∂K (flight z s)) := by
  have hflight : Measurable (flight z) := by unfold flight; fun_prop
  let J := K.comap (flight z) hflight
  have hm : Measurable (Function.uncurry (fun s v => f ((flight z s).1,v))) := by
    apply hf.comp
    unfold flight
    fun_prop
  exact hm.lintegral_kernel_prod_right (κ := J)

theorem step_add (a : ℝ) (K : Kernel Published.KineticPhase Velocity) [IsSFiniteKernel K]
    {f g : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    step a K (f+g) = step a K f+step a K g := by
  funext z
  unfold step
  simp only [Pi.add_apply]
  have hi (s : ℝ) : Measurable (fun v => f ((flight z s).1,v)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  simp_rw [lintegral_add_left (hi _)]
  exact lintegral_add_left (step_inner_measurable K hf z) _

theorem step_le_constant {a t C B : ℝ} (ha : 0 < a) (hat : a ≤ t)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (K : Kernel Published.KineticPhase Velocity)
    {f : Published.KineticPhase → ℝ≥0∞} {z : Published.KineticPhase} (hzt : z.1.1 = t)
    (hmass : ∀ s ∈ Ioc a t, K (flight z s) univ ≤ ENNReal.ofReal (C/s))
    (hf : ∀ s ∈ Ioc a t, ∀ v, f ((flight z s).1,v) ≤ ENNReal.ofReal B) :
    step a K f z ≤ ENNReal.ofReal (B*(C*Real.log (t/a))) := by
  unfold step
  rw [hzt]
  calc
    _ ≤ ∫⁻ s in Ioc a t, ENNReal.ofReal B*ENNReal.ofReal (C/s) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      calc
        _ ≤ ∫⁻ _v, ENNReal.ofReal B ∂K (flight z s) := lintegral_mono (hf s hs)
        _ = ENNReal.ofReal B*K (flight z s) univ := by rw [lintegral_const,mul_comm]
        _ ≤ _ := mul_le_mul' le_rfl (hmass s hs)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,time_mass ha hat hC,
        ← ENNReal.ofReal_mul hB]

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Removing positive-source cutoffs in a characteristic lower bound -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.Published
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [SFinite ν]

theorem positive_volterra_limit {f : ℕ → ℝ × P → ℝ} {g : ℝ × P → ℝ}
    {a : (ℝ × P) × ℝ → ℝ} {c u : ℝ × P → ℝ}
    (hfi : ∀ n, Integrable (f n) (μ.prod ν))
    (hfn : ∀ n z, 0 ≤ f n z) (hgm : Measurable g) (hgn : ∀ z, 0 ≤ g z)
    (ha : Measurable a) (hab : ∀ z, 0 ≤ a z ∧ a z ≤ 1)
    (ht : ∀ᵐ z ∂μ.prod ν, Tendsto (fun n => f n z) atTop (𝓝 (g z)))
    (hb : ∀ n, ∀ᵐ z ∂μ.prod ν, c z+survivalVolterra μ a (f n) z ≤ u z) :
    ∀ᵐ z ∂μ.prod ν,
      Integrable (fun s => if s ≤ z.1 then a (z,s)*g (s,z.2) else 0) μ ∧
      c z+survivalVolterra μ a g z ≤ u z := by
  have hpi : ∀ᵐ p ∂ν, ∀ n, Integrable (fun s => f n (s,p)) μ := by
    rw [ae_all_iff]
    exact fun n => (hfi n).prod_left_ae
  have hpt : ∀ᵐ p ∂ν, ∀ᵐ s ∂μ, Tendsto (fun n => f n (s,p)) atTop (𝓝 (g (s,p))) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae ht)
  have hball : ∀ᵐ z ∂μ.prod ν, ∀ n, c z+survivalVolterra μ a (f n) z ≤ u z := by
    rw [ae_all_iff]
    exact hb
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hpi,
    Measure.quasiMeasurePreserving_snd.ae hpt,hball] with z hzi hzt hzb
  let A n s := if s ≤ z.1 then a (z,s)*f n (s,z.2) else 0
  let B s := if s ≤ z.1 then a (z,s)*g (s,z.2) else 0
  have ham : Measurable (fun s => a (z,s)) := ha.comp (measurable_const.prodMk measurable_id)
  have hai n : Integrable (A n) μ := by
    change Integrable ((Iic z.1).indicator (fun s => a (z,s)*f n (s,z.2))) μ
    exact ((hzi n).bdd_mul ham.aestronglyMeasurable
      (ae_of_all _ (fun s => (abs_of_nonneg (hab (z,s)).1).trans_le (hab (z,s)).2))).indicator
        (s := Iic z.1) measurableSet_Iic
  have han n : 0 ≤ᵐ[μ] A n := ae_of_all _ (fun s => by
    dsimp [A]
    split
    · exact mul_nonneg (hab _).1 (hfn _ _)
    · exact le_rfl)
  have hbm : Measurable B :=
    (ham.mul (hgm.comp (measurable_id.prodMk measurable_const))).ite
      (measurableSet_le measurable_id measurable_const) measurable_const
  have hbn : 0 ≤ᵐ[μ] B := ae_of_all _ (fun s => by
    dsimp [B]
    split
    · exact mul_nonneg (hab _).1 (hgn _)
    · exact le_rfl)
  have hbt : ∀ᵐ s ∂μ, Tendsto (fun n => A n s) atTop (𝓝 (B s)) := by
    filter_upwards [hzt] with s hs
    dsimp only [A,B]
    split
    · exact tendsto_const_nhds.mul hs
    · exact tendsto_const_nhds
  have hC : 0 ≤ u z-c z := by
    have h0 := integral_nonneg_of_ae (han 0)
    have hb0 := hzb 0
    change c z+(∫ s, A 0 s ∂μ) ≤ u z at hb0
    linarith
  have h := positive_integral_limit hai han hbm.aestronglyMeasurable hbn hbt hC (fun n => by
    have h := hzb n
    change c z+(∫ s, A n s ∂μ) ≤ u z at h
    linarith)
  refine ⟨h.1,?_⟩
  change c z+(∫ s, B s ∂μ) ≤ u z
  linarith [h.2]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A finite logarithmic bound for repeated positive gains

The bound omits the factorial improvement: for a fixed number of gains this
polynomial bound suffices for the small-lower-time remainder in §8.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

def iterate (a : ℝ) (K : Kernel KineticPhase Velocity)
    (f : KineticPhase → ℝ≥0∞) : ℕ → KineticPhase → ℝ≥0∞
  | 0 => f
  | n+1 => step a K (iterate a K f n)

theorem iterate_bound {a T C B : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (K : Kernel KineticPhase Velocity) {f : KineticPhase → ℝ≥0∞}
    (hK : ∀ z : KineticPhase, z.1.1 ∈ Icc a T → K z univ ≤ ENNReal.ofReal (C/z.1.1))
    (hf : ∀ z : KineticPhase, z.1.1 ∈ Icc a T → f z ≤ ENNReal.ofReal B)
    (n : ℕ) : ∀ z : KineticPhase, z.1.1 ∈ Icc a T →
      iterate a K f n z ≤ ENNReal.ofReal (B*(C*Real.log (z.1.1/a))^n) := by
  induction n with
  | zero => simpa only [iterate,pow_zero,mul_one] using hf
  | succ n ih =>
    intro z hz
    have hlog : 0 ≤ Real.log (z.1.1/a) :=
      Real.log_nonneg ((one_le_div ha).mpr hz.1)
    have hD : 0 ≤ B*(C*Real.log (z.1.1/a))^n := by positivity
    have hb := step_le_constant ha hz.1 hC hD K (z := z) rfl
      (fun s hs => hK (flight z s) ⟨hs.1.le,hs.2.trans hz.2⟩) (f := iterate a K f n)
    have hi : ∀ s ∈ Ioc a z.1.1, ∀ v,
        iterate a K f n ((flight z s).1,v) ≤ ENNReal.ofReal (B*(C*Real.log (z.1.1/a))^n) := by
      intro s hs v
      have hsz : ((flight z s).1,v).1.1 ∈ Icc a T := ⟨hs.1.le,hs.2.trans hz.2⟩
      apply (ih _ hsz).trans
      apply ENNReal.ofReal_le_ofReal
      have hlogS : 0 ≤ Real.log (s/a) := Real.log_nonneg ((one_le_div ha).mpr hs.1.le)
      have hlogLe : Real.log (s/a) ≤ Real.log (z.1.1/a) :=
        Real.log_le_log (div_pos (ha.trans hs.1) ha)
          (div_le_div_of_nonneg_right hs.2 ha.le)
      change B*(C*Real.log (s/a))^n ≤ B*(C*Real.log (z.1.1/a))^n
      gcongr
    have hh := hb hi
    simpa only [iterate,pow_succ,mul_assoc] using hh

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Measurable positive iterates and localization to time slabs -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

theorem step_measurable (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) : Measurable (step a K f) := by
  have hflight : Measurable (fun p : KineticPhase × ℝ => flight p.1 p.2) := by
    unfold flight
    fun_prop
  let J := K.comap (fun p : KineticPhase × ℝ => flight p.1 p.2) hflight
  have hm : Measurable (fun p : (KineticPhase × ℝ) × Velocity =>
      f ((flight p.1.1 p.1.2).1,p.2)) :=
    hf.comp (((hflight.comp measurable_fst).fst).prodMk measurable_snd)
  have hi : Measurable (fun p : KineticPhase × ℝ =>
      ∫⁻ v, f ((flight p.1 p.2).1,v) ∂K (flight p.1 p.2)) :=
    hm.lintegral_kernel_prod_right' (κ := J)
  let D : Set (KineticPhase × ℝ) := {p | a < p.2 ∧ p.2 ≤ p.1.1.1}
  have hD : MeasurableSet D := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst.fst.fst)
  have h : Measurable (fun z : KineticPhase => ∫⁻ s : ℝ,
      D.indicator (fun p : KineticPhase × ℝ =>
        ∫⁻ v, f ((flight p.1 p.2).1,v) ∂K (flight p.1 p.2)) (z,s)) :=
    (hi.indicator hD).lintegral_prod_right'
  convert h using 1
  funext z
  rw [step,← lintegral_indicator measurableSet_Ioc]
  rfl

theorem iterate_measurable (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    Measurable (iterate a K f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact step_measurable a K ih

theorem step_slab_mono {a T : ℝ} (K : Kernel KineticPhase Velocity)
    {f g : KineticPhase → ℝ≥0∞}
    (h : ∀ z, z.1.1 ∈ Icc a T → f z ≤ g z)
    {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) : step a K f z ≤ step a K g z := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  apply lintegral_mono
  intro v
  exact h _ ⟨hs.1.le,hs.2.trans hz.2⟩

theorem iterate_slab_mono {a T : ℝ} (K : Kernel KineticPhase Velocity)
    {f g : KineticPhase → ℝ≥0∞}
    (h : ∀ z, z.1.1 ∈ Icc a T → f z ≤ g z) (n : ℕ) :
    ∀ z, z.1.1 ∈ Icc a T → iterate a K f n z ≤ iterate a K g n z := by
  induction n with
  | zero => exact h
  | succ n ih => exact fun _ hz => step_slab_mono K ih hz

theorem iterate_add (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {f g : KineticPhase → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    iterate a K (f+g) n = iterate a K f n+iterate a K g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterate,ih]
    exact step_add a K (iterate_measurable a K hf n)

theorem iterate_step (a : ℝ) (K : Kernel KineticPhase Velocity)
    (f : KineticPhase → ℝ≥0∞) (n : ℕ) :
    iterate a K (step a K f) n = iterate a K f (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate,ih]

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Representative invariance of finite-temperature positive iteration -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

theorem backward_measurePreserving (t : ℝ) (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving
      (fun z : ℝ × (Velocity × Velocity) => ((z.1,z.2.1-(t-z.1) • z.2.2),z.2.2))
      (μ.prod (volume : Measure (Velocity × Velocity))) ((μ.prod volume).prod volume) := by
  have h := (EuclideanFlight.characteristic_measurePreserving μ).comp
    ((MeasurePreserving.id μ).prod (EuclideanFlight.flight_measurePreserving (-t)))
  convert h using 1
  funext z
  exact (EuclideanFlight.characteristic_back z.2 t z.1).symm

theorem step_congr_ae_at (a t : ℝ) (K : Kernel KineticPhase Velocity)
    {f g : KineticPhase → ℝ≥0∞}
    (h : ChartKernel.action K f =ᵐ[((volume : Measure ℝ).prod volume).prod volume]
      ChartKernel.action K g) :
    (fun p : Velocity × Velocity => step a K f ((t,p.1),p.2)) =ᵐ[volume]
      (fun p => step a K g ((t,p.1),p.2)) := by
  have hb := (backward_measurePreserving t volume).quasiMeasurePreserving.ae h
  have hs := (measurePreserving_swap (μ := (volume : Measure (Velocity × Velocity)))
    (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae hb
  filter_upwards [ae_ae_of_ae_prod hs] with p hp
  exact lintegral_congr_ae (ae_restrict_of_ae hp)

theorem step_congr_ae (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {f g : KineticPhase → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (h : ChartKernel.action K f =ᵐ[((volume : Measure ℝ).prod volume).prod volume]
      ChartKernel.action K g) :
    step a K f =ᵐ[((volume : Measure ℝ).prod volume).prod volume] step a K g := by
  have hm : Measurable (fun z : ℝ × (Velocity × Velocity) => ((z.1,z.2.1),z.2.2)) := by
    fun_prop
  have he := (ae_prod_iff_ae_ae (measurableSet_eq_fun
    ((step_measurable a K hf).comp hm) ((step_measurable a K hg).comp hm))).mpr
    (ae_of_all volume (fun t => step_congr_ae_at a t K h))
  exact (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure Velocity)
    (volume : Measure Velocity)).quasiMeasurePreserving.ae he

theorem iterate_normalized_congr_ae (hcarleman : Published.GPV2009CarlemanInput)
    (a q : ℝ) (c : Kernel (ℝ × Velocity) Velocity) [IsSFiniteKernel c]
    {r : KineticPhase → ℝ≥0∞} (hr : Measurable r)
    (hc : ∀ x, c x = volume.withDensity (fun v => r (x,v)))
    {f g : KineticPhase → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[((volume : Measure ℝ).prod volume).prod volume] g) (n : ℕ) :
    iterate a (ChartKernel.inputKernel c q) f n =ᵐ[((volume : Measure ℝ).prod volume).prod volume]
      iterate a (ChartKernel.inputKernel c q) g n := by
  induction n with
  | zero => exact hfg
  | succ n ih =>
    exact step_congr_ae a _ (iterate_measurable a _ hf n) (iterate_measurable a _ hg n)
      (ChartKernel.action_normalized_congr_ae hcarleman _ c hr hc q
        (iterate_measurable a _ hf n) (iterate_measurable a _ hg n) ih)

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Finite residual expansion of a positive gain inequality -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

theorem residual_expansion {a T : ℝ} (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {f d : KineticPhase → ℝ≥0∞} (hd : Measurable d)
    (h : ∀ z, z.1.1 ∈ Icc a T → f z ≤ d z+step a K f z) (n : ℕ) :
    ∀ z, z.1.1 ∈ Icc a T →
      f z ≤ (∑ j ∈ Finset.range n, iterate a K d j z)+iterate a K f n z := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,zero_add,iterate,le_refl,implies_true]
  | succ n ih =>
    intro z hz
    have hi := iterate_slab_mono K h n z hz
    change iterate a K f n z ≤ iterate a K (d+step a K f) n z at hi
    rw [iterate_add a K hd,iterate_step] at hi
    change iterate a K f n z ≤ iterate a K d n z + iterate a K f (n+1) z at hi
    calc
      f z ≤ (∑ j ∈ Finset.range n, iterate a K d j z)+iterate a K f n z := ih z hz
      _ ≤ (∑ j ∈ Finset.range n, iterate a K d j z)+
          (iterate a K d n z+iterate a K f (n+1) z) := add_le_add le_rfl hi
      _ = _ := by rw [Finset.sum_range_succ,add_assoc]

theorem residual_logarithmic_bound {a T C B : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {f : KineticPhase → ℝ≥0∞}
    (hK : ∀ z : KineticPhase, z.1.1 ∈ Icc a T → K z univ ≤ ENNReal.ofReal (C/z.1.1))
    (h : ∀ z, z.1.1 ∈ Icc a T → f z ≤ ENNReal.ofReal B+step a K f z)
    (n : ℕ) {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    f z ≤ ENNReal.ofReal (B*∑ j ∈ Finset.range n, (C*Real.log (z.1.1/a))^j)+
      iterate a K f n z := by
  have he := residual_expansion K measurable_const h n z hz
  apply he.trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ ∑ j ∈ Finset.range n, ENNReal.ofReal (B*(C*Real.log (z.1.1/a))^j) := by
      apply Finset.sum_le_sum
      intro j _
      exact iterate_bound ha hC hB K hK (fun _ _ => le_rfl) j z hz
    _ = _ := by
      rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
      intro j _
      have hl := Real.log_nonneg ((one_le_div ha).mpr hz.1)
      positivity

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Finite scalar factors in positive Volterra iterations -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

theorem step_const_mul (a : ℝ) (K : Kernel KineticPhase Velocity)
    (f : KineticPhase → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ∞) :
    step a K (fun z => c*f z) = fun z => c*step a K f z := by
  funext z
  unfold step
  simp_rw [lintegral_const_mul' c _ hc]

theorem iterate_const_mul (a : ℝ) (K : Kernel KineticPhase Velocity)
    (f : KineticPhase → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ∞) (n : ℕ) :
    iterate a K (fun z => c*f z) n = fun z => c*iterate a K f n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step a K (iterate a K (fun z => c*f z) n) = _
    rw [ih]
    exact step_const_mul a K _ c hc

theorem iterate_const_bound {a T C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (K : Kernel KineticPhase Velocity)
    (hK : ∀ z : KineticPhase, z.1.1 ∈ Icc a T → K z univ ≤ ENNReal.ofReal (C/z.1.1))
    (c : ℝ≥0∞) (hc : c ≠ ∞) (n : ℕ) {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    iterate a K (fun _ => c) n z ≤ c*ENNReal.ofReal ((C*Real.log (z.1.1/a))^n) := by
  have he := congrFun (iterate_const_mul a K (fun _ => 1) c hc n) z
  simp only [mul_one] at he
  rw [he]
  apply mul_le_mul' le_rfl
  have hb := iterate_bound ha hC (by norm_num : (0:ℝ) ≤ 1) K hK
    (fun _ _ => by norm_num : ∀ w : KineticPhase, w.1.1 ∈ Icc a T → (1:ℝ≥0∞) ≤ ENNReal.ofReal 1) n z hz
  simpa only [one_mul] using hb

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Restricting an input to the time slab preserves its backward Volterra values -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

def onSlab (a T : ℝ) (f : KineticPhase → ℝ≥0∞) (z : KineticPhase) : ℝ≥0∞ :=
  {z : KineticPhase | z.1.1 ∈ Icc a T}.indicator f z

theorem onSlab_measurable (a T : ℝ) {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    Measurable (onSlab a T f) :=
  hf.indicator (measurableSet_Icc.preimage measurable_fst.fst)

theorem onSlab_eq {a T : ℝ} (f : KineticPhase → ℝ≥0∞) {z : KineticPhase}
    (hz : z.1.1 ∈ Icc a T) : onSlab a T f z = f z :=
  indicator_of_mem (show z ∈ {w : KineticPhase | w.1.1 ∈ Icc a T} from hz) _

theorem step_onSlab {a T : ℝ} (K : Kernel KineticPhase Velocity)
    (f : KineticPhase → ℝ≥0∞) {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    step a K (onSlab a T f) z = step a K f z := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  apply lintegral_congr
  intro v
  exact onSlab_eq f ⟨hs.1.le,hs.2.trans hz.2⟩

theorem iterate_onSlab {a T : ℝ} (K : Kernel KineticPhase Velocity)
    (f : KineticPhase → ℝ≥0∞) (n : ℕ) : ∀ z : KineticPhase, z.1.1 ∈ Icc a T →
      iterate a K (onSlab a T f) n z = iterate a K f n z := by
  induction n with
  | zero => exact fun _ hz => onSlab_eq f hz
  | succ n ih =>
    intro z hz
    exact le_antisymm (step_slab_mono K (fun w hw => (ih w hw).le) hz)
      (step_slab_mono K (fun w hw => (ih w hw).ge) hz)

theorem onSlab_positive_inequality {a T : ℝ} (K : Kernel KineticPhase Velocity)
    {f : KineticPhase → ℝ≥0∞} (c : ℝ≥0∞)
    (h : ∀ᵐ z ∂((volume : Measure ℝ).prod volume).prod volume,
      z.1.1 ∈ Icc a T → f z ≤ c+step a K f z) :
    onSlab a T f ≤ᵐ[((volume : Measure ℝ).prod volume).prod volume]
      fun z => c+step a K (onSlab a T f) z := by
  filter_upwards [h] with z hz
  by_cases ht : z.1.1 ∈ Icc a T
  · rw [onSlab_eq f ht,step_onSlab K f ht]
    exact hz ht
  · rw [onSlab,indicator_of_notMem (show z ∉ {w : KineticPhase | w.1.1 ∈ Icc a T} from ht)]
    exact bot_le

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Uniform bounds for a fixed finite number of gains on a time slab -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

theorem step_uniform_bound {a T : ℝ} (K : Kernel KineticPhase Velocity)
    {C B : ℝ≥0∞} (hK : ∀ z, z.1.1 ∈ Icc a T → K z univ ≤ C)
    {f : KineticPhase → ℝ≥0∞} (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ B)
    {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    step a K f z ≤ B*(C*ENNReal.ofReal (T-a)) := by
  unfold step
  calc
    _ ≤ ∫⁻ _s in Ioc a z.1.1, B*C := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have htime : s ∈ Icc a T := ⟨hs.1.le,hs.2.trans hz.2⟩
      calc
        _ ≤ ∫⁻ _v, B ∂K (flight z s) := lintegral_mono (fun v => hf _ htime)
        _ = B*K (flight z s) univ := by rw [lintegral_const,mul_comm]
        _ ≤ B*C := mul_le_mul' le_rfl (hK _ htime)
    _ ≤ B*C*ENNReal.ofReal (T-a) := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc]
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (sub_le_sub_right hz.2 a))
    _ = _ := mul_assoc _ _ _

theorem iterate_uniform_bound {a T : ℝ} (K : Kernel KineticPhase Velocity)
    {C B : ℝ≥0∞} (hK : ∀ z, z.1.1 ∈ Icc a T → K z univ ≤ C)
    {f : KineticPhase → ℝ≥0∞} (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ B) (n : ℕ) :
    ∀ z, z.1.1 ∈ Icc a T →
      iterate a K f n z ≤ B*(C*ENNReal.ofReal (T-a))^n := by
  induction n with
  | zero => simpa only [iterate,pow_zero,mul_one] using hf
  | succ n ih =>
    intro z hz
    have h := step_uniform_bound K hK ih hz
    simpa only [iterate,pow_succ,mul_assoc] using h

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Factorial time-simplex bounds for a uniformly bounded positive kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

theorem iterate_factorial_bound {T C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (K : Kernel KineticPhase Velocity)
    (hK : ∀ z, z.1.1 ∈ Icc 0 T → K z univ ≤ ENNReal.ofReal C)
    {f : KineticPhase → ℝ≥0∞} (hf : ∀ z, z.1.1 ∈ Icc 0 T → f z ≤ ENNReal.ofReal B)
    (n : ℕ) : ∀ z, z.1.1 ∈ Icc 0 T →
      iterate 0 K f n z ≤ ENNReal.ofReal (B*C^n*z.1.1^n/(n.factorial:ℝ)) := by
  induction n with
  | zero => simpa only [iterate,pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,div_one] using hf
  | succ n ih =>
    intro z hz
    let b : ℝ → ℝ := fun s => B*C^n*s^n/(n.factorial:ℝ)*C
    have hb (s : ℝ) (hs : 0 ≤ s) : 0 ≤ b s := by dsimp [b]; positivity
    have hi : IntegrableOn b (Ioc 0 z.1.1) := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.1).mp
        ((show Continuous b by dsimp [b]; fun_prop).intervalIntegrable 0 z.1.1)
    change step 0 K (iterate 0 K f n) z ≤ _
    unfold step
    calc
      _ ≤ ∫⁻ s in Ioc 0 z.1.1, ENNReal.ofReal (b s) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hst : s ∈ Icc 0 T := ⟨hs.1.le,hs.2.trans hz.2⟩
        calc
          _ ≤ ∫⁻ _v, ENNReal.ofReal (B*C^n*s^n/(n.factorial:ℝ)) ∂K (flight z s) :=
            lintegral_mono (fun v => ih _ hst)
          _ = ENNReal.ofReal (B*C^n*s^n/(n.factorial:ℝ))*K (flight z s) univ := by
            rw [lintegral_const,mul_comm]
          _ ≤ ENNReal.ofReal (B*C^n*s^n/(n.factorial:ℝ))*ENNReal.ofReal C :=
            mul_le_mul' le_rfl (hK _ hst)
          _ = ENNReal.ofReal (b s) := by
            exact (ENNReal.ofReal_mul (div_nonneg
              (mul_nonneg (mul_nonneg hB (pow_nonneg hC n)) (pow_nonneg hs.1.le n))
              (Nat.cast_nonneg _))).symm
      _ = ENNReal.ofReal (∫ s in 0..z.1.1, b s) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi]
        · rw [intervalIntegral.integral_of_le hz.1]
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact hb s hs.1.le
      _ = _ := by
        have he : b = fun s => (B*C^n*C/(n.factorial:ℝ))*s^n := by funext s; dsimp [b]; ring
        rw [he,intervalIntegral.integral_const_mul,integral_pow]
        simp only [zero_pow (Nat.succ_ne_zero n),sub_zero,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
        congr 1
        field_simp

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Separating the first two gains from bounded later factors -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

theorem iterate_count_add (a : ℝ) (K : Kernel KineticPhase Velocity)
    (f : KineticPhase → ℝ≥0∞) (n m : ℕ) :
    iterate a K f (n+m) = iterate a K (iterate a K f m) n := by
  induction n with
  | zero => simp only [Nat.zero_add,iterate]
  | succ n ih => simp only [Nat.succ_add,iterate,ih]

theorem iterate_first_two_le {a T : ℝ} (K : Kernel KineticPhase Velocity)
    (f : KineticPhase → ℝ≥0∞) (m : ℕ) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hf : ∀ z, z.1.1 ∈ Icc a T → iterate a K f m z ≤ C)
    {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    iterate a K f (m+2) z ≤ C*iterate a K (fun _ => 1) 2 z := by
  rw [Nat.add_comm m 2,iterate_count_add]
  apply (iterate_slab_mono K hf 2 z hz).trans_eq
  have he := congrFun (iterate_const_mul a K (fun _ => 1) C hC 2) z
  simpa only [mul_one] using he

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Integrating a signed source upper bound into one positive Volterra step -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

theorem step_source_upper {a t c : ℝ} (hat : a ≤ t)
    (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (p : Velocity × Velocity)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume a t) (δ : ℝ≥0∞)
    (hs : ∀ᵐ s ∂volume.restrict (Ioc a t),
      ENNReal.ofReal (g s) ≤ ChartKernel.action K f (flight ((t,p.1),p.2) s)+δ) :
    ENNReal.ofReal (c+∫ s in a..t, g s) ≤
      ENNReal.ofReal c+(step a K f ((t,p.1),p.2)+δ*ENNReal.ofReal (t-a)) := by
  apply (PositiveIntegral.ofReal_add_intervalIntegral_le hat hg).trans
  apply add_le_add le_rfl
  apply (lintegral_mono_ae hs).trans_eq
  have hm : Measurable (fun s => ChartKernel.action K f (flight ((t,p.1),p.2) s)) :=
    (ChartKernel.action_measurable K hf).comp (by unfold flight; fun_prop)
  rw [lintegral_add_left hm,lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc]
  rfl

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
