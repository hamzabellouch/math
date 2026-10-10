import Mathlib
import OAI.Probability.SKGap.Localization.DimensionDecay
import OAI.Probability.SKGap.Terminal.SpinSpectralMassBelow
import OAI.Probability.SKGap.Localization.PositiveRamp

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKGapCutoff.Regression

noncomputable def thresholdChoice {E F : Type*} (g : E → ℝ) (p q : E → F) (x : E) : F :=
  if 0 < g x then p x else q x

lemma thresholdChoice_measurable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {g : E → ℝ} {p q : E → F} (hg : Measurable g) (hp : Measurable p) (hq : Measurable q) :
    Measurable (thresholdChoice g p q) :=
  Measurable.ite (measurableSet_lt measurable_const hg) hp hq

lemma thresholdChoice_decomposition {E F : Type*} (g : E → ℝ) (p q : E → F)
    (f : F → ℝ) (x : E) :
    f (thresholdChoice g p q x) = f (q x)+(f (p x)-f (q x))*positiveIndicator (g x) := by
  by_cases hx : 0 < g x <;> simp [thresholdChoice, positiveIndicator, hx]

theorem ExponentialEmpiricalConcentration.threshold_map
    {E F : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E}
    {ν : Measure E} [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (g : E → ℝ) (p q : E → F) {K P Q : ℝ≥0}
    (hg : LipschitzWith K g) (hp : LipschitzWith P p) (hq : LipschitzWith Q q)
    (hz : ν {x | g x = 0} = 0) :
    ExponentialEmpiricalConcentration ρ
      (fun n h i => thresholdChoice g p q (X n h i)) (ν.map (thresholdChoice g p q)) := by
  intro f L hf B hB ε hε
  let D : ℝ≥0 := ‖B‖₊+1
  have hD : ∀ z, |f z| ≤ D := by
    intro z
    change |f z| ≤ |B|+1
    linarith [hB z, le_abs_self B]
  have hdiff : LipschitzWith (L*P+L*Q) (fun x => f (p x)-f (q x)) :=
    (hf.comp hp).sub (hf.comp hq)
  have hdiffB : ∀ x, |f (p x)-f (q x)| ≤ (2*D:ℝ≥0) := by
    intro x
    have ht := abs_sub (f (p x)) (f (q x))
    push_cast
    linarith [hD (p x), hD (q x)]
  have hbase := hX.average (fun x => f (q x)) (hf.comp hq) D (fun x => hD (q x))
  have hth := hX.threshold_average (fun x => f (p x)-f (q x)) g hdiff hg hdiffB hz
  have hh := (hbase.prod hth).continuous_map
    (f := fun z : ℝ × ℝ => z.1+z.2) (by fun_prop)
  have hiq := integrable_bounded_lipschitz ν (hf.comp hq) D (fun x => hD (q x))
  have hit : Integrable (fun x => (f (p x)-f (q x))*positiveIndicator (g x)) ν := by
    apply Integrable.of_bound
      ((hf.continuous.measurable.comp hp.continuous.measurable).sub
        (hf.continuous.measurable.comp hq.continuous.measurable) |>.mul
        (positiveIndicator_measurable.comp hg.continuous.measurable)).aestronglyMeasurable (2*D)
    filter_upwards [] with x
    change |(f (p x)-f (q x))*positiveIndicator (g x)| ≤ 2*(D:ℝ)
    rw [abs_mul, abs_of_nonneg (positiveIndicator_bounds (g x)).1]
    exact (mul_le_mul_of_nonneg_left (positiveIndicator_bounds (g x)).2 (abs_nonneg _)).trans
      (by simpa using hdiffB x)
  have hm : ∫ z, f z ∂ν.map (thresholdChoice g p q) =
      (∫ x, f (q x) ∂ν) + ∫ x, (f (p x)-f (q x))*positiveIndicator (g x) ∂ν := by
    rw [integral_map (thresholdChoice_measurable hg.continuous.measurable
      hp.continuous.measurable hq.continuous.measurable).aemeasurable
      hf.continuous.measurable.aestronglyMeasurable]
    simp_rw [thresholdChoice_decomposition]
    exact integral_add hiq hit
  have ha (n : ℕ) (h : H n) :
      (∑ i, f (thresholdChoice g p q (X n h i)))/(n:ℝ) =
      (∑ i, f (q (X n h i)))/(n:ℝ) +
      (∑ i, (f (p (X n h i))-f (q (X n h i)))*positiveIndicator (g (X n h i)))/(n:ℝ) := by
    simp_rw [thresholdChoice_decomposition]
    rw [Finset.sum_add_distrib, add_div]
  have hc := hh ε hε
  simpa only [ExponentiallyRare, Real.dist_eq, hm, ha] using hc

noncomputable def uniformSeedLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance uniformSeedLaw_probability : IsProbabilityMeasure uniformSeedLaw := by
  constructor
  simp [uniformSeedLaw]

instance uniformSeedLaw_noAtoms : NullSingletonClass uniformSeedLaw := by
  unfold uniformSeedLaw
  infer_instance

lemma uniform_threshold_boundary_null
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (g : E → ℝ) (hg : Measurable g) :
    (ν.prod uniformSeedLaw) {z | g z.1-z.2 = 0} = 0 := by
  have hs : MeasurableSet {z : E × ℝ | g z.1-z.2 = 0} :=
    measurableSet_eq_fun
      (show Measurable (fun z : E × ℝ => g z.1-z.2) from
        (hg.comp measurable_fst).sub measurable_snd) measurable_const
  rw [Measure.prod_apply hs]
  have hz (x : E) : uniformSeedLaw (Prod.mk x ⁻¹' {z | g z.1-z.2 = 0}) = 0 := by
    have he : Prod.mk x ⁻¹' {z | g z.1-z.2 = 0} = {g x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff, sub_eq_zero]
      exact eq_comm
    rw [he, measure_singleton]
  simp_rw [hz]
  simp

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace SKGapCutoff

def DisorderTypical (β : ℝ) (P : (n : ℕ) → GaussianCoordinates n → Prop) : Prop :=
  Tendsto (fun n => disorderLaw β n {g | ¬ P n g}) atTop (𝓝 0)

lemma DisorderTypical.mono {β : ℝ}
    {P Q : (n : ℕ) → GaussianCoordinates n → Prop}
    (hP : DisorderTypical β P) (hPQ : ∀ᶠ n in atTop, ∀ g, P n g → Q n g) :
    DisorderTypical β Q := by
  unfold DisorderTypical at hP ⊢
  apply tendsto_const_nhds.squeeze' hP (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hPQ] with n hn
  exact measure_mono (fun g hg h => hg (hn g h))

lemma DisorderTypical.and {β : ℝ}
    {P Q : (n : ℕ) → GaussianCoordinates n → Prop}
    (hP : DisorderTypical β P) (hQ : DisorderTypical β Q) :
    DisorderTypical β (fun n g => P n g ∧ Q n g) := by
  unfold DisorderTypical at hP hQ ⊢
  have hh : Tendsto (fun n => disorderLaw β n {g | ¬P n g} +
      disorderLaw β n {g | ¬Q n g}) atTop (𝓝 0) := by
    simpa using hP.add hQ
  apply tendsto_const_nhds.squeeze hh (fun _ => zero_le)
  intro n
  apply (measure_mono ?_).trans (measure_union_le _ _)
  intro g hg
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  tauto

lemma disorderLimit_of_typical_bound {β a : ℝ}
    {F : (n : ℕ) → Interaction n → ℝ}
    {P : (n : ℕ) → GaussianCoordinates n → Prop}
    {b : ℕ → ℝ} (hP : DisorderTypical β P) (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ g, P n g → |F n (sampledInteraction g) - a| ≤ b n) :
    DisorderLimit β F a := by
  intro δ hδ
  unfold DisorderTypical at hP
  apply tendsto_const_nhds.squeeze' hP (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hbound, (tendsto_order.mp hb).2 δ hδ] with n hn hbn
  apply measure_mono
  intro g hg hgood
  exact (not_lt_of_ge ((hn g hgood).trans hbn.le)) hg

lemma cutoffTime_nonneg {n : ℕ} (hn : 0 < n) {rate : ℝ} (hrate : 0 < rate) :
    0 ≤ cutoffTime rate n := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by positivity)

lemma spin_mass_cutoff_error {n : ℕ} (hn : 0 < n)
    (J : Interaction n) (hJ : ∀ i j, J i j = J j i) (hd : ∀ i, J i i = 0)
    {rate ε γ V c L : ℝ} (hrate : 0 < rate) (hε : ε < 1)
    (hγ : 0 < γ) (hgap : HasGap J γ) (hV : 1 ≤ γ * V)
    (hc : 0 < c) (hmass : c ≤ spinSpectralMassBelow J hJ hd L)
    (hvar : ∀ x, semigroup J ((1-ε)*cutoffTime rate n) (fun y => overlap x y ^ 2) x -
      (semigroup J ((1-ε)*cutoffTime rate n) (overlap x) x) ^ 2 ≤ (n : ℝ) * V) :
    |worstContinuous J ((1-ε)*cutoffTime rate n) - 1| ≤
      (8*V/c^2) * dimensionDecay (1-(1-ε)*L/rate) n := by
  have ht : 0 ≤ (1-ε)*cutoffTime rate n :=
    mul_nonneg (by linarith) (cutoffTime_nonneg hn hrate)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hat : 0 < (n : ℝ)*c^2*Real.exp (-2*L*((1-ε)*cutoffTime rate n)) := by
    positivity
  have hprod : (n : ℝ)*Real.exp (-2*L*((1-ε)*cutoffTime rate n)) *
      dimensionDecay (1-(1-ε)*L/rate) n = 1 := by
    rw [dimensionDecay, mul_assoc, ← Real.exp_add]
    have he : -2*L*((1-ε)*cutoffTime rate n) +
        -(1-(1-ε)*L/rate)*Real.log (n : ℝ) = -Real.log (n : ℝ) := by
      unfold cutoffTime
      field_simp
      ; ring
    rw [he, Real.exp_neg, Real.exp_log hn', mul_inv_cancel₀ hn'.ne']
  have heq : (n : ℝ)*c^2*Real.exp (-2*L*((1-ε)*cutoffTime rate n)) *
      ((8*V/c^2)*dimensionDecay (1-(1-ε)*L/rate) n) = 8*V := by
    calc
      _ = (8*V)*((n : ℝ)*Real.exp (-2*L*((1-ε)*cutoffTime rate n))*
          dimensionDecay (1-(1-ε)*L/rate) n) := by field_simp
      _ = _ := by rw [hprod, mul_one]
  rw [abs_of_nonpos (sub_nonpos.mpr (worstContinuous_le_one J _ ht))]
  have hs := worstContinuous_lower_from_spectralMass hn J hJ hd ht hγ hgap hV hc hmass hvar
  have hh : 1-worstContinuous J ((1-ε)*cutoffTime rate n) ≤
      (8*V/c^2)*dimensionDecay (1-(1-ε)*L/rate) n := by
    apply (mul_le_mul_iff_right₀ hat).mp
    simpa [mul_comm] using hs.trans_eq heq.symm
  linarith

theorem continuous_lower_from_typical_spin_mass
    {β rate ε γ V c L : ℝ} (hrate : 0 < rate) (hε : ε < 1)
    (hγ : 0 < γ) (hV : 1 ≤ γ * V) (hc : 0 < c)
    (hedge : (1-ε)*L < rate)
    (hgood : DisorderTypical β (fun n g =>
      HasGap (sampledInteraction g) γ ∧
      c ≤ spinSpectralMassBelow (sampledInteraction g)
        (sampledInteraction_symm g) (sampledInteraction_diag g) L ∧
      ∀ x, semigroup (sampledInteraction g) ((1-ε)*cutoffTime rate n)
        (fun y => overlap x y ^ 2) x -
        (semigroup (sampledInteraction g) ((1-ε)*cutoffTime rate n) (overlap x) x)^2 ≤
          (n : ℝ)*V)) :
    DisorderLimit β (fun n J => worstContinuous J ((1-ε)*cutoffTime rate n)) 1 := by
  apply disorderLimit_of_typical_bound hgood
    (show Tendsto (fun n => (8*V/c^2)*dimensionDecay (1-(1-ε)*L/rate) n)
      atTop (𝓝 0) from by
      simpa using (dimensionDecay_tendsto (1-(1-ε)*L/rate) (by
        have := (div_lt_one hrate).mpr hedge
        linarith)).const_mul (8*V/c^2))
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro g ⟨hgap, hmass, hvar⟩
  exact spin_mass_cutoff_error hn (sampledInteraction g)
    (sampledInteraction_symm g) (sampledInteraction_diag g) hrate hε hγ hgap hV hc hmass hvar

end SKGapCutoff

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

end

end OAI
