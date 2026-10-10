import OAI.Analysis.KadisonKastler.AbelianCesaro

namespace OAI

/-! # A scalar invariant mean for every discrete abelian group

Finite iterated Cesaro averages give a positive, unital, contractive
family of scalar functionals. An ultrafilter extending the directed
finite-set/length filter gives a simultaneous scalar limit. The explicit
telescoping bound proves invariance. This constructs the mean used for
the real modular and character groups without an amenability premise.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators BoundedContinuousFunction

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]

theorem cesaroTranslation_positive (n : ℕ) (g : G) (f : G →ᵇ ℂ)
    (hf : ∀ t, (f t).im = 0 ∧ 0 ≤ (f t).re) (t : G) :
    (cesaroTranslation n g f t).im = 0 ∧ 0 ≤ (cesaroTranslation n g f t).re := by
  have hsumim : (∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i) f t).im = 0 := by
    change Complex.imLm (∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i) f t) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i _ => (hf _).1)
  have hsumre : 0 ≤ (∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i) f t).re := by
    change 0 ≤ Complex.reLm (∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i) f t)
    rw [map_sum]
    exact Finset.sum_nonneg (fun i _ => (hf _).2)
  let c : ℂ := (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)
  have hci : c.im = 0 := by
    change (((n + 1 : ℕ) : ℂ)⁻¹).im = 0
    rw [Complex.inv_im]
    simp only [Complex.natCast_im, neg_zero, zero_div]
  have hcr : 0 ≤ c.re := by
    change 0 ≤ (((n + 1 : ℕ) : ℂ)⁻¹).re
    rw [Complex.inv_re, Complex.natCast_re]
    exact div_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  rw [cesaroTranslation_apply]
  simp only [BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.sum_apply,
    smul_eq_mul]
  change (c * _).im = 0 ∧ 0 ≤ (c * _).re
  rw [Complex.mul_im, Complex.mul_re, hci, hsumim]
  simpa only [zero_mul, mul_zero, add_zero, zero_add, sub_zero] using
    (show (0 : ℝ) = 0 ∧ 0 ≤ c.re *
      (∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i) f t).re from
      ⟨rfl, mul_nonneg hcr hsumre⟩)

theorem abelianBoxAverage_positive (n : ℕ) (s : List G) (f : G →ᵇ ℂ)
    (hf : ∀ t, (f t).im = 0 ∧ 0 ≤ (f t).re) :
    ∀ t, (abelianBoxAverage n s f t).im = 0 ∧ 0 ≤ (abelianBoxAverage n s f t).re := by
  induction s with
  | nil => exact hf
  | cons g s ih => exact cesaroTranslation_positive n g _ ih

def abelianBoxFunctional (d : Finset G × ℕ) : (G →ᵇ ℂ) →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ (1 : G)).comp
    (abelianBoxAverage d.2 d.1.toList)

theorem abelianBoxFunctional_apply (d : Finset G × ℕ) (f : G →ᵇ ℂ) :
    abelianBoxFunctional d f = abelianBoxAverage d.2 d.1.toList f 1 := rfl

theorem abelianBoxFunctional_norm_le (d : Finset G × ℕ) (f : G →ᵇ ℂ) :
    ‖abelianBoxFunctional d f‖ ≤ ‖f‖ :=
  ((abelianBoxAverage d.2 d.1.toList f).norm_coe_le_norm 1).trans
    (abelianBoxAverage_norm_le d.2 d.1.toList f)

@[simp] theorem abelianBoxFunctional_const (d : Finset G × ℕ) (c : ℂ) :
    abelianBoxFunctional d (BoundedContinuousFunction.const G c) = c := by
  rw [abelianBoxFunctional_apply, abelianBoxAverage_const]
  rfl

theorem abelianBoxFunctional_positive (d : Finset G × ℕ) (f : G →ᵇ ℂ)
    (hf : ∀ t, (f t).im = 0 ∧ 0 ≤ (f t).re) :
    (abelianBoxFunctional d f).im = 0 ∧ 0 ≤ (abelianBoxFunctional d f).re :=
  abelianBoxAverage_positive d.2 d.1.toList f hf 1

theorem abelianBoxFunctional_translation_bound (d : Finset G × ℕ) (g : G)
    (hg : g ∈ d.1) (f : G →ᵇ ℂ) :
    ‖abelianBoxFunctional d (scalarTranslation g f) - abelianBoxFunctional d f‖ ≤
      2 * (((d.2 + 1 : ℕ) : ℝ)⁻¹) * ‖f‖ := by
  have hmem : g ∈ d.1.toList := by simpa using hg
  have hb := abelianBoxAverage_difference_norm_le d.2 d.1.toList g hmem f
  rw [scalarTranslation_box] at hb
  calc
    _ = ‖(abelianBoxAverage d.2 d.1.toList (scalarTranslation g f) -
        abelianBoxAverage d.2 d.1.toList f) 1‖ := rfl
    _ ≤ ‖abelianBoxAverage d.2 d.1.toList (scalarTranslation g f) -
        abelianBoxAverage d.2 d.1.toList f‖ :=
      (BoundedContinuousFunction.norm_coe_le_norm _ _)
    _ ≤ _ := hb

private def abelianMeanFilter (G : Type*) [CommGroup G] : Ultrafilter (Finset G × ℕ) := by
  classical
  exact Ultrafilter.of atTop

omit [TopologicalSpace G] [DiscreteTopology G] in
private theorem abelianMeanFilter_le :
    ((abelianMeanFilter G) : Filter (Finset G × ℕ)) ≤ atTop := by
  classical
  exact Ultrafilter.of_le atTop

private theorem exists_abelianMeanValue (f : G →ᵇ ℂ) :
    ∃ z : ℂ, ‖z‖ ≤ ‖f‖ ∧
      Tendsto (fun d => abelianBoxFunctional d f) (abelianMeanFilter G : Filter _) (𝓝 z) := by
  obtain ⟨z, hz, ht⟩ := (isCompact_closedBall (0 : ℂ) ‖f‖).ultrafilter_le_nhds
    ((abelianMeanFilter G).map (fun d => abelianBoxFunctional d f)) (by
      apply le_principal_iff.mpr
      change ∀ᶠ d in (abelianMeanFilter G : Filter (Finset G × ℕ)),
        abelianBoxFunctional d f ∈ Metric.closedBall (0 : ℂ) ‖f‖
      exact Eventually.of_forall (fun d => by
        simpa only [Metric.mem_closedBall, dist_zero_right] using abelianBoxFunctional_norm_le d f))
  exact ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, ht⟩

private def abelianMeanValue (f : G →ᵇ ℂ) : ℂ :=
  Classical.choose (exists_abelianMeanValue f)

private theorem norm_abelianMeanValue (f : G →ᵇ ℂ) : ‖abelianMeanValue f‖ ≤ ‖f‖ :=
  (Classical.choose_spec (exists_abelianMeanValue f)).1

private theorem tendsto_abelianMeanValue (f : G →ᵇ ℂ) :
    Tendsto (fun d => abelianBoxFunctional d f) (abelianMeanFilter G : Filter _)
      (𝓝 (abelianMeanValue f)) :=
  (Classical.choose_spec (exists_abelianMeanValue f)).2

private theorem abelianMeanValue_add (f h : G →ᵇ ℂ) :
    abelianMeanValue (f + h) = abelianMeanValue f + abelianMeanValue h := by
  apply tendsto_nhds_unique (tendsto_abelianMeanValue (f + h))
  simpa only [map_add] using (tendsto_abelianMeanValue f).add (tendsto_abelianMeanValue h)

private theorem abelianMeanValue_smul (c : ℂ) (f : G →ᵇ ℂ) :
    abelianMeanValue (c • f) = c • abelianMeanValue f := by
  apply tendsto_nhds_unique (tendsto_abelianMeanValue (c • f))
  simpa only [map_smul] using (tendsto_abelianMeanValue f).const_smul c

private theorem abelianMeanValue_const (c : ℂ) :
    abelianMeanValue (BoundedContinuousFunction.const G c) = c := by
  apply tendsto_nhds_unique (tendsto_abelianMeanValue _)
  simpa only [abelianBoxFunctional_const] using
    (tendsto_const_nhds : Tendsto (fun _ : Finset G × ℕ => c)
      (abelianMeanFilter G : Filter _) (𝓝 c))

private theorem abelianMeanValue_positive (f : G →ᵇ ℂ)
    (hf : ∀ t, (f t).im = 0 ∧ 0 ≤ (f t).re) :
    (abelianMeanValue f).im = 0 ∧ 0 ≤ (abelianMeanValue f).re := by
  constructor
  · apply tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp (tendsto_abelianMeanValue f))
    have h : (fun d : Finset G × ℕ => (abelianBoxFunctional d f).im) = fun _ => 0 :=
      funext (fun d => (abelianBoxFunctional_positive d f hf).1)
    change Tendsto (fun d => (abelianBoxFunctional d f).im)
      (abelianMeanFilter G : Filter (Finset G × ℕ)) (𝓝 0)
    rw [h]
    exact tendsto_const_nhds
  · exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp (tendsto_abelianMeanValue f))
      (Eventually.of_forall (fun d => (abelianBoxFunctional_positive d f hf).2))

private theorem abelianBoxFunctional_translation_tendsto_zero (g : G) (f : G →ᵇ ℂ) :
    Tendsto (fun d => abelianBoxFunctional d (scalarTranslation g f) - abelianBoxFunctional d f)
      (atTop : Filter (Finset G × ℕ)) (𝓝 0) := by
  classical
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsnd : Tendsto (fun d : Finset G × ℕ => d.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hrate : Tendsto (fun d : Finset G × ℕ =>
      2 * (((d.2 + 1 : ℕ) : ℝ)⁻¹) * ‖f‖) atTop (𝓝 0) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd).const_mul 2).mul_const ‖f‖
    simpa only [Function.comp_def, one_div, Nat.cast_add, Nat.cast_one, mul_zero, zero_mul] using h
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hrate
  filter_upwards [eventually_ge_atTop (({g} : Finset G), 0)] with d hd
  exact abelianBoxFunctional_translation_bound d g (hd.1 (Finset.mem_singleton_self g)) f

private theorem abelianMeanValue_invariant (g : G) (f : G →ᵇ ℂ) :
    abelianMeanValue (scalarMeanTranslate g f) = abelianMeanValue f := by
  have hz := (abelianBoxFunctional_translation_tendsto_zero g f).mono_left
    (abelianMeanFilter_le (G := G))
  have hd := (tendsto_abelianMeanValue (scalarTranslation g f)).sub (tendsto_abelianMeanValue f)
  have he := tendsto_nhds_unique hd hz
  exact sub_eq_zero.mp he

/-- An actual invariant scalar mean on every discrete abelian group. -/
def abelianScalarInvariantMean (G : Type*) [CommGroup G]
    [TopologicalSpace G] [DiscreteTopology G] : ScalarInvariantMean G where
  toCLM := LinearMap.mkContinuous
    { toFun := abelianMeanValue
      map_add' := abelianMeanValue_add
      map_smul' := abelianMeanValue_smul }
    1 (fun f => by
      change ‖abelianMeanValue f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_abelianMeanValue f)
  map_const_one := abelianMeanValue_const 1
  norm_le := norm_abelianMeanValue
  positive := abelianMeanValue_positive
  invariant := abelianMeanValue_invariant

end

end KadisonKastler

end OAI
