import OAI.Analysis.Brenier.AffineTies

namespace OAI

noncomputable section

open Filter
open scoped Topology NNReal

namespace Problem358.FiniteMaxDerivative

variable {ι X : Type*} [Fintype ι] [Nonempty ι]

/-- The maximum of a nonempty finite family of real-valued functions. -/
def maxValue (f : ι → X → ℝ) (x : X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)

theorem le_maxValue (f : ι → X → ℝ) (i : ι) (x : X) :
    f i x ≤ maxValue f x :=
  Finset.le_sup' (fun j => f j x) (Finset.mem_univ i)

theorem maxValue_le {f : ι → X → ℝ} {x : X} {a : ℝ}
    (h : ∀ i, f i x ≤ a) : maxValue f x ≤ a :=
  Finset.sup'_le _ _ (fun i _ => h i)

/-- A strict active branch remains the maximum in a neighborhood. -/
theorem eventuallyEq_of_strict_max [TopologicalSpace X]
    {f : ι → X → ℝ} {x : X} {i : ι}
    (hc : ∀ j, ContinuousAt (f j) x)
    (hi : ∀ j, j ≠ i → f j x < f i x) :
    maxValue f =ᶠ[𝓝 x] f i := by
  have hnear : ∀ j, ∀ᶠ y in 𝓝 x, f j y ≤ f i y := by
    intro j
    by_cases hji : j = i
    · subst j
      exact Filter.Eventually.of_forall fun _ => le_rfl
    · exact ((hc j).eventually_lt (hc i) (hi j hji)).mono fun _ h => h.le
  filter_upwards [Filter.eventually_all.mpr hnear] with y hy
  exact le_antisymm (maxValue_le hy) (le_maxValue f i y)

/-- Differentiation of a finite maximum at a strict active branch. -/
theorem hasDerivAt_of_strict_max {f : ι → ℝ → ℝ} {x f' : ℝ} {i : ι}
    (hc : ∀ j, ContinuousAt (f j) x)
    (hi : ∀ j, j ≠ i → f j x < f i x)
    (hd : HasDerivAt (f i) f' x) : HasDerivAt (maxValue f) f' x := by
  exact hd.congr_of_eventuallyEq (eventuallyEq_of_strict_max hc hi)

/-- The corresponding Fréchet derivative statement in any real normed space. -/
theorem hasFDerivAt_of_strict_max {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : ι → V → ℝ} {x : V} {f' : V →L[ℝ] ℝ} {i : ι}
    (hc : ∀ j, ContinuousAt (f j) x)
    (hi : ∀ j, j ≠ i → f j x < f i x)
    (hd : HasFDerivAt (f i) f' x) : HasFDerivAt (maxValue f) f' x := by
  exact hd.congr_of_eventuallyEq (eventuallyEq_of_strict_max hc hi)

/-- Taking a finite maximum preserves a common Lipschitz constant. -/
theorem lipschitzWith_maxValue [PseudoMetricSpace X]
    {f : ι → X → ℝ} {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i)) :
    LipschitzWith K (maxValue f) := by
  apply LipschitzWith.of_le_add_mul K
  intro x y
  apply maxValue_le
  intro i
  exact (hf i |>.le_add_mul x y).trans
    (add_le_add (le_maxValue f i y) le_rfl)

/-- The same bound holds on any common time domain. -/
theorem lipschitzOnWith_maxValue [PseudoMetricSpace X]
    {f : ι → X → ℝ} {K : ℝ≥0} {s : Set X}
    (hf : ∀ i, LipschitzOnWith K (f i) s) :
    LipschitzOnWith K (maxValue f) s := by
  apply LipschitzOnWith.of_le_add_mul K
  intro x hx y hy
  apply maxValue_le
  intro i
  exact (hf i |>.le_add_mul hx hy).trans
    (add_le_add (le_maxValue f i y) le_rfl)

section Fubini

open MeasureTheory

/-- A finite injective family of real scores has a strict maximizing index. -/
theorem exists_strict_max_of_injective (z : ι → ℝ) (hz : Function.Injective z) :
    ∃ i, ∀ j, j ≠ i → z j < z i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty z
  refine ⟨i, fun j hji => ?_⟩
  apply lt_of_le_of_ne
  · rw [← hi]
    exact Finset.le_sup' z (Finset.mem_univ j)
  · exact fun heq => hji (hz heq)

/-- Fubini moves the a.e. no-tie property from source sections to time sections. -/
theorem ae_ae_exists_strict_max {T Z : Type*} [MeasurableSpace T] [MeasurableSpace Z]
    {τ : Measure T} {ρ : Measure Z} [SFinite τ] [SFinite ρ]
    (f : ι → T × Z → ℝ) (hf : ∀ i, Measurable (f i))
    (hunique : ∀ᵐ t ∂τ, ∀ᵐ x ∂ρ, Function.Injective (fun i => f i (t, x))) :
    ∀ᵐ x ∂ρ, ∀ᵐ t ∂τ, ∃ i, ∀ j, j ≠ i → f j (t, x) < f i (t, x) := by
  have hm : MeasurableSet {p : T × Z | ∃ i, ∀ j, j ≠ i → f j p < f i p} := by
    simp only [Set.ofPred_exists, Set.ofPred_forall]
    apply MeasurableSet.iUnion
    intro i
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt (hf j) (hf i)
  apply (Measure.ae_ae_comm hm).mp
  filter_upwards [hunique] with t ht
  filter_upwards [ht] with x hx
  exact exists_strict_max_of_injective _ hx

end Fubini

section TimeIntegral

open MeasureTheory Set

/-- Finite maxima of uniformly Lipschitz time branches obey the fundamental theorem. -/
theorem integral_deriv_maxValue {f : ι → ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}
    (hf : ∀ i, LipschitzOnWith K (f i) (uIcc a b)) :
    ∫ t in a..b, deriv (maxValue f) t = maxValue f b - maxValue f a :=
  (lipschitzOnWith_maxValue hf).absolutelyContinuousOnInterval.integral_deriv_eq_sub

/-- Replace the derivative in the finite-max FTC by any a.e. derivative formula. -/
theorem integral_eq_sub_of_ae_hasDerivAt {f : ι → ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}
    {v : ℝ → ℝ} (hf : ∀ i, LipschitzOnWith K (f i) (uIcc a b))
    (hv : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt (maxValue f) (v t) t) :
    ∫ t in a..b, v t = maxValue f b - maxValue f a := by
  rw [← integral_deriv_maxValue hf]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hv] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).deriv.symm

/-- An a.e. derivative formula for the finite maximum is interval integrable. -/
theorem intervalIntegrable_of_ae_hasDerivAt {f : ι → ℝ → ℝ} {K : ℝ≥0}
    {a b : ℝ} {v : ℝ → ℝ}
    (hf : ∀ i, LipschitzOnWith K (f i) (uIcc a b))
    (hv : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt (maxValue f) (v t) t) :
    IntervalIntegrable v volume a b := by
  apply (lipschitzOnWith_maxValue hf).absolutelyContinuousOnInterval.intervalIntegrable_deriv.congr_ae
  filter_upwards [ae_restrict_of_ae hv, ae_restrict_mem measurableSet_uIoc] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).deriv

/-- The FTC identity with the derivative of an a.e. strict active branch. -/
theorem integral_active_deriv_eq_sub {f f' : ι → ℝ → ℝ} {K : ℝ≥0}
    {a b : ℝ} (active : ℝ → ι)
    (hf : ∀ i, LipschitzOnWith K (f i) (uIcc a b))
    (hd : ∀ᵐ t, t ∈ uIcc a b → ∀ j, HasDerivAt (f j) (f' j t) t)
    (hstrict : ∀ᵐ t, t ∈ uIcc a b → ∀ j, j ≠ active t →
      f j t < f (active t) t) :
    ∫ t in a..b, f' (active t) t = maxValue f b - maxValue f a := by
  apply integral_eq_sub_of_ae_hasDerivAt hf
  filter_upwards [hd, hstrict] with t hdt hst ht
  exact hasDerivAt_of_strict_max (fun j => (hdt ht j).continuousAt)
    (hst ht) (hdt ht (active t))

end TimeIntegral

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The time derivative of a finite affine potential on a strict active cell. -/
theorem hasDerivAt_affine_max {y : ι → ℝ → V} {c : ι → ℝ → ℝ}
    {v : ι → V} {r : ι → ℝ} {t : ℝ} {i : ι} (x : V)
    (hy : ∀ j, HasDerivAt (y j) (v j) t)
    (hc : ∀ j, HasDerivAt (c j) (r j) t)
    (hi : ∀ j, j ≠ i → inner ℝ x (y j t) + c j t <
      inner ℝ x (y i t) + c i t) :
    HasDerivAt (maxValue (fun j s => inner ℝ x (y j s) + c j s))
      (inner ℝ x (v i) + r i) t := by
  have hd : ∀ j, HasDerivAt (fun s => inner ℝ x (y j s) + c j s)
      (inner ℝ x (v j) + r j) t := by
    intro j
    convert ((hasDerivAt_const t x).inner ℝ (hy j)).add (hc j) using 1
    simp only [inner_zero_left, add_zero]
  exact hasDerivAt_of_strict_max (fun j => (hd j).continuousAt) hi (hd i)

/-- Uniform bounds on site and intercept speeds make the potential Lipschitz in time. -/
theorem lipschitzOnWith_affine_max_of_deriv_bounds
    {y : ι → ℝ → V} {c : ι → ℝ → ℝ} {v : ι → ℝ → V} {r : ι → ℝ → ℝ}
    {s : Set ℝ} (hs : Convex ℝ s) (x : V) {R A B : ℝ≥0}
    (hx : ‖x‖ ≤ R)
    (hy : ∀ j t, t ∈ s → HasDerivAt (y j) (v j t) t)
    (hc : ∀ j t, t ∈ s → HasDerivAt (c j) (r j t) t)
    (hv : ∀ j t, t ∈ s → ‖v j t‖ ≤ A)
    (hr : ∀ j t, t ∈ s → ‖r j t‖ ≤ B) :
    LipschitzOnWith (R * A + B)
      (maxValue (fun j t => inner ℝ x (y j t) + c j t)) s := by
  apply lipschitzOnWith_maxValue
  intro j
  have hd : ∀ t ∈ s, HasDerivAt (fun t => inner ℝ x (y j t) + c j t)
      (inner ℝ x (v j t) + r j t) t := by
    intro t ht
    convert ((hasDerivAt_const t x).inner ℝ (hy j t ht)).add (hc j t ht) using 1
    simp only [inner_zero_left, add_zero]
  apply hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (hd t ht).hasDerivWithinAt)
  intro t ht
  change ‖inner ℝ x (v j t) + r j t‖ ≤ (↑(R * A + B) : ℝ)
  calc
    ‖inner ℝ x (v j t) + r j t‖ ≤ ‖inner ℝ x (v j t)‖ + ‖r j t‖ := norm_add_le _ _
    _ ≤ ‖x‖ * ‖v j t‖ + ‖r j t‖ := add_le_add (norm_inner_le_norm _ _) le_rfl
    _ ≤ (R : ℝ) * A + B := by gcongr; exact hv j t ht; exact hr j t ht
    _ = ↑(R * A + B) := by simp

end Problem358.FiniteMaxDerivative

end

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators NNReal

namespace Problem358
namespace FiniteMaxDerivative

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The maximum of a nonempty finite family of real numbers. -/
def finiteMax (f : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

lemma le_finiteMax (f : ι → ℝ) (i : ι) : f i ≤ finiteMax f :=
  Finset.le_sup' f (Finset.mem_univ i)

lemma finiteMax_le {f : ι → ℝ} {r : ℝ} (h : ∀ i, f i ≤ r) : finiteMax f ≤ r :=
  Finset.sup'_le Finset.univ_nonempty f (fun i _ => h i)

lemma finiteMax_eq {f : ι → ℝ} {i : ι} (h : ∀ j, f j ≤ f i) : finiteMax f = f i :=
  le_antisymm (finiteMax_le h) (le_finiteMax f i)

/-- A strict maximizer remains the maximizer for a sufficiently small affine perturbation. -/
lemma eventually_finiteMax_eq (f q : ι → ℝ) (i : ι)
    (hi : ∀ j, j ≠ i → f j < f i) :
    (fun t : ℝ => finiteMax (fun j => f j + t * q j)) =ᶠ[𝓝 0]
      (fun t => f i + t * q i) := by
  have h : ∀ᶠ t : ℝ in 𝓝 0, ∀ j, f j + t * q j ≤ f i + t * q i := by
    rw [Filter.eventually_all]
    intro j
    by_cases hji : j = i
    · subst j
      exact Filter.Eventually.of_forall (fun _ => le_rfl)
    · have hj : ContinuousAt (fun t : ℝ => f j + t * q j) 0 := by fun_prop
      have hi' : ContinuousAt (fun t : ℝ => f i + t * q i) 0 := by fun_prop
      exact (hj.eventually_lt hi' (by simpa using hi j hji)).mono (fun _ ht => ht.le)
  exact h.mono (fun _ ht => finiteMax_eq ht)

/-- Directional derivative of a finite maximum at a strict maximizer. -/
lemma hasDerivAt_finiteMax (f q : ι → ℝ) (i : ι)
    (hi : ∀ j, j ≠ i → f j < f i) :
    HasDerivAt (fun t : ℝ => finiteMax (fun j => f j + t * q j)) (q i) 0 := by
  have h : HasDerivAt (fun t : ℝ => f i + t * q i) (q i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (q i)).const_add (f i)
  exact h.congr_of_eventuallyEq (eventually_finiteMax_eq f q i hi)

/-- The maximum is uniformly Lipschitz in an affine parameter, independently of offsets. -/
lemma lipschitzWith_finiteMax (f q : ι → ℝ) (B : ℝ≥0)
    (hq : ∀ i, |q i| ≤ B) :
    LipschitzWith B (fun t : ℝ => finiteMax (fun i => f i + t * q i)) := by
  apply LipschitzWith.of_le_add_mul B
  intro t s
  apply finiteMax_le
  intro i
  calc
    f i + t * q i = (f i + s * q i) + (t - s) * q i := by ring
    _ ≤ finiteMax (fun j => f j + s * q j) + |(t - s) * q i| :=
      add_le_add (le_finiteMax (fun j => f j + s * q j) i) (le_abs_self _)
    _ ≤ finiteMax (fun j => f j + s * q j) + B * dist t s := by
      rw [abs_mul, Real.dist_eq]
      exact add_le_add le_rfl (by
        calc
          |t - s| * |q i| ≤ |t - s| * (B : ℝ) :=
            mul_le_mul_of_nonneg_left (hq i) (abs_nonneg _)
          _ = (B : ℝ) * |t - s| := mul_comm _ _)

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma aestronglyMeasurable_finiteMax (f : ι → α → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x => finiteMax (fun i => f i x)) μ := by
  have h : AEStronglyMeasurable (Finset.univ.sup' Finset.univ_nonempty f) μ := by
    exact Finset.sup'_induction Finset.univ_nonempty f
      (p := fun g : α → ℝ => AEStronglyMeasurable g μ)
      (fun g hg h hh => hg.sup hh) (fun i _ => hf i)
  convert h using 1
  funext x
  exact (Finset.sup'_apply Finset.univ_nonempty f x).symm

/-- Every finite-valued measurable selection is integrable for a finite measure. -/
lemma integrable_finite_selection {ι : Type*} [Fintype ι] [Nonempty ι]
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (q : ι → ℝ) (k : α → ι)
    (hk : ∀ i, MeasurableSet {x | k x = i}) :
    Integrable (fun x => q (k x)) μ := by
  classical
  have h : Integrable
      (fun x => ∑ i, {x | k x = i}.indicator (fun _ => q i) x) μ :=
    integrable_finsetSum _ (fun i _ => (integrable_const (q i)).indicator (hk i))
  convert h using 1
  funext x
  simp [Set.indicator_apply]

/-- Integrate a finite-valued selection by summing its fiber masses. -/
lemma integral_finite_selection {ι : Type*} [Fintype ι] [Nonempty ι]
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (q : ι → ℝ) (k : α → ι)
    (hk : ∀ i, MeasurableSet {x | k x = i}) :
    (∫ x, q (k x) ∂μ) = ∑ i, μ.real {x | k x = i} * q i := by
  classical
  calc
    (∫ x, q (k x) ∂μ) =
        ∫ x, ∑ i, {x | k x = i}.indicator (fun _ => q i) x ∂μ := by
      congr 1
      funext x
      simp [Set.indicator_apply]
    _ = ∑ i, ∫ x, {x | k x = i}.indicator (fun _ => q i) x ∂μ := by
      exact integral_finsetSum _ (fun i _ => (integrable_const (q i)).indicator (hk i))
    _ = ∑ i, μ.real {x | k x = i} * q i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_indicator (hk i)]
      simp

/-- The masses of a finite measurable partition sum to one under a probability measure. -/
lemma sum_cellMass_eq_one [IsProbabilityMeasure μ] (k : α → ι)
    (hk : ∀ i, MeasurableSet {x | k x = i}) :
    (∑ i, μ.real {x | k x = i}) = 1 := by
  simpa using (integral_finite_selection (μ := μ) (fun _ : ι => (1 : ℝ)) k hk).symm

/-- Differentiate an integral of finite maxima when its active index is unique almost everywhere.
The Lipschitz bound is independent of the point and hence integrable for every finite measure. -/
theorem hasDerivAt_integral_finiteMax [IsFiniteMeasure μ]
    (f : ι → α → ℝ) (q : ι → ℝ) (k : α → ι)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hint : Integrable (fun x => finiteMax (fun i => f i x)) μ)
    (hk : ∀ᵐ x ∂μ, ∀ j, j ≠ k x → f j x < f (k x) x)
    (hqk : AEStronglyMeasurable (fun x => q (k x)) μ) :
    HasDerivAt (fun t : ℝ => ∫ x, finiteMax (fun i => f i x + t * q i) ∂μ)
      (∫ x, q (k x) ∂μ) 0 := by
  let B : ℝ≥0 := ∑ i, ‖q i‖₊
  have hq : ∀ i, |q i| ≤ (B : ℝ) := by
    intro i
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      (show (0 : ℝ≥0) ≤ ‖q j‖₊ from zero_le)) (Finset.mem_univ i)
    exact_mod_cast h
  have hmeas : ∀ t : ℝ,
      AEStronglyMeasurable (fun x => finiteMax (fun i => f i x + t * q i)) μ := by
    intro t
    exact aestronglyMeasurable_finiteMax _ (fun i => (hf i).add_const _)
  have hbase : Integrable (fun x => finiteMax (fun i => f i x + (0 : ℝ) * q i)) μ := by
    simpa using hint
  have hlip : ∀ᵐ x ∂μ,
      LipschitzOnWith (Real.nnabs (B : ℝ))
        (fun t : ℝ => finiteMax (fun i => f i x + t * q i)) Set.univ := by
    apply Filter.Eventually.of_forall
    intro x
    simpa using (lipschitzWith_finiteMax (fun i => f i x) q B hq)
  exact (hasDerivAt_integral_of_dominated_loc_of_lip
    (s := Set.univ) (bound := fun _ : α => (B : ℝ))
    (Filter.univ_mem) (Filter.Eventually.of_forall hmeas) hbase hqk hlip
    (integrable_const _) (hk.mono (fun x hx => hasDerivAt_finiteMax _ q (k x) hx))).2

/-- Cell-mass form of the derivative formula, with only measurable fibers required of the index. -/
theorem hasDerivAt_integral_finiteMax_cellMass [IsFiniteMeasure μ]
    (f : ι → α → ℝ) (q : ι → ℝ) (k : α → ι)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hint : Integrable (fun x => finiteMax (fun i => f i x)) μ)
    (hk : ∀ᵐ x ∂μ, ∀ j, j ≠ k x → f j x < f (k x) x)
    (hkmeas : ∀ i, MeasurableSet {x | k x = i}) :
    HasDerivAt (fun t : ℝ => ∫ x, finiteMax (fun i => f i x + t * q i) ∂μ)
      (∑ i, μ.real {x | k x = i} * q i) 0 := by
  rw [← integral_finite_selection q k hkmeas]
  exact hasDerivAt_integral_finiteMax f q k hf hint hk
    (integrable_finite_selection q k hkmeas).aestronglyMeasurable

/-- Directional derivative of the finite-cell intercept objective. -/
theorem hasDerivAt_intercept_objective [IsFiniteMeasure μ]
    (f : ι → α → ℝ) (c q m : ι → ℝ) (k : α → ι)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hint : Integrable (fun x => finiteMax (fun i => f i x + c i)) μ)
    (hk : ∀ᵐ x ∂μ, ∀ j, j ≠ k x → f j x + c j < f (k x) x + c (k x))
    (hkmeas : ∀ i, MeasurableSet {x | k x = i}) :
    HasDerivAt
      (fun t : ℝ => (∫ x, finiteMax (fun i => f i x + (c i + t * q i)) ∂μ) -
        ∑ i, m i * (c i + t * q i))
      (∑ i, (μ.real {x | k x = i} - m i) * q i) 0 := by
  have hmax := hasDerivAt_integral_finiteMax_cellMass
    (fun i x => f i x + c i) q k (fun i => (hf i).add_const (c i)) hint hk hkmeas
  have hlin : HasDerivAt (fun t : ℝ => ∑ i, m i * (c i + t * q i))
      (∑ i, m i * q i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (q i)).const_add (c i)).const_mul (m i)
  convert! hmax.sub hlin using 1 <;> simp [add_assoc, sub_mul, Finset.sum_sub_distrib]
  funext t
  rfl

end FiniteMaxDerivative
end Problem358

end

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Problem358

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Injective moving affine slopes have jointly almost-everywhere distinct scores.
The joint conclusion is what is needed to integrate derivatives along time paths. -/
theorem ae_prod_injective_affine_scores (K : Set (E d))
    {τ : Measure ℝ} [SFinite (uniformMeasure K)]
    {y : ι → ℝ → E d} {c : ι → ℝ → ℝ}
    (hy : ∀ i, Measurable (y i)) (hc : ∀ i, Measurable (c i))
    (hinj : ∀ᵐ t ∂τ, Function.Injective (fun i => y i t)) :
    ∀ᵐ p ∂τ.prod (uniformMeasure K),
      Function.Injective (fun i => ⟪p.2, y i p.1⟫_ℝ + c i p.1) := by
  have hscore (i : ι) :
      Measurable (fun p : ℝ × E d => ⟪p.2, y i p.1⟫_ℝ + c i p.1) :=
    (measurable_snd.inner (hy i |>.comp measurable_fst)).add
      (hc i |>.comp measurable_fst)
  have hm : MeasurableSet {p : ℝ × E d |
      Function.Injective (fun i => ⟪p.2, y i p.1⟫_ℝ + c i p.1)} := by
    change MeasurableSet {p : ℝ × E d | ∀ i j,
      ⟪p.2, y i p.1⟫_ℝ + c i p.1 = ⟪p.2, y j p.1⟫_ℝ + c j p.1 → i = j}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i = j
    · simp [hij]
    · simpa only [hij, imp_false, Set.compl_ofPred] using
        (measurableSet_eq_fun (hscore i) (hscore j)).compl
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [hinj] with t ht
  filter_upwards [uniform_ae_affine_tie_implies_slopes_eq K
    (fun i => y i t) (fun i => c i t)] with x hx
  intro i j hij
  exact ht (hx i j hij)

/-- Any maximizing selector of moving affine scores is strictly active jointly a.e.
when the moving slopes are a.e. injective. -/
theorem ae_prod_strict_active_affine (K : Set (E d))
    {τ : Measure ℝ} [SFinite (uniformMeasure K)]
    {y : ι → ℝ → E d} {c : ι → ℝ → ℝ}
    (active : ℝ → E d → ι)
    (hy : ∀ i, Measurable (y i)) (hc : ∀ i, Measurable (c i))
    (hinj : ∀ᵐ t ∂τ, Function.Injective (fun i => y i t))
    (hactive : ∀ᵐ p ∂τ.prod (uniformMeasure K), ∀ j,
      ⟪p.2, y j p.1⟫_ℝ + c j p.1 ≤
        ⟪p.2, y (active p.1 p.2) p.1⟫_ℝ + c (active p.1 p.2) p.1) :
    ∀ᵐ p ∂τ.prod (uniformMeasure K), ∀ j, j ≠ active p.1 p.2 →
      ⟪p.2, y j p.1⟫_ℝ + c j p.1 <
        ⟪p.2, y (active p.1 p.2) p.1⟫_ℝ + c (active p.1 p.2) p.1 := by
  filter_upwards [ae_prod_injective_affine_scores K hy hc hinj, hactive] with p hp ha
  intro j hj
  exact lt_of_le_of_ne (ha j) (fun heq => hj (hp heq))

/-- The time derivative of a moving finite affine maximum agrees jointly a.e.
with the affine velocity on any maximizing selector.  Thus no separate no-ties
or strict-cell hypothesis is needed for the fundamental-theorem step. -/
theorem ae_prod_hasDerivAt_affine_max [Nonempty ι] (K : Set (E d))
    {τ : Measure ℝ} [SFinite (uniformMeasure K)]
    {y v : ι → ℝ → E d} {c r : ι → ℝ → ℝ}
    (active : ℝ → E d → ι)
    (hy : ∀ i, Measurable (y i)) (hc : ∀ i, Measurable (c i))
    (hinj : ∀ᵐ t ∂τ, Function.Injective (fun i => y i t))
    (hdy : ∀ᵐ t ∂τ, ∀ j, HasDerivAt (y j) (v j t) t)
    (hdc : ∀ᵐ t ∂τ, ∀ j, HasDerivAt (c j) (r j t) t)
    (hactive : ∀ᵐ p ∂τ.prod (uniformMeasure K), ∀ j,
      ⟪p.2, y j p.1⟫_ℝ + c j p.1 ≤
        ⟪p.2, y (active p.1 p.2) p.1⟫_ℝ + c (active p.1 p.2) p.1) :
    ∀ᵐ p ∂τ.prod (uniformMeasure K),
      HasDerivAt
        (FiniteMaxDerivative.maxValue (fun j t => ⟪p.2, y j t⟫_ℝ + c j t))
        (⟪p.2, v (active p.1 p.2) p.1⟫_ℝ + r (active p.1 p.2) p.1) p.1 := by
  have hdy' : ∀ᵐ p ∂τ.prod (uniformMeasure K),
      ∀ j, HasDerivAt (y j) (v j p.1) p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hdy
  have hdc' : ∀ᵐ p ∂τ.prod (uniformMeasure K),
      ∀ j, HasDerivAt (c j) (r j p.1) p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hdc
  filter_upwards [hdy', hdc', ae_prod_strict_active_affine K active hy hc hinj hactive]
    with p hp hq hs
  exact FiniteMaxDerivative.hasDerivAt_affine_max p.2 hp hq hs

end Problem358

end

end OAI
