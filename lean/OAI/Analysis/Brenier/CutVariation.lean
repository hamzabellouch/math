import OAI.Analysis.Brenier.HalfspaceKernel

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem358

/-- Transport the moving-halfspace derivative through a measure-preserving
coordinate chart. The affine geometry enters only through the exact threshold
identity, while the derivative and all integration steps are proved here. -/
theorem hasDerivAt_integral_cut_difference_of_chart
    {X V : Type*} [MeasurableSpace X] [MeasurableSpace V]
    {μ : Measure X} [SFinite μ] {ρ : Measure V}
    {chart : X × ℝ → V} (hchart : MeasurePreserving chart (μ.prod volume) ρ)
    {f ell : ℝ → V → ℝ} {speed : ℝ → X → ℝ} {A B slope trace : X → ℝ}
    {s : Set ℝ} (hs : s ∈ nhds 0)
    (hf : ∀ h, Measurable (f h)) (hell : ∀ h, Measurable (ell h))
    (hspeed : ∀ h, Measurable (speed h))
    (hlevel : ∀ h ∈ s, ∀ p : X × ℝ,
      0 ≤ ell h (chart p) ↔ -(h * speed h p.1) ≤ p.2)
    (hspeedlim : ∀ᵐ x ∂μ, Tendsto (fun h => speed h x) (nhds 0) (nhds (slope x)))
    (hlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => f h (chart (x, -(h * speed h x * u))))
        (nhds 0) (nhds (trace x)))
    (hspeedbound : ∀ᵐ x ∂μ, ∀ h ∈ s, |speed h x| ≤ A x)
    (hbound : ∀ᵐ x ∂μ, ∀ h ∈ s, ∀ t : ℝ, ‖f h (chart (x, t))‖ ≤ B x)
    (hdom : Integrable (fun x => A x * B x) μ)
    (hInt : ∀ᶠ h in nhds 0, Integrable (f h) ρ) :
    HasDerivAt (fun h : ℝ => ∫ v,
      f h v * ((if 0 ≤ ell h v then (1 : ℝ) else 0) -
        (if 0 ≤ ell 0 v then (1 : ℝ) else 0)) ∂ρ)
      (∫ x, slope x * trace x ∂μ) 0 := by
  let F : ℝ → X → ℝ → ℝ := fun h => Function.curry (f h ∘ chart)
  have hF : ∀ h, Measurable (Function.uncurry (F h)) := by
    intro h
    simpa only [F, Function.uncurry_curry] using (hf h).comp hchart.measurable
  have hFI : ∀ᶠ h in nhds 0, Integrable (Function.uncurry (F h)) (μ.prod volume) := by
    filter_upwards [hInt] with h hh
    simpa only [F, Function.uncurry_curry] using hchart.integrable_comp_of_integrable hh
  have hd := hasDerivAt_prod_integral_halfspace_difference_local
    (f := F) hs hF hspeed hspeedlim hlim hspeedbound hbound hdom hFI
  apply hd.congr_of_eventuallyEq
  filter_upwards [hs] with h hh
  have hraw : Measurable (fun v => f h v *
      ((if 0 ≤ ell h v then (1 : ℝ) else 0) -
        (if 0 ≤ ell 0 v then (1 : ℝ) else 0))) :=
    (hf h).mul ((Measurable.ite (measurableSet_le measurable_const (hell h))
      measurable_const measurable_const).sub
      (Measurable.ite (measurableSet_le measurable_const (hell 0))
        measurable_const measurable_const))
  rw [← hchart.map_eq, integral_map hchart.measurable.aemeasurable hraw.aestronglyMeasurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    have hz := hlevel 0 (mem_of_mem_nhds hs) p
    simp only [zero_mul, neg_zero] at hz
    simp only [F, Function.curry, Function.comp_apply, hlevel h hh p, hz]

end Problem358

end

noncomputable section

open MeasureTheory Finset
open scoped BigOperators

namespace Problem358
namespace FiniteIntersectionVariation

/-- Exact finite telescoping formula, changing the factors one at a time. -/
theorem prod_range_sub_prod_range {R : Type*} [CommRing R]
    (a b : ℕ → R) (n : ℕ) :
    (∏ i ∈ Finset.range n, a i) - (∏ i ∈ Finset.range n, b i) =
      ∑ i ∈ Finset.range n,
        (a i - b i) * (∏ j ∈ Finset.range i, a j) *
          ∏ j ∈ Finset.Ico (i + 1) n, b j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hsum :
          (∑ i ∈ Finset.range n,
            (a i - b i) * (∏ j ∈ Finset.range i, a j) *
              ∏ j ∈ Finset.Ico (i + 1) (n + 1), b j) =
          (∑ i ∈ Finset.range n,
            (a i - b i) * (∏ j ∈ Finset.range i, a j) *
              ∏ j ∈ Finset.Ico (i + 1) n, b j) * b n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.prod_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.mp hi))]
        ring
      rw [hsum, ← ih]
      simp only [Finset.Ico_self, Finset.prod_empty, mul_one, Finset.prod_range_succ]
      ring

/-- The indicator of a finite intersection factors into the individual indicators. -/
theorem indicator_finite_intersection {X : Type*} (A : ℕ → Set X) (n : ℕ) (x : X) :
    ({x | ∀ i < n, x ∈ A i}.indicator (fun _ => (1 : ℝ))) x =
      ∏ i ∈ Finset.range n, (A i).indicator (fun _ => (1 : ℝ)) x := by
  classical
  by_cases hx : ∀ i < n, x ∈ A i
  · rw [Set.indicator_of_mem (s := {x | ∀ i < n, x ∈ A i}) hx]
    symm
    apply Finset.prod_eq_one
    intro i hi
    exact Set.indicator_of_mem (hx i (Finset.mem_range.mp hi)) _
  · rw [Set.indicator_of_notMem (s := {x | ∀ i < n, x ∈ A i}) hx]
    push Not at hx
    obtain ⟨i, hi, hix⟩ := hx
    symm
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
    exact Set.indicator_of_notMem hix _

/-- Each term changes one cut; all other cuts appear only as bounded indicator factors. -/
theorem indicator_intersection_sub {X : Type*} (A B : ℕ → Set X) (n : ℕ) (x : X) :
    ({x | ∀ i < n, x ∈ A i}.indicator (fun _ => (1 : ℝ))) x -
      ({x | ∀ i < n, x ∈ B i}.indicator (fun _ => (1 : ℝ))) x =
    ∑ i ∈ Finset.range n,
      ((A i).indicator (fun _ => (1 : ℝ)) x - (B i).indicator (fun _ => (1 : ℝ)) x) *
        (∏ j ∈ Finset.range i, (A j).indicator (fun _ => (1 : ℝ)) x) *
        ∏ j ∈ Finset.Ico (i + 1) n, (B j).indicator (fun _ => (1 : ℝ)) x := by
  rw [indicator_finite_intersection, indicator_finite_intersection]
  exact prod_range_sub_prod_range _ _ n

/-- Signed contribution from changing one cut in the finite intersection. -/
def cutTerm {X : Type*} (A B : ℕ → Set X) (n i : ℕ) (x : X) : ℝ :=
  ((A i).indicator (fun _ => (1 : ℝ)) x - (B i).indicator (fun _ => (1 : ℝ)) x) *
    (∏ j ∈ Finset.range i, (A j).indicator (fun _ => (1 : ℝ)) x) *
    ∏ j ∈ Finset.Ico (i + 1) n, (B j).indicator (fun _ => (1 : ℝ)) x

lemma norm_indicator_one_le {X : Type*} (S : Set X) (x : X) :
    ‖S.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ S <;> simp [hx]

lemma norm_cutTerm_le {X : Type*} (A B : ℕ → Set X) (n i : ℕ) (x : X) :
    ‖cutTerm A B n i x‖ ≤ 1 := by
  classical
  have hd : ‖(A i).indicator (fun _ => (1 : ℝ)) x -
      (B i).indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    by_cases ha : x ∈ A i <;> by_cases hb : x ∈ B i <;>
      simp [ha, hb]
  have hp (C : ℕ → Set X) (s : Finset ℕ) :
      ‖∏ j ∈ s, (C j).indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => norm_indicator_one_le (C j) x)
  unfold cutTerm
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (1 : ℝ) * 1 * 1 := by
      gcongr
      · exact hp A _
      · exact hp B _
    _ = 1 := by norm_num

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma measurable_cutTerm (A B : ℕ → Set X) (n i : ℕ)
    (hA : ∀ j, MeasurableSet (A j)) (hB : ∀ j, MeasurableSet (B j)) :
    Measurable (cutTerm A B n i) := by
  have hAm (j : ℕ) : Measurable ((A j).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator (hA j)
  have hBm (j : ℕ) : Measurable ((B j).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator (hB j)
  exact ((hAm i).sub (hBm i)).mul
    (Finset.measurable_prod _ (fun j _ => hAm j)) |>.mul
    (Finset.measurable_prod _ (fun j _ => hBm j))

lemma integrable_cutTerm_mul (A B : ℕ → Set X) (n i : ℕ)
    (hA : ∀ j, MeasurableSet (A j)) (hB : ∀ j, MeasurableSet (B j))
    {w : X → ℝ} (hw : Integrable w μ) :
    Integrable (fun x => cutTerm A B n i x * w x) μ := by
  exact hw.bdd_mul (measurable_cutTerm A B n i hA hB).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => norm_cutTerm_le A B n i x)

/-- Weighted integral form of finite-intersection telescoping. -/
theorem integral_indicator_intersection_sub (A B : ℕ → Set X) (n : ℕ)
    (hA : ∀ j, MeasurableSet (A j)) (hB : ∀ j, MeasurableSet (B j))
    {w : X → ℝ} (hw : Integrable w μ) :
    (∫ x, (({x | ∀ i < n, x ∈ A i}.indicator (fun _ => (1 : ℝ))) x -
        ({x | ∀ i < n, x ∈ B i}.indicator (fun _ => (1 : ℝ))) x) * w x ∂μ) =
      ∑ i ∈ Finset.range n, ∫ x, cutTerm A B n i x * w x ∂μ := by
  have heq (x : X) :
      (({x | ∀ i < n, x ∈ A i}.indicator (fun _ => (1 : ℝ))) x -
        ({x | ∀ i < n, x ∈ B i}.indicator (fun _ => (1 : ℝ))) x) * w x =
      ∑ i ∈ Finset.range n, cutTerm A B n i x * w x := by
    rw [indicator_intersection_sub, Finset.sum_mul]
    rfl
  simp_rw [heq]
  exact integral_finsetSum _ (fun i _ => integrable_cutTerm_mul A B n i hA hB hw)

lemma measurableSet_finiteIntersection (A : ℕ → Set X) (n : ℕ)
    (hA : ∀ i, MeasurableSet (A i)) :
    MeasurableSet {x | ∀ i < n, x ∈ A i} := by
  have heq : {x | ∀ i < n, x ∈ A i} = ⋂ i, ⋂ (_ : i < n), A i := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun (_ : i < n) => hA i

/-- Difference of weighted intersection integrals is the sum of independent cut variations. -/
theorem integral_intersection_sub_integral_intersection (A B : ℕ → Set X) (n : ℕ)
    (hA : ∀ j, MeasurableSet (A j)) (hB : ∀ j, MeasurableSet (B j))
    {w : X → ℝ} (hw : Integrable w μ) :
    (∫ x in {x | ∀ i < n, x ∈ A i}, w x ∂μ) -
      (∫ x in {x | ∀ i < n, x ∈ B i}, w x ∂μ) =
      ∑ i ∈ Finset.range n, ∫ x, cutTerm A B n i x * w x ∂μ := by
  have hMA := measurableSet_finiteIntersection A n hA
  have hMB := measurableSet_finiteIntersection B n hB
  rw [← integral_indicator hMA, ← integral_indicator hMB,
    ← integral_sub (hw.indicator hMA) (hw.indicator hMB)]
  calc
    _ = ∫ x, (({x | ∀ i < n, x ∈ A i}.indicator (fun _ => (1 : ℝ))) x -
        ({x | ∀ i < n, x ∈ B i}.indicator (fun _ => (1 : ℝ))) x) * w x ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hax : x ∈ {x | ∀ i < n, x ∈ A i} <;>
        by_cases hbx : x ∈ {x | ∀ i < n, x ∈ B i} <;>
          simp [Set.indicator, hax, hbx]
    _ = _ := integral_indicator_intersection_sub A B n hA hB hw

/-- Reassemble derivatives of signed single-cut contributions into the derivative of a cell integral. -/
theorem hasDerivAt_intersection_integral (A : ℝ → ℕ → Set X) (n : ℕ)
    (hA : ∀ t i, MeasurableSet (A t i)) {w : X → ℝ} (hw : Integrable w μ)
    (d : ℕ → ℝ)
    (hd : ∀ i < n, HasDerivAt
      (fun t : ℝ => ∫ x, cutTerm (A t) (A 0) n i x * w x ∂μ) (d i) 0) :
    HasDerivAt (fun t : ℝ => ∫ x in {x | ∀ i < n, x ∈ A t i}, w x ∂μ)
      (∑ i ∈ Finset.range n, d i) 0 := by
  have hs : HasDerivAt
      (fun t : ℝ => ∑ i ∈ Finset.range n, ∫ x, cutTerm (A t) (A 0) n i x * w x ∂μ)
      (∑ i ∈ Finset.range n, d i) 0 :=
    HasDerivAt.fun_sum (fun i hi => hd i (Finset.mem_range.mp hi))
  have hs' := hs.const_add (∫ x in {x | ∀ i < n, x ∈ A 0 i}, w x ∂μ)
  apply hs'.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro t
  have heq := integral_intersection_sub_integral_intersection
    (A t) (A 0) n (hA t) (hA 0) hw
  dsimp
  linarith

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma integrable_cutTerm_smul (A B : ℕ → Set X) (n i : ℕ)
    (hA : ∀ j, MeasurableSet (A j)) (hB : ∀ j, MeasurableSet (B j))
    {w : X → V} (hw : Integrable w μ) :
    Integrable (fun x => cutTerm A B n i x • w x) μ := by
  exact hw.bdd_smul 1 (measurable_cutTerm A B n i hA hB).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => norm_cutTerm_le A B n i x)

/-- Vector-valued version, in particular applicable to unnormalized cell moments. -/
theorem integral_intersection_sub_integral_intersection_vector
    (A B : ℕ → Set X) (n : ℕ)
    (hA : ∀ j, MeasurableSet (A j)) (hB : ∀ j, MeasurableSet (B j))
    {w : X → V} (hw : Integrable w μ) :
    (∫ x in {x | ∀ i < n, x ∈ A i}, w x ∂μ) -
      (∫ x in {x | ∀ i < n, x ∈ B i}, w x ∂μ) =
      ∑ i ∈ Finset.range n, ∫ x, cutTerm A B n i x • w x ∂μ := by
  have hMA := measurableSet_finiteIntersection A n hA
  have hMB := measurableSet_finiteIntersection B n hB
  rw [← integral_indicator hMA, ← integral_indicator hMB,
    ← integral_sub (hw.indicator hMA) (hw.indicator hMB)]
  calc
    _ = ∫ x, ∑ i ∈ Finset.range n, cutTerm A B n i x • w x ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      have heq : {x | ∀ i < n, x ∈ A i}.indicator w x -
          {x | ∀ i < n, x ∈ B i}.indicator w x =
          (({x | ∀ i < n, x ∈ A i}.indicator (fun _ => (1 : ℝ))) x -
            ({x | ∀ i < n, x ∈ B i}.indicator (fun _ => (1 : ℝ))) x) • w x := by
        by_cases hax : x ∈ {x | ∀ i < n, x ∈ A i} <;>
          by_cases hbx : x ∈ {x | ∀ i < n, x ∈ B i} <;>
            simp [Set.indicator, hax, hbx]
      dsimp only
      rw [heq, indicator_intersection_sub, Finset.sum_smul]
      rfl
    _ = _ := integral_finsetSum _ (fun i _ => integrable_cutTerm_smul A B n i hA hB hw)

/-- Reassemble single-cut derivatives for vector-valued integrals, including cell moments. -/
theorem hasDerivAt_intersection_integral_vector (A : ℝ → ℕ → Set X) (n : ℕ)
    (hA : ∀ t i, MeasurableSet (A t i)) {w : X → V} (hw : Integrable w μ)
    (d : ℕ → V)
    (hd : ∀ i < n, HasDerivAt
      (fun t : ℝ => ∫ x, cutTerm (A t) (A 0) n i x • w x ∂μ) (d i) 0) :
    HasDerivAt (fun t : ℝ => ∫ x in {x | ∀ i < n, x ∈ A t i}, w x ∂μ)
      (∑ i ∈ Finset.range n, d i) 0 := by
  have hs : HasDerivAt
      (fun t : ℝ => ∑ i ∈ Finset.range n, ∫ x, cutTerm (A t) (A 0) n i x • w x ∂μ)
      (∑ i ∈ Finset.range n, d i) 0 :=
    HasDerivAt.fun_sum (fun i hi => hd i (Finset.mem_range.mp hi))
  have hs' := hs.const_add (∫ x in {x | ∀ i < n, x ∈ A 0 i}, w x ∂μ)
  apply hs'.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro t
  have heq := integral_intersection_sub_integral_intersection_vector
    (A t) (A 0) n (hA t) (hA 0) hw
  dsimp
  exact (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)

end FiniteIntersectionVariation
end Problem358

end

noncomputable section

open MeasureTheory Set
open scoped BigOperators NNReal

namespace Problem358

/-- Changing membership in a finite intersection requires changing membership
in at least one cut. This weighted pointwise form also applies to signed moments. -/
theorem norm_indicator_iInter_sub_le_sum
    {ι X F : Type*} [Fintype ι] [NormedAddCommGroup F]
    (A B : ι → Set X) (f : X → F) (x : X) :
    ‖(⋂ i, A i).indicator f x - (⋂ i, B i).indicator f x‖ ≤
      ∑ i, ‖(A i).indicator f x - (B i).indicator f x‖ := by
  classical
  by_cases hA : ∀ i, x ∈ A i
  · by_cases hB : ∀ i, x ∈ B i
    · simp only [indicator_of_mem (mem_iInter.mpr hA),
        indicator_of_mem (mem_iInter.mpr hB), sub_self, norm_zero]
      exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
    · obtain ⟨i, hi⟩ := not_forall.mp hB
      have hB' : x ∉ ⋂ j, B j := by simpa only [mem_iInter] using hB
      rw [indicator_of_mem (mem_iInter.mpr hA), indicator_of_notMem hB', sub_zero]
      have hsum := Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
          norm_nonneg ((A j).indicator f x - (B j).indicator f x)) (Finset.mem_univ i)
      simpa only [indicator_of_mem (hA i), indicator_of_notMem hi, sub_zero] using hsum
  · have hA' : x ∉ ⋂ j, A j := by simpa only [mem_iInter] using hA
    by_cases hB : ∀ i, x ∈ B i
    · obtain ⟨i, hi⟩ := not_forall.mp hA
      rw [indicator_of_notMem hA', indicator_of_mem (mem_iInter.mpr hB),
        zero_sub, norm_neg]
      have hsum := Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
          norm_nonneg ((A j).indicator f x - (B j).indicator f x)) (Finset.mem_univ i)
      simpa only [indicator_of_notMem hi, indicator_of_mem (hB i),
        zero_sub, norm_neg] using hsum
    · have hB' : x ∉ ⋂ j, B j := by simpa only [mem_iInter] using hB
      simp only [indicator_of_notMem hA', indicator_of_notMem hB', sub_self, norm_zero]
      exact Finset.sum_nonneg (fun i _ => norm_nonneg _)

/-- The total variation of a finite-cut weighted integral is bounded by the
sum of the individual weighted cut variations. -/
theorem norm_integral_iInter_sub_le_sum
    {ι X : Type*} [Fintype ι] [MeasurableSpace X] {μ : Measure X}
    {A B : ι → Set X} {f : X → ℝ}
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hf : Integrable f μ) :
    ‖(∫ x in ⋂ i, A i, f x ∂μ) - (∫ x in ⋂ i, B i, f x ∂μ)‖ ≤
      ∑ i, ∫ x, ‖(A i).indicator f x - (B i).indicator f x‖ ∂μ := by
  classical
  have hiA := MeasurableSet.iInter hA
  have hiB := MeasurableSet.iInter hB
  rw [← integral_indicator hiA, ← integral_indicator hiB,
    ← integral_sub (hf.indicator hiA) (hf.indicator hiB)]
  have hint (i : ι) : Integrable (fun x =>
      ‖(A i).indicator f x - (B i).indicator f x‖) μ :=
    ((hf.indicator (hA i)).sub (hf.indicator (hB i))).norm
  calc
    ‖∫ x, (⋂ i, A i).indicator f x - (⋂ i, B i).indicator f x ∂μ‖ ≤
        ∫ x, ∑ i, ‖(A i).indicator f x - (B i).indicator f x‖ ∂μ := by
      apply norm_integral_le_of_norm_le
        (integrable_finsetSum Finset.univ (fun i _ => hint i))
      exact Filter.Eventually.of_forall (norm_indicator_iInter_sub_le_sum A B f)
    _ = ∑ i, ∫ x, ‖(A i).indicator f x - (B i).indicator f x‖ ∂μ := by
      exact integral_finsetSum _ (fun i _ => hint i)

/-- Finite intersections preserve quantitative Lipschitz control when each cut
is controlled in weighted `L¹`. No differentiation or nonnegative density premise
is assumed, so both cell mass and cell moments fit this interface. -/
theorem lipschitzOnWith_integral_iInter_of_cutL1
    {ι X A : Type*} [Fintype ι] [MeasurableSpace X] [PseudoMetricSpace A]
    {μ : Measure X} {S : Set A} {cuts : A → ι → Set X} {f : X → ℝ}
    (C : ι → ℝ≥0) (hf : Integrable f μ)
    (hcuts : ∀ a ∈ S, ∀ i, MeasurableSet (cuts a i))
    (hcut : ∀ a ∈ S, ∀ b ∈ S, ∀ i,
      (∫ x, ‖(cuts a i).indicator f x - (cuts b i).indicator f x‖ ∂μ) ≤
        C i * dist a b) :
    LipschitzOnWith (∑ i, C i)
      (fun a => ∫ x in ⋂ i, cuts a i, f x ∂μ) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  rw [dist_eq_norm]
  calc
    ‖(∫ x in ⋂ i, cuts a i, f x ∂μ) - (∫ x in ⋂ i, cuts b i, f x ∂μ)‖ ≤
        ∑ i, ∫ x, ‖(cuts a i).indicator f x - (cuts b i).indicator f x‖ ∂μ :=
      norm_integral_iInter_sub_le_sum (hcuts a ha) (hcuts b hb) hf
    _ ≤ ∑ i, (C i : ℝ) * dist a b := Finset.sum_le_sum (fun i _ => hcut a ha b hb i)
    _ = (∑ i, C i : ℝ≥0) * dist a b := by simp only [NNReal.coe_sum, Finset.sum_mul]

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem358
namespace FiniteCellVariation

/-- The unchanged factors in the one-cut-at-a-time expansion of a cell. -/
def remainingIndicator {V : Type*} (ell : ℝ → ℕ → V → ℝ)
    (n i : ℕ) (h : ℝ) (v : V) : ℝ :=
  (∏ j ∈ Finset.range i, if 0 ≤ ell h j v then (1 : ℝ) else 0) *
    ∏ j ∈ Finset.Ico (i + 1) n, if 0 ≤ ell 0 j v then (1 : ℝ) else 0

lemma norm_remainingIndicator_le {V : Type*} (ell : ℝ → ℕ → V → ℝ)
    (n i : ℕ) (h : ℝ) (v : V) : ‖remainingIndicator ell n i h v‖ ≤ 1 := by
  have hp (t : ℝ) (s : Finset ℕ) :
      ‖∏ j ∈ s, if 0 ≤ ell t j v then (1 : ℝ) else 0‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    intro j _
    split_ifs <;> norm_num
  unfold remainingIndicator
  rw [norm_mul]
  calc
    _ ≤ (1 : ℝ) * 1 := by gcongr <;> exact hp _ _
    _ = 1 := mul_one _

lemma measurable_remainingIndicator {V : Type*} [MeasurableSpace V]
    (ell : ℝ → ℕ → V → ℝ) (hell : ∀ h i, Measurable (ell h i))
    (n i : ℕ) (h : ℝ) : Measurable (remainingIndicator ell n i h) := by
  have hm (t : ℝ) (j : ℕ) :
      Measurable (fun v => if 0 ≤ ell t j v then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const (hell t j))
      measurable_const measurable_const
  exact (Finset.measurable_prod _ (fun j _ => hm h j)).mul
    (Finset.measurable_prod _ (fun j _ => hm 0 j))

lemma integrable_remainingIndicator_mul {V : Type*} [MeasurableSpace V]
    {ρ : Measure V} (ell : ℝ → ℕ → V → ℝ)
    (hell : ∀ h i, Measurable (ell h i)) (n i : ℕ) (h : ℝ)
    {w : V → ℝ} (hw : Integrable w ρ) :
    Integrable (fun v => remainingIndicator ell n i h v * w v) ρ := by
  exact hw.bdd_mul (measurable_remainingIndicator ell hell n i h).aestronglyMeasurable
    (Eventually.of_forall fun v => norm_remainingIndicator_le ell n i h v)

/-- Scalar weighted cell differentiation assembled from measure-preserving face
charts. All ambient integrability and finite-intersection algebra are discharged
here; the remaining hypotheses are exclusively the local geometry, trace, and
domination data of the individual faces. The chart spaces may depend on the face. -/
theorem hasDerivAt_cell_integral_of_face_charts
    {V : Type*} [MeasurableSpace V] {ρ : Measure V}
    {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    {μ : ∀ i, Measure (X i)} [∀ i, SFinite (μ i)]
    (ell : ℝ → ℕ → V → ℝ) (n : ℕ)
    (hell : ∀ h i, Measurable (ell h i))
    {w : V → ℝ} (hwM : Measurable w) (hw : Integrable w ρ)
    (chart : ∀ i, X i × ℝ → V)
    (hchart : ∀ i < n, MeasurePreserving (chart i) ((μ i).prod volume) ρ)
    (speed : ∀ i, ℝ → X i → ℝ)
    (A B slope trace : ∀ i, X i → ℝ) (s : ℕ → Set ℝ)
    (hs : ∀ i < n, s i ∈ nhds 0)
    (hspeed : ∀ i < n, ∀ h, Measurable (speed i h))
    (hlevel : ∀ i < n, ∀ h ∈ s i, ∀ p : X i × ℝ,
      0 ≤ ell h i (chart i p) ↔ -(h * speed i h p.1) ≤ p.2)
    (hspeedlim : ∀ i < n, ∀ᵐ x ∂μ i,
      Tendsto (fun h => speed i h x) (nhds 0) (nhds (slope i x)))
    (hlim : ∀ i < n, ∀ᵐ x ∂μ i, ∀ u : ℝ,
      Tendsto (fun h : ℝ =>
        remainingIndicator ell n i h (chart i (x, -(h * speed i h x * u))) *
          w (chart i (x, -(h * speed i h x * u))))
        (nhds 0) (nhds (trace i x)))
    (hspeedbound : ∀ i < n, ∀ᵐ x ∂μ i, ∀ h ∈ s i, |speed i h x| ≤ A i x)
    (hbound : ∀ i < n, ∀ᵐ x ∂μ i, ∀ h ∈ s i, ∀ t : ℝ,
      ‖remainingIndicator ell n i h (chart i (x, t)) * w (chart i (x, t))‖ ≤ B i x)
    (hdom : ∀ i < n, Integrable (fun x => A i x * B i x) (μ i)) :
    HasDerivAt
      (fun h : ℝ => ∫ v in {v | ∀ i < n, 0 ≤ ell h i v}, w v ∂ρ)
      (∑ i ∈ Finset.range n, ∫ x, slope i x * trace i x ∂μ i) 0 := by
  let cuts : ℝ → ℕ → Set V := fun h i => {v | 0 ≤ ell h i v}
  have hcuts : ∀ h i, MeasurableSet (cuts h i) :=
    fun h i => measurableSet_le measurable_const (hell h i)
  apply FiniteIntersectionVariation.hasDerivAt_intersection_integral cuts n hcuts hw
    (fun i => ∫ x, slope i x * trace i x ∂μ i)
  intro i hi
  have hd := hasDerivAt_integral_cut_difference_of_chart (hchart i hi) (hs i hi)
    (fun h => (measurable_remainingIndicator ell hell n i h).mul hwM)
    (fun h => hell h i) (hspeed i hi) (hlevel i hi) (hspeedlim i hi)
    (hlim i hi) (hspeedbound i hi) (hbound i hi) (hdom i hi)
    (Eventually.of_forall fun h => integrable_remainingIndicator_mul ell hell n i h hw)
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro h
  apply integral_congr_ae
  apply Eventually.of_forall
  intro v
  simp only [Pi.mul_apply, FiniteIntersectionVariation.cutTerm, remainingIndicator, cuts,
    Set.indicator_apply, Set.mem_ofPred_eq]
  ring

end FiniteCellVariation
end Problem358

end

end OAI
