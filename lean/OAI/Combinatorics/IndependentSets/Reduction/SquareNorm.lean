import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.ArbitraryRealJunta

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical
noncomputable def squareNorm {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) : ℝ :=
  Real.sqrt (∫ x, (f x)^2 ∂μ)
lemma squareNorm_eq_L2 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ} (hf : MemLp f 2 μ) : squareNorm μ f = ‖hf.toLp f‖ := by
  have hn : ‖hf.toLp f‖^2 = ∫ x, (f x)^2 ∂μ := by
    calc
      _ = inner ℝ (hf.toLp f) (hf.toLp f) := (real_inner_self_eq_norm_sq _).symm
      _ = ∫ x, ((hf.toLp f) x)^2 ∂μ := by
        rw [L2.inner_def]
        simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq, Real.norm_eq_abs, sq_abs]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp] with x hx
        rw [hx]
  rw [squareNorm, ← hn, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
lemma squareNorm_sub_norm_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f g : X → ℝ} {B C : ℝ} (hf : Measurable f) (hg : Measurable g)
    (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C) :
    |squareNorm μ f-squareNorm μ g| ≤ squareNorm μ (f-g) := by
  have hfl : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  have hgl : MemLp g 2 μ := MemLp.of_bound hg.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hc x))
  rw [squareNorm_eq_L2 μ hfl, squareNorm_eq_L2 μ hgl, squareNorm_eq_L2 μ (hfl.sub hgl), MemLp.toLp_sub]
  exact abs_norm_sub_norm_le _ _
lemma squareNorm_le_bound {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} {B : ℝ} (hf : Measurable f) (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    squareNorm μ f ≤ B := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hB,?_⟩
  have hi := bounded_sq_integrable (μ := μ) hf hb
  calc
    _ ≤ ∫ _ : X, B^2 ∂μ := integral_mono hi (integrable_const _) (fun x => by
      have h := hb x
      nlinarith [sq_abs (f x), abs_nonneg (f x)])
    _ = _ := by simp

noncomputable def influenceNorm {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (i : ι) (f : (ι → α) → ℝ) : ℝ := Real.sqrt (influenceSq μ i f)
lemma influenceNorm_difference {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f g : (ι → α) → ℝ} {B C : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C) :
    |influenceNorm μ i f-influenceNorm μ i g| ≤ squareNorm (Measure.pi (fun _ : ι => μ)) (f-g) := by
  have hfm := coordinateMean_measurable μ i hf
  have hgm := coordinateMean_measurable μ i hg
  have hfb (x : ι → α) : |f x-coordinateMean μ i f x| ≤ B+B :=
    (abs_sub _ _).trans (add_le_add (hb x) (coordinateMean_bound μ i hb x))
  have hgb (x : ι → α) : |g x-coordinateMean μ i g x| ≤ C+C :=
    (abs_sub _ _).trans (add_le_add (hc x) (coordinateMean_bound μ i hc x))
  have h := squareNorm_sub_norm_le (Measure.pi (fun _ : ι => μ)) (hf.sub hfm) (hg.sub hgm) hfb hgb
  change |influenceNorm μ i f-influenceNorm μ i g| ≤ _ at h
  have hlin : (f-coordinateMean μ i f)-(g-coordinateMean μ i g) =
      (f-g)-coordinateMean μ i (f-g) := by
    funext x
    rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, coordinateMean_sub μ i hf hg hb hc]
    simp only [Pi.sub_apply]
    ring
  rw [hlin] at h
  exact h.trans (Real.sqrt_le_sqrt (influenceSq_le μ i (hf.sub hg)
    (fun x => (abs_sub _ _).trans (add_le_add (hb x) (hc x)))))
lemma influenceNorm_difference_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f g : (ι → α) → ℝ} {B C a : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C)
    (ha : 0 ≤ a) (hdiff : ∀ x, |f x-g x| ≤ a) :
    |influenceNorm μ i f-influenceNorm μ i g| ≤ a :=
  (influenceNorm_difference μ i hf hg hb hc).trans
    (squareNorm_le_bound _ (hf.sub hg) ha hdiff)
end LargeIndependentSets.ProductAveraging

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set
open scoped BigOperators Classical NNReal
lemma quotient_dist_le (x y : ℝ) : dist (x : Circle) (y : Circle) ≤ |x-y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ i, Fintype (M i)]
variable {κ τ : Type*} [Fintype κ]

omit [DecidableEq ι] [∀ index, Fintype (M index)] [Fintype κ] in
lemma phase_measurable (p : ∀ j, κ → M j) (t : ι → ℝ) : Measurable (phase p t) := by
  apply Measurable.of_eval
  intro k
  exact Finset.measurable_sum _ (fun l _ => quotient_preserving.measurable.comp
    (measurable_const.mul (measurable_pi_apply (⟨l,p l k⟩ : Sigma M))))

omit [DecidableEq ι] [∀ index, Fintype (M index)] in
lemma phase_dist_le (p : ∀ j, κ → M j) (t : ι → ℝ) (ht : ∀ j, |t j| ≤ 1)
    (θ φ : Sigma M → ℝ) {e : ℝ} (he : 0 ≤ e) (hθ : ∀ c, |θ c-φ c| ≤ e) :
    dist (phase p t θ) (phase p t φ) ≤ (Fintype.card ι : ℝ)*e := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro k
  calc
    _ ≤ ∑ j, dist (((t j*θ ⟨j,p j k⟩ : ℝ) : Circle)) (((t j*φ ⟨j,p j k⟩ : ℝ) : Circle)) :=
      dist_sum_sum_le _ _ _
    _ ≤ ∑ _j : ι, e := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ |t j*θ ⟨j,p j k⟩-t j*φ ⟨j,p j k⟩| := quotient_dist_le _ _
        _ = |t j| * |θ ⟨j,p j k⟩-φ ⟨j,p j k⟩| := by rw [← mul_sub, abs_mul]
        _ ≤ 1*e := mul_le_mul (ht j) (hθ _) (abs_nonneg _) (by norm_num)
        _ = e := one_mul _
    _ = _ := by simp

omit [DecidableEq ι] in
lemma phase_lipschitz (p : ∀ j, κ → M j) (t : ι → ℝ) (ht : ∀ j, |t j| ≤ 1) :
    LipschitzWith (Fintype.card ι : ℝ≥0) (phase p t) := by
  apply LipschitzWith.of_dist_le_mul
  intro θ φ
  exact phase_dist_le p t ht θ φ dist_nonneg (fun c => by simpa only [Real.dist_eq] using dist_le_pi_dist θ φ c)

omit [∀ index, Fintype (M index)] in
lemma phase_change_coefficient (p : ∀ j, κ → M j) (t t' : ι → ℝ) (j : ι)
    (hc : ∀ l, l ≠ j → t l = t' l) (θ : Sigma M → ℝ) (hθ : ∀ c, |θ c| ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) (hd : |t j-t' j| ≤ u) :
    dist (phase p t θ) (phase p t' θ) ≤ u := by
  apply (dist_pi_le_iff hu).mpr
  intro k
  calc
    _ ≤ ∑ l, dist (((t l*θ ⟨l,p l k⟩ : ℝ) : Circle)) (((t' l*θ ⟨l,p l k⟩ : ℝ) : Circle)) :=
      dist_sum_sum_le _ _ _
    _ ≤ ∑ l, if l=j then u else 0 := by
      apply Finset.sum_le_sum
      intro l _
      by_cases hl : l = j
      · subst l
        rw [ite_eq_left rfl]
        calc
          _ ≤ |t j*θ ⟨j,p j k⟩-t' j*θ ⟨j,p j k⟩| := quotient_dist_le _ _
          _ = |t j-t' j| * |θ ⟨j,p j k⟩| := by rw [← sub_mul, abs_mul]
          _ ≤ u*1 := mul_le_mul hd (hθ _) (abs_nonneg _) hu
          _ = u := mul_one _
      · simp only [hc l hl, hl, ↓reduceIte, dist_self, le_refl]
    _ = _ := by simp

omit [∀ index, Fintype (M index)] in
lemma auxiliary_change_coefficient (p : ∀ j, κ → M j) (r : κ → τ) (a : τ → ι)
    (t t' : ι → ℝ) (j : ι) (hc : ∀ l, l ≠ j → t l = t' l)
    (θ : Sigma M → ℝ) (hθ : ∀ c, |θ c| ≤ 1) (z : ι → Circle)
    {u : ℝ} (hu : 0 ≤ u) (hd : |t j-t' j| ≤ u) :
    dist (auxiliary p r a t θ z) (auxiliary p r a t' θ z) ≤ u := by
  apply (dist_pi_le_iff hu).mpr
  intro k
  simpa only [auxiliary, dist_add_left] using
    (dist_le_pi_dist (phase p t θ) (phase p t' θ) k).trans
      (phase_change_coefficient p t t' j hc θ hθ hu hd)

omit [∀ index, Fintype (M index)] in
lemma auxiliary_influence_step (p : ∀ j, κ → M j) (r : κ → τ) (a : τ → ι)
    (t t' : ι → ℝ) (j : ι) (hc : ∀ l, l ≠ j → t l = t' l)
    (θ : Sigma M → ℝ) (hθ : ∀ c, |θ c| ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) (hd : |t j-t' j| ≤ u)
    {L : ℝ≥0} (F : (κ → Circle) → ℝ) (hF : LipschitzWith L F) (hb : ∀ x, |F x| ≤ 1) :
    |ProductAveraging.influenceNorm volume j (fun z => F (auxiliary p r a t θ z)) -
      ProductAveraging.influenceNorm volume j (fun z => F (auxiliary p r a t' θ z))| ≤ L*u := by
  apply ProductAveraging.influenceNorm_difference_le volume j
    ((hF.comp (auxiliary_lipschitz p r a t θ)).continuous.measurable)
    ((hF.comp (auxiliary_lipschitz p r a t' θ)).continuous.measurable)
    (fun z => hb _) (fun z => hb _) (by positivity)
  intro z
  calc
    _ = dist (F (auxiliary p r a t θ z)) (F (auxiliary p r a t' θ z)) := (Real.dist_eq _ _).symm
    _ ≤ L*dist (auxiliary p r a t θ z) (auxiliary p r a t' θ z) := hF.dist_le_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (auxiliary_change_coefficient p r a t t' j hc θ hθ z hu hd) (by positivity)

lemma squared_value_distance {X : Type*} [PseudoMetricSpace X] {L : ℝ≥0}
    {F : X → ℝ} (hF : LipschitzWith L F) (hb : ∀ x, |F x| ≤ 1) (x y : X) :
    |(F x)^2-(F y)^2| ≤ 2*L*dist x y := by
  calc
    _ = |F x-F y| * |F x+F y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ (L*dist x y)*2 := mul_le_mul (by simpa only [Real.dist_eq] using hF.dist_le_mul x y)
      ((abs_add_le _ _).trans (by linarith [hb x,hb y])) (abs_nonneg _) (by positivity)
    _ = _ := by ring

omit [DecidableEq ι] [∀ index, Fintype (M index)] in
lemma grid_square_error (p : ∀ j, κ → M j) (t : ι → ℝ) (ht : ∀ j, |t j| ≤ 1)
    (θ φ : Sigma M → ℝ) {e : ℝ} (he : 0 ≤ e) (hθ : ∀ c, |θ c-φ c| ≤ e)
    {L : ℝ≥0} {F : (κ → Circle) → ℝ} (hF : LipschitzWith L F) (hb : ∀ x, |F x| ≤ 1) :
    |(F (phase p t θ))^2-(F (phase p t φ))^2| ≤ 2*L*Fintype.card ι*e := by
  calc
    _ ≤ 2*L*dist (phase p t θ) (phase p t φ) := squared_value_distance hF hb _ _
    _ ≤ 2*L*((Fintype.card ι : ℝ)*e) := mul_le_mul_of_nonneg_left (phase_dist_le p t ht θ φ he hθ) (by positivity)
    _ = _ := by ring
end LargeIndependentSets.PhaseTest

end OAI
