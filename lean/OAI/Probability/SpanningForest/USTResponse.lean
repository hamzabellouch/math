import OAI.Probability.SpanningForest.Definitions
import OAI.Probability.SpanningForest.GibbsResponse

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.USTResponse

abbrev TreeSample (K : FiniteSubgraphCode) :=
  {T : Finset (ℕ × ℕ) // T ∈ spanningTrees K}

abbrev FiniteEdge (K : FiniteSubgraphCode) :=
  {e : ℕ × ℕ // e ∈ K.2}

def indicator (K : FiniteSubgraphCode) (T : TreeSample K) (e : FiniteEdge K) : ℝ :=
  if e.1 ∈ T.1 then 1 else 0

lemma tree_property (K : FiniteSubgraphCode) (T : TreeSample K) : TreeOn K T.1 := by
  classical
  exact (Finset.mem_filter.mp T.2).2

lemma indicator_binary (K : FiniteSubgraphCode) (T : TreeSample K) (e : FiniteEdge K) :
    indicator K T e = 0 ∨ indicator K T e = 1 := by
  unfold indicator
  split_ifs <;> simp

lemma sum_indicator (K : FiniteSubgraphCode) (T : TreeSample K) :
    (∑ e : FiniteEdge K, indicator K T e) = (K.1.card : ℝ) - 1 := by
  have hsub : T.1 ⊆ K.2 := (tree_property K T).1
  have hcard : T.1.card + 1 = K.1.card := (tree_property K T).2.1
  have heq : (∑ e : FiniteEdge K, indicator K T e) = (T.1.card : ℝ) := by
    unfold indicator
    rw [← Finset.sum_subtype K.2 (fun _ => Iff.rfl)
      (fun e => if e ∈ T.1 then (1 : ℝ) else 0)]
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
  rw [heq]
  have hc : (T.1.card : ℝ) + 1 = (K.1.card : ℝ) := by exact_mod_cast hcard
  linarith

def weight (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ) (T : TreeSample K) : ℝ :=
  Real.exp (∑ e, h e * indicator K T e)

def partition (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ) : ℝ :=
  ∑ T : TreeSample K, weight K h T

def mass (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ) (T : TreeSample K) : ℝ :=
  weight K h T / partition K h

lemma weight_pos (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ) (T : TreeSample K) :
    0 < weight K h T := Real.exp_pos _

lemma partition_pos (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ)
    (hne : (spanningTrees K).Nonempty) : 0 < partition K h := by
  obtain ⟨T, hT⟩ := hne
  exact Finset.sum_pos (fun _ _ => weight_pos K h _) ⟨⟨T, hT⟩, Finset.mem_univ _⟩

lemma mass_nonneg (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ)
    (hne : (spanningTrees K).Nonempty) (T : TreeSample K) : 0 ≤ mass K h T := by
  exact div_nonneg (weight_pos K h T).le (partition_pos K h hne).le

lemma sum_mass (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ)
    (hne : (spanningTrees K).Nonempty) : (∑ T : TreeSample K, mass K h T) = 1 := by
  simp only [mass, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos K h hne))

def inclusion (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ) (e : FiniteEdge K) : ℝ :=
  FiniteResponse.mean (mass K h) (indicator K) e

def edgeCovariance (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ)
    (e f : FiniteEdge K) : ℝ :=
  FiniteResponse.covariance (mass K h) (indicator K) e f

lemma weight_zero (K : FiniteSubgraphCode) (T : TreeSample K) :
    weight K 0 T = 1 := by simp [weight]

lemma partition_zero (K : FiniteSubgraphCode) :
    partition K 0 = ((spanningTrees K).card : ℝ) := by
  simp [partition, weight_zero]

lemma mass_zero (K : FiniteSubgraphCode) (T : TreeSample K) :
    mass K 0 T = 1 / ((spanningTrees K).card : ℝ) := by
  simp [mass, weight_zero, partition_zero]

lemma inclusion_eq_ratio (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ)
    (e : FiniteEdge K) : inclusion K h e =
      (∑ T : TreeSample K, weight K h T * indicator K T e) / partition K h := by
  simp only [inclusion, FiniteResponse.mean, mass, div_mul_eq_mul_div,
    Finset.sum_div]

lemma inclusion_zero (K : FiniteSubgraphCode) (e : FiniteEdge K) :
    inclusion K 0 e =
      (((spanningTrees K).filter (fun T => e.1 ∈ T)).card : ℝ) /
        (spanningTrees K).card := by
  rw [inclusion_eq_ratio, partition_zero]
  simp only [weight_zero, one_mul]
  unfold indicator
  rw [← Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl)
    (fun T => if e.1 ∈ T then (1 : ℝ) else 0), Finset.sum_boole]

lemma inclusion_zero_eq_ustCylinder (K : FiniteSubgraphCode) (e : EdgeCode)
    (he : e.1 ∈ K.2) :
    inclusion K 0 ⟨e.1, he⟩ = (ustCylinder K {e} ∅).toReal := by
  classical
  rw [inclusion_zero]
  simp [ustCylinder, ENNReal.toReal_div]

lemma inclusion_nonneg (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ)
    (hne : (spanningTrees K).Nonempty) (e : FiniteEdge K) : 0 ≤ inclusion K h e := by
  apply FiniteResponse.mean_nonneg (mass K h) (indicator K) (mass_nonneg K h hne)
  intro T f
  rcases indicator_binary K T f with ht | ht <;> simp [ht]

lemma inclusion_le_one (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ)
    (hne : (spanningTrees K).Nonempty) (e : FiniteEdge K) : inclusion K h e ≤ 1 := by
  apply FiniteResponse.mean_le_one (mass K h) (indicator K) (mass_nonneg K h hne)
    (sum_mass K h hne)
  intro T f
  rcases indicator_binary K T f with ht | ht <;> simp [ht]

lemma sum_edgeCovariance_eq_zero (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ)
    (hne : (spanningTrees K).Nonempty) (e : FiniteEdge K) :
    (∑ f, edgeCovariance K h e f) = 0 := by
  exact FiniteResponse.sum_covariance_eq_zero (mass K h) (indicator K)
    (sum_mass K h hne) ((K.1.card : ℝ) - 1) (sum_indicator K) e

theorem abs_covariance_row (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ)
    (hne : (spanningTrees K).Nonempty)
    (hneg : ∀ e f, e ≠ f → edgeCovariance K h e f ≤ 0) (e : FiniteEdge K) :
    (∑ f, |edgeCovariance K h e f|) =
      2 * inclusion K h e * (1 - inclusion K h e) := by
  exact FiniteResponse.covariance_abs_row (mass K h) (indicator K)
    (mass_nonneg K h hne) (sum_mass K h hne) (indicator_binary K)
    ((K.1.card : ℝ) - 1) (sum_indicator K) hneg e

theorem abs_covariance_row_le_half (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ)
    (hne : (spanningTrees K).Nonempty)
    (hneg : ∀ e f, e ≠ f → edgeCovariance K h e f ≤ 0) (e : FiniteEdge K) :
    (∑ f, |edgeCovariance K h e f|) ≤ (1 : ℝ) / 2 := by
  exact FiniteResponse.covariance_abs_row_le_half (mass K h) (indicator K)
    (mass_nonneg K h hne) (sum_mass K h hne) (indicator_binary K)
    ((K.1.card : ℝ) - 1) (sum_indicator K) hneg e

lemma inclusion_eq_gibbs_mean (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ)
    (e : FiniteEdge K) :
    inclusion K h e = GibbsField.mean (indicator K) (fun T => indicator K T e) h := by
  rw [GibbsField.coordinate_mean_eq_finiteResponse]
  rfl

lemma edgeCovariance_eq_gibbs_covariance (K : FiniteSubgraphCode)
    (h : FiniteEdge K → ℝ) (e f : FiniteEdge K) :
    edgeCovariance K h e f =
      GibbsField.covariance (indicator K) (fun T => indicator K T e)
        (fun T => indicator K T f) h := by
  rw [GibbsField.coordinate_covariance_eq_finiteResponse]
  rfl

theorem hasDerivAt_inclusion_direction (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty) (h k : FiniteEdge K → ℝ)
    (e : FiniteEdge K) (t : ℝ) :
    HasDerivAt (fun s => inclusion K (fun f => h f + s * k f) e)
      (∑ f, k f * edgeCovariance K (fun f => h f + t * k f) e f) t := by
  let : Nonempty (TreeSample K) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  simpa only [inclusion_eq_gibbs_mean, edgeCovariance_eq_gibbs_covariance] using
    GibbsField.hasDerivAt_mean_direction_sum (indicator K) (fun T => indicator K T e) h k t

theorem inclusion_response (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty)
    (hneg : ∀ h e f, e ≠ f → edgeCovariance K h e f ≤ 0)
    (a b : FiniteEdge K → ℝ) (e : FiniteEdge K) :
    |inclusion K b e - inclusion K a e| ≤ (1 / 2 : ℝ) * ‖b - a‖ := by
  let : Nonempty (TreeSample K) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hn : ∀ h e f, e ≠ f → GibbsField.covariance (indicator K)
      (fun T => indicator K T e) (fun T => indicator K T f) h ≤ 0 := by
    simpa only [edgeCovariance_eq_gibbs_covariance] using hneg
  simpa only [inclusion_eq_gibbs_mean] using
    GibbsField.response_bound (indicator K) (indicator_binary K)
      ((K.1.card : ℝ) - 1) (sum_indicator K) hn a b e

theorem inclusion_response_of_coordinate_bound (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty)
    (hneg : ∀ h e f, e ≠ f → edgeCovariance K h e f ≤ 0)
    (a b : FiniteEdge K → ℝ) (e : FiniteEdge K) (D : ℝ) (hD : 0 ≤ D)
    (hab : ∀ f, |b f - a f| ≤ D) :
    |inclusion K b e - inclusion K a e| ≤ D / 2 := by
  apply (inclusion_response K hne hneg a b e).trans
  have hn : ‖b - a‖ ≤ D := (pi_norm_le_iff_of_nonneg hD).mpr hab
  linarith

lemma continuous_inclusion (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty) (e : FiniteEdge K) :
    Continuous (fun h => inclusion K h e) := by
  let : Nonempty (TreeSample K) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  simpa only [inclusion_eq_gibbs_mean] using
    GibbsField.continuous_mean (indicator K) (fun T => indicator K T e)

lemma measurable_inclusion (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty) (e : FiniteEdge K) :
    Measurable (fun h => inclusion K h e) :=
  (continuous_inclusion K hne e).measurable

end Problem336.USTResponse

end

end OAI
