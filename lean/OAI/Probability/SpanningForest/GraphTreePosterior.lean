import OAI.Probability.SpanningForest.IntrinsicBridge
import OAI.Probability.SpanningForest.Exhaustion

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.GraphTreePosterior

def energy (T : Finset (ℕ × ℕ)) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : ℝ := by
  classical
  exact ∑ f ∈ S, if f.1 ∈ T then y f - t / 2 else 0

def weight (T : Finset (ℕ × ℕ)) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : ℝ := Real.exp (energy T S t y)

def partition (K : FiniteSubgraphCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : ℝ :=
  ∑ T ∈ spanningTrees K, weight T S t y

def numerator (K : FiniteSubgraphCode) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : ℝ := by
  classical
  exact ∑ T ∈ (spanningTrees K).filter (fun T => e.1 ∈ T), weight T S t y

def mean (K : FiniteSubgraphCode) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : ℝ := numerator K e S t y / partition K S t y

theorem weight_pos (T : Finset (ℕ × ℕ)) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : 0 < weight T S t y := Real.exp_pos _

theorem partition_nonneg (K : FiniteSubgraphCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : 0 ≤ partition K S t y :=
  Finset.sum_nonneg (fun T _ => (weight_pos T S t y).le)

theorem partition_pos {K : FiniteSubgraphCode} (hK : (spanningTrees K).Nonempty)
    (S : Finset EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) : 0 < partition K S t y :=
  Finset.sum_pos (fun T _ => weight_pos T S t y) hK

theorem numerator_nonneg (K : FiniteSubgraphCode) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : 0 ≤ numerator K e S t y :=
  Finset.sum_nonneg (fun T _ => (weight_pos T S t y).le)

theorem numerator_le_partition (K : FiniteSubgraphCode) (e : EdgeCode)
    (S : Finset EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    numerator K e S t y ≤ partition K S t y := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun T _ _ => (weight_pos T S t y).le)

theorem mean_mem_Icc (K : FiniteSubgraphCode) (e : EdgeCode)
    (S : Finset EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    mean K e S t y ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (numerator_nonneg K e S t y) (partition_nonneg K S t y), ?_⟩
  by_cases h : partition K S t y = 0
  · simp [mean, h]
  · exact (div_le_one (lt_of_le_of_ne (partition_nonneg K S t y) (Ne.symm h))).2
      (numerator_le_partition K e S t y)

theorem measurable_energy (T : Finset (ℕ × ℕ)) (S : Finset EdgeCode) :
    Measurable (fun q : ℝ × (EdgeCode → ℝ) => energy T S q.1 q.2) := by
  classical
  apply Finset.measurable_sum
  intro f _
  by_cases hf : f.1 ∈ T
  · have hy : Measurable (fun q : ℝ × (EdgeCode → ℝ) => q.2 f) :=
      (measurable_pi_apply f).comp measurable_snd
    have ht : Measurable (fun q : ℝ × (EdgeCode → ℝ) => q.1 / 2) :=
      measurable_fst.div_const (2 : ℝ)
    simpa only [hf, ite_true, Pi.sub_def] using hy.sub ht
  · simp only [hf, ite_false]
    exact measurable_const

theorem measurable_weight (T : Finset (ℕ × ℕ)) (S : Finset EdgeCode) :
    Measurable (fun q : ℝ × (EdgeCode → ℝ) => weight T S q.1 q.2) :=
  (measurable_energy T S).exp

theorem measurable_partition (K : FiniteSubgraphCode) (S : Finset EdgeCode) :
    Measurable (fun q : ℝ × (EdgeCode → ℝ) => partition K S q.1 q.2) :=
  Finset.measurable_sum _ (fun T _ => measurable_weight T S)

theorem measurable_numerator (K : FiniteSubgraphCode) (e : EdgeCode) (S : Finset EdgeCode) :
    Measurable (fun q : ℝ × (EdgeCode → ℝ) => numerator K e S q.1 q.2) :=
  Finset.measurable_sum _ (fun T _ => measurable_weight T S)

theorem measurable_mean (K : FiniteSubgraphCode) (e : EdgeCode) (S : Finset EdgeCode) :
    Measurable (fun q : ℝ × (EdgeCode → ℝ) => mean K e S q.1 q.2) :=
  (measurable_numerator K e S).div (measurable_partition K S)

theorem measurable_mean_joint :
    Measurable (fun q : (FiniteSubgraphCode × (EdgeCode × Finset EdgeCode)) ×
        (ℝ × (EdgeCode → ℝ)) => mean q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2) := by
  apply measurable_from_prod_countable_right
  intro q
  exact measurable_mean q.1 q.2.1 q.2.2

theorem mean_zero (K : FiniteSubgraphCode) (e : EdgeCode) (S : Finset EdgeCode) :
    mean K e S 0 (fun _ => 0) = (ustCylinder K {e} ∅).toReal := by
  classical
  simp [mean, numerator, partition, weight, energy, ustCylinder, ENNReal.toReal_div]

theorem mean_of_not_mem {K : FiniteSubgraphCode} {e : EdgeCode}
    (he : e.1 ∉ K.2) (S : Finset EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    mean K e S t y = 0 := by
  classical
  have hempty : (spanningTrees K).filter (fun T => e.1 ∈ T) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro T hT heT
    have hTree : TreeOn K T := (Finset.mem_filter.mp hT).2
    exact he (hTree.1 heT)
  simp [mean, numerator, hempty]

def edgeCodes (K : FiniteSubgraphCode) : Finset EdgeCode :=
  K.2.subtype (fun p => p.1 < p.2)

@[simp] theorem mem_edgeCodes (K : FiniteSubgraphCode) (e : EdgeCode) :
    e ∈ edgeCodes K ↔ e.1 ∈ K.2 := Finset.mem_subtype

theorem measurable_edgeCodes : Measurable edgeCodes := measurable_of_countable _

theorem mean_congr_field (K : FiniteSubgraphCode) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y z : EdgeCode → ℝ) (h : ∀ f ∈ S, y f = z f) :
    mean K e S t y = mean K e S t z := by
  have hw (T : Finset (ℕ × ℕ)) : weight T S t y = weight T S t z := by
    unfold weight energy
    congr 1
    apply Finset.sum_congr rfl
    intro f hf
    rw [h f hf]
  simp only [mean, numerator, partition, hw]

def finiteBallMean (G : GraphCode) (e : EdgeCode) (n m : ℕ)
    (t : ℝ) (y : EdgeCode → ℝ) : ℝ :=
  mean (Intrinsic.exhaustion G e m) e (edgeCodes (Intrinsic.exhaustion G e n)) t y

theorem finiteBallMean_mem_Icc (G : GraphCode) (e : EdgeCode) (n m : ℕ)
    (t : ℝ) (y : EdgeCode → ℝ) :
    finiteBallMean G e n m t y ∈ Set.Icc (0 : ℝ) 1 :=
  mean_mem_Icc (Intrinsic.exhaustion G e m) e (edgeCodes (Intrinsic.exhaustion G e n)) t y

theorem measurable_finiteBallMean (e : EdgeCode) (n m : ℕ) :
    Measurable (fun q : GraphCode × (ℝ × (EdgeCode → ℝ)) =>
      finiteBallMean q.1 e n m q.2.1 q.2.2) := by
  let Ω := GraphCode × (ℝ × (EdgeCode → ℝ))
  have hK0 : Measurable (fun G : GraphCode => Intrinsic.exhaustion G e m) :=
    Intrinsic.measurable_exhaustion.comp (measurable_id.prodMk
      (measurable_const : Measurable (fun _ : GraphCode => (m, e))))
  have hS0 : Measurable (fun G : GraphCode => Intrinsic.exhaustion G e n) :=
    Intrinsic.measurable_exhaustion.comp (measurable_id.prodMk
      (measurable_const : Measurable (fun _ : GraphCode => (n, e))))
  have hK : Measurable (fun q : Ω => Intrinsic.exhaustion q.1 e m) :=
    hK0.comp measurable_fst
  have hS : Measurable (fun q : Ω => edgeCodes (Intrinsic.exhaustion q.1 e n)) :=
    measurable_edgeCodes.comp (hS0.comp measurable_fst)
  have hE : Measurable (fun _ : Ω => e) := measurable_const
  have hF : Measurable (fun q : Ω => q.2) := measurable_snd
  have hArgs := (hK.prodMk (hE.prodMk hS)).prodMk hF
  have h := measurable_mean_joint.comp hArgs
  simpa only [Function.comp_def, finiteBallMean] using h

theorem eventually_mem_observedEdges {G : GraphCode} (hC : GraphConnected G)
    (hL : GraphLocallyFinite G) (e : EdgeCode) (he : Adj G e.1.1 e.1.2)
    (f : EdgeCode) (hf : Adj G f.1.1 f.1.2) :
    ∀ᶠ n in Filter.atTop, f ∈ edgeCodes (Intrinsic.exhaustion G e n) := by
  have hH := Intrinsic.isConnectedExhaustion G hC hL e he
  simpa only [mem_edgeCodes] using hH.eventually_mem_edges f hf

end Problem336.GraphTreePosterior

end

end OAI
