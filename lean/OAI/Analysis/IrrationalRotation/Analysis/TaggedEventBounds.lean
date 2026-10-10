import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic

namespace OAI

namespace InvariantRotation.TaggedEventBounds

theorem neg_div_one_sub_le_log {t : ℝ} (ht : t < 1) :
    -t / (1 - t) ≤ Real.log (1 - t) := by
  have hp : 0 < 1 - t := sub_pos.mpr ht
  have heq : -t / (1 - t) = 1 - (1 - t)⁻¹ := by
    field_simp
    ring
  rw [heq]
  exact Real.one_sub_inv_le_log_of_pos hp

theorem exp_neg_le_one_sub_pow (n : ℕ) {t a : ℝ} (ht : t < 1)
    (hbudget : (n : ℝ) * t ≤ a * (1 - t)) :
    Real.exp (-a) ≤ (1 - t) ^ n := by
  have hp : 0 < 1 - t := sub_pos.mpr ht
  apply (Real.le_log_iff_exp_le (pow_pos hp n)).mp
  rw [Real.log_pow]
  have hb : -a ≤ (n : ℝ) * (-t / (1 - t)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hp).mpr
    nlinarith
  exact hb.trans (mul_le_mul_of_nonneg_left
    (neg_div_one_sub_le_log ht) (Nat.cast_nonneg n))

theorem circle_tag_bound (m : ℕ) (hm : 200 ≤ m) :
    Real.exp (-90) ≤ (1 - 61 / (m : ℝ)) ^ (m - 1) := by
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hsub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  apply exp_neg_le_one_sub_pow (m - 1)
  · exact (div_lt_one hmpos).mpr (by linarith)
  · rw [hsub]
    apply (mul_le_mul_iff_left₀ hmpos).mp
    field_simp
    nlinarith

theorem product_tag_bound (m : ℕ) (hm : 100 ≤ m) :
    Real.exp (-82) ≤ (1 - 41 / (m : ℝ)) ^ (m - 1) := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hsub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  apply exp_neg_le_one_sub_pow (m - 1)
  · exact (div_lt_one hmpos).mpr (by linarith)
  · rw [hsub]
    apply (mul_le_mul_iff_left₀ hmpos).mp
    field_simp
    nlinarith

open MeasureTheory

section ProductEvent

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

def tagRectangle (T G : ι → Set Ω) (i : ι) : Set (ι → Ω) :=
  Set.pi Set.univ (fun j => if j = i then T j else G j)

def oneTagEvent (T G : ι → Set Ω) : Set (ι → Ω) :=
  ⋃ i, tagRectangle T G i

omit [Fintype ι] [MeasurableSpace Ω] in
theorem tagRectangle_pairwiseDisjoint (T G : ι → Set Ω)
    (hdis : ∀ i, Disjoint (T i) (G i)) :
    Pairwise (fun i j => Disjoint (tagRectangle T G i) (tagRectangle T G j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi : x i ∈ T i := by simpa [tagRectangle] using hxi i (Set.mem_univ i)
  have hj : x i ∈ G i := by simpa [tagRectangle, hij] using hxj i (Set.mem_univ i)
  exact Set.disjoint_left.mp (hdis i) hi hj

theorem measurableSet_tagRectangle (T G : ι → Set Ω)
    (hT : ∀ i, MeasurableSet (T i)) (hG : ∀ i, MeasurableSet (G i)) (i : ι) :
    MeasurableSet (tagRectangle T G i) := by
  apply MeasurableSet.univ_pi
  intro j
  split_ifs
  · exact hT j
  · exact hG j

theorem measurableSet_oneTagEvent (T G : ι → Set Ω)
    (hT : ∀ i, MeasurableSet (T i)) (hG : ∀ i, MeasurableSet (G i)) :
    MeasurableSet (oneTagEvent T G) :=
  MeasurableSet.iUnion (measurableSet_tagRectangle T G hT hG)

theorem oneTagEvent_measureReal (μ : ι → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (T G : ι → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) (hdis : ∀ i, Disjoint (T i) (G i)) :
    (Measure.pi μ).real (oneTagEvent T G) =
      ∑ i, ∏ j, (μ j).real (if j = i then T j else G j) := by
  rw [oneTagEvent, measureReal_iUnion_fintype (tagRectangle_pairwiseDisjoint T G hdis)
    (measurableSet_tagRectangle T G hT hG)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [tagRectangle, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]

theorem oneTagEvent_measureReal_lower_bound
    (μ : ι → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (T G : ι → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) (hdis : ∀ i, Disjoint (T i) (G i))
    {t g : ℝ} (ht : 0 ≤ t) (hg : 0 ≤ g)
    (hTag : ∀ i, t ≤ (μ i).real (T i)) (hGood : ∀ i, g ≤ (μ i).real (G i)) :
    (Fintype.card ι : ℝ) * t * g ^ (Fintype.card ι - 1) ≤
      (Measure.pi μ).real (oneTagEvent T G) := by
  rw [oneTagEvent_measureReal μ T G hT hG hdis]
  have hprod (i : ι) : (∏ j : ι, if j = i then t else g) =
      t * g ^ (Fintype.card ι - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => if j = i then t else g) (Finset.mem_univ i)]
    simp only [ite_true]
    congr 1
    calc
      (∏ j ∈ Finset.univ.erase i, if j = i then t else g) =
          ∏ _j ∈ Finset.univ.erase i, g := by
        apply Finset.prod_congr rfl
        intro j hj
        exact ite_eq_right (Finset.mem_erase.mp hj).1
      _ = g ^ (Fintype.card ι - 1) := by simp
  calc
    (Fintype.card ι : ℝ) * t * g ^ (Fintype.card ι - 1) =
        ∑ _i : ι, t * g ^ (Fintype.card ι - 1) := by simp [mul_assoc]
    _ = ∑ i : ι, ∏ j : ι, if j = i then t else g := by simp_rw [hprod]
    _ ≤ ∑ i, ∏ j, (μ j).real (if j = i then T j else G j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.prod_le_prod₀
      · intro j hj
        split_ifs <;> assumption
      · intro j hj
        split_ifs
        · exact hTag j
        · exact hGood j

theorem oneTagEvent_measureReal_ge_pow (m : ℕ) (hm : 0 < m)
    (μ : Fin m → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (T G : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) (hdis : ∀ i, Disjoint (T i) (G i))
    {g : ℝ} (hg : 0 ≤ g)
    (hTag : ∀ i, 1 / (m : ℝ) ≤ (μ i).real (T i))
    (hGood : ∀ i, g ≤ (μ i).real (G i)) :
    g ^ (m - 1) ≤ (Measure.pi μ).real (oneTagEvent T G) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := oneTagEvent_measureReal_lower_bound μ T G hT hG hdis
    (t := 1 / (m : ℝ)) (by positivity) hg hTag hGood
  simp only [Fintype.card_fin] at h
  have hcancel : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
  simpa only [hcancel, one_mul] using h

theorem circle_oneTagEvent_bound (m : ℕ) (hm : 200 ≤ m)
    (μ : Fin m → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (T G : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) (hdis : ∀ i, Disjoint (T i) (G i))
    (hTag : ∀ i, 1 / (m : ℝ) ≤ (μ i).real (T i))
    (hGood : ∀ i, 1 - 61 / (m : ℝ) ≤ (μ i).real (G i)) :
    Real.exp (-90) ≤ (Measure.pi μ).real (oneTagEvent T G) := by
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  refine (circle_tag_bound m hm).trans
    (oneTagEvent_measureReal_ge_pow m (by omega) μ T G hT hG hdis ?_ hTag hGood)
  exact sub_nonneg.mpr ((div_le_one hmpos).mpr (by linarith))

theorem product_oneTagEvent_bound (m : ℕ) (hm : 100 ≤ m)
    (μ : Fin m → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (T G : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) (hdis : ∀ i, Disjoint (T i) (G i))
    (hTag : ∀ i, 1 / (m : ℝ) ≤ (μ i).real (T i))
    (hGood : ∀ i, 1 - 41 / (m : ℝ) ≤ (μ i).real (G i)) :
    Real.exp (-82) ≤ (Measure.pi μ).real (oneTagEvent T G) := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  refine (product_tag_bound m hm).trans
    (oneTagEvent_measureReal_ge_pow m (by omega) μ T G hT hG hdis ?_ hTag hGood)
  exact sub_nonneg.mpr ((div_le_one hmpos).mpr (by linarith))

end ProductEvent

section InfiniteProductEvent

variable {κ Ω : Type*} [DecidableEq κ] [MeasurableSpace Ω]

theorem infinitePi_oneTagEvent_measureReal
    (μ : κ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (J : Finset κ)
    (T G : J → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) :
    (Measure.infinitePi μ).real (J.restrict ⁻¹' oneTagEvent T G) =
      (Measure.pi (fun i : J => μ i)).real (oneTagEvent T G) := by
  classical
  simp only [measureReal_def]
  rw [← Measure.map_apply (Finset.measurable_restrict J) (measurableSet_oneTagEvent T G hT hG),
    Measure.infinitePi_map_restrict]

theorem infinitePi_oneTagEvent_lower_bound
    (μ : κ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (J : Finset κ)
    (T G : J → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) (hdis : ∀ i, Disjoint (T i) (G i))
    {t g : ℝ} (ht : 0 ≤ t) (hg : 0 ≤ g)
    (hTag : ∀ i : J, t ≤ (μ i).real (T i))
    (hGood : ∀ i : J, g ≤ (μ i).real (G i)) :
    (J.card : ℝ) * t * g ^ (J.card - 1) ≤
      (Measure.infinitePi μ).real (J.restrict ⁻¹' oneTagEvent T G) := by
  classical
  rw [infinitePi_oneTagEvent_measureReal μ J T G hT hG]
  simpa using oneTagEvent_measureReal_lower_bound (fun i : J => μ i)
    T G hT hG hdis ht hg hTag hGood

end InfiniteProductEvent

section EventLoss

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measureReal_remove_bad_union {ι : Type*} [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Set Ω) (B : ι → Set Ω) :
    μ.real A - ∑ i, μ.real (B i) ≤ μ.real (A \ ⋃ i, B i) := by
  have hsum := measureReal_iUnion_fintype_le (μ := μ) B
  have hremove := le_measureReal_sdiff (μ := μ) (s₁ := A) (s₂ := ⋃ i, B i)
  linarith

theorem admissible_nontag_measureReal_lower_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T B₁ B₂ : Set Ω)
    (hT : MeasurableSet T) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂)
    {t b₁ b₂ : ℝ} (hTag : μ.real T ≤ t)
    (hBad₁ : μ.real B₁ ≤ b₁) (hBad₂ : μ.real B₂ ≤ b₂) :
    1 - t - b₁ - b₂ ≤ μ.real (Tᶜ ∩ B₁ᶜ ∩ B₂ᶜ) := by
  have hbound : μ.real (T ∪ B₁ ∪ B₂) ≤ t + b₁ + b₂ :=
    (measureReal_union_le (T ∪ B₁) B₂).trans
      (add_le_add ((measureReal_union_le T B₁).trans (add_le_add hTag hBad₁)) hBad₂)
  have heq : μ.real (Tᶜ ∩ B₁ᶜ ∩ B₂ᶜ) = 1 - μ.real (T ∪ B₁ ∪ B₂) := by
    rw [← Set.compl_union, ← Set.compl_union, measureReal_compl (hT.union hB₁ |>.union hB₂)]
    simp
  rw [heq]
  linarith

theorem eventually_half_le_measureReal_sdiff
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (A B : ℕ → Set Ω) {c : ℝ} (hc : 0 < c)
    (hbase : ∀ᶠ n in Filter.atTop, c ≤ (μ n).real (A n))
    (hloss : Filter.Tendsto (fun n => (μ n).real (B n)) Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop, c / 2 ≤ (μ n).real (A n \ B n) := by
  have hsmall : ∀ᶠ n in Filter.atTop, (μ n).real (B n) < c / 2 :=
    (tendsto_order.1 hloss).2 (c / 2) (by linarith)
  filter_upwards [hbase, hsmall] with n hn hsmalln
  have hremove := le_measureReal_sdiff (μ := μ n) (s₁ := A n) (s₂ := B n)
  linarith

theorem eventually_half_le_measureReal_remove_bad_union
    {ι : Type*} [Fintype ι] (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (A : ℕ → Set Ω) (B : ℕ → ι → Set Ω) {c : ℝ} (hc : 0 < c)
    (hbase : ∀ᶠ n in Filter.atTop, c ≤ (μ n).real (A n))
    (hloss : Filter.Tendsto (fun n => ∑ i, (μ n).real (B n i))
      Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop, c / 2 ≤ (μ n).real (A n \ ⋃ i, B n i) := by
  have hsmall : ∀ᶠ n in Filter.atTop, (∑ i, (μ n).real (B n i)) < c / 2 :=
    (tendsto_order.1 hloss).2 (c / 2) (by linarith)
  filter_upwards [hbase, hsmall] with n hn hsmalln
  have hremove := measureReal_remove_bad_union (μ n) (A n) (B n)
  linarith

theorem eventually_half_le_measureReal_sdiff_varying
    {Ω' : ℕ → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (μ : (n : ℕ) → Measure (Ω' n)) [∀ n, IsFiniteMeasure (μ n)]
    (A B : (n : ℕ) → Set (Ω' n)) {c : ℝ} (hc : 0 < c)
    (hbase : ∀ᶠ n in Filter.atTop, c ≤ (μ n).real (A n))
    (hloss : Filter.Tendsto (fun n => (μ n).real (B n)) Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop, c / 2 ≤ (μ n).real (A n \ B n) := by
  have hsmall : ∀ᶠ n in Filter.atTop, (μ n).real (B n) < c / 2 :=
    (tendsto_order.1 hloss).2 (c / 2) (by linarith)
  filter_upwards [hbase, hsmall] with n hn hsmalln
  have hremove := le_measureReal_sdiff (μ := μ n) (s₁ := A n) (s₂ := B n)
  linarith

theorem eventually_half_le_measureReal_remove_bad_union_varying
    {Ω' : ℕ → Type*} [∀ n, MeasurableSpace (Ω' n)] {ι : Type*} [Fintype ι]
    (μ : (n : ℕ) → Measure (Ω' n)) [∀ n, IsFiniteMeasure (μ n)]
    (A : (n : ℕ) → Set (Ω' n)) (B : (n : ℕ) → ι → Set (Ω' n))
    {c : ℝ} (hc : 0 < c)
    (hbase : ∀ᶠ n in Filter.atTop, c ≤ (μ n).real (A n))
    (hloss : Filter.Tendsto (fun n => ∑ i, (μ n).real (B n i))
      Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop, c / 2 ≤ (μ n).real (A n \ ⋃ i, B n i) := by
  have hsmall : ∀ᶠ n in Filter.atTop, (∑ i, (μ n).real (B n i)) < c / 2 :=
    (tendsto_order.1 hloss).2 (c / 2) (by linarith)
  filter_upwards [hbase, hsmall] with n hn hsmalln
  have hremove := measureReal_remove_bad_union (μ n) (A n) (B n)
  linarith

end EventLoss


variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

def currentBlockEvent (T B₁ B₂ : ι → Set Ω) : Set (ι → Ω) :=
  {x | (∃ i, x i ∈ T i) ∧ ∀ i, x i ∉ B₁ i ∧ x i ∉ B₂ i}

omit [DecidableEq ι] in
theorem measurableSet_currentBlockEvent (T B₁ B₂ : ι → Set Ω)
    (hT : ∀ i, MeasurableSet (T i)) (hB₁ : ∀ i, MeasurableSet (B₁ i))
    (hB₂ : ∀ i, MeasurableSet (B₂ i)) :
    MeasurableSet (currentBlockEvent T B₁ B₂) := by
  change MeasurableSet ({x : ι → Ω | ∃ i, x i ∈ T i} ∩
    {x : ι → Ω | ∀ i, x i ∉ B₁ i ∧ x i ∉ B₂ i})
  rw [Set.ofPred_exists, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iUnion
    intro i
    exact (hT i).preimage (measurable_pi_apply i)
  · apply MeasurableSet.iInter
    intro i
    exact ((hB₁ i).preimage (measurable_pi_apply i)).compl.inter
      ((hB₂ i).preimage (measurable_pi_apply i)).compl

omit [Fintype ι] [MeasurableSpace Ω] in
theorem oneTagEvent_subset_currentBlockEvent (T B₁ B₂ : ι → Set Ω)
    (hTagSafe : ∀ i, T i ⊆ (B₁ i)ᶜ ∩ (B₂ i)ᶜ) :
    oneTagEvent T (fun i => (T i)ᶜ ∩ (B₁ i)ᶜ ∩ (B₂ i)ᶜ) ⊆
      currentBlockEvent T B₁ B₂ := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have htag : x i ∈ T i := by
    simpa [tagRectangle] using hi i (Set.mem_univ i)
  refine ⟨⟨i, htag⟩, ?_⟩
  intro j
  by_cases hji : j = i
  · subst j
    exact hTagSafe i htag
  · have hj : x j ∈ (T j)ᶜ ∩ (B₁ j)ᶜ ∩ (B₂ j)ᶜ := by
      simpa [tagRectangle, hji] using hi j (Set.mem_univ j)
    exact ⟨hj.1.2, hj.2⟩

theorem currentBlockEvent_measureReal_lower_bound (m : ℕ) (hm : 0 < m)
    (μ : Fin m → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (T B₁ B₂ : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hB₁ : ∀ i, MeasurableSet (B₁ i)) (hB₂ : ∀ i, MeasurableSet (B₂ i))
    (hTagSafe : ∀ i, T i ⊆ (B₁ i)ᶜ ∩ (B₂ i)ᶜ) {a : ℝ}
    (hg : 0 ≤ 1 - (1 + 2 * a) / (m : ℝ))
    (hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ))
    (hBad₁ : ∀ i, (μ i).real (B₁ i) ≤ a / (m : ℝ))
    (hBad₂ : ∀ i, (μ i).real (B₂ i) ≤ a / (m : ℝ)) :
    (1 - (1 + 2 * a) / (m : ℝ)) ^ (m - 1) ≤
      (Measure.pi μ).real (currentBlockEvent T B₁ B₂) := by
  let G : Fin m → Set Ω := fun i => (T i)ᶜ ∩ (B₁ i)ᶜ ∩ (B₂ i)ᶜ
  have hG : ∀ i, MeasurableSet (G i) := fun i =>
    ((hT i).compl.inter (hB₁ i).compl).inter (hB₂ i).compl
  have hdis : ∀ i, Disjoint (T i) (G i) := by
    intro i
    exact Set.disjoint_left.mpr (fun x hx hGx => hGx.1.1 hx)
  have hGood : ∀ i, 1 - (1 + 2 * a) / (m : ℝ) ≤ (μ i).real (G i) := by
    intro i
    have h := admissible_nontag_measureReal_lower_bound (μ i) (T i) (B₁ i) (B₂ i)
      (hT i) (hB₁ i) (hB₂ i) (le_of_eq (hTag i)) (hBad₁ i) (hBad₂ i)
    convert h using 1
    ring
  exact (oneTagEvent_measureReal_ge_pow m hm μ T G hT hG hdis hg
    (fun i => (hTag i).ge) hGood).trans
    (measureReal_mono (oneTagEvent_subset_currentBlockEvent T B₁ B₂ hTagSafe))


end InvariantRotation.TaggedEventBounds

end OAI
