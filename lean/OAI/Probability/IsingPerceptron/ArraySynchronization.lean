import Mathlib
import OAI.Probability.IsingPerceptron.TiltedLabelLaw

namespace OAI

/-! Array Synchronization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix

namespace IsingPerceptron

 
def arrayBlock {Ω : Type*} (B : Ω → ℕ → ℕ → ℝ) (n : ℕ) (ω : Ω) :
    Fin n → Fin n → ℝ := fun i j => B ω i j

 

def HasGhirlandaGuerra {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → ℕ → ℕ → ℝ) (μ : Measure Ω) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (i : Fin n)
    (A : Set (Fin n → Fin n → ℝ)), MeasurableSet A →
    ∀ (t : Set ℝ), MeasurableSet t →
    μ.real ((arrayBlock B n ⁻¹' A) ∩ {ω | B ω i n ∈ t}) =
      (μ.real (arrayBlock B n ⁻¹' A) * μ.real {ω | B ω 0 1 ∈ t}) / n +
      (∑ j ∈ Finset.univ.erase i,
        μ.real ((arrayBlock B n ⁻¹' A) ∩ {ω | B ω i j ∈ t})) / n

 
def negativeBlock {Ω : Type*} (B : Ω → ℕ → ℕ → ℝ) (ε : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ i j : Fin n, i ≠ j → B ω i j < -ε}

lemma matrix_sum_le_of_offDiagonal {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    {D ε : ℝ} (hdiag : ∀ i, B i i = D)
    (hoff : ∀ i j, i ≠ j → B i j ≤ -ε) :
    ∑ i, ∑ j, B i j ≤ (n : ℝ) * (D - (n - 1 : ℝ) * ε) := by
  classical
  have hrow : ∀ i, ∑ j, B i j ≤ D - (n - 1 : ℝ) * ε := by
    intro i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hdiag i]
    have hn : 0 < n := (Nat.zero_le i.val).trans_lt i.isLt
    have h := Finset.sum_le_sum (s := Finset.univ.erase i) (f := fun j => B i j)
      (g := fun _ => -ε) (fun j hj => hoff i j (Ne.symm (Finset.mem_erase.mp hj).1))
    have hcard : (Finset.univ.erase i).card = n - 1 := by simp
    simp only [Finset.sum_const, nsmul_eq_mul, hcard] at h
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h
    linarith
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)

lemma posSemidef_sum_nonneg {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef) : 0 ≤ ∑ i, ∑ j, B i j := by
  simpa [dotProduct, Matrix.mulVec] using hB.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))

lemma no_large_negative_block {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    {D ε : ℝ} (hn : 0 < n) (hsize : D < (n - 1 : ℝ) * ε)
    (hB : B.PosSemidef) (hdiag : ∀ i, B i i = D)
    (hoff : ∀ i j, i ≠ j → B i j < -ε) : False := by
  have hs := matrix_sum_le_of_offDiagonal hdiag (fun i j h => (hoff i j h).le)
  have hp := posSemidef_sum_nonneg hB
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

lemma measurableSet_negative_finite (n : ℕ) (ε : ℝ) :
    MeasurableSet {b : Fin n → Fin n → ℝ | ∀ i j, i ≠ j → b i j < -ε} := by
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
    MeasurableSet.iInter (fun _ => ?_)))
  exact measurableSet_lt
    ((measurable_pi_apply j).comp (measurable_pi_apply i)) measurable_const

lemma mem_negativeBlock_succ {Ω : Type*} {B : Ω → ℕ → ℕ → ℝ}
    (hsym : ∀ ω i j, B ω i j = B ω j i) {ω : Ω} {ε : ℝ} {n : ℕ} :
    ω ∈ negativeBlock B ε (n + 1) ↔
      ω ∈ negativeBlock B ε n ∧ ∀ i : Fin n, B ω i n < -ε := by
  constructor
  · intro h
    constructor
    · intro i j hij
      exact h i.castSucc j.castSucc (fun he => hij (Fin.ext (congrArg (fun t : Fin (n + 1) => t.val) he)))
    · intro i
      exact h i.castSucc (Fin.last n) (by intro he; have := congrArg Fin.val he; simp at this; omega)
  · rintro ⟨h, ht⟩ i j hij
    by_cases hi : i.val < n
    · by_cases hj : j.val < n
      · exact h ⟨i.val, hi⟩ ⟨j.val, hj⟩ (fun he => hij (Fin.ext (congrArg (fun t : Fin n => t.val) he)))
      · have hjn : j.val = n := by omega
        change B ω i.val j.val < -ε
        rw [hjn]
        exact ht ⟨i.val, hi⟩
    · have hin : i.val = n := by omega
      by_cases hj : j.val < n
      · change B ω i.val j.val < -ε
        rw [hin, hsym]
        exact ht ⟨j.val, hj⟩
      · have hjn : j.val = n := by omega
        exact (hij (Fin.ext (hin.trans hjn.symm))).elim

lemma negativeBlock_two {Ω : Type*} {B : Ω → ℕ → ℕ → ℝ}
    (hsym : ∀ ω i j, B ω i j = B ω j i) (ε : ℝ) :
    negativeBlock B ε 2 = {ω | B ω 0 1 < -ε} := by
  ext ω
  constructor
  · intro h
    exact h 0 1 (by decide)
  · intro h i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact h
    · change B ω 1 0 < -ε
      rw [hsym]
      exact h
    · exact (hij rfl).elim

lemma negativeBlock_next_probability {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → ℕ → ℕ → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : ∀ i j, Measurable (fun ω => B ω i j))
    (hsym : ∀ ω i j, B ω i j = B ω j i) (hGG : HasGhirlandaGuerra B μ)
    (ε : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    μ.real (negativeBlock B ε n) * μ.real {ω | B ω 0 1 < -ε} ≤
      μ.real (negativeBlock B ε (n + 1)) := by
  classical
  let A := negativeBlock B ε n
  let Bad := fun i : Fin n => A ∩ {ω | -ε ≤ B ω i n}
  have hbase : μ.real {ω | -ε ≤ B ω 0 1} = 1 - μ.real {ω | B ω 0 1 < -ε} := by
    have hset : {ω | -ε ≤ B ω 0 1} = {ω | B ω 0 1 < -ε}ᶜ := by ext ω; simp
    rw [hset, measureReal_compl (measurableSet_lt (hm 0 1) measurable_const), probReal_univ]
  have hbad : ∀ i : Fin n, μ.real (Bad i) =
      μ.real A * (1 - μ.real {ω | B ω 0 1 < -ε}) / n := by
    intro i
    have h := hGG n hn i {b | ∀ i j, i ≠ j → b i j < -ε}
      (measurableSet_negative_finite n ε) (Set.Ici (-ε)) measurableSet_Ici
    have hp : arrayBlock B n ⁻¹' {b | ∀ i j, i ≠ j → b i j < -ε} = A := rfl
    rw [hp] at h
    have hz : ∀ j ∈ Finset.univ.erase i,
        A ∩ {ω | B ω i j ∈ Set.Ici (-ε)} = ∅ := by
      intro j hj
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨hω, hω'⟩
      exact (not_le_of_gt (hω i j (Ne.symm (Finset.mem_erase.mp hj).1))) hω'
    have hzero : (∑ j ∈ Finset.univ.erase i,
        μ.real (A ∩ {ω | B ω i j ∈ Set.Ici (-ε)})) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hz j hj, measureReal_empty]
    rw [hzero] at h
    simp only [zero_div, add_zero, Set.mem_Ici] at h
    simpa only [Bad, hbase] using h
  have hsub : A ⊆ negativeBlock B ε (n + 1) ∪ ⋃ i : Fin n, Bad i := by
    intro ω hω
    by_cases ht : ∀ i : Fin n, B ω i n < -ε
    · exact Or.inl ((mem_negativeBlock_succ hsym).mpr ⟨hω, ht⟩)
    · right
      push Not at ht
      obtain ⟨i, hi⟩ := ht
      exact Set.mem_iUnion.mpr ⟨i, hω, hi⟩
  have hbound := (measureReal_mono (μ := μ) hsub).trans
    (measureReal_union_le (negativeBlock B ε (n + 1)) (⋃ i : Fin n, Bad i))
  have hsum := measureReal_iUnion_fintype_le Bad (μ := μ)
  simp_rw [hbad] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [mul_div_left_comm, div_self hn', mul_one] at hsum
  nlinarith

lemma gg_negative_probability_zero {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → ℕ → ℕ → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℝ}
    (hm : ∀ i j, Measurable (fun ω => B ω i j))
    (hsym : ∀ ω i j, B ω i j = B ω j i) (hGG : HasGhirlandaGuerra B μ)
    (hGram : ∀ᵐ ω ∂μ, ∀ n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | B ω 0 1 < -ε} = 0 := by
  apply (measureReal_eq_zero_iff (μ := μ)).mp
  by_contra hbne
  have hb : 0 < μ.real {ω | B ω 0 1 < -ε} :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hbne)
  have hblocks : ∀ k : ℕ, 0 < μ.real (negativeBlock B ε (k + 2)) := by
    intro k
    induction k with
    | zero => simpa only [Nat.zero_add, negativeBlock_two hsym] using hb
    | succ k ih =>
      have h := negativeBlock_next_probability hm hsym hGG ε (k + 2) (by omega)
      exact (mul_pos ih hb).trans_le (by simpa only [Nat.succ_add] using h)
  obtain ⟨m, hmgt⟩ := exists_nat_gt (D / ε)
  have hsize : D < ((m + 2 : ℕ) - 1 : ℝ) * ε := by
    have h := (div_lt_iff₀ hε).mp hmgt
    simp only [Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  have hnull : μ (negativeBlock B ε (m + 2)) = 0 := by
    have ha : ∀ᵐ ω ∂μ, ω ∉ negativeBlock B ε (m + 2) := by
      filter_upwards [hGram, hdiag] with ω hg hd
      intro hn
      exact no_large_negative_block (by omega : 0 < m + 2) hsize (hg (m + 2))
        (fun i => hd i) hn
    simpa using ae_iff.mp ha
  have hpos := hblocks m
  rw [Measure.real, hnull, ENNReal.toReal_zero] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

 

theorem gg_pair_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → ℕ → ℕ → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℝ}
    (hm : ∀ i j, Measurable (fun ω => B ω i j))
    (hsym : ∀ ω i j, B ω i j = B ω j i) (hGG : HasGhirlandaGuerra B μ)
    (hGram : ∀ᵐ ω ∂μ, ∀ n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D) :
    ∀ᵐ ω ∂μ, 0 ≤ B ω 0 1 := by
  have ha : ∀ k : ℕ, ∀ᵐ ω ∂μ, -(1 / (k + 1 : ℝ)) ≤ B ω 0 1 := by
    intro k
    rw [ae_iff]
    simp only [not_le]
    exact gg_negative_probability_zero hm hsym hGG hGram hdiag (by positivity)
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  simp only [neg_zero] at hlim
  exact le_of_tendsto' hlim hω

 

lemma polya_no_linear_cap {n : ℕ} (hn : 2 ≤ n) {b : ℝ} (hb : b < 1)
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (h0 : 0 < r 0)
    (hrec : ∀ k, r (k+1) = r k * ((n : ℝ) + k - b) / ((n : ℝ) + k))
    (hcap : ∀ k : ℕ, (k+1 : ℝ) * r k ≤ 1) : False := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let t : ℕ → ℝ := fun k => ((n : ℝ) + k - 1) * r k
  have ht : ∀ k, t (k+1) = t k + (1-b) * r k := by
    intro k
    have hnk : (n : ℝ) + k ≠ 0 := by positivity
    dsimp [t]
    rw [hrec]
    push_cast
    field_simp
    ring
  have hbase : 0 < t 0 := by
    dsimp [t]; simp only [Nat.cast_zero, add_zero]
    exact mul_pos (by linarith) h0
  have hmono : Monotone t := monotone_nat_of_le_succ (fun k => by
    rw [ht]
    nlinarith [hr k])
  have hlower : ∀ k, t 0 / ((n : ℝ) + k - 1) ≤ r k := by
    intro k
    have h := hmono (Nat.zero_le k)
    have hden : 0 < (n : ℝ) + k - 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    exact (div_le_iff₀ hden).mpr (by simpa only [t, mul_comm] using h)
  have hsum : ∀ k, t 0 + (1-b)*t 0 *
      (∑ j ∈ Finset.range k, 1 / ((n : ℝ) + j - 1)) ≤ t k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ht]
      have he := mul_le_mul_of_nonneg_left (hlower k) (sub_pos.mpr hb).le
      calc
        _ = (t 0 + (1-b)*t 0 * (∑ j ∈ Finset.range k, 1 / ((n : ℝ) + j - 1))) +
              (1-b)*(t 0 / ((n : ℝ) + k - 1)) := by ring
        _ ≤ _ := add_le_add ih he
  have hupper : ∀ k, t k ≤ (n : ℝ) - 1 := by
    intro k
    have h := hcap k
    have he : (n : ℝ) + k - 1 ≤ ((n : ℝ)-1) * (k+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have he' := mul_le_mul_of_nonneg_right he (hr k)
    have h' := mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ (n : ℝ)-1)
    dsimp [t]
    nlinarith
  have hcompare : ∀ k, (∑ j ∈ Finset.range k, 1 / (j+1 : ℝ)) / n ≤
      ∑ j ∈ Finset.range k, 1 / ((n : ℝ) + j - 1) := by
    intro k
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hden : 0 < (n : ℝ) + j - 1 := by linarith
    rw [div_div]
    apply one_div_le_one_div_of_le hden
    nlinarith
  have hH : Tendsto (fun k => t 0 + (1-b)*t 0 *
      ((∑ j ∈ Finset.range k, 1 / (j+1 : ℝ)) / n)) atTop atTop := by
    apply tendsto_atTop_add_const_left
    apply Filter.Tendsto.const_mul_atTop (by positivity)
    exact Filter.Tendsto.atTop_div_const (by positivity)
      Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨k, hk⟩ := ((tendsto_atTop.1 hH) ((n : ℝ) - 1 + 1)).exists
  have he := (mul_le_mul_of_nonneg_left (hcompare k) (by positivity : 0 ≤ (1-b)*t 0))
  have hs := hsum k
  have hu := hupper k
  linarith

 

lemma equal_probability_aedisjoint_cap {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} {s : Fin (k+1) → Set Ω}
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => AEDisjoint μ (s i) (s j)))
    {r : ℝ} (hs : ∀ i, μ.real (s i) = r) : (k+1 : ℝ)*r ≤ 1 := by
  have he := measureReal_biUnion_finset₀ (μ := μ) (s := Finset.univ)
    (fun i _ j _ hij => hd hij) (fun i _ => (hm i).nullMeasurableSet)
    (fun i _ => measure_ne_top μ (s i))
  have hu : (⋃ i ∈ Finset.univ, s i) = ⋃ i, s i := by simp
  rw [hu] at he
  have hh : μ.real (⋃ i, s i) ≤ 1 := measureReal_le_one
  rw [he] at hh
  simpa [hs, Nat.cast_add, Nat.cast_one] using hh

abbrev RealArray := ℕ → ℕ → ℝ

def permuteArray (e : Equiv.Perm ℕ) (b : RealArray) : RealArray :=
  fun i j => b (e i) (e j)

 

def WeaklyExchangeable {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → RealArray) (μ : Measure Ω) : Prop :=
  ∀ e : Equiv.Perm ℕ, {i | e i ≠ i}.Finite →
    IdentDistrib B (fun ω => permuteArray e (B ω)) μ μ

lemma swap_hasFiniteSupport (i j : ℕ) : {a | (Equiv.swap i j) a ≠ a}.Finite := by
  apply ((Set.finite_singleton j).insert i).subset
  intro a ha
  by_contra hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hn
  exact ha (Equiv.swap_apply_of_ne_of_ne hn.1 hn.2)

lemma measurable_permuteArray (e : Equiv.Perm ℕ) : Measurable (permuteArray e) := by
  exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
    (measurable_pi_apply (e j)).comp (measurable_pi_apply (e i))

 

def starSet (a : ℕ) (J : Finset ℕ) (A : Set (Fin a → Fin a → ℝ))
    (T : Set (Fin a → ℝ)) (t : ℝ) (i : ℕ) : Set RealArray :=
  {b | (fun x y : Fin a => b x y) ∈ A ∧
    (fun x : Fin a => b x i) ∈ T ∧ ∀ j ∈ J, j ≠ i → b i j < t}

def duplicateSet (a : ℕ) (A : Set (Fin a → Fin a → ℝ))
    (T : Set (Fin a → ℝ)) (t : ℝ) (i j : ℕ) : Set RealArray :=
  {b | (fun x y : Fin a => b x y) ∈ A ∧
    (fun x : Fin a => b x i) ∈ T ∧
    (fun x : Fin a => b x j) ∈ T ∧ b i j < t}

lemma measurableSet_starSet {a : ℕ} (J : Finset ℕ) {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} (hA : MeasurableSet A) (hT : MeasurableSet T)
    (t : ℝ) (i : ℕ) : MeasurableSet (starSet a J A T t i) := by
  apply MeasurableSet.inter
  · exact hA.preimage (Measurable.of_eval fun x => Measurable.of_eval fun y =>
      (measurable_pi_apply (y : ℕ)).comp (measurable_pi_apply (x : ℕ)))
  apply MeasurableSet.inter
  · exact hT.preimage (Measurable.of_eval fun x =>
      (measurable_pi_apply i).comp (measurable_pi_apply (x : ℕ)))
  change MeasurableSet {b : RealArray | ∀ j ∈ J, j ≠ i → b i j < t}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => measurableSet_lt
      (by fun_prop : Measurable (fun b : RealArray => b i j)) measurable_const

lemma measurableSet_duplicateSet {a : ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} (hA : MeasurableSet A) (hT : MeasurableSet T)
    (t : ℝ) (i j : ℕ) : MeasurableSet (duplicateSet a A T t i j) := by
  apply MeasurableSet.inter
  · exact hA.preimage (Measurable.of_eval fun x => Measurable.of_eval fun y =>
      (measurable_pi_apply (y : ℕ)).comp (measurable_pi_apply (x : ℕ)))
  apply MeasurableSet.inter
  · exact hT.preimage (Measurable.of_eval fun x =>
      (measurable_pi_apply i).comp (measurable_pi_apply (x : ℕ)))
  exact (hT.preimage (Measurable.of_eval fun x =>
      (measurable_pi_apply j).comp (measurable_pi_apply (x : ℕ)))).inter
    (measurableSet_lt (by fun_prop : Measurable (fun b : RealArray => b i j)) measurable_const)

lemma starSet_permute {a : ℕ} {J : Finset ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} {t : ℝ} {i : ℕ} {e : Equiv.Perm ℕ}
    (hfix : ∀ x < a, e x = x) (hJ : ∀ j, j ∈ J ↔ e j ∈ J) :
    permuteArray e ⁻¹' starSet a J A T t i = starSet a J A T t (e i) := by
  ext b
  have hA : (fun x y : Fin a => permuteArray e b x y) = fun x y : Fin a => b x y := by
    funext x y
    simp only [permuteArray, hfix x x.isLt, hfix y y.isLt]
  have hT : (fun x : Fin a => permuteArray e b x i) = fun x : Fin a => b x (e i) := by
    funext x
    simp only [permuteArray, hfix x x.isLt]
  change (_ ∈ A ∧ _ ∈ T ∧ _) ↔ (_ ∈ A ∧ _ ∈ T ∧ _)
  rw [hA, hT]
  constructor
  · rintro ⟨ha, ht, hs⟩
    refine ⟨ha, ht, ?_⟩
    intro j hj hji
    have hj' : e.symm j ∈ J := (hJ _).mpr (by simpa using hj)
    have hji' : e.symm j ≠ i := by intro he; apply hji; rw [← he]; simp
    simpa only [permuteArray, Equiv.apply_symm_apply] using hs _ hj' hji'
  · rintro ⟨ha, ht, hs⟩
    exact ⟨ha, ht, fun j hj hji => hs (e j) ((hJ j).mp hj) (e.injective.ne hji)⟩

lemma duplicateSet_permute {a : ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} {t : ℝ} {i j : ℕ} {e : Equiv.Perm ℕ}
    (hfix : ∀ x < a, e x = x) :
    permuteArray e ⁻¹' duplicateSet a A T t i j = duplicateSet a A T t (e i) (e j) := by
  ext b
  change (_ ∈ A ∧ _ ∈ T ∧ _ ∈ T ∧ _) ↔ (_ ∈ A ∧ _ ∈ T ∧ _ ∈ T ∧ _)
  have hA : (fun x y : Fin a => permuteArray e b x y) = fun x y : Fin a => b x y := by
    funext x y
    simp only [permuteArray, hfix x x.isLt, hfix y y.isLt]
  have hT : ∀ i, (fun x : Fin a => permuteArray e b x i) = fun x : Fin a => b x (e i) := by
    intro i; funext x
    simp only [permuteArray, hfix x x.isLt]
  rw [hA, hT i, hT j]
  rfl

lemma swap_preserves_ge {a x y z : ℕ} (hx : a ≤ x) (hy : a ≤ y) (hz : a ≤ z) :
    a ≤ (Equiv.swap x y) z := by
  by_cases hzx : z = x
  · subst z; simpa using hy
  by_cases hzy : z = y
  · subst z; simpa using hx
  simpa only [Equiv.swap_apply_of_ne_of_ne hzx hzy] using hz

lemma star_probability_equal {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hwe : WeaklyExchangeable B μ)
    {a : ℕ} {J : Finset ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} (hA : MeasurableSet A) (hT : MeasurableSet T)
    {t : ℝ} {i j : ℕ} (hai : a ≤ i) (haj : a ≤ j) (hi : i ∈ J) (hj : j ∈ J) :
    μ (B ⁻¹' starSet a J A T t i) = μ (B ⁻¹' starSet a J A T t j) := by
  have h := (hwe (Equiv.swap i j) (swap_hasFiniteSupport i j)).measure_mem_eq
    (measurableSet_starSet J hA hT t i)
  change μ (B ⁻¹' starSet a J A T t i) =
    μ (B ⁻¹' (permuteArray (Equiv.swap i j) ⁻¹' starSet a J A T t i)) at h
  have hfix : ∀ x < a, (Equiv.swap i j) x = x := by
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have hJ : ∀ x, x ∈ J ↔ (Equiv.swap i j) x ∈ J := by
    intro x
    by_cases hxi : x = i
    · subst x; simp only [Equiv.swap_apply_left]; exact iff_of_true hi hj
    by_cases hxj : x = j
    · subst x; simp only [Equiv.swap_apply_right]; exact iff_of_true hj hi
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  rw [starSet_permute hfix hJ, Equiv.swap_apply_left] at h
  exact h

lemma duplicate_probability_swap {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hwe : WeaklyExchangeable B μ)
    {a : ℕ} {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ) (i j : ℕ)
    {x y : ℕ} (hx : a ≤ x) (hy : a ≤ y) :
    μ (B ⁻¹' duplicateSet a A T t i j) =
      μ (B ⁻¹' duplicateSet a A T t ((Equiv.swap x y) i) ((Equiv.swap x y) j)) := by
  have h := (hwe (Equiv.swap x y) (swap_hasFiniteSupport x y)).measure_mem_eq
    (measurableSet_duplicateSet hA hT t i j)
  change μ (B ⁻¹' duplicateSet a A T t i j) =
    μ (B ⁻¹' (permuteArray (Equiv.swap x y) ⁻¹' duplicateSet a A T t i j)) at h
  rwa [duplicateSet_permute (by
    intro z hz
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega))] at h

lemma duplicate_probability_equal {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hwe : WeaklyExchangeable B μ)
    {a : ℕ} {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ)
    {i j : ℕ} (hi : a ≤ i) (hj : a ≤ j) (hij : i ≠ j) :
    μ (B ⁻¹' duplicateSet a A T t a (a+1)) = μ (B ⁻¹' duplicateSet a A T t i j) := by
  let k := (Equiv.swap a i) (a+1)
  have hk : a ≤ k := swap_preserves_ge (le_refl a) hi (by omega)
  have hki : k ≠ i := by
    have hh : (Equiv.swap a i) (a+1) ≠ (Equiv.swap a i) a :=
      (Equiv.swap a i).injective.ne (by omega)
    simpa only [Equiv.swap_apply_left] using hh
  have h₁ := duplicate_probability_swap hwe hA hT t a (a+1) (le_refl a) hi
  have h₂ := duplicate_probability_swap hwe hA hT t i k hk hj
  rw [Equiv.swap_apply_of_ne_of_ne hki.symm hij, Equiv.swap_apply_left] at h₂
  rw [Equiv.swap_apply_left] at h₁
  exact h₁.trans h₂

lemma no_duplicate_star_cap {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hwe : WeaklyExchangeable B μ)
    {a : ℕ} {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ)
    (hdup : μ (B ⁻¹' duplicateSet a A T t a (a+1)) = 0) (k : ℕ) :
    (k+1 : ℝ) * μ.real (B ⁻¹' starSet a (Finset.Ico a (a+k+1)) A T t a) ≤ 1 := by
  let J := Finset.Ico a (a+k+1)
  let s : Fin (k+1) → Set Ω := fun i => B ⁻¹' starSet a J A T t (a+i)
  have hmem : ∀ i : Fin (k+1), a+i ∈ J := by
    intro i
    simp only [J, Finset.mem_Ico]
    constructor <;> omega
  apply equal_probability_aedisjoint_cap (μ := μ) (s := s)
  · intro i
    exact (measurableSet_starSet J hA hT t (a+i)).preimage hm
  · intro i j hij
    have hnull : μ (B ⁻¹' duplicateSet a A T t (a+i) (a+j)) = 0 := by
      rw [← duplicate_probability_equal hwe hA hT t (by omega) (by omega)
        (by intro h; apply hij; apply Fin.ext; omega), hdup]
    change μ (s i ∩ s j) = 0
    apply measure_mono_null (t := B ⁻¹' duplicateSet a A T t (a+i) (a+j)) ?_ hnull
    intro ω hω
    exact ⟨hω.1.1, hω.1.2.1, hω.2.2.1,
      hω.1.2.2 (a+j) (hmem j) (by intro h; apply hij; apply Fin.ext; omega)⟩
  · intro i
    apply congrArg ENNReal.toReal
    exact star_probability_equal hwe hA hT (by omega) (le_refl a) (hmem i)
      (by simp only [J, Finset.mem_Ico]; constructor <;> omega)

 
def extendArrayBlock (n : ℕ) (b : Fin n → Fin n → ℝ) : RealArray :=
  fun i j => if hi : i < n then if hj : j < n then b ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

lemma measurable_extendArrayBlock (n : ℕ) : Measurable (extendArrayBlock n) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  by_cases hi : i < n
  · by_cases hj : j < n
    · simpa only [extendArrayBlock, dite_eq_left hi, dite_eq_left hj, Function.comp_def] using
        ((measurable_pi_apply (⟨j,hj⟩ : Fin n)).comp (measurable_pi_apply (⟨i,hi⟩ : Fin n)))
    · simp only [extendArrayBlock, dite_eq_left hi, dite_eq_right hj]; exact measurable_const
  · simp only [extendArrayBlock, dite_eq_right hi]; exact measurable_const

lemma starSet_dependsOn {Ω : Type*} {B : Ω → RealArray} {ω : Ω}
    {n a : ℕ} {J : Finset ℕ} {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    {t : ℝ} {i : ℕ} (han : a ≤ n) (hin : i < n) (hJ : ∀ j ∈ J, j < n) :
    extendArrayBlock n (arrayBlock B n ω) ∈ starSet a J A T t i ↔
      B ω ∈ starSet a J A T t i := by
  have he : ∀ x y, x < n → y < n →
      extendArrayBlock n (arrayBlock B n ω) x y = B ω x y := by
    intro x y hx hy
    simp only [extendArrayBlock, dite_eq_left hx, dite_eq_left hy, arrayBlock]
  have hA : (fun x y : Fin a => extendArrayBlock n (arrayBlock B n ω) x y) =
      fun x y : Fin a => B ω x y := by
    funext x y
    exact he x y (x.isLt.trans_le han) (y.isLt.trans_le han)
  have hT : (fun x : Fin a => extendArrayBlock n (arrayBlock B n ω) x i) =
      fun x : Fin a => B ω x i := by
    funext x
    exact he x i (x.isLt.trans_le han) hin
  change (_ ∈ A ∧ _ ∈ T ∧ _) ↔ (_ ∈ A ∧ _ ∈ T ∧ _)
  rw [hA, hT]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply forall_congr'; intro j
  apply forall_congr'; intro hj
  rw [he i j hin (hJ j hj)]

lemma starSet_chain_succ {a k : ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} {t : ℝ} :
    starSet a (Finset.Ico a (a+(k+1)+1)) A T t a =
      starSet a (Finset.Ico a (a+k+1)) A T t a ∩ {b | b a (a+k+1) < t} := by
  ext b
  constructor
  · rintro ⟨ha, ht, hs⟩
    refine ⟨⟨ha, ht, fun j hj hja => hs j ?_ hja⟩, hs (a+k+1) ?_ (by omega)⟩
    · simp only [Finset.mem_Ico] at hj ⊢; omega
    · simp only [Finset.mem_Ico]; omega
  · rintro ⟨⟨ha, ht, hs⟩, hn⟩
    refine ⟨ha, ht, ?_⟩
    intro j hj hja
    by_cases hjn : j = a+k+1
    · change b a (a+k+1) < t at hn
      simpa only [hjn] using hn
    · apply hs j _ hja
      simp only [Finset.mem_Ico] at hj ⊢; omega

lemma gg_star_chain_recurrence {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hsym : ∀ ω i j, B ω i j = B ω j i) (hGG : HasGhirlandaGuerra B μ)
    {a : ℕ} (ha : 0 < a) {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ)
    (hTlow : ∀ v ∈ T, ∀ i, v i < t) (k : ℕ) :
    μ.real (B ⁻¹' starSet a (Finset.Ico a (a+(k+1)+1)) A T t a) =
      μ.real (B ⁻¹' starSet a (Finset.Ico a (a+k+1)) A T t a) *
        ((a+1 : ℕ) + (k : ℝ) - (1 - μ.real {ω | B ω 0 1 < t})) /
        ((a+1 : ℕ) + (k : ℝ)) := by
  classical
  let n := a+k+1
  let J := Finset.Ico a n
  let C : Set Ω := B ⁻¹' starSet a J A T t a
  let F : Set (Fin n → Fin n → ℝ) := extendArrayBlock n ⁻¹' starSet a J A T t a
  let i : Fin n := ⟨a, by dsimp [n]; omega⟩
  have hF : MeasurableSet F :=
    (measurableSet_starSet J hA hT t a).preimage (measurable_extendArrayBlock n)
  have hC : arrayBlock B n ⁻¹' F = C := by
    ext ω
    exact starSet_dependsOn (by dsimp [n]; omega) (by dsimp [n]; omega)
      (by intro j hj; exact (Finset.mem_Ico.mp hj).2)
  have h := hGG n (by dsimp [n]; omega) i F hF (Set.Iio t) measurableSet_Iio
  rw [hC] at h
  have hevent : ∀ j ∈ Finset.univ.erase i,
      C ∩ {ω | B ω i j ∈ Set.Iio t} = C := by
    intro j hj
    apply Set.inter_eq_left.mpr
    intro ω hω
    have hji : j.val ≠ a := by
      intro he
      exact (Finset.mem_erase.mp hj).1 (Fin.ext he)
    change B ω a j.val < t
    by_cases hja : j.val < a
    · rw [hsym ω a j.val]
      exact hTlow _ hω.2.1 ⟨j.val,hja⟩
    · exact hω.2.2 j.val (Finset.mem_Ico.mpr ⟨by omega, j.isLt⟩) hji
  have hsum : (∑ j ∈ Finset.univ.erase i, μ.real (C ∩ {ω | B ω i j ∈ Set.Iio t})) =
      (n-1 : ℝ) * μ.real C := by
    calc
      _ = ∑ _j ∈ Finset.univ.erase i, μ.real C :=
        Finset.sum_congr rfl (fun j hj => congrArg μ.real (hevent j hj))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Nat.cast_sub (by dsimp [n]; omega : 1 ≤ n), Nat.cast_one]
  rw [hsum] at h
  rw [starSet_chain_succ, Set.preimage_inter]
  change μ.real (C ∩ {ω | B ω a n < t}) = _
  change μ.real (C ∩ {ω | B ω a n < t}) = _ at h
  rw [h]
  dsimp [C, J, n]
  simp only [Set.mem_Iio]
  push_cast
  ring

lemma low_pair_probability_equal {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hwe : WeaklyExchangeable B μ)
    {a : ℕ} (ha : 0 < a) (t : ℝ) :
    μ {ω | B ω 0 1 < t} = μ {ω | B ω 0 a < t} := by
  have h := (hwe (Equiv.swap 1 a) (swap_hasFiniteSupport 1 a)).measure_mem_eq
    (measurableSet_lt (by fun_prop : Measurable (fun b : RealArray => b 0 1))
      (measurable_const (a := t)))
  have hz : (Equiv.swap 1 a) 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  simpa only [Set.preimage_ofPred_eq, permuteArray, hz, Equiv.swap_apply_left] using h

lemma starSet_base (a : ℕ) (A : Set (Fin a → Fin a → ℝ)) (T : Set (Fin a → ℝ)) (t : ℝ) :
    starSet a (Finset.Ico a (a+1)) A T t a =
      {b | (fun x y : Fin a => b x y) ∈ A ∧ (fun x : Fin a => b x a) ∈ T} := by
  ext b
  constructor
  · intro h; exact ⟨h.1, h.2.1⟩
  · rintro ⟨hA, hT⟩
    refine ⟨hA, hT, ?_⟩
    intro j hj hjne
    simp only [Finset.mem_Ico] at hj
    omega

 

theorem gg_duplication_positive {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {a : ℕ} (ha : 0 < a) {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ)
    (hTlow : ∀ v ∈ T, ∀ i, v i < t)
    (hpos : 0 < μ.real (B ⁻¹' starSet a (Finset.Ico a (a+1)) A T t a)) :
    0 < μ.real (B ⁻¹' duplicateSet a A T t a (a+1)) := by
  by_contra hn
  have hzero : μ (B ⁻¹' duplicateSet a A T t a (a+1)) = 0 := by
    apply (measureReal_eq_zero_iff (μ := μ)).mp
    exact le_antisymm (not_lt.mp hn) measureReal_nonneg
  have hp : 0 < μ.real {ω | B ω 0 1 < t} := by
    have he := congrArg ENNReal.toReal (low_pair_probability_equal hwe ha t)
    change μ.real {ω | B ω 0 1 < t} = μ.real {ω | B ω 0 a < t} at he
    rw [he]
    exact hpos.trans_le (measureReal_mono (μ := μ) (fun ω hω => hTlow _ hω.2.1 ⟨0,ha⟩))
  apply polya_no_linear_cap (n := a+1) (b := 1 - μ.real {ω | B ω 0 1 < t})
    (r := fun k => μ.real (B ⁻¹' starSet a (Finset.Ico a (a+k+1)) A T t a))
    (by omega) (by linarith) (fun _ => measureReal_nonneg)
    (by simpa only [Nat.add_zero] using hpos)
  · exact gg_star_chain_recurrence hsym hGG ha hA hT t hTlow
  · exact no_duplicate_star_cap hm hwe hA hT t hzero

 
def blockLaw {Ω : Type*} [MeasurableSpace Ω] (B : Ω → RealArray)
    (μ : Measure Ω) (n : ℕ) : Measure (Fin n → Fin n → ℝ) :=
  Measure.map (arrayBlock B n) μ

lemma measurable_arrayBlock {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} (hm : Measurable B) (n : ℕ) :
    Measurable (arrayBlock B n) := by
  unfold arrayBlock
  fun_prop

lemma blockLaw_support_compact {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hm : Measurable B) {D : ℝ}
    (hb : ∀ ω i j, |B ω i j| ≤ D) (n : ℕ) :
    IsCompact (blockLaw B μ n).support := by
  apply (isCompact_Icc (a := fun _ _ : Fin n => -D)
    (b := fun _ _ : Fin n => D)).of_isClosed_subset Measure.isClosed_support
  apply Measure.support_subset_of_isClosed isClosed_Icc
  rw [mem_ae_iff]
  rw [blockLaw, Measure.map_apply (measurable_arrayBlock hm n) isClosed_Icc.isOpen_compl.measurableSet]
  have he : arrayBlock B n ⁻¹' (Set.Icc (fun _ _ : Fin n => -D) (fun _ _ : Fin n => D))ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    apply hω
    constructor
    · intro i j; exact (abs_le.mp (hb ω i j)).1
    · intro i j; exact (abs_le.mp (hb ω i j)).2
  rw [he, measure_empty]

 

theorem gg_duplicate_supported_last {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    {a : ℕ} (ha : 0 < a) {A : Fin (a+1) → Fin (a+1) → ℝ}
    (hA : A ∈ (blockLaw B μ (a+1)).support) {t : ℝ}
    (ht : ∀ i : Fin a, A i.castSucc (Fin.last a) ≤ t) :
    ∃ C ∈ (blockLaw B μ (a+2)).support,
      (∀ i j : Fin a, C i.castSucc.castSucc j.castSucc.castSucc = A i.castSucc j.castSucc) ∧
      (∀ i : Fin a, C i.castSucc.castSucc (Fin.last a).castSucc = A i.castSucc (Fin.last a)) ∧
      (∀ i : Fin a, C i.castSucc.castSucc (Fin.last (a+1)) = A i.castSucc (Fin.last a)) ∧
      C (Fin.last a).castSucc (Fin.last (a+1)) ≤ t := by
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ C ∈ (blockLaw B μ (a+2)).support,
      (∀ i j : Fin a, |C i.castSucc.castSucc j.castSucc.castSucc - A i.castSucc j.castSucc| < ε) ∧
      (∀ i : Fin a, |C i.castSucc.castSucc (Fin.last a).castSucc - A i.castSucc (Fin.last a)| < ε) ∧
      (∀ i : Fin a, |C i.castSucc.castSucc (Fin.last (a+1)) - A i.castSucc (Fin.last a)| < ε) ∧
      C (Fin.last a).castSucc (Fin.last (a+1)) < t+ε := by
    intro ε hε
    let F : Set (Fin a → Fin a → ℝ) :=
      {c | ∀ i j, |c i j - A i.castSucc j.castSucc| < ε}
    let T : Set (Fin a → ℝ) :=
      {c | ∀ i, |c i - A i.castSucc (Fin.last a)| < ε}
    have hF : MeasurableSet F := by
      dsimp [F]; simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => measurableSet_lt (by fun_prop) measurable_const
    have hT : MeasurableSet T := by
      dsimp [T]; simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) measurable_const
    have hball := (Measure.mem_support_iff_forall A).mp hA
      (Metric.ball A ε) (Metric.ball_mem_nhds A hε)
    rw [blockLaw, Measure.map_apply (measurable_arrayBlock hm (a+1)) Metric.isOpen_ball.measurableSet] at hball
    have hpos : 0 < μ.real (B ⁻¹' starSet a (Finset.Ico a (a+1)) F T (t+ε) a) := by
      have hsub : arrayBlock B (a+1) ⁻¹' Metric.ball A ε ⊆
          B ⁻¹' starSet a (Finset.Ico a (a+1)) F T (t+ε) a := by
        intro ω hω
        rw [starSet_base]
        have hc := (dist_pi_lt_iff hε).mp hω
        constructor
        · intro i j
          exact (dist_pi_lt_iff hε).mp (hc i.castSucc) j.castSucc
        · intro i
          exact (dist_pi_lt_iff hε).mp (hc i.castSucc) (Fin.last a)
      exact ENNReal.toReal_pos (ne_of_gt (hball.trans_le (measure_mono hsub))) (measure_ne_top _ _)
    have hd := gg_duplication_positive hm hsym hwe hGG ha hF hT (t+ε)
      (by intro v hv i; have hi := (abs_lt.mp (hv i)).2; have := ht i; linarith) hpos
    let E : Set (Fin (a+2) → Fin (a+2) → ℝ) := {c |
      (∀ i j : Fin a, |c i.castSucc.castSucc j.castSucc.castSucc - A i.castSucc j.castSucc| < ε) ∧
      (∀ i : Fin a, |c i.castSucc.castSucc (Fin.last a).castSucc - A i.castSucc (Fin.last a)| < ε) ∧
      (∀ i : Fin a, |c i.castSucc.castSucc (Fin.last (a+1)) - A i.castSucc (Fin.last a)| < ε) ∧
      c (Fin.last a).castSucc (Fin.last (a+1)) < t+ε}
    have hE : MeasurableSet E := by
      change MeasurableSet ({c : Fin (a+2) → Fin (a+2) → ℝ | ∀ i j : Fin a, |c i.castSucc.castSucc j.castSucc.castSucc - A i.castSucc j.castSucc| < ε} ∩
        ({c | ∀ i : Fin a, |c i.castSucc.castSucc (Fin.last a).castSucc - A i.castSucc (Fin.last a)| < ε} ∩
        ({c | ∀ i : Fin a, |c i.castSucc.castSucc (Fin.last (a+1)) - A i.castSucc (Fin.last a)| < ε} ∩
        {c | c (Fin.last a).castSucc (Fin.last (a+1)) < t+ε})))
      refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
      · simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => measurableSet_lt (by fun_prop) measurable_const
      · simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) measurable_const
      · simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) measurable_const
      · exact measurableSet_lt (by fun_prop) measurable_const
    have hEp : 0 < (blockLaw B μ (a+2)) E := by
      rw [blockLaw, Measure.map_apply (measurable_arrayBlock hm (a+2)) hE]
      exact ENNReal.toReal_pos_iff.mp hd |>.1
    obtain ⟨C, hCE, hCs⟩ := Measure.nonempty_inter_support_of_pos hEp
    exact ⟨C, hCs, hCE⟩
  choose C hCs hC using fun k : ℕ => happrox (1 / (k+1)) (by positivity)
  obtain ⟨L, hLs, φ, hφ, hlim⟩ := (blockLaw_support_compact hm hb (a+2)).tendsto_subseq hCs
  have hzero : Tendsto (fun k => 1 / ((φ k : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hentry : ∀ i j, Tendsto (fun k => C (φ k) i j) atTop (𝓝 (L i j)) := by
    intro i j
    exact ((continuous_apply j).comp (continuous_apply i)).continuousAt.tendsto.comp hlim
  have heq : ∀ (i j : Fin (a+2)) (v : ℝ),
      (∀ k, |C k i j-v| < 1/((k:ℝ)+1)) → L i j = v := by
    intro i j v hv
    have hl := ((hentry i j).sub (tendsto_const_nhds (x := v))).abs
    have hg : |L i j-v| ≤ 0 := le_of_tendsto_of_tendsto hl hzero
      (Filter.Eventually.of_forall fun k => (hv (φ k)).le)
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hg (abs_nonneg _)))
  refine ⟨L, hLs, ?_, ?_, ?_, ?_⟩
  · intro i j; exact heq _ _ _ (fun k => (hC k).1 i j)
  · intro i; exact heq _ _ _ (fun k => (hC k).2.1 i)
  · intro i; exact heq _ _ _ (fun k => (hC k).2.2.1 i)
  · have htlim := tendsto_const_nhds.add hzero (a := t)
    simp only [add_zero] at htlim
    exact le_of_tendsto_of_tendsto (hentry _ _) htlim
      (Filter.Eventually.of_forall fun k => (hC (φ k)).2.2.2.le)

lemma support_mem_of_continuous_invariant {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : Continuous f) (hi : ∀ s, MeasurableSet s → μ (f ⁻¹' s) = μ s)
    {x : X} (hx : x ∈ μ.support) : f x ∈ μ.support := by
  apply (Measure.mem_support_iff_forall _).mpr
  intro U hU
  obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hU
  have hp := (Measure.mem_support_iff_forall x).mp hx _
    (hf.continuousAt.preimage_mem_nhds (hVo.mem_nhds hxV))
  rw [hi V hVo.measurableSet] at hp
  exact hp.trans_le (measure_mono hVU)

lemma blockLaw_support_swap {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω}
    (hm : Measurable B) (hwe : WeaklyExchangeable B μ)
    {n : ℕ} {A : Fin n → Fin n → ℝ} (hA : A ∈ (blockLaw B μ n).support)
    (i j : Fin n) :
    (fun x y => A ((Equiv.swap i j) x) ((Equiv.swap i j) y)) ∈
      (blockLaw B μ n).support := by
  have hcoe : ∀ x : Fin n, ((Equiv.swap i j) x).val = (Equiv.swap i.val j.val) x.val := by
    intro x
    by_cases hxi : x = i
    · subst x; simp
    by_cases hxj : x = j
    · subst x; simp
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxj,
      Equiv.swap_apply_of_ne_of_ne (fun h => hxi (Fin.ext h)) (fun h => hxj (Fin.ext h))]
  let f : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) :=
    fun A x y => A ((Equiv.swap i j) x) ((Equiv.swap i j) y)
  have hf : Continuous f := by unfold f; fun_prop
  apply support_mem_of_continuous_invariant hf _ hA
  intro S hS
  rw [blockLaw, Measure.map_apply (measurable_arrayBlock hm n) (hS.preimage hf.measurable),
    Measure.map_apply (measurable_arrayBlock hm n) hS]
  have h := (hwe (Equiv.swap i.val j.val) (swap_hasFiniteSupport i.val j.val)).measure_mem_eq
    (s := (fun b : RealArray => arrayBlock (fun _ : Unit => b) n ()) ⁻¹' S)
    (hS.preimage (by unfold arrayBlock; fun_prop))
  convert h.symm using 2 <;> ext ω <;> simp only [Set.mem_preimage, arrayBlock, f, hcoe] <;> rfl

lemma isClosed_setOf_posSemidef (n : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} := by
  have he : {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} =
      {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, A i j = A j i} ∩ {A | ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v)} := by
    ext A
    constructor
    · intro h
      refine ⟨?_, fun v => by simpa using h.dotProduct_mulVec_nonneg v⟩
      intro i j
      have he := congrFun (congrFun h.1 i) j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using he.symm
    · rintro ⟨hs, hq⟩
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · ext i j; exact hs j i
      · intro v; simpa using hq v
  rw [he]
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (by unfold dotProduct Matrix.mulVec; fun_prop)

lemma blockLaw_support_gram {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hm : Measurable B) {D : ℝ}
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D) {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hA : A ∈ (blockLaw B μ n).support) :
    Matrix.PosSemidef A ∧ ∀ i, A i i = D := by
  have hdclosed : IsClosed {A : Fin n → Fin n → ℝ | ∀ i, A i i = D} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const
  have hc : IsClosed {A : Fin n → Fin n → ℝ | Matrix.PosSemidef A ∧ ∀ i, A i i = D} :=
    (isClosed_setOf_posSemidef n).inter hdclosed
  apply Measure.support_subset_of_isClosed hc _ hA
  rw [mem_ae_iff, blockLaw, Measure.map_apply (measurable_arrayBlock hm n) hc.isOpen_compl.measurableSet]
  have he : arrayBlock B n ⁻¹' {A : Fin n → Fin n → ℝ | Matrix.PosSemidef A ∧ ∀ i, A i i = D}ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact hω ⟨hpsd ω n, fun i => hdiag ω i⟩
  rw [he, measure_empty]

lemma real_posSemidef_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : ∀ i j, A i j = A j i := by
  intro i j
  have h := congrFun (congrFun hA.1 i) j
  simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm

 
theorem gg_duplicate_supported {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {a : ℕ} (ha : 0 < a) {A : Fin (a+1) → Fin (a+1) → ℝ}
    (hA : A ∈ (blockLaw B μ (a+1)).support) (p : Fin (a+1)) {t : ℝ}
    (ht : ∀ i, i ≠ p → A i p ≤ t) :
    ∃ C ∈ (blockLaw B μ (a+2)).support,
      (∀ i j : Fin (a+1), C i.castSucc j.castSucc = A i j) ∧
      (∀ i : Fin (a+1), i ≠ p → C i.castSucc (Fin.last (a+1)) = A i p) ∧
      C p.castSucc (Fin.last (a+1)) ≤ t := by
  let e := Equiv.swap p (Fin.last a)
  let A' : Fin (a+1) → Fin (a+1) → ℝ := fun i j => A (e i) (e j)
  have hA' : A' ∈ (blockLaw B μ (a+1)).support := blockLaw_support_swap hm hwe hA p (Fin.last a)
  have ht' : ∀ i : Fin a, A' i.castSucc (Fin.last a) ≤ t := by
    intro i
    simp only [A', e, Equiv.swap_apply_right]
    apply ht
    intro he
    have hh := congrArg e he
    simp only [e, Equiv.swap_apply_self, Equiv.swap_apply_left] at hh
    exact Fin.castSucc_ne_last i hh
  obtain ⟨C, hCs, hC0, hC1, hC2, hC3⟩ :=
    gg_duplicate_supported_last hm hsym hwe hGG hb ha hA' ht'
  have hgramA := blockLaw_support_gram hm hpsd hdiag hA
  have hgramC := blockLaw_support_gram hm hpsd hdiag hCs
  have hfull : ∀ i j : Fin (a+1), C i.castSucc j.castSucc = A' i j := by
    intro i j
    refine Fin.lastCases ?_ (fun ii => ?_) i
    · refine Fin.lastCases ?_ (fun jj => ?_) j
      · exact (hgramC.2 _).trans (hgramA.2 _).symm
      · rw [real_posSemidef_symm hgramC.1, hC1]
        exact real_posSemidef_symm hgramA.1 _ _
    · refine Fin.lastCases ?_ (fun jj => ?_) j
      · exact hC1 ii
      · exact hC0 ii jj
  let e' := Equiv.swap p.castSucc (Fin.last a).castSucc
  have hecast : ∀ i : Fin (a+1), e' i.castSucc = (e i).castSucc := by
    intro i
    by_cases hi : i = p
    · subst i; simp [e', e]
    by_cases hil : i = Fin.last a
    · subst i; simp [e', e]
    rw [show e i = i from Equiv.swap_apply_of_ne_of_ne hi hil]
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hi (Fin.castSucc_injective _ h))
      (fun h => hil (Fin.castSucc_injective _ h))
  have helast : e' (Fin.last (a+1)) = Fin.last (a+1) := by
    apply Equiv.swap_apply_of_ne_of_ne <;> exact (Fin.castSucc_ne_last _).symm
  refine ⟨fun i j => C (e' i) (e' j), blockLaw_support_swap hm hwe hCs _ _, ?_, ?_, ?_⟩
  · intro i j
    change C (e' i.castSucc) (e' j.castSucc) = _
    rw [hecast, hecast, hfull]
    simp only [A', e, Equiv.swap_apply_self]
  · intro i hip
    change C (e' i.castSucc) (e' (Fin.last (a+1))) = _
    rw [hecast, helast]
    have heil : e i ≠ Fin.last a := by
      intro he
      have he' := congrArg e he
      simp only [e, Equiv.swap_apply_self, Equiv.swap_apply_right] at he'
      exact hip he'
    obtain ⟨ii, hii⟩ := Fin.eq_castSucc_of_ne_last heil
    rw [← hii, hC2]
    dsimp [A']
    have heii : e ii.castSucc = i := by rw [hii]; exact Equiv.swap_apply_self _ _ _
    rw [heii]
    simp [e]
  · change C (e' p.castSucc) (e' (Fin.last (a+1))) ≤ _
    rw [hecast, helast]
    simpa only [e, Equiv.swap_apply_left] using hC3

lemma psd_bilinear_symm {ι : Type*} [Fintype ι] {B : Matrix ι ι ℝ}
    (hB : B.PosSemidef) (x y : ι → ℝ) :
    x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
  have hs : ∀ i j, B i j = B j i := by
    intro i j
    have h := congrFun (congrFun hB.1 i) j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hs j i]
  ring

lemma psd_cauchy_schwarz {ι : Type*} [Fintype ι] {B : Matrix ι ι ℝ}
    (hB : B.PosSemidef) (x y : ι → ℝ) :
    (x ⬝ᵥ (B *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (B *ᵥ x)) * (y ⬝ᵥ (B *ᵥ y)) := by
  have hq : ∀ t : ℝ, 0 ≤ (x ⬝ᵥ (B *ᵥ x)) * (t * t) +
      (2 * (x ⬝ᵥ (B *ᵥ y))) * t + (y ⬝ᵥ (B *ᵥ y)) := by
    intro t
    have h := hB.dotProduct_mulVec_nonneg (t • x + y)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
      dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at h
    rw [psd_bilinear_symm hB y x] at h
    nlinarith
  have h := discrim_le_zero hq
  dsimp [discrim] at h
  nlinarith

lemma psd_three_gap {B : Matrix (Fin 3) (Fin 3) ℝ} (hB : B.PosSemidef) :
    (B 0 2 - B 0 1) ^ 2 ≤ B 0 0 * (B 1 1 + B 2 2 - 2 * B 1 2) := by
  have hs : B 2 1 = B 1 2 := by
    have h := congrFun (congrFun hB.1 1) 2
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have h := psd_cauchy_schwarz hB ![1, 0, 0] ![0, -1, 1]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, hs] at h
  nlinarith

 
def groupAverageMatrix {m : ℕ} (B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (∑ a : Fin m, ∑ b : Fin m, B (i,a) (j,b)) / (m : ℝ)^2

lemma groupAverageMatrix_posSemidef {m : ℕ}
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} (hB : B.PosSemidef) :
    (groupAverageMatrix B).PosSemidef := by
  classical
  let C : Matrix (Fin 3 × Fin m) (Fin 3) ℝ := fun a i => if a.1 = i then (m : ℝ)⁻¹ else 0
  have h := hB.conjTranspose_mul_mul_same C
  have heq : C.conjTranspose * B * C = groupAverageMatrix B := by
    ext i j
    change (∑ a : Fin 3 × Fin m, (∑ b : Fin 3 × Fin m, C b i * B b a) * C a j) = _
    simp only [C, Fintype.sum_prod_type, ite_mul, zero_mul, mul_ite, mul_zero]
    simp only [Finset.sum_mul]
    dsimp [groupAverageMatrix]
    rw [Finset.sum_comm]
    simp [div_eq_mul_inv, pow_two, mul_assoc, mul_comm]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rwa [heq] at h

lemma groupAverageMatrix_cross {m : ℕ} (hm : 0 < m)
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} {i j : Fin 3} {q : ℝ}
    (h : ∀ a b, B (i,a) (j,b) = q) : groupAverageMatrix B i j = q := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp [groupAverageMatrix, h, pow_two]
  field_simp

lemma groupAverageMatrix_diag_le {m : ℕ} (hm : 0 < m)
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} {i : Fin 3} {D q : ℝ}
    (hd : ∀ a, B (i,a) (i,a) = D)
    (ho : ∀ a b, a ≠ b → B (i,a) (i,b) ≤ q) :
    groupAverageMatrix B i i ≤ D / m + (1 - 1 / (m : ℝ)) * q := by
  classical
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr : ∀ a, ∑ b : Fin m, B (i,a) (i,b) ≤ D + (m - 1 : ℝ) * q := by
    intro a
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a), hd a]
    have h := Finset.sum_le_sum (s := Finset.univ.erase a)
      (f := fun b => B (i,a) (i,b)) (g := fun _ => q)
      (fun b hb => ho a b (Ne.symm (Finset.mem_erase.mp hb).1))
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at h
    linarith
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hr a)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  dsimp [groupAverageMatrix]
  apply (div_le_iff₀ (sq_pos_of_pos hm')).mpr
  calc
    _ ≤ m * (D + (m - 1 : ℝ) * q) := h
    _ = _ := by field_simp

lemma psd_entry_le_diagonal {ι : Type*} [Fintype ι] {B : Matrix ι ι ℝ}
    (hB : B.PosSemidef) {D : ℝ} (hd : ∀ i, B i i = D) (i j : ι) : B i j ≤ D := by
  classical
  have hD : 0 ≤ D := hd i ▸ hB.diag_nonneg
  have h := psd_cauchy_schwarz hB (Pi.single i 1) (Pi.single j 1)
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, ite_mul, mul_ite, hd] at h
  nlinarith [sq_nonneg (B i j - D)]

lemma groupAverageMatrix_diag_le_common {m : ℕ} (hm : 0 < m)
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} {D : ℝ}
    (hB : B.PosSemidef) (hd : ∀ a, B a a = D) (i : Fin 3) :
    groupAverageMatrix B i i ≤ D := by
  have h := groupAverageMatrix_diag_le hm (fun a => hd (i,a))
    (fun a b _ => psd_entry_le_diagonal hB hd (i,a) (i,b))
  have hD : D / (m : ℝ) + (1 - 1 / (m : ℝ)) * D = D := by ring
  rwa [hD] at h

 
lemma duplicated_triple_gap_bound {m : ℕ} (hm : 0 < m)
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} {D a b c : ℝ}
    (hB : B.PosSemidef) (hd : ∀ i, B i i = D)
    (hab : ∀ i j, B (0,i) (1,j) = a)
    (hac : ∀ i j, B (0,i) (2,j) = b)
    (hbc : ∀ i j, B (1,i) (2,j) = c)
    (h22 : ∀ i j, i ≠ j → B (1,i) (1,j) ≤ c)
    (h33 : ∀ i j, i ≠ j → B (2,i) (2,j) ≤ c) :
    (b - a)^2 ≤ 2 * D * (D - c) / m := by
  have hG := groupAverageMatrix_posSemidef hB
  have h := psd_three_gap hG
  have h00 := groupAverageMatrix_diag_le_common hm hB hd 0
  have h11 := groupAverageMatrix_diag_le hm (fun i => hd (1,i)) h22
  have h22' := groupAverageMatrix_diag_le hm (fun i => hd (2,i)) h33
  have h01 := groupAverageMatrix_cross hm hab
  have h02 := groupAverageMatrix_cross hm hac
  have h12 := groupAverageMatrix_cross hm hbc
  rw [h01, h02, h12] at h
  have hD : 0 ≤ D := (hG.diag_nonneg (i := 0)).trans h00
  have hq : 0 ≤ groupAverageMatrix B 1 1 + groupAverageMatrix B 2 2 - 2 * c := by
    have h0 := hG.dotProduct_mulVec_nonneg ![0, -1, 1]
    have hs : groupAverageMatrix B 2 1 = groupAverageMatrix B 1 2 := by
      have he := congrFun (congrFun hG.1 1) 2
      simpa only [Matrix.conjTranspose_apply, star_trivial] using he
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, hs, h12] at h0
    linarith
  calc
    (b - a)^2 ≤ groupAverageMatrix B 0 0 *
        (groupAverageMatrix B 1 1 + groupAverageMatrix B 2 2 - 2*c) := h
    _ ≤ D * (groupAverageMatrix B 1 1 + groupAverageMatrix B 2 2 - 2*c) :=
      mul_le_mul_of_nonneg_right h00 hq
    _ ≤ D * (2 * (D / m + (1 - 1 / (m : ℝ)) * c) - 2*c) :=
      mul_le_mul_of_nonneg_left (by linarith) hD
    _ = 2 * D * (D - c) / m := by ring

 

lemma no_arbitrary_nonultrametric_duplicates {D a b c : ℝ} (hab : a < b)
    (hex : ∀ m : ℕ, 0 < m → ∃ B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ,
      B.PosSemidef ∧ (∀ i, B i i = D) ∧
      (∀ i j, B (0,i) (1,j) = a) ∧ (∀ i j, B (0,i) (2,j) = b) ∧
      (∀ i j, B (1,i) (2,j) = c) ∧
      (∀ i j, i ≠ j → B (1,i) (1,j) ≤ c) ∧
      (∀ i j, i ≠ j → B (2,i) (2,j) ≤ c)) : False := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * D * (D - c) / (b-a)^2)
  obtain ⟨B, hB, hd, h01, h02, h12, h11, h22⟩ := hex (m+1) (by omega)
  have h := duplicated_triple_gap_bound (by omega : 0 < m+1) hB hd h01 h02 h12 h11 h22
  have hp : 0 < (b-a)^2 := sq_pos_of_pos (sub_pos.mpr hab)
  have hm' : (0 : ℝ) < (m+1 : ℕ) := by positivity
  have hbound := (div_lt_iff₀ hp).mp hm
  have hbig := (le_div_iff₀ hm').mp h
  simp only [Nat.cast_add, Nat.cast_one] at hbig
  nlinarith

lemma gg_duplicate_supported_of_two_le {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {n : ℕ} (hn : 2 ≤ n) {A : Fin n → Fin n → ℝ}
    (hA : A ∈ (blockLaw B μ n).support) (p : Fin n) {t : ℝ}
    (ht : ∀ i, i ≠ p → A i p ≤ t) :
    ∃ C ∈ (blockLaw B μ (n+1)).support,
      (∀ i j : Fin n, C i.castSucc j.castSucc = A i j) ∧
      (∀ i : Fin n, i ≠ p → C i.castSucc (Fin.last n) = A i p) ∧
      C p.castSucc (Fin.last n) ≤ t := by
  cases n with
  | zero => omega
  | succ a => exact gg_duplicate_supported hm hsym hwe hGG hb hpsd hdiag (by omega) hA p ht

def tripleLabel {n : ℕ} (i : Fin n) : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩

lemma tripleLabel_castSucc {n : ℕ} (i : Fin n) : tripleLabel i.castSucc = tripleLabel i := rfl

 

lemma gg_supported_populations {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {Q : Fin 3 → Fin 3 → ℝ} (hQ : Q ∈ (blockLaw B μ 3).support)
    {t : ℝ} (ht : ∀ i j, i ≠ j → Q i j ≤ t) :
    ∀ n, 3 ≤ n → ∃ A ∈ (blockLaw B μ n).support,
      (∀ i j, i ≠ j → A i j ≤ t) ∧
      (∀ i j, tripleLabel i ≠ tripleLabel j → A i j = Q (tripleLabel i) (tripleLabel j)) := by
  have hQsym := real_posSemidef_symm (blockLaw_support_gram hm hpsd hdiag hQ).1
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨Q, hQ, ht, ?_⟩
    intro i j _
    have hh : ∀ i : Fin 3, tripleLabel i = i := fun i => Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [hh, hh]
  | succ n hn ih =>
    obtain ⟨A, hAs, hAo, hAc⟩ := ih
    let p : Fin n := ⟨n % 3, (Nat.mod_lt n (by decide : 0 < 3)).trans_le hn⟩
    have hp : tripleLabel p = tripleLabel (Fin.last n) := by
      apply Fin.ext; exact Nat.mod_eq_of_lt (Nat.mod_lt n (by decide))
    obtain ⟨C, hCs, hC0, hC1, hCp⟩ := gg_duplicate_supported_of_two_le
      hm hsym hwe hGG hb hpsd hdiag (by omega) hAs p (fun i hi => hAo i p hi)
    have hCsym := real_posSemidef_symm (blockLaw_support_gram hm hpsd hdiag hCs).1
    refine ⟨C, hCs, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun ii => ?_) i
      · refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro hij; exact (hij rfl).elim
        · intro _
          rw [hCsym]
          by_cases hj : jj = p
          · subst jj; exact hCp
          · rw [hC1 jj hj]; exact hAo jj p hj
      · refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro _
          by_cases hi : ii = p
          · subst ii; exact hCp
          · rw [hC1 ii hi]; exact hAo ii p hi
        · intro hij
          rw [hC0]; exact hAo ii jj (fun he => hij (congrArg Fin.castSucc he))
    · intro i j
      refine Fin.lastCases ?_ (fun ii => ?_) i
      · refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro hij; exact (hij rfl).elim
        · intro hij
          have hjp : tripleLabel jj ≠ tripleLabel p := by
            intro he; apply hij; exact hp.symm.trans he.symm
          have hjne : jj ≠ p := fun he => hjp (congrArg tripleLabel he)
          rw [hCsym, hC1 jj hjne, hAc jj p hjp, hp, hQsym]
          rfl
      · refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro hij
          have hip : tripleLabel ii ≠ tripleLabel p := by
            intro he; apply hij; exact he.trans hp
          have hine : ii ≠ p := fun he => hip (congrArg tripleLabel he)
          rw [hC1 ii hine, hAc ii p hip, hp]
          rfl
        · intro hij
          rw [hC0]; exact hAc ii jj hij

lemma gg_supported_triple_ordered {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {Q : Fin 3 → Fin 3 → ℝ} (hQ : Q ∈ (blockLaw B μ 3).support)
    (horder : Q 0 2 ≤ Q 1 2) : Q 0 2 ≤ Q 0 1 := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hQsym := real_posSemidef_symm (blockLaw_support_gram hm hpsd hdiag hQ).1
  have hQo : ∀ i j : Fin 3, i ≠ j → Q i j ≤ Q 1 2 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hlt.le.trans horder
    · exact horder
    · exact (hQsym 1 0).le.trans (hlt.le.trans horder)
    · exact (hij rfl).elim
    · exact le_rfl
    · exact (hQsym 2 0).le.trans horder
    · exact (hQsym 2 1).le
    · exact (hij rfl).elim
  apply no_arbitrary_nonultrametric_duplicates hlt
  intro m hmpos
  obtain ⟨A, hAs, hAo, hAc⟩ := gg_supported_populations hm hsym hwe hGG hb hpsd hdiag
    hQ hQo (3*m) (by omega)
  let e : Fin 3 × Fin m → Fin (3*m) := fun x => ⟨3*x.2.val+x.1.val, by omega⟩
  have he : ∀ i a, tripleLabel (e (i,a)) = i := by
    intro i a
    apply Fin.ext
    dsimp [tripleLabel, e]
    omega
  have hei : Function.Injective e := by
    intro x y hxy
    have hv := congrArg Fin.val hxy
    dsimp [e] at hv
    apply Prod.ext <;> apply Fin.ext <;> omega
  have hgram := blockLaw_support_gram hm hpsd hdiag hAs
  refine ⟨Matrix.submatrix A e e, Matrix.PosSemidef.submatrix hgram.1 e,
    fun _ => hgram.2 _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    change A (e (0,i)) (e (1,j)) = _
    rw [hAc _ _ (by rw [he, he]; decide), he, he]
  · intro i j
    change A (e (0,i)) (e (2,j)) = _
    rw [hAc _ _ (by rw [he, he]; decide), he, he]
  · intro i j
    change A (e (1,i)) (e (2,j)) = _
    rw [hAc _ _ (by rw [he, he]; decide), he, he]
  · intro i j hij
    exact hAo _ _ (fun hh => hij (congrArg Prod.snd (hei hh)))
  · intro i j hij
    exact hAo _ _ (fun hh => hij (congrArg Prod.snd (hei hh)))

lemma array_entry_abs_le_diagonal {B : RealArray} {D : ℝ}
    (hp : ∀ n, Matrix.PosSemidef (fun i j : Fin n => B i j))
    (hd : ∀ i, B i i = D) (i j : ℕ) : |B i j| ≤ D := by
  let n := max i j + 1
  let ii : Fin n := ⟨i, by dsimp [n]; omega⟩
  let jj : Fin n := ⟨j, by dsimp [n]; omega⟩
  have hD : 0 ≤ D := (hp n).diag_nonneg (i := ii) |>.trans (hd i).le
  have hs := psd_cauchy_schwarz (hp n) (Pi.single ii 1) (Pi.single jj 1)
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, ite_mul, mul_ite, hd] at hs
  change B i j ^ 2 ≤ D * D at hs
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (B i j - D), sq_nonneg (B i j + D)]

lemma gg_supported_triple_ultrametric {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {Q : Fin 3 → Fin 3 → ℝ} (hQ : Q ∈ (blockLaw B μ 3).support) :
    min (Q 0 2) (Q 1 2) ≤ Q 0 1 := by
  have hb : ∀ ω i j, |B ω i j| ≤ D :=
    fun ω => array_entry_abs_le_diagonal (hpsd ω) (hdiag ω)
  by_cases ho : Q 0 2 ≤ Q 1 2
  · rw [min_eq_left ho]
    exact gg_supported_triple_ordered hm hsym hwe hGG hb hpsd hdiag hQ ho
  · have ho' : Q 1 2 ≤ Q 0 2 := le_of_not_ge ho
    rw [min_eq_right ho']
    have hQs := blockLaw_support_swap hm hwe hQ 0 1
    have hqsym := real_posSemidef_symm (blockLaw_support_gram hm hpsd hdiag hQ).1
    have hh : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    have h := gg_supported_triple_ordered hm hsym hwe hGG hb hpsd hdiag hQs
      (by simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right, hh] using ho')
    simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right, hh, hqsym 1 0] using h

 

theorem gg_ultrametric_triple {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D) :
    ∀ᵐ ω ∂μ, min (B ω 0 2) (B ω 1 2) ≤ B ω 0 1 := by
  have hs : ∀ᵐ A ∂blockLaw B μ 3, A ∈ (blockLaw B μ 3).support :=
    Measure.support_mem_ae
  have ht : ∀ᵐ A ∂blockLaw B μ 3, min (A 0 2) (A 1 2) ≤ A 0 1 :=
    hs.mono (fun _ h => gg_supported_triple_ultrametric hm hsym hwe hGG hpsd hdiag h)
  exact (ae_map_iff (measurable_arrayBlock hm 3).aemeasurable
    (measurableSet_le (by fun_prop) (by fun_prop))).mp ht

 
def IsUltrametricArray (b : RealArray) : Prop :=
  ∀ i j k, min (b i k) (b j k) ≤ b i j

lemma ultrametric_survival_rectangle {b : RealArray} (hs : ∀ i j, b i j = b j i)
    (hu : IsUltrametricArray b) {n : ℕ} (t : Fin n → ℝ) (k : Fin n)
    (hk : ∀ i, t i ≤ t k) :
    (∀ i : Fin n, t i ≤ b i n) ↔
      (∀ i : Fin n, t i ≤ b i k) ∧ t k ≤ b k n := by
  constructor
  · intro h
    exact ⟨fun i => (le_min (h i) ((hk i).trans (h k))).trans (hu i k n), h k⟩
  · rintro ⟨h, hkn⟩ i
    have hh := hu i n k
    rw [hs n k] at hh
    exact (le_min (h i) ((hk i).trans hkn)).trans hh

lemma measurableSet_survival_compatible {n : ℕ} (t : Fin n → ℝ) (k : Fin n) :
    MeasurableSet {b : Fin n → Fin n → ℝ | ∀ i, t i ≤ b i k} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (by fun_prop))

lemma gg_survival_extension {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hGG : HasGhirlandaGuerra B μ) (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hu : ∀ᵐ ω ∂μ, IsUltrametricArray (B ω)) {n : ℕ} (hn : 2 ≤ n)
    {A : Set (Fin n → Fin n → ℝ)} (hA : MeasurableSet A)
    (t : Fin n → ℝ) (k : Fin n) (hk : ∀ i, t i ≤ t k) :
    let A' := A ∩ {b : Fin n → Fin n → ℝ | ∀ i, t i ≤ b i k}
    μ.real ((arrayBlock B n ⁻¹' A) ∩ {ω | ∀ i : Fin n, t i ≤ B ω i n}) =
      (μ.real (arrayBlock B n ⁻¹' A') * μ.real {ω | t k ≤ B ω 0 1}) / n +
      (∑ j ∈ Finset.univ.erase k,
        μ.real ((arrayBlock B n ⁻¹' A') ∩ {ω | t k ≤ B ω k j})) / n := by
  dsimp only
  have he := hGG n hn k _ (hA.inter (measurableSet_survival_compatible t k))
    (Set.Ici (t k)) measurableSet_Ici
  simp only [Set.mem_Ici] at he
  rw [← he]
  apply measureReal_congr
  filter_upwards [hs, hu] with ω hs hu
  apply propext
  change (arrayBlock B n ω ∈ A ∧ ∀ i : Fin n, t i ≤ B ω i n) ↔
    ((arrayBlock B n ω ∈ A ∧ ∀ i : Fin n, t i ≤ B ω i k) ∧ t k ≤ B ω k n)
  rw [ultrametric_survival_rectangle hs hu t k hk]
  tauto

lemma isCountablySpanning_real_Ici :
    IsCountablySpanning (Set.range (Set.Ici : ℝ → Set ℝ)) := by
  refine ⟨fun n => Set.Ici (-(n : ℝ)), fun n => ⟨_, rfl⟩, ?_⟩
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt (-x)
  exact Set.mem_iUnion.mpr ⟨n, by change -(n : ℝ) ≤ x; linarith⟩

lemma measure_eq_of_upper_orthants {ι : Type*} [Fintype ι]
    {μ ν : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (h : ∀ t : ι → ℝ, μ {x | ∀ i, t i ≤ x i} = ν {x | ∀ i, t i ≤ x i})
    (hU : μ Set.univ = ν Set.univ) : μ = ν := by
  classical
  let C : Set (Set (ι → ℝ)) := Set.pi Set.univ '' Set.pi Set.univ
    (fun _ : ι => Set.range (Set.Ici : ℝ → Set ℝ))
  have hgen : (inferInstance : MeasurableSpace (ι → ℝ)) = MeasurableSpace.generateFrom C := by
    exact (generateFrom_eq_pi (fun _ => by
      rw [← borel_eq_generateFrom_Ici]; exact BorelSpace.measurable_eq.symm)
      (fun _ => isCountablySpanning_real_Ici)).symm
  apply ext_of_generate_finite C hgen (IsPiSystem.pi (fun _ => isPiSystem_Ici)) ?_ hU
  rintro _ ⟨s, hs, rfl⟩
  have hs' : ∀ i, ∃ t : ℝ, Set.Ici t = s i := fun i => hs i (Set.mem_univ i)
  choose t ht using hs'
  have he : Set.pi Set.univ s = {x | ∀ i, t i ≤ x i} := by
    ext x
    simp only [← ht, Set.mem_pi, Set.mem_univ, Set.mem_Ici, forall_true_left, Set.mem_ofPred_eq]
  rw [he]
  exact h t

lemma finite_permutation_extending {ι β : Type*} [Fintype ι]
    (f g : ι → β) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ e : Equiv.Perm β, {b | e b ≠ b}.Finite ∧ ∀ i, e (f i) = g i := by
  classical
  let U : Finset β := Finset.univ.image f ∪ Finset.univ.image g
  let f' : ι → U := fun i => ⟨f i, Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))⟩
  let g' : ι → U := fun i => ⟨g i, Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))⟩
  have hf' : Function.Injective f' := fun i j h => hf (congrArg Subtype.val h)
  have hg' : Function.Injective g' := fun i j h => hg (congrArg Subtype.val h)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f' g' hf' hg'
  let emb : U ↪ β := Function.Embedding.subtype _
  refine ⟨σ.viaFintypeEmbedding emb, ?_, ?_⟩
  · apply U.finite_toSet.subset
    intro b hb
    by_contra h
    apply hb
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
    rintro ⟨a, rfl⟩
    exact h a.2
  · intro i
    change σ.viaFintypeEmbedding emb (emb (f' i)) = emb (g' i)
    rw [Equiv.Perm.viaFintypeEmbedding_apply_image, hσ]

lemma gg_ultrametric {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D) :
    ∀ᵐ ω ∂μ, IsUltrametricArray (B ω) := by
  have ht := gg_ultrametric_triple hm hsym hwe hGG hpsd hdiag
  have hall : ∀ i j k, ∀ᵐ ω ∂μ, min (B ω i k) (B ω j k) ≤ B ω i j := by
    intro i j k
    by_cases hij : i = j
    · subst j
      apply ae_of_all
      intro ω
      have hb := array_entry_abs_le_diagonal (hpsd ω) (hdiag ω) i k
      simpa only [min_self, hdiag] using (le_abs_self (B ω i k)).trans hb
    by_cases hik : i = k
    · subst k
      exact ae_of_all _ (fun ω => by rw [hsym ω j i]; exact min_le_right _ _)
    by_cases hjk : j = k
    · subst k
      exact ae_of_all _ (fun ω => min_le_left _ _)
    let f : Fin 3 → ℕ := fun a => a.val
    let g : Fin 3 → ℕ := ![i,j,k]
    have hg : Function.Injective g := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [g]
    obtain ⟨e, he, hef⟩ := finite_permutation_extending f g Fin.val_injective hg
    have hh := (hwe e he).ae_mem_snd
      (t := {b : RealArray | min (b 0 2) (b 1 2) ≤ b 0 1})
      (measurableSet_le (by fun_prop) (by fun_prop)) ht
    have he0 : e 0 = i := hef 0
    have he1 : e 1 = j := hef 1
    have he2 : e 2 = k := hef 2
    simpa only [Set.mem_ofPred_eq, permuteArray, he0, he1, he2] using hh
  exact ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ae_all_iff.mpr (hall i j)))

lemma blockLaw_measureReal_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {B : Ω → RealArray} {C : Ω' → RealArray} {μ : Measure Ω} {ν : Measure Ω'}
    (hm : Measurable B) (hm' : Measurable C) {n : ℕ}
    (h : blockLaw B μ n = blockLaw C ν n)
    {A : Set (Fin n → Fin n → ℝ)} (hA : MeasurableSet A) :
    μ.real (arrayBlock B n ⁻¹' A) = ν.real (arrayBlock C n ⁻¹' A) := by
  rw [← map_measureReal_apply (measurable_arrayBlock hm n) hA,
    ← map_measureReal_apply (measurable_arrayBlock hm' n) hA]
  exact congrArg (fun η => η.real A) h

lemma gg_survival_measure_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {B : Ω → RealArray} {C : Ω' → RealArray} {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hm : Measurable B) (hm' : Measurable C)
    (hGG : HasGhirlandaGuerra B μ) (hGG' : HasGhirlandaGuerra C ν)
    (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hs' : ∀ᵐ ω ∂ν, ∀ i j, C ω i j = C ω j i)
    (hu : ∀ᵐ ω ∂μ, IsUltrametricArray (B ω))
    (hu' : ∀ᵐ ω ∂ν, IsUltrametricArray (C ω)) {n : ℕ} (hn : 2 ≤ n)
    (h : blockLaw B μ n = blockLaw C ν n)
    {A : Set (Fin n → Fin n → ℝ)} (hA : MeasurableSet A) (t : Fin n → ℝ) :
    μ ((arrayBlock B n ⁻¹' A) ∩ {ω | ∀ i : Fin n, t i ≤ B ω i n}) =
    ν ((arrayBlock C n ⁻¹' A) ∩ {ω | ∀ i : Fin n, t i ≤ C ω i n}) := by
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ t
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hk' : ∀ i, t i ≤ t k := fun i => hk i (Finset.mem_univ _)
  apply (measureReal_eq_measureReal_iff).mp
  rw [gg_survival_extension hGG hs hu hn hA t k hk',
    gg_survival_extension hGG' hs' hu' hn hA t k hk']
  have hcomp := hA.inter (measurableSet_survival_compatible t k)
  have hp := blockLaw_measureReal_eq hm hm' h
    (A := {b | t k ≤ b ⟨0, by omega⟩ ⟨1, by omega⟩})
    (measurableSet_le measurable_const (by fun_prop))
  change μ.real {ω | t k ≤ B ω 0 1} = ν.real {ω | t k ≤ C ω 0 1} at hp
  rw [blockLaw_measureReal_eq hm hm' h hcomp, hp]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  exact blockLaw_measureReal_eq hm hm' h
    (hcomp.inter (measurableSet_le measurable_const (show Measurable (fun b : Fin n → Fin n → ℝ => b k j) by fun_prop)))

lemma gg_joint_extension_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {B : Ω → RealArray} {C : Ω' → RealArray} {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hm : Measurable B) (hm' : Measurable C)
    (hGG : HasGhirlandaGuerra B μ) (hGG' : HasGhirlandaGuerra C ν)
    (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hs' : ∀ᵐ ω ∂ν, ∀ i j, C ω i j = C ω j i)
    (hu : ∀ᵐ ω ∂μ, IsUltrametricArray (B ω))
    (hu' : ∀ᵐ ω ∂ν, IsUltrametricArray (C ω)) {n : ℕ} (hn : 2 ≤ n)
    (h : blockLaw B μ n = blockLaw C ν n) :
    μ.map (fun ω => (arrayBlock B n ω, fun i : Fin n => B ω i n)) =
    ν.map (fun ω => (arrayBlock C n ω, fun i : Fin n => C ω i n)) := by
  have hbm : Measurable (fun ω => (arrayBlock B n ω, fun i : Fin n => B ω i n)) :=
    (measurable_arrayBlock hm n).prodMk (by fun_prop)
  have hcm : Measurable (fun ω => (arrayBlock C n ω, fun i : Fin n => C ω i n)) :=
    (measurable_arrayBlock hm' n).prodMk (by fun_prop)
  apply Measure.ext_prod
  intro A T hA hT
  let μA := (μ.restrict (arrayBlock B n ⁻¹' A)).map (fun ω => fun i : Fin n => B ω i n)
  let νA := (ν.restrict (arrayBlock C n ⁻¹' A)).map (fun ω => fun i : Fin n => C ω i n)
  have hr : μA = νA := by
    apply measure_eq_of_upper_orthants
    · intro t
      have ht : MeasurableSet {x : Fin n → ℝ | ∀ i, t i ≤ x i} := by
        simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (by fun_prop))
      dsimp [μA, νA]
      rw [Measure.map_apply (by fun_prop) ht, Measure.map_apply (by fun_prop) ht,
        Measure.restrict_apply ((by fun_prop : Measurable (fun ω => fun i : Fin n => B ω i n)) ht),
        Measure.restrict_apply ((by fun_prop : Measurable (fun ω => fun i : Fin n => C ω i n)) ht)]
      rw [Set.inter_comm, Set.inter_comm _ (arrayBlock C n ⁻¹' A)]
      exact gg_survival_measure_eq hm hm' hGG hGG' hs hs' hu hu' hn h hA t
    · dsimp [μA, νA]
      simp only [Measure.map_apply (by fun_prop : Measurable (fun ω => fun i : Fin n => B ω i n)) MeasurableSet.univ,
        Measure.map_apply (by fun_prop : Measurable (fun ω => fun i : Fin n => C ω i n)) MeasurableSet.univ,
        Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact (measureReal_eq_measureReal_iff).mp (blockLaw_measureReal_eq hm hm' h hA)
  have he := congrArg (fun η => η T) hr
  dsimp [μA, νA] at he
  rw [Measure.map_apply (by fun_prop) hT, Measure.map_apply (by fun_prop) hT,
    Measure.restrict_apply ((by fun_prop : Measurable (fun ω => fun i : Fin n => B ω i n)) hT),
    Measure.restrict_apply ((by fun_prop : Measurable (fun ω => fun i : Fin n => C ω i n)) hT)] at he
  rw [Measure.map_apply hbm (hA.prod hT), Measure.map_apply hcm (hA.prod hT)]
  change μ ((arrayBlock B n ⁻¹' A) ∩ ((fun ω => fun i : Fin n => B ω i n) ⁻¹' T)) =
    ν ((arrayBlock C n ⁻¹' A) ∩ ((fun ω => fun i : Fin n => C ω i n) ⁻¹' T))
  simpa only [Set.inter_comm] using he

def augmentArrayBlock (D : ℝ) (n : ℕ)
    (p : (Fin n → Fin n → ℝ) × (Fin n → ℝ)) : Fin (n+1) → Fin (n+1) → ℝ :=
  fun i j => if hi : i.val < n then
    if hj : j.val < n then p.1 ⟨i.val, hi⟩ ⟨j.val, hj⟩ else p.2 ⟨i.val, hi⟩
    else if hj : j.val < n then p.2 ⟨j.val, hj⟩ else D

lemma measurable_augmentArrayBlock (D : ℝ) (n : ℕ) : Measurable (augmentArrayBlock D n) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold augmentArrayBlock
  split_ifs <;> fun_prop

lemma augmentArrayBlock_eq {b : RealArray} (hs : ∀ i j, b i j = b j i)
    {D : ℝ} (hd : ∀ i, b i i = D) (n : ℕ) :
    augmentArrayBlock D n ((fun i j : Fin n => b i j), fun i : Fin n => b i n) =
      fun i j : Fin (n+1) => b i j := by
  funext i j
  unfold augmentArrayBlock
  split_ifs with hi hj hj
  · rfl
  · have hj' : j.val = n := by omega
    simp only [hj']
  · have hi' : i.val = n := by omega
    simp only [hi', hs n j]
  · have hi' : i.val = n := by omega
    have hj' : j.val = n := by omega
    simp only [hi', hj', hd]

lemma gg_next_blockLaw_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {B : Ω → RealArray} {C : Ω' → RealArray} {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hm : Measurable B) (hm' : Measurable C)
    (hGG : HasGhirlandaGuerra B μ) (hGG' : HasGhirlandaGuerra C ν)
    (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hs' : ∀ᵐ ω ∂ν, ∀ i j, C ω i j = C ω j i)
    (hu : ∀ᵐ ω ∂μ, IsUltrametricArray (B ω))
    (hu' : ∀ᵐ ω ∂ν, IsUltrametricArray (C ω)) {D : ℝ}
    (hd : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D) (hd' : ∀ᵐ ω ∂ν, ∀ i, C ω i i = D)
    {n : ℕ} (hn : 2 ≤ n) (h : blockLaw B μ n = blockLaw C ν n) :
    blockLaw B μ (n+1) = blockLaw C ν (n+1) := by
  have he := congrArg (Measure.map (augmentArrayBlock D n))
    (gg_joint_extension_law hm hm' hGG hGG' hs hs' hu hu' hn h)
  rw [Measure.map_map (measurable_augmentArrayBlock D n) (by
      exact (measurable_arrayBlock hm n).prodMk (by fun_prop)),
    Measure.map_map (measurable_augmentArrayBlock D n) (by
      exact (measurable_arrayBlock hm' n).prodMk (by fun_prop))] at he
  have hB : (fun ω => augmentArrayBlock D n (arrayBlock B n ω, fun i : Fin n => B ω i n)) =ᵐ[μ]
      arrayBlock B (n+1) := by
    filter_upwards [hs, hd] with ω hs hd
    exact augmentArrayBlock_eq hs hd n
  have hC : (fun ω => augmentArrayBlock D n (arrayBlock C n ω, fun i : Fin n => C ω i n)) =ᵐ[ν]
      arrayBlock C (n+1) := by
    filter_upwards [hs', hd'] with ω hs hd
    exact augmentArrayBlock_eq hs hd n
  exact (Measure.map_congr hB).symm.trans (he.trans (Measure.map_congr hC))

lemma blockLaw_two_eq_pair_map {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hm : Measurable B) {D : ℝ}
    (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hd : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D) :
    blockLaw B μ 2 = (μ.map (fun ω => B ω 0 1)).map
      (fun r => fun i j : Fin 2 => if i = j then D else r) := by
  rw [Measure.map_map (by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    split_ifs <;> fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [hs, hd] with ω hs hd
  funext i j
  fin_cases i <;> fin_cases j <;> simp [arrayBlock, hs, hd]

lemma blockLaw_restrict {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hm : Measurable B) {m n : ℕ} (hmn : m ≤ n) :
    (blockLaw B μ n).map (fun b => fun i j : Fin m => b (Fin.castLE hmn i) (Fin.castLE hmn j)) =
      blockLaw B μ m := by
  unfold blockLaw
  rw [Measure.map_map (by fun_prop) (measurable_arrayBlock hm n)]
  rfl

 

theorem gg_blockLaw_unique {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {B : Ω → RealArray} {C : Ω' → RealArray} {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hm : Measurable B) (hm' : Measurable C)
    (hGG : HasGhirlandaGuerra B μ) (hGG' : HasGhirlandaGuerra C ν)
    (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hs' : ∀ᵐ ω ∂ν, ∀ i j, C ω i j = C ω j i)
    (hu : ∀ᵐ ω ∂μ, IsUltrametricArray (B ω))
    (hu' : ∀ᵐ ω ∂ν, IsUltrametricArray (C ω)) {D : ℝ}
    (hd : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D) (hd' : ∀ᵐ ω ∂ν, ∀ i, C ω i i = D)
    (hp : μ.map (fun ω => B ω 0 1) = ν.map (fun ω => C ω 0 1)) :
    ∀ n, blockLaw B μ n = blockLaw C ν n := by
  have h2 : blockLaw B μ 2 = blockLaw C ν 2 := by
    rw [blockLaw_two_eq_pair_map hm hs hd, blockLaw_two_eq_pair_map hm' hs' hd', hp]
  have hind : ∀ n, 2 ≤ n → blockLaw B μ n = blockLaw C ν n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact h2
    | succ n hn ih => exact gg_next_blockLaw_eq hm hm' hGG hGG' hs hs' hu hu' hd hd' hn ih
  intro n
  by_cases hn : 2 ≤ n
  · exact hind n hn
  · have hn' : n ≤ 2 := by omega
    rw [← blockLaw_restrict hm hn', ← blockLaw_restrict hm' hn', h2]

 
lemma HasEntryGhirlandaGuerra.map {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] {B : Ω → ℕ → ℕ → E} {μ : Measure Ω}
    (h : HasEntryGhirlandaGuerra B μ) {f : E → F} (hf : Measurable f) :
    HasEntryGhirlandaGuerra (fun ω i j => f (B ω i j)) μ := by
  intro n hn i A hA t ht
  exact h n hn i ((fun b j k => f (b j k)) ⁻¹' A)
    (hA.preimage (by fun_prop)) (f ⁻¹' t) (ht.preimage hf)

lemma HasEntryGhirlandaGuerra.real_map {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {B : Ω → ℕ → ℕ → E} {μ : Measure Ω}
    (h : HasEntryGhirlandaGuerra B μ) {f : E → ℝ} (hf : Measurable f) :
    HasGhirlandaGuerra (fun ω i j => f (B ω i j)) μ := h.map hf

lemma gg_two_links_positive {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {B : Ω → ℕ → ℕ → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hGG : HasEntryGhirlandaGuerra B μ) {A C : Set E}
    (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hpA : 0 < μ.real {ω | B ω 0 1 ∈ A}) (hpC : 0 < μ.real {ω | B ω 0 1 ∈ C}) :
    0 < μ.real ({ω | B ω 0 1 ∈ A} ∩ {ω | B ω 0 2 ∈ C}) := by
  have h := hGG 2 (by omega) 0 {b : Fin 2 → Fin 2 → E | b 0 1 ∈ A}
    (hA.preimage (by fun_prop)) C hC
  change μ.real ({ω | B ω 0 1 ∈ A} ∩ {ω | B ω 0 2 ∈ C}) = _ at h
  rw [h]
  exact add_pos_of_pos_of_nonneg (div_pos (mul_pos hpA hpC) (by norm_num))
    (div_nonneg (Finset.sum_nonneg (fun _ _ => measureReal_nonneg)) (by norm_num))

lemma ultrametric_no_crossing {r t : RealArray}
    (hr : IsUltrametricArray r) (ht : IsUltrametricArray t)
    (hs : IsUltrametricArray (fun i j => r i j + t i j))
    (hrsym : ∀ i j, r i j = r j i) (htsym : ∀ i j, t i j = t j i) :
    ¬ (r 0 1 < r 0 2 ∧ t 0 2 < t 0 1) := by
  rintro ⟨hR, hT⟩
  have hr23 : r 1 2 = r 0 1 := by
    have h1 := hr 0 1 2
    have h2 := hr 1 2 0
    rw [hrsym 1 0, hrsym 2 0, min_eq_left hR.le] at h2
    have : r 1 2 ≤ r 0 1 := by
      by_contra! hn
      exact (lt_min hR hn).not_ge h1
    exact le_antisymm this h2
  have ht23 : t 1 2 = t 0 2 := by
    have h1 := ht 0 2 1
    have h2 := ht 1 2 0
    rw [htsym 2 1] at h1
    rw [htsym 1 0, htsym 2 0, min_eq_right hT.le] at h2
    have : t 1 2 ≤ t 0 2 := by
      by_contra! hn
      exact (lt_min hT hn).not_ge h1
    exact le_antisymm this h2
  have hh := hs 1 2 0
  simp only [hrsym 1 0, hrsym 2 0, htsym 1 0, htsym 2 0, hr23, ht23] at hh
  exact (lt_min (by linarith) (by linarith)).not_ge hh

 

theorem jointGG_support_ordered {Ω : Type*} [MeasurableSpace Ω]
    {R T : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hR : Measurable R) (hT : Measurable T)
    (hGG : HasEntryGhirlandaGuerra (fun ω i j => (R ω i j, T ω i j)) μ)
    (huR : ∀ᵐ ω ∂μ, IsUltrametricArray (R ω))
    (huT : ∀ᵐ ω ∂μ, IsUltrametricArray (T ω))
    (huS : ∀ᵐ ω ∂μ, IsUltrametricArray (fun i j => R ω i j + T ω i j))
    (hsR : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hsT : ∀ᵐ ω ∂μ, ∀ i j, T ω i j = T ω j i) :
    let ν := μ.map (fun ω => (R ω 0 1, T ω 0 1))
    ∀ x ∈ ν.support, ∀ y ∈ ν.support, x.1 < y.1 → x.2 ≤ y.2 := by
  dsimp only
  intro x hx y hy hxy
  by_contra! hc
  let a := (x.1+y.1)/2
  let b := (x.2+y.2)/2
  let A : Set (ℝ × ℝ) := {z | z.1 < a ∧ b < z.2}
  let C : Set (ℝ × ℝ) := {z | a < z.1 ∧ z.2 < b}
  have hAo : IsOpen A := (isOpen_lt continuous_fst continuous_const).inter
    (isOpen_lt continuous_const continuous_snd)
  have hCo : IsOpen C := (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_snd continuous_const)
  have hm : Measurable (fun ω => (R ω 0 1, T ω 0 1)) := by fun_prop
  have hyp : 0 < (μ.map (fun ω => (R ω 0 1,T ω 0 1))) A :=
    (Measure.mem_support_iff_forall x).mp hx A (hAo.mem_nhds (by dsimp [A,a,b]; constructor <;> linarith))
  have hxp : 0 < (μ.map (fun ω => (R ω 0 1,T ω 0 1))) C :=
    (Measure.mem_support_iff_forall y).mp hy C (hCo.mem_nhds (by dsimp [C,a,b]; constructor <;> linarith))
  rw [Measure.map_apply hm hAo.measurableSet] at hyp
  rw [Measure.map_apply hm hCo.measurableSet] at hxp
  have hp := gg_two_links_positive hGG hAo.measurableSet hCo.measurableSet
    (ENNReal.toReal_pos hyp.ne' (measure_ne_top _ _))
    (ENNReal.toReal_pos hxp.ne' (measure_ne_top _ _))
  have hz : μ ({ω | (R ω 0 1,T ω 0 1) ∈ A} ∩
      {ω | (R ω 0 2,T ω 0 2) ∈ C}) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [huR,huT,huS,hsR,hsT] with ω hr ht hs hsr hst
    rintro ⟨ha,hc⟩
    exact ultrametric_no_crossing hr ht hs hsr hst
      ⟨ha.1.trans hc.1, hc.2.trans ha.2⟩
  rw [measureReal_def, hz, ENNReal.toReal_zero] at hp
  exact lt_irrefl 0 hp

end IsingPerceptron

end

end OAI
