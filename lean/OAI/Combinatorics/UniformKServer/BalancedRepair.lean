import Mathlib
import OAI.Combinatorics.UniformKServer.Epochs

namespace OAI

                                   
section

                                                                      
                                                                        
                                                                  
namespace UniformKServer.BalancedRepair
open scoped symmDiff
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]

abbrev Joint (Ω ι : Type*) := (Ω × Finset ι) → ℝ

def admissible (μ : Ω → ℝ) (r : Ω → ℕ) (g : Joint Ω ι) : Prop :=
  (∀ q, 0 ≤ g q) ∧ (∀ ω, ∑ A : Finset ι, g (ω,A) = μ ω) ∧
    ∀ q, q.2.card ≠ r q.1 → g q = 0

def marginal (g : Joint Ω ι) (i : ι) : ℝ :=
  ∑ q, g q * if i ∈ q.2 then 1 else 0

def discrepancy (f : ι → ℝ) (g : Joint Ω ι) : ℝ :=
  ∑ i, |marginal g i - f i|

def hamming (base : Ω → Finset ι) (q : Ω × Finset ι) : ℝ :=
  (q.2 ∆ base q.1).card

def cost (base : Ω → Finset ι) (g : Joint Ω ι) : ℝ :=
  ∑ q, g q * hamming base q

def initial (μ : Ω → ℝ) (base : Ω → Finset ι) : Joint Ω ι :=
  fun q => if q.2 = base q.1 then μ q.1 else 0

def objective (base : Ω → Finset ι) (f : ι → ℝ) (g : Joint Ω ι) : ℝ :=
  cost base g + 10 * discrepancy f g


omit [Fintype Ω] [DecidableEq Ω] in
theorem initial_admissible (μ : Ω → ℝ) (r : Ω → ℕ) (base : Ω → Finset ι)
    (hμ : ∀ ω, 0 ≤ μ ω) (hbase : ∀ ω, (base ω).card = r ω) :
    admissible μ r (initial μ base) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    simp only [initial]
    split
    · exact hμ q.1
    · exact le_rfl
  · intro ω
    simp [initial]
  · intro q hq
    simp only [initial]
    split_ifs with h
    · exact False.elim (hq (h ▸ hbase q.1))
    · rfl

omit [DecidableEq Ω] [DecidableEq ι] in
theorem total_mass {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) : ∑ q, g q = ∑ ω, μ ω := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun ω _ => hg.2.1 ω

omit [DecidableEq Ω] in
theorem initial_cost (μ : Ω → ℝ) (base : Ω → Finset ι) :
    cost base (initial μ base) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  simp only [initial]
  split_ifs with h
  · simp [hamming, h]
  · simp

omit [DecidableEq Ω] [DecidableEq ι] in
theorem admissible_compact (μ : Ω → ℝ) (r : Ω → ℕ) :
    IsCompact {g : Joint Ω ι | admissible μ r g} := by
  have h₁ : IsClosed {g : Joint Ω ι | ∀ q, 0 ≤ g q} := by
    simp only [← Set.iInter_ofPred]
    exact isClosed_iInter fun q => isClosed_le continuous_const (continuous_apply q)
  have h₂ : IsClosed {g : Joint Ω ι | ∀ ω, ∑ A : Finset ι, g (ω,A) = μ ω} := by
    simp only [← Set.iInter_ofPred]
    exact isClosed_iInter fun ω => isClosed_eq (by fun_prop) continuous_const
  have h₃ : IsClosed {g : Joint Ω ι | ∀ q, q.2.card ≠ r q.1 → g q = 0} := by
    simp only [← Set.iInter_ofPred]
    apply isClosed_iInter
    intro q
    by_cases hq : q.2.card ≠ r q.1
    · simpa [hq] using isClosed_eq (continuous_apply q) (continuous_const (y := (0 : ℝ)))
    · simp [hq]
  have hc : IsClosed {g : Joint Ω ι | admissible μ r g} := h₁.inter (h₂.inter h₃)
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : Ω × Finset ι => (0 : ℝ))
    (fun _ => ∑ ω, μ ω))).of_isClosed_subset hc
  intro g hg
  refine ⟨hg.1, ?_⟩
  intro q
  calc
    g q ≤ ∑ q', g q' := Finset.single_le_sum (fun q' _ => hg.1 q') (Finset.mem_univ q)
    _ = _ := total_mass hg

omit [DecidableEq Ω] in
theorem objective_continuous (base : Ω → Finset ι) (f : ι → ℝ) :
    Continuous (objective base f) := by
  unfold objective cost discrepancy marginal
  fun_prop

omit [DecidableEq Ω] in
theorem minimizer_exists (μ : Ω → ℝ) (r : Ω → ℕ) (base : Ω → Finset ι)
    (f : ι → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (hbase : ∀ ω, (base ω).card = r ω) :
    ∃ g, admissible μ r g ∧ ∀ g', admissible μ r g' →
      objective base f g ≤ objective base f g' := by
  exact (admissible_compact μ r).exists_isMinOn
    ⟨initial μ base, initial_admissible μ r base hμ hbase⟩
    (objective_continuous base f).continuousOn

def transfer (g : Joint Ω ι) (q q' : Ω × Finset ι) (ε : ℝ) : Joint Ω ι :=
  fun z => g z - (if z = q then ε else 0) + (if z = q' then ε else 0)

theorem sum_transfer (g : Joint Ω ι) (q q' : Ω × Finset ι) (ε : ℝ)
    (c : (Ω × Finset ι) → ℝ) :
    (∑ z, transfer g q q' ε z * c z) = (∑ z, g z * c z) + ε*(c q' - c q) := by
  simp only [transfer, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have he : ∀ a : Ω × Finset ι, (∑ z, (if z = a then ε else 0) * c z) = ε*c a := by
    intro a
    simp
  rw [he, he]
  ring

omit [Fintype Ω] in
theorem transfer_admissible {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) (q q' : Ω × Finset ι) (ε : ℝ)
    (hε : 0 ≤ ε) (hbound : ε ≤ g q) (hstate : q.1 = q'.1)
    (hcard : q'.2.card = r q'.1) :
    admissible μ r (transfer g q q' ε) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    dsimp [transfer]
    have hsub : 0 ≤ g z - (if z = q then ε else 0) := by
      split_ifs with h
      · subst z; exact sub_nonneg.mpr hbound
      · simpa using hg.1 z
    exact add_nonneg hsub (by split <;> positivity)
  · intro ω
    simp only [transfer, Finset.sum_add_distrib, Finset.sum_sub_distrib, hg.2.1]
    have he : ∀ a : Ω × Finset ι, (∑ A : Finset ι, if (ω,A) = a then ε else 0) =
        if ω = a.1 then ε else 0 := by
      intro a
      rcases a with ⟨ω', A'⟩
      by_cases h : ω = ω'
      · subst ω'; simp
      · simp [h]
    rw [he, he, hstate]
    ring
  · intro z hz
    have hnew : z ≠ q' := by intro h; subst z; exact hz hcard
    have hold : z = q → ε = 0 := by
      intro h
      subst z
      have hzero := hg.2.2 q hz
      linarith
    simp only [transfer, hg.2.2 z hz, ite_eq_right hnew, add_zero, zero_sub]
    split_ifs with h
    · simp [hold h]
    · simp


def exchange (A : Finset ι) (i j : ι) : Finset ι := insert j (A.erase i)

omit [Fintype ι] in
theorem exchange_card {A : Finset ι} {i j : ι} (hi : i ∈ A) (hj : j ∉ A) :
    (exchange A i j).card = A.card := by
  rw [exchange, Finset.card_insert_of_notMem (by simp [hj]), Finset.card_erase_of_mem hi]
  have : 0 < A.card := Finset.card_pos.mpr ⟨i, hi⟩
  omega

omit [Fintype ι] in
theorem exchange_indicator {A : Finset ι} {i j : ι} (hi : i ∈ A) (hj : j ∉ A) (l : ι) :
    (if l ∈ exchange A i j then (1 : ℝ) else 0) =
      (if l ∈ A then 1 else 0) + (if l = j then 1 else 0) - (if l = i then 1 else 0) := by
  have hij : i ≠ j := by intro h; subst j; exact hj hi
  by_cases hli : l = i
  · subst l; simp [exchange, hij, hi]
  · by_cases hlj : l = j
    · subst l; simp [exchange, hli, hj]
    · by_cases hl : l ∈ A <;> simp [exchange, hli, hlj, hl]

omit [Fintype Ω] [Fintype ι] [DecidableEq Ω] in
theorem exchange_hamming (base : Ω → Finset ι) (ω : Ω) (A : Finset ι) (i j : ι) :
    hamming base (ω, exchange A i j) ≤ hamming base (ω,A) + 2 := by
  have hs : exchange A i j ∆ base ω ⊆ insert j (insert i (A ∆ base ω)) := by
    intro l hl
    by_cases hi : l = i
    · simp [hi]
    by_cases hj : l = j
    · simp [hj]
    simp only [Finset.mem_insert, hi, hj, false_or]
    simpa [exchange, Finset.mem_symmDiff, hi, hj] using hl
  have hcard := Finset.card_le_card hs
  have h₁ := Finset.card_insert_le j (insert i (A ∆ base ω))
  have h₂ := Finset.card_insert_le i (A ∆ base ω)
  dsimp [hamming]
  exact_mod_cast (show (exchange A i j ∆ base ω).card ≤ (A ∆ base ω).card + 2 by omega)

def swap (g : Joint Ω ι) (ω : Ω) (A : Finset ι) (i j : ι) (ε : ℝ) : Joint Ω ι :=
  transfer g (ω,A) (ω,exchange A i j) ε

omit [Fintype Ω] in
theorem swap_admissible {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) (ω : Ω) (A : Finset ι) (i j : ι) (ε : ℝ)
    (hε : 0 ≤ ε) (hbound : ε ≤ g (ω,A)) (hcard : A.card = r ω)
    (hi : i ∈ A) (hj : j ∉ A) : admissible μ r (swap g ω A i j ε) := by
  apply transfer_admissible hg (ω,A) (ω,exchange A i j) ε hε hbound rfl
  simpa [exchange_card hi hj] using hcard

theorem swap_marginal (g : Joint Ω ι) (ω : Ω) (A : Finset ι) (i j : ι) (ε : ℝ)
    (hi : i ∈ A) (hj : j ∉ A) (l : ι) :
    marginal (swap g ω A i j ε) l = marginal g l +
      ε*((if l = j then 1 else 0) - (if l = i then 1 else 0)) := by
  rw [marginal, swap, sum_transfer]
  change marginal g l + ε * ((if l ∈ exchange A i j then 1 else 0) -
    (if l ∈ A then 1 else 0)) = _
  rw [exchange_indicator hi hj]
  ring

theorem swap_cost (base : Ω → Finset ι) (g : Joint Ω ι) (ω : Ω) (A : Finset ι)
    (i j : ι) (ε : ℝ) (hε : 0 ≤ ε) :
    cost base (swap g ω A i j ε) ≤ cost base g + 2*ε := by
  rw [cost, swap, sum_transfer]
  change cost base g + ε*(hamming base (ω,exchange A i j) - hamming base (ω,A)) ≤ _
  nlinarith [exchange_hamming base ω A i j]

omit [DecidableEq Ω] in
theorem discrepancy_transfer {f : ι → ℝ} {g g' : Joint Ω ι} {i j : ι} {ε : ℝ}
    (hij : i ≠ j) (hε : 0 ≤ ε)
    (hi : ε ≤ marginal g i - f i) (hj : ε ≤ f j - marginal g j)
    (hmarg : ∀ l, marginal g' l = marginal g l +
      ε*((if l = j then 1 else 0) - (if l = i then 1 else 0))) :
    discrepancy f g' = discrepancy f g - 2*ε := by
  have he : ∀ l, |marginal g' l - f l| = |marginal g l - f l| -
      (if l = i then ε else 0) - (if l = j then ε else 0) := by
    intro l
    rw [hmarg]
    by_cases hli : l = i
    · subst l
      simp only [hij, ↓reduceIte, zero_sub, mul_neg, mul_one]
      rw [abs_of_nonneg (by linarith : 0 ≤ marginal g i + -ε - f i),
        abs_of_nonneg (by linarith : 0 ≤ marginal g i - f i)]
      ring
    · by_cases hlj : l = j
      · subst l
        simp only [hli, ↓reduceIte, sub_zero, mul_one]
        rw [abs_of_nonpos (by linarith : marginal g j + ε - f j ≤ 0),
          abs_of_nonpos (by linarith : marginal g j - f j ≤ 0)]
        ring
      · simp [hli, hlj]
  simp only [discrepancy, he, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

omit [DecidableEq Ω] in
theorem sum_marginal {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) : ∑ i, marginal g i = ∑ ω, μ ω * (r ω : ℝ) := by
  unfold marginal
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    (∑ A : Finset ι, g (ω,A) * (A.card : ℝ)) =
        ∑ A : Finset ι, g (ω,A) * (r ω : ℝ) := by
      apply Finset.sum_congr rfl
      intro A _
      by_cases h : A.card = r ω
      · rw [h]
      · rw [hg.2.2 (ω,A) h]; simp
    _ = _ := by rw [← Finset.sum_mul, hg.2.1]


omit [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] in
theorem supported_card {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) {q : Ω × Finset ι} (hq : 0 < g q) : q.2.card = r q.1 := by
  by_contra h
  have := hg.2.2 q h
  linarith

omit [DecidableEq Ω] in
theorem supported_mem {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) {i : ι} (hi : 0 < marginal g i) :
    ∃ q, 0 < g q ∧ i ∈ q.2 := by
  obtain ⟨q, _, hq⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun q _ => mul_nonneg (hg.1 q) (by split <;> positivity))).mp hi
  by_cases h : i ∈ q.2
  · exact ⟨q, by simpa [h] using hq, h⟩
  · simp [h] at hq

omit [DecidableEq Ω] in
theorem supported_notMem {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) (hμ : ∑ ω, μ ω = 1) {i : ι} (hi : marginal g i < 1) :
    ∃ q, 0 < g q ∧ i ∉ q.2 := by
  by_contra! h
  have he : marginal g i = ∑ q, g q := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases hzero : g q = 0
    · simp [hzero]
    · have hp : 0 < g q := lt_of_le_of_ne (hg.1 q) (Ne.symm hzero)
      simp [h q hp]
  rw [he, total_mass hg, hμ] at hi
  exact lt_irrefl _ hi

theorem four_positive {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) : ∃ ε : ℝ, 0 < ε ∧ ε ≤ a ∧ ε ≤ b ∧ ε ≤ c ∧ ε ≤ d := by
  refine ⟨min a (min b (min c d)), lt_min ha (lt_min hb (lt_min hc hd)),
    min_le_left _ _, ?_, ?_, ?_⟩
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

omit [Fintype ι] in
theorem exchange_intermediate {A B : Finset ι} {i j : ι}
    (hij : i ≠ j) (hiA : i ∈ A) (hjA : j ∈ A) (hiB : i ∉ B) (hjB : j ∉ B)
    (hc : A.card ≤ B.card + 1) : ∃ h, h ∈ B ∧ h ∉ A := by
  by_contra! h
  have hsub : insert i (insert j B) ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hiA
    · exact hjA
    · exact h x hx
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hij, hiB]),
    Finset.card_insert_of_notMem hjB] at hcard
  omega

omit [DecidableEq ι] in
theorem discrepancy_pair {f p : ι → ℝ} (hsum : ∑ i, p i = ∑ i, f i)
    (hne : ¬ ∀ i, p i = f i) : ∃ i j, f i < p i ∧ p j < f j := by
  have hpos : ∃ i, f i < p i := by
    by_contra! h
    exact hne (fun i => (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).mp hsum i (Finset.mem_univ i))
  have hneg : ∃ j, p j < f j := by
    by_contra! h
    exact hne (fun i => ((Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).mp hsum.symm i
      (Finset.mem_univ i)).symm)
  obtain ⟨i, hi⟩ := hpos
  obtain ⟨j, hj⟩ := hneg
  exact ⟨i,j,hi,hj⟩

theorem minimizer_exact (μ : Ω → ℝ) (r : Ω → ℕ) (base : Ω → Finset ι) (f : ι → ℝ)
    (hμsum : ∑ ω, μ ω = 1) (s : ℕ) (hr : ∀ ω, r ω = s ∨ r ω = s+1)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∑ i, f i = ∑ ω, μ ω * (r ω : ℝ))
    (g : Joint Ω ι) (hg : admissible μ r g)
    (hmin : ∀ g', admissible μ r g' → objective base f g ≤ objective base f g') :
    ∀ i, marginal g i = f i := by
  by_contra hne
  obtain ⟨i,j,hi,hj⟩ := discrepancy_pair ((sum_marginal hg).trans hsum.symm) hne
  have hij : i ≠ j := by intro h; subst j; linarith
  by_cases hdirect : ∃ q : Ω × Finset ι, 0 < g q ∧ i ∈ q.2 ∧ j ∉ q.2
  · obtain ⟨q,hq,hiA,hjA⟩ := hdirect
    obtain ⟨ε,hε,heq,_,hei,hej⟩ := four_positive hq hq (sub_pos.mpr hi) (sub_pos.mpr hj)
    let g' := swap g q.1 q.2 i j ε
    have hg' : admissible μ r g' := swap_admissible hg _ _ _ _ _ hε.le heq
      (supported_card hg hq) hiA hjA
    have hmarg := swap_marginal g q.1 q.2 i j ε hiA hjA
    have hd := discrepancy_transfer hij hε.le hei hej hmarg
    have hc := swap_cost base g q.1 q.2 i j ε hε.le
    have hm := hmin g' hg'
    change cost base g + 10*discrepancy f g ≤ cost base g' + 10*discrepancy f g' at hm
    change discrepancy f g' = _ at hd
    change cost base g' ≤ _ at hc
    rw [hd] at hm
    linarith
  · obtain ⟨a,ha,hia⟩ := supported_mem hg (lt_of_le_of_lt (hf i).1 hi)
    have hja : j ∈ a.2 := by
      by_contra h
      exact hdirect ⟨a,ha,hia,h⟩
    obtain ⟨b,hb,hjb⟩ := supported_notMem hg hμsum (lt_of_lt_of_le hj (hf j).2)
    have hib : i ∉ b.2 := by
      intro h
      exact hdirect ⟨b,hb,h,hjb⟩
    have hca := supported_card hg ha
    have hcb := supported_card hg hb
    have hcards : a.2.card ≤ b.2.card + 1 := by
      rcases hr a.1 with h | h <;> rcases hr b.1 with h' | h' <;> omega
    obtain ⟨h,hhb,hha⟩ := exchange_intermediate hij hia hja hib hjb hcards
    have hih : i ≠ h := by intro he; subst h; exact hha hia
    have hjh : j ≠ h := by intro he; subst h; exact hha hja
    obtain ⟨ε,hε,hea,heb,hei,hej⟩ := four_positive ha hb (sub_pos.mpr hi) (sub_pos.mpr hj)
    let g₁ := swap g a.1 a.2 i h ε
    have hg₁ : admissible μ r g₁ := swap_admissible hg _ _ _ _ _ hε.le hea hca hia hha
    have hneq₀ : (b.1,b.2) ≠ (a.1,a.2) := by
      intro he
      have he' := congrArg Prod.snd he
      exact hjb (he' ▸ hja)
    have hneq₁ : (b.1,b.2) ≠ (a.1,exchange a.2 i h) := by
      intro he
      have he' := congrArg Prod.snd he
      apply hjb
      rw [he']
      simp [exchange, Ne.symm hij, hja]
    have hgb : g₁ (b.1,b.2) = g b := by
      simp [g₁, swap, transfer, hneq₀, hneq₁]
    let g₂ := swap g₁ b.1 b.2 h j ε
    have hg₂ : admissible μ r g₂ := swap_admissible hg₁ _ _ _ _ _ hε.le
      (by simpa [hgb] using heb) hcb hhb hjb
    have hmarg : ∀ l, marginal g₂ l = marginal g l +
        ε*((if l = j then 1 else 0) - (if l = i then 1 else 0)) := by
      intro l
      rw [show marginal g₂ l = _ from swap_marginal g₁ b.1 b.2 h j ε hhb hjb l,
        show marginal g₁ l = _ from swap_marginal g a.1 a.2 i h ε hia hha l]
      ring
    have hd := discrepancy_transfer hij hε.le hei hej hmarg
    have hc₁ := swap_cost base g a.1 a.2 i h ε hε.le
    have hc₂ := swap_cost base g₁ b.1 b.2 h j ε hε.le
    change cost base g₁ ≤ cost base g + 2*ε at hc₁
    change cost base g₂ ≤ cost base g₁ + 2*ε at hc₂
    have hm := hmin g₂ hg₂
    change cost base g + 10*discrepancy f g ≤ cost base g₂ + 10*discrepancy f g₂ at hm
    rw [hd] at hm
    linarith

/-- A finite kernel repairs all coordinate means while keeping each actual
state's prescribed total, even when the total is correlated with the old vector. -/
theorem repair (μ : Ω → ℝ) (r : Ω → ℕ) (base : Ω → Finset ι) (f : ι → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (hbase : ∀ ω, (base ω).card = r ω)
    (s : ℕ) (hr : ∀ ω, r ω = s ∨ r ω = s+1)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∑ i, f i = ∑ ω, μ ω * (r ω : ℝ)) :
    ∃ g : Joint Ω ι, admissible μ r g ∧ (∀ i, marginal g i = f i) ∧
      cost base g ≤ 10 * discrepancy f (initial μ base) := by
  obtain ⟨g,hg,hmin⟩ := minimizer_exists μ r base f hμ hbase
  have hexact := minimizer_exact μ r base f hμsum s hr hf hsum g hg hmin
  refine ⟨g,hg,hexact,?_⟩
  have hm := hmin (initial μ base) (initial_admissible μ r base hμ hbase)
  simpa [objective, discrepancy, hexact, initial_cost] using hm

end UniformKServer.BalancedRepair


end

end OAI
