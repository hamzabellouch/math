import OAI.Probability.TraceReconstruction.FiniteLaw
import OAI.Probability.TraceReconstruction.Kernels
import OAI.Probability.TraceReconstruction.Scales

namespace OAI

/-!
# Ranks

Retained subsets, conditional rank experiments, tagged gaps, period geometry, Gaussian Schur estimates, and uniform square sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


namespace TraceReconstruction

variable {α : Type*} [Fintype α]

def subsetWeight (p : ℝ) (S : Finset α) : ℝ :=
  p^S.card * (1-p)^(Fintype.card α-S.card)

theorem sum_subsetWeight (p : ℝ) : (∑ S : Finset α, subsetWeight p S)=1 := by
  classical
  have h := Finset.sum_pow_mul_eq_add_pow p (1-p) (Finset.univ : Finset α)
  simpa [subsetWeight] using h

theorem sum_fixedCard_subsetWeight (p : ℝ) (l : ℕ) :
    (∑ S : Finset α, if S.card=l then subsetWeight p S else 0) =
      binomialMass (Fintype.card α) p l := by
  classical
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter (fun S : Finset α => S.card=l)) =
      (Finset.univ : Finset α).powersetCard l := by ext; simp
  rw [hset]
  have he : ∀ S ∈ (Finset.univ : Finset α).powersetCard l,
      subsetWeight p S=p^l*(1-p)^(Fintype.card α-l) := by
    classical
    intro S hS
    simp only [subsetWeight, (Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul,
    binomialMass]
  ring

def subsetLaw (p : ℝ) (hp : p ∈ Set.Icc 0 1) : FiniteLaw (Finset α) where
  mass := subsetWeight p
  nonneg S := by unfold subsetWeight; positivity [hp.1, sub_nonneg.mpr hp.2]
  total := sum_subsetWeight p

abbrev FixedSubset (α : Type*) [Fintype α] (l : ℕ) := {S : Finset α // S.card=l}

theorem card_fixedSubset (l : ℕ) :
    Fintype.card (FixedSubset α l)=(Fintype.card α).choose l := by
  classical
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter (fun S : Finset α => S.card=l)) =
      (Finset.univ : Finset α).powersetCard l := by ext; simp
  rw [hset, Finset.card_powersetCard, Finset.card_univ]

def uniformSubsetLaw (l : ℕ) (hl : l ≤ Fintype.card α) : FiniteLaw (FixedSubset α l) where
  mass _ := 1 / ((Fintype.card α).choose l : ℝ)
  nonneg _ := by positivity
  total := by
    classical
    simp only [Finset.sum_const, Finset.card_univ, card_fixedSubset, nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast (Nat.choose_pos hl).ne')

/-- Conditional Bernoulli sampling, at every interior parameter, is exactly uniform. -/
theorem conditional_subset_uniform {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    {l : ℕ} (hl : l ≤ Fintype.card α) (S : FixedSubset α l) :
    subsetWeight p S.val / binomialMass (Fintype.card α) p l =
      (uniformSubsetLaw l hl).mass S := by
  classical
  have hp0 : p≠0 := hp.1.ne'
  have hq0 : 1-p≠0 := by linarith [hp.2]
  have hc : (((Fintype.card α).choose l):ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hl).ne'
  simp only [subsetWeight, S.property, binomialMass, uniformSubsetLaw]
  field_simp

/-- Slot at an observed return rank, with the original total order. -/
def slotAtRank {n l : ℕ} (S : FixedSubset (Fin n) l) (v : Fin l) : Fin n :=
  (S.val.orderIsoOfFin S.property v).val

theorem slotAtRank_mem {n l : ℕ} (S : FixedSubset (Fin n) l) (v : Fin l) :
    slotAtRank S v ∈ S.val := (S.val.orderIsoOfFin S.property v).property

theorem slotAtRank_strictMono {n l : ℕ} (S : FixedSubset (Fin n) l) :
    StrictMono (slotAtRank S) := by
  classical
  intro a b hab
  exact (S.val.orderIsoOfFin S.property).strictMono hab

def defectAtRank {n l : ℕ} (D : Finset (Fin n)) (S : FixedSubset (Fin n) l)
    (v : Fin l) : Bool := decide (slotAtRank S v ∈ D)

def taggedRankEvent {n l r : ℕ} (p : Fin r → Fin n) (v : Fin r → Fin l)
    (S : FixedSubset (Fin n) l) : Prop := ∀ i, slotAtRank S (v i)=p i

/-- Unhypothesized rank kernel: defined from the actual uniformly retained subset. -/
def subsetRankKernel {n l r : ℕ} (hl : l≤n) (p : Fin r → Fin n) (v : Fin r → Fin l) : ℝ := by
  classical
  exact ∑ S : FixedSubset (Fin n) l, if taggedRankEvent p v S then
    (uniformSubsetLaw l (by simpa using hl)).mass S else 0

theorem subsetRankKernel_nonneg {n l r : ℕ} (hl : l≤n)
    (p : Fin r → Fin n) (v : Fin r → Fin l) : 0 ≤ subsetRankKernel hl p v := by
  classical
  unfold subsetRankKernel
  apply Finset.sum_nonneg
  intro S _
  split_ifs
  · exact (uniformSubsetLaw l (by simpa using hl)).nonneg S
  · rfl

theorem subsetRankKernel_le_one {n l r : ℕ} (hl : l≤n)
    (p : Fin r → Fin n) (v : Fin r → Fin l) : subsetRankKernel hl p v ≤ 1 := by
  classical
  unfold subsetRankKernel
  rw [← (uniformSubsetLaw (α := Fin n) l (by simpa using hl)).total]
  apply Finset.sum_le_sum
  intro S _
  split_ifs
  · rfl
  · exact (uniformSubsetLaw l (by simpa using hl)).nonneg S


/-- Canonical slot universe split at the tagged positions. Actual order is only
needed to identify each component with its before/between/after interval. -/
abbrev GapUniverse (r d : ℕ) (g : Fin d → ℕ) := Fin r ⊕ ((i : Fin d) × Fin (g i))

def gapDecode {r d : ℕ} {g : Fin d → ℕ} (S : Finset (GapUniverse r d g))
    (i : Fin d) : Finset (Fin (g i)) :=
  Finset.univ.filter fun a => Sum.inr ⟨i,a⟩ ∈ S

def gapEncode {r d : ℕ} {g : Fin d → ℕ} (A : (i : Fin d) → Finset (Fin (g i))) :
    Finset (GapUniverse r d g) := by
  classical
  exact Finset.univ.filter fun x => match x with
    | Sum.inl _ => True
    | Sum.inr a => a.2 ∈ A a.1

@[simp] theorem mem_gapEncode_left {r d : ℕ} {g : Fin d → ℕ}
    (A : (i : Fin d) → Finset (Fin (g i))) (a : Fin r) :
    Sum.inl a ∈ gapEncode A := by simp [gapEncode]

@[simp] theorem mem_gapEncode_right {r d : ℕ} {g : Fin d → ℕ}
    (A : (i : Fin d) → Finset (Fin (g i))) (i : Fin d) (a : Fin (g i)) :
    Sum.inr ⟨i,a⟩ ∈ gapEncode (r := r) A ↔ a ∈ A i := by simp [gapEncode]

@[simp] theorem gapDecode_encode {r d : ℕ} {g : Fin d → ℕ}
    (A : (i : Fin d) → Finset (Fin (g i))) (i : Fin d) :
    gapDecode (gapEncode (r := r) A) i=A i := by ext; simp [gapDecode]

theorem gapEncode_decode {r d : ℕ} {g : Fin d → ℕ}
    (S : Finset (GapUniverse r d g)) (hS : ∀ a, Sum.inl a∈S) :
    gapEncode (gapDecode S)=S := by
  ext x
  cases x with
  | inl a => simp [hS]
  | inr a => rcases a with ⟨i,a⟩; simp [gapDecode]

def gapEvent {r d : ℕ} {g : Fin d → ℕ} (z : Fin d → ℕ)
    (S : Finset (GapUniverse r d g)) : Prop :=
  (∀ a, Sum.inl a∈S) ∧ ∀ i, (gapDecode S i).card=z i

instance gapEvent_decidable {r d : ℕ} {g : Fin d → ℕ} (z : Fin d → ℕ)
    (S : Finset (GapUniverse r d g)) : Decidable (gapEvent z S) := by
  unfold gapEvent
  infer_instance

def gapEventEquiv {r d : ℕ} {g z : Fin d → ℕ} :
    {S : Finset (GapUniverse r d g) // gapEvent z S} ≃
      ((i : Fin d) → FixedSubset (Fin (g i)) (z i)) where
  toFun S i := ⟨gapDecode S.val i, S.property.2 i⟩
  invFun A := ⟨gapEncode (fun i => (A i).val), by
    constructor
    · intro a; simp
    · intro i; simp only [gapDecode_encode, (A i).property]⟩
  left_inv S := by
    apply Subtype.ext
    exact gapEncode_decode S.val S.property.1
  right_inv A := by
    funext i
    apply Subtype.ext
    change gapDecode (gapEncode (fun i => (A i).val)) i = (A i).val
    exact gapDecode_encode _ _

theorem card_gapEvent {r d : ℕ} (g z : Fin d → ℕ) :
    Fintype.card {S : Finset (GapUniverse r d g) // gapEvent z S} =
      ∏ i, (g i).choose (z i) := by
  classical
  rw [Fintype.card_congr gapEventEquiv, Fintype.card_pi]
  simp only [card_fixedSubset, Fintype.card_fin]

theorem card_gapEncode {r d : ℕ} {g : Fin d → ℕ}
    (A : (i : Fin d) → Finset (Fin (g i))) :
    (gapEncode (r := r) A).card = r + ∑ i, (A i).card := by
  classical
  rw [Finset.card_eq_sum_ones]
  simp only [gapEncode, Finset.sum_filter]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ x : Fin (g i), if x ∈ A i then (1:ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
    _ = _ := (Finset.card_eq_sum_ite (Finset.subset_univ (A i))).symm

theorem card_of_gapEvent {r d : ℕ} {g z : Fin d → ℕ}
    (S : Finset (GapUniverse r d g)) (hS : gapEvent z S) :
    S.card = r+∑ i, z i := by
  rw [← gapEncode_decode S hS.1, card_gapEncode]
  simp only [hS.2]


/-- The exact unconditioned tagged-gap probability; no asymptotic estimate is used. -/
theorem gapEvent_bernoulli_probability {r d : ℕ} (g z : Fin d → ℕ)
    (hz : ∀ i, z i≤g i) (p : ℝ) :
    (∑ S : Finset (GapUniverse r d g), if gapEvent z S then subsetWeight p S else 0) =
      p^r * ∏ i, binomialMass (g i) p (z i) := by
  classical
  have hcount : (∑ S : Finset (GapUniverse r d g),
      if gapEvent z S then (1:ℝ) else 0) = ∏ i, ((g i).choose (z i):ℝ) := by
    rw [Finset.sum_boole, ← Fintype.card_subtype, card_gapEvent, Nat.cast_prod]
  have hnum : (∑ S : Finset (GapUniverse r d g), if gapEvent z S then subsetWeight p S else 0) =
      (∏ i, ((g i).choose (z i):ℝ)) *
        (p^(r+∑ i, z i)*(1-p)^(r+∑ i, g i-(r+∑ i, z i))) := by
    rw [← hcount, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs with hS
    · simp only [one_mul, subsetWeight, card_of_gapEvent S hS,
        Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
    · exact (zero_mul _).symm
  have hsub : (∑ i, g i)-(∑ i, z i)=∑ i, (g i-z i) := by
    exact (Finset.sum_tsub_distrib Finset.univ (fun i _ => hz i)).symm
  rw [hnum, Nat.add_sub_add_left, hsub, pow_add]
  simp only [binomialMass, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/-- Conditional Bernoulli representation of the source rank kernel in gap coordinates. -/
theorem gapEvent_conditional_formula {r d : ℕ} (g z : Fin d → ℕ)
    (hz : ∀ i, z i≤g i) (p : ℝ) :
    (∑ S : Finset (GapUniverse r d g), if gapEvent z S then subsetWeight p S else 0) /
      binomialMass (r+∑ i, g i) p (r+∑ i, z i) =
    p^r / binomialMass (r+∑ i, g i) p (r+∑ i, z i) *
      ∏ i, binomialMass (g i) p (z i) := by
  rw [gapEvent_bernoulli_probability g z hz]
  ring

end TraceReconstruction


namespace TraceReconstruction

theorem slotAtRank_lower_card {n l : ℕ} (S : FixedSubset (Fin n) l) (v : Fin l) :
    (S.val.filter fun j => j < slotAtRank S v).card = v.val := by
  classical
  let e := S.val.orderEmbOfFin S.property
  have hslot (i:Fin l) : e i = slotAtRank S i := rfl
  have hmap : (Finset.Iio v).map e.toEmbedding = S.val.filter (fun j => j<e v) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_Iio, Finset.mem_filter, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨S.val.orderEmbOfFin_mem S.property i, e.strictMono hi⟩
    · rintro ⟨hj,hv⟩
      obtain ⟨i,hi⟩ := (S.val.orderIsoOfFin S.property).surjective ⟨j,hj⟩
      have hei : e i=j := congrArg Subtype.val hi
      refine ⟨i, ?_, hei⟩
      exact e.lt_iff_lt.mp (hei.symm ▸ hv)
  rw [← hslot, ← hmap, Finset.card_map, Fin.card_Iio]

theorem slotAtRank_eq_iff {n l : ℕ} (S : FixedSubset (Fin n) l) (v : Fin l) (p : Fin n) :
    slotAtRank S v=p ↔ p∈S.val ∧ (S.val.filter fun j => j<p).card=v.val := by
  classical
  constructor
  · intro h
    rw [← h]
    exact ⟨slotAtRank_mem S v, slotAtRank_lower_card S v⟩
  · rintro ⟨hp,hcard⟩
    obtain ⟨i,hi⟩ := (S.val.orderIsoOfFin S.property).surjective ⟨p,hp⟩
    have he : slotAtRank S i=p := congrArg Subtype.val hi
    have hcv := slotAtRank_lower_card S i
    rw [he,hcard] at hcv
    have hiv : i=v := Fin.ext hcv.symm
    simpa [hiv] using he

/-- Bounds for the open gaps of an increasing tuple; slots and ranks are zero-based. -/
def tupleLower {n r : ℕ} (p : Fin r → Fin n) : Fin (r+1) → ℕ :=
  Fin.cons 0 (fun i => (p i).val + 1)

def tupleUpper {n r : ℕ} (p : Fin r → Fin n) : Fin (r+1) → ℕ :=
  Fin.snoc (fun i => (p i).val) n

def tupleGap {n r : ℕ} (p : Fin r → Fin n) (j : Fin (r+1)) : ℕ :=
  tupleUpper p j - tupleLower p j

@[simp] theorem tupleLower_zero {n r : ℕ} (p : Fin r → Fin n) : tupleLower p 0 = 0 :=
  Fin.cons_zero _ _
@[simp] theorem tupleLower_succ {n r : ℕ} (p : Fin r → Fin n) (i : Fin r) :
    tupleLower p i.succ = (p i).val + 1 := Fin.cons_succ _ _ _
@[simp] theorem tupleUpper_castSucc {n r : ℕ} (p : Fin r → Fin n) (i : Fin r) :
    tupleUpper p i.castSucc = (p i).val := Fin.snoc_castSucc _ _ _
@[simp] theorem tupleUpper_last {n r : ℕ} (p : Fin r → Fin n) :
    tupleUpper p (Fin.last r) = n := Fin.snoc_last _ _

theorem tupleLower_le_tag {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (i : Fin r) (j : Fin (r+1)) (hji : j ≤ i.castSucc) :
    tupleLower p j ≤ (p i).val := by
  induction j using Fin.cases with
  | zero => simp
  | succ a =>
    simp only [tupleLower_succ]
    have hai : a < i := by
      change a.val < i.val
      have hh : a.val + 1 ≤ i.val := hji
      omega
    exact hp hai

theorem tag_lt_tupleLower {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (i : Fin r) (j : Fin (r+1)) (hij : i.castSucc < j) :
    (p i).val < tupleLower p j := by
  induction j using Fin.cases with
  | zero => exact False.elim (by simp at hij)
  | succ a =>
    simp only [tupleLower_succ]
    have hia : i ≤ a := by
      change i.val ≤ a.val
      have hh : i.val < a.val + 1 := hij
      omega
    exact Nat.lt_succ_of_le (hp.monotone hia)

theorem tupleUpper_le_total {n r : ℕ} (p : Fin r → Fin n) (j : Fin (r+1)) :
    tupleUpper p j ≤ n := by
  induction j using Fin.lastCases with
  | last => simp
  | cast i => simpa only [tupleUpper_castSucc] using (p i).isLt.le

theorem tupleLower_le_total {n r : ℕ} (p : Fin r → Fin n) (j : Fin (r+1)) :
    tupleLower p j ≤ n := by
  induction j using Fin.cases with
  | zero => simp
  | succ i => simpa only [tupleLower_succ] using Nat.succ_le_of_lt (p i).isLt

theorem tupleLower_le_upper {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (j : Fin (r+1)) : tupleLower p j ≤ tupleUpper p j := by
  induction j using Fin.lastCases with
  | last => simpa using tupleLower_le_total p (Fin.last r)
  | cast i => simpa using tupleLower_le_tag p hp i i.castSucc le_rfl

theorem tupleGap_total {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p) :
    r + ∑ j, tupleGap p j = n := by
  have hrs : r ≤ n := by simpa using Fintype.card_le_of_injective p hp.injective
  have ha : (∑ j, tupleLower p j) = (∑ i, (p i).val) + r := by
    rw [Fin.sum_univ_succ]
    simp [Finset.sum_add_distrib]
  have hb : (∑ j, tupleUpper p j) = (∑ i, (p i).val) + n := by
    rw [Fin.sum_univ_castSucc]
    simp
  simp only [tupleGap]
  rw [Finset.sum_tsub_distrib _ (fun j _ => tupleLower_le_upper p hp j), ha, hb]
  omega

/-- Maps abstract gap coordinates to their actual source slots. -/
def tupleGapMap {n r : ℕ} (p : Fin r → Fin n) :
    GapUniverse r (r+1) (tupleGap p) → Fin n
  | .inl i => p i
  | .inr ⟨j,a⟩ => ⟨tupleLower p j + a.val, by
      have hx := a.isLt
      have hu := tupleUpper_le_total p j
      simp only [tupleGap] at hx
      omega⟩

theorem tupleGapMap_gap_lt_tag {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (i : Fin r) (j : Fin (r+1)) (a : Fin (tupleGap p j)) :
    tupleGapMap p (.inr ⟨j,a⟩) < p i ↔ j ≤ i.castSucc := by
  constructor
  · intro h
    by_contra hn
    have hx := tag_lt_tupleLower p hp i j (lt_of_not_ge hn)
    change tupleLower p j + a.val < (p i).val at h
    omega
  · intro h
    have hji : j.val < r := lt_of_le_of_lt (show j.val ≤ i.val from h) i.isLt
    let k : Fin r := ⟨j.val, hji⟩
    have hjk : j = k.castSucc := Fin.ext rfl
    have ht : tupleUpper p j ≤ (p i).val := by
      rw [hjk, tupleUpper_castSucc]
      exact hp.monotone (show k ≤ i from h)
    have hx := a.isLt
    change tupleLower p j + a.val < (p i).val
    unfold tupleGap at hx
    omega

theorem tupleGapMap_tag_lt_gap {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (i : Fin r) (j : Fin (r+1)) (a : Fin (tupleGap p j)) :
    p i < tupleGapMap p (.inr ⟨j,a⟩) ↔ i.castSucc < j := by
  constructor
  · intro h
    by_contra hn
    have hx := (tupleGapMap_gap_lt_tag p hp i j a).2 (le_of_not_gt hn)
    exact (lt_asymm h hx)
  · intro h
    have hx := tag_lt_tupleLower p hp i j h
    change (p i).val < tupleLower p j + a.val
    omega

theorem tupleGapMap_injective {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p) :
    Function.Injective (tupleGapMap p) := by
  rintro (i | ⟨j,a⟩) (i' | ⟨j',a'⟩) h
  · exact congrArg Sum.inl (hp.injective h)
  · have hn : p i ≠ tupleGapMap p (.inr ⟨j',a'⟩) := by
      rcases le_or_gt j' i.castSucc with hj | hj
      · exact ne_of_gt ((tupleGapMap_gap_lt_tag p hp i j' a').2 hj)
      · exact ne_of_lt ((tupleGapMap_tag_lt_gap p hp i j' a').2 hj)
    exact False.elim (hn h)
  · have hn : p i' ≠ tupleGapMap p (.inr ⟨j,a⟩) := by
      rcases le_or_gt j i'.castSucc with hj | hj
      · exact ne_of_gt ((tupleGapMap_gap_lt_tag p hp i' j a).2 hj)
      · exact ne_of_lt ((tupleGapMap_tag_lt_gap p hp i' j a).2 hj)
    exact False.elim (hn h.symm)
  · have hj : j=j' := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hj | hj
      · let i : Fin r := ⟨j.val, lt_of_lt_of_le hj (Nat.le_of_lt_succ j'.isLt)⟩
        have hji : j=i.castSucc := Fin.ext rfl
        have h1 := (tupleGapMap_gap_lt_tag p hp i j a).2 (by rw [hji])
        have h2 := (tupleGapMap_tag_lt_gap p hp i j' a').2 (by rwa [← hji])
        rw [h] at h1
        exact (lt_asymm h1 h2)
      · let i : Fin r := ⟨j'.val, lt_of_lt_of_le hj (Nat.le_of_lt_succ j.isLt)⟩
        have hji : j'=i.castSucc := Fin.ext rfl
        have h1 := (tupleGapMap_gap_lt_tag p hp i j' a').2 (by rw [hji])
        have h2 := (tupleGapMap_tag_lt_gap p hp i j a).2 (by rwa [← hji])
        rw [h] at h2
        exact (lt_asymm h1 h2)
    subst j'
    have ha : a=a' := by
      apply Fin.ext
      have hh := congrArg Fin.val h
      change tupleLower p j + a.val = tupleLower p j + a'.val at hh
      omega
    subst a'
    rfl

def tupleGapEquiv {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p) :
    GapUniverse r (r+1) (tupleGap p) ≃ Fin n :=
  Equiv.ofBijective (tupleGapMap p) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨tupleGapMap_injective p hp, by
      simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
      exact tupleGap_total p hp⟩)

/-- The count below a tagged slot is its tag index plus the retained gap counts. -/
theorem gapEncoded_lower_card {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (A : (j : Fin (r+1)) → Finset (Fin (tupleGap p j))) (i : Fin r) :
    (((gapEncode A).map (tupleGapEquiv p hp).toEmbedding).filter
      fun x => x < p i).card = i.val + ∑ j ∈ Finset.Iic i.castSucc, (A j).card := by
  classical
  have hmap : (((gapEncode A).map (tupleGapEquiv p hp).toEmbedding).filter
      fun x => x < p i) =
      ((gapEncode A).filter fun x => tupleGapMap p x < p i).map
        (tupleGapEquiv p hp).toEmbedding := by
    rw [Finset.filter_map]
    rfl
  rw [hmap, Finset.card_map, Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, gapEncode]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only
  simp only [↓reduceIte]
  have hleft : (∑ a : Fin r, if tupleGapMap p (.inl a) < p i then (1:ℕ) else 0) = i.val := by
    simp only [tupleGapMap, hp.lt_iff_lt]
    have hx : (Finset.univ.filter fun a : Fin r => a < i) = Finset.Iio i := by ext; simp
    rw [← Finset.sum_filter, hx, Finset.sum_const, Fin.card_Iio, smul_eq_mul, mul_one]
  rw [hleft]
  congr 1
  simp_rw [tupleGapMap_gap_lt_tag p hp]
  have hr (j : Fin (r+1)) :
      (∑ a : Fin (tupleGap p j), if a ∈ A j then
        (if j ≤ i.castSucc then (1:ℕ) else 0) else 0) =
      if j ≤ i.castSucc then (A j).card else 0 := by
    by_cases hj : j ≤ i.castSucc
    · simp only [hj, ite_true]
      exact (Finset.card_eq_sum_ite (Finset.subset_univ (A j))).symm
    · simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => hr j), ← Finset.sum_filter]
  congr 1
  ext j
  simp

@[simp] theorem gapEncode_univ {r d : ℕ} {g : Fin d → ℕ} :
    gapEncode (r := r) (fun i => (Finset.univ : Finset (Fin (g i)))) = Finset.univ := by
  ext x
  cases x with
  | inl i => simp
  | inr p => rcases p with ⟨j,a⟩; simp

theorem tupleGap_prefix {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (i : Fin r) : i.val + ∑ j ∈ Finset.Iic i.castSucc, tupleGap p j = (p i).val := by
  have h := gapEncoded_lower_card p hp (fun _ => Finset.univ) i
  have hset : (Finset.univ.filter fun x : Fin n => x < p i) = Finset.Iio (p i) := by
    ext; simp
  simpa only [gapEncode_univ, Finset.map_univ_equiv,
    hset, Fin.card_Iio, Finset.card_univ, Fintype.card_fin] using h.symm

/-- Initial-segment sums determine a family of natural numbers. -/
theorem fin_prefix_sum_injective {d : ℕ} (f g : Fin d → ℕ)
    (h : ∀ i, (∑ j ∈ Finset.Iic i, f j) = ∑ j ∈ Finset.Iic i, g j) : f=g := by
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have hset : Finset.Iic i = insert i (Finset.Iio i) := by ext; simp
    have hprev : (∑ j ∈ Finset.Iio i, f j) = ∑ j ∈ Finset.Iio i, g j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact ih j (Finset.mem_Iio.mp hj)
    have hh := h i
    rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp), hprev] at hh
    omega

def pullGapSet {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (S : Finset (Fin n)) : Finset (GapUniverse r (r+1) (tupleGap p)) :=
  S.map (tupleGapEquiv p hp).symm.toEmbedding

@[simp] theorem mem_pullGapSet {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (S : Finset (Fin n)) (x : GapUniverse r (r+1) (tupleGap p)) :
    x ∈ pullGapSet p hp S ↔ tupleGapMap p x ∈ S := by
  simp [pullGapSet, tupleGapEquiv]

@[simp] theorem map_pullGapSet {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (S : Finset (Fin n)) :
    (pullGapSet p hp S).map (tupleGapEquiv p hp).toEmbedding = S := by
  ext x
  simp only [pullGapSet, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]

@[simp] theorem pullGapSet_map {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (T : Finset (GapUniverse r (r+1) (tupleGap p))) :
    pullGapSet p hp (T.map (tupleGapEquiv p hp).toEmbedding) = T := by
  ext x
  simp only [pullGapSet, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem pullGapSet_lower_card {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (S : Finset (Fin n)) (hS : ∀ i, p i ∈ S) (i : Fin r) :
    (S.filter fun x => x < p i).card =
      i.val + ∑ j ∈ Finset.Iic i.castSucc, (gapDecode (pullGapSet p hp S) j).card := by
  have hT : ∀ a, Sum.inl a ∈ pullGapSet p hp S := by
    intro a
    simpa only [mem_pullGapSet, tupleGapMap] using hS a
  have h := gapEncoded_lower_card p hp (gapDecode (pullGapSet p hp S)) i
  rwa [gapEncode_decode _ hT, map_pullGapSet] at h

theorem pullGapSet_total_card {n r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (S : Finset (Fin n)) (hS : ∀ i, p i ∈ S) :
    S.card = r + ∑ j, (gapDecode (pullGapSet p hp S) j).card := by
  have hT : ∀ a, Sum.inl a ∈ pullGapSet p hp S := by
    intro a
    simpa only [mem_pullGapSet, tupleGapMap] using hS a
  have h := card_gapEncode (r := r) (gapDecode (pullGapSet p hp S))
  rw [gapEncode_decode _ hT] at h
  simpa only [pullGapSet, Finset.card_map] using h

theorem taggedRankEvent_iff_gapEvent {n l r : ℕ} (p : Fin r → Fin n)
    (hp : StrictMono p) (v : Fin r → Fin l) (hv : StrictMono v)
    (S : FixedSubset (Fin n) l) :
    taggedRankEvent p v S ↔ gapEvent (tupleGap v) (pullGapSet p hp S.val) := by
  constructor
  · intro h
    have hS : ∀ i, p i ∈ S.val := fun i => (slotAtRank_eq_iff S (v i) (p i)).mp (h i) |>.1
    have hbefore : ∀ i, (S.val.filter fun x => x < p i).card = (v i).val :=
      fun i => (slotAtRank_eq_iff S (v i) (p i)).mp (h i) |>.2
    refine ⟨?_, ?_⟩
    · intro i
      simpa only [mem_pullGapSet, tupleGapMap] using hS i
    · have heq : (fun j => (gapDecode (pullGapSet p hp S.val) j).card) = tupleGap v := by
        apply fin_prefix_sum_injective
        intro j
        induction j using Fin.lastCases with
        | last =>
          have htot := pullGapSet_total_card p hp S.val hS
          have hvtot := tupleGap_total v hv
          have hset : Finset.Iic (Fin.last r) = Finset.univ := by ext; simp [Fin.le_last]
          rw [hset]
          rw [S.property] at htot
          omega
        | cast i =>
          have hpre := pullGapSet_lower_card p hp S.val hS i
          rw [hbefore i] at hpre
          have hvpre := tupleGap_prefix v hv i
          omega
      intro j
      exact congrFun heq j
  · intro h
    have hS : ∀ i, p i ∈ S.val := by
      intro i
      simpa only [mem_pullGapSet, tupleGapMap] using h.1 i
    intro i
    apply (slotAtRank_eq_iff S (v i) (p i)).2
    refine ⟨hS i, ?_⟩
    rw [pullGapSet_lower_card p hp S.val hS i]
    simp_rw [h.2]
    exact tupleGap_prefix v hv i

instance taggedRankEvent_decidable {n l r : ℕ} (p : Fin r → Fin n)
    (v : Fin r → Fin l) (S : FixedSubset (Fin n) l) : Decidable (taggedRankEvent p v S) := by
  unfold taggedRankEvent
  infer_instance

/-- The actual event of seeing specified source slots at specified output ranks
is in bijection with independent choices of the retained slots in each gap. -/
def rankGapEventEquiv {n l r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (v : Fin r → Fin l) (hv : StrictMono v) :
    {S : FixedSubset (Fin n) l // taggedRankEvent p v S} ≃
      {T : Finset (GapUniverse r (r+1) (tupleGap p)) // gapEvent (tupleGap v) T} where
  toFun S := ⟨pullGapSet p hp S.val.val, (taggedRankEvent_iff_gapEvent p hp v hv S.val).mp S.property⟩
  invFun T :=
    let S : FixedSubset (Fin n) l := ⟨T.val.map (tupleGapEquiv p hp).toEmbedding, by
      rw [Finset.card_map, card_of_gapEvent T.val T.property, tupleGap_total v hv]⟩
    ⟨S, (taggedRankEvent_iff_gapEvent p hp v hv S).mpr (by
      change gapEvent (tupleGap v) (pullGapSet p hp (T.val.map (tupleGapEquiv p hp).toEmbedding))
      rw [pullGapSet_map]
      exact T.property)⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_pullGapSet p hp S.val.val
  right_inv T := by
    apply Subtype.ext
    exact pullGapSet_map p hp T.val

theorem card_taggedRankEvent {n l r : ℕ} (p : Fin r → Fin n) (hp : StrictMono p)
    (v : Fin r → Fin l) (hv : StrictMono v) :
    Fintype.card {S : FixedSubset (Fin n) l // taggedRankEvent p v S} =
      ∏ j, (tupleGap p j).choose (tupleGap v j) := by
  classical
  rw [Fintype.card_congr (rankGapEventEquiv p hp v hv), card_gapEvent]

/-- Exact counting formula, including impossible rank/gap profiles. -/
theorem subsetRankKernel_choose_formula {n l r : ℕ} (hl : l ≤ n)
    (p : Fin r → Fin n) (hp : StrictMono p) (v : Fin r → Fin l) (hv : StrictMono v) :
    subsetRankKernel hl p v =
      (∏ j, ((tupleGap p j).choose (tupleGap v j) : ℝ)) / (n.choose l : ℝ) := by
  classical
  unfold subsetRankKernel
  simp only [uniformSubsetLaw, Fintype.card_fin]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    ← Fintype.card_subtype, card_taggedRankEvent p hp v hv, Nat.cast_prod]
  ring

theorem gapEvent_conditional_choose {r d : ℕ} (g z : Fin d → ℕ)
    (p : ℝ) (hp : p ∈ Set.Ioo 0 1) :
    (∑ S : Finset (GapUniverse r d g), if gapEvent z S then subsetWeight p S else 0) /
      binomialMass (r+∑ i, g i) p (r+∑ i, z i) =
    (∏ i, ((g i).choose (z i):ℝ)) /
      ((r+∑ i, g i).choose (r+∑ i, z i) : ℝ) := by
  classical
  have hcount : (∑ S : Finset (GapUniverse r d g),
      if gapEvent z S then (1:ℝ) else 0) = ∏ i, ((g i).choose (z i):ℝ) := by
    rw [Finset.sum_boole, ← Fintype.card_subtype, card_gapEvent, Nat.cast_prod]
  have hnum : (∑ S : Finset (GapUniverse r d g), if gapEvent z S then subsetWeight p S else 0) =
      (∏ i, ((g i).choose (z i):ℝ)) *
        (p^(r+∑ i, z i)*(1-p)^(r+∑ i, g i-(r+∑ i, z i))) := by
    rw [← hcount, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs with hS
    · simp only [one_mul, subsetWeight, card_of_gapEvent S hS,
        Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
    · exact (zero_mul _).symm
  rw [hnum, binomialMass]
  have hp0 : p ≠ 0 := hp.1.ne'
  have hq0 : 1-p ≠ 0 := by linarith [hp.2]
  rw [mul_assoc, mul_div_mul_right _ _ (mul_ne_zero (pow_ne_zero _ hp0) (pow_ne_zero _ hq0))]

/-- Conditional product formula for the kernel defined from actual retained
subsets, not an assumed auxiliary kernel. Source the initial-pair construction 50–62. -/
theorem subsetRankKernel_binomial_formula {n l r : ℕ} (hl : l ≤ n)
    (p : Fin r → Fin n) (hp : StrictMono p) (v : Fin r → Fin l) (hv : StrictMono v)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 1) :
    subsetRankKernel hl p v = θ^r / binomialMass n θ l *
      ∏ j, binomialMass (tupleGap p j) θ (tupleGap v j) := by
  classical
  by_cases hz : ∀ j, tupleGap v j ≤ tupleGap p j
  · have h1 := gapEvent_conditional_choose (r := r) (tupleGap p) (tupleGap v) θ hθ
    have h2 := gapEvent_conditional_formula (r := r) (tupleGap p) (tupleGap v) hz θ
    rw [tupleGap_total p hp, tupleGap_total v hv] at h1 h2
    rw [subsetRankKernel_choose_formula hl p hp v hv, ← h1, h2]
  · push Not at hz
    obtain ⟨j,hj⟩ := hz
    have hc : (tupleGap p j).choose (tupleGap v j) = 0 := Nat.choose_eq_zero_of_lt hj
    have hz1 : (∏ j, ((tupleGap p j).choose (tupleGap v j) : ℝ))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hc])
    have hz2 : (∏ j, binomialMass (tupleGap p j) θ (tupleGap v j))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [binomialMass, hc])
    rw [subsetRankKernel_choose_formula hl p hp v hv, hz1, hz2]
    simp

end TraceReconstruction

namespace TraceReconstruction

/-- Twice the coarse period gaps (endpoints are half-integral before doubling). -/
def coarsePeriodGap {u r : ℕ} (j : Fin r → Fin u) (i : Fin (r+1)) : ℕ :=
  2 * tupleGap j i + if i = 0 ∨ i = Fin.last r then 1 else 2

theorem coarsePeriodGap_pos {u r : ℕ} (j : Fin r → Fin u) (i : Fin (r+1)) :
    1 ≤ coarsePeriodGap j i := by
  unfold coarsePeriodGap
  split_ifs <;> omega

theorem coarsePeriodGap_sum {u r : ℕ} (hr : 0 < r) (j : Fin r → Fin u)
    (hj : StrictMono j) : ∑ i, coarsePeriodGap j i = 2*u := by
  classical
  have hc : (∑ i : Fin (r+1), if i = 0 ∨ i = Fin.last r then 1 else 2) = 2*r := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    rw [Fin.sum_univ_succ]
    simp only [true_or, ↓reduceIte, Fin.succ_ne_zero, false_or]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_last, ↓reduceIte]
    have hx (i : Fin d) : i.castSucc.succ ≠ Fin.last (d+1) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
      omega
    simp only [hx, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    omega
  simp only [coarsePeriodGap, Finset.sum_add_distrib, ← Finset.mul_sum]
  have ht := tupleGap_total j hj
  omega

theorem coarsePeriodGap_le {u r : ℕ} (hr : 0 < r) (j : Fin r → Fin u)
    (hj : StrictMono j) (i : Fin (r+1)) : coarsePeriodGap j i ≤ 2*u := by
  rw [← coarsePeriodGap_sum hr j hj]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem tupleGap_injective {n r : ℕ} {p q : Fin r → Fin n}
    (hp : StrictMono p) (hq : StrictMono q) (h : tupleGap p = tupleGap q) : p=q := by
  funext i
  apply Fin.ext
  have hp' := tupleGap_prefix p hp i
  have hq' := tupleGap_prefix q hq i
  rw [h] at hp'
  omega

theorem coarsePeriodGap_injective {u r : ℕ} {j k : Fin r → Fin u}
    (hj : StrictMono j) (hk : StrictMono k) (h : coarsePeriodGap j = coarsePeriodGap k) :
    j=k := by
  apply tupleGap_injective hj hk
  funext i
  have hi := congrFun h i
  unfold coarsePeriodGap at hi
  omega

/-- Actual defect slot in a period, with zero-based period and slot indices. -/
def periodSlot {u m : ℕ} (off : Fin u → Fin m) (j : Fin u) : Fin (u*m) :=
  ⟨j.val*m + (off j).val, by
    have h := (off j).isLt
    have h' := Nat.mul_le_mul_right m (Nat.succ_le_of_lt j.isLt)
    nlinarith⟩

theorem periodSlot_strictMono {u m : ℕ} (off : Fin u → Fin m) :
    StrictMono (periodSlot off) := by
  intro j k hjk
  change j.val*m + (off j).val < k.val*m + (off k).val
  have hjk' : j.val+1 ≤ k.val := hjk
  have ho := (off j).isLt
  have hm := Nat.mul_le_mul_right m hjk'
  nlinarith

theorem tupleGap_zero {n r : ℕ} (p : Fin (r+1) → Fin n) :
    tupleGap p 0 = (p 0).val := by
  have he : (0 : Fin (r+2)) = (0 : Fin (r+1)).castSucc := rfl
  unfold tupleGap
  rw [tupleLower_zero, Nat.sub_zero, he, tupleUpper_castSucc]

theorem tupleGap_last {n r : ℕ} (p : Fin (r+1) → Fin n) :
    tupleGap p (Fin.last (r+1)) = n - ((p (Fin.last r)).val+1) := by
  unfold tupleGap
  rw [tupleUpper_last, ← Fin.succ_last, tupleLower_succ]

theorem tupleGap_middle {n r : ℕ} (p : Fin (r+1) → Fin n) (i : Fin r) :
    tupleGap p i.castSucc.succ = (p i.succ).val - ((p i.castSucc).val+1) := by
  unfold tupleGap
  rw [tupleLower_succ, Fin.succ_castSucc, tupleUpper_castSucc]

theorem coarsePeriodGap_zero {u r : ℕ} (j : Fin (r+1) → Fin u) :
    coarsePeriodGap j 0 = 2*(j 0).val+1 := by
  simp only [coarsePeriodGap, tupleGap_zero, true_or, ↓reduceIte]

theorem coarsePeriodGap_last {u r : ℕ} (j : Fin (r+1) → Fin u) :
    coarsePeriodGap j (Fin.last (r+1)) = 2*(u-((j (Fin.last r)).val+1))+1 := by
  simp only [coarsePeriodGap, tupleGap_last, or_true, ↓reduceIte]

theorem coarsePeriodGap_middle {u r : ℕ} (j : Fin (r+1) → Fin u) (i : Fin r) :
    coarsePeriodGap j i.castSucc.succ = 2*((j i.succ).val-((j i.castSucc).val+1))+2 := by
  have hn : i.castSucc.succ ≠ Fin.last (r+1) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
    omega
  simp only [coarsePeriodGap, tupleGap_middle, Fin.succ_ne_zero, hn, or_self, ↓reduceIte]

/-- Actual bounded defect displacements give the O(1) gap errors of the initial-pair construction. -/
theorem period_gap_rounding {u m r : ℕ} (hr : 0 < r)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j : Fin r → Fin u) (hj : StrictMono j) (i : Fin (r+1)) :
    |(tupleGap (periodSlot off ∘ j) i:ℝ) - (m:ℝ)*coarsePeriodGap j i/2| ≤ 4 := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hp := (periodSlot_strictMono off).comp hj
  induction i using Fin.cases with
  | zero =>
    rw [tupleGap_zero, coarsePeriodGap_zero]
    simp only [Function.comp_apply, periodSlot, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
    have offset_bound := abs_le.mp (hoff (j 0))
    apply abs_le.mpr
    constructor <;> linarith
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, tupleGap_last, coarsePeriodGap_last]
      have hcut : (j (Fin.last d)).val+1 ≤ u := Nat.succ_le_of_lt (j _).isLt
      have hslot : ((periodSlot off ∘ j) (Fin.last d)).val+1 ≤ u*m :=
        Nat.succ_le_of_lt (((periodSlot off ∘ j) (Fin.last d))).isLt
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [Nat.cast_sub hslot, Nat.cast_sub hcut]
      simp only [Function.comp_apply, periodSlot, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      have h := abs_le.mp (hoff (j (Fin.last d)))
      apply abs_le.mpr
      constructor <;> linarith
    | cast i =>
      rw [tupleGap_middle, coarsePeriodGap_middle]
      have hcut : (j i.castSucc).val+1 ≤ (j i.succ).val := hj (Fin.castSucc_lt_succ (i := i))
      have hslot : ((periodSlot off ∘ j) i.castSucc).val+1 ≤
          ((periodSlot off ∘ j) i.succ).val := hp (Fin.castSucc_lt_succ (i := i))
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [Nat.cast_sub hslot, Nat.cast_sub hcut]
      simp only [Function.comp_apply, periodSlot, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      have h := abs_le.mp (hdiff (j i.succ) (j i.castSucc))
      apply abs_le.mpr
      constructor <;> linarith

end TraceReconstruction

namespace TraceReconstruction

/-- An increasing tuple enumerates a monomial's distinct observed ranks. -/
abbrev IncreasingTuple (n r : ℕ) := {v : Fin r → Fin n // StrictMono v}

noncomputable instance increasingTupleFintype (n r : ℕ) : Fintype (IncreasingTuple n r) :=
  Fintype.ofFinite _

theorem tupleGap_le_remainder {n r : ℕ} (v : IncreasingTuple n r) (i : Fin (r+1)) :
    tupleGap v.val i ≤ n-r := by
  have ht := tupleGap_total v.val v.property
  have hle : tupleGap v.val i ≤ ∑ j, tupleGap v.val j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

def rankGapProfile {n r : ℕ} (σ : Equiv.Perm (Fin (r+1))) (v : IncreasingTuple n r) :
    Fin (r+1) → Fin (n-r+1) :=
  fun i => ⟨tupleGap v.val (σ i), Nat.lt_succ_of_le (tupleGap_le_remainder v (σ i))⟩

theorem rankGapProfile_sum {n r : ℕ} (σ : Equiv.Perm (Fin (r+1)))
    (v : IncreasingTuple n r) : ∑ i, (rankGapProfile σ v i).val = n-r := by
  change (∑ i, tupleGap v.val (σ i)) = _
  rw [Equiv.sum_comp σ]
  have ht := tupleGap_total v.val v.property
  omega

theorem rankGapProfile_injective {n r : ℕ} (σ : Equiv.Perm (Fin (r+1))) :
    Function.Injective (rankGapProfile (n := n) σ) := by
  intro v w h
  apply Subtype.ext
  funext i
  apply Fin.ext
  have he : tupleGap v.val = tupleGap w.val := by
    funext j
    have hh := congrArg Fin.val (congrFun h (σ.symm j))
    simpa only [rankGapProfile, Equiv.apply_symm_apply] using hh
  have hv := tupleGap_prefix v.val v.property i
  have hw := tupleGap_prefix w.val w.property i
  rw [he] at hv
  omega

/-- Summing nonnegative kernels over actual profiles may drop any remaining constraints. -/
theorem sum_injective_profile_le {α β : Type*} [Fintype α] [Fintype β]
    (profile : α → β) (hinj : Function.Injective profile)
    (P : β → Prop) [DecidablePred P] (hp : ∀ a, P (profile a))
    (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (profile a)) ≤ ∑ b, if P b then f b else 0 := by
  classical
  let S := Finset.univ.image profile
  have hs : ∀ b ∈ S, P b := by
    intro b hb
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hb
    exact hp a
  calc
    _ = ∑ b ∈ S, f b := by
      symm
      exact Finset.sum_image (fun _ _ _ _ h => hinj h)
    _ = ∑ b ∈ S, if P b then f b else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [ite_eq_left (hs b hb)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro b _ _
      split_ifs
      · exact hf b
      · rfl)

/-- The actual conditional rank kernel, summed over distinct observed ranks,
reduces to the constrained finite product estimate with any eliminated gap. -/
theorem subsetRankKernel_cross_le {n l r : ℕ} (hl : l ≤ n)
    (p q : Fin r → Fin n) (hp : StrictMono p) (hq : StrictMono q)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 1) (e : Fin (r+1))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ k : Fin (l-r+1),
      binomialMass (tupleGap p e) θ k * binomialMass (tupleGap q e) θ k ≤ M) :
    (∑ v : IncreasingTuple l r,
      subsetRankKernel hl p v.val * subsetRankKernel hl q v.val) ≤
      (θ^r / binomialMass n θ l)^2 * M *
        ∏ i : Fin r, ∑ k : Fin (l-r+1),
          binomialMass (tupleGap p (Equiv.swap 0 e i.succ)) θ k *
          binomialMass (tupleGap q (Equiv.swap 0 e i.succ)) θ k := by
  classical
  let σ : Equiv.Perm (Fin (r+1)) := Equiv.swap 0 e
  let f : Fin (r+1) → Fin (l-r+1) → ℝ := fun i k => binomialMass (tupleGap p (σ i)) θ k
  let g : Fin (r+1) → Fin (l-r+1) → ℝ := fun i k => binomialMass (tupleGap q (σ i)) θ k
  have hf : ∀ i k, 0 ≤ f i k := by
    intro i k
    dsimp [f,binomialMass]
    positivity [hθ.1.le, sub_nonneg.mpr hθ.2.le]
  have hg : ∀ i k, 0 ≤ g i k := by
    intro i k
    dsimp [g,binomialMass]
    positivity [hθ.1.le, sub_nonneg.mpr hθ.2.le]
  let F (z : Fin (r+1) → Fin (l-r+1)) := (∏ i, f i (z i)) * (∏ i, g i (z i))
  have hF : ∀ z, 0 ≤ F z := by
    intro z
    exact mul_nonneg (Finset.prod_nonneg fun i _ => hf i _) (Finset.prod_nonneg fun i _ => hg i _)
  have hpoint (v : IncreasingTuple l r) :
      subsetRankKernel hl p v.val * subsetRankKernel hl q v.val =
        (θ^r / binomialMass n θ l)^2 * F (rankGapProfile σ v) := by
    rw [subsetRankKernel_binomial_formula hl p hp v.val v.property θ hθ,
      subsetRankKernel_binomial_formula hl q hq v.val v.property θ hθ]
    dsimp only [F,f,g,rankGapProfile]
    rw [Equiv.prod_comp σ (fun j => binomialMass (tupleGap p j) θ (tupleGap v.val j)),
      Equiv.prod_comp σ (fun j => binomialMass (tupleGap q j) θ (tupleGap v.val j))]
    ring
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (θ^r / binomialMass n θ l)^2 *
        ∑ z : Fin (r+1) → Fin (l-r+1), if ∑ i, (z i).val = l-r then F z else 0 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sum_injective_profile_le (rankGapProfile σ) (rankGapProfile_injective σ)
        (fun z => ∑ i, (z i).val = l-r) (rankGapProfile_sum σ) F hF
    _ ≤ (θ^r / binomialMass n θ l)^2 * (M * ∏ i : Fin r, ∑ k, f i.succ k * g i.succ k) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact constrained_cross_kernel_le r (l-r) f g hf hg M hM (by
        intro k
        simpa only [f,g,σ,Equiv.swap_apply_left] using hbound k)
    _ = _ := by dsimp [f,g,σ]; ring

end TraceReconstruction

namespace TraceReconstruction

theorem finite_geometric_distance (S : Finset ℤ) (a : ℤ) {ρ : ℝ}
    (hρ : ρ∈Set.Ico 0 1) :
    (∑ z ∈ S, ρ^(z-a).natAbs) ≤ 2/(1-ρ) := by
  have hs : Summable (fun n:ℕ => ρ^n) := summable_geometric_of_lt_one hρ.1 hρ.2
  have hnat : Summable (fun n:ℕ => ρ^((n:ℤ).natAbs)) := by simpa using hs
  have hneg : Summable (fun n:ℕ => ρ^((-(n:ℤ)).natAbs)) := by simpa using hs
  have hz : Summable (fun z:ℤ => ρ^z.natAbs) := hnat.of_nat_of_neg hneg
  have ht : (∑' z:ℤ, ρ^z.natAbs)=2/(1-ρ)-1 := by
    rw [Summable.tsum_of_nat_of_neg (f := fun z : ℤ => ρ^z.natAbs) hnat hneg]
    simp only [Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_zero, pow_zero]
    rw [tsum_geometric_of_lt_one hρ.1 hρ.2]
    ring
  have hshift : Summable (fun z:ℤ => ρ^(z-a).natAbs) :=
    hz.comp_injective (sub_left_injective)
  have hts : (∑' z:ℤ, ρ^(z-a).natAbs)=(∑' z:ℤ, ρ^z.natAbs) :=
    (Equiv.subRight a).tsum_eq (fun z:ℤ => ρ^z.natAbs)
  have hbound := hshift.sum_le_tsum S (fun z _ => pow_nonneg hρ.1 _)
  rw [hts,ht] at hbound
  linarith

theorem finite_gaussian_distance (S : Finset ℤ) (a : ℤ) {c : ℝ}
    (hc : 0<c) :
    (∑ z ∈ S, Real.exp (-c*((z:ℝ)-a)^2)) ≤ 2/(1-Real.exp (-c)) := by
  apply le_trans _ (finite_geometric_distance S a ⟨(Real.exp_pos _).le, by
    rw [Real.exp_lt_one_iff]; linarith⟩)
  apply Finset.sum_le_sum
  intro z _
  have hcast (w : ℤ) : (w.natAbs:ℝ)=|(w:ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have he : Real.exp (-c)^(z-a).natAbs = Real.exp (-c*|(z:ℝ)-a|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [mul_comm, hcast, Int.cast_sub]
  rw [he]
  apply Real.exp_le_exp.mpr
  have hd : |(z:ℝ)-a| ≤ ((z:ℝ)-a)^2 := by
    have hnat : (z-a).natAbs ≤ (z-a).natAbs^2 := by
      nlinarith only [Nat.zero_le (z-a).natAbs, (Nat.mul_self_le_mul_self_iff.mpr (show 0≤(z-a).natAbs by omega))]
    have hr : ((z-a).natAbs:ℝ) ≤ ((z-a).natAbs:ℝ)^2 := by exact_mod_cast hnat
    simpa only [hcast, Int.cast_sub, sq_abs] using hr
  nlinarith [mul_le_mul_of_nonneg_left hd hc.le]

end TraceReconstruction

namespace TraceReconstruction

theorem fin_geometric_distance (N : ℕ) (a : ℤ) {ρ : ℝ} (hρ : ρ∈Set.Ico 0 1) :
    (∑ z : Fin N, ρ^((z.val:ℤ)-a).natAbs) ≤ 2/(1-ρ) := by
  let e : ℕ ↪ ℤ := ⟨Int.ofNat, Nat.cast_injective⟩
  have h := finite_geometric_distance ((Finset.range N).map e) a hρ
  rw [Finset.sum_map] at h
  rw [Fin.sum_univ_eq_sum_range (fun z:ℕ => ρ^((z:ℤ)-a).natAbs) N]
  exact h

theorem coarse_laplace_sum_with_zero {h : ℝ} (hh : 0<h) (h1 : h≤1) (M : ℕ) :
    (∑ k : Fin (M+1), (Real.sqrt (k.val:ℝ))⁻¹ * Real.exp (-h*(k.val:ℝ))) ≤
      6/Real.sqrt h := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_mul, zero_add]
  have hc := coarse_laplace_sum hh h1 M
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    (Real.sqrt (k+1:ℝ))⁻¹ * Real.exp (-h*(k+1:ℝ))) M] at hc
  simpa only [Fin.val_succ, Nat.cast_add, Nat.cast_one] using hc

/-- The total constraint eliminates one coarse gap with no cost in its size.
The zero-extension of x^(-1/2) avoids any singular integral convention. -/
theorem coarse_constrained_inverse_sum (r U : ℕ) {h : ℝ} (hh : 0<h) (h1 : h≤1) :
    (∑ γ : Fin (r+1) → Fin (U+1),
      if ∑ i, (γ i).val=U then ∏ i : Fin r, (Real.sqrt ((γ i.succ).val:ℝ))⁻¹ else 0) ≤
      Real.exp (h*U) * (6/Real.sqrt h)^r := by
  classical
  let f : Fin (r+1) → Fin (U+1) → ℝ := Fin.cases
    (fun k => Real.exp (-h*(k.val:ℝ)))
    (fun _ k => (Real.sqrt (k.val:ℝ))⁻¹ * Real.exp (-h*(k.val:ℝ)))
  have hf : ∀ i k, 0≤f i k := by
    intro i k
    refine Fin.cases ?_ (fun _ => ?_) i <;> dsimp [f] <;> positivity
  have hf0 : ∀ k, f 0 k≤1 := by
    intro k
    change Real.exp (-h*(k.val:ℝ))≤1
    apply Real.exp_le_one_iff.mpr
    nlinarith [show (0:ℝ)≤k.val by positivity]
  have hid (γ : Fin (r+1) → Fin (U+1)) (hγ : ∑ i, (γ i).val=U) :
      ∏ i : Fin r, (Real.sqrt ((γ i.succ).val:ℝ))⁻¹ =
        Real.exp (h*U) * ∏ i, f i (γ i) := by
    have hγr : ((γ 0).val:ℝ) + ∑ i:Fin r, ((γ i.succ).val:ℝ)=(U:ℝ) := by
      exact_mod_cast (show (γ 0).val+∑ i:Fin r, (γ i.succ).val=U by
        simpa only [Fin.sum_univ_succ] using hγ)
    simp only [Fin.prod_univ_succ, f, Fin.cases_zero, Fin.cases_succ,
      Finset.prod_mul_distrib, ← Real.exp_sum]
    have he : Real.exp (h*U) * Real.exp (-h*((γ 0).val:ℝ)) *
        Real.exp (∑ i:Fin r, -h*((γ i.succ).val:ℝ))=1 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Finset.mul_sum]
      rw [show h*(U:ℝ)+ -h*((γ 0).val:ℝ)+ -h*∑ i:Fin r, ((γ i.succ).val:ℝ)=0 by
        rw [← hγr]
        ring]
      exact Real.exp_zero
    calc
      _ = (Real.exp (h*U) * Real.exp (-h*((γ 0).val:ℝ)) *
        Real.exp (∑ i:Fin r, -h*((γ i.succ).val:ℝ))) *
          (∏ i:Fin r, (Real.sqrt ((γ i.succ).val:ℝ))⁻¹) := by rw [he, one_mul]
      _ = _ := by ring
  have hrew : (∑ γ : Fin (r+1) → Fin (U+1),
      if ∑ i, (γ i).val=U then ∏ i : Fin r, (Real.sqrt ((γ i.succ).val:ℝ))⁻¹ else 0) =
      Real.exp (h*U) * ∑ γ : Fin (r+1) → Fin (U+1),
        if ∑ i, (γ i).val=U then ∏ i, f i (γ i) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    split_ifs with hγ
    · exact hid γ hγ
    · simp
  rw [hrew]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply (constrained_sum_product_le r U f hf 1 (by norm_num) hf0).trans
  simp only [one_mul]
  calc
    _ ≤ ∏ _i : Fin r, (6/Real.sqrt h) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact Finset.sum_nonneg (fun k _ => hf i.succ k)
      · intro i _; exact coarse_laplace_sum_with_zero hh h1 U
    _ = _ := by simp [div_pow]

/-- The squared norm of an aggregate equals the sum of the cross-kernels. -/
theorem sum_sq_sum_kernel {α β : Type*} [Fintype β] (S : Finset α) (K : α → β → ℝ) :
    (∑ z, (∑ a ∈ S, K a z)^2) =
      ∑ a ∈ S, ∑ b ∈ S, ∑ z, K a z*K b z := by
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

/-- Schur summation over all pairs of coarse-gap profiles, retaining the
largest-gap total constraint before dropping other restrictions. -/
theorem coarse_kernel_square_sum {β : Type*} [Fintype β] (r U : ℕ)
    (S : Finset (Fin (r+1) → Fin (U+1)))
    (K : (Fin (r+1) → Fin (U+1)) → β → ℝ) {M ρ h : ℝ}
    (hM : 0≤M) (hρ : ρ∈Set.Ico 0 1) (hh : 0<h) (h1 : h≤1)
    (hS : ∀ γ∈S, ∑ i, (γ i).val=U)
    (hcross : ∀ γ∈S, ∀ γ'∈S, (∑ z, K γ z*K γ' z) ≤
      M * ∏ i:Fin r, ((Real.sqrt ((γ i.succ).val:ℝ))⁻¹ *
        ρ^(((γ' i.succ).val:ℤ)-(γ i.succ).val).natAbs)) :
    (∑ z, (∑ γ∈S, K γ z)^2) ≤
      M * (2/(1-ρ))^r * Real.exp (h*U) * (6/Real.sqrt h)^r := by
  classical
  let A (γ : Fin (r+1) → Fin (U+1)) :=
    ∏ i:Fin r, (Real.sqrt ((γ i.succ).val:ℝ))⁻¹
  have hA (γ) : 0≤A γ := by dsimp [A]; positivity
  have hinner (γ : Fin (r+1) → Fin (U+1)) :
      (∑ γ'∈S, ∏ i:Fin r, ρ^(((γ' i.succ).val:ℤ)-(γ i.succ).val).natAbs) ≤
        (2/(1-ρ))^r := by
    let f : Fin (r+1) → Fin (U+1) → ℝ := Fin.cases (fun _ => 1)
      (fun i k => ρ^((k.val:ℤ)-(γ i.succ).val).natAbs)
    have hf : ∀ i k, 0≤f i k := by
      intro i k
      refine Fin.cases ?_ (fun _ => ?_) i
      · norm_num [f]
      · exact pow_nonneg hρ.1 _
    have hsub : (∑ γ'∈S, ∏ i:Fin r, ρ^(((γ' i.succ).val:ℤ)-(γ i.succ).val).natAbs) ≤
        ∑ γ' : Fin (r+1) → Fin (U+1), if ∑ i, (γ' i).val=U then ∏ i, f i (γ' i) else 0 := by
      calc
        _ = ∑ γ'∈S, if ∑ i, (γ' i).val=U then ∏ i, f i (γ' i) else 0 := by
          apply Finset.sum_congr rfl
          intro γ' hγ'
          simp only [hS γ' hγ', ↓reduceIte, Fin.prod_univ_succ, f, Fin.cases_zero,
            Fin.cases_succ, one_mul]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
          intro γ' _ _
          split_ifs
          · exact Finset.prod_nonneg (fun i _ => hf i _)
          · rfl)
    apply hsub.trans
    apply (constrained_sum_product_le r U f hf 1 (by norm_num) (by intro k; rfl)).trans
    simp only [one_mul]
    calc
      _ ≤ ∏ _i:Fin r, (2/(1-ρ)) := by
        apply Finset.prod_le_prod₀
        · intro i _; exact Finset.sum_nonneg (fun k _ => hf i.succ k)
        · intro i _; exact fin_geometric_distance (U+1) ((γ i.succ).val:ℤ) hρ
      _ = _ := by simp [div_pow]
  have houter : (∑ γ∈S, A γ) ≤ Real.exp (h*U)*(6/Real.sqrt h)^r := by
    apply le_trans _ (coarse_constrained_inverse_sum r U hh h1)
    calc
      _ = ∑ γ∈S, if ∑ i, (γ i).val=U then A γ else 0 := by
        apply Finset.sum_congr rfl
        intro γ hγ
        rw [ite_eq_left (hS γ hγ)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro γ _ _
        split_ifs
        · exact hA γ
        · rfl)
  rw [sum_sq_sum_kernel]
  calc
    _ ≤ ∑ γ∈S, ∑ γ'∈S, M * ∏ i:Fin r, ((Real.sqrt ((γ i.succ).val:ℝ))⁻¹ *
        ρ^(((γ' i.succ).val:ℤ)-(γ i.succ).val).natAbs) := by
      exact Finset.sum_le_sum (fun γ hγ => Finset.sum_le_sum (fun γ' hγ' => hcross γ hγ γ' hγ'))
    _ = ∑ γ∈S, M*A γ * ∑ γ'∈S, ∏ i:Fin r, ρ^(((γ' i.succ).val:ℤ)-(γ i.succ).val).natAbs := by
      simp only [Finset.prod_mul_distrib, A, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ γ∈S, M*A γ*(2/(1-ρ))^r := by
      exact Finset.sum_le_sum (fun γ _ => mul_le_mul_of_nonneg_left (hinner γ) (mul_nonneg hM (hA γ)))
    _ = M*(2/(1-ρ))^r * ∑ γ∈S, A γ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ M*(2/(1-ρ))^r * (Real.exp (h*U)*(6/Real.sqrt h)^r) := by
      apply mul_le_mul_of_nonneg_left houter
      exact mul_nonneg hM (pow_nonneg (div_nonneg (by norm_num) (by linarith [hρ.2])) _)
    _ = _ := by ring

theorem coarse_kernel_rectangular_sum {β : Type*} [Fintype β] (r U : ℕ)
    (S T : Finset (Fin (r+1) → Fin (U+1)))
    (K G : (Fin (r+1) → Fin (U+1)) → β → ℝ) {M ρ h : ℝ}
    (hM : 0≤M) (hρ : ρ∈Set.Ico 0 1) (hh : 0<h) (h1 : h≤1)
    (hS : ∀ γ∈S, ∑ i, (γ i).val=U)
    (hT : ∀ γ∈T, ∑ i, (γ i).val=U)
    (hcross : ∀ γ∈S, ∀ γ'∈T, (∑ z, K γ z*G γ' z) ≤
      M * ∏ i:Fin r, ((Real.sqrt ((γ i.succ).val:ℝ))⁻¹ *
        ρ^(((γ' i.succ).val:ℤ)-(γ i.succ).val).natAbs)) :
    (∑ γ∈S, ∑ γ'∈T, ∑ z, K γ z*G γ' z) ≤
      M * (2/(1-ρ))^r * Real.exp (h*U) * (6/Real.sqrt h)^r := by
  classical
  let A (γ : Fin (r+1) → Fin (U+1)) :=
    ∏ i:Fin r, (Real.sqrt ((γ i.succ).val:ℝ))⁻¹
  have hA (γ) : 0≤A γ := by dsimp [A]; positivity
  have hinner (γ : Fin (r+1) → Fin (U+1)) :
      (∑ γ'∈T, ∏ i:Fin r, ρ^(((γ' i.succ).val:ℤ)-(γ i.succ).val).natAbs) ≤
        (2/(1-ρ))^r := by
    let f : Fin (r+1) → Fin (U+1) → ℝ := Fin.cases (fun _ => 1)
      (fun i k => ρ^((k.val:ℤ)-(γ i.succ).val).natAbs)
    have hf : ∀ i k, 0≤f i k := by
      intro i k
      refine Fin.cases ?_ (fun _ => ?_) i
      · norm_num [f]
      · exact pow_nonneg hρ.1 _
    have hsub : (∑ γ'∈T, ∏ i:Fin r, ρ^(((γ' i.succ).val:ℤ)-(γ i.succ).val).natAbs) ≤
        ∑ γ' : Fin (r+1) → Fin (U+1), if ∑ i, (γ' i).val=U then ∏ i, f i (γ' i) else 0 := by
      calc
        _ = ∑ γ'∈T, if ∑ i, (γ' i).val=U then ∏ i, f i (γ' i) else 0 := by
          apply Finset.sum_congr rfl
          intro γ' hγ'
          simp only [hT γ' hγ', ↓reduceIte, Fin.prod_univ_succ, f, Fin.cases_zero,
            Fin.cases_succ, one_mul]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
          intro γ' _ _
          split_ifs
          · exact Finset.prod_nonneg (fun i _ => hf i _)
          · rfl)
    apply hsub.trans
    apply (constrained_sum_product_le r U f hf 1 (by norm_num) (by intro k; rfl)).trans
    simp only [one_mul]
    calc
      _ ≤ ∏ _i:Fin r, (2/(1-ρ)) := by
        apply Finset.prod_le_prod₀
        · intro i _; exact Finset.sum_nonneg (fun k _ => hf i.succ k)
        · intro i _; exact fin_geometric_distance (U+1) ((γ i.succ).val:ℤ) hρ
      _ = _ := by simp [div_pow]
  have houter : (∑ γ∈S, A γ) ≤ Real.exp (h*U)*(6/Real.sqrt h)^r := by
    apply le_trans _ (coarse_constrained_inverse_sum r U hh h1)
    calc
      _ = ∑ γ∈S, if ∑ i, (γ i).val=U then A γ else 0 := by
        apply Finset.sum_congr rfl
        intro γ hγ
        rw [ite_eq_left (hS γ hγ)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro γ _ _
        split_ifs
        · exact hA γ
        · rfl)
  calc
    _ ≤ ∑ γ∈S, ∑ γ'∈T, M * ∏ i:Fin r, ((Real.sqrt ((γ i.succ).val:ℝ))⁻¹ *
        ρ^(((γ' i.succ).val:ℤ)-(γ i.succ).val).natAbs) := by
      exact Finset.sum_le_sum (fun γ hγ => Finset.sum_le_sum (fun γ' hγ' => hcross γ hγ γ' hγ'))
    _ = ∑ γ∈S, M*A γ * ∑ γ'∈T, ∏ i:Fin r, ρ^(((γ' i.succ).val:ℤ)-(γ i.succ).val).natAbs := by
      simp only [Finset.prod_mul_distrib, A, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ γ∈S, M*A γ*(2/(1-ρ))^r := by
      exact Finset.sum_le_sum (fun γ _ => mul_le_mul_of_nonneg_left (hinner γ) (mul_nonneg hM (hA γ)))
    _ = M*(2/(1-ρ))^r * ∑ γ∈S, A γ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ M*(2/(1-ρ))^r * (Real.exp (h*U)*(6/Real.sqrt h)^r) := by
      apply mul_le_mul_of_nonneg_left houter
      exact mul_nonneg hM (pow_nonneg (div_nonneg (by norm_num) (by linarith [hρ.2])) _)
    _ = _ := by ring


end TraceReconstruction

namespace TraceReconstruction

/-- Geometry of actual period gaps: the half-integer coarse gaps are
represented by positive integers a,b, with bounded slot-rounding errors. -/
theorem coarse_gap_geometry (m U a b g k : ℕ) (hm : 32 ≤ m) (hUm : U  ≤  2*m)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (haU : a ≤ U) (hbU : b ≤ U)
    (hg : |(g:ℝ)-(m:ℝ)*a/2| ≤ 4) (hk : |(k:ℝ)-(m:ℝ)*b/2| ≤ 4) :
    (m:ℝ)*a/4  ≤  (g:ℝ)+1 ∧ 0<(g:ℝ)+k ∧
      ((a:ℝ)-b)^2/1024  ≤  ((g:ℝ)-k)^2/(16*((g:ℝ)+k)) := by
  have hmR : (32:ℝ) ≤ m := by exact_mod_cast hm
  have hUmR : (U:ℝ)  ≤  2*m := by exact_mod_cast hUm
  have haR : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb
  have haUR : (a:ℝ) ≤ U := by exact_mod_cast haU
  have hbUR : (b:ℝ) ≤ U := by exact_mod_cast hbU
  have hga := abs_le.mp hg
  have hkb := abs_le.mp hk
  have hma : (32:ℝ) ≤ (m:ℝ)*a := by nlinarith
  have hmb : (32:ℝ) ≤ (m:ℝ)*b := by nlinarith
  have hlo : (m:ℝ)*a/4 ≤ (g:ℝ)+1 := by nlinarith only [hga.1,hma]
  have hsum0 : 0<(g:ℝ)+k := by nlinarith only [hga.1,hkb.1,hma,hmb]
  refine ⟨hlo,hsum0,?_⟩
  by_cases hab : a=b
  · simp only [hab, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div]
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hd1 : 1 ≤ |(a:ℝ)-b| := by
    rcases lt_or_gt_of_ne hab with hab | hab
    · rw [abs_of_neg (sub_neg.mpr (by exact_mod_cast hab : (a:ℝ) < b))]
      have hx : (a:ℝ)+1 ≤ b := by exact_mod_cast hab
      linarith
    · rw [abs_of_pos (sub_pos.mpr (by exact_mod_cast hab : (b:ℝ) < a))]
      have hx : (b:ℝ)+1 ≤ a := by exact_mod_cast hab
      linarith
  have herr : |((g:ℝ)-k)-(m:ℝ)/2*((a:ℝ)-b)| ≤ 8 := by
    calc
      _ = |((g:ℝ)-(m:ℝ)*a/2)-((k:ℝ)-(m:ℝ)*b/2)| := by congr 1; ring
      _  ≤  |(g:ℝ)-(m:ℝ)*a/2|+|(k:ℝ)-(m:ℝ)*b/2| := abs_sub _ _
      _  ≤  _ := by linarith
  have hd : (m:ℝ)/4*|(a:ℝ)-b|  ≤  |(g:ℝ)-k| := by
    have ht := abs_sub_abs_le_abs_sub ((m:ℝ)/2*((a:ℝ)-b)) ((g:ℝ)-k)
    rw [abs_sub_comm ((m:ℝ)/2*((a:ℝ)-b)) ((g:ℝ)-k)] at ht
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (m:ℝ)/2)] at ht
    have hmabs : (32:ℝ) ≤ (m:ℝ)*|(a:ℝ)-b| := by nlinarith only [hmR,hd1]
    nlinarith only [ht,herr,hmabs]
  have hsq : (m:ℝ)^2*((a:ℝ)-b)^2/16 ≤ ((g:ℝ)-k)^2 := by
    have hx := mul_self_le_mul_self (by positivity : 0 ≤ (m:ℝ)/4*|(a:ℝ)-b|) hd
    nlinarith only [hx, sq_abs ((a:ℝ)-b), sq_abs ((g:ℝ)-k)]
  have hsum : (g:ℝ)+k  ≤  4*(m:ℝ)^2 := by
    have hu1 : (1:ℝ) ≤ U := by linarith
    have hmu : (32:ℝ) ≤ (m:ℝ)*U := by nlinarith only [hmR,hu1]
    have hmaU := mul_le_mul_of_nonneg_left haUR (show (0:ℝ) ≤ m by positivity)
    have hmbU := mul_le_mul_of_nonneg_left hbUR (show (0:ℝ) ≤ m by positivity)
    have hUmM := mul_le_mul_of_nonneg_left hUmR (show (0:ℝ) ≤ m by positivity)
    nlinarith only [hga.2,hkb.2,hmaU,hmbU,hmu,hUmM]
  apply (le_div_iff₀ (by positivity : 0<16*((g:ℝ)+k))).mpr
  have hx := mul_le_mul_of_nonneg_right hsum (sq_nonneg ((a:ℝ)-b))
  nlinarith only [hx,hsq]

/-- From integer Gaussian decay to a summable geometric profile. -/
theorem exp_integer_square_le (a b : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    Real.exp (-c * ((a:ℝ)-b)^2) ≤
      (Real.exp (-c)) ^ ((a:ℤ)-b).natAbs := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hd : (((a:ℤ)-b).natAbs : ℝ) = |(a:ℝ)-b| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, Int.cast_sub]
    simp only [Int.cast_natCast]
  have hsq : (((a:ℤ)-b).natAbs:ℝ) ≤ (((a:ℤ)-b).natAbs:ℝ)^2 := by
    exact_mod_cast (show ((a:ℤ)-b).natAbs ≤ ((a:ℤ)-b).natAbs^2 by
      simpa only [pow_two] using Nat.le_mul_self ((a:ℤ)-b).natAbs)
  rw [hd, sq_abs] at hsq
  have hmul := mul_le_mul_of_nonneg_left hsq hc
  rw [hd]
  nlinarith only [hmul]

theorem coarse_binomial_overlap (m U a b g k L : ℕ)
    (hm : 32 ≤ m) (hUm : U ≤ 2*m)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (haU : a ≤ U) (hbU : b ≤ U)
    (hg : |(g:ℝ)-(m:ℝ)*a/2| ≤ 4) (hk : |(k:ℝ)-(m:ℝ)*b/2| ≤ 4)
    {θ : ℝ} (hθ : θ ∈ Set.Ico (1/2:ℝ) 1) :
    (∑ z : Fin (L+1), binomialMass g θ z * binomialMass k θ z) ≤
      Real.sqrt (8 / ((m:ℝ)*θ*(1-θ))) * (Real.sqrt (a:ℝ))⁻¹ *
        (Real.exp (-(1/1024:ℝ))) ^ ((a:ℤ)-b).natAbs := by
  have geo := coarse_gap_geometry m U a b g k hm hUm ha hb haU hbU hg hk
  have hsum : 0 < g+k := by exact_mod_cast geo.2.1
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hθ1 : 0 < 1-θ := sub_pos.mpr hθ.2
  have varpos : 0 < θ*(1-θ) := mul_pos hθ0 hθ1
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have ha0 : (0:ℝ) < a := by exact_mod_cast ha
  have hpref : Real.sqrt (2 / (((g:ℝ)+1)*θ*(1-θ))) ≤
      Real.sqrt (8 / ((m:ℝ)*θ*(1-θ))) * (Real.sqrt (a:ℝ))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity : 0 ≤ 8/((m:ℝ)*θ*(1-θ)))]
    apply Real.sqrt_le_sqrt
    have hdg : 0 < ((g:ℝ)+1)*θ*(1-θ) := by nlinarith
    have hdm : 0 < (m:ℝ)*θ*(1-θ) := by nlinarith
    apply (div_le_iff₀ hdg).mpr
    have hdiv : 0 < (m:ℝ)*θ*(1-θ)*(a:ℝ) := by positivity
    have heq : (8 / ((m:ℝ)*θ*(1-θ)) * (a:ℝ)⁻¹) * (((g:ℝ)+1)*θ*(1-θ)) =
        (8*((g:ℝ)+1)) / ((m:ℝ)*a) := by
      field_simp [ne_of_gt hθ0, ne_of_gt hθ1, ne_of_gt hm0, ne_of_gt ha0]
    rw [heq]
    apply (le_div_iff₀ (mul_pos hm0 ha0)).mpr
    linarith [geo.1]
  have hexp : Real.exp (-((g:ℝ)-k)^2/(16*((g:ℝ)+k))) ≤
      (Real.exp (-(1/1024:ℝ))) ^ ((a:ℤ)-b).natAbs := by
    apply le_trans _ (exp_integer_square_le a b (by norm_num : (0:ℝ)≤1/1024))
    apply Real.exp_le_exp.mpr
    convert neg_le_neg geo.2.2 using 2 <;> first | rfl | ring
  exact (binomial_gaussian_overlap_general g k L hθ hsum).trans
    (mul_le_mul hpref hexp (Real.exp_nonneg _) (by positivity))

end TraceReconstruction


namespace TraceReconstruction

theorem int_natAbs_sub_comm (a b : ℤ) : (a-b).natAbs = (b-a).natAbs := by
  rw [← Int.natAbs_neg (a-b),neg_sub]

theorem subsetRankKernel_cross_normalized {n l r : ℕ} (hl : l  ≤  n)
    (p q : Fin r → Fin n) (hp : StrictMono p) (hq : StrictMono q)
    {θ : ℝ} (hθ : θ  ∈  Set.Ico (1/2:ℝ) 1)
    (hmean : (n:ℝ)*θ=l) (hv : 1 ≤ (n:ℝ)*θ*(1-θ)) (e : Fin (r+1)) :
    (∑ v : IncreasingTuple l r,
      subsetRankKernel hl p v.val * subsetRankKernel hl q v.val)  ≤ 
      (4608*n/((tupleGap p e:ℝ)+1))*
        ∏ i : Fin r, ∑ k : Fin (l-r+1),
          binomialMass (tupleGap p (Equiv.swap 0 e i.succ)) θ k *
          binomialMass (tupleGap q (Equiv.swap 0 e i.succ)) θ k := by
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hqpos : 0 < 1-θ := sub_pos.mpr hθ.2
  have hc : (θ^r/binomialMass n θ l)^2  ≤  144*((n:ℝ)*θ*(1-θ)) := by
    rw [div_eq_mul_inv,mul_pow]
    apply (mul_le_mul_of_nonneg_right
      (show (θ^r)^2  ≤  (1:ℝ) by
        exact pow_le_one₀ (pow_nonneg hθ0.le _) (pow_le_one₀ hθ0.le hθ.2.le))
      (sq_nonneg _)).trans
    simpa only [one_mul] using binomialMass_mean_inverse_sq n l ⟨hθ0,hθ.2⟩ hl hmean hv
  have hprod : 0  ≤  ∏ i : Fin r, ∑ k : Fin (l-r+1),
      binomialMass (tupleGap p (Equiv.swap 0 e i.succ)) θ k *
      binomialMass (tupleGap q (Equiv.swap 0 e i.succ)) θ k := by
    apply Finset.prod_nonneg
    intro i _
    exact Finset.sum_nonneg fun k _ => mul_nonneg
      (binomialMass_nonneg _ _ ⟨hθ0.le,hθ.2.le⟩)
      (binomialMass_nonneg _ _ ⟨hθ0.le,hθ.2.le⟩)
  apply (subsetRankKernel_cross_le hl p q hp hq θ ⟨hθ0,hθ.2⟩ e
    (32/(((tupleGap p e:ℝ)+1)*θ*(1-θ))) (by positivity)
    (fun k => binomial_product_sup _ _ k hθ)).trans
  calc
    _  ≤  (144*((n:ℝ)*θ*(1-θ)))*(32/(((tupleGap p e:ℝ)+1)*θ*(1-θ)))*_ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) hprod
    _ = _ := by
      have hq0 : 1-θ ≠ 0 := ne_of_gt (sub_pos.mpr hθ.2)
      field_simp
      ring

def periodProfile {u r : ℕ} (hr : 0 < r) (σ : Equiv.Perm (Fin (r+1)))
    (j : IncreasingTuple u r) : Fin (r+1) → Fin (2*u+1) :=
  fun i => ⟨coarsePeriodGap j.val (σ i),
    Nat.lt_succ_of_le (coarsePeriodGap_le hr j.val j.property (σ i))⟩

theorem periodProfile_sum {u r : ℕ} (hr : 0 < r) (σ : Equiv.Perm (Fin (r+1)))
    (j : IncreasingTuple u r) : ∑ i, (periodProfile hr σ j i).val = 2*u := by
  change (∑ i, coarsePeriodGap j.val (σ i)) = _
  rw [Equiv.sum_comp σ]
  exact coarsePeriodGap_sum hr j.val j.property

theorem periodProfile_injective {u r : ℕ} (hr : 0 < r) (σ : Equiv.Perm (Fin (r+1))) :
    Function.Injective (periodProfile (u:=u) hr σ) := by
  intro j k h
  apply Subtype.ext
  apply coarsePeriodGap_injective j.property k.property
  funext i
  have he := congrArg Fin.val (congrFun h (σ.symm i))
  simpa only [periodProfile,Equiv.apply_symm_apply] using he

theorem period_kernel_cross {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hm : 32 ≤ m) (hum : u ≤ m) {θ : ℝ} (hθ : θ ∈ Set.Ico (1/2:ℝ) 1)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2)
    (j k : IncreasingTuple u r) (e : Fin (r+1))
    (he : 2*u  ≤  (r+1)*coarsePeriodGap j.val e) :
    (∑ v : IncreasingTuple l r,
      subsetRankKernel hl (periodSlot off ∘ j.val) v.val *
      subsetRankKernel hl (periodSlot off ∘ k.val) v.val)  ≤ 
      (9216*(r+1:ℕ) : ℝ)* (Real.sqrt (8/((m:ℝ)*θ*(1-θ))))^r *
        ∏ i : Fin r, (Real.sqrt ((periodProfile hr (Equiv.swap 0 e) j i.succ).val:ℝ))⁻¹ *
          (Real.exp (-(1/1024:ℝ)))^(((periodProfile hr (Equiv.swap 0 e) k i.succ).val:ℤ)-
            (periodProfile hr (Equiv.swap 0 e) j i.succ).val).natAbs := by
  classical
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hUm : 2*u ≤ 2*m := Nat.mul_le_mul_left 2 hum
  have hg (v : IncreasingTuple u r) (i : Fin (r+1)) :=
    period_gap_rounding hr off hoff hdiff v.val v.property i
  have hgeo := coarse_gap_geometry m (2*u) (coarsePeriodGap j.val e)
    (coarsePeriodGap k.val e) (tupleGap (periodSlot off ∘ j.val) e)
    (tupleGap (periodSlot off ∘ k.val) e) hm hUm
    (coarsePeriodGap_pos j.val e) (coarsePeriodGap_pos k.val e)
    (coarsePeriodGap_le hr j.val j.property e) (coarsePeriodGap_le hr k.val k.property e)
    (hg j e) (hg k e)
  have hlarge : (4608 * (u*m:ℕ) : ℝ)/((tupleGap (periodSlot off ∘ j.val) e:ℝ)+1)  ≤ 
      9216*(r+1:ℕ) := by
    have heR : 2*(u:ℝ)  ≤  (r+1:ℕ)* (coarsePeriodGap j.val e:ℝ) := by exact_mod_cast he
    apply (div_le_iff₀ (by positivity : 0 < (tupleGap (periodSlot off ∘ j.val) e:ℝ)+1)).mpr
    have hx := mul_le_mul_of_nonneg_right hgeo.1
      (show (0:ℝ) ≤ (r+1:ℕ) by positivity)
    have hy := mul_le_mul_of_nonneg_left heR hm0.le
    simp only [Nat.cast_mul]
    nlinarith only [hx,hy]
  have hover (i : Fin r) :
      (∑ z : Fin (l-r+1),
        binomialMass (tupleGap (periodSlot off ∘ j.val) (Equiv.swap 0 e i.succ)) θ z *
        binomialMass (tupleGap (periodSlot off ∘ k.val) (Equiv.swap 0 e i.succ)) θ z)  ≤ 
      Real.sqrt (8/((m:ℝ)*θ*(1-θ))) *
        ((Real.sqrt ((periodProfile hr (Equiv.swap 0 e) j i.succ).val:ℝ))⁻¹ *
          (Real.exp (-(1/1024:ℝ)))^(((periodProfile hr (Equiv.swap 0 e) k i.succ).val:ℤ)-
            (periodProfile hr (Equiv.swap 0 e) j i.succ).val).natAbs) := by
    have ho := coarse_binomial_overlap m (2*u) _ _ _ _ (l-r) hm hUm
      (coarsePeriodGap_pos j.val _) (coarsePeriodGap_pos k.val _)
      (coarsePeriodGap_le hr j.val j.property _) (coarsePeriodGap_le hr k.val k.property _)
      (hg j (Equiv.swap 0 e i.succ)) (hg k (Equiv.swap 0 e i.succ)) hθ
    rw [int_natAbs_sub_comm] at ho
    simpa only [periodProfile,mul_assoc] using ho
  have hn (i : Fin r) : 0 ≤  ∑ z : Fin (l-r+1),
      binomialMass (tupleGap (periodSlot off ∘ j.val) (Equiv.swap 0 e i.succ)) θ z *
      binomialMass (tupleGap (periodSlot off ∘ k.val) (Equiv.swap 0 e i.succ)) θ z := by
    exact Finset.sum_nonneg fun z _ => mul_nonneg
      (binomialMass_nonneg _ _ ⟨hθ0.le,hθ.2.le⟩) (binomialMass_nonneg _ _ ⟨hθ0.le,hθ.2.le⟩)
  apply (subsetRankKernel_cross_normalized hl _ _
    ((periodSlot_strictMono off).comp j.property) ((periodSlot_strictMono off).comp k.property)
    hθ hmean hv e).trans
  calc
    _  ≤  (9216*(r+1:ℕ) : ℝ)*
        ∏ i : Fin r, (Real.sqrt (8/((m:ℝ)*θ*(1-θ))) *
        ((Real.sqrt ((periodProfile hr (Equiv.swap 0 e) j i.succ).val:ℝ))⁻¹ *
          (Real.exp (-(1/1024:ℝ)))^(((periodProfile hr (Equiv.swap 0 e) k i.succ).val:ℤ)-
            (periodProfile hr (Equiv.swap 0 e) j i.succ).val).natAbs)) := by
      apply mul_le_mul hlarge (Finset.prod_le_prod₀ (fun i _ => hn i) (fun i _ => hover i))
        (Finset.prod_nonneg (fun i _ => hn i)) (by positivity)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; ring

end TraceReconstruction


namespace TraceReconstruction

theorem coarse_profile_geometric_sum {α : Type*} [Fintype α] (r U : ℕ)
    (profile : α → Fin (r+1) → Fin (U+1)) (hinj : Function.Injective profile)
    (htotal : ∀ a, ∑ i, (profile a i).val=U)
    (γ : Fin (r+1) → Fin (U+1)) {ρ : ℝ} (hρ : ρ∈Set.Ico 0 1) :
    (∑ a, ∏ i : Fin r, ρ^(((profile a i.succ).val:ℤ)-(γ i.succ).val).natAbs) ≤
      (2/(1-ρ))^r := by
  classical
  let f : Fin (r+1) → Fin (U+1) → ℝ := Fin.cases (fun _ => 1)
    (fun i k => ρ^((k.val:ℤ)-(γ i.succ).val).natAbs)
  have hf : ∀ i k, 0≤f i k := by
    intro i k
    refine Fin.cases ?_ (fun _ => ?_) i
    · norm_num [f]
    · exact pow_nonneg hρ.1 _
  have hid (δ : Fin (r+1) → Fin (U+1)) :
      (∏ i : Fin r, ρ^(((δ i.succ).val:ℤ)-(γ i.succ).val).natAbs) = ∏ i, f i (δ i) := by
    simp only [Fin.prod_univ_succ,f,Fin.cases_zero,Fin.cases_succ,one_mul]
  simp_rw [hid]
  apply (sum_injective_profile_le profile hinj (fun δ => ∑ i, (δ i).val=U)
    htotal (fun δ => ∏ i, f i (δ i)) (fun δ => Finset.prod_nonneg (fun i _ => hf i _))).trans
  apply (constrained_sum_product_le r U f hf 1 (by norm_num) (by intro k; rfl)).trans
  simp only [one_mul]
  calc
    _ ≤ ∏ _i : Fin r, (2/(1-ρ)) := by
      apply Finset.prod_le_prod₀
      · exact fun i _ => Finset.sum_nonneg (fun k _ => hf i.succ k)
      · exact fun i _ => fin_geometric_distance (U+1) ((γ i.succ).val:ℤ) hρ
    _ = _ := by simp [div_pow]

theorem coarse_profile_inverse_sum {α : Type*} [Fintype α] (r U : ℕ)
    (profile : α → Fin (r+1) → Fin (U+1)) (hinj : Function.Injective profile)
    (htotal : ∀ a, ∑ i, (profile a i).val=U)
    {h : ℝ} (hh : 0<h) (h1 : h≤1) :
    (∑ a, ∏ i : Fin r, (Real.sqrt ((profile a i.succ).val:ℝ))⁻¹) ≤
      Real.exp (h*U)*(6/Real.sqrt h)^r := by
  classical
  apply le_trans _ (coarse_constrained_inverse_sum r U hh h1)
  exact sum_injective_profile_le profile hinj (fun δ => ∑ i, (δ i).val=U)
    htotal (fun δ => ∏ i : Fin r, (Real.sqrt ((δ i.succ).val:ℝ))⁻¹) (fun δ => by positivity)

/-- Coarse Schur bound for actual injective profiles, with no extension of
kernels outside their geometric domain. -/
theorem coarse_profile_bilinear_sum {α β : Type*} [Fintype α] [Fintype β]
    (r U : ℕ) (p : α → Fin (r+1) → Fin (U+1)) (q : β → Fin (r+1) → Fin (U+1))
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hpt : ∀ a, ∑ i, (p a i).val=U) (hqt : ∀ b, ∑ i, (q b i).val=U)
    (K : α → β → ℝ) {M ρ h : ℝ}
    (hM : 0≤M) (hρ : ρ∈Set.Ico 0 1) (hh : 0<h) (h1 : h≤1)
    (hcross : ∀ a b, K a b ≤ M * ∏ i : Fin r,
      (Real.sqrt ((p a i.succ).val:ℝ))⁻¹ *
        ρ^(((q b i.succ).val:ℤ)-(p a i.succ).val).natAbs) :
    (∑ a, ∑ b, K a b) ≤ M*(2/(1-ρ))^r * Real.exp (h*U)*(6/Real.sqrt h)^r := by
  classical
  let A (a : α) := ∏ i : Fin r, (Real.sqrt ((p a i.succ).val:ℝ))⁻¹
  have hA (a) : 0≤A a := by dsimp [A]; positivity
  have hinner (a) := coarse_profile_geometric_sum r U q hq hqt (p a) hρ
  have houter := coarse_profile_inverse_sum r U p hp hpt hh h1
  calc
    _ ≤ ∑ a, ∑ b, M * ∏ i : Fin r,
        (Real.sqrt ((p a i.succ).val:ℝ))⁻¹ *
          ρ^(((q b i.succ).val:ℤ)-(p a i.succ).val).natAbs :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hcross a b))
    _ = ∑ a, M*A a * ∑ b, ∏ i : Fin r, ρ^(((q b i.succ).val:ℤ)-(p a i.succ).val).natAbs := by
      simp only [Finset.prod_mul_distrib,A,Finset.mul_sum,mul_assoc]
    _ ≤ ∑ a, M*A a*(2/(1-ρ))^r :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hinner a) (mul_nonneg hM (hA a)))
    _ = M*(2/(1-ρ))^r * ∑ a, A a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ M*(2/(1-ρ))^r * (Real.exp (h*U)*(6/Real.sqrt h)^r) := by
      apply mul_le_mul_of_nonneg_left houter
      exact mul_nonneg hM (pow_nonneg (div_nonneg (by norm_num) (by linarith [hρ.2])) _)
    _ = _ := by ring

end TraceReconstruction

namespace TraceReconstruction

def LargePeriodTuple (u r : ℕ) (e : Fin (r+1)) :=
  {j : IncreasingTuple u r // 2*u ≤ (r+1)*coarsePeriodGap j.val e}

noncomputable instance largePeriodTupleFintype (u r : ℕ) (e : Fin (r+1)) :
    Fintype (LargePeriodTuple u r e) := by
  unfold LargePeriodTuple
  exact Fintype.ofFinite _

theorem exists_large_period_gap {u r : ℕ} (hr : 0 < r) (j : IncreasingTuple u r) :
    ∃ e : Fin (r+1), 2*u ≤ (r+1)*coarsePeriodGap j.val e := by
  obtain ⟨e,_,he⟩ := Finset.exists_max_image Finset.univ (coarsePeriodGap j.val)
    Finset.univ_nonempty
  refine ⟨e,?_⟩
  calc
    _ = ∑ i, coarsePeriodGap j.val i := (coarsePeriodGap_sum hr j.val j.property).symm
    _ ≤ ∑ _i : Fin (r+1), coarsePeriodGap j.val e := Finset.sum_le_sum (fun i hi => he i hi)
    _ = _ := by simp

/-- Unnormalized but explicit source rank-kernel square-sum estimate. The
only remaining factors are elementary scale simplifications. -/
theorem period_rank_square_sum_raw {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hm : 32 ≤ m) (hum : u ≤ m) {θ h : ℝ} (hθ : θ ∈ Set.Ico (1/2:ℝ) 1)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh : 0 < h) (h1 : h ≤ 1)
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) :
    (∑ v : IncreasingTuple l r,
      (∑ j : IncreasingTuple u r, subsetRankKernel hl (periodSlot off ∘ j.val) v.val)^2) ≤
      9216*(r+1:ℕ)^2 * (Real.sqrt (8/((m:ℝ)*θ*(1-θ))))^r *
        (2/(1-Real.exp (-(1/1024:ℝ))))^r * Real.exp (h*(2*u:ℕ)) * (6/Real.sqrt h)^r := by
  classical
  let K (j : IncreasingTuple u r) (v : IncreasingTuple l r) :=
    subsetRankKernel hl (periodSlot off ∘ j.val) v.val
  let C (j k : IncreasingTuple u r) := ∑ v : IncreasingTuple l r, K j v*K k v
  have hC (j k) : 0 ≤ C j k := by
    exact Finset.sum_nonneg (fun v _ => mul_nonneg
      (subsetRankKernel_nonneg hl _ _) (subsetRankKernel_nonneg hl _ _))
  have hρ : Real.exp (-(1/1024:ℝ)) ∈ Set.Ico 0 1 := by
    refine ⟨(Real.exp_pos _).le,?_⟩
    rw [Real.exp_lt_one_iff]
    norm_num
  have hschur (e : Fin (r+1)) :
      (∑ j : LargePeriodTuple u r e, ∑ k : IncreasingTuple u r, C j.val k) ≤
        ((9216*(r+1:ℕ):ℝ)*(Real.sqrt (8/((m:ℝ)*θ*(1-θ))))^r) *
          (2/(1-Real.exp (-(1/1024:ℝ))))^r * Real.exp (h*(2*u:ℕ)) * (6/Real.sqrt h)^r := by
    apply coarse_profile_bilinear_sum r (2*u)
      (fun j : LargePeriodTuple u r e => periodProfile hr (Equiv.swap 0 e) j.val)
      (periodProfile hr (Equiv.swap 0 e))
      ((periodProfile_injective hr (Equiv.swap 0 e)).comp Subtype.val_injective)
      (periodProfile_injective hr (Equiv.swap 0 e))
      (fun j => periodProfile_sum hr _ j.val) (periodProfile_sum hr _)
      (fun j k => C j.val k) (by positivity) hρ hh h1
    intro j k
    exact period_kernel_cross hl hr hm hum hθ hmean hv off hoff hdiff j.val k e j.property
  have hcover (j : IncreasingTuple u r) :
      (∑ k : IncreasingTuple u r, C j k) ≤ ∑ e : Fin (r+1),
        if 2*u ≤ (r+1)*coarsePeriodGap j.val e then ∑ k : IncreasingTuple u r, C j k else 0 := by
    obtain ⟨e,he⟩ := exists_large_period_gap hr j
    have hn : ∀ e' : Fin (r+1), 0 ≤
        if 2*u ≤ (r+1)*coarsePeriodGap j.val e' then ∑ k : IncreasingTuple u r, C j k else 0 := by
      intro e'
      split_ifs
      · exact Finset.sum_nonneg (fun k _ => hC j k)
      · rfl
    simpa only [ite_eq_left he] using Finset.single_le_sum (fun e' _ => hn e') (Finset.mem_univ e)
  have heq (e : Fin (r+1)) :
      (∑ j : IncreasingTuple u r,
        if 2*u ≤ (r+1)*coarsePeriodGap j.val e then ∑ k : IncreasingTuple u r, C j k else 0) =
      ∑ j : LargePeriodTuple u r e, ∑ k : IncreasingTuple u r, C j.val k := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by intro j; simp) _
  calc
    _ = ∑ j : IncreasingTuple u r, ∑ k : IncreasingTuple u r, C j k := by
      exact sum_sq_sum_kernel Finset.univ K
    _ ≤ ∑ j : IncreasingTuple u r, ∑ e : Fin (r+1),
        if 2*u ≤ (r+1)*coarsePeriodGap j.val e then ∑ k : IncreasingTuple u r, C j k else 0 :=
      Finset.sum_le_sum (fun j _ => hcover j)
    _ = ∑ e : Fin (r+1), ∑ j : LargePeriodTuple u r e,
        ∑ k : IncreasingTuple u r, C j.val k := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun e _ => heq e)
    _ ≤ ∑ _e : Fin (r+1),
        ((9216*(r+1:ℕ):ℝ)*(Real.sqrt (8/((m:ℝ)*θ*(1-θ))))^r) *
          (2/(1-Real.exp (-(1/1024:ℝ))))^r * Real.exp (h*(2*u:ℕ)) * (6/Real.sqrt h)^r :=
      Finset.sum_le_sum (fun e _ => hschur e)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end TraceReconstruction

namespace TraceReconstruction

theorem rank_polynomial_factor {r : ℕ} (hr : 0 < r) :
    (9216:ℝ)*(r+1:ℕ)^2 ≤ (36864:ℝ)^r := by
  have h1 : (9216:ℝ) ≤ (9216:ℝ)^r := le_self_pow₀ (by norm_num) (Nat.ne_of_gt hr)
  have h2 : ((r+1:ℕ):ℝ) ≤ (2:ℝ)^r := by exact_mod_cast nat_add_one_le_two_pow r
  have h3 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (r+1:ℕ)) h2 2
  have h4 : ((2:ℝ)^r)^2 = (4:ℝ)^r := by
    rw [← pow_mul,Nat.mul_comm r 2,pow_mul]
    norm_num
  calc
    _ ≤ (9216:ℝ)^r*((2:ℝ)^r)^2 := mul_le_mul h1 h3 (by positivity) (by positivity)
    _ = _ := by rw [h4,← mul_pow]; norm_num

noncomputable def rankSchurConstant : ℝ :=
  884736 * (2/(1-Real.exp (-(1/1024:ℝ)))) * Real.exp 1

theorem rankSchurConstant_pos : 0 < rankSchurConstant := by
  have hρ : Real.exp (-(1/1024:ℝ)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  unfold rankSchurConstant
  positivity

/-- Rank-kernel square sum, with an explicit absolute constant, uniformly
in the defect types and admissible conditional count. -/
theorem period_rank_square_sum {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hru : r ≤ u) (hm : 32 ≤ m) (hum : u ≤ m) {θ : ℝ} (hθ : θ ∈ Set.Ico (1/2:ℝ) 1)
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) :
    (∑ v : IncreasingTuple l r,
      (∑ j : IncreasingTuple u r, subsetRankKernel hl (periodSlot off ∘ j.val) v.val)^2) ≤
      (rankSchurConstant * Real.sqrt ((u:ℝ)/((m:ℝ)*r*θ*(1-θ))))^r := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  have hu0 : (0:ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hq0 : 0 < 1-θ := sub_pos.mpr hθ.2
  let h : ℝ := (r:ℝ)/(2*u)
  have hh : 0 < h := div_pos hr0 (by positivity)
  have h1 : h ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ) < 2*u)).mpr
    have hruR : (r:ℝ) ≤ u := by exact_mod_cast hru
    linarith
  have hx : h*(2*u:ℕ) = r := by
    dsimp [h]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    field_simp
  have he : Real.exp (h*(2*u:ℕ)) = (Real.exp 1)^r := by
    rw [hx,← Real.exp_nat_mul]
    simp
  have hρ : 0 ≤ 2/(1-Real.exp (-(1/1024:ℝ))) := by
    have hn : Real.exp (-(1/1024:ℝ)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    positivity
  have hp : 0 ≤ (u:ℝ)/((m:ℝ)*r*θ*(1-θ)) := by positivity
  have hs : Real.sqrt (8/((m:ℝ)*θ*(1-θ))) * (6/Real.sqrt h) ≤
      24 * Real.sqrt ((u:ℝ)/((m:ℝ)*r*θ*(1-θ))) := by
    have hsq : (Real.sqrt (8/((m:ℝ)*θ*(1-θ))) * (6/Real.sqrt h))^2 =
        576 * ((u:ℝ)/((m:ℝ)*r*θ*(1-θ))) := by
      rw [mul_pow,div_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ 8/((m:ℝ)*θ*(1-θ))),
        Real.sq_sqrt hh.le]
      dsimp [h]
      field_simp
      ring
    nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg ((u:ℝ)/((m:ℝ)*r*θ*(1-θ)))]
  apply (period_rank_square_sum_raw hl hr hm hum hθ hmean hv hh h1 off hoff hdiff).trans
  rw [he]
  calc
    _ ≤ (36864:ℝ)^r * (Real.sqrt (8/((m:ℝ)*θ*(1-θ))))^r *
        (2/(1-Real.exp (-(1/1024:ℝ))))^r * (Real.exp 1)^r * (6/Real.sqrt h)^r := by
      gcongr
      exact rank_polynomial_factor hr
    _ = ((36864:ℝ)*(2/(1-Real.exp (-(1/1024:ℝ))))*Real.exp 1 *
        (Real.sqrt (8/((m:ℝ)*θ*(1-θ)))*(6/Real.sqrt h)))^r := by
      simp only [mul_pow]
      ring
    _ ≤ ((36864:ℝ)*(2/(1-Real.exp (-(1/1024:ℝ))))*Real.exp 1 *
        (24 * Real.sqrt ((u:ℝ)/((m:ℝ)*r*θ*(1-θ)))))^r := by
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by congr 1; unfold rankSchurConstant; ring

end TraceReconstruction

namespace TraceReconstruction

/-- The source's channel-uniform rank-kernel estimate (base-kernel),
with the absolute constant made explicit. -/
theorem period_rank_square_sum_delta {u m l r : ℕ} (hl : l ≤ u*m) (hr : 0 < r)
    (hru : r ≤ u) (hm : 32 ≤ m) (hum : u ≤ m) {δ θ : ℝ}
    (hδ : δ ∈ Set.Ioc 0 (1/2:ℝ))
    (hθ : θ ∈ Set.Icc (1-δ^2) (1-δ^2/4))
    (hmean : ((u*m:ℕ):ℝ)*θ=l) (hv : 1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off : Fin u → Fin m)
    (hoff : ∀ j, |((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff : ∀ j k, |((off j).val:ℝ)-(off k).val| ≤ 2) :
    (∑ v : IncreasingTuple l r,
      (∑ j : IncreasingTuple u r, subsetRankKernel hl (periodSlot off ∘ j.val) v.val)^2) ≤
      ((3*rankSchurConstant/δ) * Real.sqrt ((u:ℝ)/((m:ℝ)*r)))^r := by
  have hd0 : 0 < δ := hδ.1
  have hd2 : 0 < δ^2 := sq_pos_of_pos hδ.1
  have hd2b : δ^2 ≤ 1/4 := by nlinarith [hδ.1,hδ.2]
  have ht : θ ∈ Set.Ico (1/2:ℝ) 1 := by
    constructor <;> nlinarith [hθ.1,hθ.2]
  have ht0 : 0 < θ := by linarith [ht.1]
  have hq0 : 0 < 1-θ := sub_pos.mpr ht.2
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hu0 : (0:ℝ) ≤ u := Nat.cast_nonneg u
  have hvar : δ^2/8 ≤ θ*(1-θ) := by
    have hq : δ^2/4 ≤ 1-θ := by linarith [hθ.2]
    nlinarith [mul_le_mul ht.1 hq (by positivity) ht0.le]
  have hdiv : (u:ℝ)/((m:ℝ)*r*θ*(1-θ)) ≤
      (3/δ)^2*((u:ℝ)/((m:ℝ)*r)) := by
    have hden : (0:ℝ) < (m:ℝ)*r*θ*(1-θ) := by positivity
    apply (div_le_iff₀ hden).mpr
    have he : (3/δ)^2 * ((u:ℝ)/((m:ℝ)*r)) * ((m:ℝ)*r*θ*(1-θ)) =
        ((u:ℝ)*9*θ*(1-θ))/δ^2 := by field_simp; ring
    rw [he]
    apply (le_div_iff₀ hd2).mpr
    nlinarith [mul_le_mul_of_nonneg_left hvar (by positivity : (0:ℝ) ≤ 9*(u:ℝ))]
  have hs : Real.sqrt ((u:ℝ)/((m:ℝ)*r*θ*(1-θ))) ≤
      (3/δ)*Real.sqrt ((u:ℝ)/((m:ℝ)*r)) := by
    calc
      _ ≤ Real.sqrt ((3/δ)^2*((u:ℝ)/((m:ℝ)*r))) := Real.sqrt_le_sqrt hdiv
      _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
  apply (period_rank_square_sum hl hr hru hm hum ht hmean hv off hoff hdiff).trans
  apply pow_le_pow_left₀ (by positivity [rankSchurConstant_pos])
  calc
    _ ≤ rankSchurConstant*((3/δ)*Real.sqrt ((u:ℝ)/((m:ℝ)*r))) :=
      mul_le_mul_of_nonneg_left hs rankSchurConstant_pos.le
    _ = _ := by ring

end TraceReconstruction

end

end OAI
