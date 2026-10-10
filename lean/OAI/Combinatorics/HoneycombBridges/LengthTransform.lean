import Mathlib
import OAI.Combinatorics.HoneycombBridges.Factorization

namespace OAI

/-! Renewal transforms and irreducible length kernels. -/

noncomputable section
open scoped ENNReal
open Filter

namespace HoneycombActual

def discountedWeight (s u : ℝ) (b : Bridge) : ℝ≥0∞ :=
  weight b * ENNReal.ofReal (Real.exp (-s * (b.height : ℝ) - u * (b.length : ℝ)))

def bridgePartition (s u : ℝ) : ℝ≥0∞ :=
  1 + ∑' b : Bridge, discountedWeight s u b

def irreducibleLaplace (s u : ℝ) : ℝ≥0∞ :=
  ∑' b : {b : Bridge // b.Irreducible}, discountedWeight s u b.val

def UnnormalizedRenewalIdentity : Prop :=
  ∀ s u : ℝ, 0 < s → 0 ≤ u →
    bridgePartition s u = (1 - irreducibleLaplace s u)⁻¹



abbrev IrreducibleBridge := {b : Bridge // b.Irreducible}

def irreducibleProduct (bs : List IrreducibleBridge) : Option Bridge :=
  bridgeProduct (bs.map Subtype.val)

theorem irreducibleProduct_injective : Function.Injective irreducibleProduct := by
  intro as bs h
  apply (List.map_inj_right (fun _ _ he => Subtype.ext he)).mp
  apply irreducible_product_unique _ _ _ _ h
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact x.property
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact x.property

theorem irreducibleProduct_surjective : Function.Surjective irreducibleProduct := by
  intro x
  cases x with
  | none => exact ⟨[], rfl⟩
  | some b =>
    obtain ⟨bs, hp, hi⟩ := irreducible_factorization_exists b
    refine ⟨bs.attachWith Bridge.Irreducible hi, ?_⟩
    simpa [irreducibleProduct, List.attachWith_map_val] using hp

noncomputable def irreducibleProductEquiv : List IrreducibleBridge ≃ Option Bridge :=
  Equiv.ofBijective irreducibleProduct
    ⟨irreducibleProduct_injective, irreducibleProduct_surjective⟩

@[simp] theorem discountedWeight_concat (s u : ℝ) (b c : Bridge) :
    discountedWeight s u (b.concat c) = discountedWeight s u b * discountedWeight s u c := by
  simp only [discountedWeight, weight_concat, Bridge.concat_height, Bridge.concat_length,
    Nat.cast_add]
  have he : -s * ((b.height : ℝ) + c.height) - u * ((b.length : ℝ) + c.length) =
      (-s * b.height - u * b.length) + (-s * c.height - u * c.length) := by ring
  rw [he, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  ring

def optionWeight (s u : ℝ) : Option Bridge → ℝ≥0∞
  | none => 1
  | some b => discountedWeight s u b

theorem optionWeight_bridgeProduct (s u : ℝ) (bs : List Bridge) :
    optionWeight s u (bridgeProduct bs) = (bs.map (discountedWeight s u)).prod := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases h : bridgeProduct bs with
    | none =>
      have hn := (bridgeProduct_eq_none_iff bs).mp h
      subst bs
      simp [bridgeProduct, optionWeight]
    | some c =>
      simpa [bridgeProduct, h, optionWeight, discountedWeight_concat] using
        congrArg (fun x => discountedWeight s u b * x) ih

theorem optionWeight_irreducibleProduct (s u : ℝ) (bs : List IrreducibleBridge) :
    optionWeight s u (irreducibleProduct bs) =
      (bs.map (fun b => discountedWeight s u b.val)).prod := by
  simpa [irreducibleProduct, List.map_map, Function.comp_def] using
    optionWeight_bridgeProduct s u (bs.map Subtype.val)

end HoneycombActual

namespace HoneycombActual.RenewalList

def lengthSuccEquiv (α : Type*) (n : ℕ) :
    (α × {l : List α // l.length = n}) ≃ {l : List α // l.length = n+1} where
  toFun p := ⟨p.1 :: p.2.val, by simp [p.2.property]⟩
  invFun l := by
    rcases l with ⟨l, hl⟩
    cases l with
    | nil => simp at hl
    | cons a as => exact (a, ⟨as, by simpa using hl⟩)
  left_inv p := by rcases p with ⟨a, ⟨l, hl⟩⟩; rfl
  right_inv p := by
    rcases p with ⟨l, hl⟩
    cases l with
    | nil => simp at hl
    | cons a as => rfl

theorem sum_prod_length {α : Type*} (q : α → ℝ≥0∞) (n : ℕ) :
    (∑' l : {l : List α // l.length = n}, (l.val.map q).prod) = (∑' a, q a)^n := by
  classical
  induction n with
  | zero =>
    let : Unique {l : List α // l.length = 0} :=
      ⟨⟨⟨[], rfl⟩⟩, fun l => Subtype.ext (List.length_eq_zero_iff.mp l.property)⟩
    simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton, pow_zero]
    rfl
  | succ n ih =>
    rw [← (lengthSuccEquiv α n).tsum_eq (fun l => (l.val.map q).prod)]
    change (∑' p : α × {l : List α // l.length = n}, q p.1 * (p.2.val.map q).prod) = _
    rw [@ENNReal.tsum_prod α {l : List α // l.length = n}
      (fun a l => q a * (l.val.map q).prod)]
    simp_rw [ENNReal.tsum_mul_left, ih]
    rw [ENNReal.tsum_mul_right, pow_succ']

theorem sum_prod {α : Type*} (q : α → ℝ≥0∞) :
    (∑' l : List α, (l.map q).prod) = (1 - ∑' a, q a)⁻¹ := by
  rw [← ENNReal.tsum_fiberwise (fun l : List α => (l.map q).prod) List.length]
  change (∑' n : ℕ, ∑' l : {l : List α // l.length = n}, (l.val.map q).prod) = _
  simp_rw [sum_prod_length]
  exact ENNReal.tsum_geometric _

end HoneycombActual.RenewalList

namespace HoneycombActual

theorem optionWeight_tsum (s u : ℝ) :
    (∑' b : Option Bridge, optionWeight s u b) = bridgePartition s u := by
  rw [← (Equiv.optionEquivSumPUnit.{0,0} Bridge).symm.tsum_eq (optionWeight s u)]
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  simp [optionWeight, bridgePartition, tsum_fintype, add_comm]

theorem bridgePartition_geometric (s u : ℝ) :
    bridgePartition s u = (1 - irreducibleLaplace s u)⁻¹ := by
  rw [← optionWeight_tsum, ← irreducibleProductEquiv.tsum_eq (optionWeight s u)]
  calc
    (∑' bs : List IrreducibleBridge, optionWeight s u (irreducibleProductEquiv bs)) =
        ∑' bs : List IrreducibleBridge,
          (bs.map (fun b => discountedWeight s u b.val)).prod := by
      apply tsum_congr
      intro bs
      exact optionWeight_irreducibleProduct s u bs
    _ = (1 - irreducibleLaplace s u)⁻¹ :=
      RenewalList.sum_prod (fun b : IrreducibleBridge => discountedWeight s u b.val)

theorem unnormalizedRenewalIdentity : UnnormalizedRenewalIdentity := by
  intro s u _ _
  exact bridgePartition_geometric s u



def lengthPartition (s : ℝ) : ℝ≥0∞ :=
  ∑' b : Bridge, (b.length : ℝ≥0∞) * discountedWeight s 0 b

def irreducibleLengthPartition (s : ℝ) : ℝ≥0∞ :=
  ∑' b : IrreducibleBridge, (b.val.length : ℝ≥0∞) * discountedWeight s 0 b.val

def LengthRewardTransformIdentity : Prop :=
  ∀ s : ℝ, 0 < s →
    lengthPartition s = bridgePartition s 0 ^ 2 * irreducibleLengthPartition s

end HoneycombActual

namespace HoneycombActual.RenewalList

abbrev Marked (α : Type*) := (l : List α) × Fin l.length

def mark {α : Type*} (p : List α × α × List α) : Marked α :=
  ⟨p.1 ++ p.2.1 :: p.2.2, ⟨p.1.length, by simp⟩⟩

def unmark {α : Type*} (p : Marked α) : List α × α × List α :=
  (p.1.take p.2.val, p.1[p.2.val], p.1.drop (p.2.val+1))

theorem unmark_mark {α : Type*} (p : List α × α × List α) : unmark (mark p) = p := by
  rcases p with ⟨as, a, bs⟩
  simp [mark, unmark, List.drop_append]

theorem mark_unmark {α : Type*} (p : Marked α) : mark (unmark p) = p := by
  rcases p with ⟨l, i⟩
  have hl : l.take i.val ++ l[i.val] :: l.drop (i.val+1) = l := by
    rw [← List.drop_eq_getElem_cons i.isLt, List.take_append_drop]
  apply Sigma.ext hl
  apply (Fin.heq_ext_iff (congrArg List.length hl)).mpr
  change (l.take i.val).length = i.val
  simp [List.length_take, i.isLt.le]

noncomputable def markedEquiv (α : Type*) : (List α × α × List α) ≃ Marked α where
  toFun := mark
  invFun := unmark
  left_inv := unmark_mark
  right_inv := mark_unmark

def markedWeight {α : Type*} (q r : α → ℝ≥0∞) (p : Marked α) : ℝ≥0∞ :=
  (p.1.map q).prod * r p.1[p.2.val]

theorem sum_map_eq_sum_fin {α : Type*} (r : α → ℝ≥0∞) (l : List α) :
    (l.map r).sum = ∑ i : Fin l.length, r l[i.val] := by
  calc
    (l.map r).sum = ((List.ofFn (fun i : Fin l.length => l[i.val])).map r).sum := by
      rw [List.ofFn_getElem]
    _ = _ := by rw [List.map_ofFn, List.sum_ofFn]; rfl

theorem sum_markedWeight {α : Type*} (q r : α → ℝ≥0∞) :
    (∑' l : List α, (l.map q).prod * (l.map r).sum) =
      ∑' p : Marked α, markedWeight q r p := by
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro l
  simp only [markedWeight, tsum_fintype, ← Finset.mul_sum]
  rw [sum_map_eq_sum_fin]

theorem markedWeight_mark {α : Type*} (q r : α → ℝ≥0∞) (p : List α × α × List α) :
    markedWeight q r (mark p) =
      (p.1.map q).prod * (q p.2.1 * r p.2.1) * (p.2.2.map q).prod := by
  rcases p with ⟨as, a, bs⟩
  simp [markedWeight, mark, List.prod_append]
  ring

theorem sum_prod_reward {α : Type*} (q r : α → ℝ≥0∞) :
    (∑' l : List α, (l.map q).prod * (l.map r).sum) =
      (∑' l : List α, (l.map q).prod)^2 * ∑' a : α, q a * r a := by
  rw [sum_markedWeight, ← (markedEquiv α).tsum_eq (markedWeight q r)]
  simp_rw [show ∀ p : List α × α × List α,
      markedWeight q r (markedEquiv α p) =
        (p.1.map q).prod * (q p.2.1 * r p.2.1) * (p.2.2.map q).prod from
      markedWeight_mark q r]
  rw [@ENNReal.tsum_prod (List α) (α × List α)
    (fun as p => (as.map q).prod * (q p.1 * r p.1) * (p.2.map q).prod)]
  trans ∑' as : List α, ∑' a : α, ∑' bs : List α,
    (as.map q).prod * (q a * r a) * (bs.map q).prod
  · apply tsum_congr
    intro as
    exact @ENNReal.tsum_prod α (List α)
      (fun a bs => (as.map q).prod * (q a * r a) * (bs.map q).prod)
  · simp_rw [mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
    ring

end HoneycombActual.RenewalList

namespace HoneycombActual

def optionLength : Option Bridge → ℕ
  | none => 0
  | some b => b.length

theorem optionLength_bridgeProduct (bs : List Bridge) :
    optionLength (bridgeProduct bs) = (bs.map Bridge.length).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases h : bridgeProduct bs with
    | none =>
      have hn := (bridgeProduct_eq_none_iff bs).mp h
      subst bs
      simp [bridgeProduct, optionLength]
    | some c =>
      simpa [bridgeProduct, h, optionLength] using
        congrArg (fun n => b.length + n) ih

theorem optionLength_irreducibleProduct (bs : List IrreducibleBridge) :
    (optionLength (irreducibleProduct bs) : ℝ≥0∞) =
      (bs.map (fun b => (b.val.length : ℝ≥0∞))).sum := by
  simp [irreducibleProduct, optionLength_bridgeProduct, List.map_map, Function.comp_def]

theorem optionLengthWeight_tsum (s : ℝ) :
    (∑' b : Option Bridge, (optionLength b : ℝ≥0∞) * optionWeight s 0 b) =
      lengthPartition s := by
  rw [← (Equiv.optionEquivSumPUnit.{0,0} Bridge).symm.tsum_eq
    (fun b => (optionLength b : ℝ≥0∞) * optionWeight s 0 b)]
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  simp [optionWeight, optionLength, lengthPartition, tsum_fintype]

theorem listWeight_tsum (s u : ℝ) :
    (∑' bs : List IrreducibleBridge,
      (bs.map (fun b => discountedWeight s u b.val)).prod) = bridgePartition s u := by
  rw [← optionWeight_tsum, ← irreducibleProductEquiv.tsum_eq (optionWeight s u)]
  apply tsum_congr
  intro bs
  exact (optionWeight_irreducibleProduct s u bs).symm

theorem lengthPartition_marked (s : ℝ) :
    lengthPartition s = bridgePartition s 0 ^ 2 * irreducibleLengthPartition s := by
  rw [← optionLengthWeight_tsum, ← irreducibleProductEquiv.tsum_eq
    (fun b => (optionLength b : ℝ≥0∞) * optionWeight s 0 b)]
  calc
    (∑' bs : List IrreducibleBridge,
        (optionLength (irreducibleProductEquiv bs) : ℝ≥0∞) *
          optionWeight s 0 (irreducibleProductEquiv bs)) =
      ∑' bs : List IrreducibleBridge,
        (bs.map (fun b => discountedWeight s 0 b.val)).prod *
          (bs.map (fun b => (b.val.length : ℝ≥0∞))).sum := by
      apply tsum_congr
      intro bs
      change (optionLength (irreducibleProduct bs) : ℝ≥0∞) *
        optionWeight s 0 (irreducibleProduct bs) = _
      rw [optionLength_irreducibleProduct, optionWeight_irreducibleProduct, mul_comm]
    _ = _ := by
      rw [RenewalList.sum_prod_reward, listWeight_tsum]
      congr 1
      apply tsum_congr
      intro b
      exact mul_comm _ _

theorem lengthRewardTransformIdentity : LengthRewardTransformIdentity := by
  intro s _
  exact lengthPartition_marked s



theorem tsum_by_halfLength (f : Bridge → ℝ≥0∞) :
    (∑' b : Bridge, f b) =
      ∑' m : ℕ, ∑' b : Bridge, if b.length = 2*m then f b else 0 := by
  classical
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro b
  have hiff (m : ℕ) : b.length = 2*m ↔ m = b.length / 2 := by
    have hb := b.twice_halfLength
    omega
  simp_rw [hiff]
  simp



def truncatedIrreducibleLength (T : ℝ) : ℝ≥0∞ := by
  classical
  exact ∑' b : Bridge, if b.Irreducible then
    weight b * ENNReal.ofReal (min (b.length : ℝ) T) else 0

def ActualTruncatedLengthLower : Prop :=
  ∃ c T₀ : ℝ, 0 < c ∧ 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
    ENNReal.ofReal (c * T ^ (7/16 : ℝ)) ≤ truncatedIrreducibleLength T

theorem half_min_le_length_kernel (t : ℝ) (ht : 0 ≤ t) :
    (min t 1) / 2 ≤ 1 - Real.exp (-t) := by
  have hp : Real.exp (-t) * (t + 1) ≤ 1 := by
    calc
      Real.exp (-t) * (t + 1) ≤ Real.exp (-t) * Real.exp t :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp t) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have he := Real.exp_pos (-t)
  rcases le_total t 1 with ht1 | ht1
  · rw [min_eq_left ht1]
    by_cases h : Real.exp (-t) ≤ 1/2
    · linarith
    · have hh : (1/2 : ℝ) ≤ Real.exp (-t) := le_of_lt (lt_of_not_ge h)
      nlinarith
  · rw [min_eq_right ht1]
    nlinarith

theorem length_kernel_le_min (t : ℝ) :
    1 - Real.exp (-t) ≤ min t 1 := by
  apply le_min
  · have := Real.add_one_le_exp (-t)
    linarith
  · have := Real.exp_pos (-t)
    linarith

theorem lengthLaplaceReward_le_truncated (u : ℝ) (hu : 0 < u) :
    lengthLaplaceReward u ≤
      ENNReal.ofReal u * truncatedIrreducibleLength u⁻¹ := by
  classical
  unfold lengthLaplaceReward truncatedIrreducibleLength
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro b
  by_cases hi : b.Irreducible
  · simp only [hi, ite_true]
    have hm : u * min (b.length : ℝ) u⁻¹ = min (u * b.length) 1 := by
      rw [mul_min_of_nonneg _ _ hu.le, mul_inv_cancel₀ hu.ne']
    have hk : 1 - Real.exp (-u * (b.length : ℝ)) ≤
        u * min (b.length : ℝ) u⁻¹ := by
      rw [hm]
      simpa only [neg_mul] using length_kernel_le_min (u * b.length)
    calc
      weight b * ENNReal.ofReal (1 - Real.exp (-u * (b.length : ℝ))) ≤
          weight b * ENNReal.ofReal (u * min (b.length : ℝ) u⁻¹) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hk) _
      _ = _ := by rw [ENNReal.ofReal_mul hu.le]; ac_rfl
  · simp only [hi, ite_false, mul_zero]
    exact le_rfl

theorem truncated_le_lengthLaplaceReward (u : ℝ) (hu : 0 < u) :
    ENNReal.ofReal (u/2) * truncatedIrreducibleLength u⁻¹ ≤
      lengthLaplaceReward u := by
  classical
  unfold lengthLaplaceReward truncatedIrreducibleLength
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro b
  by_cases hi : b.Irreducible
  · simp only [hi, ite_true]
    have hm : u * min (b.length : ℝ) u⁻¹ = min (u * b.length) 1 := by
      rw [mul_min_of_nonneg _ _ hu.le, mul_inv_cancel₀ hu.ne']
    have hk : (u/2) * min (b.length : ℝ) u⁻¹ ≤
        1 - Real.exp (-u * (b.length : ℝ)) := by
      calc
        (u/2) * min (b.length : ℝ) u⁻¹ = min (u * b.length) 1 / 2 := by
          rw [← hm]; ring
        _ ≤ _ := by
          simpa only [neg_mul] using
            half_min_le_length_kernel (u * b.length) (by positivity)
    calc
      ENNReal.ofReal (u/2) * (weight b * ENNReal.ofReal (min (b.length : ℝ) u⁻¹)) =
          weight b * ENNReal.ofReal ((u/2) * min (b.length : ℝ) u⁻¹) := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ u/2)]; ac_rfl
      _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal hk) _
  · simp only [hi, ite_false, mul_zero]
    exact le_rfl

private theorem exponent_balance (t : ℝ) (ht : 0 < t) :
    t * (t⁻¹) ^ (7/16 : ℝ) = t ^ (9/16 : ℝ) := by
  rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
  calc
    t * t ^ (-(7/16 : ℝ)) = t ^ (1 : ℝ) * t ^ (-(7/16 : ℝ)) := by
      rw [Real.rpow_one]
    _ = t ^ ((1 : ℝ) + -(7/16 : ℝ)) := (Real.rpow_add ht _ _).symm
    _ = _ := by norm_num

theorem actualLengthLaplaceLower_iff_truncated :
    ActualLengthLaplaceLower ↔ ActualTruncatedLengthLower := by
  constructor
  · rintro ⟨c, u₀, hc, hu₀, h⟩
    refine ⟨c, u₀⁻¹, hc, inv_pos.mpr hu₀, ?_⟩
    intro T hT
    have hTp : 0 < T := lt_of_lt_of_le (inv_pos.mpr hu₀) hT
    have hu : T⁻¹ ≤ u₀ := by
      have hi := (inv_le_inv₀ hTp (inv_pos.mpr hu₀)).mpr hT
      simpa only [inv_inv] using hi
    have hl := (h T⁻¹ (inv_pos.mpr hTp) hu).trans
      (lengthLaplaceReward_le_truncated T⁻¹ (inv_pos.mpr hTp))
    simp only [inv_inv] at hl
    have heq : ENNReal.ofReal (T⁻¹) * ENNReal.ofReal (c * T ^ (7/16 : ℝ)) =
        ENNReal.ofReal (c * (T⁻¹) ^ (9/16 : ℝ)) := by
      rw [← ENNReal.ofReal_mul (inv_pos.mpr hTp).le]
      congr 1
      have hb := exponent_balance T⁻¹ (inv_pos.mpr hTp)
      simp only [inv_inv] at hb
      calc
        T⁻¹ * (c * T ^ (7/16 : ℝ)) = c * (T⁻¹ * T ^ (7/16 : ℝ)) := by ring
        _ = _ := by rw [hb]
    apply (ENNReal.mul_le_mul_iff_right
      (ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hTp))) ENNReal.ofReal_ne_top).mp
    rw [heq]
    exact hl
  · rintro ⟨c, T₀, hc, hT₀, h⟩
    refine ⟨c/2, T₀⁻¹, by positivity, inv_pos.mpr hT₀, ?_⟩
    intro u hu hu₀
    have hT : T₀ ≤ u⁻¹ := by
      have hi := (inv_le_inv₀ (inv_pos.mpr hT₀) hu).mpr hu₀
      simpa only [inv_inv] using hi
    have hl := mul_le_mul_right (h u⁻¹ hT) (ENNReal.ofReal (u/2))
    have heq : ENNReal.ofReal (u/2) * ENNReal.ofReal (c * (u⁻¹) ^ (7/16 : ℝ)) =
        ENNReal.ofReal ((c/2) * u ^ (9/16 : ℝ)) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ u/2)]
      congr 1
      calc
        (u/2) * (c * (u⁻¹) ^ (7/16 : ℝ)) =
            (c/2) * (u * (u⁻¹) ^ (7/16 : ℝ)) := by ring
        _ = _ := by rw [exponent_balance u hu]
    rw [heq] at hl
    exact hl.trans (truncated_le_lengthLaplaceReward u hu)

def irreducibleCount (m : ℕ) : ℕ :=
  Nat.card {b : Bridge // b.length = 2*m ∧ b.Irreducible}

theorem truncatedIrreducibleLength_eq_count_series (T : ℝ) :
    truncatedIrreducibleLength T = ∑' m : ℕ,
      ENNReal.ofReal (min (2*m : ℕ) T) *
        ((irreducibleCount m : ℝ≥0∞) * ENNReal.ofReal (rho ^ (2*m))) := by
  classical
  rw [truncatedIrreducibleLength, tsum_by_halfLength]
  apply tsum_congr
  intro m
  unfold irreducibleCount
  rw [← exactLengthMass_eq (2*m) Bridge.Irreducible]
  unfold criticalMass
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  by_cases hl : b.length = 2*m <;> by_cases hi : b.Irreducible <;>
    simp [hl, hi]
  ac_rfl

def ActualCoefficientLower : Prop :=
  ∃ c T₀ : ℝ, 0 < c ∧ 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
    ENNReal.ofReal (c * T ^ (7/16 : ℝ)) ≤ ∑' m : ℕ,
      ENNReal.ofReal (min (2*m : ℕ) T) *
        ((irreducibleCount m : ℝ≥0∞) * ENNReal.ofReal (rho ^ (2*m)))

theorem actualLengthLaplaceLower_iff_coefficients :
    ActualLengthLaplaceLower ↔ ActualCoefficientLower := by
  rw [actualLengthLaplaceLower_iff_truncated]
  simp only [ActualTruncatedLengthLower, ActualCoefficientLower,
    truncatedIrreducibleLength_eq_count_series]

end HoneycombActual

end

end OAI
