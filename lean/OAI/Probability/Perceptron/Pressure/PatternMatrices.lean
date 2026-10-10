import Mathlib
import OAI.Probability.Perceptron.Interpolation.OverlapArray

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma block_event_swap (μ : Measure OverlapArray) (hEx : OverlapSwapInvariant μ)
    {n : ℕ} (p q : Fin n) {s : Set (OverlapBlock n)} (hs : MeasurableSet s) :
    μ.real (overlapBlock id n ⁻¹' (relabelBlock (Equiv.swap p q) ⁻¹' s)) =
      μ.real (overlapBlock id n ⁻¹' s) := by
  have heq : overlapBlock id n ⁻¹' (relabelBlock (Equiv.swap p q) ⁻¹' s) =
      relabelArray (Equiv.swap p.val q.val) ⁻¹' (overlapBlock id n ⁻¹' s) := by
    ext Q
    change relabelBlock (Equiv.swap p q) (overlapBlock id n Q) ∈ s ↔ _
    rw [relabelBlock_swap]
    rfl
  rw [heq]
  exact (hEx _ _).measureReal_preimage
    (hs.preimage (Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
      (measurable_pi_apply _).comp (measurable_pi_apply _))).nullMeasurableSet

theorem gg_duplicate_index (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    {r : ℕ} (hr : 1 ≤ r) (p : Fin (r + 1)) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hA : 0 < μ.real (overlapBlock id (r + 1) ⁻¹' s))
    (hrow : ∀ Q ∈ overlapBlock id (r + 1) ⁻¹' s,
      ∀ j : Fin (r + 1), j ≠ p → Q p j < t) :
    0 < μ.real ((overlapBlock id (r + 1) ⁻¹' s) ∩ replaceEvent p s (r + 1) ∩
      {Q | Q p (r + 1) < t}) := by
  let q : Fin (r + 1) := Fin.last r
  let e := Equiv.swap p q
  let π := Equiv.swap p.val q.val
  let s' := relabelBlock e ⁻¹' s
  have hs' : MeasurableSet s' := hs.preimage (relabelBlock_measurable e)
  have hbase : copyEvent r s' r = overlapBlock id (r + 1) ⁻¹' s' := by
    ext Q
    change copyBlock r r Q ∈ s' ↔ overlapBlock id (r + 1) Q ∈ s'
    have hb : copyBlock r r Q = overlapBlock id (r + 1) Q := by
      ext a b
      simp [copyBlock, overlapBlock]
    rw [hb]
  have hA' : 0 < μ.real (copyEvent r s' r) := by
    rw [hbase]
    exact (block_event_swap μ hEx p q hs).symm ▸ hA
  have hrow' : ∀ Q ∈ copyEvent r s' r, ∀ j < r, Q r j < t := by
    intro Q hQ j hj
    have hmem : relabelArray π Q ∈ overlapBlock id (r + 1) ⁻¹' s := by
      rw [hbase] at hQ
      change relabelBlock e (overlapBlock id (r + 1) Q) ∈ s at hQ
      rwa [relabelBlock_swap] at hQ
    let a : Fin (r + 1) := ⟨j, by omega⟩
    have hne : e a ≠ p := by
      intro h
      have h' := congrArg e h
      have haq : a = q := by simpa [e] using h'
      have := congrArg Fin.val haq
      dsimp [a, q] at this
      omega
    have h := hrow (relabelArray π Q) hmem (e a) hne
    have hp : π p.val = r := by simp [π, q]
    have ha : π (e a).val = j := by simp [π, e, fin_swap_val, a]
    simpa only [relabelArray, hp, ha] using h
  have hD := gg_duplicate_last μ hEx hGG hr hs' t hA' hrow'
  have hset : relabelArray π ⁻¹' duplicateEvent r s' t (r + 1) =
      (overlapBlock id (r + 1) ⁻¹' s) ∩ replaceEvent p s (r + 1) ∩
        {Q | Q p (r + 1) < t} := by
    ext Q
    have hfirst : copyBlock r r (relabelArray π Q) ∈ s' ↔
        overlapBlock id (r + 1) Q ∈ s := by
      change relabelBlock e (copyBlock r r (relabelArray π Q)) ∈ s ↔ _
      have hb : copyBlock r r (relabelArray π Q) =
          overlapBlock id (r + 1) (relabelArray π Q) := by
        ext a b
        simp [copyBlock, overlapBlock]
      rw [hb, relabelBlock_swap, relabelArray_swap_swap]
    have hsecond : copyBlock r (r + 1) (relabelArray π Q) ∈ s' ↔
        replaceBlock p (r + 1) Q ∈ s := by
      change relabelBlock e (copyBlock r (r + 1) (relabelArray π Q)) ∈ s ↔ _
      rw [← replaceBlock_last]
      change relabelBlock (Equiv.swap p q)
        (replaceBlock q (r + 1) (relabelArray (Equiv.swap p.val q.val) Q)) ∈ s ↔ _
      rw [replaceBlock_swap p q (le_refl _)]
    have hp : π r = p.val := by exact Equiv.swap_apply_right _ _
    have hnew : π (r + 1) = r + 1 :=
      Equiv.swap_apply_of_ne_of_ne (by have := p.isLt; omega) (by dsimp [q]; omega)
    change ((copyBlock r r (relabelArray π Q) ∈ s' ∧
      copyBlock r (r + 1) (relabelArray π Q) ∈ s') ∧
      Q (π r) (π (r + 1)) < t) ↔ ((overlapBlock id (r + 1) Q ∈ s ∧
        replaceBlock p (r + 1) Q ∈ s) ∧ Q p (r + 1) < t)
    rw [hfirst, hsecond, hp, hnew]
  rw [← hset]
  rwa [(hEx _ _).measureReal_preimage
    (duplicateEvent_measurable r hs' t (r + 1)).nullMeasurableSet]

def patternMatrices {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) : Set (OverlapBlock n) :=
  {B | ∀ i j, i ≠ j → B i j ∈ C (labels i) (labels j)}

lemma patternMatrices_measurable {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) :
    MeasurableSet (patternMatrices labels C) := by
  simp only [patternMatrices, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact (hC _ _).preimage ((measurable_pi_apply j).comp (measurable_pi_apply i))

def appendLabel {κ : Type*} {n : ℕ} (labels : Fin n → κ) (k : κ) : Fin (n + 1) → κ :=
  Fin.lastCases k labels

@[simp] lemma appendLabel_last {κ : Type*} {n : ℕ} (labels : Fin n → κ) (k : κ) :
    appendLabel labels k (Fin.last n) = k := Fin.lastCases_last

@[simp] lemma appendLabel_castSucc {κ : Type*} {n : ℕ} (labels : Fin n → κ) (k : κ)
    (i : Fin n) : appendLabel labels k i.castSucc = labels i := Fin.lastCases_castSucc i

lemma pattern_append_of_duplicate {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (p : Fin n) (t : ℝ) (hdiag : C (labels p) (labels p) = Iio t)
    (Q : OverlapArray) (hSym : ∀ i j, Q i j = Q j i)
    (hA : overlapBlock id n Q ∈ patternMatrices labels C)
    (hB : replaceBlock p n Q ∈ patternMatrices labels C) (hedge : Q p n < t) :
    overlapBlock id (n + 1) Q ∈ patternMatrices (appendLabel labels (labels p)) C := by
  intro i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · intro j
    refine Fin.lastCases (fun h => (h rfl).elim) (fun b _ => ?_) j
    by_cases hb : b = p
    · subst b
      simpa [overlapBlock, hdiag, hSym n p] using hedge
    · have h := hB p b (Ne.symm hb)
      simpa [replaceBlock, replaceIndex, hb, overlapBlock] using h
  · intro j
    refine Fin.lastCases (fun _ => ?_) (fun b hab => ?_) j
    · by_cases ha : a = p
      · subst a
        simpa [overlapBlock, hdiag] using hedge
      · have h := hB a p ha
        simpa [replaceBlock, replaceIndex, ha, overlapBlock] using h
    · have h := hA a b (fun h => hab (congrArg Fin.castSucc h))
      simpa [overlapBlock] using h

theorem gg_pattern_append (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    {κ : Type*} {r : ℕ} (hr : 1 ≤ r) (labels : Fin (r + 1) → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (p : Fin (r + 1)) (t : ℝ)
    (hdiag : C (labels p) (labels p) = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id (r + 1) ⁻¹' patternMatrices labels C)) :
    0 < μ.real (overlapBlock id (r + 1 + 1) ⁻¹'
      patternMatrices (appendLabel labels (labels p)) C) := by
  have hd := gg_duplicate_index μ hEx hGG hr p (patternMatrices_measurable labels C hC) t hA
    (fun Q hQ j hj => hcut _ _ (hQ p j (Ne.symm hj)))
  apply hd.trans_le
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hSym] with Q hQ
  exact fun h => pattern_append_of_duplicate labels C p t hdiag Q hQ h.1.1 h.1.2 h.2

lemma gg_pattern_append_nat (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    {κ : Type*} {n : ℕ} (hn : 2 ≤ n) (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (p : Fin n) (t : ℝ)
    (hdiag : C (labels p) (labels p) = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id n ⁻¹' patternMatrices labels C)) :
    0 < μ.real (overlapBlock id (n + 1) ⁻¹'
      patternMatrices (appendLabel labels (labels p)) C) := by
  cases n with
  | zero => omega
  | succ r => exact gg_pattern_append μ hEx hGG hSym (by omega) labels C hC p t hdiag hcut hA

def tripleLabels (n : ℕ) (i : Fin n) : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩

lemma appendLabel_tripleLabels {n : ℕ} (hn : 3 ≤ n) :
    appendLabel (tripleLabels n) (tripleLabels n ⟨n % 3, (Nat.mod_lt _ (by omega)).trans_le hn⟩) =
      tripleLabels (n + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · apply Fin.ext
    simp [tripleLabels]
  · simp [tripleLabels]

theorem gg_triple_pattern (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (C : Fin 3 → Fin 3 → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (t : ℝ)
    (hdiag : ∀ k, C k k = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id 3 ⁻¹' patternMatrices (tripleLabels 3) C)) :
    ∀ n ≥ 3, 0 < μ.real (overlapBlock id n ⁻¹' patternMatrices (tripleLabels n) C) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hA
  | succ n hn ih =>
    have h := gg_pattern_append_nat μ hEx hGG hSym (by omega) (tripleLabels n) C hC
      ⟨n % 3, (Nat.mod_lt _ (by omega)).trans_le hn⟩ t (hdiag _) hcut ih
    rwa [appendLabel_tripleLabels hn] at h

open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def replicaMean {n : ℕ} (v : Fin n → H) : H := (n : ℝ)⁻¹ • ∑ i, v i

lemma inner_replicaMean {n : ℕ} (v w : Fin n → H) :
    ⟪replicaMean v, replicaMean w⟫_ℝ =
      (n : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, ⟪v i, w j⟫_ℝ := by
  simp only [replicaMean, real_inner_smul_left, real_inner_smul_right]
  rw [sum_inner]
  simp_rw [inner_sum]
  ring

lemma replicaMean_norm_sq_le {n : ℕ} (hn : 0 < n) (v : Fin n → H) {c : ℝ}
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ 1)
    (hoff : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ ≤ c) :
    ‖replicaMean v‖ ^ 2 ≤ c + (1 - c) / n := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrow (i : Fin n) : (∑ j, ⟪v i, v j⟫_ℝ) ≤ 1 + ((n : ℝ) - 1) * c := by
    have hs : (∑ j ∈ Finset.univ.erase i, ⟪v i, v j⟫_ℝ) ≤
        ∑ _j ∈ Finset.univ.erase i, c :=
      Finset.sum_le_sum fun j hj => hoff i j (Ne.symm (Finset.ne_of_mem_erase hj))
    have hc : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      rw [Nat.cast_sub hn]
      norm_num
    simp only [Finset.sum_const, nsmul_eq_mul, hc] at hs
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [real_inner_self_eq_norm_sq]
    linarith [hdiag i]
  rw [← real_inner_self_eq_norm_sq, inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  calc
    (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, v j⟫_ℝ) ≤
      (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * (1 + ((n : ℝ) - 1) * c)) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = c + (1 - c) / n := by field_simp; ring

lemma inner_replicaMean_eq {n : ℕ} (hn : 0 < n) (v w : Fin n → H) {a : ℝ}
    (h : ∀ i j, ⟪v i, w j⟫_ℝ = a) :
    ⟪replicaMean v, replicaMean w⟫_ℝ = a := by
  rw [inner_replicaMean]
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp

lemma duplicate_blocks_bound {n : ℕ} (hn : 0 < n) (v : Fin 3 → Fin n → H)
    {a b c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hdiag : ∀ k i, ‖v k i‖ ^ 2 ≤ 1)
    (hoff : ∀ k i j, i ≠ j → ⟪v k i, v k j⟫_ℝ ≤ c)
    (h12 : ∀ i j, ⟪v 0 i, v 1 j⟫_ℝ = a)
    (h13 : ∀ i j, ⟪v 0 i, v 2 j⟫_ℝ = b)
    (h23 : ∀ i j, ⟪v 1 i, v 2 j⟫_ℝ = c) :
    (a - b) ^ 2 ≤ 2 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let x := replicaMean (v 0)
  let y := replicaMean (v 1)
  let z := replicaMean (v 2)
  have hx := replicaMean_norm_sq_le hn (v 0) (hdiag 0) (hoff 0)
  have hy := replicaMean_norm_sq_le hn (v 1) (hdiag 1) (hoff 1)
  have hz := replicaMean_norm_sq_le hn (v 2) (hdiag 2) (hoff 2)
  have hxy : ⟪x, y⟫_ℝ = a := inner_replicaMean_eq hn _ _ h12
  have hxz : ⟪x, z⟫_ℝ = b := inner_replicaMean_eq hn _ _ h13
  have hyz : ⟪y, z⟫_ℝ = c := inner_replicaMean_eq hn _ _ h23
  change ‖x‖ ^ 2 ≤ _ at hx
  change ‖y‖ ^ 2 ≤ _ at hy
  change ‖z‖ ^ 2 ≤ _ at hz
  have hsmall : (1 - c) / n ≤ 1 - c :=
    (div_le_iff₀ hnpos).mpr (by nlinarith)
  have hx1 : ‖x‖ ^ 2 ≤ 1 := by linarith
  have hdiff : ‖y - z‖ ^ 2 ≤ 2 * ((1 - c) / n) := by
    rw [norm_sub_sq_real, hyz]
    linarith
  have hcs : (a - b) ^ 2 ≤ ‖x‖ ^ 2 * ‖y - z‖ ^ 2 := by
    have h := abs_real_inner_le_norm x (y - z)
    rw [inner_sub_right, hxy, hxz] at h
    have hs := sq_le_sq₀ (abs_nonneg (a - b))
      (mul_nonneg (norm_nonneg x) (norm_nonneg (y - z))) |>.mpr h
    simpa only [sq_abs, mul_pow] using hs
  calc
    (a - b) ^ 2 ≤ ‖x‖ ^ 2 * ‖y - z‖ ^ 2 := hcs
    _ ≤ 1 * ‖y - z‖ ^ 2 := mul_le_mul_of_nonneg_right hx1 (sq_nonneg _)
    _ ≤ 2 * ((1 - c) / n) := by simpa using hdiff
    _ ≤ 2 / n := by apply (le_div_iff₀ hnpos).mpr; nlinarith [div_mul_cancel₀ (1 - c) (ne_of_gt hnpos)]

lemma arbitrary_duplicate_blocks_equal {a b c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hdup : ∀ n : ℕ, 0 < n → ∃ v : Fin 3 → Fin n → H,
      (∀ k i, ‖v k i‖ ^ 2 ≤ 1) ∧
      (∀ k i j, i ≠ j → ⟪v k i, v k j⟫_ℝ ≤ c) ∧
      (∀ i j, ⟪v 0 i, v 1 j⟫_ℝ = a) ∧
      (∀ i j, ⟪v 0 i, v 2 j⟫_ℝ = b) ∧
      (∀ i j, ⟪v 1 i, v 2 j⟫_ℝ = c)) : a = b := by
  have hbound (n : ℕ) : (a - b) ^ 2 ≤ 2 / ((n : ℝ) + 1) := by
    obtain ⟨v, hd, ho, h12, h13, h23⟩ := hdup (n + 1) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using
      duplicate_blocks_bound (by omega : 0 < n + 1) v hc0 hc1 hd ho h12 h13 h23
  have ht : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, mul_one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.const_mul 2
  have hs : (a - b) ^ 2 ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hbound)
  nlinarith [sq_nonneg (a - b)]

lemma replicaMean_norm_le_one {n : ℕ} (hn : 0 < n) (v : Fin n → H)
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ 1) : ‖replicaMean v‖ ≤ 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hsum : ‖∑ i, v i‖ ≤ (n : ℝ) := by
    calc
      ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        nlinarith [hdiag i, norm_nonneg (v i)]
      _ = n := by simp
  calc
    ‖replicaMean v‖ = (n : ℝ)⁻¹ * ‖∑ i, v i‖ := by
      simp [replicaMean, norm_smul]
    _ ≤ (n : ℝ)⁻¹ * n := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ hn0

lemma inner_replicaMean_le {n : ℕ} (hn : 0 < n) (v w : Fin n → H) {a : ℝ}
    (h : ∀ i j, ⟪v i, w j⟫_ℝ ≤ a) : ⟪replicaMean v, replicaMean w⟫_ℝ ≤ a := by
  rw [inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, w j⟫_ℝ) ≤
      (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ((n : ℝ) * a)) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = a := by field_simp

lemma le_inner_replicaMean {n : ℕ} (hn : 0 < n) (v w : Fin n → H) {a : ℝ}
    (h : ∀ i j, a ≤ ⟪v i, w j⟫_ℝ) : a ≤ ⟪replicaMean v, replicaMean w⟫_ℝ := by
  rw [inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    a = (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ((n : ℝ) * a)) := by field_simp
    _ ≤ (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, w j⟫_ℝ) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)

lemma duplicate_ordered_blocks_bound {n : ℕ} (hn : 0 < n) (v : Fin 3 → Fin n → H)
    {a b c t : ℝ} (hab : a ≤ b)
    (hdiag : ∀ k i, ‖v k i‖ ^ 2 ≤ 1)
    (hoff : ∀ k i j, i ≠ j → ⟪v k i, v k j⟫_ℝ ≤ t)
    (h12 : ∀ i j, ⟪v 0 i, v 1 j⟫_ℝ ≤ a)
    (h13 : ∀ i j, b ≤ ⟪v 0 i, v 2 j⟫_ℝ)
    (h23 : ∀ i j, c ≤ ⟪v 1 i, v 2 j⟫_ℝ) :
    (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
  let x := replicaMean (v 0)
  let y := replicaMean (v 1)
  let z := replicaMean (v 2)
  have hx := replicaMean_norm_le_one hn (v 0) (hdiag 0)
  have hy := replicaMean_norm_sq_le hn (v 1) (hdiag 1) (hoff 1)
  have hz := replicaMean_norm_sq_le hn (v 2) (hdiag 2) (hoff 2)
  have hxy : ⟪x, y⟫_ℝ ≤ a := inner_replicaMean_le hn _ _ h12
  have hxz : b ≤ ⟪x, z⟫_ℝ := le_inner_replicaMean hn _ _ h13
  have hyz : c ≤ ⟪y, z⟫_ℝ := le_inner_replicaMean hn _ _ h23
  change ‖x‖ ≤ _ at hx
  change ‖y‖ ^ 2 ≤ _ at hy
  change ‖z‖ ^ 2 ≤ _ at hz
  have hx1 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hdiff : ‖z - y‖ ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
    rw [norm_sub_sq_real, real_inner_comm]
    linarith
  have hinner : b - a ≤ ⟪x, z - y⟫_ℝ := by rw [inner_sub_right]; linarith
  have hnonneg : 0 ≤ ⟪x, z - y⟫_ℝ := by linarith
  have habsq : (b - a) ^ 2 ≤ ⟪x, z - y⟫_ℝ ^ 2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hab) hnonneg).mpr hinner
  have hcs : ⟪x, z - y⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * ‖z - y‖ ^ 2 := by
    have h := abs_real_inner_le_norm x (z - y)
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg _))).mpr h
    simpa only [sq_abs, mul_pow] using hs
  exact habsq.trans (hcs.trans ((mul_le_mul_of_nonneg_right hx1 (sq_nonneg _)).trans
    (by simpa using hdiff)))

lemma posSemidef_standard_basis_inner {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) (i j : Fin n) :
    letI := B.toSeminormedAddCommGroup hB
    letI := B.toInnerProductSpace hB
    ⟪(Pi.single i 1 : Fin n → ℝ), Pi.single j 1⟫_ℝ = B i j := by
  change (B *ᵥ Pi.single j 1) ⬝ᵥ star (Pi.single i 1) = B i j
  simp

def triangleConstraints (a b c t : ℝ) (k l : Fin 3) : Set ℝ :=
  if k = l then Iio t
  else if (k = 0 ∧ l = 1) ∨ (k = 1 ∧ l = 0) then Iio a
  else if (k = 0 ∧ l = 2) ∨ (k = 2 ∧ l = 0) then Ioo b t
  else Ioo c t

lemma triangleConstraints_measurable (a b c t : ℝ) (k l : Fin 3) :
    MeasurableSet (triangleConstraints a b c t k l) := by
  unfold triangleConstraints
  split_ifs <;> measurability

end SphericalPerceptronFreeEnergy
end

end OAI
