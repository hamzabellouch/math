import OAI.Algebra.DepthFive.IsolatedFlip
import OAI.Algebra.DepthFive.SwitchRestoration

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.IsolatedWeight

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Internal neighboring positions of the same normal (false) type. -/
def falseNeighbors (R : ι → ι → Prop) (w : ι → Bool) (i : ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun j => R i j ∧ w j = false)

/-- The coincidence correction factors at the normal V positions. -/
def correction (V : Finset ι) (R : ι → ι → Prop) (A x : ℝ)
    (w : ι → Bool) : ℝ := by
  classical
  exact ∏ i ∈ V.filter (fun i => w i = false),
    (1 + A * x ^ (falseNeighbors R w i).card)

/-- Restoring any subset of an independent V set does not change the
neighbors of any V position. Endpoints are allowed in V. -/
theorem falseNeighbors_unset {V T : Finset ι} {R : ι → ι → Prop}
    (hT : T ⊆ V) (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (w : ι → Bool) {i : ι} (hi : i ∈ V) :
    falseNeighbors R (IsolatedFlip.unset w T) i = falseNeighbors R w i := by
  classical
  ext j
  by_cases hr : R i j
  · have hj : j ∉ T := fun ht => hV i hi j hr (hT ht)
    simp [falseNeighbors, IsolatedFlip.unset, hr, hj]
  · simp [falseNeighbors, hr]

omit [DecidableEq ι] in
theorem falseNeighbors_eq_empty {R : ι → ι → Prop} {w : ι → Bool} {i : ι}
    (h : ∀ j, R i j → w j = true) : falseNeighbors R w i = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hh := Finset.mem_filter.mp hj
  have heq := h j hh.2.1
  simp only [heq, Bool.true_eq_false] at hh
  exact hh.2.2

omit [Fintype ι] in
/-- The normal V positions after restoration consist of the old normal
positions together with the restored subset. -/
theorem falseVertices_unset {V T : Finset ι} (hT : T ⊆ V)
    (w : ι → Bool) :
    (V.filter fun i => IsolatedFlip.unset w T i = false) =
      (V.filter fun i => w i = false) ∪ T := by
  classical
  ext i
  by_cases hi : i ∈ T
  · simp [IsolatedFlip.unset, hi, hT hi]
  · simp [IsolatedFlip.unset, hi]

omit [Fintype ι] [DecidableEq ι] in
theorem falseVertices_disjoint {V T : Finset ι} (w : ι → Bool)
    (hw : ∀ i ∈ T, w i = true) :
    Disjoint (V.filter fun i => w i = false) T := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi ht
  have hf := (Finset.mem_filter.mp hi).2
  have ht := hw i ht
  simp only [ht, Bool.true_eq_false] at hf

/-- The exact local correction-product factor in the isolated-position flip.
Every restored position has no normal neighbors, and hence contributes `1+A`. -/
theorem correction_unset {V T : Finset ι} {R : ι → ι → Prop}
    (hT : T ⊆ V) (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (w : ι → Bool) (hw : ∀ i ∈ T, w i = true)
    (hnear : ∀ i ∈ T, ∀ j, R i j → w j = true) (A x : ℝ) :
    correction V R A x (IsolatedFlip.unset w T) =
      correction V R A x w * (1 + A) ^ T.card := by
  classical
  unfold correction
  rw [falseVertices_unset hT w, Finset.prod_union (falseVertices_disjoint w hw)]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [falseNeighbors_unset hT hV w (Finset.mem_filter.mp hi).1]
  · calc
      _ = ∏ _i ∈ T, (1 + A) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [falseNeighbors_unset hT hV w (hT hi),
          falseNeighbors_eq_empty (hnear i hi)]
        simp
      _ = (1 + A) ^ T.card := by simp

/-- True positions in the complementary variable group are unchanged. -/
theorem complement_trueVertices_unset {V T : Finset ι} (hT : T ⊆ V)
    (w : ι → Bool) :
    ((Finset.univ \ V).filter fun i => IsolatedFlip.unset w T i = true) =
      ((Finset.univ \ V).filter fun i => w i = true) := by
  classical
  ext i
  by_cases hi : i ∈ V
  · simp [hi]
  · have hit : i ∉ T := fun ht => hi (hT ht)
    simp [IsolatedFlip.unset, hi, hit]

/-- The actual weighted word summand, with `A = alpha⁻¹`, `B = beta`,
and `x = n⁻¹`. The relation records internal adjacency. -/
def weight (edges : Finset (ι × ι)) (V : Finset ι) (R : ι → ι → Prop)
    (A B x : ℝ) (w : ι → Bool) : ℝ := by
  classical
  exact x ^ SwitchRestoration.switchCount edges w *
    A ^ (V.filter fun i => w i = true).card *
    B ^ ((Finset.univ \ V).filter fun i => w i = true).card *
    correction V R A x w

/-- Exact isolated-flip weight identity given the switch-count increment.
The switch increment is supplied by `switchCount_restore_eq_add_twice_card`.
No bound or positivity is needed except nonvanishing of the D-layer weight. -/
theorem weight_unset {edges : Finset (ι × ι)} {V T : Finset ι}
    {R : ι → ι → Prop} (hT : T ⊆ V)
    (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (w : ι → Bool) (hw : ∀ i ∈ T, w i = true)
    (hnear : ∀ i ∈ T, ∀ j, R i j → w j = true)
    (hswitch : SwitchRestoration.switchCount edges (IsolatedFlip.unset w T) =
      SwitchRestoration.switchCount edges w + 2 * T.card)
    {A : ℝ} (hA : A ≠ 0) (B x : ℝ) :
    weight edges V R A B x (IsolatedFlip.unset w T) =
      weight edges V R A B x w * (x ^ 2 * (1 + A) / A) ^ T.card := by
  classical
  have hcount := SwitchRestoration.trueVertices_restore_card_add V T w hT hw
  change (V.filter fun i => IsolatedFlip.unset w T i = true).card + T.card =
      (V.filter fun i => w i = true).card at hcount
  unfold weight
  rw [hswitch, complement_trueVertices_unset hT w,
    correction_unset hT hV w hw hnear A x, ← hcount]
  simp only [pow_add, pow_mul, mul_pow, div_pow]
  field_simp

/-- The isolated-flip identity for the actual word weight. Only interior
positions (of edge degree two) may flip, while V may also contain endpoints. -/
theorem weight_flip {edges : Finset (ι × ι)} {V S : Finset ι}
    {R : ι → ι → Prop} (hS : S ⊆ V)
    (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (hR : ∀ e ∈ edges, R e.1 e.2 ∧ R e.2 e.1)
    (hdegree : ∀ i ∈ S, SwitchRestoration.endpointDegree edges i = 2)
    {A : ℝ} (hA : A ≠ 0) (B x : ℝ) (w : ι → Bool) :
    weight edges V R A B x w =
      weight edges V R A B x (IsolatedFlip.flip S R w) *
        (x ^ 2 * (1 + A) / A) ^ (IsolatedFlip.removed S R w).card := by
  classical
  let T := IsolatedFlip.removed S R w
  let y := IsolatedFlip.flip S R w
  have hTe : T ⊆ IsolatedFlip.eligible S R w := IsolatedFlip.removed_subset S R w
  have hTS : T ⊆ S := hTe.trans (IsolatedFlip.eligible_subset S R w)
  have hTV : T ⊆ V := hTS.trans hS
  have hy : ∀ i ∈ T, y i = true := by
    intro i hi
    simp only [y, IsolatedFlip.flip, ite_eq_left (hTe hi)]
  have hnear : ∀ i ∈ T, ∀ j, R i j → y j = true := by
    intro i hi j hij
    have hwj := (IsolatedFlip.mem_eligible.mp (hTe hi)).2 j hij
    simp [y, IsolatedFlip.flip, hwj]
  have hsw : SwitchRestoration.switchCount edges (IsolatedFlip.unset y T) =
      SwitchRestoration.switchCount edges y + 2 * T.card := by
    apply SwitchRestoration.switchCount_restore_eq_add_twice_card
    · intro e he h
      rcases h with h | h
      · exact ⟨hy _ h, hnear _ h _ (hR e he).1⟩
      · exact ⟨hnear _ h _ (hR e he).2, hy _ h⟩
    · intro e he h
      exact hV e.1 (hTV h.1) e.2 (hR e he).1 (hTV h.2)
    · intro i hi
      exact hdegree i (hTS hi)
  have h := weight_unset hTV hV y hy hnear hsw hA B x
  simpa only [y, T, IsolatedFlip.unset_flip_removed] using h

/-- Nonnegative parameters give a nonnegative word weight. -/
theorem weight_nonneg (edges : Finset (ι × ι)) (V : Finset ι)
    (R : ι → ι → Prop) {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x)
    (w : ι → Bool) : 0 ≤ weight edges V R A B x w := by
  classical
  unfold weight correction
  positivity

/-- Summing the exact word-weight identity over the fibers removes all
isolated positions at a multiplicative cost `(1+x²(1+A)/A)^|S|`. -/
theorem sum_weight_le_fixed {edges : Finset (ι × ι)} {V S : Finset ι}
    {R : ι → ι → Prop} (hS : S ⊆ V)
    (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (hR : ∀ e ∈ edges, R e.1 e.2 ∧ R e.2 e.1)
    (hdegree : ∀ i ∈ S, SwitchRestoration.endpointDegree edges i = 2)
    {A B x : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hx : 0 ≤ x) :
    (∑ w : ι → Bool, weight edges V R A B x w) ≤
      (1 + x ^ 2 * (1 + A) / A) ^ S.card *
        ∑ w ∈ Finset.univ.filter (fun w => IsolatedFlip.flip S R w = w),
          weight edges V R A B x w := by
  classical
  apply IsolatedFlip.correction_removal
  · intro i hi j hij hj
    exact hV i (hS hi) j hij (hS hj)
  · positivity
  · exact weight_nonneg edges V R hA.le hB hx
  · exact weight_flip hS hV hR hdegree hA.ne' B x

/-- A normal position in the flip set of a fixed word has at least one
normal neighbor: otherwise the canonical flip would change it. -/
theorem falseNeighbors_card_pos_of_fixed {S : Finset ι} {R : ι → ι → Prop}
    {w : ι → Bool} (hw : IsolatedFlip.flip S R w = w)
    {i : ι} (hi : i ∈ S) (hwi : w i = false) :
    0 < (falseNeighbors R w i).card := by
  classical
  have hn : ¬ ∀ j, R i j → w j = true := by
    intro h
    have he : i ∈ IsolatedFlip.eligible S R w := IsolatedFlip.mem_eligible.mpr ⟨hi, h⟩
    have hh := congrFun hw i
    simp [IsolatedFlip.flip, he, hwi] at hh
  push Not at hn
  obtain ⟨j, hij, hj⟩ := hn
  have hwj : w j = false := by cases h : w j <;> simp_all
  exact Finset.card_pos.mpr ⟨j, by simp [falseNeighbors, hij, hwj]⟩

/-- The coincidence correction of a word with no isolated eligible position.
The exceptional positions `V \ S` include the external endpoint. -/
theorem correction_le_of_fixed {V S : Finset ι} {R : ι → ι → Prop}
    (hS : S ⊆ V) {w : ι → Bool} (hw : IsolatedFlip.flip S R w = w)
    {A x : ℝ} (hA : 0 ≤ A) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    correction V R A x w ≤
      (1 + A * x) ^ S.card * (1 + A) ^ (V \ S).card := by
  classical
  unfold correction
  rw [Finset.prod_filter]
  calc
    _ ≤ ∏ i ∈ V, if i ∈ S then 1 + A * x else 1 + A := by
      apply Finset.prod_le_prod₀
      · intro i hi
        split_ifs <;> positivity
      · intro i hi
        by_cases his : i ∈ S <;> by_cases hwi : w i = false
        · simp only [ite_eq_left his, ite_eq_left hwi]
          have hc := falseNeighbors_card_pos_of_fixed hw his hwi
          have hp : x ^ (falseNeighbors R w i).card ≤ x := by
            simpa using pow_le_pow_of_le_one hx hx1 (show 1 ≤ (falseNeighbors R w i).card by omega)
          linarith [mul_le_mul_of_nonneg_left hp hA]
        · simp only [ite_eq_left his, ite_eq_right hwi]
          nlinarith [mul_nonneg hA hx]
        · simp only [ite_eq_right his, ite_eq_left hwi]
          have hp : x ^ (falseNeighbors R w i).card ≤ 1 := pow_le_one₀ hx hx1
          nlinarith
        · simp only [ite_eq_right his, ite_eq_right hwi]
          linarith
    _ = (1 + A * x) ^ S.card * (1 + A) ^ (V \ S).card := by
      rw [Finset.prod_ite]
      have hmem : V.filter (fun i => i ∈ S) = S := by
        ext i
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
      have hnot : V.filter (fun i => ¬ i ∈ S) = V \ S := by
        ext i
        simp
      rw [hmem, hnot]
      simp

/-- With at most one exceptional V endpoint, the fixed-word correction has
the exact uniform bound used in the manuscript. -/
theorem correction_le_endpoint_bound {V S : Finset ι} {R : ι → ι → Prop}
    (hS : S ⊆ V) (hend : (V \ S).card ≤ 1)
    {w : ι → Bool} (hw : IsolatedFlip.flip S R w = w)
    {A x : ℝ} (hA : 0 ≤ A) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    correction V R A x w ≤ (1 + A) * (1 + A * x) ^ V.card := by
  have hpow : (1 + A * x) ^ S.card ≤ (1 + A * x) ^ V.card :=
    pow_le_pow_right₀ (by nlinarith) (Finset.card_le_card hS)
  have hendpow : (1 + A) ^ (V \ S).card ≤ 1 + A := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ 1 + A) hend
  calc
    correction V R A x w ≤ (1 + A * x) ^ S.card * (1 + A) ^ (V \ S).card :=
      correction_le_of_fixed hS hw hA hx hx1
    _ ≤ (1 + A * x) ^ V.card * (1 + A) :=
      mul_le_mul hpow hendpow (by positivity) (by positivity)
    _ = (1 + A) * (1 + A * x) ^ V.card := mul_comm _ _

/-- The word summand without coincidence corrections. -/
def baseWeight (edges : Finset (ι × ι)) (V : Finset ι) (A B x : ℝ)
    (w : ι → Bool) : ℝ :=
  x ^ SwitchRestoration.switchCount edges w *
    A ^ (V.filter fun i => w i = true).card *
    B ^ ((Finset.univ \ V).filter fun i => w i = true).card

theorem weight_eq_baseWeight (edges : Finset (ι × ι)) (V : Finset ι)
    (R : ι → ι → Prop) (A B x : ℝ) (w : ι → Bool) :
    weight edges V R A B x w = baseWeight edges V A B x w * correction V R A x w := rfl

theorem baseWeight_nonneg (edges : Finset (ι × ι)) (V : Finset ι)
    {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x) (w : ι → Bool) :
    0 ≤ baseWeight edges V A B x w := by
  unfold baseWeight
  positivity

/-- Complete isolated-position correction removal, including the exceptional
endpoint factor and enlargement of the fixed-word sum to all words. -/
theorem sum_weight_le_uncorrected {edges : Finset (ι × ι)} {V S : Finset ι}
    {R : ι → ι → Prop} (hS : S ⊆ V)
    (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (hR : ∀ e ∈ edges, R e.1 e.2 ∧ R e.2 e.1)
    (hdegree : ∀ i ∈ S, SwitchRestoration.endpointDegree edges i = 2)
    (hend : (V \ S).card ≤ 1)
    {A B x : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (∑ w : ι → Bool, weight edges V R A B x w) ≤
      (1 + x ^ 2 * (1 + A) / A) ^ S.card *
        (1 + A) * (1 + A * x) ^ V.card *
          ∑ w : ι → Bool, baseWeight edges V A B x w := by
  classical
  let fixed := Finset.univ.filter (fun w => IsolatedFlip.flip S R w = w)
  let C := (1 + A) * (1 + A * x) ^ V.card
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : (∑ w ∈ fixed, weight edges V R A B x w) ≤
      C * ∑ w : ι → Bool, baseWeight edges V A B x w := by
    calc
      _ ≤ ∑ w ∈ fixed, C * baseWeight edges V A B x w := by
        apply Finset.sum_le_sum
        intro w hw
        rw [weight_eq_baseWeight, mul_comm C]
        exact mul_le_mul_of_nonneg_left
          (correction_le_endpoint_bound hS hend (Finset.mem_filter.mp hw).2 hA.le hx hx1)
          (baseWeight_nonneg edges V hA.le hB hx w)
      _ = C * ∑ w ∈ fixed, baseWeight edges V A B x w := (Finset.mul_sum _ _ _).symm
      _ ≤ C * ∑ w : ι → Bool, baseWeight edges V A B x w := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro w hw hn
        exact baseWeight_nonneg edges V hA.le hB hx w
  calc
    _ ≤ (1 + x ^ 2 * (1 + A) / A) ^ S.card *
        ∑ w ∈ fixed, weight edges V R A B x w :=
      sum_weight_le_fixed hS hV hR hdegree hA hB hx
    _ ≤ (1 + x ^ 2 * (1 + A) / A) ^ S.card *
        (C * ∑ w : ι → Bool, baseWeight edges V A B x w) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp [C]; ring

/-- The uniform correction-removal inequality in the form used by the
word-sum estimate: `A ≥ 1` bounds the flip cost by `1+2*x²`. -/
theorem sum_weight_le_uniform_uncorrected {edges : Finset (ι × ι)} {V S : Finset ι}
    {R : ι → ι → Prop} (hS : S ⊆ V)
    (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (hR : ∀ e ∈ edges, R e.1 e.2 ∧ R e.2 e.1)
    (hdegree : ∀ i ∈ S, SwitchRestoration.endpointDegree edges i = 2)
    (hend : (V \ S).card ≤ 1)
    {A B x : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (∑ w : ι → Bool, weight edges V R A B x w) ≤
      (1 + 2 * x ^ 2) ^ V.card * (1 + A) * (1 + A * x) ^ V.card *
        ∑ w : ι → Bool, baseWeight edges V A B x w := by
  classical
  have hAp : 0 < A := by linarith
  have hfrac : (1 + A) / A ≤ 2 := (div_le_iff₀ hAp).mpr (by linarith)
  have hc : x ^ 2 * (1 + A) / A ≤ 2 * x ^ 2 := by
    rw [mul_div_assoc]
    simpa only [mul_comm (x ^ 2) 2] using mul_le_mul_of_nonneg_left hfrac (sq_nonneg x)
  have hF : (1 + x ^ 2 * (1 + A) / A) ^ S.card ≤
      (1 + 2 * x ^ 2) ^ V.card := by
    calc
      _ ≤ (1 + 2 * x ^ 2) ^ S.card :=
        pow_le_pow_left₀ (by positivity) (by linarith) S.card
      _ ≤ (1 + 2 * x ^ 2) ^ V.card :=
        pow_le_pow_right₀ (by nlinarith [sq_nonneg x]) (Finset.card_le_card hS)
  have hZ : 0 ≤ ∑ w : ι → Bool, baseWeight edges V A B x w :=
    Finset.sum_nonneg (fun w _ => baseWeight_nonneg edges V hAp.le hB hx w)
  refine (sum_weight_le_uncorrected hS hV hR hdegree hend hAp hB hx hx1).trans ?_
  have h := mul_le_mul_of_nonneg_right hF
    (show 0 ≤ (1 + A) * (1 + A * x) ^ V.card *
      ∑ w : ι → Bool, baseWeight edges V A B x w by positivity)
  simpa only [mul_assoc] using h

end Problem335.IsolatedWeight

end

end OAI
