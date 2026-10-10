import OAI.Probability.Localization.Experiment

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

noncomputable def cellWidth (n J : ℕ) : ℝ := 1 / (Real.sqrt n * (2 : ℝ)^J)
noncomputable def cellLower {n : ℕ} (Q : Cell n) (i : Fin n) : ℝ :=
  -1 / (2 * Real.sqrt n) + (Q.2 i : ℝ) / (Real.sqrt n * (2 : ℝ)^Q.1)
noncomputable def cellCenter {n : ℕ} (Q : Cell n) : Coordinate n :=
  fun i => cellLower Q i + cellWidth n Q.1 / 2

lemma cellWidth_pos {n J : ℕ} (hn : 0 < n) : 0 < cellWidth n J := by
  unfold cellWidth
  positivity

lemma cellSet_eq_pi {n : ℕ} (Q : Cell n) :
    cellSet Q = Set.pi univ (fun i => Ico (cellLower Q i) (cellLower Q i + cellWidth n Q.1)) := by
  ext z
  simp only [cellSet, mem_ofPred_eq, mem_pi, mem_univ, true_implies, mem_Ico]
  congr! 3
  simp only [cellLower, cellWidth]
  ring

lemma measurableSet_cellSet {n : ℕ} (Q : Cell n) : MeasurableSet (cellSet Q) := by
  rw [cellSet_eq_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma volume_cellSet {n : ℕ} (Q : Cell n) :
    volume (cellSet Q) = ENNReal.ofReal ((cellWidth n Q.1)^n) := by
  rw [cellSet_eq_pi, Real.volume_pi_Ico]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by unfold cellWidth; positivity) n).symm

lemma cellSet_subset_initialCube {n : ℕ} (hn : 0 < n) (Q : Cell n) :
    cellSet Q ⊆ initialCube n := by
  intro z hz i hi
  have hd : 0 < Real.sqrt (n : ℝ) * (2 : ℝ)^Q.1 := by positivity
  have hidx : (Q.2 i : ℝ) + 1 ≤ (2 : ℝ)^Q.1 := by exact_mod_cast (Q.2 i).isLt
  have hl : 0 ≤ (Q.2 i : ℝ) / (Real.sqrt n * (2 : ℝ)^Q.1) := by positivity
  have hu : ((Q.2 i : ℝ) + 1) / (Real.sqrt n * (2 : ℝ)^Q.1) ≤ 1 / Real.sqrt n := by
    apply (div_le_iff₀ hd).mpr
    have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
    have he : 1 / Real.sqrt n * (Real.sqrt n * (2 : ℝ)^Q.1) = (2 : ℝ)^Q.1 := by field_simp
    rwa [he]
  have hw : -1 / (2 * Real.sqrt n) + 1 / Real.sqrt n = 1 / (2 * Real.sqrt n) := by ring
  exact ⟨(by linarith [(hz i).1]), (hz i).2.trans_le (by linarith)⟩

lemma cubePrior_cellSet {n : ℕ} (hn : 0 < n) (Q : Cell n) :
    cubePrior n (cellSet Q) = ENNReal.ofReal ((1 / 2 : ℝ)^(n * Q.1)) := by
  unfold cubePrior
  rw [cond_apply (measurable_initialCube n), inter_eq_right.mpr (cellSet_subset_initialCube hn Q),
    volume_initialCube, volume_cellSet]
  have hp : 0 < (1 / Real.sqrt n)^n := by positivity
  rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_mul (inv_nonneg.mpr hp.le)]
  congr 1
  unfold cellWidth
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  simp only [one_div, inv_pow, inv_inv, mul_inv_rev ]
  rw [← mul_pow]
  have hc : Real.sqrt n * (((2 : ℝ)^Q.1)⁻¹ * (Real.sqrt n)⁻¹) = ((2 : ℝ)^Q.1)⁻¹ := by field_simp
  rw [hc, inv_pow, ← pow_mul, Nat.mul_comm Q.1 n]

lemma cellCenter_mem {n : ℕ} (hn : 0 < n) (Q : Cell n) : cellCenter Q ∈ cellSet Q := by
  rw [cellSet_eq_pi]
  intro i hi
  have h := cellWidth_pos (J := Q.1) hn
  simp only [mem_Ico, cellCenter]
  constructor <;> linarith

noncomputable def cellIndex {n : ℕ} (J : ℕ) (z : Coordinate n) : Fin n → Fin (2^J) :=
  fun i => ⟨⌊(z i + 1 / (2 * Real.sqrt n)) * (Real.sqrt n * (2 : ℝ)^J)⌋₊ % 2^J,
    Nat.mod_lt _ (pow_pos (by norm_num) J)⟩

noncomputable def cellAt {n : ℕ} (J : ℕ) (z : Coordinate n) : Cell n := ⟨J, cellIndex J z⟩

lemma measurable_cellIndex {n : ℕ} (J : ℕ) : Measurable (cellIndex (n := n) J) := by
  apply Measurable.of_eval
  intro i
  let f : ℕ → Fin (2^J) := fun v => ⟨v % 2^J, Nat.mod_lt _ (pow_pos (by norm_num) J)⟩
  exact (measurable_of_countable f).comp
    (((measurable_pi_apply i).add_const _).mul_const _).nat_floor

lemma measurable_cellAt {n : ℕ} (J : ℕ) : Measurable (cellAt (n := n) J) := by
  exact (measurable_of_countable (fun a : Fin n → Fin (2^J) => (⟨J, a⟩ : Cell n))).comp
    (measurable_cellIndex J)

lemma cellIndex_eq_of_mem {n : ℕ} (hn : 0 < n) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : cellIndex Q.1 z = Q.2 := by
  funext i
  apply Fin.ext
  simp only [cellSet, mem_ofPred_eq, neg_div] at hz
  have hd : 0 < Real.sqrt (n : ℝ) * (2 : ℝ)^Q.1 := by positivity
  let x : ℝ := (z i + 1 / (2 * Real.sqrt n)) * (Real.sqrt n * (2 : ℝ)^Q.1)
  have hl : (Q.2 i : ℝ) ≤ x := by
    apply (div_le_iff₀ hd).mp
    linarith [(hz i).1]
  have hu : x < (Q.2 i : ℝ) + 1 := by
    apply (lt_div_iff₀ hd).mp
    linarith [(hz i).2]
  have hf : ⌊x⌋₊ = (Q.2 i).val := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg _) hl)).mpr ⟨hl, hu⟩
  change ⌊x⌋₊ % 2^Q.1 = (Q.2 i).val
  rw [hf, Nat.mod_eq_of_lt (Q.2 i).isLt]

lemma mem_cellAt {n : ℕ} (hn : 0 < n) (J : ℕ) {z : Coordinate n}
    (hz : z ∈ initialCube n) : z ∈ cellSet (cellAt J z) := by
  intro i
  have hi := hz i (mem_univ i)
  simp only [mem_Ico, neg_div] at hi
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hd : 0 < Real.sqrt (n : ℝ) * (2 : ℝ)^J := by positivity
  let x : ℝ := (z i + 1 / (2 * Real.sqrt n)) * (Real.sqrt n * (2 : ℝ)^J)
  have hx : 0 ≤ x := mul_nonneg (by linarith [hi.1]) hd.le
  have hxu : x < (2 : ℝ)^J := by
    have hw : 2 * (1 / (2 * Real.sqrt n)) = 1 / Real.sqrt n := by ring
    have hza : z i + 1 / (2 * Real.sqrt n) < 1 / Real.sqrt n := by linarith [hi.2]
    have hb := mul_lt_mul_of_pos_right hza hd
    dsimp [x]
    have he : 1 / Real.sqrt n * (Real.sqrt n * (2 : ℝ)^J) = (2 : ℝ)^J := by field_simp
    rwa [he] at hb
  have hfloor : ⌊x⌋₊ < 2^J := by
    apply (Nat.floor_lt hx).mpr
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hxu
  have hl := Nat.floor_le hx
  have hu := Nat.lt_floor_add_one x
  have hl' := (div_le_iff₀ hd).mpr hl
  have hu' := (lt_div_iff₀ hd).mpr hu
  change -1 / (2 * Real.sqrt n) + (⌊x⌋₊ % 2^J : ℕ) / (Real.sqrt n * (2 : ℝ)^J) ≤ z i ∧
    z i < -1 / (2 * Real.sqrt n) + ((⌊x⌋₊ % 2^J : ℕ) + 1) / (Real.sqrt n * (2 : ℝ)^J)
  rw [Nat.mod_eq_of_lt hfloor]
  simp only [neg_div]
  constructor <;> linarith

lemma cellSet_disjoint {n J : ℕ} (hn : 0 < n) {a b : Fin n → Fin (2^J)} (hab : a ≠ b) :
    Disjoint (cellSet ⟨J, a⟩) (cellSet ⟨J, b⟩) := by
  apply Set.disjoint_left.mpr
  intro z hza hzb
  exact hab ((cellIndex_eq_of_mem hn ⟨J, a⟩ hza).symm.trans (cellIndex_eq_of_mem hn ⟨J, b⟩ hzb))

noncomputable def childCell {n : ℕ} (Q : Cell n) (l : ℕ) (a : Fin n → Fin (2^l)) : Cell n :=
  ⟨Q.1 + l, fun i => ⟨(Q.2 i).val * 2^l + (a i).val, by
    rw [pow_add]
    have h1 := (Q.2 i).isLt
    have h2 := (a i).isLt
    nlinarith⟩⟩

lemma cellWidth_add (n J l : ℕ) :
    cellWidth n (J + l) = cellWidth n J / (2 : ℝ)^l := by
  simp only [cellWidth, pow_add]
  ring

lemma childCell_lower {n : ℕ} (Q : Cell n) (l : ℕ) (a : Fin n → Fin (2^l)) (i : Fin n) :
    cellLower (childCell Q l a) i = cellLower Q i + cellWidth n (Q.1+l) * (a i : ℝ) := by
  simp only [cellLower, cellWidth, childCell, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    pow_add]
  have ht : (2 : ℝ)^l ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

lemma childCell_subset {n : ℕ} (hn : 0 < n) (Q : Cell n) (l : ℕ) (a : Fin n → Fin (2^l)) :
    cellSet (childCell Q l a) ⊆ cellSet Q := by
  rw [cellSet_eq_pi, cellSet_eq_pi]
  intro z hz i hi
  have hz' := hz i hi
  have hw := cellWidth_pos (J := Q.1+l) hn
  have hidx : (a i : ℝ) + 1 ≤ (2 : ℝ)^l := by exact_mod_cast (a i).isLt
  have he : cellWidth n (Q.1+l) * (2 : ℝ)^l = cellWidth n Q.1 := by
    rw [cellWidth_add, div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))]
  dsimp only at hz'
  rw [childCell_lower] at hz'
  change cellLower Q i + cellWidth n (Q.1+l) * (a i : ℝ) ≤ z i ∧
    z i < cellLower Q i + cellWidth n (Q.1+l) * (a i : ℝ) + cellWidth n (Q.1+l) at hz'
  have hu := mul_le_mul_of_nonneg_left hidx hw.le
  rw [he] at hu
  have ha : (0 : ℝ) ≤ (a i : ℝ) := Nat.cast_nonneg _
  exact ⟨by nlinarith [hz'.1], by nlinarith [hz'.2]⟩

lemma cell_ext {n : ℕ} {Q R : Cell n} (h : Q.1 = R.1)
    (hi : ∀ i,(Q.2 i).val = (R.2 i).val) : Q = R := by
  rcases Q with ⟨J,a⟩
  rcases R with ⟨K,b⟩
  dsimp at h hi
  subst K
  congr 1
  funext i
  exact Fin.ext (hi i)

noncomputable def ancestorCell {n : ℕ} (Q : Cell n) (J : ℕ) (hJ : J ≤ Q.1) : Cell n :=
  ⟨J,fun i => ⟨(Q.2 i).val / 2^(Q.1-J),by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^(Q.1-J))).mpr
    rw [← pow_add,Nat.add_sub_of_le hJ]
    exact (Q.2 i).isLt⟩⟩

lemma child_ancestorCell {n : ℕ} (Q : Cell n) (J : ℕ) (hJ : J ≤ Q.1) :
    childCell (ancestorCell Q J hJ) (Q.1-J)
      (fun i => ⟨(Q.2 i).val % 2^(Q.1-J),Nat.mod_lt _ (by positivity)⟩) = Q := by
  apply cell_ext (Nat.add_sub_of_le hJ)
  intro i
  change (Q.2 i).val / 2^(Q.1-J) * 2^(Q.1-J) + (Q.2 i).val % 2^(Q.1-J) = (Q.2 i).val
  simpa only [Nat.mul_comm] using Nat.div_add_mod (Q.2 i).val (2^(Q.1-J))

lemma cellSet_subset_ancestor {n : ℕ} (hn : 0 < n) (Q : Cell n) (J : ℕ) (hJ : J ≤ Q.1) :
    cellSet Q ⊆ cellSet (ancestorCell Q J hJ) := by
  have h := childCell_subset hn (ancestorCell Q J hJ) (Q.1-J)
    (fun i => ⟨(Q.2 i).val % 2^(Q.1-J),Nat.mod_lt _ (by positivity)⟩)
  rwa [child_ancestorCell] at h

lemma cellAt_eq_of_mem {n : ℕ} (hn : 0 < n) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : cellAt Q.1 z = Q := by
  apply cell_ext (Q := cellAt Q.1 z) (R := Q) rfl
  have h := cellIndex_eq_of_mem hn Q hz
  intro i
  exact congrArg Fin.val (congrFun h i)

lemma cellAt_nested {n : ℕ} (hn : 0 < n) {J K : ℕ} (hJK : J ≤ K)
    {z : Coordinate n} (hz : z ∈ initialCube n) : cellSet (cellAt K z) ⊆ cellSet (cellAt J z) := by
  have hsub := cellSet_subset_ancestor hn (cellAt K z) J hJK
  have hmem := hsub (mem_cellAt hn K hz)
  have h := cellAt_eq_of_mem hn (ancestorCell (cellAt K z) J hJK) hmem
  change cellAt J z = ancestorCell (cellAt K z) J hJK at h
  rwa [← h] at hsub

lemma cellSet_root (n : ℕ) : cellSet (rootCell n) = initialCube n := by
  ext z
  simp only [cellSet,rootCell,initialCube,Fin.val_zero,Nat.cast_zero,zero_div,add_zero,
    pow_zero,mul_one,zero_add,Set.mem_ofPred_eq,Set.mem_pi,Set.mem_univ,forall_true_left,Set.mem_Ico]
  have he : -1/(2*Real.sqrt n)+1/Real.sqrt n = 1/(2*Real.sqrt n) := by ring
  rw [he]

end RepeatedLocalization

end OAI
