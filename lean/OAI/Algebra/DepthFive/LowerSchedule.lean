import OAI.Algebra.DepthFive.LowerParameters
import OAI.Algebra.DepthFive.ScheduleIntervals
import OAI.Algebra.DepthFive.ScheduleInterior

namespace OAI

noncomputable section

namespace Problem335.LowerParameters

/-- The actual balanced schedule for the rank-measure parameters of degree `n`. -/
def balancedWord (n : ℕ) : List Bool := BalancedSchedule.word (k n) (s n)

lemma balancedWord_length {n : ℕ} (hn : 4 ≤ n) : (balancedWord n).length = n := by
  rw [balancedWord, BalancedSchedule.word_length (k_pos hn), two_mul_k_add_s]

/-- `true` selects derivative layers and `false` selects multiplication layers. -/
def balancedLayer {n : ℕ} (hn : 4 ≤ n) : Fin n → Bool := fun i =>
  (balancedWord n).get ⟨i.val, by simp [balancedWord_length hn]⟩

lemma balancedLayer_ofFn {n : ℕ} (hn : 4 ≤ n) :
    List.ofFn (balancedLayer hn) = balancedWord n := by
  apply List.ext_getElem
  · simp [balancedWord_length hn]
  · intro i h₁ h₂
    simp [balancedLayer]

lemma balancedLayer_card_true {n : ℕ} (hn : 4 ≤ n) :
    (Finset.univ.filter (fun i => balancedLayer hn i = true)).card = k n := by
  let vec : List.Vector Bool n := ⟨balancedWord n, balancedWord_length hn⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count true vec
  change (Finset.univ.filter (fun i => balancedLayer hn i = true)).card =
    (balancedWord n).count true at h
  simpa [balancedWord] using h

lemma balancedLayer_card_false {n : ℕ} (hn : 4 ≤ n) :
    (Finset.univ.filter (fun i => balancedLayer hn i = false)).card = m n := by
  let vec : List.Vector Bool n := ⟨balancedWord n, balancedWord_length hn⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count false vec
  change (Finset.univ.filter (fun i => balancedLayer hn i = false)).card =
    (balancedWord n).count false at h
  simpa [balancedWord, BalancedSchedule.word_count_false (k_pos hn), m_eq_k_add_s] using h

lemma balancedSchedule_rho (n : ℕ) : BalancedSchedule.rho (k n) (s n) = rho n := by
  simp only [BalancedSchedule.rho, rho, m_eq_k_add_s, Nat.cast_add]

lemma balancedLayer_infix_discrepancy {n : ℕ} (hn : 4 ≤ n) (b : List (Fin n))
    (hb : b <:+: List.ofFn id) :
    (b.countP (balancedLayer hn) : ℝ) - rho n *
      (b.countP (fun i => !balancedLayer hn i) : ℝ) < 1 + rho n := by
  have hmap := hb.map (balancedLayer hn)
  have heq : (List.ofFn (id : Fin n → Fin n)).map (balancedLayer hn) = balancedWord n := by
    rw [List.map_ofFn]
    exact balancedLayer_ofFn hn
  rw [heq] at hmap
  have h := BalancedSchedule.infix_discrepancy_lt (k_pos hn) (s n) (k n) hmap
  simpa [BalancedSchedule.discrepancy, List.count_eq_countP, List.countP_map,
    Function.comp_def, balancedSchedule_rho] using h

lemma balancedLayer_no_adjacent {n : ℕ} (hn : 4 ≤ n) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    balancedLayer hn i = false ∨ balancedLayer hn j = false := by
  have hlt : i.val + 1 < (balancedWord n).length := by
    rw [balancedWord_length hn, hij]
    exact j.isLt
  have h := List.isChain_iff_getElem.mp (BalancedSchedule.word_no_adjacent_V (k n) (s n))
    i.val hlt
  simpa only [balancedLayer, balancedWord, List.get_eq_getElem, hij] using h

lemma balancedLayer_independent {n : ℕ} (hn : 4 ≤ n) {i j : Fin n}
    (hi : balancedLayer hn i = true) (hj : balancedLayer hn j = true) :
    ¬ BalancedSchedule.adjacent i j := by
  rintro (hij | hji)
  · have h := balancedLayer_no_adjacent hn i j hij
    simp [hi, hj] at h
  · have h := balancedLayer_no_adjacent hn j i hji
    simp [hi, hj] at h

lemma balancedLayer_first {n : ℕ} (hn : 4 ≤ n) :
    balancedLayer hn ⟨0, by omega⟩ = true := by
  have h := BalancedSchedule.wordPrefix_head (r := k n) (k_pos hn) (k n) (s n)
  change (balancedWord n).head? = some true at h
  have hlen : 0 < (balancedWord n).length := by rw [balancedWord_length hn]; omega
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at h
  simpa only [balancedLayer, List.get_eq_getElem] using Option.some.inj h

lemma balancedLayer_final {n : ℕ} (hn : 4 ≤ n) :
    balancedLayer hn ⟨n - 1, by omega⟩ = false := by
  have h := BalancedSchedule.wordPrefix_last (r := k n) (k_pos hn) (k n) (s n)
  change (balancedWord n).getLast? = some false at h
  have hlen : (balancedWord n).length - 1 < (balancedWord n).length := by
    rw [balancedWord_length hn]; omega
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlen] at h
  simpa only [balancedLayer, List.get_eq_getElem, balancedWord_length hn] using Option.some.inj h

/-- The actual V-layer coincidence events use pairwise disjoint vertex coordinates. -/
lemma balancedLayer_internalEnds_disjoint {n : ℕ} (hn : 4 ≤ n) {i j : Fin n}
    (hi : balancedLayer hn i = true) (hj : balancedLayer hn j = true) (hne : i ≠ j) :
    Disjoint (BalancedSchedule.internalEnds i) (BalancedSchedule.internalEnds j) :=
  BalancedSchedule.internalEnds_disjoint_of_not_adjacent hne (balancedLayer_independent hn hi hj)

/-- Layer-restricted IMM variables are a product of selected layers and matrix entries. -/
def layerVariableEquiv {n : ℕ} (p : Fin n → Bool) (b : Bool) :
    {x : Fin n × Fin n × Fin n // p x.1 = b} ≃
      {i : Fin n // p i = b} × Fin n × Fin n where
  toFun x := (⟨x.1.1, x.2⟩, x.1.2.1, x.1.2.2)
  invFun x := ⟨(x.1.1, x.2.1, x.2.2), x.1.2⟩
  left_inv := by rintro ⟨⟨i, j, l⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨i, h⟩, j, l⟩; rfl

lemma balancedVariable_card_true {n : ℕ} (hn : 4 ≤ n) :
    Fintype.card {x : Fin n × Fin n × Fin n // balancedLayer hn x.1 = true} = v n := by
  classical
  rw [Fintype.card_congr (layerVariableEquiv (balancedLayer hn) true)]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype]
  rw [balancedLayer_card_true]
  simp [v, pow_two]

lemma balancedVariable_card_false {n : ℕ} (hn : 4 ≤ n) :
    Fintype.card {x : Fin n × Fin n × Fin n // balancedLayer hn x.1 = false} = u n := by
  classical
  rw [Fintype.card_congr (layerVariableEquiv (balancedLayer hn) false)]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype]
  rw [balancedLayer_card_false]
  simp [u, pow_two]

end Problem335.LowerParameters

end

end OAI
