import OAI.Algebra.DepthFive.ScheduleEnds

namespace OAI

noncomputable section

namespace Problem335.BalancedSchedule

def firstLayer {k : ℕ} (hk : 0 < k) (s : ℕ) : Fin (2 * k + s) := ⟨0, by omega⟩

def finalLayer {k : ℕ} (hk : 0 < k) (s : ℕ) : Fin (2 * k + s) :=
  ⟨2 * k + s - 1, by omega⟩

@[simp] lemma indexedWord_first {k : ℕ} (hk : 0 < k) (s : ℕ) :
    indexedWord hk s (firstLayer hk s) = true := by
  have h := wordPrefix_head (r := k) hk k s
  change (word k s).head? = some true at h
  have hlen : 0 < (word k s).length := by rw [word_length hk]; omega
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at h
  simpa only [indexedWord, firstLayer, List.get_eq_getElem] using Option.some.inj h

@[simp] lemma indexedWord_final {k : ℕ} (hk : 0 < k) (s : ℕ) :
    indexedWord hk s (finalLayer hk s) = false := by
  have h := wordPrefix_last (r := k) hk k s
  change (word k s).getLast? = some false at h
  have hlen : (word k s).length - 1 < (word k s).length := by rw [word_length hk]; omega
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlen] at h
  simpa only [indexedWord, finalLayer, List.get_eq_getElem, word_length hk] using Option.some.inj h

@[simp] lemma firstLayer_mem_vLayers {k : ℕ} (hk : 0 < k) (s : ℕ) :
    firstLayer hk s ∈ vLayers hk s := by simp [vLayers]

lemma vLayers_nonfinal {k : ℕ} (hk : 0 < k) (s : ℕ) {i : Fin (2 * k + s)}
    (hi : i ∈ vLayers hk s) : i.val + 1 < 2 * k + s := by
  have hi' := (Finset.mem_filter.mp hi).2
  by_contra h
  have heq : i = finalLayer hk s := by
    apply Fin.ext
    dsimp [finalLayer]
    omega
  rw [heq, indexedWord_final] at hi'
  cases hi'

/-- The V positions eligible for isolated-position flips. -/
def interiorVLayers {k : ℕ} (hk : 0 < k) (s : ℕ) : Finset (Fin (2 * k + s)) :=
  (vLayers hk s).erase (firstLayer hk s)

lemma interiorVLayers_subset {k : ℕ} (hk : 0 < k) (s : ℕ) :
    interiorVLayers hk s ⊆ vLayers hk s := Finset.erase_subset _ _

lemma mem_interiorVLayers_iff {k : ℕ} (hk : 0 < k) (s : ℕ) {i : Fin (2 * k + s)} :
    i ∈ interiorVLayers hk s ↔ i ∈ vLayers hk s ∧ 0 < i.val ∧ i.val + 1 < 2 * k + s := by
  simp only [interiorVLayers, Finset.mem_erase]
  constructor
  · rintro ⟨hfirst, hi⟩
    refine ⟨hi, ?_, vLayers_nonfinal hk s hi⟩
    have hn : i.val ≠ 0 := by
      intro h
      exact hfirst (Fin.ext h)
    omega
  · rintro ⟨hi, hpos, hlast⟩
    refine ⟨?_, hi⟩
    intro h
    have hv := congrArg Fin.val h
    dsimp [firstLayer] at hv
    omega

lemma card_interiorVLayers {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (interiorVLayers hk s).card = k - 1 := by
  rw [interiorVLayers, Finset.card_erase_of_mem (firstLayer_mem_vLayers hk s), card_vLayers]

lemma vLayers_sdiff_interiorVLayers {k : ℕ} (hk : 0 < k) (s : ℕ) :
    vLayers hk s \ interiorVLayers hk s = {firstLayer hk s} := by
  simp [interiorVLayers, Finset.sdiff_erase (firstLayer_mem_vLayers hk s)]

lemma card_internalEnds_eq_two {n : ℕ} (i : Fin n) (hfirst : 0 < i.val)
    (hlast : i.val + 1 < n) : (internalEnds i).card = 2 := by
  let l : Fin (n - 1) := ⟨i.val - 1, by omega⟩
  let r : Fin (n - 1) := ⟨i.val, by omega⟩
  apply Finset.card_eq_two.mpr
  refine ⟨l, r, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    dsimp [l, r] at hv
    omega
  · ext v
    simp only [internalEnds, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inr (Fin.ext h)
      · left
        apply Fin.ext
        dsimp [l]
        omega
    · rintro (rfl | rfl)
      · dsimp [l]
        omega
      · exact Or.inl rfl

lemma interiorVLayers_degree_two {k : ℕ} (hk : 0 < k) (s : ℕ)
    {i : Fin (2 * k + s)} (hi : i ∈ interiorVLayers hk s) :
    (internalEnds i).card = 2 := by
  obtain ⟨_, hfirst, hlast⟩ := (mem_interiorVLayers_iff hk s).mp hi
  exact card_internalEnds_eq_two i hfirst hlast

end Problem335.BalancedSchedule

end

end OAI
