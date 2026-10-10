import OAI.NumberTheory.Ostmann.Arithmetic.PrimeLines

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeLineFamilies
variable {ι K : Type*} [Field K]

def CommonZero (a b : ι → K) (z : Kˣ × Kˣ) : Prop :=
  ∀ i, a i * (z.1 : K) + b i * (z.2 : K) = 0

def Solutions (a b : ι → K) := {z : Kˣ × Kˣ // CommonZero a b z}

def minor (a b : ι → K) (i j : ι) : K := a i * b j - b i * a j

def AllZero (a b : ι → K) : Prop := ∀ i, a i = 0 ∧ b i = 0

def AllMinorsZero (a b : ι → K) : Prop := ∀ i j, minor a b i j = 0

theorem rank_two_empty (a b : ι → K) (i j : ι) (hij : minor a b i j ≠ 0)
    (z : Kˣ × Kˣ) : ¬ CommonZero a b z := by
  intro hz
  exact PrimeLines.rank_two_impossible (a i) (b i) (a j) (b j)
    (z.1 : K) (z.2 : K) hij (Units.ne_zero z.2) (hz i) (hz j)

theorem single_coefficient_empty (a b : ι → K) (i : ι)
    (hi : (a i = 0 ∧ b i ≠ 0) ∨ (a i ≠ 0 ∧ b i = 0))
    (z : Kˣ × Kˣ) : ¬ CommonZero a b z := by
  intro hz
  rcases hi with hi | hi
  · exact PrimeLines.no_unit_solution_of_zero_coefficient hi.1 hi.2 z.1 z.2 (hz i)
  · have h := hz i
    rw [hi.2, zero_mul, add_zero] at h
    exact mul_ne_zero hi.1 (Units.ne_zero z.1) h

theorem all_zero_common (a b : ι → K) (hz : AllZero a b) (z : Kˣ × Kˣ) :
    CommonZero a b z := by
  intro i
  simp only [(hz i).1, (hz i).2, zero_mul, zero_add]

theorem commonZero_iff_row (a b : ι → K) (i : ι) (hai : a i ≠ 0)
    (hm : ∀ j, minor a b i j = 0) (z : Kˣ × Kˣ) :
    CommonZero a b z ↔ a i * (z.1 : K) + b i * (z.2 : K) = 0 := by
  refine ⟨fun hz => hz i, ?_⟩
  intro hi j
  have hd := hm j
  change a i * b j - b i * a j = 0 at hd
  have he : a i * (a j * (z.1 : K) + b j * (z.2 : K)) = 0 := by
    linear_combination a j * hi + (z.2 : K) * hd
  exact (mul_eq_zero.mp he).resolve_left hai

def unitLineEquiv (a b : ι → K) (i : ι) (hai : a i ≠ 0) (hbi : b i ≠ 0)
    (hm : ∀ j, minor a b i j = 0) : Solutions a b ≃ Kˣ :=
  (Equiv.subtypeEquivRight (fun z => commonZero_iff_row a b i hai hm z)).trans
    (PrimeLines.unitLineEquiv (a i) (b i) hai hbi)

def allZeroEquiv (a b : ι → K) (hz : AllZero a b) :
    Solutions a b ≃ Kˣ × Kˣ where
  toFun z := z.val
  invFun z := ⟨z, all_zero_common a b hz z⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem solutions_nonempty_iff (a b : ι → K) :
    Nonempty (Solutions a b) ↔ AllZero a b ∨
      (AllMinorsZero a b ∧ ∃ i, a i ≠ 0 ∧ b i ≠ 0) := by
  classical
  constructor
  · rintro ⟨z⟩
    by_cases hz : AllZero a b
    · exact Or.inl hz
    · right
      have hm : AllMinorsZero a b := by
        intro i j
        by_contra hij
        exact rank_two_empty a b i j hij z.val z.property
      refine ⟨hm, ?_⟩
      obtain ⟨i, hi⟩ : ∃ i, ¬ (a i = 0 ∧ b i = 0) := by
        simpa only [AllZero, not_forall] using hz
      have ha : a i ≠ 0 := by
        intro ha
        have hb : b i ≠ 0 := fun hb => hi ⟨ha, hb⟩
        exact single_coefficient_empty a b i (Or.inl ⟨ha, hb⟩) z.val z.property
      have hb : b i ≠ 0 := by
        intro hb
        exact single_coefficient_empty a b i (Or.inr ⟨ha, hb⟩) z.val z.property
      exact ⟨i, ha, hb⟩
  · rintro (hz | ⟨hm, i, hai, hbi⟩)
    · exact ⟨(allZeroEquiv a b hz).symm (1, 1)⟩
    · exact ⟨(unitLineEquiv a b i hai hbi (hm i)).symm 1⟩

theorem card_rank_one [Fintype K] [DecidableEq K] (a b : ι → K) (i : ι)
    (hai : a i ≠ 0) (hbi : b i ≠ 0) (hm : ∀ j, minor a b i j = 0) :
    Nat.card (Solutions a b) = Fintype.card Kˣ := by
  rw [Nat.card_congr (unitLineEquiv a b i hai hbi hm), Nat.card_eq_fintype_card]

theorem card_all_zero [Fintype K] [DecidableEq K] (a b : ι → K) (hz : AllZero a b) :
    Nat.card (Solutions a b) = Fintype.card (Kˣ × Kˣ) := by
  rw [Nat.card_congr (allZeroEquiv a b hz), Nat.card_eq_fintype_card]

theorem card_rank_two (a b : ι → K) (i j : ι) (hij : minor a b i j ≠ 0) :
    Nat.card (Solutions a b) = 0 := by
  have : IsEmpty (Solutions a b) := ⟨fun z => rank_two_empty a b i j hij z.val z.property⟩
  simp

theorem card_single_coefficient (a b : ι → K) (i : ι)
    (hi : (a i = 0 ∧ b i ≠ 0) ∨ (a i ≠ 0 ∧ b i = 0)) :
    Nat.card (Solutions a b) = 0 := by
  have : IsEmpty (Solutions a b) :=
    ⟨fun z => single_coefficient_empty a b i hi z.val z.property⟩
  simp

end Ostmann.Arithmetic.PrimeLineFamilies
end

end OAI
