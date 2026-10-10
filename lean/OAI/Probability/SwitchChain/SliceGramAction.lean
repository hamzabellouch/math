import OAI.Probability.SwitchChain.SliceCoefficientAlgebra

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

def orbitKernel (a b d : ℝ) (i j k l : V) : ℝ :=
  if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then a
  else if k = i ∨ k = j ∨ l = i ∨ l = j then b else d

theorem sum_two_and_outside (f : V → ℝ) {i j : V} (hij : i ≠ j) :
    (∑ k, f k) = f i + f j + ∑ k ∈ outside i j, f k := by
  have h := sum_outside f hij
  linarith

theorem half_sum_orbitKernel (a b d : ℝ) (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j) :
    (∑ k, ∑ l, orbitKernel a b d i j k l * c k l) / 2 =
      intersectionAction a b d c i j := by
  have hji : j ≠ i := Ne.symm hij
  have hout (k : V) (hk : k ∈ outside i j) : k ≠ i ∧ k ≠ j := by
    simpa [outside, and_comm] using hk
  have hfirst : (∑ l, orbitKernel a b d i j i l * c i l) =
      a * c i j + b * ∑ l ∈ outside i j, c i l := by
    rw [sum_two_and_outside _ hij]
    have hrest : (∑ l ∈ outside i j, orbitKernel a b d i j i l * c i l) =
        b * ∑ l ∈ outside i j, c i l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨hli, hlj⟩ := hout l hl
      simp [orbitKernel, hij, hli, hlj]
    rw [hrest]
    simp [orbitKernel, hij, hji, hdiag]
  have hsecond : (∑ l, orbitKernel a b d i j j l * c j l) =
      a * c i j + b * ∑ l ∈ outside i j, c j l := by
    rw [sum_two_and_outside _ hij]
    have hrest : (∑ l ∈ outside i j, orbitKernel a b d i j j l * c j l) =
        b * ∑ l ∈ outside i j, c j l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨hli, hlj⟩ := hout l hl
      simp [orbitKernel, hji, hli, hlj]
    rw [hrest]
    simp [orbitKernel, hij, hji, hdiag, hsym j i]
  have hrest (k : V) (hk : k ∈ outside i j) :
      (∑ l, orbitKernel a b d i j k l * c k l) =
        b * (c i k + c j k) + d * ∑ l ∈ outside i j, c k l := by
    obtain ⟨hki, hkj⟩ := hout k hk
    rw [sum_two_and_outside _ hij]
    have hinner : (∑ l ∈ outside i j, orbitKernel a b d i j k l * c k l) =
        d * ∑ l ∈ outside i j, c k l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨hli, hlj⟩ := hout l hl
      simp [orbitKernel, hki, hkj, hli, hlj]
    rw [hinner]
    simp only [orbitKernel, hki, hkj, false_and, or_false,
      and_false, hij, hji, ite_false, or_true, ite_true,
      hsym k i, hsym k j]
    ring
  rw [sum_two_and_outside _ hij, hfirst, hsecond]
  have houter : (∑ k ∈ outside i j, ∑ l, orbitKernel a b d i j k l * c k l) =
      b * meetingSum c i j + 2 * d * disjointSum c i j := by
    rw [Finset.sum_congr rfl hrest]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, meetingSum, disjointSum]
    ring
  rw [houter]
  simp only [intersectionAction, hij, ite_false, meetingSum, Finset.sum_add_distrib]
  ring

omit [Fintype V] in

theorem orbitKernel_eq_intersection_card (a b d : ℝ) (i j k l : V)
    (hij : i ≠ j) (hkl : k ≠ l) :
    orbitKernel a b d i j k l =
      if (({i, j} : Finset V) ∩ {k, l}).card = 2 then a
      else if (({i, j} : Finset V) ∩ {k, l}).card = 1 then b else d := by
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [orbitKernel, Finset.inter_insert, eq_comm]

theorem half_sum_kernel_eq_intersectionAction (a b d : ℝ) (K c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j)
    (hK : ∀ k l, k ≠ l → K k l = orbitKernel a b d i j k l) :
    (∑ k, ∑ l, K k l * c k l) / 2 = intersectionAction a b d c i j := by
  rw [← half_sum_orbitKernel a b d c hsym hdiag hij]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hkl : k = l
  · subst l; simp [hdiag]
  · rw [hK k l hkl]

theorem half_sum_kernel_of_intersection_card (a b d : ℝ) (K c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j)
    (hK : ∀ k l, k ≠ l → K k l =
      if (({i, j} : Finset V) ∩ {k, l}).card = 2 then a
      else if (({i, j} : Finset V) ∩ {k, l}).card = 1 then b else d) :
    (∑ k, ∑ l, K k l * c k l) / 2 = intersectionAction a b d c i j := by
  apply half_sum_kernel_eq_intersectionAction a b d K c hsym hdiag hij
  intro k l hkl
  rw [hK k l hkl, orbitKernel_eq_intersection_card a b d i j k l hij hkl]

theorem half_sum_kernel_linearPair (a b d : ℝ) (K : V → V → ℝ)
    (u : V → ℝ) (hu : ∑ i, u i = 0) {i j : V} (hij : i ≠ j)
    (hK : ∀ k l, k ≠ l → K k l = orbitKernel a b d i j k l) :
    (∑ k, ∑ l, K k l * linearPair u k l) / 2 =
      (a + ((Fintype.card V : ℝ) - 4) * b -
        ((Fintype.card V : ℝ) - 3) * d) * linearPair u i j := by
  rw [half_sum_kernel_eq_intersectionAction a b d K (linearPair u)
    (linearPair_symmetric u) (linearPair_diag u) hij hK,
    intersectionAction_linearPair a b d u hu]

theorem half_sum_kernel_rowZero (a b d : ℝ) (K c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) {i j : V} (hij : i ≠ j)
    (hK : ∀ k l, k ≠ l → K k l = orbitKernel a b d i j k l) :
    (∑ k, ∑ l, K k l * c k l) / 2 = (a - 2 * b + d) * c i j := by
  rw [half_sum_kernel_eq_intersectionAction a b d K c hsym hdiag hij hK,
    intersectionAction_rowZero a b d c hsym hdiag hrow]

end Problem315.SliceCoefficients

end

end OAI
