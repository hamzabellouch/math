import OAI.Geometry.NodalSets.Elliptic.RecursiveJet

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def transportKnown (W : ℕ → Fin 4 → CPoly) (c f : Jet) (n : ℕ) (a : Jet) : CPoly :=
  (∑ r ∈ Finset.range n, ∑ i, W (r + 1) i * pderiv i (a (n - r))) +
    (∑ r ∈ Finset.range (n + 1), c r * a (n - r)) - f n

def transportCoefficient (w : Fin 4 → ℂ) (W : ℕ → Fin 4 → CPoly)
    (c f : Jet) (n : ℕ) (a : Jet) : CPoly :=
  homogeneousComponent n
    ((∑ r ∈ Finset.range (n + 1), ∑ i,
      (if r = 0 then C (w i) else W r i) * pderiv i (a (n - r + 1))) +
      (∑ r ∈ Finset.range (n + 1), c r * a (n - r)) - f n)

lemma transportKnown_congr (W : ℕ → Fin 4 → CPoly) (c f : Jet) (n : ℕ)
    (a b : Jet) (h : ∀ k, k ≤ n → a k = b k) :
    transportKnown W c f n a = transportKnown W c f n b := by
  unfold transportKnown
  apply congrArg (· - f n)
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro i _
    rw [h (n - r) (Nat.sub_le _ _)]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [h (n - r) (Nat.sub_le _ _)]

theorem transportCoefficient_split (w : Fin 4 → ℂ) (W : ℕ → Fin 4 → CPoly)
    (c f : Jet) (n : ℕ) (a : Jet) :
    transportCoefficient w W c f n a = homogeneousComponent n
      (direction w (a (n + 1)) + transportKnown W c f n a) := by
  unfold transportCoefficient transportKnown
  apply congrArg (homogeneousComponent n)
  rw [Finset.sum_range_succ', direction_apply]
  simp only [Nat.sub_zero, ite_true, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ite_false]
  have hs : (∑ r ∈ Finset.range n, ∑ i, W (r + 1) i * pderiv i (a (n - (r + 1) + 1))) =
      ∑ r ∈ Finset.range n, ∑ i, W (r + 1) i * pderiv i (a (n - r)) := by
    apply Finset.sum_congr rfl
    intro r hr
    have he : n - (r + 1) + 1 = n - r := by have := Finset.mem_range.mp hr; omega
    rw [he]
  rw [hs]
  ring

theorem finite_transport_jets (w : Fin 4 → ℂ) (hw : w ≠ 0)
    (W : ℕ → Fin 4 → CPoly) (c f : Jet) (value : ℂ) (degree : ℕ) :
    ∃ a : Jet, (∀ k, (a k).IsHomogeneous k) ∧ a 0 = C value ∧
      ∀ n, n < degree → transportCoefficient w W c f n a = 0 := by
  let initial : Jet := fun k ↦ if k = 0 then C value else 0
  have hi : ∀ k, (initial k).IsHomogeneous k := by
    intro k
    dsimp [initial]
    split_ifs with hk
    · subst k; exact isHomogeneous_C _ _
    · exact isHomogeneous_zero _ _ _
  let low : ℕ → Jet → CPoly := fun n a ↦ homogeneousComponent n (transportKnown W c f n a)
  obtain ⟨a, ha, hkeep, hsolve⟩ := finite_triangular_jets w hw low
    (fun n a ↦ homogeneousComponent_isHomogeneous _ _)
    (fun n a b h ↦ congrArg (homogeneousComponent n) (transportKnown_congr W c f n a b h))
    initial hi 0 degree
  refine ⟨a, ha, by simpa [initial] using hkeep 0 (by omega), ?_⟩
  intro n hn
  rw [transportCoefficient_split, map_add,
    homogeneousComponent_eq_self (direction_homogeneous _ (ha (n + 1)))]
  exact hsolve n (Nat.zero_le n) (by simpa using hn)

def secondOrderCoefficient (g : ℕ → Fin 4 → Fin 4 → CPoly)
    (b : ℕ → Fin 4 → CPoly) (a : Jet) (n : ℕ) : CPoly :=
  homogeneousComponent n
    ((∑ r ∈ Finset.range (n + 1), ∑ i, ∑ j,
      g r i j * pderiv i (pderiv j (a (n - r + 2)))) +
    ∑ r ∈ Finset.range (n + 1), ∑ i, b r i * pderiv i (a (n - r + 1)))

theorem secondOrderCoefficient_congr (g : ℕ → Fin 4 → Fin 4 → CPoly)
    (b : ℕ → Fin 4 → CPoly) (a a' : Jet) (n : ℕ)
    (h : ∀ k, k ≤ n + 2 → a k = a' k) :
    secondOrderCoefficient g b a n = secondOrderCoefficient g b a' n := by
  unfold secondOrderCoefficient
  apply congrArg (homogeneousComponent n)
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [h (n - r + 2) (by omega)]
  · apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    rw [h (n - r + 1) (by omega)]

theorem transport_tower (w : Fin 4 → ℂ) (hw : w ≠ 0)
    (W : ℕ → Fin 4 → CPoly) (c : Jet)
    (g : ℕ → Fin 4 → Fin 4 → CPoly) (b : ℕ → Fin 4 → CPoly) (m J : ℕ) :
    ∃ A : ℕ → Jet,
      (∀ j k, (A j k).IsHomogeneous k) ∧
      (∀ j, A j 0 = if j = 0 then 1 else 0) ∧
      (∀ n, n < m + 1 + 2 * J → transportCoefficient w W c 0 n (A 0) = 0) ∧
      ∀ j n, n < m + 1 + 2 * (J - (j + 1)) →
        transportCoefficient w W c (fun k ↦ -secondOrderCoefficient g b (A j) k)
          n (A (j + 1)) = 0 := by
  let solve (f : Jet) (value : ℂ) (d : ℕ) : Jet :=
    Classical.choose (finite_transport_jets w hw W c f value d)
  have hs (f : Jet) (value : ℂ) (d : ℕ) :=
    Classical.choose_spec (finite_transport_jets w hw W c f value d)
  let A : ℕ → Jet := fun j ↦ Nat.rec
    (solve 0 1 (m + 1 + 2 * J))
    (fun j prev ↦ solve (fun k ↦ -secondOrderCoefficient g b prev k) 0
      (m + 1 + 2 * (J - (j + 1)))) j
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | zero => exact (hs 0 1 _).1
    | succ j => exact (hs _ 0 _).1
  · intro j
    cases j with
    | zero => simpa [A, solve] using (hs 0 1 _).2.1
    | succ j =>
        change solve (fun k ↦ -secondOrderCoefficient g b (A j) k) 0
          (m + 1 + 2 * (J - (j + 1))) 0 = 0
        exact (hs _ 0 _).2.1.trans (map_zero C)
  · exact (hs 0 1 _).2.2
  · intro j
    exact (hs _ 0 _).2.2

theorem wave_degree_budgets (m J j : ℕ) (hj : j < J) :
    (m + 1 + 2 * (J - j)) = (m + 1 + 2 * (J - (j + 1))) + 2 ∧
    (m + 1 + 2 * (J - j)) + 1 < m + 2 * J + 3 ∧
    m < m + 1 + 2 * (J - j) := by omega

end
end Yau.Jets

end OAI
