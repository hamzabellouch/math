import Mathlib

namespace OAI

universe u

noncomputable section

namespace Problem313

/-- Removing one specified coordinate injects supports containing it into the
set of supports of no larger degree. This is the finite-sum step behind the
low-degree derivative estimate. -/
theorem sum_squares_le_derivative_sum
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (L : Finset (Finset ι)) (c : Finset ι → ℝ)
    (d : ι → Finset ι → ℝ) (σ k : ℝ) (i : ι)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k)
    (hcoeff : ∀ A : Finset ι, i ∉ A → c (insert i A) = σ * d i A) :
    (∑ S ∈ L.filter (fun S => i ∈ S), c S ^ 2) ≤
      σ ^ 2 * ∑ A ∈ (Finset.univ : Finset (Finset ι)).filter
        (fun A => (A.card : ℝ) ≤ k), d i A ^ 2 := by
  classical
  let T := L.filter (fun S => i ∈ S)
  let U := (Finset.univ : Finset (Finset ι)).filter (fun A => (A.card : ℝ) ≤ k)
  have hT : ∀ S ∈ T, i ∈ S := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  have hinj : Set.InjOn (fun S : Finset ι => S.erase i) (T : Set (Finset ι)) := by
    intro S hS R hR h
    have h' := congrArg (insert i) h
    simpa [Finset.insert_erase (hT S hS), Finset.insert_erase (hT R hR)] using h'
  have hsub : T.image (fun S => S.erase i) ⊆ U := by
    intro A hA
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hA
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcard : ((S.erase i).card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.erase_subset i S)
    exact hcard.trans (hdegree S (Finset.mem_filter.mp hS).1)
  have heq : (∑ S ∈ T, c S ^ 2) =
      σ ^ 2 * ∑ A ∈ T.image (fun S => S.erase i), d i A ^ 2 := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    have hc := hcoeff (S.erase i) (Finset.notMem_erase i S)
    rw [Finset.insert_erase (hT S hS)] at hc
    rw [hc]
    ring
  change (∑ S ∈ T, c S ^ 2) ≤ σ ^ 2 * ∑ A ∈ U, d i A ^ 2
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg σ)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ => sq_nonneg (d i A))

/-- Every nonempty support is counted by at least one coordinate. Combining
this double counting with the insertion identity bounds its Fourier mass by
the sum of the low-degree masses of all coordinate derivatives. -/
theorem low_degree_derivative_counting
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (L : Finset (Finset ι)) (c : Finset ι → ℝ)
    (d : ι → Finset ι → ℝ) (σ k : ℝ)
    (hne : ∀ S ∈ L, S.Nonempty)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k)
    (hcoeff : ∀ (i : ι) (A : Finset ι), i ∉ A → c (insert i A) = σ * d i A) :
    (∑ S ∈ L, c S ^ 2) ≤
      σ ^ 2 * ∑ i : ι, ∑ A ∈ (Finset.univ : Finset (Finset ι)).filter
        (fun A => (A.card : ℝ) ≤ k), d i A ^ 2 := by
  classical
  have hcount : (∑ S ∈ L, c S ^ 2) ≤
      ∑ i : ι, ∑ S ∈ L.filter (fun S => i ∈ S), c S ^ 2 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro S hS
    obtain ⟨i, hi⟩ := hne S hS
    have h := Finset.single_le_sum
      (s := (Finset.univ : Finset ι))
      (f := fun j => if j ∈ S then c S ^ 2 else 0)
      (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
    simpa [hi] using h
  calc
    (∑ S ∈ L, c S ^ 2) ≤
        ∑ i : ι, ∑ S ∈ L.filter (fun S => i ∈ S), c S ^ 2 := hcount
    _ ≤ ∑ i : ι, σ ^ 2 * ∑ A ∈ (Finset.univ : Finset (Finset ι)).filter
        (fun A => (A.card : ℝ) ≤ k), d i A ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact sum_squares_le_derivative_sum L c d σ k i hdegree (hcoeff i)
    _ = _ := by rw [Finset.mul_sum]

end Problem313

end

end OAI
