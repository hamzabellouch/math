import OAI.NumberTheory.Ostmann.Construction.FullAtomFourierEnergy

namespace OAI

/-! # Nonzero frequencies from the actual unit and modulus-window support -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem fullAtomTransferWeight_all_frequencies_ne_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0) :
    ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
  induction n with
  | zero =>
    intro s hs
    have he : s = t := by simpa only [allFrequencyList, List.mem_singleton] using hs
    subst s
    intro ht
    subst t
    exact hw (hzero x)
  | succ n ih =>
    obtain ⟨hg, P, hP, _, _⟩ := fullAtomTransferWeight_support role childBound pivotBound ranges leaf
      (n + 1) x t hw
    have hr := ((fullAtomWeightGuard_node role childBound pivotBound ranges n x t P hP).mp hg).1
    rw [fullAtomTransferWeight_node role childBound pivotBound ranges leaf n x t P hP,
      ite_eq_left hr] at hw
    obtain ⟨hL, hR⟩ := mul_ne_zero_iff.mp hw
    have hR' : fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (reverseCopyLabelMap role n false P x) t.2.2 ≠ 0 := by
      intro hz
      exact hR (by rw [hz, map_zero])
    intro s hs
    rcases List.mem_cons.mp hs with he | hs
    · exact he ▸ hP.root_ne_zero
    · rcases List.mem_append.mp hs with hs | hs
      · exact ih _ t.2.1 hL s hs
      · exact ih _ t.2.2 hR' s hs

/-- A zero bottom frequency would make every atom equal to one. The actual
initial modulus window excludes that case, including at its endpoints. -/
theorem fullAtomFourierWeight_zero_frequency {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X) (hlo : 1 < X * lo)
    (x : CopyScheduleAtoms role 0 → ℕ) :
    fullAtomTransferWeight role childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X))
      0 x (0 : ℤ) = 0 := by
  by_contra hw
  have hu := (fullAtomTransferWeight_top_support role childBound pivotBound ranges _ 0 x (0 : ℤ) hw).2
  have hx (i) : x i = 1 := by simpa only [frequencyRoot, Int.natAbs_zero, Nat.coprime_zero_right] using hu i
  have ht : scheduleAtomTotal role ⟨0, x⟩ = 1 := by
    simp only [scheduleAtomTotal, hx, Finset.prod_const_one]
  have hm : ¬ (scheduleAtomTotal role ⟨0, x⟩ : ℝ) / X ∈ Set.Icc lo hi := by
    intro hm
    have h := (le_div_iff₀ hX).mp hm.1
    rw [ht, Nat.cast_one] at h
    nlinarith
  apply hw
  unfold fullAtomTransferWeight
  split_ifs
  · simp only [recursiveTransferWeight, hm, ite_false, zero_mul]
  · rfl

theorem fullAtomFourierWeight_all_frequencies_ne_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X) (hlo : 1 < X * lo)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) n x t ≠ 0) :
    ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
  exact fullAtomTransferWeight_all_frequencies_ne_zero role childBound pivotBound ranges _
    (fullAtomFourierWeight_zero_frequency role childBound pivotBound ranges ψ X lo hi hX hlo) n x t hw

end Ostmann

end OAI
