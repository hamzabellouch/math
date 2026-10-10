import OAI.NumberTheory.Ostmann.Construction.InitialTupleFrequencies
import OAI.NumberTheory.Ostmann.Construction.InitialGaussMultipliers

namespace OAI

/-! # The fully guarded initial constituent coefficient is the Poisson sum -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

noncomputable def scheduleFourierLeaf {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) :
    ScheduleAtomState role → ℤ → ℂ :=
  fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
    normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)

theorem initial_constituent_poisson_sum {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) [Nonempty (Σ i, Fin (size i))]
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : (Σ i, Fin (size i)) → P)
    (center : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X)
    (heven : ∀ t : ℝ, 𝓕 ψ (-t) = 𝓕 ψ t) (N : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hx : Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)))
    (hrange : ∀ r ∈ ranges 0, r.Holds (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)))
    (hwindow : ((∏ i, (x i : ℕ) : ℕ) : ℝ) / X ∈ Set.Icc lo hi) :
    (∑ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      fullAtomTransferWeight role childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
        0 (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)) v *
      sampledTuplePhase P hP χ center v x) =
    sampledTupleAmplitude P hP χ center ψ X N x := by
  let M := ∏ i, (x i : ℕ)
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hP _ (x i).property).ne_zero)
  have hMn : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  change _ = ∑ v ∈ tupleFrequencies (fun i => (x i : ℕ)) N,
    (Real.sqrt (X / M) : ℂ) * 𝓕 ψ ((v : ℝ) * X / M) *
      sampledTuplePhase P hP χ center v x
  simp only [tupleFrequencies, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  rw [fullAtomTransferWeight_initial role size childBound pivotBound ranges
    (scheduleFourierLeaf role ψ X lo hi) (fun i => (x i : ℕ)) v hx hrange]
  have htotal := initial_atom_total role size (fun i => (x i : ℕ))
  have hleaf : scheduleFourierLeaf role ψ X lo hi
      ⟨0, fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)⟩ v =
      (Real.sqrt (X / M) : ℂ) * 𝓕 ψ ((v : ℝ) * X / M) := by
    unfold scheduleFourierLeaf
    rw [htotal, ite_eq_left hwindow, one_mul]
    exact normalizedFourierProfile_even_original (𝓕 ψ : 𝓢(ℝ, ℂ)) heven X M v hX.ne' hMn
  rw [hleaf]
  simp only [intCast_isUnit_iff_natAbs_coprime]
  by_cases hu : ∀ i, (x i : ℕ).Coprime v.natAbs
  · have hv : v ≠ 0 := by
      intro hz
      obtain ⟨i⟩ := ‹Nonempty (Σ i, Fin (size i))›
      have hh := hu i
      rw [hz, Int.natAbs_zero, Nat.coprime_zero_right] at hh
      exact (hP _ (x i).property).ne_one hh
    exact (congrArg (fun z : ℂ => z * sampledTuplePhase P hP χ center v x)
      (ite_eq_left hu)).trans (ite_eq_left (And.intro hv hu)).symm
  · exact (congrArg (fun z : ℂ => z * sampledTuplePhase P hP χ center v x)
      (ite_eq_right hu)).trans ((zero_mul _).trans
        (ite_eq_right (fun h => hu h.2)).symm)

end Ostmann

end OAI
