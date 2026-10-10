import OAI.NumberTheory.Ostmann.Construction.HarmonicRepeatedMass
import OAI.NumberTheory.Ostmann.Construction.RepeatedTuplePoisson

namespace OAI

/-! # Removing repeated primes from an original-prior character statistic -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

/-- The event `S` contains the original bin and product restrictions. Its
harmonic law is never renormalized when repeated primes are removed. -/
theorem harmonic_repeat_removal (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℕ) (Q : Fin n → Finset ℕ) (S : Finset (Fin n → P))
    (χ : Fin n → ∀ p : ℕ, DirichletCharacter ℂ p)
    (hχ : ∀ i p, p ∈ P → χ i p ≠ 1) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X H R D : ℝ) (hX : 0 < X) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ p ∈ P, H * R < p)
    (hupper : ∀ x ∈ S, (∏ i, (x i : ℝ)) ≤ X * R)
    (hlower : ∀ x ∈ S, X * Real.exp D ≤ ∏ i, (x i : ℝ)) :
    let μ := fun i => primeSubsetPrior P (Q i)
    let F := fun x : Fin n → P => characterTupleSum (fun i => (x i : ℕ)) χ t ψ X
    ‖(∑ x ∈ S, (productPrior μ x : ℂ) * F x) -
      ∑ x ∈ S.filter Function.Injective, (productPrior μ x : ℂ) * F x‖ ≤
      Real.sqrt X * (‖𝓕 ψ 0‖ * (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2)) := by
  intro μ F
  let T := S.filter (fun x => ¬Function.Injective x)
  let E := T.filter (fun x => x ∈ allMultipleTuples P n)
  have hES : E ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hET : E ⊆ T := Finset.filter_subset _ _
  have hEA : E ⊆ allMultipleTuples P n := fun _ hx => (Finset.mem_filter.mp hx).2
  have hzero (x : Fin n → P) (hx : x ∈ T) (hne : x ∉ E) : F x = 0 := by
    have hxS := (Finset.mem_filter.mp hx).1
    have hn := (Finset.mem_filter.mp hx).2
    have hm : x ∉ allMultipleTuples P n := fun hm => hne (Finset.mem_filter.mpr ⟨hx, hm⟩)
    obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hn
    obtain ⟨k, hk⟩ := exists_singleton_of_not_allMultiple x hm
    exact repeated_tuple_singleton_zero (fun l => (x l : ℕ)) (fun l => hP _ (x l).property)
      χ t ψ X H R hX hR hsupp (fun l => hsmall _ (x l).property) (hupper x hxS)
      i j hij (congrArg Subtype.val heq) k
      (fun l hl => hk l (Subtype.ext hl)) (hχ k _ (x k).property)
  have hsums : (∑ x ∈ S, (productPrior μ x : ℂ) * F x) -
      ∑ x ∈ S.filter Function.Injective, (productPrior μ x : ℂ) * F x =
      ∑ x ∈ E, (productPrior μ x : ℂ) * F x := by
    have hs := Finset.sum_filter_add_sum_filter_not S Function.Injective
      (fun x => (productPrior μ x : ℂ) * F x)
    have he : (∑ x ∈ E, (productPrior μ x : ℂ) * F x) =
        ∑ x ∈ T, (productPrior μ x : ℂ) * F x :=
      Finset.sum_subset hET (fun x hx hne => by rw [hzero x hx hne, mul_zero])
    rw [he, ← hs]
    ring
  rw [hsums]
  apply harmonic_repeated_gap_bound P hP n Q E hEA X D ‖𝓕 ψ 0‖ hX (norm_nonneg _)
    (fun x hx => hlower x (hES hx)) F
  intro x hx
  have hxT := hET hx
  obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp (Finset.mem_filter.mp hxT).2
  exact repeated_tuple_sum_bound (fun l => (x l : ℕ)) (fun l => hP _ (x l).property)
    χ t ψ X H R hX hR hsupp (fun l => hsmall _ (x l).property) (hupper x (hES hx))
    i j hij (congrArg Subtype.val heq)

end Ostmann

end OAI
