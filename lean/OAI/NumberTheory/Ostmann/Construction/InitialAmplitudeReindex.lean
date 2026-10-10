import OAI.NumberTheory.Ostmann.Construction.InitialGuardedExpectation
import OAI.NumberTheory.Ostmann.Construction.DirectedPhaseReindex

namespace OAI

/-! # Coordinate invariance of the actual initial prime amplitude -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem tupleGraphPhase_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) [∀ j, NeZero (p j)]
    (χ : ∀ j, DirichletCharacter ℂ (p j)) (t : ∀ j, ZMod (p j)) (v : ℤ) :
    tupleGraphPhase (fun i => p (e i)) (fun i => χ (e i)) (fun i => t (e i)) v =
      tupleGraphPhase p χ t v := by
  classical
  rw [tupleGraphPhase_eq_directed, tupleGraphPhase_eq_directed]
  have hg : (fun i j => initialDirectedGraph (e i) (e j)) =
      (initialDirectedGraph : I → I → ℤ) := by
    funext i j
    simp only [initialDirectedGraph, e.injective.eq_iff]
  rw [← hg]
  exact directedPrimePhase_equiv e p χ t
    (fun j => primitiveGaussPhase (χ j) * (χ j)⁻¹ (v : ZMod (p j)))
    initialDirectedGraph v

theorem sampledTuplePhase_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (χ : J → ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (v : ℤ) (x : J → P) :
    sampledTuplePhase P hP (fun i => χ (e i)) t v (fun i => x (e i)) =
      sampledTuplePhase P hP χ t v x := by
  let : ∀ j, NeZero (x j : ℕ) := fun j => ⟨(hP _ (x j).property).ne_zero⟩
  exact tupleGraphPhase_equiv e (fun j => (x j : ℕ))
    (fun j => χ j (x j)) (fun j => t (x j)) v

theorem tupleFrequencies_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (N : ℕ) :
    tupleFrequencies (fun i => p (e i)) N = tupleFrequencies p N := by
  ext v
  simp only [tupleFrequencies, Finset.mem_filter, intCast_isUnit_iff_natAbs_coprime]
  constructor
  · rintro ⟨hv, hn, hu⟩
    exact ⟨hv, hn, fun j => by simpa using hu (e.symm j)⟩
  · rintro ⟨hv, hn, hu⟩
    exact ⟨hv, hn, fun i => hu (e i)⟩

theorem sampledTupleAmplitude_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (χ : J → ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (x : J → P) :
    sampledTupleAmplitude P hP (fun i => χ (e i)) t ψ X N (fun i => x (e i)) =
      sampledTupleAmplitude P hP χ t ψ X N x := by
  change (∑ v ∈ tupleFrequencies (fun i => (x (e i) : ℕ)) N,
      (Real.sqrt (X / (∏ i, (x (e i) : ℕ))) : ℂ) *
        𝓕 ψ ((v : ℝ) * X / (∏ i, (x (e i) : ℕ))) *
        sampledTuplePhase P hP (fun i => χ (e i)) t v (fun i => x (e i))) =
    ∑ v ∈ tupleFrequencies (fun j => (x j : ℕ)) N,
      (Real.sqrt (X / (∏ j, (x j : ℕ))) : ℂ) *
        𝓕 ψ ((v : ℝ) * X / (∏ j, (x j : ℕ))) * sampledTuplePhase P hP χ t v x
  rw [tupleFrequencies_equiv e (fun j => (x j : ℕ)) N,
    Equiv.prod_comp e (fun j => (x j : ℕ))]
  apply Finset.sum_congr rfl
  intro v _
  rw [sampledTuplePhase_equiv]

theorem prime_sample_pairwise_iff_injective {I : Type*}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : I → P) :
    Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) ↔ Function.Injective x := by
  constructor
  · intro h i j he
    by_contra hn
    have hc := h hn
    dsimp only at hc
    rw [he, Nat.coprime_self] at hc
    exact (hP _ (x j).property).ne_one hc
  · intro h i j hn
    apply (hP _ (x i).property).coprime_iff_not_dvd.mpr
    intro hd
    have he : (x i : ℕ) = (x j : ℕ) :=
      ((Nat.dvd_prime (hP _ (x j).property)).mp hd).resolve_left (hP _ (x i).property).ne_one
    exact hn (h (Subtype.ext he))

end Ostmann

end OAI
