import OAI.NumberTheory.Ostmann.Construction.TransferGraphPhase

namespace OAI

/-! # A common directed-graph phase for the initial and transferred amplitudes -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def directedPrimePhase {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (ν : I → ℂ) (b : I → I → ℤ) (v : ℤ) : ℂ :=
  ∏ i, ZMod.stdAddChar (t i * ((tupleCofactor p i : ZMod (p i))⁻¹ * (v : ZMod (p i)))) *
    ν i * ∏ j, χ i (p j : ZMod (p i)) ^ b i j

def initialDirectedGraph {I : Type*} [DecidableEq I] (i j : I) : ℤ :=
  if i = j then 0 else 1

private theorem initial_row_product {I : Type*} [Fintype I]
    (f : I → ℂ) (i : I) :
    (∏ j, f j ^ initialDirectedGraph i j) = ∏ j ∈ Finset.univ.erase i, f j := by
  have hi : f i ^ initialDirectedGraph i i = 1 := by simp [initialDirectedGraph]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => f j ^ initialDirectedGraph i j)
    (Finset.mem_univ i), hi, one_mul]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [initialDirectedGraph, (Finset.mem_erase.mp hj).1.symm, ite_false, zpow_one]

/-- The graph phase obtained by Poisson summation is the level-zero
specialization of the phase maintained through the transfers. -/
theorem tupleGraphPhase_eq_directed {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (v : ℤ) :
    tupleGraphPhase p χ t v = directedPrimePhase p χ t
      (fun i => primitiveGaussPhase (χ i) * (χ i)⁻¹ (v : ZMod (p i))) initialDirectedGraph v := by
  unfold tupleGraphPhase directedPrimePhase
  apply Finset.prod_congr rfl
  intro i _
  rw [initial_row_product]
  ring

theorem directedPrimePhase_norm_le_one {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (ν : I → ℂ) (hν : ∀ i, ‖ν i‖ ≤ 1)
    (b : I → I → ℤ) (v : ℤ) : ‖directedPrimePhase p χ t ν b v‖ ≤ 1 := by
  rw [directedPrimePhase, norm_prod]
  apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
  intro i _
  simp only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul, norm_prod]
  have hp := Finset.prod_le_one₀ (s := Finset.univ) (fun j _ => norm_nonneg (χ i (p j : ZMod (p i)) ^ b i j))
    (fun j _ => character_zpow_norm_le_one (χ i) (p j : ZMod (p i)) (b i j))
  exact (mul_le_mul (hν i) hp
    (Finset.prod_nonneg fun j _ => norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem initialDirectedGraph_regular {I : Type*} [DecidableEq I] (i : I) :
    RegularGraphRow initialDirectedGraph i 1 := by
  intro j hj
  simp [initialDirectedGraph, hj.symm]

end Ostmann

end OAI
