import OAI.Combinatorics.Crossing.Interpolation
import OAI.Combinatorics.Crossing.AdaptedFamily
import OAI.Combinatorics.Crossing.PolynomialCoordinates

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module Submodule
open scoped BigOperators
variable {W ι : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

def evaluationFiltration (t : ℝ) (k : ℕ) : Submodule ℝ Z :=
  LinearMap.range (constrainedEval U node Z k t)

theorem evaluationFiltration_mono
    {W ι : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    (t : ℝ) : Monotone (evaluationFiltration U node Z t) := by
  intro k l hkl z hz
  obtain ⟨p, hp⟩ := hz
  exact ⟨⟨p.val, bounded_mono p.property.1 hkl, p.property.2⟩, hp⟩

theorem evaluationFiltration_zero
    {W ι : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    (t : ℝ) : evaluationFiltration U node Z t 0 = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨p, hp⟩ := hz
  have hp0 : p.val = 0 := (bounded_zero_iff p.val).mp p.property.1
  change eval t p.val = z at hp
  rw [hp0, map_zero] at hp
  exact (Submodule.mem_bot ℝ).mpr hp.symm

def columnIncrement (t : ℝ) (e : ℕ) : ℕ :=
  finrank ℝ (evaluationFiltration U node Z t (e+1)) -
    finrank ℝ (evaluationFiltration U node Z t e)

theorem columnIncrement_zero (t : ℝ) (ht : ∀ i, node i ≠ t) :
    columnIncrement U node Z t 0 = rankIncrement U node Z 0 := by
  rw [columnIncrement, evaluationFiltration_zero U node Z t, finrank_bot, Nat.sub_zero]
  exact finrank_eval_range U node Z 0 t ht

theorem columnIncrement_succ (t : ℝ) (ht : ∀ i, node i ≠ t) (e : ℕ) :
    columnIncrement U node Z t (e+1) = rankIncrement U node Z (e+1) - rankIncrement U node Z e := by
  unfold columnIncrement evaluationFiltration
  rw [finrank_eval_range U node Z (e+1) t ht, finrank_eval_range U node Z e t ht]

theorem sum_columnIncrement (t : ℝ) (m : ℕ) :
    ∑ e ∈ Finset.range m, columnIncrement U node Z t e =
      finrank ℝ (evaluationFiltration U node Z t m) := by
  unfold columnIncrement
  rw [Finset.sum_range_tsub (fun k l hkl => Submodule.finrank_mono
    (evaluationFiltration_mono U node Z t hkl)), evaluationFiltration_zero,
    finrank_bot, Nat.sub_zero]

theorem exists_adapted_polynomials (t : ℝ) (h : ℕ) :
    ∃ (p : Fin (finrank ℝ (evaluationFiltration U node Z t (h+1))) → PolynomialModule ℝ Z)
      (d : Fin (finrank ℝ (evaluationFiltration U node Z t (h+1))) → ℕ),
      (∀ j, p j ∈ constrained U node Z (d j+1) ∧ d j ≤ h) ∧
      LinearIndependent ℝ (fun j => eval t (p j)) ∧
      span ℝ (Set.range (fun j => eval t (p j))) = evaluationFiltration U node Z t (h+1) ∧
      (∑ j, d j) = ∑ e ∈ Finset.range (h+1), e * columnIncrement U node Z t e := by
  obtain ⟨v, d, hli, hspan, hmem, hsum⟩ := exists_adapted_family
    (evaluationFiltration U node Z t) (evaluationFiltration_mono U node Z t)
    (evaluationFiltration_zero U node Z t) (h+1)
  have hex : ∀ i, ∃ p : constrained U node Z (d i+1),
      constrainedEval U node Z (d i+1) t p = v i := fun i => (hmem i).2
  choose p hp using hex
  have hpv : (fun i => eval t (p i).val) = v := funext hp
  refine ⟨fun i => (p i).val, d, ?_, ?_, ?_, hsum⟩
  · intro i
    exact ⟨(p i).property, Nat.le_of_lt_succ (hmem i).1⟩
  · rw [hpv]
    exact hli
  · rw [hpv]
    exact hspan

theorem exists_adapted_minor {κ : Type*} [Fintype κ] (b : Basis κ ℝ Z)
    (t : ℝ) (_ht : ∀ i, node i ≠ t) (h : ℕ) :
    ∃ (p : Fin (finrank ℝ (evaluationFiltration U node Z t (h+1))) → PolynomialModule ℝ Z)
      (d : Fin (finrank ℝ (evaluationFiltration U node Z t (h+1))) → ℕ)
      (r : Fin (finrank ℝ (evaluationFiltration U node Z t (h+1))) → κ),
      (∀ j, p j ∈ constrained U node Z (d j+1) ∧ d j ≤ h) ∧ Function.Injective r ∧
      let Δ := ((polynomialColumnMatrix b p).submatrix r id).det
      Δ.eval t ≠ 0 ∧
      Δ.natDegree ≤ ∑ e ∈ Finset.range (h+1), e * columnIncrement U node Z t e := by
  obtain ⟨p, d, hp, hli, hspan, hsum⟩ := exists_adapted_polynomials U node Z t h
  obtain ⟨r, hr, hd, hdeg⟩ := exists_polynomial_minor b p d (fun j => (hp j).1.1) t hli
  exact ⟨p, d, r, hp, hr, hd, hsum ▸ hdeg⟩

end Zarankiewicz

end

end OAI
