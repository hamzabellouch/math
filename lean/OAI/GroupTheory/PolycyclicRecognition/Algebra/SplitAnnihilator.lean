import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealEigenAnnihilator
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

namespace OAI

/-! # Split annihilators and real generalized eigenspaces

The usual finite-dimensional decomposition only needs a split annihilator,
rather than an algebraically closed scalar field. Restrictions retain the
same annihilator, so the argument also applies to invariant subspaces.
-/

noncomputable section
namespace PolycyclicRecognition

open Polynomial Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem aeval_restrict_apply (f : Module.End ℝ V) (S : Submodule ℝ V)
    (hS : ∀ v ∈ S, f v ∈ S) (p : ℝ[X]) (v : S) :
    ((aeval (f.restrict hS) p v : S) : V) = aeval f p (v : V) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul_of_tower]
    congr 1
    induction n with
    | zero => rfl
    | succ n hn =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      exact congrArg f hn

theorem aeval_restrict_eq_zero (f : Module.End ℝ V) (S : Submodule ℝ V)
    (hS : ∀ v ∈ S, f v ∈ S) (p : ℝ[X]) (hp : aeval f p = 0) :
    aeval (f.restrict hS) p = 0 := by
  ext v
  rw [aeval_restrict_apply, hp]
  rfl

theorem exists_eigenvalue_of_split_annihilator [FiniteDimensional ℝ V] [Nontrivial V]
    (f : Module.End ℝ V) (p : ℝ[X]) (hp0 : p ≠ 0) (hps : p.Splits)
    (hp : aeval f p = 0) : ∃ r : ℝ, f.HasEigenvalue r := by
  have hi := Algebra.IsIntegral.isIntegral (R := ℝ) f
  have hs : (minpoly ℝ f).Splits := hps.of_dvd hp0 (minpoly.dvd ℝ f hp)
  obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero (ne_of_gt (minpoly.degree_pos hi))
  exact ⟨r, Module.End.hasEigenvalue_of_isRoot hr⟩

theorem iSup_maxGenEigenspace_eq_top_of_split_annihilator [FiniteDimensional ℝ V]
    (f : Module.End ℝ V) (p : ℝ[X]) (hp0 : p ≠ 0) (hps : p.Splits)
    (hp : aeval f p = 0) : ⨆ r : ℝ, f.maxGenEigenspace r = ⊤ := by
  suffices ∀ n, finrank ℝ V = n → ⨆ r : ℝ, f.maxGenEigenspace r = ⊤ by
    exact this _ rfl
  intro n hn
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    rcases n with - | n
    · rw [← top_le_iff]
      simp only [Submodule.finrank_eq_zero.1 (Eq.trans (finrank_top _ _) hn), bot_le]
    · have : Nontrivial V := finrank_pos_iff.1 (by rw [hn]; exact Nat.zero_lt_succ n)
      obtain ⟨r, hr⟩ := exists_eigenvalue_of_split_annihilator f p hp0 hps hp
      let ES := f.genEigenspace r (finrank ℝ V)
      let ER := f.genEigenrange r (finrank ℝ V)
      have hER : ∀ v ∈ ER, f v ∈ ER := fun v hv =>
        Module.End.map_genEigenrange_le (Submodule.mem_map_of_mem hv)
      let f' : Module.End ℝ ER := f.restrict hER
      have hpos : 0 < finrank ℝ ES := by
        dsimp +instances only [ES]
        rw [hn]
        exact Module.End.pos_finrank_genEigenspace_of_hasEigenvalue hr (Nat.zero_lt_succ n)
      have hadd : finrank ℝ ER + finrank ℝ ES = finrank ℝ V := by
        dsimp +instances only [ER, ES]
        rw [Module.End.genEigenspace_nat, Module.End.genEigenrange_nat]
        exact LinearMap.finrank_range_add_finrank_ker _
      have hlt : finrank ℝ ER < n.succ := by omega
      have hspan : ⨆ r : ℝ, f'.maxGenEigenspace r = ⊤ :=
        ih (finrank ℝ ER) hlt f' (aeval_restrict_eq_zero f ER hER p hp) rfl
      have hspan' : ⨆ r : ℝ, (f'.maxGenEigenspace r).map ER.subtype = ER := by
        simp only [(Submodule.map_iSup _ _).symm, hspan, Submodule.map_subtype_top ER]
      have hmap : ∀ r, (f'.maxGenEigenspace r).map ER.subtype ≤ f.maxGenEigenspace r := by
        intro r
        rw [Module.End.maxGenEigenspace, Module.End.genEigenspace_restrict]
        apply Submodule.map_comap_le
      have hleR : ER ≤ ⨆ r : ℝ, f.maxGenEigenspace r := by
        rw [← hspan']
        exact iSup_mono hmap
      have hleS : ES ≤ ⨆ r : ℝ, f.maxGenEigenspace r :=
        ((f.genEigenspace r).mono le_top).trans (le_iSup f.maxGenEigenspace r)
      have hdis : Disjoint ER ES := Module.End.generalized_eigenvec_disjoint_range_ker f r
      rw [← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES hadd.ge hdis]
      exact sup_le hleR hleS

end PolycyclicRecognition

end

end OAI
