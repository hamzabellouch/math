import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases

namespace OAI

noncomputable section
open scoped Matrix

namespace SmoothLocal.Geometry

theorem mem_orthogonal_span_range_of_inner_eq_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} (t : ι → V) (w : V) (hw : ∀ i, inner ℝ (t i) w = 0) :
    w ∈ (Submodule.span ℝ (Set.range t))ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro x ⟨i, rfl⟩
    exact hw i
  · simp
  · intro a b ha hb hia hib
    simp only [inner_add_left, hia, hib, add_zero]
  · intro c a ha hia
    simp only [real_inner_smul_left, hia, mul_zero]

theorem normalSpace_finrank
    (t : Fin 2 → EuclideanSpace ℝ (Fin 3)) (ht : LinearIndependent ℝ t) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range t))ᗮ = 1 := by
  apply Submodule.finrank_add_finrank_orthogonal'
  simp [finrank_span_eq_card ht]

theorem exists_unit_normal_of_independent_tangents
    (t : Fin 2 → EuclideanSpace ℝ (Fin 3)) (ht : LinearIndependent ℝ t) :
    ∃ n : EuclideanSpace ℝ (Fin 3),
      inner ℝ n n = 1 ∧ ∀ i, inner ℝ (t i) n = 0 := by
  let T := Submodule.span ℝ (Set.range t)
  have hdim : Module.finrank ℝ Tᗮ = 1 := normalSpace_finrank t ht
  have hbot : Tᗮ ≠ ⊥ := by
    intro heq
    have hzero : Module.finrank ℝ Tᗮ = 0 := by rw [heq, finrank_bot]
    exact Nat.zero_ne_one (hzero.symm.trans hdim)
  obtain ⟨n, hnT, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨‖n‖⁻¹ • n, ?_, ?_⟩
  · have hnorm : ‖(‖n‖⁻¹ : ℝ) • n‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hn0
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow]
  · intro i
    rw [real_inner_smul_right]
    have hi : t i ∈ T := Submodule.subset_span (Set.mem_range_self i)
    rw [Submodule.inner_right_of_mem_orthogonal hi hnT, mul_zero]

theorem normal_eq_inner_smul_of_independent_tangents
    (t : Fin 2 → EuclideanSpace ℝ (Fin 3)) (ht : LinearIndependent ℝ t)
    (n w : EuclideanSpace ℝ (Fin 3)) (hn : inner ℝ n n = 1)
    (hnt : ∀ i, inner ℝ (t i) n = 0)
    (hwt : ∀ i, inner ℝ (t i) w = 0) :
    w = (inner ℝ n w) • n := by
  let T := Submodule.span ℝ (Set.range t)
  have hnT : n ∈ Tᗮ := mem_orthogonal_span_range_of_inner_eq_zero t n hnt
  have hwT : w ∈ Tᗮ := mem_orthogonal_span_range_of_inner_eq_zero t w hwt
  have hn0 : n ≠ 0 := by
    intro heq
    simp [heq] at hn
  have hdim : Module.finrank ℝ Tᗮ = 1 := normalSpace_finrank t ht
  have hspan : Tᗮ = ℝ ∙ n :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim hnT hn0
  rw [hspan] at hwT
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwT
  rw [← hc, real_inner_smul_right, hn, mul_one]

theorem normal_eq_inner_smul_of_pair
    (u v n w : EuclideanSpace ℝ (Fin 3)) (huv : LinearIndependent ℝ ![u, v])
    (hn : inner ℝ n n = 1) (hun : inner ℝ u n = 0) (hvn : inner ℝ v n = 0)
    (huw : inner ℝ u w = 0) (hvw : inner ℝ v w = 0) :
    w = (inner ℝ n w) • n := by
  apply normal_eq_inner_smul_of_independent_tangents ![u, v] huv n w hn
  · intro i
    fin_cases i <;> simp [hun, hvn]
  · intro i
    fin_cases i <;> simp [huw, hvw]

end SmoothLocal.Geometry

end

end OAI
