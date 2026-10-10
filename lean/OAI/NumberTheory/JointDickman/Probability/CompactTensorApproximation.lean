import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.MvPolynomial

namespace OAI

/-! # Finite tensor approximation on the four-variable smooth support -/

namespace JointDickman
open scoped Topology

noncomputable def supportPolynomialMap (K : Set (Fin 4 → ℝ)) :
    MvPolynomial (Fin 4) ℝ →ₐ[ℝ] C(K,ℝ) :=
  MvPolynomial.aeval (fun i => ⟨fun x => (x : Fin 4 → ℝ) i,
    (continuous_apply i).comp continuous_subtype_val⟩)

theorem supportPolynomialMap_apply (K : Set (Fin 4 → ℝ))
    (P : MvPolynomial (Fin 4) ℝ) (x : K) :
    supportPolynomialMap K P x = MvPolynomial.eval (x : Fin 4 → ℝ) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [supportPolynomialMap]
  | add p q hp hq => simp [map_add,hp,hq]
  | mul_X p i hp =>
    have hp' := hp
    unfold supportPolynomialMap at hp'
    simp [supportPolynomialMap,map_mul,hp']

theorem supportPolynomialMap_separates (K : Set (Fin 4 → ℝ)) :
    (supportPolynomialMap K).range.SeparatesPoints := by
  intro x y hxy
  have hne : (x : Fin 4 → ℝ) ≠ (y : Fin 4 → ℝ) := fun he => hxy (Subtype.ext he)
  have hex : ∃ i : Fin 4, (x : Fin 4 → ℝ) i ≠ (y : Fin 4 → ℝ) i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨i,hi⟩ := hex
  refine ⟨fun x => supportPolynomialMap K (MvPolynomial.X i) x,
    ⟨supportPolynomialMap K (MvPolynomial.X i),
      (supportPolynomialMap K).mem_range_self (MvPolynomial.X i),rfl⟩,?_⟩
  simpa only [supportPolynomialMap_apply,MvPolynomial.eval_X] using hi

/-- The fourth coordinate can carry the external smooth parameter. Each
polynomial is a finite sum of products of one-coordinate powers. -/
theorem compact_support_polynomial_approximation (K : Set (Fin 4 → ℝ))
    (hK : IsCompact K) (f : C(K,ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 4) ℝ, ∀ x : K,
      |MvPolynomial.eval (x : Fin 4 → ℝ) P-f x| < ε := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨g,hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (supportPolynomialMap K).range (supportPolynomialMap_separates K) f f.continuous ε hε
  obtain ⟨P,hP⟩ := g.property
  refine ⟨P,?_⟩
  intro x
  have hh := hg x
  rw [← hP] at hh
  change ‖supportPolynomialMap K P x-f x‖ < ε at hh
  simpa only [supportPolynomialMap_apply,Real.norm_eq_abs] using hh

end JointDickman

end OAI
