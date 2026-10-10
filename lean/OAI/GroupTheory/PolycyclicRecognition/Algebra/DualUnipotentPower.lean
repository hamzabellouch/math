import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConjugationDualSpectrum
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionEigenvaluesUnipotentPower
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace OAI

/-! # Returning from dual eigenvalues to an actual unipotent power

Dual functionals separate vectors. Thus nilpotence detected on the dual is
nilpotence of the original operator, with the same exponent.
-/

noncomputable section
namespace PolycyclicRecognition
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem dual_end_pow (T : Module.End K V) (n : ℕ) :
    (T ^ n).dualMap = T.dualMap ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ, ← ih]
    rfl

theorem dual_end_sub (T U : Module.End K V) :
    (T - U).dualMap = T.dualMap - U.dualMap := by
  ext φ v
  exact map_sub φ (T v) (U v)

theorem nilpotent_of_dual_nilpotent (T : Module.End K V)
    (h : IsNilpotent T.dualMap) : IsNilpotent T := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  apply LinearMap.ext
  intro v
  apply (Module.forall_dual_apply_eq_zero_iff K _).mp
  intro φ
  have he := congrArg (fun A : Module.End K (Module.Dual K V) => A φ v) hn
  rw [← dual_end_pow] at he
  exact he

theorem unipotent_power_of_dual_torsion_eigenvalues [Module.Finite K V]
    (T : Module.End K V) (hsplit : T.dualMap.charpoly.Splits)
    (hroots : ∀ z, Module.End.HasEigenvalue T.dualMap z →
      ∃ n : ℕ, 0 < n ∧ z ^ n = 1) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent (T ^ m - 1) := by
  obtain ⟨m, hm, hnil⟩ := unipotent_power_of_torsion_eigenvalues T.dualMap hsplit hroots
  refine ⟨m, hm, nilpotent_of_dual_nilpotent _ ?_⟩
  simpa only [dual_end_sub, dual_end_pow, show (1 : Module.End K V).dualMap = 1 from rfl]
    using hnil

theorem polynomial_growth_integral_conjugation_unipotent_power
    {G : Type*} [Group G] [DecidableEq G] [NumberField K] [Module.Finite K V]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (N : Subgroup G) [N.Normal] (t : G) (q : N →* Multiplicative V)
    (hq : Submodule.span K (Set.range (fun x => (q x).toAdd)) = ⊤)
    (T : Module.End K V) (hT : ∀ x, (q (MulAut.conjNormal t x)).toAdd = T (q x).toAdd)
    (hsplit : T.dualMap.charpoly.Splits)
    (hint : ∀ z, Module.End.HasEigenvalue T.dualMap z → IsIntegral ℤ z) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent (T ^ m - 1) := by
  apply unipotent_power_of_dual_torsion_eigenvalues T hsplit
  intro z hz
  exact polynomial_growth_integral_dual_eigenvalue_torsion
    S hS hgen hvol N t q hq T hT z hz (hint z hz)

end PolycyclicRecognition

end

end OAI
