import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.BilinearModulus

namespace OAI

/-! Dominated factorization for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace HochschildDomination
universe u v
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

@[nolint unusedArguments]
def PreHilbert (_φ _ψ : M →ₚ[ℂ] ℂ) := M

namespace PreHilbert
variable (φ ψ : M →ₚ[ℂ] ℂ)
instance : AddCommGroup (PreHilbert φ ψ) := inferInstanceAs (AddCommGroup M)
instance : Module ℂ (PreHilbert φ ψ) := inferInstanceAs (Module ℂ M)

def of : M ≃ₗ[ℂ] PreHilbert φ ψ := LinearEquiv.refl ℂ _
def val : PreHilbert φ ψ ≃ₗ[ℂ] M := LinearEquiv.refl ℂ _

omit [StarOrderedRing M] in
@[simp] lemma of_val (x : PreHilbert φ ψ) : of φ ψ (val φ ψ x) = x := rfl
omit [StarOrderedRing M] in
@[simp] lemma val_of (x : M) : val φ ψ (of φ ψ x) = x := rfl

abbrev core : PreInnerProductSpace.Core ℂ (PreHilbert φ ψ) where
  inner x y := φ (star (val φ ψ x) * val φ ψ y) +
    ψ (val φ ψ y * star (val φ ψ x))
  conj_inner_symm := by
    intro x y
    simp [← Complex.star_def, ← map_star φ, ← map_star ψ, star_add]
  re_inner_nonneg x := by
    exact add_nonneg (Complex.nonneg_iff.mp (φ.map_nonneg (star_mul_self_nonneg _))).1
      (Complex.nonneg_iff.mp (ψ.map_nonneg (mul_star_self_nonneg _))).1
  add_left := by
    intros
    simp only [map_add, star_add, add_mul, mul_add]
    ring
  smul_left := by
    intros
    simp only [map_smul, star_smul, smul_mul_assoc, mul_smul_comm, map_smul,
      smul_eq_mul, starRingEnd_apply, mul_add]

instance : SeminormedAddCommGroup (PreHilbert φ ψ) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := core φ ψ)
instance : InnerProductSpace ℂ (PreHilbert φ ψ) :=
  InnerProductSpace.ofCore (core φ ψ)

lemma norm_def (x : PreHilbert φ ψ) :
    ‖x‖ = Real.sqrt ((φ (star (val φ ψ x) * val φ ψ x) +
      ψ (val φ ψ x * star (val φ ψ x))).re) := rfl

lemma norm_of_le (b : M) :
    ‖of φ ψ b‖ ≤ Real.sqrt (‖φ 1‖ + ‖ψ 1‖) * ‖b‖ := by
  rw [norm_def]
  refine (Real.sqrt_le_iff).2 ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  change (φ (star b * b)).re + (ψ (b * star b)).re ≤ _
  calc
    _ ≤ ‖φ (star b * b)‖ + ‖ψ (b * star b)‖ :=
      add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)
    _ ≤ ‖φ 1‖ * ‖star b * b‖ + ‖ψ 1‖ * ‖b * star b‖ :=
      add_le_add (φ.norm_apply_le_of_nonneg _ (star_mul_self_nonneg _))
        (ψ.norm_apply_le_of_nonneg _ (mul_star_self_nonneg _))
    _ = (‖φ 1‖ + ‖ψ 1‖) * ‖b‖ ^ 2 := by
      rw [CStarRing.norm_star_mul_self, CStarRing.norm_self_mul_star]
      ring

def ofCLM : M →L[ℂ] PreHilbert φ ψ :=
  (of φ ψ).toLinearMap.mkContinuous (Real.sqrt (‖φ 1‖ + ‖ψ 1‖)) (norm_of_le φ ψ)

@[simp] lemma ofCLM_apply (b : M) : ofCLM φ ψ b = of φ ψ b := rfl

end PreHilbert

abbrev Hilbert (φ ψ : M →ₚ[ℂ] ℂ) := UniformSpace.Completion (PreHilbert φ ψ)

def beta (φ ψ : M →ₚ[ℂ] ℂ) : M →L[ℂ] Hilbert φ ψ :=
  UniformSpace.Completion.toComplL.comp (PreHilbert.ofCLM φ ψ)

variable (B : M →L[ℂ] StrongDual ℂ M) (φ ψ : M →ₚ[ℂ] ℂ)
  (C : ℝ) (hC : 0 ≤ C)
  (hdom : ∀ a b, ‖B a b‖ ≤ C * ‖a‖ * ‖PreHilbert.of φ ψ b‖)

def alphaPre : PreHilbert φ ψ →L[ℂ] StrongDual ℂ M :=
  (B.flip.toLinearMap.comp (PreHilbert.val φ ψ).toLinearMap).mkContinuous C (by
    intro x
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg x))
    intro a
    change ‖B a (PreHilbert.val φ ψ x)‖ ≤ C * ‖x‖ * ‖a‖
    have h := hdom a (PreHilbert.val φ ψ x)
    rw [PreHilbert.of_val] at h
    convert h using 1
    ring)

def alpha : Hilbert φ ψ →L[ℂ] StrongDual ℂ M :=
  (alphaPre B φ ψ C hC hdom).extend UniformSpace.Completion.toComplL

lemma factorization (a b : M) : B a b = alpha B φ ψ C hC hdom (beta φ ψ b) a := by
  have h := ContinuousLinearMap.extend_eq (alphaPre B φ ψ C hC hdom)
    (e := (UniformSpace.Completion.toComplL : PreHilbert φ ψ →L[ℂ] Hilbert φ ψ))
    UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) (PreHilbert.of φ ψ b)
  exact (congrArg (fun F : StrongDual ℂ M => F a) h).symm

end HochschildDomination

open scoped InnerProductSpace ComplexOrder
namespace HochschildDomination
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma beta_norm_sq (φ ψ : M →ₚ[ℂ] ℂ) (b : M) :
    ‖beta φ ψ b‖^2 = (φ (star b * b)).re + (ψ (b * star b)).re := by
  change ‖(PreHilbert.of φ ψ b : UniformSpace.Completion (PreHilbert φ ψ))‖^2 = _
  rw [UniformSpace.Completion.norm_coe, PreHilbert.norm_def]
  exact Real.sq_sqrt (add_nonneg
    (Complex.nonneg_iff.mp (φ.map_nonneg (star_mul_self_nonneg b))).1
    (Complex.nonneg_iff.mp (ψ.map_nonneg (mul_star_self_nonneg b))).1)

omit [PartialOrder M] [StarOrderedRing M] in

theorem exists_quartic_hilbert_modulus (B : M →L[ℂ] StrongDual ℂ M) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (β : M →L[ℂ] H) (C : ℝ),
      0 ≤ C ∧ ∀ b, ‖B.flip b‖^4 ≤ C * ‖b‖^2 * ‖β b‖^2 := by
  let := CStarAlgebra.spectralOrder M
  let := CStarAlgebra.spectralOrderedRing M
  have hp : ∃ (φ ψ : M →ₚ[ℂ] ℂ) (C : ℝ), 0 ≤ C ∧ ∀ b,
      ‖B.flip b‖^4 ≤ C * ‖b‖^2 *
        ((φ (star b * b)).re + (ψ (b * star b)).re) := by
    cases subsingleton_or_nontrivial M with
    | inl hs =>
      let := hs
      refine ⟨0,0,0,le_rfl,?_⟩
      intro b
      have hb : b = 0 := Subsingleton.elim _ _
      simp [hb]
    | inr hn =>
      let := hn
      exact HochschildFourPoint.quartic_state_modulus B
  obtain ⟨φ,ψ,C,hC,hdom⟩ := hp
  refine ⟨Hilbert φ ψ,inferInstance,inferInstance,inferInstance,beta φ ψ,C,hC,?_⟩
  intro b
  rw [beta_norm_sq]
  exact hdom b

end HochschildDomination

end

end OAI
