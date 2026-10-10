import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralExtensionTransgressionExact
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntegralAbelianBarBoundary

namespace OAI

/-! # Explicit lifts of two-chains through a central extension -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {N G Q : Type} [CommGroup N] [Group G] [Group Q]
variable (E : GroupExtension N G Q)

def centralSectionChains (σ : E.Section) : (Q →₀ ℤ) →ₗ[ℤ] (G →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ σ

def centralBarKernelLetters (σ : E.Section) : ((Q × Q) →₀ ℤ) →ₗ[ℤ] (N →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun p => GroupExtensionSection.factor E σ p.1 p.2)

def centralBarLift (σ : E.Section) : ((Q × Q) →₀ ℤ) →ₗ[ℤ] ((G × G) →₀ ℤ) :=
  Finsupp.lsum ℤ (fun p => Finsupp.lsingle (σ p.1, σ p.2) -
    Finsupp.lsingle (E.inl (GroupExtensionSection.factor E σ p.1 p.2), σ (p.1 * p.2)))

@[simp] theorem centralSectionChains_single (σ : E.Section) (q : Q) (n : ℤ) :
    centralSectionChains E σ (Finsupp.single q n) = Finsupp.single (σ q) n := by
  simp [centralSectionChains]

@[simp] theorem centralBarKernelLetters_single (σ : E.Section) (q r : Q) (n : ℤ) :
    centralBarKernelLetters E σ (Finsupp.single (q, r) n) =
      Finsupp.single (GroupExtensionSection.factor E σ q r) n := by
  simp [centralBarKernelLetters]

@[simp] theorem centralBarLift_single (σ : E.Section) (q r : Q) (n : ℤ) :
    centralBarLift E σ (Finsupp.single (q, r) n) =
      Finsupp.single (σ q, σ r) n -
        Finsupp.single (E.inl (GroupExtensionSection.factor E σ q r), σ (q * r)) n := by
  simp [centralBarLift]

theorem centralBarLift_boundary (σ : E.Section) (z : (Q × Q) →₀ ℤ) :
    groupHomology.d₂₁ (integralTrivialCoefficient G) (centralBarLift E σ z) =
      centralSectionChains E σ (groupHomology.d₂₁ (integralTrivialCoefficient Q) z) -
        groupHomology.chainsMap₁ E.inl (groupIntegralTrivialCoefficientMap E.inl)
          (centralBarKernelLetters E σ z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]; abel
  | single p n =>
    rcases p with ⟨q, r⟩
    rw [centralBarLift_single, map_sub, groupHomology.d₂₁_single,
      groupHomology.d₂₁_single, groupHomology.d₂₁_single,
      centralBarKernelLetters_single, integralBarMap₁_single]
    change (Finsupp.single (σ r) n - Finsupp.single (σ q * σ r) n +
        Finsupp.single (σ q) n) -
      (Finsupp.single (σ (q * r)) n -
        Finsupp.single (E.inl (GroupExtensionSection.factor E σ q r) * σ (q * r)) n +
          Finsupp.single (E.inl (GroupExtensionSection.factor E σ q r)) n) =
      centralSectionChains E σ
        (Finsupp.single r n - Finsupp.single (q * r) n + Finsupp.single q n) -
          Finsupp.single (E.inl (GroupExtensionSection.factor E σ q r)) n
    rw [← GroupExtensionSection.section_mul E σ]
    simp only [map_add, map_sub, centralSectionChains_single]
    abel

theorem centralBarKernelLetters_sum (σ : E.Section) (z : (Q × Q) →₀ ℤ) :
    abelianBarSum (centralBarKernelLetters E σ z) =
      groupTwoCocycleChains (centralExtensionTwoCocycle E σ) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single p n =>
    rcases p with ⟨q, r⟩
    rw [centralBarKernelLetters_single, groupTwoCocycleChains_single]
    simp [abelianBarSum, centralExtensionTwoCocycle]

end PolycyclicRecognition

end

end OAI
