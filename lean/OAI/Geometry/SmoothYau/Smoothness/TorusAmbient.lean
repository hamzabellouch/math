import Mathlib
import OAI.Geometry.SmoothYau.Geometry.RoundMetricExists

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E F A B M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
def productImmersion (f : M → A) (g : N → B) (x : M×N) : WithLp 2 (A×B) :=
  WithLp.toLp 2 (f x.1,g x.2)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma productImmersion_smooth {f : M → A} {g : N → B}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ f)
    (hg : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,B) ∞ g) :
    ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,WithLp 2 (A×B)) ∞ (productImmersion f g) := by
  have h : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,A×B) ∞
      (fun x : M×N => (f x.1,g x.2)) :=
    ((hf.comp contMDiff_fst).prodMk_space (hg.comp contMDiff_snd))
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.contDiff.contMDiff.comp
    h)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma productImmersion_derivative {f : M → A} {g : N → B}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ f)
    (hg : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,B) ∞ g) (x : M×N) :
    mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,WithLp 2 (A×B)) (productImmersion f g) x =
      (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.toContinuousLinearMap.comp
        ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) f x.1).prodMap
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,B) g x.2)) := by
  let L := (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.toContinuousLinearMap
  have hp : HasMFDerivAt (𝓘(ℝ,E).prod 𝓘(ℝ,F)) (𝓘(ℝ,A).prod 𝓘(ℝ,B))
      (fun x : M×N => (f x.1,g x.2)) x
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) f x.1).prodMap
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,B) g x.2)) :=
    ((hf.mdifferentiable (by simp) x.1).hasMFDerivAt.prodMap
      (hg.mdifferentiable (by simp) x.2).hasMFDerivAt)
  have hp' : HasMFDerivAt (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,A×B)
      (fun x : M×N => (f x.1,g x.2)) x
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) f x.1).prodMap
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,B) g x.2)) := by
    rw [modelWithCornersSelf_prod, ←chartedSpaceSelf_prod]
    exact hp
  exact ((L.hasFDerivAt.hasMFDerivAt).comp x hp').mfderiv

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma productImmersion_injective_derivative {f : M → A} {g : N → B}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ f)
    (hg : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,B) ∞ g)
    (hfi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) f x))
    (hgi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,B) g x)) (x : M×N) :
    Function.Injective (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,WithLp 2 (A×B)) (productImmersion f g) x) := by
  rw [productImmersion_derivative hf hg]
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.injective.comp
    (Prod.map_injective.mpr ⟨hfi x.1,hgi x.2⟩)

end


open Set Filter Manifold Bundle
open scoped Topology ContDiff

abbrev TorusAmbient := WithLp 2 (ℂ × ℂ)
abbrev FourAmbient := WithLp 2 (Euclidean 3 × TorusAmbient)

def torusImmersion : Circle × Circle → TorusAmbient :=
  productImmersion (fun x : Circle => (x : ℂ)) (fun x : Circle => (x : ℂ))

lemma circle_immersion_smooth :
    ContMDiff 𝓘(ℝ,Euclidean 1) 𝓘(ℝ,ℂ) ∞ (fun x : Circle => (x : ℂ)) := by
  let : Fact (Module.finrank ℝ ℂ = 1+1) := ⟨by simp⟩
  exact contMDiff_coe_sphere

lemma circle_immersion_injective (x : Circle) :
    Function.Injective (mfderiv 𝓘(ℝ,Euclidean 1) 𝓘(ℝ,ℂ) (fun x : Circle => (x : ℂ)) x) := by
  let : Fact (Module.finrank ℝ ℂ = 1+1) := ⟨by simp⟩
  exact injective_mvfderiv_subtypeVal_sphere x

lemma torusImmersion_smooth : ContMDiff 𝓘(ℝ,Euclidean 1 × Euclidean 1)
    𝓘(ℝ,TorusAmbient) ∞ torusImmersion := by
  rw [modelWithCornersSelf_prod]
  exact productImmersion_smooth circle_immersion_smooth circle_immersion_smooth

lemma torusImmersion_injective (x : Circle × Circle) :
    Function.Injective (mfderiv 𝓘(ℝ,Euclidean 1 × Euclidean 1)
      𝓘(ℝ,TorusAmbient) torusImmersion x) := by
  rw [modelWithCornersSelf_prod]
  exact productImmersion_injective_derivative circle_immersion_smooth circle_immersion_smooth
    circle_immersion_injective circle_immersion_injective x

def fourImmersion : FourManifold → FourAmbient :=
  productImmersion (fun x : Sphere 2 => (x : Euclidean 3)) torusImmersion

lemma sphere_two_immersion_smooth :
    ContMDiff 𝓘(ℝ,Euclidean 2) 𝓘(ℝ,Euclidean 3) ∞ (fun x : Sphere 2 => (x : Euclidean 3)) := by
  let : Fact (Module.finrank ℝ (Euclidean 3) = 2+1) := ⟨by simp [Euclidean]⟩
  exact contMDiff_coe_sphere

lemma sphere_two_immersion_injective (x : Sphere 2) :
    Function.Injective (mfderiv 𝓘(ℝ,Euclidean 2) 𝓘(ℝ,Euclidean 3)
      (fun x : Sphere 2 => (x : Euclidean 3)) x) := by
  let : Fact (Module.finrank ℝ (Euclidean 3) = 2+1) := ⟨by simp [Euclidean]⟩
  exact injective_mvfderiv_subtypeVal_sphere x

lemma fourImmersion_smooth : ContMDiff 𝓘(ℝ,FourModel) 𝓘(ℝ,FourAmbient) ∞ fourImmersion := by
  rw [show 𝓘(ℝ,FourModel) = 𝓘(ℝ,Euclidean 2).prod 𝓘(ℝ,Euclidean 1 × Euclidean 1)
    from modelWithCornersSelf_prod]
  exact productImmersion_smooth sphere_two_immersion_smooth torusImmersion_smooth

lemma fourImmersion_injective (x : FourManifold) :
    Function.Injective (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourAmbient) fourImmersion x) := by
  rw [show 𝓘(ℝ,FourModel) = 𝓘(ℝ,Euclidean 2).prod 𝓘(ℝ,Euclidean 1 × Euclidean 1)
    from modelWithCornersSelf_prod]
  exact productImmersion_injective_derivative sphere_two_immersion_smooth torusImmersion_smooth
    sphere_two_immersion_injective torusImmersion_injective x

def fourBackgroundMetric : SmoothMetric FourModel FourManifold :=
  inducedMetric fourImmersion fourImmersion_smooth fourImmersion_injective

lemma fourBackgroundMetric_inner (x : FourManifold) (v w : TangentSpace 𝓘(ℝ,FourModel) x) :
    fourBackgroundMetric.inner x v w =
      inner ℝ (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourAmbient) fourImmersion x v)
        (mfderiv 𝓘(ℝ,FourModel) 𝓘(ℝ,FourAmbient) fourImmersion x w) := rfl


end YauCounterexamples
end

end OAI
