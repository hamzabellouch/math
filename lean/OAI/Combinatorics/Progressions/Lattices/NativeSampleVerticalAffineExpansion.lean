import OAI.Combinatorics.Progressions.Estimates.SampledNativeModel

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

namespace NativeSampleModel

variable {σ X Y Ω : Type*} [Fintype Y] {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}

noncomputable def affineRestrictionTest
    (native : NativeSampleModel (fun _ : σ => 1) degree p sample f)
    (A : σ → Y → ℤ) (b : σ → ℤ) : native.model.Niltest (fun _ : Y => 1) :=
  native.test.affinePullback A b

theorem affineRestrictionTest_eval
    (native : NativeSampleModel (fun _ : σ => 1) degree p sample f)
    (physical : (Y → ℤ) → X) (A : σ → Y → ℤ) (b : σ → ℤ)
    (hsample : ∀ t, sample (physical t) = integerAffineMap A b t)
    (t : Y → ℤ) :
    (native.affineRestrictionTest A b).eval t = f (physical t) := by
  rw [affineRestrictionTest, native.test.eval_affinePullback, ← hsample t,
    ← native.eval]

theorem exists_affineRestriction_family
    (native : NativeSampleModel (fun _ : σ => 1) degree p sample f)
    (physical : Ω → (Y → ℤ) → X) (A : Ω → σ → Y → ℤ) (b : Ω → σ → ℤ)
    (hsample : ∀ a t, sample (physical a t) = integerAffineMap (A a) (b a) t) :
    ∃ tests : Ω → native.model.Niltest (fun _ : Y => 1),
      ∀ a, (tests a).observable = native.test.observable ∧
        (tests a).normBound = native.test.normBound ∧
        (tests a).lipBound = native.test.lipBound ∧
        (tests a).normBound ≤ 1 ∧ (tests a).ComplexityLE p ∧
        ∀ t, (tests a).eval t = f (physical a t) := by
  refine ⟨fun a => native.affineRestrictionTest (A a) (b a), ?_⟩
  intro a
  refine ⟨rfl, rfl, rfl, native.norm, ?_, ?_⟩
  · exact (native.test.affinePullback_complexityLE (A a) (b a) p).mpr native.complexity
  · exact native.affineRestrictionTest_eval (physical a) (A a) (b a) (hsample a)

end NativeSampleModel

namespace BooleanCubeKernel

theorem jointIntegerPhysicalSite_eq_integerAffineMap {K I : Type*} [Fintype K]
    (root : K → ℤ) (z : (I → ℤ) × (Option K × I → ℤ)) :
    jointIntegerPhysicalSite root z =
      integerAffineMap (fun i j => z.2 (some j, i))
        (fun i => z.1 i + z.2 (none, i)) root := by
  funext i
  simp only [jointIntegerPhysicalSite, Pi.add_apply, integerPhysicalSite,
    integerAffineMap, mul_comm, add_assoc]

end BooleanCubeKernel

namespace NativeSampleModel

theorem exists_jointPhysicalRestriction_family
    {K I Ω : Type*} [Fintype K] {degree : ℕ} {p : ℝ} {f : (I → ℤ) → ℂ}
    (native : NativeSampleModel (fun _ : I => 1) degree p id f)
    (z : Ω → (I → ℤ) × (Option K × I → ℤ)) :
    ∃ tests : Ω → native.model.Niltest (fun _ : K => 1),
      ∀ a, (tests a).observable = native.test.observable ∧
        (tests a).normBound = native.test.normBound ∧
        (tests a).lipBound = native.test.lipBound ∧
        (tests a).normBound ≤ 1 ∧ (tests a).ComplexityLE p ∧
        ∀ t, (tests a).eval t = f (BooleanCubeKernel.jointIntegerPhysicalSite t (z a)) := by
  exact native.exists_affineRestriction_family
    (fun a t => BooleanCubeKernel.jointIntegerPhysicalSite t (z a))
    (fun a i j => (z a).2 (some j, i))
    (fun a i => (z a).1 i + (z a).2 (none, i))
    (fun a t => BooleanCubeKernel.jointIntegerPhysicalSite_eq_integerAffineMap t (z a))

end NativeSampleModel

end Erdos3

end

section

namespace Erdos3.NativeSampleModel

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

namespace VerticalExpansion

variable {σ X Y : Type*} [Fintype Y] {degree : ℕ} {p q rho : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}
  {native : NativeSampleModel (fun _ : σ => 1) degree p sample f}
  (E : native.VerticalExpansion q rho)

noncomputable def affineComponent (A : σ → Y → ℤ) (b : σ → ℤ) (i : E.I) :
    native.model.Niltest (fun _ : Y => 1) :=
  (E.component i).affinePullback A b

@[simp] theorem affineComponent_observable (A : σ → Y → ℤ) (b : σ → ℤ) (i : E.I) :
    (E.affineComponent A b i).observable = (E.component i).observable := rfl

theorem affineComponent_orbit (A : σ → Y → ℤ) (b : σ → ℤ) (i : E.I) :
    (E.affineComponent A b i).orbit = (native.test.affinePullback A b).orbit := by
  change native.model.filtration.realification.polynomialOrbitSubstitute _ _
      (E.component i).orbit =
    native.model.filtration.realification.polynomialOrbitSubstitute _ _ native.test.orbit
  rw [E.orbit_eq]

@[simp] theorem affineComponent_normBound (A : σ → Y → ℤ) (b : σ → ℤ) (i : E.I) :
    (E.affineComponent A b i).normBound = native.test.normBound := E.norm_eq i

@[simp] theorem affineComponent_lipBound (A : σ → Y → ℤ) (b : σ → ℤ) (i : E.I) :
    (E.affineComponent A b i).lipBound = native.test.lipBound := E.lip_eq i

theorem affineComponent_complexity (A : σ → Y → ℤ) (b : σ → ℤ) (i : E.I) :
    (E.affineComponent A b i).ComplexityLE p := E.complexity i

theorem affineComponent_normBound_le (A : σ → Y → ℤ) (b : σ → ℤ) (i : E.I) :
    (E.affineComponent A b i).normBound ≤ 1 := E.normBound_le i

theorem affineComponent_vertical (A : σ → Y → ℤ) (b : σ → ℤ) (i : E.I)
    (z : native.model.RealGroup)
    (hz : z ∈ native.model.filtration.realification.subgroup degree)
    (x : native.model.Space) :
    (E.affineComponent A b i).observable (z • x) =
      character ((realifyFunctional (E.frequency i) z.coord : ℝ) : CircleFourier.Circle) *
        (E.affineComponent A b i).observable x := E.vertical i z hz x

theorem affineComponent_integral (A : σ → Y → ℤ) (b : σ → ℤ) (i : E.I)
    (hi : ∃ x, (E.affineComponent A b i).observable x ≠ 0)
    (z : native.model.RealGroup)
    (hz : z ∈ native.model.filtration.realification.subgroup degree)
    (hΓ : z ∈ native.model.realLattice) :
    ∃ n : ℤ, realifyFunctional (E.frequency i) z.coord = n := E.integral i hi z hz hΓ

theorem affineComponent_preserves_character (A : σ → Y → ℤ) (b : σ → ℤ)
    (z : native.model.RealGroup) (c : ℂ)
    (hchar : ∀ x, native.test.observable (z • x) = c * native.test.observable x)
    (i : E.I) (x : native.model.Space) :
    (E.affineComponent A b i).observable (z • x) =
      c * (E.affineComponent A b i).observable x := E.preserves_character z c hchar i x

@[simp] theorem affineComponent_eval (A : σ → Y → ℤ) (b : σ → ℤ) (i : E.I)
    (t : Y → ℤ) :
    (E.affineComponent A b i).eval t = (E.component i).eval (integerAffineMap A b t) :=
  (E.component i).eval_affinePullback A b t

theorem affineComponent_eval_error (A : σ → Y → ℤ) (b : σ → ℤ) (t : Y → ℤ) :
    ‖(∑ i, (E.affineComponent A b i).eval t) -
      (native.test.affinePullback A b).eval t‖ ≤ rho := by
  simpa only [affineComponent_eval, RationalFilteredNilmanifold.Niltest.eval_affinePullback]
    using E.eval_error (integerAffineMap A b t)

theorem affineComponent_sample_error (physical : (Y → ℤ) → X)
    (A : σ → Y → ℤ) (b : σ → ℤ)
    (hsample : ∀ t, sample (physical t) = integerAffineMap A b t) (t : Y → ℤ) :
    ‖(∑ i, (E.affineComponent A b i).eval t) - f (physical t)‖ ≤ rho := by
  simpa only [affineComponent_eval, ← hsample t] using E.sample_error (physical t)

theorem affineComponent_norm_eval_le (A : σ → Y → ℤ) (b : σ → ℤ)
    (i : E.I) (t : Y → ℤ) : ‖(E.affineComponent A b i).eval t‖ ≤ 1 := by
  rw [E.affineComponent_eval]
  exact E.norm_eval_le i _

section JointPhysical

variable {K I : Type*} [Fintype K] {g : (I → ℤ) → ℂ}
  {jointNative : NativeSampleModel (fun _ : I => 1) degree p id g}
  (Ejoint : jointNative.VerticalExpansion q rho)

noncomputable def jointPhysicalComponent
    (z : (I → ℤ) × (Option K × I → ℤ)) (i : Ejoint.I) :
    jointNative.model.Niltest (fun _ : K => 1) :=
  Ejoint.affineComponent (fun a k => z.2 (some k, a))
    (fun a => z.1 a + z.2 (none, a)) i

theorem jointPhysicalComponent_error
    (z : (I → ℤ) × (Option K × I → ℤ)) (t : K → ℤ) :
    ‖(∑ i, (Ejoint.jointPhysicalComponent z i).eval t) -
      g (BooleanCubeKernel.jointIntegerPhysicalSite t z)‖ ≤ rho :=
  Ejoint.affineComponent_sample_error
    (fun t => BooleanCubeKernel.jointIntegerPhysicalSite t z)
    (fun a k => z.2 (some k, a)) (fun a => z.1 a + z.2 (none, a))
    (fun t => BooleanCubeKernel.jointIntegerPhysicalSite_eq_integerAffineMap t z) t

end JointPhysical
end VerticalExpansion
end Erdos3.NativeSampleModel

end

end OAI
