import Mathlib
import OAI.Analysis.HardSphere.Bridges.PartialIndex
import OAI.Analysis.HardSphere.Geometry.ConfigurationPath

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere.FreeFourier
lemma argument_add (L : ℝ) (n : ℤ) (x y : AddCircle L) :
    fourier n (x+y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

lemma gaussian_character (L : ℝ) (n : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x : ℝ, fourier n ((Real.sqrt (2*t) * x : ℝ) : AddCircle L)
      ∂gaussianReal 0 1) = (Real.exp (-t * (2*Real.pi*n/L)^2) : ℂ) := by
  have h := charFun_gaussianReal (μ := 0) (v := 1) ((2*Real.pi*n/L)*Real.sqrt (2*t))
  rw [charFun_apply_real] at h
  have he (x : ℝ) : fourier n ((Real.sqrt (2*t)*x : ℝ) : AddCircle L) =
      Complex.exp (((2*Real.pi*n/L)*Real.sqrt (2*t)*x : ℝ) * Complex.I) := by
    rw [fourier_coe_apply]
    push_cast
    congr 1
    ring
  simp_rw [he]
  simp only [Complex.ofReal_mul] at h ⊢
  rw [h, Complex.ofReal_exp]
  congr 1
  have hs := Real.sq_sqrt (show 0 ≤ 2*t by positivity)
  push_cast at hs ⊢
  simp only [mul_zero, zero_mul, one_mul, zero_sub]
  rw [mul_pow]
  norm_cast at hs
  have hs' : (Real.sqrt (2*t) : ℂ)^2 = 2*t := by exact_mod_cast hs
  rw [hs']
  ring
end HardSphere.FreeFourier

namespace HardSphere
open Wiener ProbabilityTheory
open scoped ComplexConjugate

def configurationCharacter (N : ℕ) (L : Length) (k : Direction N → ℤ) :
    C(Configuration N L, ℂ) where
  toFun X := ∏ p : Direction N, fourier (k p) (X p.1 p.2)
  continuous_toFun := by fun_prop

lemma configurationCharacter_norm (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (X : Configuration N L) : ‖configurationCharacter N L k X‖ = 1 := by
  simp only [configurationCharacter, ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, Finset.prod_const_one]

lemma configurationCharacter_add_argument (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (X Y : Configuration N L) :
    configurationCharacter N L k (X+Y) =
      configurationCharacter N L k X * configurationCharacter N L k Y := by
  simp only [configurationCharacter, ContinuousMap.coe_mk, Pi.add_apply,
    FreeFourier.argument_add, Finset.prod_mul_distrib]

lemma wiener_endpoint_law : HasLaw (fun w : C(Time,ℝ) ↦ w 1) (gaussianReal 0 1) wiener := by
  simpa using wiener_projection_law (ι := Unit) (fun _ ↦ (1:ℝ)) (fun _ ↦ (1:Time))

lemma wiener_character (L : Length) (n : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ w : C(Time,ℝ), fourier n ((Real.sqrt (2*t)*w 1 : ℝ) : AddCircle L.val) ∂wiener) =
      (Real.exp (-t*(2*Real.pi*n/L.val)^2) : ℂ) := by
  have hcont : Continuous (fun x : ℝ ↦ fourier n ((Real.sqrt (2*t)*x : ℝ) : AddCircle L.val)) := by
    fun_prop
  exact (wiener_endpoint_law.integral_comp hcont.aestronglyMeasurable).trans
    (FreeFourier.gaussian_character L.val n t ht)

def fourierEnergy (N : ℕ) (L : Length) (k : Direction N → ℤ) : ℝ :=
  ∑ p : Direction N, (((2 : ℕ) : ℝ)*Real.pi*k p/L.val)^2

lemma fourierEnergy_nonneg (N : ℕ) (L : Length) (k : Direction N → ℤ) :
    0 ≤ fourierEnergy N L k := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma freeTrajectory_character_integral (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (t : ℝ) (ht : 0 ≤ t) (X : Configuration N L) :
    (∫ w, configurationCharacter N L k (freeTrajectory N L t w X 1) ∂coordinateWiener N) =
      configurationCharacter N L k X * (Real.exp (-t * fourierEnergy N L k) : ℂ) := by
  have hpoint (w : CoordinatePaths N) :
      configurationCharacter N L k (freeTrajectory N L t w X 1) =
        configurationCharacter N L k X *
          ∏ p : Direction N, fourier (k p) ((Real.sqrt (2*t)*w p 1 : ℝ) : AddCircle L.val) := by
    simp only [configurationCharacter, freeTrajectory, ContinuousMap.coe_mk,
      FreeFourier.argument_add, Finset.prod_mul_distrib]
  simp_rw [hpoint]
  rw [integral_const_mul]
  congr 1
  rw [coordinateWiener, integral_fintype_prod_eq_prod
    (fun p (w : C(Time,ℝ)) ↦ fourier (k p) ((Real.sqrt (2*t)*w 1 : ℝ) : AddCircle L.val))]
  simp_rw [wiener_character L _ t ht]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [fourierEnergy, Nat.cast_ofNat, Finset.mul_sum]

end HardSphere

namespace HardSphere
open scoped ComplexConjugate
open Submodule Algebra
lemma configurationCharacter_neg (N : ℕ) (L : Length) (k : Direction N → ℤ)
    (X : Configuration N L) :
    configurationCharacter N L (-k) X = conj (configurationCharacter N L k X) := by
  simp only [configurationCharacter, Pi.neg_apply, fourier_neg, ContinuousMap.coe_mk, map_prod]

lemma configurationCharacter_add (N : ℕ) (L : Length) (k l : Direction N → ℤ)
    (X : Configuration N L) :
    configurationCharacter N L (k+l) X =
      configurationCharacter N L k X * configurationCharacter N L l X := by
  simp only [configurationCharacter, Pi.add_apply, fourier_add, ContinuousMap.coe_mk,
    Finset.prod_mul_distrib]

lemma configurationCharacter_zero (N : ℕ) (L : Length) :
    configurationCharacter N L (0 : Direction N → ℤ) = 1 := by
  ext X
  simp only [configurationCharacter, Pi.zero_apply, fourier_zero, Finset.prod_const_one,
    ContinuousMap.coe_mk, ContinuousMap.one_apply]

lemma configurationCharacter_single (N : ℕ) (L : Length) (p : Direction N)
    (X : Configuration N L) :
    configurationCharacter N L (Pi.single p 1) X = fourier 1 (X p.1 p.2) := by
  classical
  change (∏ q : Direction N, fourier ((Pi.single p 1 : Direction N → ℤ) q) (X q.1 q.2)) = _
  rw [Finset.prod_eq_single p]
  · simp
  · intro q _ hqp
    simp only [Pi.single_eq_of_ne hqp, fourier_zero]
  · simp

def characterAlgebra (N : ℕ) (L : Length) : StarSubalgebra ℂ C(Configuration N L, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range (configurationCharacter N L))
  star_mem' := by
    change Algebra.adjoin ℂ (range (configurationCharacter N L)) ≤
      star (Algebra.adjoin ℂ (range (configurationCharacter N L)))
    refine adjoin_le ?_
    rintro _ ⟨k,rfl⟩
    refine subset_adjoin ⟨-k, ?_⟩
    ext X
    simp only [configurationCharacter_neg, starRingEnd_apply, ContinuousMap.star_apply]

lemma characterAlgebra_eq_span (N : ℕ) (L : Length) :
    (characterAlgebra N L).toSubalgebra.toSubmodule =
      span ℂ (range (configurationCharacter N L)) := by
  apply adjoin_eq_span_of_subset
  refine .trans (fun x ↦ Submonoid.closure_induction (fun _ ↦ id) ⟨0, ?_⟩ ?_) subset_span
  · exact configurationCharacter_zero N L
  · rintro _ _ _ _ ⟨k,rfl⟩ ⟨l,rfl⟩
    exact ⟨k+l,ContinuousMap.ext fun X ↦ configurationCharacter_add N L k l X⟩

lemma characterAlgebra_separates (N : ℕ) (L : Length) :
    (characterAlgebra N L).SeparatesPoints := by
  classical
  intro X Y hXY
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hXY
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hi
  refine ⟨_, ⟨configurationCharacter N L (Pi.single (i,j) 1),
    subset_adjoin ⟨Pi.single (i,j) 1,rfl⟩,rfl⟩, ?_⟩
  dsimp only
  rw [configurationCharacter_single, configurationCharacter_single, fourier_one, fourier_one]
  exact fun h ↦ hj (AddCircle.injective_toCircle L.property.ne' (Circle.coe_injective h))

lemma character_span_dense (N : ℕ) (L : Length) :
    (span ℂ (range (configurationCharacter N L))).topologicalClosure = ⊤ := by
  rw [← characterAlgebra_eq_span]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
      (characterAlgebra_separates N L))

section

attribute [local instance] scalarL2_addCommMonoid scalarL2_module

local instance complexBoundedSMul : IsBoundedSMul ℂ ℂ := inferInstance

def characterL2 (N : ℕ) (L : Length) (k : Direction N → ℤ) : ScalarL2 N L :=
  DFunLike.coe (F := C(Configuration N L, ℂ) →L[ℂ] ScalarL2 N L)
    (β := fun _ ↦ ScalarL2 N L)
    (@ContinuousMap.toLp _ ℂ _ _ volume _ _ _ _ _ _ ℂ _ _ _ complexBoundedSMul)
    (configurationCharacter N L k)

end

lemma characterL2_ae (N : ℕ) (L : Length) (k : Direction N → ℤ) :
    characterL2 N L k =ᵐ[volume] configurationCharacter N L k :=
  ContinuousMap.coeFn_toLp volume _

lemma characterL2_span_dense (N : ℕ) (L : Length) :
    (span ℂ (range (characterL2 N L))).topologicalClosure = ⊤ := by
  convert (ContinuousMap.toLp_denseRange ℂ (volume : Measure (Configuration N L)) ℂ
    (show (2:ℝ≥0∞) ≠ ∞ by norm_num)).topologicalClosure_map_submodule
      (character_span_dense N L) using 1
  rw [map_span]
  unfold characterL2
  rw [range_comp']
  rfl

end HardSphere

end

end OAI
