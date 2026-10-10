import Mathlib
import OAI.MathematicalPhysics.BFSS.StabilizerProfiles
import OAI.MathematicalPhysics.BFSS.EnergyLimits

namespace OAI

/-! Gauge covariance of Clifford symbols, fields and energy densities. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

lemma colorConjugate_coefficient (g : GaugeGroup N) (a : ColorVector N) (B : ColorIndex N) :
    M.colorConjugate (g : ColorMatrix N) a B = ∑ A, M.adjointCoefficient g A B*a A := by
  change (Matrix.trace (M.color B * ((g : ColorMatrix N)*M.colorEmbed a*
    (g : ColorMatrix N).conjTranspose))).re = _
  simp only [colorEmbed,LinearMap.coe_mk,AddHom.coe_mk,colorCombination,Matrix.mul_sum,
    Matrix.sum_mul,mul_smul_comm,smul_mul_assoc,Matrix.trace_sum,Matrix.trace_smul,
    smul_eq_mul,Complex.re_sum,adjointCoefficient,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  congr 1
  funext A
  ring

def colorClifford (β : SpinIndex) (a : ColorVector N) : Fermion N →L[ℂ] Fermion N :=
  ∑ A, (a A : ℂ) • M.theta β A

def deformedColorCoefficient (h m : ℝ) (x : Boson N) (α β : SpinIndex) : ColorVector N :=
  h • (∑ p : SpatialPair, (-BFSSGamma.pairGamma M.gamma p β α) •
    M.colorLie (spatialColor x p.1.1) (spatialColor x p.1.2)) +
  m • (∑ i : SpaceIndex, (BFSSGamma.massWeight i*(M.gamma i * BFSSGamma.massT M.gamma) β α) •
    spatialColor x i)

lemma deformedColorCoefficient_apply (h m : ℝ) (x : Boson N) (α β : SpinIndex) (A : ColorIndex N) :
    M.deformedColorCoefficient h m x α β A = M.deformedPotentialCoefficients h m x α (β,A) := by
  simp only [deformedColorCoefficient,PiLp.add_apply,PiLp.smul_apply,WithLp.ofLp_sum,Finset.sum_apply,smul_eq_mul,
    deformedPotentialCoefficients,deformedPotentialMatrix,BFSSGamma.bracketMassMatrix,
    Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,colorLie,PiLp.toLp_apply,spatialColor,
    coordinateBracket]
  congr 1
  · simp only [neg_mul, Finset.sum_neg_distrib, mul_neg]
    congr 2
    apply Finset.sum_congr rfl
    intro p _
    ring
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma deformedPotentialMultiplier_color (h m : ℝ) (x : Boson N) (α : SpinIndex) :
    M.deformedPotentialMultiplier h m x α = ∑ β, M.colorClifford β (M.deformedColorCoefficient h m x α β) := by
  simp only [deformedPotentialMultiplier,cliffordLinear,colorClifford,Fintype.sum_prod_type,
    M.deformedColorCoefficient_apply]

def principalColorCoefficient (α β : SpinIndex) (x : Boson N) : ColorVector N :=
  ∑ i : SpaceIndex, (M.gamma i α β) • spatialColor x i

lemma principalColorCoefficient_apply (α β : SpinIndex) (x : Boson N) (A : ColorIndex N) :
    M.principalColorCoefficient α β x A = M.principalCoefficients (Pi.single α 1) x (β,A) := by
  simp only [principalColorCoefficient,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    smul_eq_mul,spatialColor,M.principalCoefficients_basis]

lemma principalSymbol_color (α : SpinIndex) (x : Boson N) :
    M.principalSymbol (Pi.single α 1) x = ∑ β, M.colorClifford β (M.principalColorCoefficient α β x) := by
  simp only [principalSymbol,cliffordLinear,colorClifford,Fintype.sum_prod_type,
    M.principalColorCoefficient_apply]

namespace GaugeData
variable {M} (G : M.GaugeData)
lemma colorClifford_covariant (g : GaugeGroup N) (β : SpinIndex)
    (a : ColorVector N) (v : Fermion N) :
    G.fermion g (M.colorClifford β a v) =
      M.colorClifford β (M.colorConjugate (g : ColorMatrix N) a) (G.fermion g v) := by
  simp only [colorClifford,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    G.fermion_adjoint,Finset.smul_sum,smul_smul,M.colorConjugate_coefficient,
    Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  simp only [mul_comm (a B : ℂ) (M.adjointCoefficient g B A : ℂ)]

lemma spatialColor_boson (g : GaugeGroup N) (x : Boson N) (i : SpaceIndex) :
    spatialColor (G.boson g x) i = M.colorConjugate (g : ColorMatrix N) (spatialColor x i) := by
  apply M.colorEmbed_injective
  rw [M.colorEmbed_spatial,M.colorEmbed_conjugate _ g.prop.1,M.colorEmbed_spatial]
  exact G.boson_adjoint g x i

lemma deformedColorCoefficient_boson (g : GaugeGroup N) (h m : ℝ)
    (x : Boson N) (α β : SpinIndex) :
    M.deformedColorCoefficient h m (G.boson g x) α β =
      M.colorConjugate (g : ColorMatrix N) (M.deformedColorCoefficient h m x α β) := by
  simp only [deformedColorCoefficient,G.spatialColor_boson,M.colorConjugate_lie _ g.prop.1,
    map_add,map_smul,map_sum]

lemma deformedPotentialMultiplier_covariant (g : GaugeGroup N) (h m : ℝ)
    (x : Boson N) (α : SpinIndex) (v : Fermion N) :
    G.fermion g (M.deformedPotentialMultiplier h m x α v) =
      M.deformedPotentialMultiplier h m (G.boson g x) α (G.fermion g v) := by
  simp only [M.deformedPotentialMultiplier_color,_root_.sum_apply,map_sum,
    G.deformedColorCoefficient_boson,G.colorClifford_covariant]

lemma principalColorCoefficient_boson (g : GaugeGroup N) (x : Boson N) (α β : SpinIndex) :
    M.principalColorCoefficient α β (G.boson g x) =
      M.colorConjugate (g : ColorMatrix N) (M.principalColorCoefficient α β x) := by
  simp only [principalColorCoefficient,G.spatialColor_boson,map_sum,map_smul]

lemma principalSymbol_covariant (g : GaugeGroup N) (x : Boson N) (α : SpinIndex) (v : Fermion N) :
    G.fermion g (M.principalSymbol (Pi.single α 1) x v) =
      M.principalSymbol (Pi.single α 1) (G.boson g x) (G.fermion g v) := by
  simp only [M.principalSymbol_color,_root_.sum_apply,map_sum,
    G.principalColorCoefficient_boson,G.colorClifford_covariant]
end GaugeData
end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset
variable {N : ℕ} (M : AlgebraData N)

def kineticSkewLinear (α : SpinIndex) : Boson N →ₗ[ℝ] (Fermion N →L[ℝ] Fermion N) where
  toFun ξ := ((-Complex.I) • M.principalSymbolLinear α ξ).restrictScalars ℝ
  map_add' x y := by
    simp only [map_add, smul_add, ContinuousLinearMap.restrictScalars_add]
  map_smul' r x := by
    simp only [map_smul, RingHom.id_apply, smul_comm (-Complex.I) r,
      ContinuousLinearMap.restrictScalars_smul]

lemma kineticSkewLinear_basis (α : SpinIndex) (p : SpaceIndex × ColorIndex N) :
    M.kineticSkewLinear α (EuclideanSpace.single p 1) = M.kineticSkewSymbol α p := rfl

namespace GaugeData
variable {M} (G : M.GaugeData)
lemma kineticSkewLinear_covariant (g : GaugeGroup N) (α : SpinIndex)
    (ξ : Boson N) (v : Fermion N) :
    G.fermion g (M.kineticSkewLinear α ξ v) =
      M.kineticSkewLinear α (G.boson g ξ) (G.fermion g v) := by
  change G.fermion g ((-Complex.I) • M.principalSymbol (Pi.single α 1) ξ v) =
    (-Complex.I) • M.principalSymbol (Pi.single α 1) (G.boson g ξ) (G.fermion g v)
  rw [map_smul,G.principalSymbol_covariant]

lemma deformedRealField_derivative_covariant (g : GaugeGroup N) (h m : ℝ)
    (α : SpinIndex) (x ξ : Boson N) (v : Fermion N) :
    G.fermion g (fderiv ℝ (M.deformedRealField h m α) x ξ v) =
      fderiv ℝ (M.deformedRealField h m α) (G.boson g x) (G.boson g ξ) (G.fermion g v) := by
  let ρ : Fermion N →L[ℝ] Fermion N :=
    (G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hd := (M.deformedRealField_contDiff h m α).differentiable (by simp)
  have hl := ρ.hasFDerivAt.comp x ((hd x).hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  have hr := (((hd (G.boson g x)).hasFDerivAt.clm_apply
    (hasFDerivAt_const (G.fermion g v) (G.boson g x))).comp x (G.boson g).hasFDerivAt)
  have he : ρ ∘ (fun y => M.deformedRealField h m α y v) =
      (fun y => M.deformedRealField h m α y (G.fermion g v)) ∘ G.boson g := by
    funext y
    exact G.deformedPotentialMultiplier_covariant g h m y α v
  rw [he] at hl
  have he' := congrArg (fun L : Boson N →L[ℝ] Fermion N => L ξ) (hl.unique hr)
  simpa [ρ] using he'

lemma deformedFermionField_covariant (g : GaugeGroup N) (h m : ℝ)
    (x : Boson N) (v : Fermion N) :
    G.fermion g (M.deformedFermionField h m x v) =
      M.deformedFermionField h m (G.boson g x) (G.fermion g v) := by
  let e := EuclideanSpace.basisFun (SpaceIndex × ColorIndex N) ℝ
  have ha (α : SpinIndex) :
      ∑ p, G.fermion g (M.kineticSkewSymbol α p (fderiv ℝ (M.deformedRealField h m α) x
        (EuclideanSpace.single p 1) v)) =
      ∑ p, M.kineticSkewSymbol α p (fderiv ℝ (M.deformedRealField h m α) (G.boson g x)
        (EuclideanSpace.single p 1) (G.fermion g v)) := by
    have hb := BFSSSliceAnalytic.contraction_basis_independent e (e.map (G.boson g))
      (M.kineticSkewLinear α)
      ((fderiv ℝ (M.deformedRealField h m α) (G.boson g x)).flip (G.fermion g v)).toLinearMap
    have he (p : SpaceIndex × ColorIndex N) :
        G.fermion g (M.kineticSkewSymbol α p (fderiv ℝ (M.deformedRealField h m α) x
          (EuclideanSpace.single p 1) v)) =
        M.kineticSkewLinear α ((e.map (G.boson g)) p)
          (fderiv ℝ (M.deformedRealField h m α) (G.boson g x)
            ((e.map (G.boson g)) p) (G.fermion g v)) := by
      rw [← M.kineticSkewLinear_basis,G.kineticSkewLinear_covariant,
        G.deformedRealField_derivative_covariant]
      simp only [OrthonormalBasis.map_apply,e,EuclideanSpace.basisFun_apply]
    simp_rw [he]
    simpa only [ContinuousLinearMap.coe_coe,ContinuousLinearMap.flip_apply,e,
      EuclideanSpace.basisFun_apply,M.kineticSkewLinear_basis] using hb
  simp only [deformedFermionField,MixedEnergy.remainderField,_root_.sum_apply,
    _root_.smul_apply,mul_apply_eq_comp,map_sum,G.fermion_real_smul,ha]
end GaugeData
end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Finset
variable {N : ℕ} (M : AlgebraData N)

def bosonicDensity (h m : ℝ) (f : SmoothCore N) (x : Boson N) : ℝ :=
  M.deformedBosonicPotential h m x * ‖f x‖^2

def fermionicDensity (h m : ℝ) (f : SmoothCore N) (x : Boson N) : ℝ :=
  inner ℝ (f x) (M.deformedFermionField h m x (f x))

lemma bosonicDensity_continuous (h m : ℝ) (f : SmoothCore N) :
    Continuous (M.bosonicDensity h m f) := by
  have he : M.bosonicDensity h m f = fun x =>
      (1/16 : ℝ)*∑ α : SpinIndex, ‖M.deformedPotentialMultiplier h m x α (f x)‖^2 :=
    funext (fun x => (M.deformed_potential_average h m x (f x)).symm)
  rw [he]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro α _
  exact (((M.deformedPotentialMultiplier_contDiff h m α).continuous.clm_apply f.continuous).norm.pow 2)

lemma fermionicDensity_continuous (h m : ℝ) (f : SmoothCore N) :
    Continuous (M.fermionicDensity h m f) := by
  exact f.continuous.inner ((M.deformedFermionField_continuous h m).clm_apply f.continuous)

lemma bosonicDensity_compactSupport (h m : ℝ) (f : SmoothCore N) :
    HasCompactSupport (M.bosonicDensity h m f) :=
  (BFSSNormalMeasure.square_compact _ f.hasCompactSupport).mul_left

lemma fermionicDensity_compactSupport (h m : ℝ) (f : SmoothCore N) :
    HasCompactSupport (M.fermionicDensity h m f) := by
  have hf := f.hasCompactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  filter_upwards [hf] with x hx
  change f x = 0 at hx
  change inner ℝ (f x) (M.deformedFermionField h m x (f x)) = 0
  rw [hx,inner_zero_left]

namespace GaugeData
variable {M} (G : M.GaugeData)
lemma fermion_real_inner (g : GaugeGroup N) (v w : Fermion N) :
    inner ℝ (G.fermion g v) (G.fermion g w) = inner ℝ v w := by
  simpa only [PiLp.inner_apply,real_inner_eq_re_inner,Complex.re_sum,RCLike.re_to_complex] using
    congrArg Complex.re ((G.fermion g).inner_map_map v w)

lemma invariantCore_bosonicDensity (f : G.invariantCore) (g : GaugeGroup N) (h m : ℝ) (x : Boson N) :
    M.bosonicDensity h m f.val (G.boson g x) = M.bosonicDensity h m f.val x := by
  unfold bosonicDensity
  rw [←M.deformed_potential_average,←M.deformed_potential_average,G.invariantCore_equivariant]
  simp_rw [←G.deformedPotentialMultiplier_covariant,(G.fermion g).norm_map]

lemma invariantCore_fermionicDensity (f : G.invariantCore) (g : GaugeGroup N) (h m : ℝ) (x : Boson N) :
    M.fermionicDensity h m f.val (G.boson g x) = M.fermionicDensity h m f.val x := by
  unfold fermionicDensity
  rw [G.invariantCore_equivariant,←G.deformedFermionField_covariant,G.fermion_real_inner]

lemma invariantCore_bosonicDensity_unitary (hN : 2 ≤ N) (f : G.invariantCore)
    (U : unitary (ColorMatrix N)) (h m : ℝ) (x : Boson N) :
    M.bosonicDensity h m f.val (M.gaugeAction U x) = M.bosonicDensity h m f.val x := by
  obtain ⟨g,hg⟩ := G.unitary_boson_exists hN U
  rw [←hg x]
  exact G.invariantCore_bosonicDensity f g h m x

lemma invariantCore_fermionicDensity_unitary (hN : 2 ≤ N) (f : G.invariantCore)
    (U : unitary (ColorMatrix N)) (h m : ℝ) (x : Boson N) :
    M.fermionicDensity h m f.val (M.gaugeAction U x) = M.fermionicDensity h m f.val x := by
  obtain ⟨g,hg⟩ := G.unitary_boson_exists hN U
  rw [←hg x]
  exact G.invariantCore_fermionicDensity f g h m x

end GaugeData
end
end BFSSQuantum.AlgebraData

end OAI
