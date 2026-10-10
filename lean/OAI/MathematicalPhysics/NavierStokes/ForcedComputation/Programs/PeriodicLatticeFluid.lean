import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicLatticeTransform

namespace OAI

/-! Navier--Stokes transport for the transverse lattice transformation.
The vanishing first derivative makes the nonisometric scaling harmless. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace PeriodicLattice.RapidTorus
open TorusCalculus Quantitative

theorem transformedField_laplacian {F : VectorField}
    (hF : ContDiff ℝ ∞ (lifted F)) :
    laplacian (transformedField F) = transformedField (laplacian F) := by
  funext t q
  simp only [laplacian, transformedField_spaceD hF,
    transformedField_spaceD (contDiff_spaceD hF _), transformedField, shiftedField,
    map_sum]

theorem transformedField_timeD {F : VectorField}
    (hF : ContDiff ℝ ∞ (lifted F)) (t : ℝ) (ht : 0 ≤ t) (q : Torus) :
    timeD (transformedField F) t q = transverseLinear (timeD F t (shift q)) := by
  rw [timeD_eq_fullTimeD (transformedField_smooth hF) ht,
    transformedField_fullTimeD hF, timeD_eq_fullTimeD hF ht]
  rfl

theorem transformedField_advection {U : VectorField}
    (hU : ContDiff ℝ ∞ (lifted U)) (hzero : spaceD 0 U = 0) :
    advection (transformedField U) = transformedField (advection U) := by
  funext t q
  simp only [advection, Fin.sum_univ_three,
    transformedField_spaceD hU, transformedField, shiftedField,
    transverseLinear_apply, Fin.isValue, reduceIte, hzero, Pi.zero_apply,
    map_zero, smul_zero, zero_add, map_add, map_smul]
  norm_num

theorem transformedField_divergence {U : VectorField}
    (hU : ContDiff ℝ ∞ (lifted U)) (hzero : spaceD 0 U = 0) (t : ℝ) (q : Torus) :
    divergence (transformedField U) t q = divergence U t (shift q) := by
  have hdiv {V : VectorField} (hV : ContDiff ℝ ∞ (lifted V)) (s : ℝ) (x : Torus) :
      divergence V s x = ∑ i : Fin 3, spaceD i V s x i := by
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    exact (congrFun₂ (spaceD_component_eq hV i i) s x).symm
  rw [hdiv (transformedField_smooth hU), hdiv hU]
  simp only [transformedField_spaceD hU, transformedField, shiftedField,
    Fin.sum_univ_three, transverseLinear_apply, Fin.isValue, reduceIte,
    hzero, Pi.zero_apply, PiLp.zero_apply, mul_zero]
  norm_num

theorem shiftedField_gradient {p : ScalarField}
    (hp : ContDiff ℝ ∞ (lifted p)) (hz : spaceD 0 p = 0) :
    gradient (shiftedField p) = transformedField (gradient p) := by
  funext t q
  ext i
  change spaceD i (shiftedField p) t q = transverseLinear (gradient p t (shift q)) i
  rw [shiftedField_spaceD hp, transverseLinear_apply]
  change spaceD i p t (shift q) =
    if i = 0 then -(1 / 2 : ℝ) * spaceD i p t (shift q) else spaceD i p t (shift q)
  split_ifs with hi
  · subst i
    rw [hz]
    simp
  · rfl

theorem transformed_classical_equations {ν : ℝ} {g U : VectorField} {p : ScalarField}
    (hU : ContDiff ℝ ∞ (lifted U)) (hp : ContDiff ℝ ∞ (lifted p))
    (hzU : spaceD 0 U = 0) (hzp : spaceD 0 p = 0)
    (hNS : NavierStokes ν g U p) :
    NavierStokes ν (transformedField g) (transformedField U) (shiftedField p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht q
    rw [transformedField_timeD hU t ht,
      congrFun₂ (transformedField_advection hU hzU) t q,
      congrFun₂ (transformedField_laplacian hU) t q,
      congrFun₂ (shiftedField_gradient hp hzp) t q]
    simpa only [transformedField, shiftedField, map_add, map_neg, map_smul] using
      congrArg transverseLinear (hNS.1 t ht (shift q))
  · intro t ht q
    rw [transformedField_divergence hU hzU]
    exact hNS.2.1 t ht (shift q)
  · intro q
    change transverseLinear (U 0 (shift q)) = 0
    rw [hNS.2.2, map_zero]

theorem velocity_firstDerivative (d : Input) : spaceD 0 (FluidLift.velocity d) = 0 := by
  funext t q
  obtain ⟨x, rfl⟩ := mk_surjective q
  rw [spaceD_cover]
  have he : (fun s : ℝ => spaceLift (FluidLift.velocity d) t
      (x + EuclideanSpace.single 0 s)) = fun _ => FluidLift.velocity d t (torusMk x) := by
    funext s
    simp only [spaceLift, FluidLift.velocity_cover]
    congr 1
    simp [PiLp.add_apply]
  rw [he]
  exact deriv_const _ _

theorem potential_firstDerivative (d : Input) : spaceD 0 (FluidLift.potential d) = 0 := by
  funext t q
  obtain ⟨x, rfl⟩ := mk_surjective q
  rw [spaceD_cover]
  have he : (fun s : ℝ => spaceLift (FluidLift.potential d) t
      (x + EuclideanSpace.single 0 s)) = fun _ => FluidLift.potential d t (torusMk x) := by
    funext s
    simp only [spaceLift, FluidLift.potential, Pi.add_apply,
      PeriodicInverse.horizontal_cover, FluidLift.pressureOsc_cover]
    norm_num [PiLp.add_apply, PiLp.single_apply]
  rw [he]
  exact deriv_const _ _

theorem shiftedField_meanZero {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {F : Field A} (hm : MeanZero F) : MeanZero (shiftedField F) := by
  intro t ht
  change (∫ q, F t (q + torusMk shiftVector) ∂torusVolume) = 0
  rw [integral_add_right_eq_self, hm t ht]

theorem algebra_firstDerivative {F : ScalarField} (hF : RapidCalculus.Algebra F) :
    spaceD 0 F = 0 := by
  induction hF with
  | zero => exact Residual.spaceD_zero 0
  | tensor F f h hf hh he => exact RapidCalculus.tensor_spaceD_zero he
  | @add F G hF hG ihF ihG =>
      rw [spaceD_add_eq hF.smooth hG.smooth, ihF, ihG, add_zero]
  | @mul F G hF hG ihF ihG =>
      funext t q
      change spaceD 0 (fun t q => F t q • G t q) t q = 0
      rw [spaceD_smul hF.smooth hG.smooth]
      change spaceD 0 F t q * G t q + F t q * spaceD 0 G t q = 0
      rw [ihF, ihG]
      simp
  | @scale c F hF ihF =>
      rw [spaceD_scale hF.smooth, ihF, smul_zero]

theorem vectorAlgebra_firstDerivative {F : VectorField}
    (hF : RapidCalculus.VectorAlgebra F) (hs : ContDiff ℝ ∞ (lifted F)) :
    spaceD 0 F = 0 := by
  funext t q
  ext i
  rw [congrFun₂ (spaceD_component_eq hs 0 i) t q, algebra_firstDerivative (hF i)]
  rfl

theorem transformed_solenoidalForce (ν : ℝ) (d : Input) (hd : d.WellFormed) :
    Solenoidal (transformedField (FluidLift.solenoidalForce ν d)) := by
  have hF := FluidLift.solenoidalForce_contDiff ν d
  have hz := vectorAlgebra_firstDerivative (FluidLift.solenoidalForce_algebra ν d hd) hF
  intro t ht q
  rw [transformedField_divergence hF hz]
  exact FluidLift.solenoidalForce_solenoidal ν d t ht (shift q)

theorem transformed_classical_solution (ν : ℝ) (d : Input) :
    ClassicalSolution ν (transformedField (FluidLift.solenoidalForce ν d))
      (transformedField (FluidLift.velocity d)) (-shiftedField (FluidLift.potential d)) := by
  have hu := FluidLift.velocity_contDiff d
  have hp := FluidLift.potential_contDiff d
  have hn' : spaceD 0 (-FluidLift.potential d) = 0 := by
    rw [← neg_one_smul ℝ (FluidLift.potential d), spaceD_scale hp, potential_firstDerivative, smul_zero]
  have hneg : ContDiff ℝ ∞ (lifted (-FluidLift.potential d)) := hp.neg
  have hNS := transformed_classical_equations (p := -FluidLift.potential d)
    hu hneg (velocity_firstDerivative d) hn'
    (FluidLift.solenoidalForce_equations ν d)
  have hm : MeanZero (-shiftedField (FluidLift.potential d)) := by
    intro t ht
    change (∫ q, -shiftedField (FluidLift.potential d) t q ∂torusVolume) = 0
    rw [integral_neg, shiftedField_meanZero (FluidLift.potential_meanZero d) t ht, neg_zero]
  exact classical_of_smooth_pressure (transformedField_smooth hu) (shiftedField_smooth hp).neg hm hNS

end PeriodicLattice.RapidTorus

end

end OAI
