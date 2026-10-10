import OAI.Probability.ClassicalON.ModeBounds

namespace OAI

universe uE uK uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
noncomputable section
open scoped BigOperators
namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]

def weighted (J u : E → K) : K := ∑ e, J e * u e

@[simp] theorem weighted_add (J u v : E → K) :
    weighted J (u+v) = weighted J u + weighted J v := by
  simp [weighted, mul_add, Finset.sum_add_distrib]

@[simp] theorem weighted_neg (J u : E → K) : weighted J (-u) = -weighted J u := by
  simp [weighted]

structure Coeffs (E : Type uE) (K : Type uK) where
  a : E → K
  b : E → K
  aa : E → K
  ab : E → K
  bb : E → K
  aab : E → K
  abb : E → K
  aabb : E → K

def four (J : Coeffs E K) (u v w z : E → K) : K :=
  weighted J.a u * weighted J.b v * weighted J.a w * weighted J.b z +
  weighted J.ab (u*v) * weighted J.a w * weighted J.b z +
  weighted J.aa (u*w) * weighted J.b v * weighted J.b z +
  weighted J.ab (u*z) * weighted J.b v * weighted J.a w +
  weighted J.ab (v*w) * weighted J.a u * weighted J.b z +
  weighted J.bb (v*z) * weighted J.a u * weighted J.a w +
  weighted J.ab (w*z) * weighted J.a u * weighted J.b v +
  weighted J.ab (u*v) * weighted J.ab (w*z) +
  weighted J.aa (u*w) * weighted J.bb (v*z) +
  weighted J.ab (u*z) * weighted J.ab (v*w) +
  weighted J.aab (u*v*w) * weighted J.b z +
  weighted J.abb (u*v*z) * weighted J.a w +
  weighted J.aab (u*w*z) * weighted J.b v +
  weighted J.abb (v*w*z) * weighted J.a u +
  weighted J.aabb (u*v*w*z)

theorem four_add_first (J : Coeffs E K) (u u' v w z : E → K) :
    four J (u+u') v w z = four J u v w z + four J u' v w z := by
  simp only [four, add_mul, weighted_add]
  ring

theorem four_add_second (J : Coeffs E K) (u v v' w z : E → K) :
    four J u (v+v') w z = four J u v w z + four J u v' w z := by
  simp only [four, add_mul, mul_add, weighted_add]
  ring

theorem four_swap_first_third (J : Coeffs E K) (u v w z : E → K) :
    four J u v w z = four J w v u z := by
  unfold four
  simp only [mul_comm, mul_left_comm, mul_assoc]
  ring

theorem four_swap_second_fourth (J : Coeffs E K) (u v w z : E → K) :
    four J u v w z = four J u z w v := by
  unfold four
  simp only [mul_comm, mul_left_comm, mul_assoc]
  ring

end MixedAlgebra

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]

theorem four_add_third (J : Coeffs E K) (u v w w' z : E → K) :
    four J u v (w+w') z = four J u v w z + four J u v w' z := by
  rw [four_swap_first_third, four_add_first, four_swap_first_third J w,
    four_swap_first_third J w']

theorem four_add_fourth (J : Coeffs E K) (u v w z z' : E → K) :
    four J u v w (z+z') = four J u v w z + four J u v w z' := by
  rw [four_swap_second_fourth, four_add_second, four_swap_second_fourth J u z,
    four_swap_second_fourth J u z']

theorem four_polarize_a (J : Coeffs E K) (u w v : E → K) :
    four J (u+w) v (u+w) v = four J u v u v + 2 * four J u v w v + four J w v w v := by
  rw [four_add_first, four_add_third, four_add_third, four_swap_first_third J w v u]
  ring

theorem four_polarize_b (J : Coeffs E K) (u w v z : E → K) :
    four J u (v+z) w (v+z) = four J u v w v + 2 * four J u v w z + four J u z w z := by
  rw [four_add_second, four_add_fourth, four_add_fourth, four_swap_second_fourth J u z w v]
  ring

end MixedAlgebra

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]

theorem four_diagonal (J : Coeffs E K) (u v : E → K) :
    four J u v u v =
      (weighted J.a u)^2 * (weighted J.b v)^2 +
      weighted J.aa (u*u) * (weighted J.b v)^2 +
      weighted J.bb (v*v) * (weighted J.a u)^2 +
      4 * weighted J.ab (u*v) * weighted J.a u * weighted J.b v +
      weighted J.aa (u*u) * weighted J.bb (v*v) +
      2 * (weighted J.ab (u*v))^2 +
      2 * weighted J.aab (u*u*v) * weighted J.b v +
      2 * weighted J.abb (u*v*v) * weighted J.a u +
      weighted J.aabb (u*u*v*v) := by
  simp only [four, mul_comm, mul_left_comm]
  ring

end MixedAlgebra

def bell4 (x y z w : ℝ) : ℝ := w+4*x*z+3*y^2+6*x^2*y+x^4

theorem bell4_even (a b aa ab bb aaa aab abb bbb p q aaaa aabb bbbb : ℝ)
    (h : p+q = 2*aaaa+12*aabb+2*bbbb) :
    bell4 (a+b) (aa+2*ab+bb) (aaa+3*aab+3*abb+bbb) p +
      bell4 (a-b) (aa-2*ab+bb) (aaa-3*aab+3*abb-bbb) q -
      2*bell4 a aa aaa aaaa - 2*bell4 b bb bbb bbbb =
      12*(a^2*b^2+aa*b^2+bb*a^2+4*ab*a*b+aa*bb+2*ab^2+
        2*aab*b+2*abb*a+aabb) := by
  unfold bell4
  nlinarith only [h]

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem fourthResponse_plane_even (S : SpinSystem 3 V E) (f g : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0) :
    S.fourthResponse (S.planarGradient f g) +
      S.fourthResponse (S.planarGradient f (-g)) =
        6 * S.secondAxisResponse (S.crossForm f g) (S.crossForm f g) := by
  have hsk (f g : V → ℝ) (x : V) :
      planeOperator (f x) (g x) ∈ skewAdjoint (SpinOperator 3) := by
    rw [planeOperator_eq]
    exact (skewAdjoint _).add_mem (skewAdjoint.smul_mem _ axisA_skew)
      (skewAdjoint.smul_mem _ axisB_skew)
  have hp : ∀ x s, S.pin x = some s → planeOperator (f x) (g x) = 0 := by
    intro x s hs
    rw [hf x s hs, hg x s hs, planeOperator_eq]
    simp only [zero_smul ℝ axisA, zero_smul ℝ axisB, add_zero]
  have hm : ∀ x s, S.pin x = some s → planeOperator (f x) ((-g) x) = 0 := by
    intro x s hs
    rw [Pi.neg_apply, hg x s hs, neg_zero, hf x s hs, planeOperator_eq]
    simp only [zero_smul ℝ axisA, zero_smul ℝ axisB, add_zero]
  change S.fourthResponse (fun e => planeOperator (f (S.right e)) (g (S.right e)) -
    planeOperator (f (S.left e)) (g (S.left e))) + S.fourthResponse (fun e =>
      planeOperator (f (S.right e)) ((-g) (S.right e)) -
      planeOperator (f (S.left e)) ((-g) (S.left e))) = _
  rw [S.fourthResponse_gauge _ (hsk f g) hp,
    S.fourthResponse_gauge _ (hsk f (-g)) hm]
  let w := S.crossForm f g
  have he (σ : V → Spin 3) :
      S.gaugeEnergy (fun x => planeOperator (f x) (g x)) 4 0 σ +
      S.gaugeEnergy (fun x => planeOperator (f x) ((-g) x)) 4 0 σ =
        S.energy (fun e => (6*(w e)^2) • axisC^2) σ := by
    rw [gaugeEnergy, gaugeEnergy, ← S.energy_add]
    apply congrArg (fun K => S.energy K σ)
    funext e
    have ht := gaugeJet_plane_four_even (f (S.left e)) (g (S.left e))
      (f (S.right e)) (g (S.right e))
    dsimp only [Pi.add_apply, Pi.neg_apply, w, crossForm]
    with_reducible exact ht
  have hcm : (fun e =>
      planeOperator (f (S.left e)) ((-g) (S.left e)) *
        planeOperator (f (S.right e)) ((-g) (S.right e)) -
      planeOperator (f (S.right e)) ((-g) (S.right e)) *
        planeOperator (f (S.left e)) ((-g) (S.left e))) = -(fun e => w e • axisC) := by
    funext e
    rw [planeOperator_commutator]
    change (f (S.left e) * (-g) (S.right e) - (-g) (S.left e) * f (S.right e)) • axisC = -(w e • axisC)
    rw [← neg_smul (w e) axisC]
    congr 1
    dsimp only [w, crossForm, Pi.neg_apply]
    ring
  have hcp : (fun e =>
      planeOperator (f (S.left e)) (g (S.left e)) *
        planeOperator (f (S.right e)) (g (S.right e)) -
      planeOperator (f (S.right e)) (g (S.right e)) *
        planeOperator (f (S.left e)) (g (S.left e))) = (fun e => w e • axisC) := by
    funext e
    exact planeOperator_commutator _ _ _ _
  rw [hcp, hcm]
  simp only [S.energy_neg, neg_sq]
  have hc (F : V → SpinOperator 3) : Continuous (fun σ =>
      S.gaugeEnergy F 4 0 σ + 3 * (S.energy (fun e => w e • axisC) σ)^2) :=
    ((S.continuous_gaugeEnergy F 4).comp (continuous_const.prodMk continuous_id)).add
      (continuous_const.mul ((S.continuous_energy _).pow 2))
  rw [← S.average_add (hc _) (hc _)]
  have hpoint : (fun σ =>
      (S.gaugeEnergy (fun x => planeOperator (f x) (g x)) 4 0 σ +
        3 * (S.energy (fun e => w e • axisC) σ)^2) +
      (S.gaugeEnergy (fun x => planeOperator (f x) ((-g) x)) 4 0 σ +
        3 * (S.energy (fun e => w e • axisC) σ)^2)) =
      (fun σ => 6 * (S.energy (fun e => (w e*w e) • axisC^2) σ +
        S.energy (fun e => w e • axisC) σ * S.energy (fun e => w e • axisC) σ)) := by
    funext σ
    have ht := he σ
    have hsc : (fun e => (6*(w e)^2) • axisC^2) =
        (6 : ℝ) • (fun e => (w e*w e) • axisC^2) := by
      funext e
      simp only [Pi.smul_apply, smul_smul, pow_two]
    rw [hsc, S.energy_smul] at ht
    nlinarith
  change S.average (fun σ =>
      (S.gaugeEnergy (fun x => planeOperator (f x) (g x)) 4 0 σ +
        3 * (S.energy (fun e => w e • axisC) σ)^2) +
      (S.gaugeEnergy (fun x => planeOperator (f x) ((-g) x)) 4 0 σ +
        3 * (S.energy (fun e => w e • axisC) σ)^2)) = _
  rw [hpoint, S.average_mul_const]
  rfl

variable {n : ℕ}

theorem fourthResponse_axisGradient [NeZero n] (S : SpinSystem n V E)
    (g : SpinOperator n) (hg : g ∈ skewAdjoint (SpinOperator n)) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.fourthResponse (S.axisGradient f g) = 0 := by
  let A := S.axisGradient f g
  have hZ : (fun t => S.Z (fun e => NormedSpace.exp (t • A e))) =
      (fun _ : ℝ => S.Z (fun _ => 1)) := funext (S.Z_gradient_line g hg f hP)
  have hfirst : (fun t => ∫ σ, S.firstWeight A t σ ∂S.reference) = (fun _ : ℝ => 0) := by
    funext t
    have h := S.hasDerivAt_twistZ A t
    rw [hZ] at h
    exact h.unique (hasDerivAt_const t _)
  have hsecond : (fun t => ∫ σ, S.secondWeight A t σ ∂S.reference) = (fun _ : ℝ => 0) := by
    funext t
    have h := S.hasDerivAt_firstVariation A t
    rw [hfirst] at h
    exact h.unique (hasDerivAt_const t 0)
  have hthird : (fun t => ∫ σ, S.thirdWeight A t σ ∂S.reference) = (fun _ : ℝ => 0) := by
    funext t
    have h := S.hasDerivAt_secondVariation A t
    rw [hsecond] at h
    exact h.unique (hasDerivAt_const t 0)
  have hfourth : (∫ σ, S.fourthWeight A 0 σ ∂S.reference) = 0 := by
    have h := S.hasDerivAt_thirdVariation A 0
    rw [hthird] at h
    exact h.unique (hasDerivAt_const 0 0)
  rw [S.fourthResponse_integral, hfourth, zero_div]

def localCoefficient (S : SpinSystem n V E) (M : SpinOperator n)
    (σ : V → Spin n) (e : E) : ℝ :=
  S.strength e * ⟪(σ (S.left e)).val, M (σ (S.right e)).val⟫_ℝ

omit [Fintype V] in
theorem energy_weighted (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℝ) (σ : V → Spin n) :
    S.energy (fun e => u e • M) σ = MixedAlgebra.weighted (S.localCoefficient M σ) u := by
  unfold energy MixedAlgebra.weighted localCoefficient
  apply Finset.sum_congr rfl
  intro e _
  simp only [smul_apply, real_inner_smul_right]
  ring

def mixedCoefficients (S : SpinSystem 3 V E) (σ : V → Spin 3) : MixedAlgebra.Coeffs E ℝ where
  a := S.localCoefficient axisA σ
  b := S.localCoefficient axisB σ
  aa := S.localCoefficient (axisA^2) σ
  ab := S.localCoefficient mixedAB σ
  bb := S.localCoefficient (axisB^2) σ
  aab := S.localCoefficient mixedAAB σ
  abb := S.localCoefficient mixedABB σ
  aabb := S.localCoefficient mixedAABB σ

omit [Fintype V] in
def differential (S : SpinSystem n V E) {K : Type uK} [Sub K] (f : V → K) : E → K :=
  fun e => f (S.right e) - f (S.left e)

omit [Fintype V] [Fintype E] in
theorem planarGradient_eq (S : SpinSystem 3 V E) (f g : V → ℝ) :
    S.planarGradient f g = fun e => planeOperator (S.differential f e) (S.differential g e) := by
  funext e
  simp only [planarGradient, planeOperator_eq, differential]
  module

omit [Fintype V] in
theorem planeEnergy_one (S : SpinSystem 3 V E) (u v : E → ℝ) (σ : V → Spin 3) :
    S.energy (fun e => planeOperator (u e) (v e)) σ =
      MixedAlgebra.weighted (S.mixedCoefficients σ).a u +
      MixedAlgebra.weighted (S.mixedCoefficients σ).b v := by
  simp only [planeOperator_eq]
  change S.energy ((fun e => u e • axisA) + (fun e => v e • axisB)) σ = _
  rw [S.energy_add, S.energy_weighted, S.energy_weighted]
  rfl

end ClassicalON.SpinSystem

end
end

end OAI
