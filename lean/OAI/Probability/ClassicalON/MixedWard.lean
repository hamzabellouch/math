import OAI.Probability.ClassicalON.RotationWork

namespace OAI

universe uE uK uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]
theorem weighted_const_mul (J u : E → K) (r : K) :
    weighted J (fun e => r * u e) = r * weighted J u := by
  simp only [weighted, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring
end MixedAlgebra

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem planeEnergy_two (S : SpinSystem 3 V E) (u v : E → ℝ) (σ : V → Spin 3) :
    S.energy (fun e => planeOperator (u e) (v e)^2) σ =
      MixedAlgebra.weighted (S.mixedCoefficients σ).aa (u*u) +
      2 * MixedAlgebra.weighted (S.mixedCoefficients σ).ab (u*v) +
      MixedAlgebra.weighted (S.mixedCoefficients σ).bb (v*v) := by
  simp only [planeOperator_square]
  change S.energy (((fun e => u e^2 • axisA^2) +
    (fun e => (2*u e*v e) • mixedAB)) + (fun e => v e^2 • axisB^2)) σ = _
  rw [S.energy_add, S.energy_add, S.energy_weighted, S.energy_weighted, S.energy_weighted]
  simp only [mixedCoefficients, pow_two, mul_assoc]
  rw [MixedAlgebra.weighted_const_mul]
  rfl

omit [Fintype V] in
theorem planeEnergy_three (S : SpinSystem 3 V E) (u v : E → ℝ) (σ : V → Spin 3) :
    S.energy (fun e => planeOperator (u e) (v e)^3) σ =
      MixedAlgebra.weighted (S.localCoefficient (axisA^3) σ) (u^3) +
      3 * MixedAlgebra.weighted (S.mixedCoefficients σ).aab (u*u*v) +
      3 * MixedAlgebra.weighted (S.mixedCoefficients σ).abb (u*v*v) +
      MixedAlgebra.weighted (S.localCoefficient (axisB^3) σ) (v^3) := by
  simp only [planeOperator_cube]
  change S.energy ((((fun e => u e^3 • axisA^3) +
    (fun e => (3*u e^2*v e) • mixedAAB)) +
    (fun e => (3*u e*v e^2) • mixedABB)) + (fun e => v e^3 • axisB^3)) σ = _
  rw [S.energy_add, S.energy_add, S.energy_add,
    S.energy_weighted, S.energy_weighted, S.energy_weighted, S.energy_weighted]
  simp only [mixedCoefficients, pow_two, mul_assoc]
  rw [MixedAlgebra.weighted_const_mul, MixedAlgebra.weighted_const_mul]
  rfl

omit [Fintype V] in
theorem planeEnergy_four_even (S : SpinSystem 3 V E) (u v : E → ℝ) (σ : V → Spin 3) :
    S.energy (fun e => planeOperator (u e) (v e)^4) σ +
      S.energy (fun e => planeOperator (u e) (-v e)^4) σ =
      2 * MixedAlgebra.weighted (S.localCoefficient (axisA^4) σ) (u^4) +
      12 * MixedAlgebra.weighted (S.mixedCoefficients σ).aabb (u*u*v*v) +
      2 * MixedAlgebra.weighted (S.localCoefficient (axisB^4) σ) (v^4) := by
  rw [← S.energy_add]
  have hp : (fun e => planeOperator (u e) (v e)^4) +
      (fun e => planeOperator (u e) (-v e)^4) =
      ((fun e => (2*u e^4) • axisA^4) +
        (fun e => (12*u e^2*v e^2) • mixedAABB)) +
        (fun e => (2*v e^4) • axisB^4) := by
    funext e
    exact planeOperator_four_even (u e) (v e)
  rw [hp, S.energy_add, S.energy_add, S.energy_weighted, S.energy_weighted, S.energy_weighted]
  simp only [mixedCoefficients, pow_two, mul_assoc]
  rw [MixedAlgebra.weighted_const_mul, MixedAlgebra.weighted_const_mul,
    MixedAlgebra.weighted_const_mul]
  rfl

variable {n : ℕ}

omit [Fintype V] [Fintype E] in
theorem operator_smul_pow (r : ℝ) (M : SpinOperator n) (k : ℕ) :
    (r • M)^k = r^k • M^k := by
  induction k with
  | zero => simp only [pow_zero, one_smul]
  | succ k ih =>
    rw [pow_succ, ih, Algebra.smul_mul_assoc (r^k) (M^k) (r • M),
      Algebra.mul_smul_comm r (M^k) M, smul_smul (r^k) r (M^k*M),
      ← pow_succ, ← pow_succ]

omit [Fintype V] in
theorem energy_scaled_power (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℝ) (k : ℕ) (σ : V → Spin n) :
    S.energy (fun e => (u e • M)^k) σ =
      MixedAlgebra.weighted (S.localCoefficient (M^k) σ) (u^k) := by
  have hp : (fun e => (u e • M)^k) = (fun e => (u e)^k • M^k) :=
    funext (fun e => operator_smul_pow (u e) M k)
  rw [hp]
  exact S.energy_weighted (M^k) (u^k) σ

def averageLinear [NeZero n] (S : SpinSystem n V E) : C((V → Spin n), ℝ) →ₗ[ℝ] ℝ where
  toFun f := S.average f
  map_add' f g := S.average_add f.continuous g.continuous
  map_smul' r f := S.average_mul_const r f

@[simp] theorem averageLinear_apply [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℝ)) : S.averageLinear f = S.average f := rfl

attribute [local fun_prop] continuous_energy

omit [Fintype V] in
theorem continuous_fourthPolynomial (S : SpinSystem n V E) (A : E → SpinOperator n) :
    Continuous (fun σ => fourthPolynomial (fun k => S.energy (fun e => A e^k) σ)) := by
  unfold fourthPolynomial
  fun_prop

def fourthObservable (S : SpinSystem n V E) (A : E → SpinOperator n) : C((V → Spin n), ℝ) :=
  ⟨_, S.continuous_fourthPolynomial A⟩

@[simp] theorem average_fourthObservable [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) : S.averageLinear (S.fourthObservable A) = S.fourthResponse A := rfl

omit [Fintype V] in
@[fun_prop] theorem continuous_weighted_coefficient (S : SpinSystem n V E)
    (M : SpinOperator n) (u : E → ℝ) :
    Continuous (fun σ => MixedAlgebra.weighted (S.localCoefficient M σ) u) := by
  have he : (fun σ => MixedAlgebra.weighted (S.localCoefficient M σ) u) =
      S.energy (fun e => u e • M) := by
    funext σ
    exact (S.energy_weighted M u σ).symm
  rw [he]
  exact S.continuous_energy _

omit [Fintype V] in
@[fun_prop] theorem continuous_mixedPolynomial (S : SpinSystem 3 V E)
    (u v w z : E → ℝ) :
    Continuous (fun σ => MixedAlgebra.four (S.mixedCoefficients σ) u v w z) := by
  simp only [MixedAlgebra.four, mixedCoefficients]
  fun_prop

def mixedObservable (S : SpinSystem 3 V E) (u v w z : E → ℝ) : C((V → Spin 3), ℝ) :=
  ⟨_, S.continuous_mixedPolynomial u v w z⟩

def mixedResponse (S : SpinSystem 3 V E) (u v w z : E → ℝ) : ℝ :=
  S.averageLinear (S.mixedObservable u v w z)

omit [Fintype V] in
theorem fourthObservable_even (S : SpinSystem 3 V E) (u v : E → ℝ) :
    S.fourthObservable (fun e => planeOperator (u e) (v e)) +
      S.fourthObservable (fun e => planeOperator (u e) (-v e)) -
      (2:ℝ) • S.fourthObservable (fun e => u e • axisA) -
      (2:ℝ) • S.fourthObservable (fun e => v e • axisB) =
      (12:ℝ) • S.mixedObservable u v u v := by
  ext σ
  change fourthPolynomial (fun k => S.energy (fun e => planeOperator (u e) (v e)^k) σ) +
    fourthPolynomial (fun k => S.energy (fun e => planeOperator (u e) (-v e)^k) σ) -
    2 * fourthPolynomial (fun k => S.energy (fun e => (u e • axisA)^k) σ) -
    2 * fourthPolynomial (fun k => S.energy (fun e => (v e • axisB)^k) σ) =
    12 * MixedAlgebra.four (S.mixedCoefficients σ) u v u v
  simp only [fourthPolynomial, pow_one, planeEnergy_one, planeEnergy_two,
    planeEnergy_three, energy_scaled_power, energy_weighted]
  have hn : (fun e => -v e) = -v := rfl
  have hv3 : (-v)^3 = -(v^3) := by ring
  simp only [hn, hv3, neg_mul, mul_neg, neg_neg, MixedAlgebra.weighted_neg]
  have hp := S.planeEnergy_four_even u v σ
  have hb := bell4_even
    (MixedAlgebra.weighted (S.mixedCoefficients σ).a u)
    (MixedAlgebra.weighted (S.mixedCoefficients σ).b v)
    (MixedAlgebra.weighted (S.mixedCoefficients σ).aa (u*u))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).ab (u*v))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).bb (v*v))
    (MixedAlgebra.weighted (S.localCoefficient (axisA^3) σ) (u^3))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).aab (u*u*v))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).abb (u*v*v))
    (MixedAlgebra.weighted (S.localCoefficient (axisB^3) σ) (v^3))
    (S.energy (fun e => planeOperator (u e) (v e)^4) σ)
    (S.energy (fun e => planeOperator (u e) (-v e)^4) σ)
    (MixedAlgebra.weighted (S.localCoefficient (axisA^4) σ) (u^4))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).aabb (u*u*v*v))
    (MixedAlgebra.weighted (S.localCoefficient (axisB^4) σ) (v^4)) hp
  rw [MixedAlgebra.four_diagonal]
  simp only [bell4, mixedCoefficients] at hb ⊢
  convert hb using 1
  ring_nf

theorem mixedResponse_diagonal (S : SpinSystem 3 V E) (f g : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0) :
    2 * S.mixedResponse (S.differential f) (S.differential g)
      (S.differential f) (S.differential g) =
      S.secondAxisResponse (S.crossForm f g) (S.crossForm f g) := by
  have h := congrArg S.averageLinear
    (S.fourthObservable_even (S.differential f) (S.differential g))
  simp only [map_sub, map_add, map_smul, smul_eq_mul,
    average_fourthObservable] at h
  have hp := S.fourthResponse_plane_even f g hf hg
  have ha := S.fourthResponse_axisGradient axisA axisA_skew f hf
  have hb := S.fourthResponse_axisGradient axisB axisB_skew g hg
  rw [S.planarGradient_eq, S.planarGradient_eq] at hp
  have hm : S.differential (-g) = fun e => -S.differential g e := by
    funext e
    simp only [differential, Pi.neg_apply]
    ring
  rw [hm] at hp
  change S.fourthResponse (fun e => S.differential f e • axisA) = 0 at ha
  change S.fourthResponse (fun e => S.differential g e • axisB) = 0 at hb
  rw [ha, hb] at h
  unfold mixedResponse
  linarith

theorem mixedResponse_polarize_a (S : SpinSystem 3 V E) (u w v : E → ℝ) :
    S.mixedResponse (u+w) v (u+w) v = S.mixedResponse u v u v +
      2 * S.mixedResponse u v w v + S.mixedResponse w v w v := by
  have hp : S.mixedObservable (u+w) v (u+w) v = S.mixedObservable u v u v +
      (2:ℝ) • S.mixedObservable u v w v + S.mixedObservable w v w v := by
    ext σ
    exact MixedAlgebra.four_polarize_a (S.mixedCoefficients σ) u w v
  unfold mixedResponse
  rw [hp, map_add, map_add, map_smul, smul_eq_mul]

theorem mixedResponse_polarize_b (S : SpinSystem 3 V E) (u w v z : E → ℝ) :
    S.mixedResponse u (v+z) w (v+z) = S.mixedResponse u v w v +
      2 * S.mixedResponse u v w z + S.mixedResponse u z w z := by
  have hp : S.mixedObservable u (v+z) w (v+z) = S.mixedObservable u v w v +
      (2:ℝ) • S.mixedObservable u v w z + S.mixedObservable u z w z := by
    ext σ
    exact MixedAlgebra.four_polarize_b (S.mixedCoefficients σ) u w v z
  unfold mixedResponse
  rw [hp, map_add, map_add, map_smul, smul_eq_mul]

omit [Fintype V] in
@[fun_prop] theorem continuous_secondPolynomial (S : SpinSystem 3 V E) (h k : E → ℝ) :
    Continuous (fun σ => S.energy (fun e => (h e*k e) • axisC^2) σ +
      S.energy (fun e => h e • axisC) σ * S.energy (fun e => k e • axisC) σ) := by
  fun_prop

def secondObservable (S : SpinSystem 3 V E) (h k : E → ℝ) : C((V → Spin 3), ℝ) :=
  ⟨_, S.continuous_secondPolynomial h k⟩

@[simp] theorem secondObservable_average (S : SpinSystem 3 V E) (h k : E → ℝ) :
    S.averageLinear (S.secondObservable h k) = S.secondAxisResponse h k := rfl

omit [Fintype V] in
theorem secondObservable_add_left (S : SpinSystem 3 V E) (u v w : E → ℝ) :
    S.secondObservable (u+v) w = S.secondObservable u w + S.secondObservable v w := by
  ext σ
  change S.energy (fun e => (((u+v) e)*w e) • axisC^2) σ +
    S.energy (fun e => (u+v) e • axisC) σ * S.energy (fun e => w e • axisC) σ =
    (S.energy (fun e => (u e*w e) • axisC^2) σ +
      S.energy (fun e => u e • axisC) σ * S.energy (fun e => w e • axisC) σ) +
    (S.energy (fun e => (v e*w e) • axisC^2) σ +
      S.energy (fun e => v e • axisC) σ * S.energy (fun e => w e • axisC) σ)
  simp only [energy_weighted]
  change MixedAlgebra.weighted (S.localCoefficient (axisC^2) σ) ((u+v)*w) +
      MixedAlgebra.weighted (S.localCoefficient axisC σ) (u+v) *
        MixedAlgebra.weighted (S.localCoefficient axisC σ) w = _
  rw [add_mul, MixedAlgebra.weighted_add, MixedAlgebra.weighted_add]
  simp only [MixedAlgebra.weighted, Pi.mul_apply]
  ring

omit [Fintype V] in
theorem secondObservable_symm (S : SpinSystem 3 V E) (u v : E → ℝ) :
    S.secondObservable u v = S.secondObservable v u := by
  ext σ
  change S.energy (fun e => (u e*v e) • axisC^2) σ +
    S.energy (fun e => u e • axisC) σ * S.energy (fun e => v e • axisC) σ = _
  simp only [mul_comm, secondObservable, ContinuousMap.coe_mk]

theorem secondAxisResponse_add_left (S : SpinSystem 3 V E) (u v w : E → ℝ) :
    S.secondAxisResponse (u+v) w = S.secondAxisResponse u w + S.secondAxisResponse v w := by
  have h := congrArg S.averageLinear (S.secondObservable_add_left u v w)
  simpa only [map_add, secondObservable_average] using h

theorem secondAxisResponse_symm (S : SpinSystem 3 V E) (u v : E → ℝ) :
    S.secondAxisResponse u v = S.secondAxisResponse v u := by
  exact congrArg S.averageLinear (S.secondObservable_symm u v)

theorem secondAxisResponse_add_right (S : SpinSystem 3 V E) (u v w : E → ℝ) :
    S.secondAxisResponse u (v+w) = S.secondAxisResponse u v + S.secondAxisResponse u w := by
  rw [S.secondAxisResponse_symm, S.secondAxisResponse_add_left,
    S.secondAxisResponse_symm v, S.secondAxisResponse_symm w]

omit [Fintype V] [Fintype E] in
theorem differential_add (S : SpinSystem n V E) (f g : V → ℝ) :
    S.differential (f+g) = S.differential f + S.differential g := by
  funext e
  simp only [differential, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem crossForm_add_left (S : SpinSystem 3 V E) (f g h : V → ℝ) :
    S.crossForm (f+g) h = S.crossForm f h + S.crossForm g h := by
  funext e
  simp only [crossForm, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem crossForm_add_right (S : SpinSystem 3 V E) (f g h : V → ℝ) :
    S.crossForm f (g+h) = S.crossForm f g + S.crossForm f h := by
  funext e
  simp only [crossForm, Pi.add_apply]
  ring

theorem mixedResponse_a_polarized (S : SpinSystem 3 V E) (f h g : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0) :
    2 * S.mixedResponse (S.differential f) (S.differential g)
      (S.differential h) (S.differential g) =
      S.secondAxisResponse (S.crossForm f g) (S.crossForm h g) := by
  have hfh : ∀ x s, S.pin x = some s → (f+h) x = 0 := by
    intro x s hs
    simp only [Pi.add_apply, hf x s hs, hh x s hs, add_zero]
  have hp := S.mixedResponse_diagonal (f+h) g hfh hg
  rw [S.differential_add, S.mixedResponse_polarize_a, S.crossForm_add_left,
    S.secondAxisResponse_add_left, S.secondAxisResponse_add_right,
    S.secondAxisResponse_add_right, S.secondAxisResponse_symm (S.crossForm h g)] at hp
  have hdiagf := S.mixedResponse_diagonal f g hf hg
  have hdiagh := S.mixedResponse_diagonal h g hh hg
  linarith

theorem mixedResponse_ward (S : SpinSystem 3 V E) (f g h k : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hk : ∀ x s, S.pin x = some s → k x = 0) :
    4 * S.mixedResponse (S.differential f) (S.differential g)
      (S.differential h) (S.differential k) =
      S.secondAxisResponse (S.crossForm f g) (S.crossForm h k) +
        S.secondAxisResponse (S.crossForm f k) (S.crossForm h g) := by
  have hgk : ∀ x s, S.pin x = some s → (g+k) x = 0 := by
    intro x s hs
    simp only [Pi.add_apply, hg x s hs, hk x s hs, add_zero]
  have hp := S.mixedResponse_a_polarized f h (g+k) hf hh hgk
  rw [S.differential_add, S.mixedResponse_polarize_b, S.crossForm_add_right,
    S.crossForm_add_right, S.secondAxisResponse_add_left,
    S.secondAxisResponse_add_right, S.secondAxisResponse_add_right] at hp
  have hdiagg := S.mixedResponse_a_polarized f h g hf hh hg
  have hdiagk := S.mixedResponse_a_polarized f h k hf hh hk
  linarith

end ClassicalON.SpinSystem

end

end OAI
