import OAI.Probability.ClassicalON.MixedWard

namespace OAI

universe uA uE uK uL uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

structure ComplexFourForm (A : Type uA) [AddCommMonoid A] [Module ℂ A] where
  toFun : A → A → A → A → ℂ
  add_first : ∀ u u' v w z, toFun (u+u') v w z = toFun u v w z + toFun u' v w z
  add_second : ∀ u v v' w z, toFun u (v+v') w z = toFun u v w z + toFun u v' w z
  add_third : ∀ u v w w' z, toFun u v (w+w') z = toFun u v w z + toFun u v w' z
  add_fourth : ∀ u v w z z', toFun u v w (z+z') = toFun u v w z + toFun u v w z'
  smul_first : ∀ r u v w z, toFun (r • u) v w z = r * toFun u v w z
  smul_second : ∀ r u v w z, toFun u (r • v) w z = r * toFun u v w z
  smul_third : ∀ r u v w z, toFun u v (r • w) z = r * toFun u v w z
  smul_fourth : ∀ r u v w z, toFun u v w (r • z) = r * toFun u v w z

instance {A : Type uA} [AddCommMonoid A] [Module ℂ A] :
    CoeFun (ComplexFourForm A) (fun _ => A → A → A → A → ℂ) := ⟨ComplexFourForm.toFun⟩

theorem complex_linear_zero_of_real {V : Type uV} (P : V → Prop)
    (L : (V → ℂ) → ℂ)
    (ha : ∀ u v, L (u+v) = L u + L v)
    (hs : ∀ r u, L (r • u) = r * L u)
    (hr : ∀ u : V → ℝ, (∀ x, P x → u x = 0) → L (fun x => (u x : ℂ)) = 0)
    (u : V → ℂ) (hu : ∀ x, P x → u x = 0) : L u = 0 := by
  have hre : ∀ x, P x → (u x).re = 0 := by
    intro x hx
    rw [hu x hx, Complex.zero_re]
  have him : ∀ x, P x → (u x).im = 0 := by
    intro x hx
    rw [hu x hx, Complex.zero_im]
  have hd : u = (fun x => ((u x).re : ℂ)) + Complex.I • (fun x => ((u x).im : ℂ)) := by
    ext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im (u x)).symm
  rw [hd, ha, hs, hr _ hre, hr _ him]
  simp only [mul_zero, add_zero]

theorem ComplexFourForm.zero_of_real {V : Type uV} (F : ComplexFourForm (V → ℂ))
    (P : V → Prop)
    (hr : ∀ u v w z : V → ℝ,
      (∀ x, P x → u x = 0) → (∀ x, P x → v x = 0) →
      (∀ x, P x → w x = 0) → (∀ x, P x → z x = 0) →
      F (fun x => (u x : ℂ)) (fun x => (v x : ℂ))
        (fun x => (w x : ℂ)) (fun x => (z x : ℂ)) = 0)
    (u v w z : V → ℂ)
    (hu : ∀ x, P x → u x = 0) (hv : ∀ x, P x → v x = 0)
    (hw : ∀ x, P x → w x = 0) (hz : ∀ x, P x → z x = 0) :
    F u v w z = 0 := by
  apply complex_linear_zero_of_real P (fun u => F u v w z)
    (fun u u' => F.add_first u u' v w z) (fun r u => F.smul_first r u v w z) ?_ u hu
  intro a ha
  apply complex_linear_zero_of_real P (fun v => F (fun x => (a x : ℂ)) v w z)
    (fun v v' => F.add_second (fun x => (a x : ℂ)) v v' w z)
    (fun r v => F.smul_second r (fun x => (a x : ℂ)) v w z) ?_ v hv
  intro b hb
  apply complex_linear_zero_of_real P
    (fun w => F (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) w z)
    (fun w w' => F.add_third (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) w w' z)
    (fun r w => F.smul_third r (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) w z) ?_ w hw
  intro c hc
  apply complex_linear_zero_of_real P
    (fun z => F (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) (fun x => (c x : ℂ)) z)
    (fun z z' => F.add_fourth (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) (fun x => (c x : ℂ)) z z')
    (fun r z => F.smul_fourth r (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) (fun x => (c x : ℂ)) z)
    ?_ z hz
  intro d hd
  exact hr a b c d ha hb hc hd

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} {L : Type uL} [Fintype E] [CommRing K] [CommRing L]

def Coeffs.map (φ : K →+* L) (J : Coeffs E K) : Coeffs E L where
  a := φ ∘ J.a
  b := φ ∘ J.b
  aa := φ ∘ J.aa
  ab := φ ∘ J.ab
  bb := φ ∘ J.bb
  aab := φ ∘ J.aab
  abb := φ ∘ J.abb
  aabb := φ ∘ J.aabb

theorem weighted_map (φ : K →+* L) (J u : E → K) :
    weighted (φ ∘ J) (φ ∘ u) = φ (weighted J u) := by
  simp [weighted]

theorem four_map (φ : K →+* L) (J : Coeffs E K) (u v w z : E → K) :
    four (J.map φ) (φ ∘ u) (φ ∘ v) (φ ∘ w) (φ ∘ z) = φ (four J u v w z) := by
  simp only [four, Coeffs.map, weighted, Function.comp_apply, Pi.mul_apply,
    map_add, map_mul, map_sum]

theorem weighted_smul (J u : E → K) (r : K) :
    weighted J (r • u) = r * weighted J u := by
  exact weighted_const_mul J u r

theorem four_smul_first (J : Coeffs E K) (u v w z : E → K) (r : K) :
    four J (r • u) v w z = r * four J u v w z := by
  simp only [four, smul_mul_assoc, weighted_smul]
  ring

theorem four_smul_second (J : Coeffs E K) (u v w z : E → K) (r : K) :
    four J u (r • v) w z = r * four J u v w z := by
  simp only [four, mul_smul_comm, smul_mul_assoc, weighted_smul]
  ring

theorem four_smul_third (J : Coeffs E K) (u v w z : E → K) (r : K) :
    four J u v (r • w) z = r * four J u v w z := by
  rw [four_swap_first_third, four_smul_first, four_swap_first_third J w]

theorem four_smul_fourth (J : Coeffs E K) (u v w z : E → K) (r : K) :
    four J u v w (r • z) = r * four J u v w z := by
  rw [four_swap_second_fourth, four_smul_second, four_swap_second_fourth J u z]

end MixedAlgebra

namespace ClassicalON.SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem integrable_complex_integrand [NeZero n] (S : SpinSystem n V E)
    {f : (V → Spin n) → ℂ} (hf : Continuous f) :
    Integrable (fun σ => f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ)) S.reference :=
  (hf.mul (Complex.continuous_ofReal.comp (S.continuous_energy _).rexp)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def averageComplexLinear [NeZero n] (S : SpinSystem n V E) : C((V → Spin n), ℂ) →ₗ[ℂ] ℂ where
  toFun f := (∫ σ, f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ)
  map_add' f g := by
    simp only [ContinuousMap.add_apply, add_mul]
    rw [integral_add (S.integrable_complex_integrand f.continuous)
      (S.integrable_complex_integrand g.continuous), add_div]
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc,
      integral_const_mul, RingHom.id_apply, mul_div_assoc]

def ofRealObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℝ)) : C(Ω, ℂ) :=
  ⟨fun σ => (f σ : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

@[simp] theorem averageComplex_ofReal [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℝ)) :
    S.averageComplexLinear (ofRealObservable f) = (S.averageLinear f : ℂ) := by
  change (∫ σ, (f σ : ℂ) * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ) = _
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, ← Complex.ofReal_div]
  rfl

def complexCoefficients (S : SpinSystem 3 V E) (σ : V → Spin 3) : MixedAlgebra.Coeffs E ℂ :=
  (S.mixedCoefficients σ).map Complex.ofRealHom

omit [Fintype V] in
@[fun_prop] theorem continuous_complexWeighted (S : SpinSystem n V E)
    (M : SpinOperator n) (u : E → ℂ) :
    Continuous (fun σ => MixedAlgebra.weighted
      (fun e => (S.localCoefficient M σ e : ℂ)) u) := by
  unfold MixedAlgebra.weighted localCoefficient
  fun_prop

omit [Fintype V] in
@[fun_prop] theorem continuous_complexMixedPolynomial (S : SpinSystem 3 V E)
    (u v w z : E → ℂ) :
    Continuous (fun σ => MixedAlgebra.four (S.complexCoefficients σ) u v w z) := by
  simp only [MixedAlgebra.four, complexCoefficients, MixedAlgebra.Coeffs.map,
    mixedCoefficients, Function.comp_def, Complex.ofRealHom_eq_coe]
  fun_prop

def complexMixedObservable (S : SpinSystem 3 V E) (u v w z : E → ℂ) : C((V → Spin 3), ℂ) :=
  ⟨_, S.continuous_complexMixedPolynomial u v w z⟩

def complexMixedResponse (S : SpinSystem 3 V E) (u v w z : E → ℂ) : ℂ :=
  S.averageComplexLinear (S.complexMixedObservable u v w z)

theorem complexMixedResponse_ofReal (S : SpinSystem 3 V E) (u v w z : E → ℝ) :
    S.complexMixedResponse (fun e => (u e : ℂ)) (fun e => (v e : ℂ))
      (fun e => (w e : ℂ)) (fun e => (z e : ℂ)) = (S.mixedResponse u v w z : ℂ) := by
  have hc : S.complexMixedObservable (fun e => (u e : ℂ)) (fun e => (v e : ℂ))
      (fun e => (w e : ℂ)) (fun e => (z e : ℂ)) = ofRealObservable (S.mixedObservable u v w z) := by
    ext σ
    exact MixedAlgebra.four_map Complex.ofRealHom (S.mixedCoefficients σ) u v w z
  unfold complexMixedResponse
  rw [hc, S.averageComplex_ofReal]
  rfl

theorem complexMixedResponse_add_first (S : SpinSystem 3 V E) (u v w z u' : E → ℂ) :
    S.complexMixedResponse (u+u') v w z = S.complexMixedResponse u v w z + S.complexMixedResponse u' v w z := by
  have hp : S.complexMixedObservable (u+u') v w z = S.complexMixedObservable u v w z +
      S.complexMixedObservable u' v w z := by
    ext σ
    exact MixedAlgebra.four_add_first (S.complexCoefficients σ) u u' v w z
  unfold complexMixedResponse
  rw [hp, map_add]

theorem complexMixedResponse_smul_first (S : SpinSystem 3 V E) (u v w z : E → ℂ) (r : ℂ) :
    S.complexMixedResponse (r • u) v w z = r * S.complexMixedResponse u v w z := by
  have hp : S.complexMixedObservable (r • u) v w z = r • S.complexMixedObservable u v w z := by
    ext σ
    exact MixedAlgebra.four_smul_first (S.complexCoefficients σ) u v w z r
  unfold complexMixedResponse
  rw [hp, map_smul, smul_eq_mul]

theorem complexMixedResponse_add_second (S : SpinSystem 3 V E) (u v w z v' : E → ℂ) :
    S.complexMixedResponse u (v+v') w z = S.complexMixedResponse u v w z + S.complexMixedResponse u v' w z := by
  have hp : S.complexMixedObservable u (v+v') w z = S.complexMixedObservable u v w z +
      S.complexMixedObservable u v' w z := by
    ext σ
    exact MixedAlgebra.four_add_second (S.complexCoefficients σ) u v v' w z
  unfold complexMixedResponse
  rw [hp, map_add]

theorem complexMixedResponse_smul_second (S : SpinSystem 3 V E) (u v w z : E → ℂ) (r : ℂ) :
    S.complexMixedResponse u (r • v) w z = r * S.complexMixedResponse u v w z := by
  have hp : S.complexMixedObservable u (r • v) w z = r • S.complexMixedObservable u v w z := by
    ext σ
    exact MixedAlgebra.four_smul_second (S.complexCoefficients σ) u v w z r
  unfold complexMixedResponse
  rw [hp, map_smul, smul_eq_mul]

theorem complexMixedResponse_add_third (S : SpinSystem 3 V E) (u v w z w' : E → ℂ) :
    S.complexMixedResponse u v (w+w') z = S.complexMixedResponse u v w z + S.complexMixedResponse u v w' z := by
  have hp : S.complexMixedObservable u v (w+w') z = S.complexMixedObservable u v w z +
      S.complexMixedObservable u v w' z := by
    ext σ
    exact MixedAlgebra.four_add_third (S.complexCoefficients σ) u v w w' z
  unfold complexMixedResponse
  rw [hp, map_add]

theorem complexMixedResponse_smul_third (S : SpinSystem 3 V E) (u v w z : E → ℂ) (r : ℂ) :
    S.complexMixedResponse u v (r • w) z = r * S.complexMixedResponse u v w z := by
  have hp : S.complexMixedObservable u v (r • w) z = r • S.complexMixedObservable u v w z := by
    ext σ
    exact MixedAlgebra.four_smul_third (S.complexCoefficients σ) u v w z r
  unfold complexMixedResponse
  rw [hp, map_smul, smul_eq_mul]

theorem complexMixedResponse_add_fourth (S : SpinSystem 3 V E) (u v w z z' : E → ℂ) :
    S.complexMixedResponse u v w (z+z') = S.complexMixedResponse u v w z + S.complexMixedResponse u v w z' := by
  have hp : S.complexMixedObservable u v w (z+z') = S.complexMixedObservable u v w z +
      S.complexMixedObservable u v w z' := by
    ext σ
    exact MixedAlgebra.four_add_fourth (S.complexCoefficients σ) u v w z z'
  unfold complexMixedResponse
  rw [hp, map_add]

theorem complexMixedResponse_smul_fourth (S : SpinSystem 3 V E) (u v w z : E → ℂ) (r : ℂ) :
    S.complexMixedResponse u v w (r • z) = r * S.complexMixedResponse u v w z := by
  have hp : S.complexMixedObservable u v w (r • z) = r • S.complexMixedObservable u v w z := by
    ext σ
    exact MixedAlgebra.four_smul_fourth (S.complexCoefficients σ) u v w z r
  unfold complexMixedResponse
  rw [hp, map_smul, smul_eq_mul]

def complexEnergy (S : SpinSystem n V E) (M : SpinOperator n) (u : E → ℂ)
    (σ : V → Spin n) : ℂ := MixedAlgebra.weighted
      (fun e => (S.localCoefficient M σ e : ℂ)) u

omit [Fintype V] in
@[fun_prop] theorem continuous_complexEnergy (S : SpinSystem n V E)
    (M : SpinOperator n) (u : E → ℂ) : Continuous (S.complexEnergy M u) :=
  S.continuous_complexWeighted M u

omit [Fintype V] in
theorem complexEnergy_ofReal (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℝ) (σ : V → Spin n) :
    S.complexEnergy M (fun e => (u e : ℂ)) σ =
      (S.energy (fun e => u e • M) σ : ℂ) := by
  rw [S.energy_weighted]
  exact MixedAlgebra.weighted_map Complex.ofRealHom (S.localCoefficient M σ) u

omit [Fintype V] in
@[simp] theorem complexEnergy_add (S : SpinSystem n V E) (M : SpinOperator n)
    (u v : E → ℂ) (σ : V → Spin n) :
    S.complexEnergy M (u+v) σ = S.complexEnergy M u σ + S.complexEnergy M v σ :=
  MixedAlgebra.weighted_add _ u v

omit [Fintype V] in
@[simp] theorem complexEnergy_smul (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℂ) (r : ℂ) (σ : V → Spin n) :
    S.complexEnergy M (r • u) σ = r * S.complexEnergy M u σ :=
  MixedAlgebra.weighted_smul _ u r

omit [Fintype V] in
@[fun_prop] theorem continuous_complexSecondPolynomial (S : SpinSystem 3 V E)
    (u v : E → ℂ) : Continuous (fun σ => S.complexEnergy (axisC^2) (u*v) σ +
      S.complexEnergy axisC u σ * S.complexEnergy axisC v σ) := by
  fun_prop

def complexSecondObservable (S : SpinSystem 3 V E) (u v : E → ℂ) : C((V → Spin 3), ℂ) :=
  ⟨_, S.continuous_complexSecondPolynomial u v⟩

def complexSecondResponse (S : SpinSystem 3 V E) (u v : E → ℂ) : ℂ :=
  S.averageComplexLinear (S.complexSecondObservable u v)

theorem complexSecondResponse_ofReal (S : SpinSystem 3 V E) (u v : E → ℝ) :
    S.complexSecondResponse (fun e => (u e : ℂ)) (fun e => (v e : ℂ)) =
      (S.secondAxisResponse u v : ℂ) := by
  have hp : S.complexSecondObservable (fun e => (u e : ℂ)) (fun e => (v e : ℂ)) =
      ofRealObservable (S.secondObservable u v) := by
    ext σ
    change S.complexEnergy (axisC^2) ((fun e => (u e : ℂ)) * (fun e => (v e : ℂ))) σ +
      S.complexEnergy axisC (fun e => (u e : ℂ)) σ *
        S.complexEnergy axisC (fun e => (v e : ℂ)) σ = _
    rw [show ((fun e => (u e : ℂ)) * (fun e => (v e : ℂ))) =
      (fun e => ((u e*v e : ℝ) : ℂ)) from by ext; simp]
    simp only [complexEnergy_ofReal, ← Complex.ofReal_add, ← Complex.ofReal_mul]
    rfl
  unfold complexSecondResponse
  rw [hp, S.averageComplex_ofReal, S.secondObservable_average]

theorem complexSecondResponse_add_left (S : SpinSystem 3 V E) (u v w : E → ℂ) :
    S.complexSecondResponse (u+v) w = S.complexSecondResponse u w + S.complexSecondResponse v w := by
  have hp : S.complexSecondObservable (u+v) w =
      S.complexSecondObservable u w + S.complexSecondObservable v w := by
    ext σ
    change S.complexEnergy (axisC^2) ((u+v)*w) σ +
      S.complexEnergy axisC (u+v) σ * S.complexEnergy axisC w σ =
      (S.complexEnergy (axisC^2) (u*w) σ +
        S.complexEnergy axisC u σ * S.complexEnergy axisC w σ) +
      (S.complexEnergy (axisC^2) (v*w) σ +
        S.complexEnergy axisC v σ * S.complexEnergy axisC w σ)
    rw [add_mul, complexEnergy_add, complexEnergy_add]
    ring
  unfold complexSecondResponse
  rw [hp, map_add]

theorem complexSecondResponse_symm (S : SpinSystem 3 V E) (u v : E → ℂ) :
    S.complexSecondResponse u v = S.complexSecondResponse v u := by
  have hp : S.complexSecondObservable u v = S.complexSecondObservable v u := by
    ext σ
    change S.complexEnergy (axisC^2) (u*v) σ +
      S.complexEnergy axisC u σ * S.complexEnergy axisC v σ =
      S.complexEnergy (axisC^2) (v*u) σ +
        S.complexEnergy axisC v σ * S.complexEnergy axisC u σ
    rw [mul_comm u v, mul_comm (S.complexEnergy axisC u σ)]
  exact congrArg S.averageComplexLinear hp

theorem complexSecondResponse_add_right (S : SpinSystem 3 V E) (u v w : E → ℂ) :
    S.complexSecondResponse u (v+w) = S.complexSecondResponse u v + S.complexSecondResponse u w := by
  rw [S.complexSecondResponse_symm, S.complexSecondResponse_add_left,
    S.complexSecondResponse_symm v, S.complexSecondResponse_symm w]

theorem complexSecondResponse_smul_left (S : SpinSystem 3 V E) (u v : E → ℂ) (r : ℂ) :
    S.complexSecondResponse (r • u) v = r * S.complexSecondResponse u v := by
  have hp : S.complexSecondObservable (r • u) v = r • S.complexSecondObservable u v := by
    ext σ
    change S.complexEnergy (axisC^2) ((r • u)*v) σ +
      S.complexEnergy axisC (r • u) σ * S.complexEnergy axisC v σ =
      r * (S.complexEnergy (axisC^2) (u*v) σ +
        S.complexEnergy axisC u σ * S.complexEnergy axisC v σ)
    rw [smul_mul_assoc, complexEnergy_smul, complexEnergy_smul]
    ring
  unfold complexSecondResponse
  rw [hp, map_smul, smul_eq_mul]

theorem complexSecondResponse_smul_right (S : SpinSystem 3 V E) (u v : E → ℂ) (r : ℂ) :
    S.complexSecondResponse u (r • v) = r * S.complexSecondResponse u v := by
  rw [S.complexSecondResponse_symm, S.complexSecondResponse_smul_left,
    S.complexSecondResponse_symm v]

omit [Fintype V] [Fintype E] in
def complexCross (S : SpinSystem 3 V E) (f g : V → ℂ) : E → ℂ :=
  fun e => f (S.left e)*g (S.right e) - g (S.left e)*f (S.right e)

omit [Fintype V] [Fintype E] in
theorem complexCross_ofReal (S : SpinSystem 3 V E) (f g : V → ℝ) :
    S.complexCross (fun x => (f x : ℂ)) (fun x => (g x : ℂ)) =
      fun e => (S.crossForm f g e : ℂ) := by
  ext e
  simp [complexCross, crossForm]

omit [Fintype V] [Fintype E] in
theorem differential_ofReal (S : SpinSystem n V E) (f : V → ℝ) :
    S.differential (fun x => (f x : ℂ)) = fun e => (S.differential (K := ℝ) f e : ℂ) := by
  ext e
  simp [differential]

omit [Fintype V] [Fintype E] in
theorem complexCross_add_left (S : SpinSystem 3 V E) (f g h : V → ℂ) :
    S.complexCross (f+h) g = S.complexCross f g + S.complexCross h g := by
  ext e
  simp only [complexCross, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem complexCross_smul_left (S : SpinSystem 3 V E) (f g : V → ℂ) (r : ℂ) :
    S.complexCross (r • f) g = r • S.complexCross f g := by
  ext e
  simp only [complexCross, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype V] [Fintype E] in
theorem complexCross_add_right (S : SpinSystem 3 V E) (f g h : V → ℂ) :
    S.complexCross f (g+h) = S.complexCross f g + S.complexCross f h := by
  ext e
  simp only [complexCross, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem complexCross_smul_right (S : SpinSystem 3 V E) (f g : V → ℂ) (r : ℂ) :
    S.complexCross f (r • g) = r • S.complexCross f g := by
  ext e
  simp only [complexCross, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype V] [Fintype E] in
theorem complexDifferential_add (S : SpinSystem n V E) (f g : V → ℂ) :
    S.differential (f+g) = S.differential f + S.differential g := by
  ext e
  simp only [differential, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem complexDifferential_smul (S : SpinSystem n V E) (f : V → ℂ) (r : ℂ) :
    S.differential (r • f) = r • S.differential f := by
  ext e
  simp only [differential, Pi.smul_apply, smul_eq_mul]
  ring

def complexWardDefect (S : SpinSystem 3 V E) : ComplexFourForm (V → ℂ) where
  toFun f g h k := 4 * S.complexMixedResponse (S.differential f) (S.differential g)
    (S.differential h) (S.differential k) -
    (S.complexSecondResponse (S.complexCross f g) (S.complexCross h k) +
      S.complexSecondResponse (S.complexCross f k) (S.complexCross h g))
  add_first := by
    intro f f' g h k
    simp only [complexDifferential_add, complexMixedResponse_add_first,
      complexCross_add_left, complexSecondResponse_add_left]
    ring
  add_second := by
    intro f g g' h k
    simp only [complexDifferential_add, complexMixedResponse_add_second,
      complexCross_add_right, complexSecondResponse_add_left, complexSecondResponse_add_right]
    ring
  add_third := by
    intro f g h h' k
    simp only [complexDifferential_add, complexMixedResponse_add_third,
      complexCross_add_left, complexSecondResponse_add_right]
    ring
  add_fourth := by
    intro f g h k k'
    simp only [complexDifferential_add, complexMixedResponse_add_fourth,
      complexCross_add_right, complexSecondResponse_add_left, complexSecondResponse_add_right]
    ring
  smul_first := by
    intro r f g h k
    simp only [complexDifferential_smul, complexMixedResponse_smul_first,
      complexCross_smul_left, complexSecondResponse_smul_left]
    ring
  smul_second := by
    intro r f g h k
    simp only [complexDifferential_smul, complexMixedResponse_smul_second,
      complexCross_smul_right, complexSecondResponse_smul_left, complexSecondResponse_smul_right]
    ring
  smul_third := by
    intro r f g h k
    simp only [complexDifferential_smul, complexMixedResponse_smul_third,
      complexCross_smul_left, complexSecondResponse_smul_right]
    ring
  smul_fourth := by
    intro r f g h k
    simp only [complexDifferential_smul, complexMixedResponse_smul_fourth,
      complexCross_smul_right, complexSecondResponse_smul_left, complexSecondResponse_smul_right]
    ring

theorem complexWardDefect_real (S : SpinSystem 3 V E) (f g h k : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hk : ∀ x s, S.pin x = some s → k x = 0) :
    S.complexWardDefect (fun x => (f x : ℂ)) (fun x => (g x : ℂ))
      (fun x => (h x : ℂ)) (fun x => (k x : ℂ)) = 0 := by
  change _ - _ = 0
  apply sub_eq_zero.mpr
  simp only [differential_ofReal, complexCross_ofReal, complexMixedResponse_ofReal,
    complexSecondResponse_ofReal]
  exact_mod_cast S.mixedResponse_ward f g h k hf hg hh hk

theorem complexMixedResponse_ward (S : SpinSystem 3 V E) (f g h k : V → ℂ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hk : ∀ x s, S.pin x = some s → k x = 0) :
    4 * S.complexMixedResponse (S.differential f) (S.differential g)
      (S.differential h) (S.differential k) =
      S.complexSecondResponse (S.complexCross f g) (S.complexCross h k) +
        S.complexSecondResponse (S.complexCross f k) (S.complexCross h g) := by
  apply sub_eq_zero.mp
  change S.complexWardDefect f g h k = 0
  refine S.complexWardDefect.zero_of_real (fun x => ∃ s, S.pin x = some s) ?_ f g h k ?_ ?_ ?_ ?_
  · intro a b c d ha hb hc hd
    exact S.complexWardDefect_real a b c d
      (fun x s hs => ha x ⟨s, hs⟩) (fun x s hs => hb x ⟨s, hs⟩)
      (fun x s hs => hc x ⟨s, hs⟩) (fun x s hs => hd x ⟨s, hs⟩)
  · rintro x ⟨s, hs⟩; exact hf x s hs
  · rintro x ⟨s, hs⟩; exact hg x s hs
  · rintro x ⟨s, hs⟩; exact hh x s hs
  · rintro x ⟨s, hs⟩; exact hk x s hs

end ClassicalON.SpinSystem

end
end

end OAI
