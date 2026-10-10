import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model

namespace OAI

/-!
# Spatial dilation on the actual weak H¹ domain

The physical-energy amplification in both manuscripts changes coordinates
on the full fermionic form domain. Here weak derivatives are transformed
by changing variables in the compact-test identity, rather than assuming
pointwise differentiability of an arbitrary state.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem memLp_comp_dilation {n : ℕ} {f : Configuration n → ℂ}
    (hf : MemLp f 2) {scale : ℝ} (hscale : scale ≠ 0) :
    MemLp (fun x => f (scale • x)) 2 := by
  have hm : MemLp f 2 (Measure.map (fun x => scale • x) volume) := by
    rw [Measure.map_addHaar_smul volume hscale]
    exact hf.smul_measure (by simp)
  exact hm.comp_of_map (measurable_const_smul scale).aemeasurable

theorem weak_partial_dilation {n : ℕ} (u g : Configuration n → ℂ)
    (a : Fin n × Fin 3) {scale : ℝ} (hscale : scale ≠ 0)
    (hweak : ∀ (phi : Configuration n → ℝ), ContDiff ℝ (⊤ : ℕ∞) phi →
      HasCompactSupport phi →
      (∫ x, u x * (fderiv ℝ phi x (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ x, g x * (phi x : ℂ)))
    (phi : Configuration n → ℝ) (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (hcompact : HasCompactSupport phi) :
    (∫ x, u (scale • x) * (fderiv ℝ phi x (EuclideanSpace.single a 1) : ℂ)) =
      -(∫ x, (scale : ℂ) * g (scale • x) * (phi x : ℂ)) := by
  let test : Configuration n → ℝ := fun y => phi (scale⁻¹ • y)
  have htest : ContDiff ℝ (⊤ : ℕ∞) test := by dsimp [test]; fun_prop
  have hderiv (y : Configuration n) :
      fderiv ℝ test y (EuclideanSpace.single a 1) =
        scale⁻¹ * fderiv ℝ phi (scale⁻¹ • y) (EuclideanSpace.single a 1) := by
    have hlin : HasFDerivAt (fun z : Configuration n => scale⁻¹ • z)
        (scale⁻¹ • ContinuousLinearMap.id ℝ (Configuration n)) y :=
      (hasFDerivAt_id y).const_smul scale⁻¹
    have h := (hphi.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y hlin
    change fderiv ℝ (phi ∘ fun z => scale⁻¹ • z) y _ = _
    rw [h.fderiv]
    simp
  have hw := hweak test htest (hcompact.comp_smul (inv_ne_zero hscale))
  have hleft : (∫ y, u y * (fderiv ℝ test y (EuclideanSpace.single a 1) : ℂ)) =
      (scale⁻¹ : ℂ) * ∫ y, u y *
        (fderiv ℝ phi (scale⁻¹ • y) (EuclideanSpace.single a 1) : ℂ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only
      rw [hderiv]
      push_cast
      ring
  rw [hleft] at hw
  have hsC : (scale : ℂ) ≠ 0 := by exact_mod_cast hscale
  have hwscaled := congrArg (fun z : ℂ => (scale : ℂ) * z) hw
  simp only [← mul_assoc, mul_inv_cancel₀ hsC, one_mul] at hwscaled
  let jacobian : ℝ := |(scale ^ Module.finrank ℝ (Configuration n))⁻¹|
  have hchangeLeft :
      (∫ x, u (scale • x) * (fderiv ℝ phi x (EuclideanSpace.single a 1) : ℂ)) =
        jacobian • ∫ y, u y *
          (fderiv ℝ phi (scale⁻¹ • y) (EuclideanSpace.single a 1) : ℂ) := by
    simpa only [inv_smul_smul₀ hscale] using Measure.integral_comp_smul volume
      (fun y => u y * (fderiv ℝ phi (scale⁻¹ • y) (EuclideanSpace.single a 1) : ℂ)) scale
  have hchangeRight : (∫ x, g (scale • x) * (phi x : ℂ)) =
      jacobian • ∫ y, g y * (test y : ℂ) := by
    simpa only [test, inv_smul_smul₀ hscale] using Measure.integral_comp_smul volume
      (fun y => g y * (phi (scale⁻¹ • y) : ℂ)) scale
  have hright : (∫ x, (scale : ℂ) * g (scale • x) * (phi x : ℂ)) =
      (scale : ℂ) * (jacobian • ∫ y, g y * (test y : ℂ)) := by
    calc
      _ = (scale : ℂ) * ∫ x, g (scale • x) * (phi x : ℂ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun _ => by ring
      _ = _ := by rw [hchangeRight]
  rw [hchangeLeft, hright, hwscaled]
  simp only [Complex.real_smul]
  ring

def dilateState {n : ℕ} (state : Coulomb.H1Vector n) (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.H1Vector n where
  value spin x := state.value spin (scale • x)
  gradient spin a x := (scale : ℂ) * state.gradient spin a (scale • x)
  value_L2 spin := memLp_comp_dilation (state.value_L2 spin) hscale
  partial_L2 spin a := (memLp_comp_dilation (state.partial_L2 spin a) hscale).const_mul _
  weak_partial spin a := weak_partial_dilation (state.value spin) (state.gradient spin a)
    a hscale (state.weak_partial spin a)

theorem dilateState_antisymmetric {n : ℕ} (state : Coulomb.H1Vector n)
    (hstate : Coulomb.Antisymmetric state) (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.Antisymmetric (dilateState state scale hscale) := by
  intro p spin
  have h := (Measure.quasiMeasurePreserving_smul volume hscale).ae (hstate p spin)
  filter_upwards [h] with x hx
  have hperm : Coulomb.permute p (scale • x) = scale • Coulomb.permute p x := by
    ext a
    rfl
  simpa only [dilateState, hperm] using hx

theorem integral_dilation {n : ℕ} (f : Configuration n → ℝ) (scale : ℝ) :
    (∫ x, f (scale • x)) =
      |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ * ∫ x, f x := by
  simpa only [abs_inv, smul_eq_mul] using
    Measure.integral_comp_smul volume f scale

theorem mass_dilateState {n : ℕ} (state : Coulomb.H1Vector n)
    (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.mass (dilateState state scale hscale) =
      |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ * Coulomb.mass state := by
  change (∑ spin, ∫ x, ‖state.value spin (scale • x)‖ ^ 2) = _
  rw [Coulomb.mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spin _
  exact integral_dilation (fun x => ‖state.value spin x‖ ^ 2) scale

theorem kinetic_dilateState {n : ℕ} (state : Coulomb.H1Vector n)
    (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.kinetic (dilateState state scale hscale) =
      scale ^ 2 * |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ *
        Coulomb.kinetic state := by
  change (1 / 2 : ℝ) * (∑ spin, ∑ a, ∫ x,
    ‖(scale : ℂ) * state.gradient spin a (scale • x)‖ ^ 2) = _
  have hI (spin : SpinConfiguration n) (a : Fin n × Fin 3) :
      (∫ x, ‖state.gradient spin a (scale • x)‖ ^ 2) =
        |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ *
          ∫ x, ‖state.gradient spin a x‖ ^ 2 :=
    integral_dilation (fun x => ‖state.gradient spin a x‖ ^ 2) scale
  simp_rw [Coulomb.norm_real_mul_sq, integral_const_mul, hI]
  simp only [← Finset.mul_sum, Coulomb.kinetic]
  ring

/-- The Jacobian factor makes spatial dilation preserve the physical norm. -/
def normalizedDilation {n : ℕ} (state : Coulomb.H1Vector n)
    (scale : ℝ) (hscale : scale ≠ 0) : Coulomb.H1Vector n :=
  (dilateState state scale hscale).rsmul
    (Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)|)

theorem mass_normalizedDilation {n : ℕ} (state : Coulomb.H1Vector n)
    (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.mass (normalizedDilation state scale hscale) = Coulomb.mass state := by
  rw [normalizedDilation, Coulomb.mass_rsmul, mass_dilateState,
    Real.sq_sqrt (abs_nonneg _), ← mul_assoc,
    mul_inv_cancel₀ (abs_ne_zero.mpr (pow_ne_zero _ hscale)), one_mul]

theorem kinetic_normalizedDilation {n : ℕ} (state : Coulomb.H1Vector n)
    (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.kinetic (normalizedDilation state scale hscale) =
      scale ^ 2 * Coulomb.kinetic state := by
  rw [normalizedDilation, Coulomb.kinetic_rsmul, kinetic_dilateState,
    Real.sq_sqrt (abs_nonneg _)]
  have h := mul_inv_cancel₀ (abs_ne_zero.mpr
    (pow_ne_zero (Module.finrank ℝ (Configuration n)) hscale))
  calc
    _ = scale ^ 2 * (|scale ^ Module.finrank ℝ (Configuration n)| *
        |scale ^ Module.finrank ℝ (Configuration n)|⁻¹) * Coulomb.kinetic state := by ring
    _ = _ := by rw [h, mul_one]

theorem normalizedDilation_antisymmetric {n : ℕ} (state : Coulomb.H1Vector n)
    (hstate : Coulomb.Antisymmetric state) (scale : ℝ) (hscale : scale ≠ 0) :
    Coulomb.Antisymmetric (normalizedDilation state scale hscale) :=
  (dilateState_antisymmetric state hstate scale hscale).rsmul _

theorem h1Vector_ext {n : ℕ} {u v : Coulomb.H1Vector n}
    (hvalue : u.value = v.value) (hgradient : u.gradient = v.gradient) : u = v := by
  cases u
  cases v
  cases hvalue
  cases hgradient
  rfl

/-- Inverse dilation acts on every weak-H¹ state, so lower energy estimates
can be transferred back from the entire physical form domain. -/
theorem normalizedDilation_inverse {n : ℕ} (state : Coulomb.H1Vector n)
    (scale : ℝ) (hscale : scale ≠ 0) :
    normalizedDilation (normalizedDilation state scale hscale) scale⁻¹
      (inv_ne_zero hscale) = state := by
  have hroot : Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)| ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (abs_pos.mpr (pow_ne_zero _ hscale))
  have hamp : Real.sqrt |scale⁻¹ ^ Module.finrank ℝ (Configuration n)| *
      Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)| = 1 := by
    rw [inv_pow, abs_inv, Real.sqrt_inv, inv_mul_cancel₀ hroot]
  have hampC : (Real.sqrt |scale⁻¹ ^ Module.finrank ℝ (Configuration n)| : ℂ) *
      (Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)| : ℂ) = 1 := by
    exact_mod_cast hamp
  have hscaleC : (scale : ℂ) * ((scale⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast (mul_inv_cancel₀ hscale)
  apply h1Vector_ext
  · funext spin x
    change (Real.sqrt |scale⁻¹ ^ Module.finrank ℝ (Configuration n)| : ℂ) *
      ((Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)| : ℂ) *
        state.value spin (scale • scale⁻¹ • x)) = _
    rw [smul_inv_smul₀ hscale, ← mul_assoc, hampC, one_mul]
  · funext spin a x
    change (Real.sqrt |scale⁻¹ ^ Module.finrank ℝ (Configuration n)| : ℂ) *
      (((scale⁻¹ : ℝ) : ℂ) *
        ((Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)| : ℂ) *
          ((scale : ℂ) * state.gradient spin a (scale • scale⁻¹ • x)))) = _
    rw [smul_inv_smul₀ hscale]
    calc
      _ = ((Real.sqrt |scale⁻¹ ^ Module.finrank ℝ (Configuration n)| : ℂ) *
          (Real.sqrt |scale ^ Module.finrank ℝ (Configuration n)| : ℂ)) *
            ((scale : ℂ) * ((scale⁻¹ : ℝ) : ℂ)) * state.gradient spin a x := by ring
      _ = _ := by rw [hampC, hscaleC, one_mul, one_mul]

theorem position_smul {n : ℕ} (x : Configuration n) (i : Fin n) (scale : ℝ) :
    Coulomb.position (scale • x) i = scale • Coulomb.position x i := by
  ext a
  rfl

theorem coulombKernel_smul (x : Position) {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.coulombKernel (scale • x) = scale⁻¹ * Coulomb.coulombKernel x := by
  simp only [Coulomb.coulombKernel, norm_smul, Real.norm_eq_abs,
    abs_of_pos hscale, mul_inv_rev]
  ring

/-- Rescaling the nuclear positions leaves all nuclear charges unchanged. -/
def dilatedNuclei {M : ℕ} (S : Coulomb.Nuclei M) (scale : ℝ)
    (hscale : scale ≠ 0) : Coulomb.Nuclei M where
  nonempty := S.nonempty
  position a := scale⁻¹ • S.position a
  distinct := by
    intro a b hab
    apply S.distinct
    have h := congrArg (fun x : Position => scale • x) hab
    simpa only [smul_inv_smul₀ hscale] using h
  charge := S.charge
  charge_ge_one := S.charge_ge_one

theorem attraction_dilatedNuclei {M : ℕ} (S : Coulomb.Nuclei M)
    {scale : ℝ} (hscale : 0 < scale) (x : Position) :
    Coulomb.attraction (dilatedNuclei S scale hscale.ne') x =
      scale * Coulomb.attraction S (scale • x) := by
  have hpos (a : Fin M) : x - scale⁻¹ • S.position a =
      scale⁻¹ • (scale • x - S.position a) := by
    rw [smul_sub, inv_smul_smul₀ hscale.ne']
  simp only [Coulomb.attraction, dilatedNuclei, hpos,
    coulombKernel_smul _ (inv_pos.mpr hscale), inv_inv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem nuclearEnergy_dilateState {M n : ℕ} (S : Coulomb.Nuclei M)
    (state : Coulomb.H1Vector n) {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.nuclearEnergy (dilatedNuclei S scale hscale.ne')
        (dilateState state scale hscale.ne') =
      scale * |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ *
        Coulomb.nuclearEnergy S state := by
  have hspin (spin : SpinConfiguration n) :
      (∫ x, (∑ i, Coulomb.attraction (dilatedNuclei S scale hscale.ne')
          (Coulomb.position x i)) * ‖state.value spin (scale • x)‖ ^ 2) =
        scale * |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ *
          ∫ x, (∑ i, Coulomb.attraction S (Coulomb.position x i)) *
            ‖state.value spin x‖ ^ 2 := by
    simp_rw [attraction_dilatedNuclei S hscale, ← position_smul,
      ← Finset.mul_sum, mul_assoc, integral_const_mul]
    have hi := integral_dilation (fun x =>
      (∑ i, Coulomb.attraction S (Coulomb.position x i)) *
        ‖state.value spin x‖ ^ 2) scale
    simpa only [mul_assoc] using congrArg (fun z : ℝ => scale * z) hi
  change (∑ spin, ∫ x, (∑ i, Coulomb.attraction
    (dilatedNuclei S scale hscale.ne') (Coulomb.position x i)) *
      ‖state.value spin (scale • x)‖ ^ 2) = _
  rw [Coulomb.nuclearEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spin _
  exact hspin spin

theorem nuclearEnergy_normalizedDilation {M n : ℕ} (S : Coulomb.Nuclei M)
    (state : Coulomb.H1Vector n) {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.nuclearEnergy (dilatedNuclei S scale hscale.ne')
        (normalizedDilation state scale hscale.ne') =
      scale * Coulomb.nuclearEnergy S state := by
  rw [normalizedDilation, Coulomb.nuclearEnergy_rsmul,
    nuclearEnergy_dilateState S state hscale, Real.sq_sqrt (abs_nonneg _)]
  have h := mul_inv_cancel₀ (abs_ne_zero.mpr
    (pow_ne_zero (Module.finrank ℝ (Configuration n)) hscale.ne'))
  calc
    _ = scale * (|scale ^ Module.finrank ℝ (Configuration n)| *
        |scale ^ Module.finrank ℝ (Configuration n)|⁻¹) *
          Coulomb.nuclearEnergy S state := by ring
    _ = _ := by rw [h, mul_one]

theorem pairPotential_dilation {n : ℕ} (x : Configuration n)
    {scale : ℝ} (hscale : 0 < scale) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then
      Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j) else 0) =
      scale * (∑ i : Fin n, ∑ j : Fin n, if i < j then
        Coulomb.coulombKernel (Coulomb.position (scale • x) i -
          Coulomb.position (scale • x) j) else 0) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · rw [position_smul, position_smul, ← smul_sub, coulombKernel_smul _ hscale]
    rw [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul]
  · exact (mul_zero _).symm

theorem pairEnergy_dilateState {n : ℕ} (state : Coulomb.H1Vector n)
    {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.pairEnergy (dilateState state scale hscale.ne') =
      scale * |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ *
        Coulomb.pairEnergy state := by
  have hspin (spin : SpinConfiguration n) :
      (∫ x, (∑ i : Fin n, ∑ j : Fin n, if i < j then
          Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j) else 0) *
            ‖state.value spin (scale • x)‖ ^ 2) =
        scale * |scale ^ Module.finrank ℝ (Configuration n)|⁻¹ *
          ∫ x, (∑ i : Fin n, ∑ j : Fin n, if i < j then
            Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j) else 0) *
              ‖state.value spin x‖ ^ 2 := by
    conv_lhs => enter [2, x, 1]; rw [pairPotential_dilation x hscale]
    simp_rw [mul_assoc, integral_const_mul]
    have hi := integral_dilation (fun x =>
      (∑ i : Fin n, ∑ j : Fin n, if i < j then
        Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j) else 0) *
          ‖state.value spin x‖ ^ 2) scale
    simpa only [mul_assoc] using congrArg (fun z : ℝ => scale * z) hi
  change (∑ spin, ∫ x, _ * ‖state.value spin (scale • x)‖ ^ 2) = _
  simp_rw [hspin]
  exact (Finset.mul_sum _ _ _).symm

theorem pairEnergy_normalizedDilation {n : ℕ} (state : Coulomb.H1Vector n)
    {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.pairEnergy (normalizedDilation state scale hscale.ne') =
      scale * Coulomb.pairEnergy state := by
  rw [normalizedDilation, Coulomb.pairEnergy_rsmul,
    pairEnergy_dilateState state hscale, Real.sq_sqrt (abs_nonneg _)]
  have h := mul_inv_cancel₀ (abs_ne_zero.mpr
    (pow_ne_zero (Module.finrank ℝ (Configuration n)) hscale.ne'))
  calc
    _ = scale * (|scale ^ Module.finrank ℝ (Configuration n)| *
        |scale ^ Module.finrank ℝ (Configuration n)|⁻¹) * Coulomb.pairEnergy state := by ring
    _ = _ := by rw [h, mul_one]

/-- Full electronic form under physical coordinate scaling; no projected
sector or differentiability beyond weak H¹ is used. -/
theorem form_normalizedDilation {M n : ℕ} (S : Coulomb.Nuclei M)
    (state : Coulomb.H1Vector n) {scale : ℝ} (hscale : 0 < scale) :
    Coulomb.form (dilatedNuclei S scale hscale.ne')
        (normalizedDilation state scale hscale.ne') =
      scale ^ 2 * Coulomb.kinetic state - scale * Coulomb.nuclearEnergy S state +
        scale * Coulomb.pairEnergy state := by
  rw [Coulomb.form, kinetic_normalizedDilation,
    nuclearEnergy_normalizedDilation S state hscale,
    pairEnergy_normalizedDilation state hscale]

end ContinuumCoulomb

end

end OAI
