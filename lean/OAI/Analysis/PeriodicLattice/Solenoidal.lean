import OAI.Analysis.PeriodicLattice.MeanBounds

namespace OAI

/-! Pressure potentials, solenoidal forcing and the analytic lattice conclusion. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingSolenoidal {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace FluidLift

open scoped ContDiff
open TorusCalculus RapidCalculus

def doubleSlope (z : ℝ) : ℝ := 2 * slope z ^ 2 - 1

theorem doubleSlope_contDiff : ContDiff ℝ ∞ doubleSlope :=
  ((contDiff_const.mul (slope_contDiff.pow 2)).sub contDiff_const)

theorem doubleSlope_periodic : Function.Periodic doubleSlope 1 := by
  intro z
  simp only [doubleSlope, slope_periodic z]

theorem slope_hasDerivAt (z : ℝ) :
    HasDerivAt slope (-(2 * Real.pi)^2 * eta z) z := by
  have h := (((hasDerivAt_id z).sub_const (1 / 2)).const_mul (2 * Real.pi)).cos
  simp only [id_eq, mul_one] at h
  change HasDerivAt slope (-Real.sin (2 * Real.pi * (z - 1 / 2)) * (2 * Real.pi)) z at h
  convert h using 1
  dsimp only [eta]
  field_simp

@[simp] theorem eta_deriv : deriv eta = slope := funext (fun z => (eta_hasDerivAt z).deriv)
@[simp] theorem slope_deriv : deriv slope = fun z => -(2 * Real.pi)^2 * eta z :=
  funext (fun z => (slope_hasDerivAt z).deriv)

theorem vertical_energy (z : ℝ) : slope z ^ 2 + (2 * Real.pi)^2 * eta z ^ 2 = 1 := by
  dsimp only [slope, eta]
  rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero 2 (mul_ne_zero (by norm_num) Real.pi_ne_zero))]
  exact Real.cos_sq_add_sin_sq _

theorem doubleSlope_second (z : ℝ) :
    deriv (deriv doubleSlope) z = -(4 * Real.pi)^2 * doubleSlope z := by
  have h₁ (z : ℝ) : HasDerivAt doubleSlope (4 * slope z * (-(2 * Real.pi)^2 * eta z)) z := by
    convert (((slope_hasDerivAt z).pow 2).const_mul 2).sub_const 1 using 1 <;> first | rfl | ring
  have he : deriv doubleSlope = fun z => 4 * slope z * (-(2 * Real.pi)^2 * eta z) :=
    funext fun z => (h₁ z).deriv
  rw [he, (((slope_hasDerivAt z).const_mul 4).fun_mul
    ((eta_hasDerivAt z).const_mul (-(2 * Real.pi)^2))).deriv]
  have hv := vertical_energy z
  dsimp [doubleSlope]
  nlinarith [hv]

def pressureSource (d : Input) (t y : ℝ) : ℝ :=
  bdy d t y * bdy d t y - b d t y * biD false (bdy d) t y

theorem pressureSource_contDiff (d : Input) :
    ContDiff ℝ ∞ (Function.uncurry (pressureSource d)) :=
  ((bdy_contDiff d).mul (bdy_contDiff d)).sub
    ((b_contDiff d).mul (partial_contDiff (bdy_contDiff d) false))

theorem pressureSource_periodic (d : Input) (t : ℝ) :
    Function.Periodic (pressureSource d t) 1 :=
  ((bdy_periodic d t).mul (bdy_periodic d t)).sub
    ((b_periodic d t).mul (periodic_deriv (bdy_periodic d t)))

theorem pressureSource_rapid (d : Input) (hd : d.WellFormed) : Rapid2 (pressureSource d) :=
  (((b_rapid2 d hd).biD false).mul ((b_rapid2 d hd).biD false)).sub
    ((b_rapid2 d hd).mul (((b_rapid2 d hd).biD false).biD false))

end FluidLift

namespace RapidCalculus

open scoped ContDiff
open TorusCalculus

theorem tensor_contDiff {F : ScalarField} {f : ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (hh : ContDiff ℝ ∞ h)
    (he : ∀ t x, F t (torusMk x) = h (x 2) * f t (x 1)) : ContDiff ℝ ∞ (lifted F) := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun tx : ℝ × Space => tx.2 i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff.comp contDiff_snd
  change ContDiff ℝ ∞ (fun tx : ℝ × Space => F tx.1 (torusMk tx.2))
  simp_rw [he]
  exact (hh.comp (hc 2)).mul (hf.comp (contDiff_fst.prodMk (hc 1)))

theorem tensor_laplacian {F : ScalarField} {f : ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (hh : ContDiff ℝ ∞ h)
    (he : ∀ t x, F t (torusMk x) = h (x 2) * f t (x 1)) (t : ℝ) (x : Space) :
    laplacian F t (torusMk x) = h (x 2) * biD false (biD false f) t (x 1) +
      deriv (deriv h) (x 2) * f t (x 1) := by
  have h₁ := tensor_spaceD_one hf he
  have h₂ := tensor_spaceD_two hh he
  have hh' : ContDiff ℝ ∞ (deriv h) := by simpa using ContDiff.iterate_deriv 1 hh
  simp only [laplacian, Fin.sum_univ_three, tensor_spaceD_zero he, Residual.spaceD_zero, Pi.zero_apply,
    zero_add, tensor_spaceD_one (partial_contDiff hf false) h₁, tensor_spaceD_two hh' h₂]

end RapidCalculus

namespace FluidLift

open scoped ContDiff
open TorusCalculus RapidCalculus PeriodicInverse MeasureTheory

def pressureBase (d : Input) (t y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (b d t y * b d t y - mean (fun t y => b d t y * b d t y) t y)

theorem pressureBase_contDiff (d : Input) : ContDiff ℝ ∞ (Function.uncurry (pressureBase d)) :=
  contDiff_const.mul (((b_contDiff d).mul (b_contDiff d)).sub
    (mean_contDiff ((b_contDiff d).mul (b_contDiff d))))

theorem pressureBase_periodic (d : Input) (t : ℝ) : Function.Periodic (pressureBase d t) 1 := by
  intro y
  simp only [pressureBase, b_periodic d t y, mean]

theorem pressureBase_rapid (d : Input) (hd : d.WellFormed) : Rapid2 (pressureBase d) :=
  (((b_rapid2 d hd).mul (b_rapid2 d hd)).sub
    (mean_rapid ((b_rapid2 d hd).mul (b_rapid2 d hd)))).scale (1 / 2)

theorem pressureBase_deriv (d : Input) :
    biD false (pressureBase d) = fun t y => b d t y * bdy d t y := by
  funext t y
  have hh := (((b_hasDerivAt d t y).fun_mul (b_hasDerivAt d t y)).sub_const
    (mean (fun t y => b d t y * b d t y) t y)).const_mul (1 / 2)
  have he : (1 / 2 : ℝ) * (bdy d t y * b d t y + b d t y * bdy d t y) = b d t y * bdy d t y := by ring
  change deriv (fun z => (1 / 2 : ℝ) * (b d t z * b d t z - ∫ s in (0 : ℝ)..1, b d t s * b d t s)) y = _
  simpa only [he, mean] using hh.deriv

theorem pressureBase_second (d : Input) (t y : ℝ) :
    biD false (biD false (pressureBase d)) t y =
      bdy d t y * bdy d t y + b d t y * biD false (bdy d) t y := by
  rw [pressureBase_deriv]
  exact ((b_hasDerivAt d t y).fun_mul
    (((bdy_contDiff d).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y).hasDerivAt).deriv

def pressureMode (d : Input) := screened (4 * Real.pi) (pressureSource d)

theorem pressureMode_contDiff (d : Input) : ContDiff ℝ ∞ (Function.uncurry (pressureMode d)) :=
  screened_contDiff (4 * Real.pi) (pressureSource_contDiff d)

theorem pressureMode_periodic (d : Input) : ∀ t, Function.Periodic (pressureMode d t) 1 :=
  screened_periodic (4 * Real.pi) (pressureSource_periodic d)

theorem pressureMode_rapid (d : Input) (hd : d.WellFormed) : Rapid2 (pressureMode d) :=
  screened_rapid (4 * Real.pi) (pressureSource_rapid d hd)

def pressureOsc (d : Input) : ScalarField := fun t q =>
  doubleSlope_periodic.lift (q 2) * (pressureMode_periodic d t).lift (q 1)

@[simp] theorem pressureOsc_cover (d : Input) (t : ℝ) (x : Space) :
    pressureOsc d t (torusMk x) = doubleSlope (x 2) * pressureMode d t (x 1) := by
  simp only [pressureOsc, torusMk, Function.Periodic.lift_coe]

theorem pressureOsc_contDiff (d : Input) : ContDiff ℝ ∞ (lifted (pressureOsc d)) :=
  tensor_contDiff (pressureMode_contDiff d) doubleSlope_contDiff (pressureOsc_cover d)

theorem pressureOsc_algebra (d : Input) (hd : d.WellFormed) : Algebra (pressureOsc d) :=
  Algebra.tensor _ _ _ (pressureMode_rapid d hd)
    (boundedProfile_of_periodic doubleSlope_contDiff doubleSlope_periodic) (pressureOsc_cover d)

def potential (d : Input) : ScalarField :=
  horizontal (pressureBase d) (pressureBase_periodic d) + pressureOsc d

theorem potential_contDiff (d : Input) : ContDiff ℝ ∞ (lifted (potential d)) :=
  (horizontal_contDiff (pressureBase_periodic d) (pressureBase_contDiff d)).add (pressureOsc_contDiff d)

theorem potential_algebra (d : Input) (hd : d.WellFormed) : Algebra (potential d) :=
  (horizontal_algebra (pressureBase_periodic d) (pressureBase_rapid d hd)).add (pressureOsc_algebra d hd)

theorem potential_meanZero (d : Input) : MeanZero (potential d) := by
  have ho (t : ℝ) : (∫ q, pressureOsc d t q ∂torusVolume) = 0 := by
    have he : spaceD 2 (spaceD 2 (pressureOsc d)) = -(4 * Real.pi)^2 • pressureOsc d := by
      funext t q
      obtain ⟨x, rfl⟩ := mk_surjective q
      rw [tensor_spaceD_two (show ContDiff ℝ ∞ (deriv doubleSlope) from
        ContDiff.iterate_deriv 1 doubleSlope_contDiff)
        (tensor_spaceD_two doubleSlope_contDiff (pressureOsc_cover d)), doubleSlope_second]
      change -(4 * Real.pi)^2 * doubleSlope (x 2) * pressureMode d t (x 1) =
        -(4 * Real.pi)^2 * (doubleSlope (x 2) * pressureMode d t (x 1))
      ring
    have hi := integral_spaceD (contDiff_spaceD (pressureOsc_contDiff d) 2) t 2
    rw [he] at hi
    change (∫ q, -(4 * Real.pi)^2 * pressureOsc d t q ∂torusVolume) = 0 at hi
    rw [integral_const_mul] at hi
    exact (mul_eq_zero.mp hi).resolve_left (neg_ne_zero.mpr (pow_ne_zero 2 (mul_ne_zero (by norm_num) Real.pi_ne_zero)))
  intro t ht
  change (∫ q, horizontal (pressureBase d) (pressureBase_periodic d) t q + pressureOsc d t q ∂torusVolume) = 0
  rw [integral_add (smooth_slice_integrable
    (horizontal_contDiff (pressureBase_periodic d) (pressureBase_contDiff d)) t)
    (smooth_slice_integrable (pressureOsc_contDiff d) t), ho, add_zero,
    horizontal_integral (pressureBase_periodic d) (pressureBase_contDiff d)]
  have hi : IntervalIntegrable (fun y => b d t y * b d t y) volume 0 1 :=
    (((b_contDiff d).mul (b_contDiff d)).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  simp only [pressureBase, mean, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hi (intervalIntegrable_const), intervalIntegral.integral_const,
    sub_zero, one_smul, sub_self, mul_zero]

end FluidLift

namespace TorusCalculus
open scoped ContDiff

section Addition
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem spaceD_add_eq {F G : Field A} (hF : ContDiff ℝ ∞ (lifted F))
    (hG : ContDiff ℝ ∞ (lifted G)) (i : Fin 3) :
    spaceD i (F + G) = spaceD i F + spaceD i G := by
  funext t q
  exact spaceD_add (smooth_slice_differentiable hF t) (smooth_slice_differentiable hG t) i q

theorem laplacian_add {F G : Field A} (hF : ContDiff ℝ ∞ (lifted F))
    (hG : ContDiff ℝ ∞ (lifted G)) : laplacian (F + G) = laplacian F + laplacian G := by
  simp only [laplacian_as_sum, spaceD_add_eq hF hG,
    spaceD_add_eq (contDiff_spaceD hF _) (contDiff_spaceD hG _), Finset.sum_add_distrib]

end Addition

end TorusCalculus

namespace FluidLift

open scoped ContDiff
open TorusCalculus RapidCalculus PeriodicInverse

theorem force_divergence (ν : ℝ) (d : Input) (t : ℝ) (x : Space) :
    divergence (force ν d) t (torusMk x) =
      bdy d t (x 1) * bdy d t (x 1) + b d t (x 1) * biD false (bdy d) t (x 1) +
        doubleSlope (x 2) * pressureSource d t (x 1) := by
  have hdiv : divergence (velocity d) = 0 := funext fun t => funext fun q => divergence_zero d t q
  change divergence (Residual.fullForce ν (velocity d)) t (torusMk x) = _
  rw [divergence_fullForce (velocity_contDiff d) hdiv,
    divergence_advection (velocity_contDiff d) hdiv]
  have hzero (j : Fin 3) : spaceD 0 (fun t q => velocity d t q j) = 0 := by
    fin_cases j
    · exact tensor_spaceD_zero (f := a d) (h := slope) (fun t x => by simp only [velocity_cover]; rfl)
    · exact tensor_spaceD_zero (f := b d) (h := slope) (fun t x => by simp only [velocity_cover]; rfl)
    · exact tensor_spaceD_zero (f := bdy d) (h := fun z => -eta z) (fun t x => by simp only [velocity_cover]; rfl)
  have hc₁ : ∀ t x, (velocity d t (torusMk x)) 1 = slope (x 2) * b d t (x 1) := by
    intro t x
    simp only [velocity_cover]; rfl
  have hc₂ : ∀ t x, (velocity d t (torusMk x)) 2 = (-eta (x 2)) * bdy d t (x 1) := by
    intro t x
    simp only [velocity_cover]; rfl
  simp only [Fin.sum_univ_three, hzero, Pi.zero_apply, zero_mul, mul_zero, zero_add, add_zero,
    tensor_spaceD_one (F := fun t q => velocity d t q 1) (h := slope) (b_contDiff d) hc₁, tensor_spaceD_one (F := fun t q => velocity d t q 2) (h := fun z => -eta z) (bdy_contDiff d) hc₂,
    tensor_spaceD_two (F := fun t q => velocity d t q 1) (f := b d) slope_contDiff hc₁, tensor_spaceD_two (F := fun t q => velocity d t q 2) (f := bdy d) eta_contDiff.neg hc₂,
    slope_deriv, deriv.fun_neg, eta_deriv]
  change slope (x 2) * bdy d t (x 1) * (slope (x 2) * bdy d t (x 1)) +
      -eta (x 2) * biD false (bdy d) t (x 1) * (-(2 * Real.pi)^2 * eta (x 2) * b d t (x 1)) +
      (-(2 * Real.pi)^2 * eta (x 2) * b d t (x 1) * (-eta (x 2) * biD false (bdy d) t (x 1)) +
        -slope (x 2) * bdy d t (x 1) * (-slope (x 2) * bdy d t (x 1))) = _
  dsimp only [doubleSlope, pressureSource]
  linear_combination 2 * b d t (x 1) * biD false (bdy d) t (x 1) * vertical_energy (x 2)

theorem potential_poisson (ν : ℝ) (d : Input) (t : ℝ) (q : Torus) :
    laplacian (potential d) t q = divergence (force ν d) t q := by
  obtain ⟨x, rfl⟩ := mk_surjective q
  have hb : ∀ t x, horizontal (pressureBase d) (pressureBase_periodic d) t (torusMk x) =
      1 * pressureBase d t (x 1) := fun t x => by simp
  rw [potential, laplacian_add (horizontal_contDiff (pressureBase_periodic d) (pressureBase_contDiff d))
    (pressureOsc_contDiff d)]
  change laplacian (horizontal (pressureBase d) (pressureBase_periodic d)) t (torusMk x) +
      laplacian (pressureOsc d) t (torusMk x) = _
  rw [tensor_laplacian (pressureBase_contDiff d) contDiff_const hb,
    tensor_laplacian (pressureMode_contDiff d) doubleSlope_contDiff (pressureOsc_cover d),
    pressureBase_second, doubleSlope_second]
  have hs := screened_equation (4 * Real.pi) (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (pressureSource_contDiff d) (pressureSource_periodic d) t (x 1)
  change biD false (biD false (pressureMode d)) t (x 1) =
    (4 * Real.pi)^2 * pressureMode d t (x 1) + pressureSource d t (x 1) at hs
  rw [hs, force_divergence]
  have hd (c : ℝ) : deriv (fun _ : ℝ => c) = fun _ => 0 := by funext z; exact deriv_const z c
  simp only [hd, one_mul, zero_mul, add_zero]
  ring

end FluidLift

namespace TorusCalculus

open scoped ContDiff
open MeasureTheory

theorem contDiff_gradient {p : ScalarField} (hp : ContDiff ℝ ∞ (lifted p)) :
    ContDiff ℝ ∞ (lifted (gradient p)) :=
  (contDiff_piLp _).mpr (fun i => contDiff_spaceD hp i)

theorem divergence_gradient (p : ScalarField) : divergence (gradient p) = laplacian p := rfl

theorem gradient_neg {p : ScalarField} : gradient (-p) = -gradient p := by
  funext t q
  ext i
  exact deriv.neg

theorem integral_gradient {p : ScalarField} (hp : ContDiff ℝ ∞ (lifted p)) (t : ℝ) :
    (∫ q, gradient p t q ∂torusVolume) = 0 := by
  ext i
  have hi := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).integral_comp_comm
    (smooth_slice_integrable (contDiff_gradient hp) t)
  simpa only [PiLp.proj_apply, gradient, WithLp.toLp_ofLp, PiLp.zero_apply] using
    hi.symm.trans (integral_spaceD hp t i)

theorem classical_of_smooth_pressure {ν : ℝ} {F U : VectorField} {p : ScalarField}
    (hU : ContDiff ℝ ∞ (lifted U)) (hp : ContDiff ℝ ∞ (lifted p))
    (hm : MeanZero p) (hNS : NavierStokes ν F U p) : ClassicalSolution ν F U p where
  velocityContinuous := cylinderContinuous hU
  timeDifferentiable := by
    intro t _ht q
    obtain ⟨x, rfl⟩ := mk_surjective q
    exact (((hU.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)) t).differentiableWithinAt
  timeContinuous := timeD_cylinderContinuous hU
  spaceTwiceDifferentiable := fun _t _ht =>
    (hU.comp (contDiff_const.prodMk contDiff_id)).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  spaceFirstContinuous := fun i => cylinderContinuous (contDiff_spaceD hU i)
  spaceSecondContinuous := fun i j => cylinderContinuous (contDiff_spaceD (contDiff_spaceD hU j) i)
  pressureContinuous := cylinderContinuous hp
  pressureDifferentiable := fun t _ => smooth_slice_differentiable hp t
  pressureGradientContinuous := cylinderContinuous (contDiff_gradient hp)
  pressureMeanZero := hm
  equations := hNS

end TorusCalculus

namespace FluidLift

open scoped ContDiff
open TorusCalculus RapidCalculus MeasureTheory

def solenoidalForce (ν : ℝ) (d : Input) : VectorField := force ν d - gradient (potential d)

theorem solenoidalForce_contDiff (ν : ℝ) (d : Input) :
    ContDiff ℝ ∞ (lifted (solenoidalForce ν d)) :=
  (force_contDiff ν d).sub (contDiff_gradient (potential_contDiff d))

theorem solenoidalForce_solenoidal (ν : ℝ) (d : Input) : Solenoidal (solenoidalForce ν d) := by
  intro t ht q
  rw [solenoidalForce, divergence_sub (smooth_slice_differentiable (force_contDiff ν d) t)
    (smooth_slice_differentiable (contDiff_gradient (potential_contDiff d)) t),
    ← Pi.sub_apply, ← Pi.sub_apply, divergence_gradient]
  change divergence (force ν d) t q - laplacian (potential d) t q = 0
  rw [potential_poisson, sub_self]

theorem solenoidalForce_meanZero (ν : ℝ) (d : Input) : MeanZero (solenoidalForce ν d) := by
  intro t ht
  change (∫ q, force ν d t q - gradient (potential d) t q ∂torusVolume) = 0
  rw [integral_sub (smooth_slice_integrable (force_contDiff ν d) t)
    (smooth_slice_integrable (contDiff_gradient (potential_contDiff d)) t),
    force_meanZero ν d t ht, integral_gradient (potential_contDiff d) t, sub_self]

theorem solenoidalForce_equations (ν : ℝ) (d : Input) :
    NavierStokes ν (solenoidalForce ν d) (velocity d) (-potential d) := by
  refine ⟨?_, (equations ν d).2⟩
  intro t ht q
  rw [(equations ν d).1 t ht q, Residual.gradient_zero, Pi.zero_apply, Pi.zero_apply,
    neg_zero, zero_add, gradient_neg]
  change ν • laplacian (velocity d) t q + force ν d t q =
    -(-gradient (potential d) t q) + ν • laplacian (velocity d) t q +
      (force ν d t q - gradient (potential d) t q)
  abel

theorem solenoidalForce_classical_solution (ν : ℝ) (d : Input) :
    ClassicalSolution ν (solenoidalForce ν d) (velocity d) (-potential d) := by
  refine classical_of_smooth_pressure (velocity_contDiff d) (potential_contDiff d).neg ?_
    (solenoidalForce_equations ν d)
  intro t ht
  change (∫ q, -potential d t q ∂torusVolume) = 0
  rw [integral_neg, potential_meanZero d t ht, neg_zero]

theorem gradient_algebra {p : ScalarField} (hp : Algebra p) : VectorAlgebra (gradient p) :=
  fun i => hp.spaceDeriv i

theorem solenoidalForce_algebra (ν : ℝ) (d : Input) (hd : d.WellFormed) :
    VectorAlgebra (solenoidalForce ν d) :=
  ((velocity_algebra d hd).fullForce ν).sub (gradient_algebra (potential_algebra d hd))

end FluidLift

namespace RapidCalculus

theorem RapidPair.mono {U F : VectorField} {C D : ℕ → MultiIndex → ℕ → ℕ}
    (hC : RapidPair U F C) (hCD : ∀ r α J, C r α J ≤ D r α J) : RapidPair U F D := by
  intro r J α t ht
  exact (hC r J α t ht).trans (div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (hCD r α J)) (by positivity))

end RapidCalculus

namespace FluidLift

open scoped ContDiff
open TorusCalculus RapidCalculus

theorem analytic_lattice_conclusion (ν : ℝ) (hν : 0 ≤ ν) (d : Input) (hd : d.WellFormed) :
    ∃ C : ℕ → MultiIndex → ℕ → ℕ,
      LatticeConclusion ν d (velocity d) (force ν d) (solenoidalForce ν d) (potential d) C := by
  obtain ⟨Cg, hg⟩ := force_rapid ν d hd
  obtain ⟨Cf, hf⟩ := rapidPair_of_algebra (velocity_algebra d hd) (solenoidalForce_algebra ν d hd)
  refine ⟨fun r α J => max (Cg r α J) (Cf r α J),
    velocity_smooth d, force_smooth ν d, (solenoidalForce_contDiff ν d).contDiffOn,
    (potential_contDiff d).contDiffOn, velocity_meanZero d, force_meanZero ν d,
    solenoidalForce_meanZero ν d, potential_meanZero d, classical_solution ν d,
    solenoidalForce_classical_solution ν d, RapidPair.mono hg (fun _ _ _ => le_max_left _ _),
    RapidPair.mono hf (fun _ _ _ => le_max_right _ _), solenoidalForce_solenoidal ν d,
    fun t _ q => potential_poisson ν d t q, ?_, fun _ _ _ => rfl,
    force_classical_unique ν hν d, classical_unique hν (solenoidalForce_classical_solution ν d),
    path d, path_isParticle d hd, fun _Y hY _t ht => path_unique d hd hY ht, path_event_iff d hd⟩
  exact poisson_unique (fun t _ => ((potential_contDiff d).comp
    (contDiff_const.prodMk contDiff_id)).of_le (by exact WithTop.coe_le_coe.mpr le_top))
    (potential_meanZero d) (fun t _ q => potential_poisson ν d t q)

end FluidLift

end
end PeriodicLattice

end OAI
