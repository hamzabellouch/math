import Mathlib
import OAI.Geometry.BallPacking.Energy.CircularEnergy
import OAI.Geometry.BallPacking.Necessity.SquareBounds

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

theorem stdDot_I_smul_self {n : ℕ} (a : Phase n) :
    stdDot n (Complex.I • a) (Complex.I • a) = stdDot n a a := by
  change stdDot n (standardJ n a) (standardJ n a) = _
  simp only [←standardForm_J_right]
  exact (compatible_standardJ n).2.1 a (standardJ n a)

def affineError {n : ℕ} (u : ℂ → Phase n) (a : Phase n) : ℂ → Phase n :=
  fun z => u z-z • a

theorem affineError_smooth {n : ℕ} {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    ContDiff ℝ ∞ (affineError u a) := hu.sub (affine_smooth a)

theorem dirichlet_le_affineError {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n) (z : Plane) :
    dirichletDensity u z ≤ 2*dirichletDensity (affineError u a) z+4*(euclideanNorm a)^2 := by
  have he : realCurve (affineError u a) = realCurve u-realCurve (fun ζ : ℂ => ζ • a) := rfl
  have hd := fderiv_sub ((realCurve_smooth hu).differentiable (by simp) z)
    ((realCurve_smooth (affine_smooth a)).differentiable (by simp) z)
  have hx : Complex.equivRealProdCLM.symm ((1,0):Plane) = 1 := rfl
  have hy : Complex.equivRealProdCLM.symm ((0,1):Plane) = Complex.I := rfl
  unfold dirichletDensity
  rw [he,hd]
  simp only [sub_apply,realCurve_affine_fderiv,hx,hy,one_smul,euclideanNorm_sq]
  have h1 := stdDot_add_self_le (fderiv ℝ (realCurve u) z (1,0)-a) a
  have h2 := stdDot_add_self_le (fderiv ℝ (realCurve u) z (0,1)-Complex.I • a) (Complex.I • a)
  simp only [sub_add_cancel] at h1 h2
  rw [stdDot_I_smul_self] at h2
  linarith

theorem integral_constant_square (d : ℝ) (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    (∫ _ in planeSquare c r, d) = 4*r^2*d := by
  unfold planeSquare
  rw [rectangle_integral_eq_iterated continuous_const (show (c.1-r,c.2-r) ≤ (c.1+r,c.2+r) from
    ⟨by linarith,by linarith⟩)]
  simp only [intervalIntegral.integral_const,smul_eq_mul]
  ring

theorem squareEnergy_le_affineError {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n)
    (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D)
    (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    squareEnergy (realCurve u) c r ≤ 16*r^2*(euclideanNorm a)^2+2*D := by
  have hwi : IntegrableOn (dirichletDensity (affineError u a)) (planeSquare c r) := hi.integrableOn
  have hci : IntegrableOn (fun _ : Plane => 4*(euclideanNorm a)^2) (planeSquare c r) :=
    continuous_const.integrableOn_Icc
  have hb := integral_mono (μ := volume.restrict (planeSquare c r))
    ((dirichletDensity_smooth hu).continuous.integrableOn_Icc) ((hwi.const_mul 2).add hci)
    (fun z => dirichlet_le_affineError hu a z)
  change (∫ z in planeSquare c r, dirichletDensity u z) ≤
    ∫ z in planeSquare c r, 2*dirichletDensity (affineError u a) z+4*(euclideanNorm a)^2 at hb
  rw [integral_add (hwi.const_mul 2) hci,integral_const_mul,integral_constant_square _ c hr] at hb
  have hh := (setIntegral_le_integral (s := planeSquare c r) hi
    (Eventually.of_forall (dirichletDensity_nonneg (affineError u a)))).trans hD
  change (∫ z in planeSquare c r, dirichletDensity u z) ≤ _
  nlinarith

theorem sqrt_squareEnergy_le_affineError {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n)
    (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D)
    (hD0 : 0 ≤ D) (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (squareEnergy (realCurve u) c r) ≤ 4*r*euclideanNorm a+2*Real.sqrt D := by
  have hh := squareEnergy_le_affineError hu a hi hD c hr
  have ha0 := euclideanNorm_nonneg a
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (squareEnergy_nonneg _ _ _)]
  have hs := Real.sq_sqrt hD0
  nlinarith [euclideanNorm_nonneg a,Real.sqrt_nonneg D,
    mul_nonneg (mul_nonneg hr (euclideanNorm_nonneg a)) (Real.sqrt_nonneg D)]

theorem projection_squareMean_error {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n) (ℓ : Phase n →L[ℝ] ℝ)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    squareMean (fun z => ℓ (realCurve (affineError u a) z)) c r =
      squareMean (fun z => ℓ (realCurve u z)) c r-
        ℓ (realCurve (fun ζ : ℂ => ζ • a) c) := by
  have he : (fun z => ℓ (realCurve (affineError u a) z)) =
      fun z => ℓ (realCurve u z)-ℓ (realCurve (fun ζ : ℂ => ζ • a) z) := by
    funext z
    exact ℓ.map_sub _ _
  rw [he]
  have hs := squareMean_sub (f := fun z => ℓ (realCurve u z))
    (g := fun z => ℓ (realCurve (fun ζ : ℂ => ζ • a) z))
    (ℓ.continuous.comp (realCurve_smooth hu).continuous)
    (ℓ.continuous.comp (realCurve_smooth (affine_smooth a)).continuous) c r
  rw [hs,projection_squareMean_affine ℓ a c hr]


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem exists_morrey_scale {C : ℝ} (hC : 0 ≤ C) :
    ∃ k : ℕ, morreyConstant C * (Real.sqrt (decayRatio C))^k ≤ 1/16 := by
  have hlt : Real.sqrt (decayRatio C) < 1 := (Real.sqrt_lt' (by norm_num)).mpr
    (by simpa using decayRatio_lt_one hC)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) hlt).const_mul
    (morreyConstant C)
  have he : ∀ᶠ k : ℕ in atTop, morreyConstant C * (Real.sqrt (decayRatio C))^k < 1/16 :=
    ht.eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨k,hk⟩ := he.exists
  exact ⟨k,hk.le⟩

theorem projection_dyadic_bound {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet (realCurve u) z ≤ C * standardForm
      (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1)))
    (a : Phase n) (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D) (hD0 : 0 ≤ D)
    (ℓ : Phase n →L[ℝ] ℝ) (hℓ : ∀ v, (ℓ v)^2 ≤ stdDot n v v)
    (c : Plane) (k : ℕ) :
    |ℓ (realCurve u c)-squareMean (fun z => ℓ (realCurve u z)) c ((1/2:ℝ)^k)| ≤
      (morreyConstant C * (Real.sqrt (decayRatio C))^k) *
        (4*euclideanNorm a+2*Real.sqrt D) := by
  have hm := projection_point_bound (realCurve_smooth hu) hC hE ℓ hℓ c
    (show 0 < (1/2:ℝ)^k by positivity)
  have hd := Real.sqrt_le_sqrt
    (square_energy_decay_dyadic (realCurve_smooth hu) hC hE c (by norm_num : (0:ℝ)<1) k)
  have he : Real.sqrt ((decayRatio C)^k) = (Real.sqrt (decayRatio C))^k := by
    clear hm hd
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg (decayRatio_nonneg hC) k),ih,pow_succ]
  rw [one_mul,Real.sqrt_mul (pow_nonneg (decayRatio_nonneg hC) k),he] at hd
  have hb := sqrt_squareEnergy_le_affineError hu a hi hD hD0 c (by norm_num : (0:ℝ)≤1)
  simp only [mul_one] at hb
  have hh := hd.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  exact hm.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hh (morreyConstant_pos hC).le)

theorem affine_slope_bound {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet (realCurve u) z ≤ C * standardForm
      (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1)))
    (a : Phase n) (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D) (hD0 : 0 ≤ D)
    {p q : Phase n} (hp : u 0=p) (hq : u 1=q)
    (k : ℕ) (hk : morreyConstant C * (Real.sqrt (decayRatio C))^k ≤ 1/16) :
    euclideanNorm a ≤ 2*(euclideanNorm (q-p)+
      (1+2*(1+(1/2:ℝ)^k)/((1/2:ℝ)^k))*Real.sqrt D) := by
  let ℓ := phaseProjection a
  let r : ℝ := (1/2:ℝ)^k
  let B : ℝ := (morreyConstant C * (Real.sqrt (decayRatio C))^k) *
    (4*euclideanNorm a+2*Real.sqrt D)
  have hr : 0 < r := by dsimp [r]; positivity
  have h0 := projection_dyadic_bound hu hC hE a hi hD hD0 ℓ (phaseProjection_sq_le a) 0 k
  have h1 := projection_dyadic_bound hu hC hE a hi hD hD0 ℓ (phaseProjection_sq_le a) (1,0) k
  have hu0 : realCurve u 0 = p := hp
  have hu1 : realCurve u (1,0) = q := hq
  rw [hu0] at h0
  rw [hu1] at h1
  change |ℓ p-squareMean (fun z => ℓ (realCurve u z)) 0 r| ≤ B at h0
  change |ℓ q-squareMean (fun z => ℓ (realCurve u z)) (1,0) r| ≤ B at h1
  have hw := projection_translate_bound (realCurve_smooth (affineError_smooth hu a))
    ℓ (phaseProjection_sq_le a) hi hD (1,0) (by norm_num : (0:ℝ)≤1) hr
    (by norm_num) (by norm_num)
  rw [projection_squareMean_error hu a ℓ (1,0) hr,
    projection_squareMean_error hu a ℓ 0 hr] at hw
  have ha0 : realCurve (fun ζ : ℂ => ζ • a) 0 = 0 := by simp [realCurve]
  have ha1 : realCurve (fun ζ : ℂ => ζ • a) (1,0) = a := by
    change (1:ℂ) • a = a
    simp
  rw [ha0,ha1,map_zero,sub_zero] at hw
  have hla : ℓ a = euclideanNorm a := phaseProjection_self a
  rw [hla] at hw
  have hb : B ≤ euclideanNorm a/4+Real.sqrt D/8 := by
    have hh := mul_le_mul_of_nonneg_right hk
      (show 0 ≤ 4*euclideanNorm a+2*Real.sqrt D from by
        have ha := euclideanNorm_nonneg a
        positivity)
    dsimp [B]
    nlinarith
  have hpq := (le_abs_self (ℓ (q-p))).trans
    (projection_abs_le ℓ (phaseProjection_sq_le a) (q-p))
  rw [map_sub] at hpq
  have hh0 := (abs_le.mp h0).2
  have hh1 := (abs_le.mp h1).1
  have hhw := (abs_le.mp hw).1
  change euclideanNorm a ≤ 2*(euclideanNorm (q-p)+(1+2*(1+r)/r)*Real.sqrt D)
  nlinarith [Real.sqrt_nonneg D]


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem euclideanNorm_I_smul {n : ℕ} (a : Phase n) :
    euclideanNorm (Complex.I • a) = euclideanNorm a := by
  apply (sq_eq_sq₀ (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)).mp
  simp only [euclideanNorm_sq,stdDot_I_smul_self]

theorem projection_affine_abs_bound {n : ℕ} (ℓ : Phase n →L[ℝ] ℝ)
    (hℓ : ∀ a, (ℓ a)^2 ≤ stdDot n a a) (a : Phase n) (c : Plane)
    {R L : ℝ} (hR : 0 ≤ R) (hL : euclideanNorm a ≤ L)
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    |ℓ (realCurve (fun ζ : ℂ => ζ • a) c)| ≤ 2*R*L := by
  have ha := projection_abs_le ℓ hℓ a
  have hb := projection_abs_le ℓ hℓ (Complex.I • a)
  rw [euclideanNorm_I_smul] at hb
  rw [realCurve_affine_eq,map_add,map_smul,map_smul]
  change |c.1*ℓ a+c.2*ℓ (Complex.I • a)| ≤ _
  calc
    _ ≤ |c.1*ℓ a|+|c.2*ℓ (Complex.I • a)| := abs_add_le _ _
    _ ≤ R*L+R*L := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul hc1 (ha.trans hL) (abs_nonneg _) hR)
        (mul_le_mul hc2 (hb.trans hL) (abs_nonneg _) hR)
    _ = _ := by ring

theorem affine_local_bound {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet (realCurve u) z ≤ C * standardForm
      (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1)))
    (a : Phase n) (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D) (hD0 : 0 ≤ D)
    {p : Phase n} (hp : u 0=p) {L : ℝ} (hL : euclideanNorm a ≤ L)
    (c : Plane) {R : ℝ} (hR : 0 ≤ R) (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    euclideanNorm (realCurve u c-p) ≤
      2*morreyConstant C*(4*L+2*Real.sqrt D)+2*R*L+2*(R+1)*Real.sqrt D := by
  let ℓ := phaseProjection (realCurve u c-p)
  have hℓ := phaseProjection_sq_le (realCurve u c-p)
  have hpoint (d : Plane) :
      |ℓ (realCurve u d)-squareMean (fun z => ℓ (realCurve u z)) d 1| ≤
        morreyConstant C*(4*L+2*Real.sqrt D) := by
    have hm := projection_point_bound (realCurve_smooth hu) hC hE ℓ hℓ d (by norm_num : (0:ℝ)<1)
    have hb := sqrt_squareEnergy_le_affineError hu a hi hD hD0 d (by norm_num : (0:ℝ)≤1)
    have hh : Real.sqrt (squareEnergy (realCurve u) d 1) ≤ 4*L+2*Real.sqrt D := by
      simpa only [mul_one] using hb.trans (by nlinarith : 4*1*euclideanNorm a+2*Real.sqrt D ≤ _)
    exact hm.trans (mul_le_mul_of_nonneg_left hh (morreyConstant_pos hC).le)
  have hp0 : realCurve u 0 = p := hp
  have h0 := hpoint 0
  rw [hp0] at h0
  have hc := hpoint c
  have hw := projection_translate_bound (realCurve_smooth (affineError_smooth hu a))
    ℓ hℓ hi hD c hR (by norm_num : (0:ℝ)<1) hc1 hc2
  rw [projection_squareMean_error hu a ℓ c (by norm_num : (0:ℝ)<1),
    projection_squareMean_error hu a ℓ 0 (by norm_num : (0:ℝ)<1)] at hw
  have ha0 : realCurve (fun ζ : ℂ => ζ • a) 0 = 0 := by simp [realCurve]
  rw [ha0,map_zero,sub_zero,div_one] at hw
  have haf := projection_affine_abs_bound ℓ hℓ a c hR hL hc1 hc2
  have he : ℓ (realCurve u c)-ℓ p = euclideanNorm (realCurve u c-p) := by
    rw [←map_sub]
    exact phaseProjection_self _
  have h0l := (abs_le.mp h0).1
  have hcu := (abs_le.mp hc).2
  have hwu := (abs_le.mp hw).2
  have hau := (abs_le.mp haf).2
  linarith

theorem homotopy_common_affine_carrier (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) (R : ℝ) (hR : 0 < R) :
    ∃ K : Set (Phase n), IsCompact K ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
        AffineLineCurve (lineHomotopy J t) p q u →
        MapsTo u (Metric.ball (0:ℂ) (2*R)) K := by
  obtain ⟨D,hD,hDb⟩ := homotopy_affine_error_energy n hn J hJs hJ hc hs p q hpq
  obtain ⟨C,hC,hCb⟩ := homotopy_standard_energy_bound hJs hJ hc
  obtain ⟨k,hk⟩ := exists_morrey_scale hC.le
  let L := 2*(euclideanNorm (q-p)+(1+2*(1+(1/2:ℝ)^k)/((1/2:ℝ)^k))*Real.sqrt D)
  let B := 2*morreyConstant C*(4*L+2*Real.sqrt D)+2*(2*R)*L+2*(2*R+1)*Real.sqrt D
  refine ⟨(phaseEuclidean n).symm '' Metric.closedBall (phaseEuclidean n p) B,
    (isCompact_closedBall _ _).image (phaseEuclidean n).symm.continuous,?_⟩
  intro t ht u hu z hz
  obtain ⟨a,ha,hal,hai,haD⟩ := hDb t ht u hu
  have hE (w : Plane) : planarDirichlet (realCurve u) w ≤ C * standardForm
      (fderiv ℝ (realCurve u) w (1,0)) (fderiv ℝ (realCurve u) w (0,1)) := by
    change stdDot n _ _+stdDot n _ _ ≤ _
    rw [realCurve_CR (hu.2.1 _)]
    exact hCb t ht _ _
  have hL : euclideanNorm a ≤ L := affine_slope_bound hu.1 hC.le hE a hai haD hD.le
    hu.2.2.1 hu.2.2.2.1 k hk
  have hz0 : ‖z‖ < 2*R := by simpa only [Metric.mem_ball,dist_zero_right] using hz
  have hz1 : |z.re| ≤ 2*R := z.abs_re_le_norm.trans hz0.le
  have hz2 : |z.im| ≤ 2*R := z.abs_im_le_norm.trans hz0.le
  have hb := affine_local_bound hu.1 hC.le hE a hai haD hD.le hu.2.2.1 hL
    (z.re,z.im) (by linarith : 0 ≤ 2*R) hz1 hz2
  have hreal : realCurve u (z.re,z.im) = u z := by
    change u (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z)) = u z
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hreal] at hb
  refine ⟨phaseEuclidean n (u z),?_,by simp⟩
  rw [Metric.mem_closedBall,dist_eq_norm,←map_sub]
  exact hb

 
theorem uniform_affine_bound (n : ℕ) (hn : 3≤n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p≠q)
    (t : ℕ → ℝ) (ht : ∀ j, t j∈Icc (0:ℝ) 1)
    (u : ℕ → ℂ → Phase n)
    (hu : ∀ j, AffineLineCurve (lineHomotopy J (t j)) p q (u j))
    (R : ℝ) (hR : 0<R) :
    ∃ K : Set (Phase n), IsCompact K ∧
      ∀ j, MapsTo (u j) (Metric.ball (0:ℂ) (2*R)) K := by
  obtain ⟨K,hK,hKu⟩ := homotopy_common_affine_carrier n hn J hJs hJ hc hs p q hpq R hR
  exact ⟨K,hK,fun j => hKu (t j) (ht j) (u j) (hu j)⟩


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem squareMean_translate_local_bound {f dx dy e : Plane → ℝ}
    (hf : Continuous f) (hdx : Continuous dx) (hdy : Continuous dy) (he : Continuous e)
    (hfX : ∀ x y, HasDerivAt (fun s => f (s,y)) (dx (x,y)) x)
    (hfY : ∀ x y, HasDerivAt (fun s => f (x,s)) (dy (x,y)) y)
    (hxE : ∀ z, (dx z)^2 ≤ e z) (hyE : ∀ z, (dy z)^2 ≤ e z)
    {D : ℝ} (c : Plane) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hD : (∫ z in planeSquare 0 (R+r), e z) ≤ D)
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    |squareMean f c r-squareMean f 0 r| ≤ 2*(R+r)/r*Real.sqrt D := by
  let L := R+r
  have hL : 0 < L := by dsimp [L]; linarith
  have hc1' := abs_le.mp hc1
  have hc2' := abs_le.mp hc2
  let F : ℝ → ℝ := fun y => lineMean (fun x => f (x,y)) (c.1-r) (c.1+r)
  let G : ℝ → ℝ := fun y => lineMean (fun x => f (x,y)) (-r) r
  let H : ℝ → ℝ := fun y => ∫ x in -L..L, |dx (x,y)|
  let V : ℝ → ℝ := fun x => ∫ y in -L..L, |dy (x,y)|
  have hF : Continuous F := lineMean_horizontal_continuous hf _ _
  have hG : Continuous G := lineMean_horizontal_continuous hf _ _
  have hH : Continuous H := horizontal_integral_continuous hdx.abs _ _
  have hV : Continuous V := vertical_integral_continuous hdy.abs _ _
  have hH0 (y : ℝ) : 0 ≤ H y := intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => abs_nonneg _)
  have hV0 (x : ℝ) : 0 ≤ V x := intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => abs_nonneg _)
  have hFG (y : ℝ) : |F y-G y| ≤ H y :=
    lineMean_oscillation (fun x => hfX x y) (hdx.comp (continuous_id.prodMk continuous_const))
      (by linarith) (by linarith) (by dsimp [L]; linarith) (by dsimp [L]; linarith)
      (by dsimp [L]; linarith) (by dsimp [L]; linarith)
  have hab : (-L,-L) ≤ (L,L) := ⟨by linarith,by linarith⟩
  have hsquare : Icc (-L,-L) (L,L) = planeSquare 0 L := by simp [planeSquare]
  have hstep1 : |lineMean F (c.2-r) (c.2+r)-lineMean G (c.2-r) (c.2+r)| ≤
      (∫ z in planeSquare 0 L, |dx z|)/(2*r) := by
    rw [←lineMean_sub hF hG]
    apply (lineMean_abs_le _ (by linarith)).trans
    apply (lineMean_mono (hF.sub hG).abs hH (by linarith) (fun y _ => hFG y)).trans
    have hm := intervalIntegral.integral_mono_interval (μ := volume)
      (by dsimp [L]; linarith : -L ≤ c.2-r) (by linarith : c.2-r ≤ c.2+r)
      (by dsimp [L]; linarith : c.2+r ≤ L) (Eventually.of_forall hH0) (hH.intervalIntegrable (-L) L)
    change (∫ y in c.2-r..c.2+r, H y)/((c.2+r)-(c.2-r)) ≤ _
    rw [show (c.2+r)-(c.2-r)=2*r by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact hm.trans_eq (by rw [←rectangle_integral_eq_iterated_swap hdx.abs hab,hsquare])
  let F' : ℝ → ℝ := fun x => lineMean (fun y => f (x,y)) (c.2-r) (c.2+r)
  let G' : ℝ → ℝ := fun x => lineMean (fun y => f (x,y)) (-r) r
  have hF' : Continuous F' := lineMean_vertical_continuous hf _ _
  have hG' : Continuous G' := lineMean_vertical_continuous hf _ _
  have hFG' (x : ℝ) : |F' x-G' x| ≤ V x :=
    lineMean_oscillation (fun y => hfY x y) (hdy.comp (continuous_const.prodMk continuous_id))
      (by linarith) (by linarith) (by dsimp [L]; linarith) (by dsimp [L]; linarith)
      (by dsimp [L]; linarith) (by dsimp [L]; linarith)
  have hstep2 : |lineMean G (c.2-r) (c.2+r)-squareMean f 0 r| ≤
      (∫ z in planeSquare 0 L, |dy z|)/(2*r) := by
    have hs1 : lineMean G (c.2-r) (c.2+r) = lineMean F' (-r) r :=
      rectangleMean_swap (a := (-r,c.2-r)) (b := (r,c.2+r)) hf ⟨by dsimp; linarith,by dsimp; linarith⟩
    have hs2 : squareMean f 0 r = lineMean G' (-r) r := by
      simpa only [squareMean,Prod.fst_zero,Prod.snd_zero,zero_sub,zero_add] using
        rectangleMean_swap (a := (-r,-r)) (b := (r,r)) hf ⟨by dsimp; linarith,by dsimp; linarith⟩
    rw [hs1,hs2,←lineMean_sub hF' hG']
    apply (lineMean_abs_le _ (by linarith)).trans
    apply (lineMean_mono (hF'.sub hG').abs hV (by linarith) (fun x _ => hFG' x)).trans
    have hm := intervalIntegral.integral_mono_interval (μ := volume)
      (by dsimp [L]; linarith : -L ≤ -r) (by linarith : -r ≤ r)
      (by dsimp [L]; linarith : r ≤ L) (Eventually.of_forall hV0) (hV.intervalIntegrable (-L) L)
    change (∫ x in -r..r, V x)/(r-(-r)) ≤ _
    rw [show r-(-r)=2*r by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact hm.trans_eq (by rw [←rectangle_integral_eq_iterated hdy.abs hab,hsquare])
  have he0 (z : Plane) : 0 ≤ e z := (sq_nonneg (dx z)).trans (hxE z)
  have hE : (∫ z in planeSquare 0 L, e z) ≤ D := hD
  have hX := (square_integral_abs_le hdx he hxE 0 hL).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (by positivity : 0 ≤ 2*L))
  have hY := (square_integral_abs_le hdy he hyE 0 hL).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (by positivity : 0 ≤ 2*L))
  have hX' : (∫ z in planeSquare 0 L, |dx z|)/(2*r) ≤ L/r*Real.sqrt D := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ 2*L*Real.sqrt D := hX
      _ = L/r*Real.sqrt D*(2*r) := by field_simp
  have hY' : (∫ z in planeSquare 0 L, |dy z|)/(2*r) ≤ L/r*Real.sqrt D := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ 2*L*Real.sqrt D := hY
      _ = L/r*Real.sqrt D*(2*r) := by field_simp
  have ht := abs_sub_le (squareMean f c r) (lineMean G (c.2-r) (c.2+r)) (squareMean f 0 r)
  change |squareMean f c r-lineMean G (c.2-r) (c.2+r)| ≤ _ at hstep1
  calc
    _ ≤ L/r*Real.sqrt D+L/r*Real.sqrt D :=
      ht.trans (add_le_add (hstep1.trans hX') (hstep2.trans hY'))
    _ = 2*(R+r)/r*Real.sqrt D := by dsimp [L]; ring

theorem projection_translate_local_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (ℓ : Phase n →L[ℝ] ℝ)
    (hℓ : ∀ a, (ℓ a)^2 ≤ stdDot n a a)
    {D : ℝ} (c : Plane) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hD : (∫ z in planeSquare 0 (R+r), planarDirichlet v z) ≤ D)
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    |squareMean (fun z => ℓ (v z)) c r-squareMean (fun z => ℓ (v z)) 0 r| ≤
      2*(R+r)/r*Real.sqrt D := by
  apply squareMean_translate_local_bound (ℓ.continuous.comp hv.continuous)
    (ℓ.continuous.comp (planar_partial_continuous hv (1,0)))
    (ℓ.continuous.comp (planar_partial_continuous hv (0,1))) (planarDirichlet_continuous hv)
  · intro x y
    exact ℓ.hasFDerivAt.comp_hasDerivAt x
      ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
  · intro x y
    exact ℓ.hasFDerivAt.comp_hasDerivAt y
      ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
  · intro z
    exact (hℓ _).trans (le_add_of_nonneg_right (stdDot_nonneg _))
  · intro z
    exact (hℓ _).trans (le_add_of_nonneg_left (stdDot_nonneg _))
  · exact hR
  · exact hr
  · exact hD
  · exact hc1
  · exact hc2


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem planeSquare_subset_origin {c : Plane} {R r : ℝ}
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    planeSquare c r ⊆ planeSquare 0 (R+r) := by
  intro z hz
  rcases hz with ⟨⟨h11,h12⟩,⟨h21,h22⟩⟩
  have ha := abs_le.mp hc1
  have hb := abs_le.mp hc2
  change ((0:ℝ)-(R+r) ≤ z.1 ∧ (0:ℝ)-(R+r) ≤ z.2) ∧ (z.1 ≤ 0+(R+r) ∧ z.2 ≤ 0+(R+r))
  dsimp at h11 h12 h21 h22
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem squareEnergy_le_origin {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {c : Plane} {R r : ℝ}
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    squareEnergy v c r ≤ squareEnergy v 0 (R+r) :=
  setIntegral_mono_set (planarDirichlet_continuous hv).integrableOn_Icc
    (Eventually.of_forall (planarDirichlet_nonneg v)) (planeSquare_subset_origin hc1 hc2).eventuallyLE

theorem marked_distance_le_energy {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1))) :
    euclideanNorm (v (1,0)-v 0) ≤ (2*morreyConstant C+4)*Real.sqrt (squareEnergy v 0 2) := by
  let ℓ := phaseProjection (v (1,0)-v 0)
  have hℓ := phaseProjection_sq_le (v (1,0)-v 0)
  have h0 := projection_point_bound hv hC hE ℓ hℓ 0 (by norm_num : (0:ℝ)<1)
  have h1 := projection_point_bound hv hC hE ℓ hℓ (1,0) (by norm_num : (0:ℝ)<1)
  have hb0 : squareEnergy v 0 1 ≤ squareEnergy v 0 2 := by
    simpa only [show (1:ℝ)+1=2 by norm_num] using squareEnergy_le_origin hv
      (c := 0) (r := 1) (by norm_num : |(0:Plane).1| ≤ 1) (by norm_num)
  have hb1 : squareEnergy v (1,0) 1 ≤ squareEnergy v 0 2 := by
    simpa only [show (1:ℝ)+1=2 by norm_num] using squareEnergy_le_origin hv
      (c := (1,0)) (r := 1) (by norm_num : |((1,0):Plane).1| ≤ 1) (by norm_num)
  have h0' := h0.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb0) (morreyConstant_pos hC).le)
  have h1' := h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb1) (morreyConstant_pos hC).le)
  have ht := projection_translate_local_bound hv ℓ hℓ (1,0)
    (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)<1)
    (le_refl (squareEnergy v 0 (1+1))) (by norm_num) (by norm_num)
  norm_num only [add_self_div_two,one_add_one_eq_two,div_one,show (2:ℝ)*2=4 by norm_num] at ht
  have he : ℓ (v (1,0))-ℓ (v 0) = euclideanNorm (v (1,0)-v 0) := by
    rw [←map_sub]
    exact phaseProjection_self _
  have h01 := (abs_le.mp h0').1
  have h11 := (abs_le.mp h1').2
  have ht1 := (abs_le.mp ht).2
  linarith

theorem scaled_sqrt_energy_bound {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet (realCurve u) z ≤ C * standardForm
      (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1)))
    (a : Phase n) (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D) (hD0 : 0 ≤ D) (k : ℕ) :
    Real.sqrt (squareEnergy (realCurve u) 0 2) ≤
      8*(2:ℝ)^k*euclideanNorm a+2*(Real.sqrt (decayRatio C))^k*Real.sqrt D := by
  have hd := Real.sqrt_le_sqrt (square_energy_decay_dyadic (realCurve_smooth hu) hC hE 0
    (show 0 < 2*(2:ℝ)^k by positivity) k)
  have hp : 2*(2:ℝ)^k*(1/2:ℝ)^k=2 := by rw [mul_assoc,←mul_pow]; norm_num
  have he (j : ℕ) : Real.sqrt ((decayRatio C)^j) = (Real.sqrt (decayRatio C))^j := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg (decayRatio_nonneg hC) j),ih,pow_succ]
  rw [hp,Real.sqrt_mul (pow_nonneg (decayRatio_nonneg hC) k),he] at hd
  have huB := sqrt_squareEnergy_le_affineError hu a hi hD hD0 0 (by positivity : 0 ≤ 2*(2:ℝ)^k)
  have hs1 : (Real.sqrt (decayRatio C))^k ≤ 1 := pow_le_one₀ (Real.sqrt_nonneg _)
    (by apply (Real.sqrt_le_one).mpr; exact (decayRatio_lt_one hC).le)
  have hmul := mul_le_mul_of_nonneg_left huB (by positivity : 0 ≤ (Real.sqrt (decayRatio C))^k)
  have ha := euclideanNorm_nonneg a
  have hpow := pow_nonneg (by norm_num : (0:ℝ)≤2) k
  have hm := mul_le_mul_of_nonneg_right hs1 (show 0 ≤ 8*(2:ℝ)^k*euclideanNorm a by positivity)
  nlinarith

theorem exists_positive_slope_bound {C D d : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D) (hd : 0 < d) :
    ∃ m > 0, ∀ A : ℝ, 0 ≤ A →
      (∀ k : ℕ, d ≤ (2*morreyConstant C+4)*
        (8*(2:ℝ)^k*A+2*(Real.sqrt (decayRatio C))^k*Real.sqrt D)) → m ≤ A := by
  let H := 2*morreyConstant C+4
  have hH : 0 < H := by dsimp [H]; have := morreyConstant_pos hC; linarith
  have hs1 : Real.sqrt (decayRatio C) < 1 := (Real.sqrt_lt' (by norm_num)).mpr
    (by simpa using decayRatio_lt_one hC)
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) hs1).const_mul
    (2*H)).mul_const (Real.sqrt D)
  have hev : ∀ᶠ k : ℕ in atTop, (2*H)*(Real.sqrt (decayRatio C))^k*Real.sqrt D < d/2 :=
    ht.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨k,hk⟩ := hev.exists
  refine ⟨d/(16*H*(2:ℝ)^k),by positivity,?_⟩
  intro A hA hb
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := hb k
  change d ≤ H*(8*(2:ℝ)^k*A+2*(Real.sqrt (decayRatio C))^k*Real.sqrt D) at hh
  nlinarith

theorem homotopy_slopes_bounded_below (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) :
    ∃ m > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u →
      ∃ a : Phase n, m ≤ euclideanNorm a ∧
        Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) := by
  obtain ⟨D,hD,hDb⟩ := homotopy_affine_error_energy n hn J hJs hJ hc hs p q hpq
  obtain ⟨C,hC,hCb⟩ := homotopy_standard_energy_bound hJs hJ hc
  have hd : 0 < euclideanNorm (q-p) := by
    apply norm_pos_iff.mpr
    intro hh
    have he : q-p=0 := (phaseEuclidean n).injective (hh.trans (map_zero _).symm)
    exact hpq (sub_eq_zero.mp he).symm
  obtain ⟨m,hm,hmb⟩ := exists_positive_slope_bound hC.le hD.le hd
  refine ⟨m,hm,?_⟩
  intro t ht u hu
  obtain ⟨a,ha,hal,hai,haD⟩ := hDb t ht u hu
  refine ⟨a,?_,hal⟩
  apply hmb _ (euclideanNorm_nonneg a)
  intro k
  have hE (w : Plane) : planarDirichlet (realCurve u) w ≤ C * standardForm
      (fderiv ℝ (realCurve u) w (1,0)) (fderiv ℝ (realCurve u) w (0,1)) := by
    change stdDot n _ _+stdDot n _ _ ≤ _
    rw [realCurve_CR (hu.2.1 _)]
    exact hCb t ht _ _
  have hh := marked_distance_le_energy (realCurve_smooth hu.1) hC.le hE
  have hp0 : realCurve u 0 = p := hu.2.2.1
  have hq1 : realCurve u (1,0) = q := hu.2.2.2.1
  rw [hp0,hq1] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (scaled_sqrt_energy_bound hu.1 hC.le hE
    a hai haD hD.le k) (by have := morreyConstant_pos hC.le; linarith))

end HigherDimensionalBallPacking.Rigidity

end

end OAI
