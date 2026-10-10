import Mathlib
import OAI.Geometry.BallPacking.Necessity.AffineSlopes
import OAI.Geometry.BallPacking.Necessity.TangentLimits

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

theorem projection_mean_double_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (ℓ : Phase n →L[ℝ] ℝ)
    (hℓ : ∀ a, (ℓ a)^2 ≤ stdDot n a a)
    (hi : Integrable (planarDirichlet v)) {D : ℝ} (hD : (∫ z, planarDirichlet v z) ≤ D)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    |squareMean (fun z => ℓ (v z)) c r-squareMean (fun z => ℓ (v z)) c (2*r)| ≤
      4*Real.sqrt D := by
  have hh : |squareMean (fun z => ℓ (v z)) c ((2*r)/2)-
      squareMean (fun z => ℓ (v z)) c (2*r)| ≤ 4*Real.sqrt (squareEnergy v c (2*r)) := by
    apply squareMean_half_bound (ℓ.continuous.comp hv.continuous)
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
    · positivity
  rw [show (2*r)/2=r by ring] at hh
  have hb : squareEnergy v c (2*r) ≤ D :=
    (setIntegral_le_integral hi (Eventually.of_forall (planarDirichlet_nonneg v))).trans hD
  exact hh.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb) (by norm_num))

theorem projection_mean_grow_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (ℓ : Phase n →L[ℝ] ℝ)
    (hℓ : ∀ a, (ℓ a)^2 ≤ stdDot n a a)
    (hi : Integrable (planarDirichlet v)) {D : ℝ} (hD : (∫ z, planarDirichlet v z) ≤ D)
    (c : Plane) (k : ℕ) :
    |squareMean (fun z => ℓ (v z)) c 1-squareMean (fun z => ℓ (v z)) c ((2:ℝ)^k)| ≤
      4*(k:ℝ)*Real.sqrt D := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := projection_mean_double_bound hv ℓ hℓ hi hD c (show 0 < (2:ℝ)^k by positivity)
    have ht := abs_sub_le (squareMean (fun z => ℓ (v z)) c 1)
      (squareMean (fun z => ℓ (v z)) c ((2:ℝ)^k))
      (squareMean (fun z => ℓ (v z)) c ((2:ℝ)^(k+1)))
    have he : (2:ℝ)^(k+1)=2*(2:ℝ)^k := by rw [pow_succ]; ring
    rw [he] at ht ⊢
    rw [Nat.cast_add,Nat.cast_one]
    linarith

theorem projection_error_point_bound {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet (realCurve u) z ≤ C * standardForm
      (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1)))
    (a : Phase n) (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D) (hD0 : 0 ≤ D)
    (ℓ : Phase n →L[ℝ] ℝ) (hℓ : ∀ v, (ℓ v)^2 ≤ stdDot n v v) (c : Plane) :
    |ℓ (realCurve (affineError u a) c)-squareMean (fun z => ℓ (realCurve (affineError u a) z)) c 1| ≤
      morreyConstant C*(4*euclideanNorm a+2*Real.sqrt D) := by
  have hp := projection_point_bound (realCurve_smooth hu) hC hE ℓ hℓ c (by norm_num : (0:ℝ)<1)
  have hb := sqrt_squareEnergy_le_affineError hu a hi hD hD0 c (by norm_num : (0:ℝ)≤1)
  simp only [mul_one] at hb
  have hh := hp.trans (mul_le_mul_of_nonneg_left hb (morreyConstant_pos hC).le)
  rw [projection_squareMean_error hu a ℓ c (by norm_num : (0:ℝ)<1)]
  have he : ℓ (realCurve (affineError u a) c) = ℓ (realCurve u c)-ℓ (realCurve (fun z : ℂ => z • a) c) :=
    ℓ.map_sub _ _
  rw [he,sub_sub_sub_cancel_right]
  exact hh

theorem affine_error_log_bound {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet (realCurve u) z ≤ C * standardForm
      (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1)))
    (a : Phase n) (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D) (hD0 : 0 ≤ D)
    {p : Phase n} (hp : u 0=p) (c : Plane) (k : ℕ)
    (hc1 : |c.1| ≤ (2:ℝ)^k) (hc2 : |c.2| ≤ (2:ℝ)^k) :
    euclideanNorm (realCurve (affineError u a) c-p) ≤
      2*morreyConstant C*(4*euclideanNorm a+2*Real.sqrt D)+(8*(k:ℝ)+4)*Real.sqrt D := by
  let v := realCurve (affineError u a)
  let ℓ := phaseProjection (v c-p)
  have hℓ := phaseProjection_sq_le (v c-p)
  have hv := realCurve_smooth (affineError_smooth hu a)
  have hp0 : v 0 = p := by change u 0-(0:ℂ) • a=p; simpa using hp
  have h0p := projection_error_point_bound hu hC hE a hi hD hD0 ℓ hℓ 0
  have hcp := projection_error_point_bound hu hC hE a hi hD hD0 ℓ hℓ c
  change |ℓ (v 0)-squareMean (fun z => ℓ (v z)) 0 1| ≤ _ at h0p
  rw [hp0] at h0p
  have h0g := projection_mean_grow_bound hv ℓ hℓ hi hD 0 k
  have hcg := projection_mean_grow_bound hv ℓ hℓ hi hD c k
  have ht := projection_translate_bound hv ℓ hℓ hi hD c
    (show 0 ≤ (2:ℝ)^k by positivity) (show 0 < (2:ℝ)^k by positivity) hc1 hc2
  have hcst : 2*((2:ℝ)^k+(2:ℝ)^k)/(2:ℝ)^k=4 := by
    have hn : (2:ℝ)^k ≠ 0 := by positivity
    field_simp
    ring
  rw [hcst] at ht
  have he : ℓ (v c)-ℓ p = euclideanNorm (v c-p) := by rw [←map_sub]; exact phaseProjection_self _
  have hh1 := (abs_le.mp h0p).1
  have hh2 := (abs_le.mp hcp).2
  have hh3 := (abs_le.mp h0g).1
  have hh4 := (abs_le.mp hcg).2
  have hh5 := (abs_le.mp ht).2
  change euclideanNorm (v c-p) ≤ _
  linarith


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem euclideanNorm_complex_smul {n : ℕ} (z : ℂ) (a : Phase n) :
    euclideanNorm (z • a) = ‖z‖*euclideanNorm a := by
  change ‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm (z • a)‖ = _
  have he : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm (z • a) =
      z • (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm a := by
    ext i
    rfl
  rw [he,norm_smul]
  rfl

theorem euclideanNorm_neg {n : ℕ} (a : Phase n) : euclideanNorm (-a) = euclideanNorm a := by
  simp only [euclideanNorm,map_neg,norm_neg]

theorem affine_reverse_bound {n : ℕ} (u : ℂ → Phase n) (a p : Phase n) (z : ℂ) :
    ‖z‖*euclideanNorm a ≤ euclideanNorm (u z)+euclideanNorm (affineError u a z-p)+euclideanNorm p := by
  have hh := euclideanNorm_add_le (u z) (-(affineError u a z))
  have he : u z + -(affineError u a z) = z • a := by simp only [affineError]; abel
  rw [he,euclideanNorm_neg,euclideanNorm_complex_smul] at hh
  have hh2 := euclideanNorm_add_le (affineError u a z-p) p
  rw [sub_add_cancel] at hh2
  linarith

theorem exists_linear_lt_dyadic {m : ℝ} (hm : 0 < m) (b h : ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, b+h*((k:ℝ)+1) < m*(2:ℝ)^k := by
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)
  have ht : Tendsto (fun k : ℕ => (b+h*((k:ℝ)+1))/(2:ℝ)^k) atTop (𝓝 0) := by
    have hh := (h0.const_mul (b+h)).add (h1.const_mul h)
    convert hh using 1
    · ext k
      simp only [pow_zero,pow_one]
      ring
    · simp
  have he : ∀ᶠ k : ℕ in atTop, (b+h*((k:ℝ)+1))/(2:ℝ)^k < m :=
    ht.eventually (eventually_lt_nhds hm)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun k hk => ?_⟩
  exact (div_lt_iff₀ (by positivity)).mp (hN k hk)

theorem homotopy_uniform_properness (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) (B : ℝ) :
    ∃ S > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u →
      ∀ z : ℂ, S < ‖z‖ → B < euclideanNorm (u z) := by
  obtain ⟨D,hD,hDb⟩ := homotopy_affine_error_energy n hn J hJs hJ hc hs p q hpq
  obtain ⟨C,hC,hCb⟩ := homotopy_standard_energy_bound hJs hJ hc
  obtain ⟨j,hj⟩ := exists_morrey_scale hC.le
  let L := 2*(euclideanNorm (q-p)+(1+2*(1+(1/2:ℝ)^j)/((1/2:ℝ)^j))*Real.sqrt D)
  let E := 2*morreyConstant C*(4*L+2*Real.sqrt D)+4*Real.sqrt D
  obtain ⟨m,hm,hmb⟩ := homotopy_slopes_bounded_below n hn J hJs hJ hc hs p q hpq
  obtain ⟨N,hN⟩ := exists_linear_lt_dyadic hm (B+E+euclideanNorm p) (8*Real.sqrt D)
  refine ⟨(2:ℝ)^N,by positivity,?_⟩
  intro t ht u hu z hz
  obtain ⟨a,ha,hal,hai,haD⟩ := hDb t ht u hu
  obtain ⟨a',ha',hal'⟩ := hmb t ht u hu
  have heq : a'=a := tendsto_nhds_unique hal' hal
  rw [heq] at ha'
  have hE (w : Plane) : planarDirichlet (realCurve u) w ≤ C * standardForm
      (fderiv ℝ (realCurve u) w (1,0)) (fderiv ℝ (realCurve u) w (0,1)) := by
    change stdDot n _ _+stdDot n _ _ ≤ _
    rw [realCurve_CR (hu.2.1 _)]
    exact hCb t ht _ _
  have hL : euclideanNorm a ≤ L := affine_slope_bound hu.1 hC.le hE a hai haD hD.le
    hu.2.2.1 hu.2.2.2.1 j hj
  have hz1 : 1 ≤ ‖z‖ := (one_le_pow₀ (by norm_num : (1:ℝ)≤2)).trans hz.le
  obtain ⟨k,hk0,hk1⟩ := exists_nat_pow_near hz1 (by norm_num : (1:ℝ)<2)
  have hkN : N ≤ k := by
    by_contra hh
    have hh' : k+1 ≤ N := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hh)
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hh'
    linarith
  have hc1 : |z.re| ≤ (2:ℝ)^(k+1) := z.abs_re_le_norm.trans hk1.le
  have hc2 : |z.im| ≤ (2:ℝ)^(k+1) := z.abs_im_le_norm.trans hk1.le
  have hb := affine_error_log_bound hu.1 hC.le hE a hai haD hD.le hu.2.2.1
    (z.re,z.im) (k+1) hc1 hc2
  have hreal : realCurve (affineError u a) (z.re,z.im) = affineError u a z := by
    change affineError u a (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hreal,Nat.cast_add,Nat.cast_one] at hb
  have hb' : euclideanNorm (affineError u a z-p) ≤ E+8*Real.sqrt D*((k:ℝ)+1) := by
    have hM := morreyConstant_pos hC.le
    dsimp [E]
    nlinarith
  have hr := affine_reverse_bound u a p z
  have hh := hN k hkN
  have hmz := mul_le_mul_of_nonneg_left ha' (norm_nonneg z)
  have hmk := mul_le_mul_of_nonneg_left hk0 hm.le
  nlinarith


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem homotopy_slopes_bounded_above (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) :
    ∃ L : ℝ, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u → ∀ a : Phase n,
      Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) → euclideanNorm a ≤ L := by
  obtain ⟨D,hD,hDb⟩ := homotopy_affine_error_energy n hn J hJs hJ hc hs p q hpq
  obtain ⟨C,hC,hCb⟩ := homotopy_standard_energy_bound hJs hJ hc
  obtain ⟨j,hj⟩ := exists_morrey_scale hC.le
  refine ⟨2*(euclideanNorm (q-p)+(1+2*(1+(1/2:ℝ)^j)/((1/2:ℝ)^j))*Real.sqrt D),?_⟩
  intro t ht u hu a hal
  obtain ⟨a',ha',hal',hai,haD⟩ := hDb t ht u hu
  have heq : a'=a := tendsto_nhds_unique hal' hal
  subst a'
  have hE (w : Plane) : planarDirichlet (realCurve u) w ≤ C * standardForm
      (fderiv ℝ (realCurve u) w (1,0)) (fderiv ℝ (realCurve u) w (0,1)) := by
    change stdDot n _ _+stdDot n _ _ ≤ _
    rw [realCurve_CR (hu.2.1 _)]
    exact hCb t ht _ _
  exact affine_slope_bound hu.1 hC.le hE a hai haD hD.le hu.2.2.1 hu.2.2.2.1 j hj

theorem homotopy_uniform_asymptotic (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) (ε : ℝ) (hε : 0 < ε) :
    ∃ S > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u → ∀ a : Phase n,
      Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
      ∀ z : ℂ, S < ‖z‖ → euclideanNorm (z⁻¹ • u z-a) < ε := by
  obtain ⟨D,hD,hDb⟩ := homotopy_affine_error_energy n hn J hJs hJ hc hs p q hpq
  obtain ⟨C,hC,hCb⟩ := homotopy_standard_energy_bound hJs hJ hc
  obtain ⟨L,hLb⟩ := homotopy_slopes_bounded_above n hn J hJs hJ hc hs p q hpq
  let E := 2*morreyConstant C*(4*L+2*Real.sqrt D)+4*Real.sqrt D
  obtain ⟨N,hN⟩ := exists_linear_lt_dyadic hε (E+euclideanNorm p) (8*Real.sqrt D)
  refine ⟨(2:ℝ)^N,by positivity,?_⟩
  intro t ht u hu a hal z hz
  obtain ⟨a',ha',hal',hai,haD⟩ := hDb t ht u hu
  have heq : a'=a := tendsto_nhds_unique hal' hal
  subst a'
  have hE (w : Plane) : planarDirichlet (realCurve u) w ≤ C * standardForm
      (fderiv ℝ (realCurve u) w (1,0)) (fderiv ℝ (realCurve u) w (0,1)) := by
    change stdDot n _ _+stdDot n _ _ ≤ _
    rw [realCurve_CR (hu.2.1 _)]
    exact hCb t ht _ _
  have hL := hLb t ht u hu a hal
  have hz1 : 1 ≤ ‖z‖ := (one_le_pow₀ (by norm_num : (1:ℝ)≤2)).trans hz.le
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨k,hk0,hk1⟩ := exists_nat_pow_near hz1 (by norm_num : (1:ℝ)<2)
  have hkN : N ≤ k := by
    by_contra hh
    have hh' : k+1 ≤ N := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hh)
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hh'
    linarith
  have hb := affine_error_log_bound hu.1 hC.le hE a hai haD hD.le hu.2.2.1
    (z.re,z.im) (k+1) (z.abs_re_le_norm.trans hk1.le) (z.abs_im_le_norm.trans hk1.le)
  have hreal : realCurve (affineError u a) (z.re,z.im) = affineError u a z := by
    change affineError u a (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hreal,Nat.cast_add,Nat.cast_one] at hb
  have hb' : euclideanNorm (affineError u a z-p) ≤ E+8*Real.sqrt D*((k:ℝ)+1) := by
    have hM := morreyConstant_pos hC.le
    dsimp [E]
    nlinarith
  have hw := euclideanNorm_add_le (affineError u a z-p) p
  rw [sub_add_cancel] at hw
  have hh := hN k hkN
  have hmk := mul_le_mul_of_nonneg_left hk0 hε.le
  have hb'' : euclideanNorm (affineError u a z) < ε*‖z‖ := by linarith
  have he : z⁻¹ • u z-a = z⁻¹ • affineError u a z := by
    simp only [affineError,smul_sub,smul_smul,inv_mul_cancel₀ hz0,one_smul]
  rw [he,euclideanNorm_complex_smul,norm_inv,inv_mul_eq_div]
  exact (div_lt_iff₀ (norm_pos_iff.mpr hz0)).mpr hb''

theorem homotopy_limit_has_nonzero_asymptotic (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q)
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1)
    (u : ℕ → ℂ → Phase n)
    (hu : ∀ j, AffineLineCurve (lineHomotopy J (t j)) p q (u j))
    (v : ℂ → Phase n) (hv : ∀ z, Tendsto (fun j => u j z) atTop (𝓝 (v z))) :
    ∃ a : Phase n, a ≠ 0 ∧ Tendsto (fun z : ℂ => z⁻¹ • v z) (cocompact ℂ) (𝓝 a) := by
  classical
  choose a ha hal using fun j => (hu j).2.2.2.2
  obtain ⟨L,hLb⟩ := homotopy_slopes_bounded_above n hn J hJs hJ hc hs p q hpq
  obtain ⟨m,hm,hmb⟩ := homotopy_slopes_bounded_below n hn J hJs hJ hc hs p q hpq
  have ham (j : ℕ) : m ≤ euclideanNorm (a j) := by
    obtain ⟨a',ha',hal'⟩ := hmb (t j) (ht j) (u j) (hu j)
    have he : a'=a j := tendsto_nhds_unique hal' (hal j)
    simpa only [he] using ha'
  have haL (j : ℕ) : euclideanNorm (a j) ≤ L := hLb (t j) (ht j) (u j) (hu j) (a j) (hal j)
  obtain ⟨b,hb,φ,hφ,hφb⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) L).tendsto_subseq
    (x := fun j => phaseEuclidean n (a j)) (fun j => by simpa only [Metric.mem_closedBall,dist_zero_right,euclideanNorm] using haL j)
  let a₀ := (phaseEuclidean n).symm b
  have hφa : Tendsto (a ∘ φ) atTop (𝓝 a₀) := by
    simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using
      (phaseEuclidean n).symm.continuous.continuousAt.tendsto.comp hφb
  have hma : m ≤ euclideanNorm a₀ := ge_of_tendsto
    (((phaseEuclidean n).continuous.continuousAt.tendsto.comp hφa).norm)
    (Eventually.of_forall fun j => ham (φ j))
  have ha₀ : a₀ ≠ 0 := by
    intro he
    have hz : euclideanNorm a₀=0 := by simp [he,euclideanNorm]
    linarith
  refine ⟨a₀,ha₀,?_⟩
  have htail : ∀ ε > 0, ∃ S > 0, ∀ z : ℂ, S < ‖z‖ → euclideanNorm (z⁻¹ • v z-a₀) < ε := by
    intro ε hε
    obtain ⟨S,hS,hSb⟩ := homotopy_uniform_asymptotic n hn J hJs hJ hc hs p q hpq
      (ε/2) (by linarith)
    refine ⟨S,hS,?_⟩
    intro z hz
    have hconv : Tendsto (fun j => z⁻¹ • u (φ j) z-a (φ j)) atTop (𝓝 (z⁻¹ • v z-a₀)) :=
      ((hv z).comp hφ.tendsto_atTop).const_smul z⁻¹ |>.sub hφa
    have hnconv := ((phaseEuclidean n).continuous.continuousAt.tendsto.comp hconv).norm
    have hle : euclideanNorm (z⁻¹ • v z-a₀) ≤ ε/2 := le_of_tendsto hnconv
      (Eventually.of_forall fun j => (hSb (t (φ j)) (ht (φ j)) (u (φ j)) (hu (φ j))
        (a (φ j)) (hal (φ j)) z hz).le)
    linarith
  have hconv : Tendsto (fun z : ℂ => phaseEuclidean n (z⁻¹ • v z)) (cocompact ℂ)
      (𝓝 (phaseEuclidean n a₀)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨S,hS,hSb⟩ := htail ε hε
    filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop S)] with z hz
    rw [dist_eq_norm,←map_sub]
    exact hSb z hz
  simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using
    (phaseEuclidean n).symm.continuous.continuousAt.tendsto.comp hconv


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem lineMean_add_right (f : ℝ → ℝ) (a b d : ℝ) :
    lineMean (fun x => f (x+d)) a b = lineMean f (a+d) (b+d) := by
  simp only [lineMean,intervalIntegral.integral_comp_add_right]
  congr 1
  ring

theorem squareMean_translate (f : Plane → ℝ) (c d : Plane) (r : ℝ) :
    squareMean (fun z => f (z+d)) c r = squareMean f (c+d) r := by
  simp only [squareMean,rectangleMean,Prod.fst_add,Prod.snd_add]
  have he (y : ℝ) : lineMean (fun x => f ((x,y)+d)) (c.1-r) (c.1+r) =
      lineMean (fun x => f (x,y+d.2)) (c.1+d.1-r) (c.1+d.1+r) := by
    change lineMean (fun x => f (x+d.1,y+d.2)) _ _ = _
    rw [lineMean_add_right (fun x => f (x,y+d.2))]
    congr 1 <;> ring
  simp_rw [he]
  rw [lineMean_add_right (fun y => lineMean (fun x => f (x,y)) (c.1+d.1-r) (c.1+d.1+r))]
  congr 1 <;> ring

theorem squareMean_eq_integral {f : Plane → ℝ} (hf : Continuous f) (c : Plane)
    {r : ℝ} (hr : 0 < r) :
    squareMean f c r = (∫ z in planeSquare c r, f z)/(4*r^2) := by
  rw [squareMean,rectangleMean_eq_integral hf ⟨by dsimp; linarith,by dsimp; linarith⟩]
  congr 1
  dsimp
  ring

theorem squareIntegral_translate {f : Plane → ℝ} (hf : Continuous f) (c d : Plane)
    {r : ℝ} (hr : 0 < r) :
    (∫ z in planeSquare c r, f (z+d)) = ∫ z in planeSquare (c+d) r, f z := by
  have he := squareMean_translate f c d r
  have hsh : Continuous (fun z : Plane => f (z+d)) := hf.comp (continuous_id.add continuous_const)
  rw [squareMean_eq_integral hsh c hr,
    squareMean_eq_integral hf (c+d) hr] at he
  exact (div_left_inj' (by positivity : (4:ℝ)*r^2 ≠ 0)).mp he

theorem fderiv_plane_translate {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (d z : Plane) :
    fderiv ℝ (fun w => v (w+d)) z = fderiv ℝ v (z+d) := by
  have ht := ((hv.differentiable (by simp) (z+d)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).add_const d)).fderiv
  simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using ht

theorem planarDirichlet_translate {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (d z : Plane) :
    planarDirichlet (fun w => v (w+d)) z = planarDirichlet v (z+d) := by
  simp only [planarDirichlet,fderiv_plane_translate hv]

theorem squareEnergy_translate {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (c d : Plane) {r : ℝ} (hr : 0 < r) :
    squareEnergy (fun w => v (w+d)) c r = squareEnergy v (c+d) r := by
  simp only [squareEnergy,planarDirichlet_translate hv]
  exact squareIntegral_translate (planarDirichlet_continuous hv) c d hr

theorem point_distance_le_energy_zero {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1))) (c : Plane) {r : ℝ} (hr : 0 < r)
    (hc1 : |c.1| ≤ r) (hc2 : |c.2| ≤ r) :
    euclideanNorm (v c-v 0) ≤ (2*morreyConstant C+4)*Real.sqrt (squareEnergy v 0 (2*r)) := by
  let ℓ := phaseProjection (v c-v 0)
  have hℓ := phaseProjection_sq_le (v c-v 0)
  have h0 := projection_point_bound hv hC hE ℓ hℓ 0 hr
  have h1 := projection_point_bound hv hC hE ℓ hℓ c hr
  have hb0 : squareEnergy v 0 r ≤ squareEnergy v 0 (2*r) := squareEnergy_mono hv 0 (by linarith)
  have hb1 : squareEnergy v c r ≤ squareEnergy v 0 (2*r) := by
    simpa only [show r+r=2*r by ring] using squareEnergy_le_origin hv (r := r) hc1 hc2
  have h0' := h0.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb0) (morreyConstant_pos hC).le)
  have h1' := h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb1) (morreyConstant_pos hC).le)
  have ht := projection_translate_local_bound hv ℓ hℓ c hr.le hr
    (le_refl (squareEnergy v 0 (r+r))) hc1 hc2
  rw [show r+r=2*r by ring,show 2*(2*r)/r=4 by field_simp; ring] at ht
  have he : ℓ (v c)-ℓ (v 0) = euclideanNorm (v c-v 0) := by
    rw [←map_sub]
    exact phaseProjection_self _
  have h01 := (abs_le.mp h0').1
  have h11 := (abs_le.mp h1').2
  have ht1 := (abs_le.mp ht).2
  linarith

theorem point_distance_le_energy {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1))) (c d : Plane) {r : ℝ} (hr : 0 < r)
    (hc1 : |c.1-d.1| ≤ r) (hc2 : |c.2-d.2| ≤ r) :
    euclideanNorm (v c-v d) ≤ (2*morreyConstant C+4)*Real.sqrt (squareEnergy v d (2*r)) := by
  have hvs : ContDiff ℝ ∞ (fun w => v (w+d)) := hv.comp (contDiff_id.add contDiff_const)
  have hEs (z : Plane) : planarDirichlet (fun w => v (w+d)) z ≤ C * standardForm
      (fderiv ℝ (fun w => v (w+d)) z (1,0)) (fderiv ℝ (fun w => v (w+d)) z (0,1)) := by
    simp only [planarDirichlet_translate hv,fderiv_plane_translate hv]
    exact hE (z+d)
  have hh := point_distance_le_energy_zero hvs hC hEs (c-d) hr hc1 hc2
  rw [squareEnergy_translate hv 0 d (by positivity),zero_add,sub_add_cancel] at hh
  exact hh


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem affine_pair_oscillation_dyadic {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet (realCurve u) z ≤ C * standardForm
      (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1)))
    (a : Phase n) (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D) (hD0 : 0 ≤ D)
    {L : ℝ} (hL : euclideanNorm a ≤ L) (c d : Plane) (k : ℕ)
    (hc1 : |c.1-d.1| ≤ (1/2:ℝ)^(k+1)) (hc2 : |c.2-d.2| ≤ (1/2:ℝ)^(k+1)) :
    euclideanNorm (realCurve u c-realCurve u d) ≤
      (2*morreyConstant C+4)*(Real.sqrt (decayRatio C))^k*(4*L+2*Real.sqrt D) := by
  have hp := point_distance_le_energy (realCurve_smooth hu) hC hE c d
    (show 0 < (1/2:ℝ)^(k+1) by positivity) hc1 hc2
  have hr : 2*(1/2:ℝ)^(k+1)=(1/2:ℝ)^k := by rw [pow_succ]; ring
  rw [hr] at hp
  have hd := Real.sqrt_le_sqrt (square_energy_decay_dyadic (realCurve_smooth hu) hC hE d
    (by norm_num : (0:ℝ)<1) k)
  have he (j : ℕ) : Real.sqrt ((decayRatio C)^j) = (Real.sqrt (decayRatio C))^j := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg (decayRatio_nonneg hC) j),ih,pow_succ]
  rw [one_mul,Real.sqrt_mul (pow_nonneg (decayRatio_nonneg hC) k),he] at hd
  have hb := sqrt_squareEnergy_le_affineError hu a hi hD hD0 d (by norm_num : (0:ℝ)≤1)
  simp only [mul_one] at hb
  have hb' : Real.sqrt (squareEnergy (realCurve u) d 1) ≤ 4*L+2*Real.sqrt D := hb.trans (by linarith)
  have hh := hd.trans (mul_le_mul_of_nonneg_left hb' (by positivity))
  have hm : 0 ≤ 2*morreyConstant C+4 := by have := morreyConstant_pos hC; linarith
  exact hp.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hm)

theorem homotopy_uniform_modulus (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) :
    ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u → ∀ z w : ℂ,
      ‖z-w‖ < δ → euclideanNorm (u z-u w) < ε := by
  intro ε hε
  obtain ⟨D,hD,hDb⟩ := homotopy_affine_error_energy n hn J hJs hJ hc hs p q hpq
  obtain ⟨C,hC,hCb⟩ := homotopy_standard_energy_bound hJs hJ hc
  obtain ⟨L,hLb⟩ := homotopy_slopes_bounded_above n hn J hJs hJ hc hs p q hpq
  have hs1 : Real.sqrt (decayRatio C) < 1 := (Real.sqrt_lt' (by norm_num)).mpr
    (by simpa using decayRatio_lt_one hC.le)
  have hlim := ((tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) hs1).const_mul
    (2*morreyConstant C+4)).mul_const (4*L+2*Real.sqrt D)
  have hev : ∀ᶠ k : ℕ in atTop,
      (2*morreyConstant C+4)*(Real.sqrt (decayRatio C))^k*(4*L+2*Real.sqrt D) < ε :=
    hlim.eventually (eventually_lt_nhds (by simpa using hε))
  obtain ⟨k,hk⟩ := hev.exists
  refine ⟨(1/2:ℝ)^(k+1),by positivity,?_⟩
  intro t ht u hu z w hzw
  obtain ⟨a,ha,hal,hai,haD⟩ := hDb t ht u hu
  have hE (s : Plane) : planarDirichlet (realCurve u) s ≤ C * standardForm
      (fderiv ℝ (realCurve u) s (1,0)) (fderiv ℝ (realCurve u) s (0,1)) := by
    change stdDot n _ _+stdDot n _ _ ≤ _
    rw [realCurve_CR (hu.2.1 _)]
    exact hCb t ht _ _
  have hh := affine_pair_oscillation_dyadic hu.1 hC.le hE a hai haD hD.le
    (hLb t ht u hu a hal) (z.re,z.im) (w.re,w.im) k
    ((z-w).abs_re_le_norm.trans hzw.le) ((z-w).abs_im_le_norm.trans hzw.le)
  have hreal (ζ : ℂ) : realCurve u (ζ.re,ζ.im) = u ζ := by
    change u (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM ζ)) = u ζ
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hreal,hreal] at hh
  exact hh.trans_lt hk

theorem norm_le_euclideanNorm_constant (n : ℕ) :
    ∃ K > 0, ∀ a : Phase n, ‖a‖ ≤ K*euclideanNorm a := by
  let K := max 1 ‖(phaseEuclidean n).symm.toContinuousLinearMap‖
  refine ⟨K,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro a
  have hh := (phaseEuclidean n).symm.toContinuousLinearMap.le_opNorm (phaseEuclidean n a)
  simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (euclideanNorm_nonneg a))

theorem homotopy_curves_uniformEquicontinuous (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q)
    {ι : Type*} (t : ι → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1)
    (u : ι → ℂ → Phase n)
    (hu : ∀ j, AffineLineCurve (lineHomotopy J (t j)) p q (u j)) :
    UniformEquicontinuous u := by
  obtain ⟨K,hK,hKb⟩ := norm_le_euclideanNorm_constant n
  apply Metric.uniformEquicontinuous_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδb⟩ := homotopy_uniform_modulus n hn J hJs hJ hc hs p q hpq
    (ε/K) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro z w hzw j
  rw [dist_eq_norm] at hzw ⊢
  have hb := hδb (t j) (ht j) (u j) (hu j) z w hzw
  have hh := mul_lt_mul_of_pos_left hb hK
  rw [mul_div_cancel₀ ε hK.ne'] at hh
  exact (hKb _).trans_lt hh


 

 

 

open scoped ContDiff Topology
open Set Function Filter
open SymplecticBallPacking.Hamiltonian

theorem homotopy_C0_compactness (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q)
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1)
    (u : ℕ → ℂ → Phase n)
    (hu : ∀ j, AffineLineCurve (lineHomotopy J (t j)) p q (u j)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → Phase n,
      Continuous v ∧ TendstoLocallyUniformly (fun j => u (φ j)) v atTop ∧
      v 0=p ∧ v 1=q ∧ ∃ a : Phase n, a ≠ 0 ∧
        Tendsto (fun z : ℂ => z⁻¹ • v z) (cocompact ℂ) (𝓝 a) := by
  classical
  let F : ℕ → C(ℂ,Phase n) := fun j => ⟨u j,(hu j).1.continuous⟩
  have heq := (homotopy_curves_uniformEquicontinuous n hn J hJs hJ hc hs p q hpq t ht u hu).equicontinuous
  have heqr : Equicontinuous (fun f : Set.range F => (f.val : ℂ → Phase n)) := by
    let ψ : Set.range F → ℕ := fun f => f.property.choose
    have hp (f : Set.range F) : F (ψ f) = f.val := f.property.choose_spec
    have he : (fun f : Set.range F => (f.val : ℂ → Phase n)) = u ∘ ψ := by
      funext f z
      exact congrArg (fun g : C(ℂ,Phase n) => g z) (hp f).symm
    rw [he]
    exact heq.comp ψ
  let : T2Space (UniformOnFun ℂ (Phase n) {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply Set.eq_univ_iff_forall.mpr
      intro z
      exact mem_sUnion_of_mem (mem_singleton z) isCompact_singleton)
  have hcomp : IsCompact (closure (Set.range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun f : C(ℂ,Phase n) => (f : ℂ → Phase n))
      (𝔖 := {K | IsCompact K}) (fun K hK => hK)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K hK
      exact heqr.equicontinuousOn K
    · intro K hK z hz
      obtain ⟨Q,hQ,hQb⟩ := homotopy_common_affine_carrier n hn J hJs hJ hc hs p q hpq
        (‖z‖+1) (by positivity)
      refine ⟨Q,hQ,?_⟩
      rintro f ⟨j,rfl⟩
      exact hQb (t j) (ht j) (u j) (hu j) (by
        simp only [Metric.mem_ball,dist_zero_right]
        have := norm_nonneg z
        linarith)
  obtain ⟨v,hv,φ,hφ,hφv⟩ := hcomp.tendsto_subseq (x := F)
    (fun j => subset_closure (mem_range_self j))
  have hloc : TendstoLocallyUniformly (fun j => u (φ j)) v atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hφv
  have hpw : ∀ z, Tendsto (fun j => u (φ j) z) atTop (𝓝 (v z)) :=
    fun z => hloc.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  refine ⟨φ,hφ,v,v.continuous,hloc,?_,?_,?_⟩
  · exact tendsto_nhds_unique (hpw 0) (by simpa only [(hu (φ _)).2.2.1] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p)))
  · exact tendsto_nhds_unique (hpw 1) (by simpa only [(hu (φ _)).2.2.2.1] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => q) atTop (𝓝 q)))
  · exact homotopy_limit_has_nonzero_asymptotic n hn J hJs hJ hc hs p q hpq
      (t ∘ φ) (fun j => ht (φ j)) (fun j => u (φ j)) (fun j => hu (φ j)) v hpw


 

 

 

open scoped ContDiff Topology
open Set Function Filter

theorem homotopy_uniform_holomorphic_exterior (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) :
    ∃ S > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u →
      DifferentiableOn ℂ u {z : ℂ | S < ‖z‖} := by
  obtain ⟨S,hS,hSb⟩ := homotopy_uniform_properness n hn J hJs hJ hc hs p q hpq 1
  refine ⟨S,hS,?_⟩
  intro t ht u hu z hz
  have hzN := hSb t ht u hu z hz
  have hzC : 1 < capacity (u z) := by
    rw [capacity_eq_stdDot,←euclideanNorm_sq]
    have hsq : 1 < (euclideanNorm (u z))^2 := by nlinarith
    have hpi := Real.pi_gt_three
    nlinarith
  have hnot : u z ∉ tsupport (fun x => lineHomotopy J t x-standardJ n) := by
    intro hh
    have hh' := hs (lineHomotopy_support J ht hh)
    change capacity (u z) < 1 at hh'
    linarith
  have hstd : lineHomotopy J t (u z)=standardJ n :=
    sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun x => lineHomotopy J t x-standardJ n) hnot)
  apply DifferentiableAt.differentiableWithinAt
  apply complex_differentiable_of_CR (hu.2.1 z).1
  intro w
  rw [(hu.2.1 z).2,hstd]

theorem homotopy_C0_limit_analytic_at_infinity (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q)
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1)
    (u : ℕ → ℂ → Phase n)
    (hu : ∀ j, AffineLineCurve (lineHomotopy J (t j)) p q (u j))
    (v : ℂ → Phase n) (hv : TendstoLocallyUniformly u v atTop) :
    ∃ a : Phase n, a ≠ 0 ∧ AnalyticAt ℂ (infinityGerm v a) 0 ∧
      infinityGerm v a 0=a := by
  obtain ⟨S,hS,hSb⟩ := homotopy_uniform_holomorphic_exterior n hn J hJs hJ hc hs p q hpq
  have hU : IsOpen {z : ℂ | S < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hhol : DifferentiableOn ℂ v {z : ℂ | S < ‖z‖} :=
    hv.tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun j => hSb (t j) (ht j) (u j) (hu j)) hU
  obtain ⟨a,ha,hal⟩ := homotopy_limit_has_nonzero_asymptotic n hn J hJs hJ hc hs p q hpq
    t ht u hu v (fun z => hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z))
  refine ⟨a,ha,infinityGerm_analyticAt ?_ hal,by simp [infinityGerm]⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop S)] with z hz
  exact hhol.differentiableAt (hU.mem_nhds hz)


 

 

 

open scoped ContDiff Topology
open Set Filter Function

theorem homotopy_C0_smooth_limit (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q)
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1)
    (τ : ℝ) (htτ : Tendsto t atTop (𝓝 τ))
    (u : ℕ → ℂ → Phase n)
    (hu : ∀ j, AffineLineCurve (lineHomotopy J (t j)) p q (u j))
    (v : ℂ → Phase n) (hv : TendstoLocallyUniformly u v atTop) :
    AffineLineCurve (lineHomotopy J τ) p q v := by
  have hCR (j : ℕ) (z : ℂ) : fderiv ℝ (u j) z Complex.I =
      lineHomotopy J (t j) (u j z) (fderiv ℝ (u j) z 1) := by
    simpa only [mul_one] using (hu j).2.1 z |>.2 (1:ℂ)
  have hreg := FramedCR.field_C0_smooth_closure
    (fun y : ℝ × Phase n => lineHomotopy J y.1 y.2)
    (fun y hy => lineHomotopy_contDiffAt hJs hJ hy)
    (fun y hy => compatible_standard_frame (lineHomotopy_compatible hJ hy y.2))
    t ht htτ u (fun j => (hu j).1) hCR v hv
  refine ⟨hreg.1,(homotopy_C0_C1_CR hJs hJ t ht htτ u (fun j => (hu j).1)
      (fun j => (hu j).2.1) v hv).2,?_,?_,?_⟩
  · exact tendsto_nhds_unique
      (hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (0:ℂ)))
      (by simpa only [(hu _).2.2.1] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p)))
  · exact tendsto_nhds_unique
      (hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (1:ℂ)))
      (by simpa only [(hu _).2.2.2.1] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => q) atTop (𝓝 q)))
  · exact homotopy_limit_has_nonzero_asymptotic n hn J hJs hJ hc hs p q hpq
      t ht u hu v (fun z => hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z))

theorem homotopy_affine_curve_compactness (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q)
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1)
    (u : ℕ → ℂ → Phase n)
    (hu : ∀ j, AffineLineCurve (lineHomotopy J (t j)) p q (u j)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ τ ∈ Icc (0:ℝ) 1,
      Tendsto (fun j => t (φ j)) atTop (𝓝 τ) ∧ ∃ v : ℂ → Phase n,
        TendstoLocallyUniformly (fun j => u (φ j)) v atTop ∧
        AffineLineCurve (lineHomotopy J τ) p q v := by
  obtain ⟨τ,hτ,ψ,hψ,hψt⟩ := isCompact_Icc.tendsto_subseq ht
  obtain ⟨φ,hφ,v,hvc,hφv,hvp,hvq,a,ha,has⟩ := homotopy_C0_compactness
    n hn J hJs hJ hc hs p q hpq (t ∘ ψ) (fun j => ht (ψ j))
    (fun j => u (ψ j)) (fun j => hu (ψ j))
  refine ⟨ψ ∘ φ,hψ.comp hφ,τ,hτ,hψt.comp hφ.tendsto_atTop,v,hφv,?_⟩
  exact homotopy_C0_smooth_limit n hn J hJs hJ hc hs p q hpq
    (t ∘ ψ ∘ φ) (fun j => ht (ψ (φ j))) τ (hψt.comp hφ.tendsto_atTop)
    (fun j => u (ψ (φ j))) (fun j => hu (ψ (φ j))) v hφv

end HigherDimensionalBallPacking.Rigidity

end

end OAI
