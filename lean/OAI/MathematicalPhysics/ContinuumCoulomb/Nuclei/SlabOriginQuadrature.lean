import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalTripleQuadrature
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CappedKernelProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabSections
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CappedCoulombMass

namespace OAI

/-! The scalar slab shift is computed by cubature of a capped kernel on
the fixed cube. Its singular truncation error is independent of the box. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.SlabOriginQuadrature

def point (H S : ℝ) (v : Fin 3 → ℝ) : Position :=
  WithLp.toLp 2 ![H*v 0,H*v 1,S*v 2]

def integrand (ε H S : ℝ) (v : Fin 3 → ℝ) : ℝ := cappedCoulombKernel ε (point H S v)

def capped (ε rho H S : ℝ) : ℝ := -rho * ∫ x in slabDomain H S, cappedCoulombKernel ε x

theorem point_norm_sub {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S)
    (v w : Fin 3 → ℝ) : ‖point H S v-point H S w‖ ≤
      (H+S)*∑ i, |v i-w i| := by
  have hn : ‖point H S v-point H S w‖ ≤
      ∑ i : Fin 3, |(point H S v-point H S w) i| := by
    apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _))).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun i : Fin 3 => |(point H S v-point H S w) i|) (fun i _ => abs_nonneg _))
  apply hn.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  fin_cases i
  · change |H*v 0-H*w 0| ≤ (H+S)*|v 0-w 0|
    rw [← mul_sub,abs_mul,abs_of_nonneg hH]
    nlinarith [abs_nonneg (v 0-w 0)]
  · change |H*v 1-H*w 1| ≤ (H+S)*|v 1-w 1|
    rw [← mul_sub,abs_mul,abs_of_nonneg hH]
    nlinarith [abs_nonneg (v 1-w 1)]
  · change |S*v 2-S*w 2| ≤ (H+S)*|v 2-w 2|
    rw [← mul_sub,abs_mul,abs_of_nonneg hS]
    nlinarith [abs_nonneg (v 2-w 2)]

theorem modulus {ε H S : ℝ} (hε : 0 < ε) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (a b : ℝ) : UniformQuadrature.cubeModulus a b (ε⁻¹^2*(H+S)) (integrand ε H S) := by
  intro v _ w _
  exact (cappedCoulombKernel_norm_sub hε _ _).trans
    ((mul_le_mul_of_nonneg_left (point_norm_sub hH hS v w) (sq_nonneg _)).trans_eq
      (by ring))

theorem cap_error {ε rho H S : ℝ} (hε : 0 < ε) (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) :
    |capped ε rho H S-slabPotential rho H S 0| ≤
      rho*NeutralAtom.kernelBallMass ε := by
  have hp (x : Position) : 0 ≤ slabDensity rho H S x := by
    by_cases hx : x ∈ slabDomain H S <;> simp [slabDensity,hx,hrho]
  have hb (x : Position) : slabDensity rho H S x ≤ rho := by
    by_cases hx : x ∈ slabDomain H S <;> simp [slabDensity,hx,hrho]
  have he := cappedCoulombPotential_error hε (slabDensity_integrable hH hS rho) hp hb (0:Position)
  have hc : cappedCoulombPotential ε (slabDensity rho H S) 0 =
      rho*∫ x in slabDomain H S, cappedCoulombKernel ε x := by
    unfold cappedCoulombPotential
    have hfun : (fun y : Position => cappedCoulombKernel ε (0-y)*slabDensity rho H S y) =
        (slabDomain H S).indicator (fun y => rho*cappedCoulombKernel ε y) := by
      funext y
      by_cases hy : y ∈ slabDomain H S
      · simp only [slabDensity,Set.indicator_of_mem hy,zero_sub,cappedCoulombKernel,norm_neg]
        ring
      · simp only [slabDensity,Set.indicator_of_notMem hy,mul_zero]
    rw [hfun,integral_indicator (slabDomain_isClosed H S).measurableSet,integral_const_mul]
  have hs : NeutralAtom.potentialOf (slabDensity rho H S) 0 = -slabPotential rho H S 0 := by
    simp only [slabPotential,neg_neg]
    rfl
  rw [hc,hs] at he
  have hid : capped ε rho H S-slabPotential rho H S 0 =
      -slabPotential rho H S 0-rho*∫ x in slabDomain H S, cappedCoulombKernel ε x := by
    unfold capped
    ring
  rw [hid]
  exact he

theorem interval_scale (f : ℝ → ℝ) (c : ℝ) :
    (∫ x in -c..c, f x) = c*(∫ x in (-1:ℝ)..1, f (c*x)) := by
  simpa only [smul_eq_mul,mul_neg,mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left (a := (-1:ℝ)) (b := 1) f c).symm

theorem triple_interval_scale (f : ℝ → ℝ → ℝ → ℝ) (H S : ℝ) :
    (∫ x in -H..H, ∫ y in -H..H, ∫ z in -S..S, f x y z) =
      H^2*S*(∫ x in (-1:ℝ)..1, ∫ y in (-1:ℝ)..1, ∫ z in (-1:ℝ)..1,
        f (H*x) (H*y) (S*z)) := by
  have hz (x y : ℝ) := interval_scale (f x y) S
  simp_rw [hz,intervalIntegral.integral_const_mul]
  rw [interval_scale (fun x => ∫ y in -H..H, ∫ z in (-1:ℝ)..1, f x y (S*z)) H]
  have hy (x : ℝ) := interval_scale (fun y => ∫ z in (-1:ℝ)..1, f (H*x) y (S*z)) H
  simp_rw [hy,intervalIntegral.integral_const_mul]
  ring

theorem triple_setIntegral {f : Position → ℝ} (hf : Continuous f)
    (H S : ℝ) :
    (∫ x in slabDomain H S, f x) =
      ∫ x in Set.Icc (-H) H, ∫ y in Set.Icc (-H) H,
        ∫ z in Set.Icc (-S) S, f (WithLp.toLp 2 ![x,y,z]) := by
  let F : SlabTriple → ℝ := fun p => f (WithLp.toLp 2 ![p.1,p.2.1,p.2.2])
  have hF : Continuous F := by
    apply hf.comp
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  have hi : IntegrableOn F (slabTripleBox H S) :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  rw [slabTriple_setIntegral]
  simp_rw [slabTripleEquiv_symm_apply]
  change (∫ p in slabTripleBox H S, F p) = _
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [show slabTripleBox H S = Set.Icc (-H) H ×ˢ
    (Set.Icc (-H) H ×ˢ Set.Icc (-S) S) from rfl, setIntegral_prod F hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have hc : Continuous (fun p : ℝ×ℝ => F (x,p)) := hF.comp (continuous_const.prodMk continuous_id)
    have hj : IntegrableOn (fun p : ℝ×ℝ => F (x,p))
        (Set.Icc (-H) H ×ˢ Set.Icc (-S) S) :=
      hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    rw [Measure.volume_eq_prod] at hj ⊢
    exact setIntegral_prod _ hj

theorem setIntegral_scale (f : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (∫ x in Set.Icc (-c) c, f x) = c*(∫ x in (-1:ℝ)..1, f (c*x)) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  exact interval_scale f c

theorem capped_eq_cube {ε H S : ℝ} (hε : 0 < ε) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (rho : ℝ) : capped ε rho H S =
      -rho*H^2*S*UniformQuadrature.cubeIntegral (-1) 1 3 (integrand ε H S) := by
  unfold capped
  rw [triple_setIntegral (cappedCoulombKernel_continuous hε) H S]
  have hs (x y : ℝ) := setIntegral_scale
    (fun z => cappedCoulombKernel ε (WithLp.toLp 2 ![x,y,z])) hS
  simp_rw [hs,integral_const_mul]
  rw [setIntegral_scale (fun x => ∫ y in Set.Icc (-H) H,
    ∫ z in (-1:ℝ)..1, cappedCoulombKernel ε (WithLp.toLp 2 ![x,y,S*z])) hH]
  have hh (x : ℝ) := setIntegral_scale
    (fun y => ∫ z in (-1:ℝ)..1, cappedCoulombKernel ε (WithLp.toLp 2 ![H*x,y,S*z])) hH
  simp_rw [hh,intervalIntegral.integral_const_mul]
  have hcube : UniformQuadrature.cubeIntegral (-1) 1 3 (integrand ε H S) =
      ∫ x in (-1:ℝ)..1, ∫ y in (-1:ℝ)..1, ∫ z in (-1:ℝ)..1,
        cappedCoulombKernel ε (WithLp.toLp 2 ![H*x,H*y,S*z]) := by rfl
  rw [hcube]
  ring

theorem sampling_error {ε rho H S h σ : ℝ} {N : ℕ}
    (hε : 0 < ε) (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (hh : 0 ≤ h) (hσ : 0 ≤ σ) (hend : (N:ℝ)*h=2)
    (v : (Fin 3 → ℕ) → ℝ)
    (hv : ∀ w, (∀ i, w i < N) →
      |v w-integrand ε H S (fun i => UniformQuadrature.node (-1) h (w i))| ≤ σ) :
    |-rho*H^2*S*UniformQuadrature.cubeSample h N 3 v-slabPotential rho H S 0| ≤
      rho*H^2*S*8*(3*(ε⁻¹^2*(H+S))*h+σ)+rho*(2*Real.pi*ε^2) := by
  have he := UniformQuadrature.cube_quadrature_error 3 hh
    (mul_nonneg (sq_nonneg _) (add_nonneg hH hS)) hσ (modulus hε hH hS _ _) hv
  have hb : UniformQuadrature.node (-1) h N = 1 := by
    unfold UniformQuadrature.node
    linarith
  rw [hb,hend] at he
  norm_num only [Nat.cast_ofNat,show (2:ℝ)^3=8 by norm_num] at he
  have hc := cap_error hε hrho hH hS
  rw [coulomb_kernelBallMass hε.le] at hc
  have hmul := mul_le_mul_of_nonneg_left he (mul_nonneg (mul_nonneg hrho (sq_nonneg H)) hS)
  calc
    _ ≤ |-rho*H^2*S*UniformQuadrature.cubeSample h N 3 v-capped ε rho H S| +
        |capped ε rho H S-slabPotential rho H S 0| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (by
      rw [capped_eq_cube hε hH hS,← mul_sub,abs_mul,abs_of_nonpos (by
        have hp := mul_nonneg (mul_nonneg hrho (sq_nonneg H)) hS
        nlinarith : -rho*H^2*S≤0)]
      convert hmul using 1 <;> ring) hc

end ContinuumCoulomb.SlabOriginQuadrature

end

end OAI
