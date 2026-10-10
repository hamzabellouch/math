import Mathlib
import OAI.Probability.SKFluctuations.CenteredMonotoneIntegral
import OAI.Probability.SKFluctuations.ScalarPlantedEnergy

namespace OAI

/-! Gaussian Root Transversality. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Scalar.PhysicalSlopeSlice
open MeasureTheory Set Filter
open scoped Topology
variable {m : ℝ} (S : PhysicalSlopeSlice m)

theorem rootIntegral_pos_gaussian {w : ℝ → ℝ} (hm : 0 < m) {s : ℝ} (hs : 0 < s)
    (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    (hdw : ∀ x, HasDerivAt w (w x*(-x/s-S.A x-3*S.z x)) x)
    (hGauss : GaussianDominated w) (hB : PolyBounded S.B) (hC : PolyBounded S.C)
    (hz : PolyBounded S.z) (hκ : PolyBounded S.κ) (hlam : PolyBounded S.lam)
    (hcLam : Continuous S.lam)
    (hcenter : ∫ x in Ioi 0, w x*S.Φ x = 0) :
    0 < ∫ x in Ioi 0, w x*S.thirdTest x := by
  have hA : PolyBounded S.A := hz.sub (hB.const_mul m)
  have hΦ : PolyBounded S.Φ := ((hz.pow 2).const_mul 2).sub (hC.const_mul m)
  have hR₀ : PolyBounded S.R₀ := ((hκ.const_mul 2).sub ((hC.const_mul m).div_const 2)).sub
    ((hz.pow 2).div_const 2)
  have hR₁ : PolyBounded (S.R₁ s) := ((hA.mul PolyBounded.id).div_const s).add ((hA.pow 2).div_const 2)
  have hG : PolyBounded S.G := (hz.const_mul 2).mul (((hz.const_mul 3).mul hκ).sub hlam)
  have hT : PolyBounded S.thirdTest :=
    (((((hz.pow 2).const_mul 4).sub (hC.const_mul (2*m))).sub (hκ.const_mul 2)).pow 2 |>.sub
      ((hC.const_mul (48*m)).mul (hz.pow 2))).add ((hC.pow 2).const_mul (6*m^2))
  have hRate : PolyBounded (fun x => 2*S.lam x-5*S.z x*S.κ x) :=
    (hlam.const_mul 2).sub ((hz.const_mul 5).mul hκ)
  have hFlux : PolyBounded (S.fluxCore s) :=
    (hz.mul ((hκ.const_mul 2).add (hC.const_mul (3*m)))).add
      ((((PolyBounded.id.div_const (2*s)).sub ((hz.const_mul 3).div_const 2)).add (hA.div_const 2)).mul hΦ)
  have hcB := S.continuous_B
  have hcC := S.continuous_C
  have hcz := S.continuous_z
  have hcκ := S.continuous_κ
  have hcA := S.continuous_A
  have hcR₀ : Continuous S.R₀ := by unfold R₀; fun_prop
  have hcR₁ : Continuous (S.R₁ s) := by unfold R₁; fun_prop
  have hcG : Continuous S.G := by unfold G; fun_prop
  have hcT : Continuous S.thirdTest := by unfold thirdTest; fun_prop
  have hcRate : Continuous (fun x => 2*S.lam x-5*S.z x*S.κ x) := by fun_prop
  have hi : IntegrableOn (fun x => w x*S.Φ x) (Ioi 0) :=
    (hGauss.mul_poly_integrable hΦ (hw.mul S.continuous_Φ).aestronglyMeasurable).integrableOn
  have hi₂ : IntegrableOn (fun x => w x*S.Φ x*x^2) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul (PolyBounded.id.pow 2))
      (hw.mul (S.continuous_Φ.mul (continuous_id.pow 2))).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hi₁ : IntegrableOn (fun x => w x*S.Φ x*S.R₁ s x) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul hR₁)
      (hw.mul (S.continuous_Φ.mul hcR₁)).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hi₀ : IntegrableOn (fun x => w x*S.Φ x*S.R₀ x) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul hR₀)
      (hw.mul (S.continuous_Φ.mul hcR₀)).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hiG := (hGauss.mul_poly_integrable hG (hw.mul hcG).aestronglyMeasurable).integrableOn (s := Ioi 0)
  have hiT := (hGauss.mul_poly_integrable hT (hw.mul hcT).aestronglyMeasurable).integrableOn (s := Ioi 0)
  have htz := hGauss.mul_poly_tendsto hz
  let F := S.rootPrimitive w
  have hdF := S.rootPrimitive_hasDerivAt hw
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hdF x).continuousAt
  have hFb (x : ℝ) (hx : 0 ≤ x) : 0 ≤ F x ∧ F x ≤ w x*S.z x :=
    S.weighted_tail_bounds hm hs (fun y => (hwp y).le) hdw hdF
      (S.rootPrimitive_zero w) (S.rootPrimitive_tendsto hi hcenter) htz hx
  have hiF : IntegrableOn (fun x => F x*(2*S.lam x-5*S.z x*S.κ x)) (Ioi 0) := by
    have hh := (hGauss.mul_poly_integrable (hz.mul hRate)
      (hw.mul (S.continuous_z.mul hcRate)).aestronglyMeasurable).norm.integrableOn (s := Ioi 0)
    apply hh.mono' (hcF.mul hcRate).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [Pi.mul_apply,Real.norm_eq_abs,abs_mul,abs_of_pos (hwp x),abs_of_nonneg (S.z_nonneg hm hx.le),
      abs_of_nonneg (hFb x hx.le).1]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hFb x hx.le).2 (abs_nonneg (2*S.lam x-5*S.z x*S.κ x))
  have htF : Tendsto (fun x => F x*S.R₀ x) atTop (𝓝 0) := by
    have ht := (hGauss.mul_poly_tendsto (hz.mul hR₀)).norm
    rw [norm_zero] at ht
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ ht
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (hwp x),abs_of_nonneg (S.z_nonneg hm hx),
      abs_of_nonneg (hFb x hx).1]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hFb x hx).2 (abs_nonneg (S.R₀ x))
  exact S.rootIntegral_pos hm hs hw hwp hdw hi hi₂ hi₁ hi₀ hiG hiT hiF htz htF
    (hGauss.mul_poly_tendsto hFlux) hcenter

noncomputable def gaussianWeight (U : ℝ → ℝ) (s x : ℝ) : ℝ :=
  Real.exp (m*U x-x^2/(2*s))*(S.C x)^2

theorem gaussianWeight_pos (U : ℝ → ℝ) (s x : ℝ) : 0 < S.gaussianWeight U s x :=
  mul_pos (Real.exp_pos _) (sq_pos_of_pos (S.Cpos x))

theorem gaussianWeight_deriv {U : ℝ → ℝ} (hU : ∀ x, HasDerivAt U (S.B x) x)
    {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt (S.gaussianWeight U s)
      (S.gaussianWeight U s x*(-x/s-S.A x-3*S.z x)) x := by
  have hd := (((hU x).const_mul m).sub (((hasDerivAt_id x).pow 2).div_const (2*s))).exp
  convert hd.mul ((S.dC x).pow 2) using 1 <;> first | rfl | (simp only [gaussianWeight,A,Pi.sub_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]; field_simp [hs.ne']; ring)

theorem gaussianWeight_dominated {U : ℝ → ℝ} (hm : 0 ≤ m) {s : ℝ} (hs : 0 < s)
    (hU : ∀ x, U x ≤ U 0+|x|) (hC : Hierarchy.AbsBounded S.C) :
    GaussianDominated (S.gaussianWeight U s) := by
  obtain ⟨K,hK,hC⟩ := hC
  refine ⟨1/(4*s),Real.exp (m*U 0+s*m^2)*K^2,by positivity,by positivity,fun x => ?_⟩
  have hquad : m*|x|-x^2/(4*s) ≤ s*m^2 := by
    have hh : m*|x|-s*m^2 ≤ x^2/(4*s) := by
      apply (le_div_iff₀ (by positivity : 0 < 4*s)).mpr
      nlinarith [sq_nonneg (|x|-2*s*m),sq_abs x]
    linarith
  have he : m*U x-x^2/(2*s) ≤ (m*U 0+s*m^2)+(-(1/(4*s))*x^2) := by
    have hu := mul_le_mul_of_nonneg_left (hU x) hm
    have hdiv : x^2/(2*s) = 2*(x^2/(4*s)) := by field_simp; ring
    rw [hdiv]
    have heq : -(1/(4*s))*x^2 = -(x^2/(4*s)) := by ring
    rw [heq]
    nlinarith
  rw [abs_of_pos (S.gaussianWeight_pos U s x)]
  unfold gaussianWeight
  calc
    Real.exp (m*U x-x^2/(2*s))*(S.C x)^2 ≤
        Real.exp ((m*U 0+s*m^2)+(-(1/(4*s))*x^2))*K^2 :=
      mul_le_mul (Real.exp_le_exp.mpr he) ((sq_le_sq₀ (S.Cpos x).le hK).mpr ((le_abs_self _).trans (hC x)))
        (sq_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring
end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Scalar
open Hierarchy

theorem absBounded_ratio {f g : ℝ → ℝ} (hg : ∀ x, 0 < g x) {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x, |f x| ≤ K*g x) : AbsBounded (fun x => f x/g x) := by
  refine ⟨K,hK,fun x => ?_⟩
  rw [abs_div,abs_of_pos (hg x)]
  exact (div_le_iff₀ (hg x)).mpr (hf x)

variable {m : ℝ} (j : ℕ → ℝ → ℝ)
  (hd : ∀ k x, HasDerivAt (j k) (j (k+1) x) x)
  (hp : ∀ x, 0 < j 2 x) (h1 : j 1 0 = 0) (h3 : j 3 0 = 0)
  (hs : PolynomialSigns m j)

theorem physicalSlopeOfJets_bounded (hb : ∀ k, AbsBounded (j (k+1)))
    (hr : ∀ k, AbsBounded (fun x => j (k+2) x/j 2 x)) :
    let S := physicalSlopeOfJets j hd hp h1 h3 hs
    PolyBounded S.B ∧ PolyBounded S.C ∧ PolyBounded S.z ∧
      PolyBounded S.κ ∧ PolyBounded S.lam := by
  dsimp only
  have hC : PolyBounded (j 2) := PolyBounded.of_absBounded (hb 1)
  have h3r : PolyBounded (fun x => j 3 x/j 2 x) := PolyBounded.of_absBounded (hr 1)
  have h4r : PolyBounded (fun x => j 4 x/j 2 x) := PolyBounded.of_absBounded (hr 2)
  have h5r : PolyBounded (fun x => j 5 x/j 2 x) := PolyBounded.of_absBounded (hr 3)
  refine ⟨PolyBounded.of_absBounded (hb 0),hC,?_,?_,?_⟩
  · have he : (physicalSlopeOfJets j hd hp h1 h3 hs).z = fun x => -(j 3 x/j 2 x)/2 := by
      funext x
      dsimp only [physicalSlopeOfJets]
      ring
    rw [he]
    exact h3r.neg.div_const 2
  · have he : (physicalSlopeOfJets j hd hp h1 h3 hs).κ = fun x =>
        -m*j 2 x-j 4 x/j 2 x/2+(j 3 x/j 2 x)^2/2 := by
      funext x
      dsimp only [physicalSlopeOfJets,invariantP]
      field_simp [(hp x).ne']
    rw [he]
    exact ((hC.const_mul (-m)).sub (h4r.div_const 2)).add ((h3r.pow 2).div_const 2)
  · have he : (physicalSlopeOfJets j hd hp h1 h3 hs).lam = fun x =>
        -(j 5 x/j 2 x)/2+2*(j 3 x/j 2 x)*(j 4 x/j 2 x)-3*(j 3 x/j 2 x)^3/2 := by
      funext x
      dsimp only [physicalSlopeOfJets,invariantQ]
      field_simp [(hp x).ne']
    rw [he]
    exact ((h5r.neg.div_const 2).add ((h3r.const_mul 2).mul h4r)).sub
      (((h3r.pow 3).const_mul 3).div_const 2)

theorem physicalSlopeOfJets_lam_continuous :
    Continuous (physicalSlopeOfJets j hd hp h1 h3 hs).lam := by
  have hc (k) : Continuous (j k) := continuous_iff_continuousAt.mpr fun x => (hd k x).continuousAt
  unfold physicalSlopeOfJets invariantQ
  exact (((((hc 2).pow 2).neg.mul (hc 5)).div_const 2).add
    ((((hc 2).const_mul 2).mul (hc 3)).mul (hc 4))).sub
      (((hc 3).pow 3).const_mul 3 |>.div_const 2) |>.div ((hc 2).pow 3) (fun x => pow_ne_zero 3 (hp x).ne')

 

theorem physicalSlopeOfJets_second (x : ℝ) :
    (j 3 x)^2-2*m*(j 2 x)^3 =
      2*((physicalSlopeOfJets j hd hp h1 h3 hs).C x)^2*(physicalSlopeOfJets j hd hp h1 h3 hs).Φ x := by
  dsimp only [physicalSlopeOfJets,PhysicalSlopeSlice.Φ]
  field_simp [(hp x).ne']

theorem physicalSlopeOfJets_third (x : ℝ) :
    (j 4 x)^2-12*m*j 2 x*(j 3 x)^2+6*m^2*(j 2 x)^4 =
      ((physicalSlopeOfJets j hd hp h1 h3 hs).C x)^2*(physicalSlopeOfJets j hd hp h1 h3 hs).thirdTest x := by
  dsimp only [physicalSlopeOfJets,PhysicalSlopeSlice.thirdTest,invariantP]
  field_simp [(hp x).ne']
  ring
end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

noncomputable def scalarClockProfileJet (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (m : ℝ) (r : ℝ≥0) (k : ℕ) (x : ℝ) : ℝ :=
  (scalarProfileHeatJet α hα l t).scalarClockJet m k r (fun _ => x)

section
variable (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0)

private theorem ScalarClockPhysicalSlice_profG (k : ℕ) (i : Fin 1) : BddSmooth k ((scalarProfileHeatJet α hα l t).G i) :=
  scalarProfileJet_bddSmooth_all α hα l t k 0

include hm hmα

omit hmα in
theorem scalarClockProfileJet_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (scalarClockProfileJet α hα l t m r k)
      (scalarClockProfileJet α hα l t m r (k+1) x) x :=
  realSpatialJet_hasDerivAt ((scalarProfileHeatJet α hα l t).scalarClockPlane_spatialRegular
    (ScalarClockPhysicalSlice_profG α hα l t) hm) k r x

omit hmα in
theorem scalarClockProfileJet_parity (k : ℕ) (x : ℝ) :
    scalarClockProfileJet α hα l t m r k (-x) =
      (-1:ℝ)^k*scalarClockProfileJet α hα l t m r k x := by
  have he : ∀ x, (scalarProfileHeatJet α hα l t).F (-x) = (scalarProfileHeatJet α hα l t).F x :=
    fun x => scalarProfileJet_zero_even α hα l t (x 0)
  exact realSpatialJet_parity ((scalarProfileHeatJet α hα l t).scalarClockPlane_spatialRegular
    (ScalarClockPhysicalSlice_profG α hα l t) hm) (fun r x => clockContinuation_even he m r (fun _ => x)) k r x

omit hmα in
theorem scalarClockProfileJet_one_zero : scalarClockProfileJet α hα l t m r 1 0 = 0 := by
  have hh := scalarClockProfileJet_parity α hα l t hm r 1 0
  simp only [neg_zero,pow_one,neg_one_mul] at hh
  linarith

omit hmα in
theorem scalarClockProfileJet_three_zero : scalarClockProfileJet α hα l t m r 3 0 = 0 := by
  have hh := scalarClockProfileJet_parity α hα l t hm r 3 0
  norm_num at hh
  linarith

theorem scalarClockProfileJet_curvature_pos (x : ℝ) :
    0 < scalarClockProfileJet α hα l t m r 2 x := by
  let J := scalarProfileHeatJet α hα l t
  have had : J.ScalarAdmissible := fun x => scalarProfileJet_admissible α hα l t (x 0)
  have hl : ∀ x, Real.exp (-4*(t:ℝ))*Scalar.curvature (x 0) ≤ J.H 0 x :=
    fun x => scalarProfileJet_curvature_lower α hα l t (x 0)
  have hb := HeatJet.evolve_curvature_lower had hm (hmα.trans (hα l)) (Real.exp_pos _).le hl
    r.coe_nonneg (fun _ => x)
  change 0 < J.scalarClockJet m 2 r (fun _ => x)
  rw [J.scalarClockJet_two hm]
  exact lt_of_lt_of_le (mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (Scalar.curvature_pos x)) hb

noncomputable def scalarClockProfileSlice : PhysicalSlopeSlice m :=
  physicalSlopeOfJets (scalarClockProfileJet α hα l t m r)
    (scalarClockProfileJet_deriv α hα l t hm r)
    (scalarClockProfileJet_curvature_pos α hα l t hm hmα r)
    (scalarClockProfileJet_one_zero α hα l t hm r)
    (scalarClockProfileJet_three_zero α hα l t hm r)
    (scalarClockProfile_polynomialSigns α hα l t hm hmα r)

omit hmα in
theorem scalarClockProfileJet_absBounded (k : ℕ) :
    AbsBounded (scalarClockProfileJet α hα l t m r (k+1)) := by
  obtain ⟨K,hK,hb⟩ := (scalarProfileHeatJet α hα l t).scalarClockJet_bound (ScalarClockPhysicalSlice_profG α hα l t) hm k
  exact ⟨K,hK,fun x => hb (r,fun _ => x)⟩

theorem scalarClockProfileSlice_polyBounded :
    let S := scalarClockProfileSlice α hα l t hm hmα r
    PolyBounded S.B ∧ PolyBounded S.C ∧ PolyBounded S.z ∧ PolyBounded S.κ ∧ PolyBounded S.lam := by
  apply physicalSlopeOfJets_bounded
  · exact scalarClockProfileJet_absBounded α hα l t hm r
  · intro k
    exact absBounded_ratio (scalarClockProfileJet_curvature_pos α hα l t hm hmα r)
      (by positivity : 0 ≤ (ReplicaTree.attachmentCount 1 (k+1):ℝ)/m)
      (scalarClockProfile_relative_curvature α hα l t hm hmα r k)

theorem scalarClockProfileSlice_lam_continuous :
    Continuous (scalarClockProfileSlice α hα l t hm hmα r).lam :=
  physicalSlopeOfJets_lam_continuous ..

omit hmα in
theorem scalarClockProfileJet_zero_upper (x : ℝ) :
    scalarClockProfileJet α hα l t m r 0 x ≤ scalarClockProfileJet α hα l t m r 0 0+|x| := by
  have hh := ((scalarProfileHeatJet α hα l t).evolve hm r).lipschitz.dist_le_mul
    (fun _ : Fin 1 => x) (fun _ => 0)
  change dist (scalarClockProfileJet α hα l t m r 0 x) (scalarClockProfileJet α hα l t m r 0 0) ≤
    (1:ℝ)*dist (fun _ : Fin 1 => x) (fun _ => 0) at hh
  rw [one_mul,dist_pi_const,Real.dist_eq,Real.dist_eq,sub_zero] at hh
  linarith [(abs_le.mp hh).2]

theorem scalarClockProfileSlice_root_pos {s : ℝ} (hs : 0 < s)
    (hcenter : ∫ x in Ioi 0,
      (scalarClockProfileSlice α hα l t hm hmα r).gaussianWeight
        (scalarClockProfileJet α hα l t m r 0) s x*
      (scalarClockProfileSlice α hα l t hm hmα r).Φ x = 0) :
    0 < ∫ x in Ioi 0,
      (scalarClockProfileSlice α hα l t hm hmα r).gaussianWeight
        (scalarClockProfileJet α hα l t m r 0) s x*
      (scalarClockProfileSlice α hα l t hm hmα r).thirdTest x := by
  let S := scalarClockProfileSlice α hα l t hm hmα r
  let U := scalarClockProfileJet α hα l t m r 0
  have hdU : ∀ x, HasDerivAt U (S.B x) x := scalarClockProfileJet_deriv α hα l t hm r 0
  have hdw := S.gaussianWeight_deriv hdU hs
  obtain ⟨hB,hC,hz,hκ,hlam⟩ := scalarClockProfileSlice_polyBounded α hα l t hm hmα r
  exact S.rootIntegral_pos_gaussian hm hs
    (continuous_iff_continuousAt.mpr fun x => (hdw x).continuousAt)
    (S.gaussianWeight_pos U s) hdw
    (S.gaussianWeight_dominated hm.le hs (scalarClockProfileJet_zero_upper α hα l t hm r)
      (scalarClockProfileJet_absBounded α hα l t hm r 1))
    hB hC hz hκ hlam (scalarClockProfileSlice_lam_continuous α hα l t hm hmα r) hcenter
end
end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem integral_pi_one (μ : Measure ℝ) (f : (Fin 1 → ℝ) → ℝ) :
    (∫ y, f y ∂Measure.pi fun _ : Fin 1 => μ) = ∫ x, f (fun _ => x) ∂μ := by
  have hh := (measurePreserving_funUnique μ (Fin 1)).integral_comp
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding (fun x => f (fun _ => x))
  change (∫ y, f (fun _ => y 0) ∂Measure.pi fun _ : Fin 1 => μ) = _ at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  funext i
  rw [Fin.eq_zero i]

theorem scalar_gaussian_density (F A : (Fin 1 → ℝ) → ℝ) (m : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ y, A y*Real.exp (m*F y) ∂Measure.pi fun _ : Fin 1 => gaussianReal 0 (Real.toNNReal s)) =
      (Real.sqrt (2*Real.pi*s))⁻¹*∫ x, Real.exp (m*F (fun _ => x)-x^2/(2*s))*A (fun _ => x) := by
  rw [integral_pi_one,integral_gaussianReal_eq_integral_smul ((Real.toNNReal_pos.mpr hs).ne')]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [gaussianPDFReal,Real.coe_toNNReal _ hs.le,sub_zero,smul_eq_mul]
  rw [Real.exp_sub,neg_div,Real.exp_neg]
  ring

theorem scalar_clockTest_density (F A : (Fin 1 → ℝ) → ℝ) (m : ℝ) {s : ℝ} (hs : 0 < s) :
    clockTest m F A s 0 =
      (∫ x, Real.exp (m*F (fun _ => x)-x^2/(2*s))*A (fun _ => x))/
        (∫ x, Real.exp (m*F (fun _ => x)-x^2/(2*s))) := by
  unfold clockTest shiftedMean tiltedMean
  simp only [zero_add]
  rw [scalar_gaussian_density F A m hs]
  have hh := scalar_gaussian_density F (fun _ => 1) m hs
  simp only [one_mul,mul_one] at hh
  rw [hh]
  exact mul_div_mul_left _ _ (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity)))

theorem scalar_density_partition_pos {F : (Fin 1 → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (m : ℝ) {s : ℝ} (hs : 0 < s) :
    0 < ∫ x, Real.exp (m*F (fun _ => x)-x^2/(2*s)) := by
  have hi := (exponentialIncrement_gaussian (fun _ : Fin 1 => Real.toNNReal s)).integrable_shift hF m 0
  simp only [zero_add] at hi
  have hp := partition_pos m hi
  have hh := scalar_gaussian_density F (fun _ => 1) m hs
  simp only [one_mul,mul_one] at hh
  rw [hh] at hp
  exact (mul_pos_iff.mp hp).resolve_right (by intro h; exact not_lt_of_ge (by positivity) h.1) |>.2

theorem integral_even_eq_two_Ioi {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) :
    (∫ x, f x) = 2*∫ x in Ioi 0, f x := by
  have he : (fun x => f |x|) = f := by
    funext x
    rcases le_total 0 x with hx|hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx,hf]
  rw [← integral_comp_abs,he]
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def realGaussianKernel (s x : ℝ) : ℝ :=
  gaussianPDFReal 0 (Real.toNNReal s) x

theorem realGaussianKernel_pos {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 < realGaussianKernel s x :=
  gaussianPDFReal_pos _ _ _ (Real.toNNReal_pos.mpr hs).ne'

theorem realGaussianKernel_bridge {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : ℝ) :
    realGaussianKernel t (x-y)*realGaussianKernel s y =
      realGaussianKernel (s+t) x*realGaussianKernel (s*t/(s+t)) (y-s/(s+t)*x) := by
  have hst : 0 < s+t := add_pos hs ht
  have hτ : 0 < s*t/(s+t) := div_pos (mul_pos hs ht) hst
  have hn : (Real.sqrt (2*Real.pi*t))⁻¹*(Real.sqrt (2*Real.pi*s))⁻¹ =
      (Real.sqrt (2*Real.pi*(s+t)))⁻¹*(Real.sqrt (2*Real.pi*(s*t/(s+t))))⁻¹ := by
    rw [← mul_inv,← mul_inv,← Real.sqrt_mul (by positivity),← Real.sqrt_mul (by positivity)]
    congr 2
    field_simp
  have he : -(x-y)^2/(2*t)+ -y^2/(2*s) =
      -x^2/(2*(s+t))+ -(y-s/(s+t)*x)^2/(2*(s*t/(s+t))) := by
    field_simp
    ring
  simp only [realGaussianKernel,gaussianPDFReal,Real.coe_toNNReal _ hs.le,
    Real.coe_toNNReal _ ht.le,Real.coe_toNNReal _ hst.le,Real.coe_toNNReal _ hτ.le,sub_zero]
  calc
    _ = ((Real.sqrt (2*Real.pi*t))⁻¹*(Real.sqrt (2*Real.pi*s))⁻¹)*
        Real.exp (-(x-y)^2/(2*t)+ -y^2/(2*s)) := by rw [Real.exp_add]; ring
    _ = _ := by rw [hn,he,Real.exp_add]; ring

 

theorem gaussian_heat_factor (F : ℝ → ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    (∫ y, realGaussianKernel t (x-y)*(realGaussianKernel s y*Real.exp (F y))) =
      realGaussianKernel (s+t) x *
        ∫ z, Real.exp (F (s/(s+t)*x+z)) ∂gaussianReal 0 (Real.toNNReal (s*t/(s+t))) := by
  have hτ : 0 < s*t/(s+t) := div_pos (mul_pos hs ht) (add_pos hs ht)
  calc
    _ = ∫ y, realGaussianKernel (s+t) x*
        (realGaussianKernel (s*t/(s+t)) (y-s/(s+t)*x)*Real.exp (F y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← mul_assoc,realGaussianKernel_bridge hs ht]
      ring
    _ = ∫ z, realGaussianKernel (s+t) x*
        (realGaussianKernel (s*t/(s+t)) z*Real.exp (F (s/(s+t)*x+z))) := by
      calc
        _ = ∫ z, realGaussianKernel (s+t) x *
            (realGaussianKernel (s*t/(s+t)) ((s/(s+t)*x+z)-s/(s+t)*x) *
              Real.exp (F (s/(s+t)*x+z))) :=
          (integral_add_left_eq_self (μ := volume)
            (fun y : ℝ => realGaussianKernel (s+t) x *
              (realGaussianKernel (s*t/(s+t)) (y-s/(s+t)*x)*Real.exp (F y)))
            (s/(s+t)*x)).symm
        _ = _ := by simp only [add_sub_cancel_left]
    _ = _ := by
      rw [integral_gaussianReal_eq_integral_smul (Real.toNNReal_pos.mpr hτ).ne',← integral_const_mul]
      rfl

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem ResidualJet.exp_heat (J : ResidualJet) (t a x : ℝ) :
    Real.exp ((J.heat t a).jet 0 x) =
      ∫ z, Real.exp (J.jet 0 (a*x+z)) ∂gaussianReal 0 (Real.toNNReal t) := by
  have hi := (exponentialIncrement_gaussian (fun _ : Fin 1 => Real.toNNReal t)).integrable_shift
    J.heatJet.lipschitz 1 (fun _ => a*x)
  have hh := exp_mul_shiftedContinuation (by norm_num : (1:ℝ) ≠ 0) (fun _ : Fin 1 => a*x) hi
  rw [integral_pi_one] at hh
  simpa only [ResidualJet.heat,pow_zero,one_mul,realSpatialJet,HeatJet.scalarClockPlane,
    clockContinuation,ResidualJet.heatJet,Pi.add_apply] using hh

structure GaussianResidual where
  variance : ℝ
  positive : 0 < variance
  residual : ResidualJet

namespace GaussianResidual

noncomputable def density (R : GaussianResidual) (x : ℝ) : ℝ :=
  realGaussianKernel R.variance x*Real.exp (R.residual.jet 0 x)

noncomputable def potential (R : GaussianResidual) (x : ℝ) : ℝ := -Real.log (R.density x)

theorem density_pos (R : GaussianResidual) (x : ℝ) : 0 < R.density x :=
  mul_pos (realGaussianKernel_pos R.positive x) (Real.exp_pos _)

noncomputable def ofVariance (s : ℝ) (hs : 0 < s) : GaussianResidual := ⟨s,hs,ResidualJet.zero⟩

noncomputable def heat (R : GaussianResidual) (t : ℝ) (ht : 0 ≤ t) : GaussianResidual where
  variance := R.variance+t
  positive := add_pos_of_pos_of_nonneg R.positive ht
  residual := R.residual.heat (R.variance*t/(R.variance+t)) (R.variance/(R.variance+t))

noncomputable def atom (R : GaussianResidual) (c : ℝ) (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) : GaussianResidual where
  variance := R.variance
  positive := R.positive
  residual := R.residual.add ((ResidualJet.scalarPotential α hα l t).scale (-c))

theorem density_heat (R : GaussianResidual) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (R.heat t ht.le).density x = ∫ y, realGaussianKernel t (x-y)*R.density y := by
  simp only [density]
  rw [gaussian_heat_factor _ R.positive ht]
  change realGaussianKernel (R.variance+t) x *
    Real.exp ((R.residual.heat (R.variance*t/(R.variance+t)) (R.variance/(R.variance+t))).jet 0 x) = _
  rw [ResidualJet.exp_heat]

theorem density_atom (R : GaussianResidual) (c : ℝ) (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (x : ℝ) :
    (R.atom c α hα l t).density x = Real.exp (-c*scalarProfileJet α l t 0 x)*R.density x := by
  change realGaussianKernel R.variance x *
    Real.exp (R.residual.jet 0 x+ -c*scalarProfileJet α l t 0 x) = _
  rw [Real.exp_add]
  dsimp only [density]
  ring

theorem cone_heat {R : GaussianResidual} (hR : R.residual.Cone) {t : ℝ} (ht : 0 ≤ t) :
    (R.heat t ht).residual.Cone :=
  hR.heat (div_nonneg (mul_nonneg R.positive.le ht) (R.positive.le.trans (le_add_of_nonneg_right ht)))
    (div_nonneg R.positive.le (add_nonneg R.positive.le ht))

theorem cone_atom {R : GaussianResidual} (hR : R.residual.Cone) {c : ℝ} (hc : 0 ≤ c)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) :
    (R.atom c α hα l t).residual.Cone := hR.add (ResidualJet.scalarPotential_neg_cone α hα l t hc)

end GaussianResidual
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem exponentialIncrement_gaussianReal_zero (v : ℝ≥0) : ExponentialIncrement (gaussianReal 0 v) := by
  intro c
  simpa only [Real.norm_eq_abs] using integrable_exp_mul_abs_gaussianReal c v

theorem realGaussianKernel_continuous (s : ℝ) : Continuous (realGaussianKernel s) := by
  unfold realGaussianKernel gaussianPDFReal
  fun_prop

theorem realGaussianKernel_integrable_iff {s : ℝ} (hs : 0 < s) (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 (Real.toNNReal s)) ↔
      Integrable (fun x => realGaussianKernel s x*f x) := by
  rw [gaussianReal_of_var_ne_zero _ (Real.toNNReal_pos.mpr hs).ne']
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [gaussianPDF_def,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul,
    realGaussianKernel]

theorem realGaussianKernel_weighted_integrable {s : ℝ} (hs : 0 < s)
    {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (m : ℝ) :
    Integrable (fun x => realGaussianKernel s x*Real.exp (m*F x)) := by
  apply (realGaussianKernel_integrable_iff hs _).mp
  simpa only [zero_add] using
    (exponentialIncrement_gaussianReal_zero (Real.toNNReal s)).integrable_shift hF m 0

theorem GaussianResidual.density_continuous (R : GaussianResidual) : Continuous R.density :=
  (realGaussianKernel_continuous R.variance).mul (Real.continuous_exp.comp (R.residual.continuous 0))

theorem GaussianResidual.weighted_integrable (R : GaussianResidual)
    {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (m : ℝ) :
    Integrable (fun x => R.density x*Real.exp (m*F x)) := by
  obtain ⟨L,hL⟩ := R.residual.lipschitz
  have hi := realGaussianKernel_weighted_integrable R.positive (hL.add ((lipschitzWith_smul m).comp hF)) 1
  simpa only [GaussianResidual.density,Function.comp_apply,smul_eq_mul,one_mul,Real.exp_add,mul_assoc] using hi

 
theorem convolution_product_integrable {g h : ℝ → ℝ}
    (gc : Continuous g) (hc : Continuous h) (gi : Integrable g) (hi : Integrable h)
    (gp : ∀ x, 0 ≤ g x) (hp : ∀ x, 0 ≤ h x) :
    Integrable (fun p : ℝ × ℝ => g (p.1-p.2)*h p.2) (volume.prod volume) := by
  apply (integrable_prod_iff' ((gc.comp (continuous_fst.sub continuous_snd)).mul
    (hc.comp continuous_snd)).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun y => (gi.comp_sub_right y).mul_const (h y)),?_⟩
  have he (y : ℝ) : (∫ x : ℝ, ‖g (x-y)*h y‖) = (∫ x : ℝ, g x)*h y := by
    simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (gp _) (hp _))]
    rw [integral_mul_const,integral_sub_right_eq_self]
  exact (hi.const_mul (∫ x : ℝ, g x)).congr (ae_of_all _ fun y => (he y).symm)

 

theorem GaussianResidual.heat_joint_integrable (R : GaussianResidual) {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (m : ℝ) :
    Integrable (fun p : ℝ × ℝ => realGaussianKernel t (p.1-p.2)*R.density p.2*
      Real.exp (m*F p.1)) (volume.prod volume) := by
  let L : ℝ := |m| *C
  let g : ℝ → ℝ := fun x => realGaussianKernel t x*Real.exp (L* |x|)
  let h : ℝ → ℝ := fun y => R.density y*Real.exp (L* |y|)
  have gc : Continuous g := (realGaussianKernel_continuous t).mul
    (Real.continuous_exp.comp (continuous_abs.const_mul L))
  have hc : Continuous h := R.density_continuous.mul (Real.continuous_exp.comp (continuous_abs.const_mul L))
  have habs : LipschitzWith 1 (fun x : ℝ => |x|) := by
    intro x y
    rw [edist_dist, edist_dist]
    simpa only [ENNReal.coe_one, one_mul, Real.dist_eq] using
      (ENNReal.ofReal_le_ofReal (abs_abs_sub_abs_le_abs_sub x y))
  have gi : Integrable g := realGaussianKernel_weighted_integrable ht habs L
  have hi : Integrable h := R.weighted_integrable habs L
  have gp (x) : 0 ≤ g x := mul_nonneg (realGaussianKernel_pos ht x).le (Real.exp_nonneg _)
  have hp (x) : 0 ≤ h x := mul_nonneg (R.density_pos x).le (Real.exp_nonneg _)
  have hmajor := (convolution_product_integrable gc hc gi hi gp hp).const_mul (Real.exp (m*F 0))
  apply hmajor.mono' (((realGaussianKernel_continuous t).comp
    (continuous_fst.sub continuous_snd)).mul (R.density_continuous.comp continuous_snd) |>.mul
      (Real.continuous_exp.comp ((hF.continuous.comp continuous_fst).const_mul m))).aestronglyMeasurable
  filter_upwards [] with p
  obtain ⟨x,y⟩ := p
  have he : m*F x ≤ m*F 0+L* |x-y|+L* |y| := by
    have hd : |F x-F 0| ≤ C* |x| := by
      simpa only [Real.dist_eq,sub_zero] using hF.dist_le_mul x 0
    have hx : |x| ≤ |x-y|+|y| := by simpa only [sub_add_cancel] using abs_add_le (x-y) y
    have hg : m*(F x-F 0) ≤ |m| *(C* |x|) := calc
      _ ≤ |m| * |F x-F 0| := by simpa only [abs_mul] using le_abs_self (m*(F x-F 0))
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (abs_nonneg m)
    have hl : 0 ≤ L := mul_nonneg (abs_nonneg m) C.coe_nonneg
    have hh := mul_le_mul_of_nonneg_left hx hl
    dsimp only [L] at hg hh ⊢
    nlinarith
  change |realGaussianKernel t (x-y)*R.density y*Real.exp (m*F x)| ≤
    Real.exp (m*F 0)*(g (x-y)*h y)
  simp only [abs_of_nonneg (mul_nonneg (mul_nonneg
    (realGaussianKernel_pos ht (x-y)).le (R.density_pos y).le) (Real.exp_nonneg _))]
  calc
    _ ≤ realGaussianKernel t (x-y)*R.density y*Real.exp (m*F 0+L* |x-y|+L* |y|) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
        (mul_nonneg (realGaussianKernel_pos ht (x-y)).le (R.density_pos y).le)
    _ = _ := by simp only [g,h,Real.exp_add]; ring

end SKFluctuations.Hierarchy

end

end OAI
