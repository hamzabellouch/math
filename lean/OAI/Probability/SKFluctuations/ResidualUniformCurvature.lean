import Mathlib
import OAI.Probability.SKFluctuations.ResidualRootMoment

namespace OAI

/-! Residual Uniform Curvature. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open Set Scalar

 theorem ResidualJet.Cone.curvature_bound {J : ResidualJet} (hJ : J.Cone)
    (hg : ∀ x, |J.jet 1 x| ≤ 1) {a : ℝ} (ha : 0 < a) :
    |J.jet 2 a| ≤ 1/a := by
  have hm : MonotoneOn (J.jet 2) (Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici _)
    (J.continuous 2).continuousOn
    (fun x _ => (J.derivative 2 x).differentiableAt.differentiableWithinAt) (by
      intro x hx
      rw [interior_Ici] at hx
      rw [(J.derivative 2 x).deriv]
      exact hJ.2.2 x hx.le)
  let f := fun x => J.jet 1 x-x*J.jet 2 a
  have hd (x : ℝ) : HasDerivAt f (J.jet 2 x-J.jet 2 a) x := by
    convert (J.derivative 1 x).sub ((hasDerivAt_id x).mul_const (J.jet 2 a)) using 1 <;>
      first | rfl | simp only [one_mul]
  have hf : AntitoneOn f (Icc 0 a) := antitoneOn_of_deriv_nonpos (convex_Icc ..)
    (continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt).continuousOn
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) (by
      intro x hx
      rw [interior_Icc] at hx
      rw [(hd x).deriv]
      exact sub_nonpos.mpr (hm hx.1.le ha.le hx.2.le))
  have hb := hf (show (0:ℝ) ∈ Icc 0 a from ⟨le_rfl,ha.le⟩) ⟨ha.le,le_rfl⟩ ha.le
  dsimp only [f] at hb
  rw [hJ.gradient_zero,zero_mul,sub_zero] at hb
  rw [abs_of_nonpos (hJ.2.1 a),le_div_iff₀ ha]
  have hg' := neg_le_abs (J.jet 1 a) |>.trans (hg a)
  nlinarith

 theorem GaussianResidual.potential_gradient_bound {R : GaussianResidual}
    (hg : ∀ x, |R.residual.jet 1 x| ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    |deriv R.potential a| ≤ a/R.variance+1 := by
  rw [R.potential_deriv]
  exact (abs_sub _ _).trans (by
    rw [abs_of_nonneg (div_nonneg ha R.positive.le)]
    exact add_le_add le_rfl (hg a))

 theorem GaussianResidual.potential_curvature_bound {R : GaussianResidual}
    (hR : R.residual.Cone) (hg : ∀ x, |R.residual.jet 1 x| ≤ 1)
    {a : ℝ} (ha : 0 < a) :
    |deriv (deriv R.potential) a| ≤ 1/R.variance+1/a := by
  rw [R.potential_second]
  exact (abs_sub _ _).trans (by
    rw [abs_of_pos (one_div_pos.mpr R.positive)]
    exact add_le_add le_rfl (hR.curvature_bound hg ha))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar.PhysicalSlopeSlice
open Set Hierarchy
variable {m : ℝ} (S : PhysicalSlopeSlice m)

theorem exists_Phi_pos (hm : 0 < m) (hB : AbsBounded S.B) :
    ∃ b : ℝ, 0 ≤ b ∧ 0 < S.Φ b := by
  by_contra hn
  have hn' (x : ℝ) (hx : 0 ≤ x) : S.Φ x ≤ 0 := by
    by_contra hp
    exact hn ⟨x,hx,lt_of_not_ge hp⟩
  obtain ⟨K,hK,hb⟩ := hB
  let c := (S.z 1)^2/m
  have hc : 0 < c := div_pos (sq_pos_of_pos (S.z_pos hm (by norm_num))) hm
  have hC (x : ℝ) (hx : 1 ≤ x) : c ≤ S.C x := by
    have hz1 := S.z_pos hm (x:=1) (by norm_num)
    have hzx : S.z 1 ≤ S.z x := (S.z_strictMono hm).monotoneOn
      (show (1:ℝ) ∈ Ici 0 from by norm_num)
      (show x ∈ Ici (0:ℝ) from le_trans (by norm_num : (0:ℝ) ≤ 1) hx) hx
    have hn0 := hn' x (by linarith)
    dsimp only [Φ] at hn0
    change (S.z 1)^2/m ≤ S.C x
    rw [div_le_iff₀ hm]
    nlinarith [sq_nonneg (S.z x-S.z 1)]
  let f := fun x => S.B x-c*x
  have hd (x : ℝ) : HasDerivAt f (S.C x-c) x := by
    convert (S.dB x).sub ((hasDerivAt_id x).const_mul c) using 1 <;> first | rfl | simp only [mul_one]
  have hf : MonotoneOn f (Ici 1) := monotoneOn_of_deriv_nonneg (convex_Ici _)
    (continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt).continuousOn
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) (by
      intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact sub_nonneg.mpr (hC x hx.le))
  let b := 1+(2*K+1)/c
  have hbb : 1 ≤ b := by
    have hh : 0 ≤ (2*K+1)/c := by positivity
    dsimp only [b]; linarith
  have hh := hf (show (1:ℝ) ∈ Ici 1 from by simp) (show b ∈ Ici 1 from hbb) hbb
  have he : c*b=c+2*K+1 := by dsimp only [b]; field_simp; ring
  have hb1 := neg_le_abs (S.B 1) |>.trans (hb 1)
  have hbb' := le_abs_self (S.B b) |>.trans (hb b)
  dsimp only [f] at hh
  rw [he] at hh
  nlinarith

theorem exists_Phi_root (hm : 0 < m) (hB : AbsBounded S.B) :
    ∃ a : ℝ, 0 < a ∧ S.Φ a=0 := by
  obtain ⟨b,hb,hp⟩ := S.exists_Phi_pos hm hB
  have hh := intermediate_value_Icc hb S.continuous_Φ.continuousOn
    (show (0:ℝ) ∈ Icc (S.Φ 0) (S.Φ b) from ⟨(S.Φ_zero_neg hm).le,hp.le⟩)
  obtain ⟨a,ha,hz⟩ := hh
  refine ⟨a,?_,hz⟩
  exact lt_of_le_of_ne ha.1 (by intro he; subst a; exact (S.Φ_zero_neg hm).ne hz)

end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

noncomputable def physicalRootErrorCoefficient {m : ℝ} (S : PhysicalSlopeSlice m)
    (s a : ℝ) : ℝ :=
  ((a/s+1)^2+(1/s+1/a))/2+|S.A a| *(a/s+1)+(S.A a)^2/2+|S.R₀ 0|

theorem physicalRootErrorCoefficient_nonneg {m s a : ℝ} (S : PhysicalSlopeSlice m)
    (hs : 0 < s) (ha : 0 < a) : 0 ≤ physicalRootErrorCoefficient S s a := by
  unfold physicalRootErrorCoefficient
  positivity

theorem physicalRootCoefficient_bound {m : ℝ} (S : PhysicalSlopeSlice m)
    {R : GaussianResidual} (hR : R.residual.Cone) (hg : ∀ x, |R.residual.jet 1 x| ≤ 1)
    {a : ℝ} (ha : 0 < a) :
    |PhysicalSlopeSlice.potentialTerm (deriv R.potential) (deriv (deriv R.potential)) a+
      S.generalR₁ (deriv R.potential) a+S.R₀ 0| ≤ physicalRootErrorCoefficient S R.variance a := by
  let D := deriv R.potential a
  let E := deriv (deriv R.potential) a
  let b := a/R.variance+1
  have hb : 0 ≤ b := by dsimp only [b]; exact add_nonneg (div_nonneg ha.le R.positive.le) (by norm_num)
  have hd : |D| ≤ b := R.potential_gradient_bound hg ha.le
  have he : |E| ≤ 1/R.variance+1/a := R.potential_curvature_bound hR hg ha
  have hdsq : D^2 ≤ b^2 := by nlinarith [sq_abs D,abs_nonneg D]
  have hpot : |(D^2-E)/2| ≤ (b^2+(1/R.variance+1/a))/2 := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg (sq_nonneg D)]; exact add_le_add hdsq he)
  have hr : |S.A a*D+(S.A a)^2/2| ≤ |S.A a| *b+(S.A a)^2/2 := by
    exact (abs_add_le _ _).trans (by
      rw [abs_mul,abs_of_nonneg (div_nonneg (sq_nonneg (S.A a)) (by norm_num : (0:ℝ) ≤ 2))]
      exact add_le_add (mul_le_mul_of_nonneg_left hd (abs_nonneg _)) le_rfl)
  change |(D^2-E)/2+(S.A a*D+(S.A a)^2/2)+S.R₀ 0| ≤ _
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hpot hr)) le_rfl) |>.trans_eq (by
    dsimp only [physicalRootErrorCoefficient,b]; ring)

section
variable (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0)
include hm hmα

theorem scalarClockProfileSlice_residual_uniform_near_root {R : GaussianResidual}
    (hR : R.residual.Cone) (hgrad : ∀ x, |R.residual.jet 1 x| ≤ 1)
    (hn : (∫ x, R.plantedDensity (scalarClockProfileJet α hα l t m r 0) m x)=1)
    {a : ℝ} (ha : 0 < a) (hz : (scalarClockProfileSlice α hα l t hm hmα r).Φ a=0) :
    let S := scalarClockProfileSlice α hα l t hm hmα r
    let w := R.rootWeight S (scalarClockProfileJet α hα l t m r 0)
    (1/R.variance)^2*rootCovarianceFloor S R.variance a-
      (2*physicalRootErrorCoefficient S R.variance a+14*|∫ x in Ioi 0, S.z x*S.κ x|) *
        |∫ x in Ioi 0, w x*S.Φ x| ≤ ∫ x in Ioi 0, w x*S.thirdTest x := by
  let S := scalarClockProfileSlice α hα l t hm hmα r
  let U := scalarClockProfileJet α hα l t m r 0
  let w := R.rootWeight S U
  have hU : LipschitzWith 1 U :=
    scalar_restrict_lipschitz ((scalarProfileHeatJet α hα l t).evolve hm r).lipschitz
  have hlo (x : ℝ) : gaussianDensityFloor R.variance x*(S.C x)^2 ≤ w x := by
    have hh := R.plantedDensity_envelope hgrad hU
      (by rw [abs_of_pos hm]; exact hmα.trans (hα l)) hn x
    dsimp only [w]
    rw [R.rootWeight_eq]
    exact mul_le_mul_of_nonneg_right hh.1 (sq_nonneg _)
  obtain ⟨_,hC,hzpoly,_,_⟩ := scalarClockProfileSlice_polyBounded α hα l t hm hmα r
  have hΦ : PolyBounded S.Φ := ((hzpoly.pow 2).const_mul 2).sub (hC.const_mul m)
  have hGauss : GaussianDominated w := GaussianResidual.rootWeight_dominated hR S hm.le
    (scalarClockProfileJet_zero_upper α hα l t hm r)
    (scalarClockProfileJet_absBounded α hα l t hm r 1)
  have hw : Continuous w := continuous_iff_continuousAt.mpr fun x =>
    (R.rootWeight_deriv S (scalarClockProfileJet_deriv α hα l t hm r 0) x).continuousAt
  have hi := (hGauss.mul_poly_integrable hΦ (hw.mul S.continuous_Φ).aestronglyMeasurable).integrableOn (s := Ioi 0)
  have hiQ : IntegrableOn (fun x => w x*S.Φ x*x^2) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul (PolyBounded.id.pow 2))
      (hw.mul (S.continuous_Φ.mul (continuous_id.pow 2))).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hfloor : rootCovarianceFloor S R.variance a+a^2*(∫ x in Ioi 0, w x*S.Φ x) ≤
      ∫ x in Ioi 0, w x*S.Φ x*x^2 := weight_mul_lower
    (fun x _ => hlo x) (S.Φ_strictMono hm).monotoneOn
    (by intro x hx y hy hxy; change 0 ≤ x at hx; change 0 ≤ y at hy; change x^2 ≤ y^2; nlinarith)
    ha.le hz hi hiQ (rootCovarianceFloor_integrable S R.positive a hC hzpoly)
  have hroot := scalarClockProfileSlice_residual_near_root_lower α hα l t hm hmα r hR ha.le hz
  let M := ∫ x in Ioi 0, w x*S.Φ x
  let V := PhysicalSlopeSlice.potentialTerm (deriv R.potential) (deriv (deriv R.potential)) a+
    S.generalR₁ (deriv R.potential) a+S.R₀ 0
  let K := physicalRootErrorCoefficient S R.variance a
  have hcoeff : |V| ≤ K := physicalRootCoefficient_bound S hR hgrad ha
  have herr : -(|M| *K) ≤ M*V := by
    have hh : |M*V| ≤ |M| *K := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hcoeff (abs_nonneg _)
    exact (neg_le_neg hh).trans (neg_abs_le _)
  have hI : |M| *(∫ x in Ioi 0, S.z x*S.κ x) ≤ |M| *|∫ x in Ioi 0, S.z x*S.κ x| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)
  have hfl := mul_le_mul_of_nonneg_left hfloor (sq_nonneg (1/R.variance))
  change (1/R.variance)^2*rootCovarianceFloor S R.variance a-
    (2*K+14*|∫ x in Ioi 0, S.z x*S.κ x|) *|M| ≤ _
  change (1/R.variance)^2*(∫ x in Ioi 0, w x*S.Φ x*x^2)+
    2*M*(PhysicalSlopeSlice.potentialTerm (deriv R.potential) (deriv (deriv R.potential)) a-
      (1/R.variance)^2*a^2/2+S.generalR₁ (deriv R.potential) a+S.R₀ 0)-
    14*|M| *(∫ x in Ioi 0, S.z x*S.κ x) ≤ _ at hroot
  dsimp only [V] at herr
  change (1/R.variance)^2*(rootCovarianceFloor S R.variance a+a^2*M) ≤ _ at hfl
  nlinarith

end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set Scalar
open scoped Topology NNReal

 theorem scalarClockProfileSlice_residual_sequence_root
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0)
    (R : ℕ → GaussianResidual) {s L : ℝ} (hs : 0 < s)
    (hv : ∀ N, (R N).variance=s) (hR : ∀ N, (R N).residual.Cone)
    (hg : ∀ N x, |(R N).residual.jet 1 x| ≤ 1)
    (hn : ∀ N, (∫ x, (R N).plantedDensity (scalarClockProfileJet α hα l t m r 0) m x)=1)
    (hM : Tendsto (fun N => ∫ x in Ioi 0,
      (R N).rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
      (scalarClockProfileSlice α hα l t hm hmα r).Φ x) atTop (𝓝 0))
    (hL : Tendsto (fun N => ∫ x in Ioi 0,
      (R N).rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
      (scalarClockProfileSlice α hα l t hm hmα r).thirdTest x) atTop (𝓝 L)) : 0 < L := by
  let S := scalarClockProfileSlice α hα l t hm hmα r
  obtain ⟨hB,hC,hz,_,_⟩ := scalarClockProfileSlice_polyBounded α hα l t hm hmα r
  obtain ⟨hbB,_,_,_,_⟩ := scalarClockProfileSlice_absBounded α hα l t hm hmα r
  obtain ⟨a,ha,hφ⟩ := S.exists_Phi_root hm hbB
  let δ := (1/s)^2*rootCovarianceFloor S s a
  have hδ : 0 < δ := mul_pos (sq_pos_of_pos (one_div_pos.mpr hs))
    (rootCovarianceFloor_pos S hm hs ha.le hφ hC hz)
  let K := 2*physicalRootErrorCoefficient S s a+14*|∫ x in Ioi 0, S.z x*S.κ x|
  have ht : Tendsto (fun N => δ-K*|∫ x in Ioi 0,
      (R N).rootWeight S (scalarClockProfileJet α hα l t m r 0) x*S.Φ x|) atTop (𝓝 δ) := by
    simpa only [abs_zero,mul_zero,sub_zero] using tendsto_const_nhds.sub (hM.abs.const_mul K)
  apply hδ.trans_le
  apply le_of_tendsto_of_tendsto ht hL
  exact Eventually.of_forall fun N => by
    have hh := scalarClockProfileSlice_residual_uniform_near_root α hα l t hm hmα r
      (hR N) (hg N) (hn N) ha hφ
    simpa only [hv N] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set Scalar
open scoped Topology NNReal

 theorem scalarClockProfile_residual_moments
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0)
    {R : GaussianResidual} (hR : R.residual.Cone) :
    (∫ x, R.plantedDensity (scalarClockProfileJet α hα l t m r 0) m x*
      ((scalarClockProfileJet α hα l t m r 3 x)^2-
        2*m*(scalarClockProfileJet α hα l t m r 2 x)^3)) =
      4*(∫ x in Ioi 0, R.rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
        (scalarClockProfileSlice α hα l t hm hmα r).Φ x) ∧
    (∫ x, R.plantedDensity (scalarClockProfileJet α hα l t m r 0) m x*
      ((scalarClockProfileJet α hα l t m r 4 x)^2-
        12*m*scalarClockProfileJet α hα l t m r 2 x*(scalarClockProfileJet α hα l t m r 3 x)^2+
        6*m^2*(scalarClockProfileJet α hα l t m r 2 x)^4)) =
      2*(∫ x in Ioi 0, R.rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
        (scalarClockProfileSlice α hα l t hm hmα r).thirdTest x) := by
  let j := scalarClockProfileJet α hα l t m r
  let S := scalarClockProfileSlice α hα l t hm hmα r
  let E := fun x : ℝ => R.density x*Real.exp (m*j 0 x)
  let f := fun x : ℝ => E x*((j 3 x)^2-2*m*(j 2 x)^3)
  let g := fun x : ℝ => E x*((j 4 x)^2-12*m*j 2 x*(j 3 x)^2+6*m^2*(j 2 x)^4)
  have hj0 (x) : j 0 (-x) = j 0 x := by
    simpa only [pow_zero,one_mul] using scalarClockProfileJet_parity α hα l t hm r 0 x
  have hj2 (x) : j 2 (-x) = j 2 x := by
    simpa using scalarClockProfileJet_parity α hα l t hm r 2 x
  have hj3 (x) : j 3 (-x) = -j 3 x := by
    simpa only [show (-1:ℝ)^3 = -1 by norm_num,neg_one_mul] using scalarClockProfileJet_parity α hα l t hm r 3 x
  have hj4 (x) : j 4 (-x) = j 4 x := by
    simpa only [show (-1:ℝ)^4 = 1 by norm_num,one_mul] using scalarClockProfileJet_parity α hα l t hm r 4 x
  have hden (x : ℝ) : R.density (-x) = R.density x := by
    have he := GaussianResidual.potential_even hR x
    have hd (y : ℝ) : R.density y = Real.exp (-R.potential y) := by
      simp only [GaussianResidual.potential,neg_neg,Real.exp_log (R.density_pos y)]
    rw [hd,hd,he]
  have hE (x) : E (-x) = E x := by simp only [E,hj0,hden]
  have hf (x) : f (-x) = f x := by simp only [f,hE,hj2,hj3,neg_sq]
  have hg (x) : g (-x) = g x := by simp only [g,hE,hj2,hj3,hj4,neg_sq]
  have hfw (x : ℝ) : f x = 2*(R.rootWeight S (j 0) x*S.Φ x) := by
    dsimp only [f]
    rw [scalarClockProfileSlice_second α hα l t hm hmα r]
    rw [R.rootWeight_eq]
    dsimp only [E,S,j]
    ring
  have hgw (x : ℝ) : g x = R.rootWeight S (j 0) x*S.thirdTest x := by
    dsimp only [g]
    rw [scalarClockProfileSlice_third α hα l t hm hmα r]
    rw [R.rootWeight_eq]
    dsimp only [E,S,j]
    ring
  constructor
  · change (∫ x, f x) = _
    rw [integral_even_eq_two_Ioi hf]
    simp_rw [hfw]
    rw [integral_const_mul]
    ring
  · change (∫ x, g x) = _
    rw [integral_even_eq_two_Ioi hg]
    simp_rw [hgw]
    rfl

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set Scalar
open scoped Topology NNReal

noncomputable def scalarRootSecond (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (m : ℝ) (r : ℝ≥0) (y : Fin 1 → ℝ) : ℝ :=
  (scalarClockProfileJet α hα l t m r 3 (y 0))^2-
    2*m*(scalarClockProfileJet α hα l t m r 2 (y 0))^3
noncomputable def scalarRootThird (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (m : ℝ) (r : ℝ≥0) (y : Fin 1 → ℝ) : ℝ :=
  (scalarClockProfileJet α hα l t m r 4 (y 0))^2-
    12*m*scalarClockProfileJet α hα l t m r 2 (y 0)*(scalarClockProfileJet α hα l t m r 3 (y 0))^2+
    6*m^2*(scalarClockProfileJet α hα l t m r 2 (y 0))^4

theorem scalarClockProfileJet_bddSmooth (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {m : ℝ} (hm : 0 < m) (r : ℝ≥0) (k j : ℕ) :
    BddSmooth k (fun y : Fin 1 → ℝ => scalarClockProfileJet α hα l t m r (j+1) (y 0)) :=
  (scalarProfileHeatJet α hα l t).scalarClockPlane_positiveJets_bddSmooth
    (fun k _ => scalarProfileJet_bddSmooth_all α hα l t k 0) hm k j r

theorem scalarRootSecond_bddSmooth (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {m : ℝ} (hm : 0 < m) (r : ℝ≥0) (k : ℕ) :
    BddSmooth k (scalarRootSecond α hα l t m r) :=
  ((scalarClockProfileJet_bddSmooth α hα l t hm r k 2).pow 2).sub
    (((scalarClockProfileJet_bddSmooth α hα l t hm r k 1).pow 3).const_mul (2*m))

theorem scalarRootThird_bddSmooth (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {m : ℝ} (hm : 0 < m) (r : ℝ≥0) (k : ℕ) :
    BddSmooth k (scalarRootThird α hα l t m r) := by
  have h := scalarClockProfileJet_bddSmooth α hα l t hm r k
  convert (((h 3).pow 2).sub (((h 1).mul ((h 2).pow 2)).const_mul (12*m))).add
      (((h 1).pow 4).const_mul (6*m^2)) using 1
  funext y
  dsimp only [scalarRootThird]
  ring

theorem scalarClockProfileJet_zero_clock (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {m : ℝ} (hm : 0 < m) (x : ℝ) :
    scalarClockProfileJet α hα l t m 0 0 x=(scalarProfileHeatJet α hα l t).F (fun _ => x) := by
  change clockContinuation m (scalarProfileHeatJet α hα l t).F 0 (fun _ => x)=_
  exact clockContinuation_zero hm.ne' _

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set Scalar
open scoped Topology NNReal

theorem scalarClockProfile_residual_test_sequence_root
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0)
    (R : ℕ → GaussianResidual) {s L : ℝ} (hs : 0 < s)
    (hv : ∀ N, (R N).variance=s) (hR : ∀ N, (R N).residual.Cone)
    (hg : ∀ N x, |(R N).residual.jet 1 x| ≤ 1)
    (hn : ∀ N, (∫ x, (R N).plantedDensity (scalarClockProfileJet α hα l t m r 0) m x)=1)
    (hM : Tendsto (fun N => ∫ x,
      (R N).plantedDensity (scalarClockProfileJet α hα l t m r 0) m x*
      scalarRootSecond α hα l t m r (fun _ => x)) atTop (𝓝 0))
    (hL : Tendsto (fun N => ∫ x,
      (R N).plantedDensity (scalarClockProfileJet α hα l t m r 0) m x*
      scalarRootThird α hα l t m r (fun _ => x)) atTop (𝓝 L)) : 0 < L := by
  let S := scalarClockProfileSlice α hα l t hm hmα r
  let M := fun N => ∫ x in Ioi 0,
    (R N).rootWeight S (scalarClockProfileJet α hα l t m r 0) x*S.Φ x
  let P := fun N => ∫ x in Ioi 0,
    (R N).rootWeight S (scalarClockProfileJet α hα l t m r 0) x*S.thirdTest x
  have h2 (N) : (∫ x, (R N).plantedDensity (scalarClockProfileJet α hα l t m r 0) m x*
      scalarRootSecond α hα l t m r (fun _ => x))=4*M N :=
    (scalarClockProfile_residual_moments α hα l t hm hmα r (hR N)).1
  have h3 (N) : (∫ x, (R N).plantedDensity (scalarClockProfileJet α hα l t m r 0) m x*
      scalarRootThird α hα l t m r (fun _ => x))=2*P N :=
    (scalarClockProfile_residual_moments α hα l t hm hmα r (hR N)).2
  have hm0 : Tendsto M atTop (𝓝 0) := by
    have hh := hM.div_const 4
    simp_rw [h2] at hh
    simpa using hh
  have hpL : Tendsto P atTop (𝓝 (L/2)) := by
    have hh := hL.div_const 2
    simp_rw [h3] at hh
    simpa using hh
  have hp := scalarClockProfileSlice_residual_sequence_root α hα l t hm hmα r R hs hv hR hg hn hm0 hpL
  linarith

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open Filter Set
open scoped Topology NNReal

noncomputable def prefixGridPoint (q h x : ℝ) : ℝ :=
  min q (((Nat.floor (x/h) : ℝ)+1)*h)

theorem prefixGridPoint_monotone {q h : ℝ} (hh : 0 < h) :
    Monotone (prefixGridPoint q h) := by
  intro x y hxy
  have hf : (Nat.floor (x/h):ℝ) ≤ (Nat.floor (y/h):ℝ) :=
    Nat.cast_le.mpr (Nat.floor_mono (div_le_div_of_nonneg_right hxy hh.le))
  exact min_le_min_left q (mul_le_mul_of_nonneg_right (by linarith :
    (Nat.floor (x/h):ℝ)+1 ≤ (Nat.floor (y/h):ℝ)+1) hh.le)

theorem prefixGridPoint_bounds {q h x : ℝ} (hh : 0 < h) (hx : 0 ≤ x) (hxq : x ≤ q) :
    x ≤ prefixGridPoint q h x ∧ prefixGridPoint q h x ≤ x+h := by
  have hlo := Nat.lt_floor_add_one (x/h)
  have hhi := Nat.floor_le (div_nonneg hx hh.le)
  constructor
  · exact le_min hxq (le_of_lt ((div_lt_iff₀ hh).mp hlo))
  · exact (min_le_right _ _).trans (by
      have hd : (Nat.floor (x/h):ℝ)*h ≤ x := (le_div_iff₀ hh).mp hhi
      nlinarith)

theorem prefixGridPoint_cell {q h x : ℝ} {k : ℕ} (hh : 0 < h)
    (hx : x ∈ Ico ((k:ℝ)*h) (((k:ℝ)+1)*h)) (hkq : ((k:ℝ)+1)*h ≤ q) :
    prefixGridPoint q h x = ((k:ℝ)+1)*h := by
  have hx0 : 0 ≤ x := (mul_nonneg (Nat.cast_nonneg k) hh.le).trans hx.1
  have hf : Nat.floor (x/h)=k := (Nat.floor_eq_iff (div_nonneg hx0 hh.le)).mpr
    ⟨(le_div_iff₀ hh).mpr hx.1,(div_lt_iff₀ hh).mpr hx.2⟩
  simp only [prefixGridPoint,hf,min_eq_right hkq]

noncomputable def prefixGridProfile (α : boundedMassProfiles) {q h ε : ℝ}
    (_hq : 0 ≤ q) (hh : 0 < h) (hε : 0 ≤ ε) (hεq : ε ≤ α.val q) : boundedMassProfiles :=
  ⟨fun x => if x < 0 then α.val x else if x < q then max ε (α.val (prefixGridPoint q h x)) else α.val x, by
    constructor
    · intro x
      change (if x < 0 then α.val x else if x < q then max ε (α.val (prefixGridPoint q h x)) else α.val x) ∈ Icc 0 1
      split_ifs
      · exact α.property.1 x
      · exact ⟨hε.trans (le_max_left _ _),max_le (hεq.trans (α.property.1 q).2) (α.property.1 _).2⟩
      · exact α.property.1 x
    · intro x y hxy
      change (if x < 0 then α.val x else if x < q then max ε (α.val (prefixGridPoint q h x)) else α.val x) ≤
        (if y < 0 then α.val y else if y < q then max ε (α.val (prefixGridPoint q h y)) else α.val y)
      by_cases hx : x < 0
      · rw [ite_eq_left hx]
        split_ifs with hy hyq
        · exact α.property.2 hxy
        · exact (α.property.2 (hxy.trans (prefixGridPoint_bounds hh (le_of_not_gt hy) hyq.le).1)).trans (le_max_right _ _)
        · exact α.property.2 hxy
      · have hy : ¬ y < 0 := not_lt.mpr ((le_of_not_gt hx).trans hxy)
        rw [ite_eq_right hx,ite_eq_right hy]
        by_cases hxq : x < q
        · rw [ite_eq_left hxq]
          split_ifs with hyq
          · exact max_le_max_left ε (α.property.2 (prefixGridPoint_monotone hh hxy))
          · exact max_le (hεq.trans (α.property.2 (le_of_not_gt hyq)))
              (α.property.2 ((min_le_left _ _).trans (le_of_not_gt hyq)))
        · rw [ite_eq_right hxq,ite_eq_right (not_lt.mpr ((le_of_not_gt hxq).trans hxy))]
          exact α.property.2 hxy⟩

theorem prefixGridProfile_tail (α : boundedMassProfiles) {q h ε : ℝ}
    (hq : 0 ≤ q) (hh : 0 < h) (hε : 0 ≤ ε) (hεq : ε ≤ α.val q) {x : ℝ} (hx : q ≤ x) :
    (prefixGridProfile α hq hh hε hεq).val x=α.val x := by
  change (if x < 0 then α.val x else if x < q then max ε (α.val (prefixGridPoint q h x)) else α.val x)=α.val x
  rw [ite_eq_right (not_lt.mpr (hq.trans hx)),ite_eq_right (not_lt.mpr hx)]

theorem prefixGridProfile_mem {α : boundedMassProfiles} (hα : α ∈ scalarProfiles) {q h ε : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hh : 0 < h) (hε : 0 ≤ ε) (hεq : ε ≤ α.val q) :
    prefixGridProfile α hq hh hε hεq ∈ scalarProfiles := by
  constructor
  · intro x hx
    change (if x < 0 then α.val x else if x < q then max ε (α.val (prefixGridPoint q h x)) else α.val x)=0
    rw [ite_eq_left hx,hα.1 x hx]
  · intro x hx
    rw [prefixGridProfile_tail α hq hh hε hεq (hq1.trans hx.le)]
    exact hα.2 x hx

theorem prefixGridProfile_cell (α : boundedMassProfiles) {q h ε : ℝ} {k : ℕ}
    (hq : 0 ≤ q) (hh : 0 < h) (hε : 0 ≤ ε) (hεq : ε ≤ α.val q)
    (hkq : ((k:ℝ)+1)*h ≤ q) {x : ℝ} (hx : x ∈ Ioo ((k:ℝ)*h) (((k:ℝ)+1)*h)) :
    (prefixGridProfile α hq hh hε hεq).val x = max ε (α.val (((k:ℝ)+1)*h)) := by
  change (if x < 0 then α.val x else if x < q then max ε (α.val (prefixGridPoint q h x)) else α.val x)=_
  rw [ite_eq_right (not_lt.mpr ((mul_nonneg (Nat.cast_nonneg k) hh.le).trans hx.1.le)),
    ite_eq_left (hx.2.trans_le hkq),prefixGridPoint_cell hh ⟨hx.1.le,hx.2⟩ hkq]

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open Filter Set Scalar
open scoped Topology NNReal

theorem prefixGridProfile_finite (α : boundedMassProfiles) {q h ε : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hh : 0 < h) (hε : 0 < ε) (hεq : ε ≤ α.val q)
    (N : ℕ) (hNq : ((N+1:ℕ):ℝ)*h ≤ q) :
    ScalarFinitePositivePrefix (prefixGridProfile α hq hh hε.le hεq)
      (((N+1:ℕ):ℝ)*h) (max ε (α.val (((N+1:ℕ):ℝ)*h))) := by
  induction N with
  | zero =>
    have he : ((0+1:ℕ):ℝ)*h=h := by norm_num
    rw [he] at hNq ⊢
    apply ScalarFinitePositivePrefix.initial hh (hNq.trans hq1)
      (hε.trans_le (le_max_left _ _)) (max_le (hεq.trans (α.property.1 q).2) (α.property.1 h).2)
    intro u hu
    have hv := prefixGridProfile_cell α hq hh hε.le hεq (k:=0) (by simpa using hNq) (x:=u) (by simpa using hu)
    simpa using hv
  | succ N ih =>
    have hstep : ((N+1:ℕ):ℝ)*h < (((N+1)+1:ℕ):ℝ)*h := by push_cast; nlinarith
    have hp := ih (hstep.le.trans hNq)
    apply ScalarFinitePositivePrefix.step hp hstep (hNq.trans hq1)
      (max_le_max_left ε (α.property.2 hstep.le))
      (max_le (hεq.trans (α.property.1 q).2) (α.property.1 _).2)
    intro u hu
    have he : (((N+1:ℕ):ℝ)+1)*h=(((N+1)+1:ℕ):ℝ)*h := by norm_num
    have hv := prefixGridProfile_cell α hq hh hε.le hεq (k:=N+1) (by rwa [he]) (x:=u) (by rwa [he])
    simpa only [he] using hv

 

theorem prefixGridProfile_uniform_density {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) {q h ε : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hh : 0 < h) (hε : 0 < ε) (hεq : ε ≤ α.val q)
    (N : ℕ) (hNq : ((N+1:ℕ):ℝ)*h=q) :
    ∃ R : GaussianResidual, R.variance=T*q ∧ R.residual.Cone ∧
      ScalarPrefixDensity hT (prefixGridProfile α hq.le hh hε.le hεq) q (α.val q) R ∧
      (∀ x, |R.residual.jet 1 x| ≤ α.val q) ∧
      (∀ x, gaussianLinearEnvelope (T*q) (-2) x/gaussianLinearEnvelopeMass (T*q) 2 ≤
        R.plantedDensity (fun y => (scalarTailJet hT (prefixGridProfile α hq.le hh hε.le hεq) q).F (fun _ => y)) (α.val q) x ∧
        R.plantedDensity (fun y => (scalarTailJet hT (prefixGridProfile α hq.le hh hε.le hεq) q).F (fun _ => y)) (α.val q) x ≤
        gaussianLinearEnvelope (T*q) 2 x/gaussianLinearEnvelopeMass (T*q) (-2)) := by
  have hf := prefixGridProfile_finite α hq.le hq1 hh hε hεq N hNq.le
  rw [hNq,max_eq_right hεq] at hf
  exact hf.uniform_density hT

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open Filter Set
open scoped Topology NNReal

theorem prefixGridPoint_tendsto {q x : ℝ} {h : ℕ → ℝ}
    (hh : ∀ N, 0 < h N) (ht : Tendsto h atTop (𝓝 0)) (hx : 0 ≤ x) (hxq : x ≤ q) :
    Tendsto (fun N => prefixGridPoint q (h N) x) atTop (𝓝[≥] x) := by
  have hb (N) := prefixGridPoint_bounds (hh N) hx hxq
  have hc : Tendsto (fun N => prefixGridPoint q (h N) x) atTop (𝓝 x) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using tendsto_const_nhds.add ht) (fun N => (hb N).1) (fun N => (hb N).2)
  exact tendsto_nhdsWithin_iff.mpr ⟨hc,Eventually.of_forall fun N => (hb N).1⟩

theorem prefixGridProfile_tendsto (α : boundedMassProfiles) {q : ℝ}
    (hq : 0 ≤ q) (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x)
    {h ε : ℕ → ℝ} (hh : ∀ N, 0 < h N) (hε : ∀ N, 0 ≤ ε N)
    (hεq : ∀ N, ε N ≤ α.val q) (ht : Tendsto h atTop (𝓝 0))
    (hεt : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun N => prefixGridProfile α hq (hh N) (hε N) (hεq N)) atTop (𝓝 α) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro x
  by_cases hx : x < 0
  · have he (N) : (prefixGridProfile α hq (hh N) (hε N) (hεq N)).val x=α.val x := by
      change (if x < 0 then α.val x else if x < q then max (ε N) (α.val (prefixGridPoint q (h N) x)) else α.val x)=_
      rw [ite_eq_left hx]
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => α.val x) atTop (𝓝 (α.val x)))
  · by_cases hxq : x < q
    · have hct := (hc x ⟨le_of_not_gt hx,hxq⟩).tendsto.comp
        (prefixGridPoint_tendsto hh ht (le_of_not_gt hx) hxq.le)
      have he (N) : (prefixGridProfile α hq (hh N) (hε N) (hεq N)).val x=
          max (ε N) (α.val (prefixGridPoint q (h N) x)) := by
        change (if x < 0 then α.val x else if x < q then max (ε N) (α.val (prefixGridPoint q (h N) x)) else α.val x)=_
        rw [ite_eq_right hx,ite_eq_left hxq]
      simpa only [he,Function.comp_def,max_eq_right (α.property.1 x).1] using hεt.max hct
    · have he (N) := prefixGridProfile_tail α hq (hh N) (hε N) (hεq N) (le_of_not_gt hxq)
      simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => α.val x) atTop (𝓝 (α.val x)))

 

theorem prefixGridProfile_test_tendsto {n : ℕ} (J : HeatJet n)
    (α : boundedMassProfiles) {q : ℝ} (hq : 0 ≤ q)
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x)
    {h ε : ℕ → ℝ} (hh : ∀ N, 0 < h N) (hε : ∀ N, 0 ≤ ε N)
    (hεq : ∀ N, ε N ≤ α.val q) (ht : Tendsto h atTop (𝓝 0))
    (hεt : Tendsto ε atTop (𝓝 0)) (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    Tendsto (fun N => J.nonnegativeProfileTest
      (boundedNonnegativeProfile (prefixGridProfile α hq (hh N) (hε N) (hεq N))) l t x)
      atTop (𝓝 (J.nonnegativeProfileTest (boundedNonnegativeProfile α) l t x)) :=
  (continuous_boundedProfile_test J l t x).continuousAt.tendsto.comp
    (prefixGridProfile_tendsto α hq hc hh hε hεq ht hεt)

end SKFluctuations.Hierarchy

end

end OAI
