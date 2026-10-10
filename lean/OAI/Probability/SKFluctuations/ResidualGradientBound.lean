import Mathlib
import OAI.Probability.SKFluctuations.TransformedDensityShape

namespace OAI

/-! Residual Gradient Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem ResidualJet.heat_gradient_bound (J : ResidualJet) {K : ℝ}
    (hJ : ∀ x, |J.jet 1 x| ≤ K) (t a x : ℝ) :
    |(J.heat t a).jet 1 x| ≤ |a| * K := by
  have he : realSpatialJet (J.heatJet.scalarClockPlane 1) 1 (t,a*x) =
      clockTest 1 J.heatJet.F (J.heatJet.G 0) t (fun _ => a*x) :=
    ((J.heatJet.evolve (by norm_num : (0:ℝ)<1) t).scalar_derivF (a*x)).deriv
  change |a^1*realSpatialJet (J.heatJet.scalarClockPlane 1) 1 (t,a*x)| ≤ _
  rw [pow_one,abs_mul,he]
  exact mul_le_mul_of_nonneg_left
    (clockTest_abs_le J.heatJet.lipschitz (J.heatJet.smoothG 0) (fun y => hJ (y 0)) 1 t _) (abs_nonneg _)

theorem GaussianResidual.heat_gradient_bound (R : GaussianResidual) {K t : ℝ}
    (hK : 0 ≤ K) (hR : ∀ x, |R.residual.jet 1 x| ≤ K) (ht : 0 ≤ t) (x : ℝ) :
    |(R.heat t ht).residual.jet 1 x| ≤ K := by
  have hden : 0 < R.variance+t := add_pos_of_pos_of_nonneg R.positive ht
  have ha : 0 ≤ R.variance/(R.variance+t) := div_nonneg R.positive.le hden.le
  have hb : R.variance/(R.variance+t) ≤ 1 := (div_le_one hden).mpr (le_add_of_nonneg_right ht)
  exact (R.residual.heat_gradient_bound hR _ _ x).trans (by
    rw [abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_right hb hK).trans_eq (one_mul K))

theorem GaussianResidual.atom_gradient_bound (R : GaussianResidual) {K c : ℝ}
    (hR : ∀ x, |R.residual.jet 1 x| ≤ K) (hc : 0 ≤ c)
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (x : ℝ) :
    |(R.atom c α hα l t).residual.jet 1 x| ≤ K+c := by
  have hb : |scalarProfileJet α l t 1 x| ≤ 1 := by
    simpa only [ReplicaTree.attachmentCount,Nat.cast_one] using scalarProfileJet_bound α hα l t 0 x
  change |R.residual.jet 1 x+ -c*scalarProfileJet α l t 1 x| ≤ _
  calc
    _ ≤ |R.residual.jet 1 x|+|-c*scalarProfileJet α l t 1 x| := abs_add_le _ _
    _ ≤ K+c := by
      rw [abs_mul,abs_neg,abs_of_nonneg hc]
      exact add_le_add (hR x) ((mul_le_mul_of_nonneg_left hb hc).trans_eq (mul_one c))

 

theorem ScalarFinitePositivePrefix.density_gradient_bound {T : ℝ} (hT : 0 < T)
    {α : boundedMassProfiles} {q m : ℝ} (h : ScalarFinitePositivePrefix α q m) :
    ∃ R : GaussianResidual, R.variance=T*q ∧ R.residual.Cone ∧
      ScalarPrefixDensity hT α q m R ∧ (∀ x, |R.residual.jet 1 x| ≤ m) := by
  induction h with
  | @initial q m hq _ hm hm1 hf =>
    refine ⟨GaussianResidual.initial (T*q) (mul_pos hT hq)
      (-m*clockContinuation m (scalarTailJet hT α q).F (T*q) 0),rfl,
      ResidualJet.constant_cone _,scalarPrefixDensity_initial hT hq α hm hm1 hf,?_⟩
    intro x
    simpa [GaussianResidual.initial,ResidualJet.constant] using hm.le
  | @step p q a m prev hpq hq ham hm1 hf ih =>
    obtain ⟨R,hv,hcone,hR,hgrad⟩ := ih
    let S := R.atom (m-a) (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
      (T*p) (Real.toNNReal (T*(1-p)))
    have hs : ScalarPrefixDensity hT α p m S := by
      have hh := scalarPrefixDensity_atom (c:=m-a) hT α hR
      rwa [add_sub_cancel] at hh
    have hsc : S.residual.Cone := GaussianResidual.cone_atom hcone (sub_nonneg.mpr ham)
      (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2) _ _
    have hd : 0 ≤ T*(q-p) := mul_nonneg hT.le (sub_nonneg.mpr hpq.le)
    have hsg (x : ℝ) : |S.residual.jet 1 x| ≤ m := by
      simpa only [add_sub_cancel] using R.atom_gradient_bound hgrad (sub_nonneg.mpr ham)
        (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
        (T*p) (Real.toNNReal (T*(1-p))) x
    refine ⟨S.heat (T*(q-p)) hd,?_,GaussianResidual.cone_heat hsc hd,?_,?_⟩
    · change R.variance+T*(q-p)=T*q
      rw [hv]
      ring
    · exact scalarPrefixDensity_heat hT prev.bounds.1.le hpq hq α
        (prev.bounds.2.2.1.trans_le ham) hm1 hf hs
    · exact fun x => S.heat_gradient_bound (prev.bounds.2.2.1.le.trans ham) hsg hd x

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem ScalarPrefixDensity.integral {T q m : ℝ} (hT : 0 < T)
    {α : boundedMassProfiles} {R : GaussianResidual} (hR : ScalarPrefixDensity hT α q m R) :
    (∫ x, R.plantedDensity (fun y => (scalarTailJet hT α q).F (fun _ => y)) m x)=1 := by
  let J := scalarTailJet hT α q
  let K := J.withTest (fun _ => 1) (BddSmooth.const 2 1)
  have hh := J.nonnegativeProfileTest_affine K 1 0 rfl (by funext x; change (1:ℝ)=1+0*J.A x; ring)
    (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2) 0 (Real.toNNReal (T*q)) 0
  have hd := hR (fun _ => 1) (BddSmooth.const 2 1)
  simp only [mul_one] at hd
  rw [← hd]
  simpa only [zero_mul,add_zero] using hh

noncomputable def gaussianLinearEnvelope (s a x : ℝ) : ℝ :=
  realGaussianKernel s x*Real.exp (a*|x|)

noncomputable def gaussianLinearEnvelopeMass (s a : ℝ) : ℝ :=
  ∫ x, gaussianLinearEnvelope s a x

theorem gaussianLinearEnvelope_integrable {s : ℝ} (hs : 0 < s) (a : ℝ) :
    Integrable (gaussianLinearEnvelope s a) := by
  apply realGaussianKernel_weighted_integrable hs (C:=1) ?_ a
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y

theorem gaussianLinearEnvelopeMass_pos {s : ℝ} (hs : 0 < s) (a : ℝ) :
    0 < gaussianLinearEnvelopeMass s a := by
  have hp (x : ℝ) : 0 < gaussianLinearEnvelope s a x :=
    mul_pos (realGaussianKernel_pos hs x) (Real.exp_pos _)
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le)
    (gaussianLinearEnvelope_integrable hs a)).mpr
  have he : Function.support (gaussianLinearEnvelope s a)=univ := by
    ext x
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (hp x).ne'
  rw [he]
  simp

 

theorem gaussian_tilt_envelope {s : ℝ} (hs : 0 < s) {f : ℝ → ℝ}
    (hf : ∀ x, |f x-f 0| ≤ 2*|x|)
    (hi : Integrable (fun x => realGaussianKernel s x*Real.exp (f x)))
    (hn : (∫ x, realGaussianKernel s x*Real.exp (f x))=1) (x : ℝ) :
    gaussianLinearEnvelope s (-2) x/gaussianLinearEnvelopeMass s 2 ≤
      realGaussianKernel s x*Real.exp (f x) ∧
    realGaussianKernel s x*Real.exp (f x) ≤
      gaussianLinearEnvelope s 2 x/gaussianLinearEnvelopeMass s (-2) := by
  have hl (y : ℝ) : Real.exp (f 0)*gaussianLinearEnvelope s (-2) y ≤
      realGaussianKernel s y*Real.exp (f y) := by
    have hh := (abs_le.mp (hf y)).1
    have he : Real.exp (f 0+ -2*|y|) ≤ Real.exp (f y) := Real.exp_le_exp.mpr (by linarith)
    have hk := mul_le_mul_of_nonneg_left he (realGaussianKernel_pos hs y).le
    simpa only [Real.exp_add,gaussianLinearEnvelope,mul_left_comm,mul_assoc] using hk
  have hu (y : ℝ) : realGaussianKernel s y*Real.exp (f y) ≤
      Real.exp (f 0)*gaussianLinearEnvelope s 2 y := by
    have hh := (abs_le.mp (hf y)).2
    have he : Real.exp (f y) ≤ Real.exp (f 0+2*|y|) := Real.exp_le_exp.mpr (by linarith)
    have hk := mul_le_mul_of_nonneg_left he (realGaussianKernel_pos hs y).le
    simpa only [Real.exp_add,gaussianLinearEnvelope,mul_left_comm,mul_assoc] using hk
  have hlow := integral_mono ((gaussianLinearEnvelope_integrable hs (-2)).const_mul (Real.exp (f 0))) hi hl
  have hupp := integral_mono hi ((gaussianLinearEnvelope_integrable hs 2).const_mul (Real.exp (f 0))) hu
  rw [hn,integral_const_mul] at hlow hupp
  change Real.exp (f 0)*gaussianLinearEnvelopeMass s (-2) ≤ 1 at hlow
  change 1 ≤ Real.exp (f 0)*gaussianLinearEnvelopeMass s 2 at hupp
  have hL := (le_div_iff₀ (gaussianLinearEnvelopeMass_pos hs (-2))).mpr hlow
  have hU := (div_le_iff₀ (gaussianLinearEnvelopeMass_pos hs 2)).mpr hupp
  constructor
  · calc
      _ = (1/gaussianLinearEnvelopeMass s 2)*gaussianLinearEnvelope s (-2) x := by ring
      _ ≤ Real.exp (f 0)*gaussianLinearEnvelope s (-2) x :=
        mul_le_mul_of_nonneg_right hU (mul_nonneg (realGaussianKernel_pos hs x).le (Real.exp_nonneg _))
      _ ≤ _ := hl x
  · calc
      _ ≤ Real.exp (f 0)*gaussianLinearEnvelope s 2 x := hu x
      _ ≤ (1/gaussianLinearEnvelopeMass s (-2))*gaussianLinearEnvelope s 2 x :=
        mul_le_mul_of_nonneg_right hL (mul_nonneg (realGaussianKernel_pos hs x).le (Real.exp_nonneg _))
      _ = _ := by ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.flatten_one_absolute_error {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) {a b A d : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (hA0 : 0 ≤ A) (hd : 0 ≤ d)
    (x : Fin 1 → ℝ) :
    |clockContinuation a (J.evolve hb d).F A x-clockContinuation a J.F (A+d) x-
      ((b-a)*d/2)*J.observedSquare a (A+d) x| ≤ 2 * |b-a| * d^2 := by
  have hbE (s : ℝ) (hs : s ∈ uIoc A (A+d)) :
      |J.mixedSquare a hb (A+d) s x-J.observedSquare a (A+d) x| ≤ 4*d := by
    rw [uIoc_of_le (by linarith : A ≤ A+d)] at hs
    have hh := HeatJet.mixedSquare_lipschitz hJ hA ⟨ha.le,ha1⟩ hb hb1
      (r:=A+d) (s:=s) (T:=A+d) ⟨by positivity,le_rfl⟩ ⟨hA0.trans hs.1.le,hs.2⟩ x
    rw [J.mixedSquare_terminal,abs_of_nonpos (sub_nonpos.mpr hs.2)] at hh
    linarith [hs.1]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=A) (b:=A+d) (f:=fun s => J.mixedSquare a hb (A+d) s x-J.observedSquare a (A+d) x)
    (C:=4*d) (fun s hs => by simpa only [Real.norm_eq_abs] using hbE s hs)
  rw [intervalIntegral.integral_sub ((J.continuous_mixedSquare a hb (A+d) x).intervalIntegrable A (A+d)) intervalIntegrable_const,
    intervalIntegral.integral_const] at hi
  simp only [add_sub_cancel_left,smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg hd] at hi
  rw [HeatJet.flatten_one_identity hA ha hb hA0 hd]
  have he : (b-a)/2*(∫ s in A..A+d, J.mixedSquare a hb (A+d) s x)-
      (b-a)*d/2*J.observedSquare a (A+d) x =
      ((b-a)/2)*((∫ s in A..A+d, J.mixedSquare a hb (A+d) s x)-d*J.observedSquare a (A+d) x) := by ring
  rw [he,abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  calc
    _ ≤ (|b-a|/2)*(4*d*d) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

theorem clockExcess_nonpos (a : ℝ) (cs : List HeatClock)
    (hc : ∀ c ∈ cs, c.mass ≤ a) : clockExcess a cs ≤ 0 := by
  induction cs with
  | nil => exact le_rfl
  | cons c cs ih =>
    exact add_nonpos (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hc c (List.mem_cons_self ..))) c.time.coe_nonneg)
      (ih (fun d hd => hc d (List.mem_cons_of_mem _ hd)))

 theorem HeatJet.flatten_schedule_reverse_error {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) (cs : List HeatClock) {a A : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hc : ∀ c ∈ cs, c.mass ≤ a)
    (hA0 : 0 ≤ A) (x : Fin 1 → ℝ) :
    |clockContinuation a (J.schedule cs).F A x-clockContinuation a J.F (A+clockLength cs) x-
      (clockExcess a cs/2)*J.observedSquare a (A+clockLength cs) x| ≤
      -(2*clockLength cs*clockExcess a cs) := by
  induction cs generalizing A with
  | nil => simp only [HeatJet.schedule,clockLength_nil,clockExcess_nil,add_zero,sub_self,
      zero_div,zero_mul,abs_zero,mul_zero,neg_zero,le_refl]
  | cons c cs ih =>
    have hcs : ∀ d ∈ cs, d.mass ≤ a := fun d hd => hc d (List.mem_cons_of_mem _ hd)
    have hcc := hc c (List.mem_cons_self ..)
    have hh := HeatJet.flatten_one_absolute_error (hJ.schedule cs (fun d hd => (hcs d hd).trans ha1))
      (hA.schedule cs) ha ha1 c.positive (hcc.trans ha1) hA0 c.time.coe_nonneg x
    rw [abs_of_nonpos (sub_nonpos.mpr hcc)] at hh
    have hi := ih hcs (A:=A+c.time) (by positivity)
    have he := HeatJet.flatten_schedule_energy hJ hA cs (fun d hd => (hcs d hd).trans ha1)
      ⟨ha.le,ha1⟩ (A:=A+c.time) (by positivity) x
    let F₀ := clockContinuation a (J.schedule (c::cs)).F A x
    let F₁ := clockContinuation a (J.schedule cs).F (A+c.time) x
    let F₂ := clockContinuation a J.F (A+c.time+clockLength cs) x
    let E₁ := (J.schedule cs).observedSquare a (A+c.time) x
    let E₂ := J.observedSquare a (A+c.time+clockLength cs) x
    let w := (c.mass-a)*(c.time:ℝ)
    have hw : w ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcc) c.time.coe_nonneg
    have hW : clockExcess a cs ≤ 0 := clockExcess_nonpos a cs hcs
    change |F₀-F₁-w/2*E₁| ≤ 2* (-(c.mass-a))*(c.time:ℝ)^2 at hh
    change |F₁-F₂-clockExcess a cs/2*E₂| ≤ _ at hi
    change |E₁-E₂| ≤ _ at he
    have h3 : |w/2*(E₁-E₂)| ≤ -2*w*clockLength cs := by
      rw [abs_mul,abs_of_nonpos (by linarith : w/2 ≤ 0)]
      calc
        _ ≤ -(w/2)*(4*clockLength cs) := mul_le_mul_of_nonneg_left he (by linarith)
        _ = _ := by ring
    have ht : |F₀-F₂-(w+clockExcess a cs)/2*E₂| ≤
        2* (-(c.mass-a))*(c.time:ℝ)^2+ -(2*clockLength cs*clockExcess a cs)+ -2*w*clockLength cs := by
      calc
        _ = |(F₀-F₁-w/2*E₁)+(F₁-F₂-clockExcess a cs/2*E₂)+w/2*(E₁-E₂)| := by congr 1; ring
        _ ≤ |F₀-F₁-w/2*E₁|+|F₁-F₂-clockExcess a cs/2*E₂|+|w/2*(E₁-E₂)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ _ := add_le_add (add_le_add hh hi) h3
    have hb : 2* (-(c.mass-a))*(c.time:ℝ)^2+ -(2*clockLength cs*clockExcess a cs)+ -2*w*clockLength cs ≤
        -(2*((c.time:ℝ)+clockLength cs)*(w+clockExcess a cs)) := by
      dsimp only [w]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos c.time.coe_nonneg hW]
    simpa only [clockLength_cons,clockExcess_cons,add_assoc,F₀,F₂,E₂,w] using ht.trans hb

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.flatten_one_signed_error {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) {a b A d : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (hA0 : 0 ≤ A) (hd : 0 ≤ d)
    (x : Fin 1 → ℝ) :
    |clockContinuation a (J.evolve hb d).F A x-clockContinuation a J.F (A+d) x-
      ((b-a)*d/2)*J.observedSquare a (A+d) x| ≤ 2*d^2 := by
  have hbE (s : ℝ) (hs : s ∈ uIoc A (A+d)) :
      |J.mixedSquare a hb (A+d) s x-J.observedSquare a (A+d) x| ≤ 4*d := by
    rw [uIoc_of_le (by linarith : A ≤ A+d)] at hs
    have hh := HeatJet.mixedSquare_lipschitz hJ hA ⟨ha.le,ha1⟩ hb hb1
      (r:=A+d) (s:=s) (T:=A+d) ⟨by positivity,le_rfl⟩ ⟨hA0.trans hs.1.le,hs.2⟩ x
    rw [J.mixedSquare_terminal,abs_of_nonpos (sub_nonpos.mpr hs.2)] at hh
    linarith [hs.1]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=A) (b:=A+d) (f:=fun s => J.mixedSquare a hb (A+d) s x-J.observedSquare a (A+d) x)
    (C:=4*d) (fun s hs => by simpa only [Real.norm_eq_abs] using hbE s hs)
  rw [intervalIntegral.integral_sub ((J.continuous_mixedSquare a hb (A+d) x).intervalIntegrable A (A+d)) intervalIntegrable_const,
    intervalIntegral.integral_const] at hi
  simp only [add_sub_cancel_left,smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg hd] at hi
  rw [HeatJet.flatten_one_identity hA ha hb hA0 hd]
  have he : (b-a)/2*(∫ s in A..A+d, J.mixedSquare a hb (A+d) s x)-
      (b-a)*d/2*J.observedSquare a (A+d) x =
      ((b-a)/2)*((∫ s in A..A+d, J.mixedSquare a hb (A+d) s x)-d*J.observedSquare a (A+d) x) := by ring
  rw [he,abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hab : |b-a| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  calc
    _ ≤ (|b-a|/2)*(4*d*d) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ (1/2:ℝ)*(4*d*d) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

 

theorem HeatJet.flatten_schedule_signed_error {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) (cs : List HeatClock) {a A : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hc : ∀ c ∈ cs, c.mass ≤ 1)
    (hA0 : 0 ≤ A) (x : Fin 1 → ℝ) :
    |clockContinuation a (J.schedule cs).F A x-clockContinuation a J.F (A+clockLength cs) x-
      (clockExcess a cs/2)*J.observedSquare a (A+clockLength cs) x| ≤
      2*(clockLength cs)^2 := by
  induction cs generalizing A with
  | nil => simp only [HeatJet.schedule,clockLength_nil,clockExcess_nil,add_zero,sub_self,
      zero_div,zero_mul,abs_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
  | cons c cs ih =>
    have hcs : ∀ d ∈ cs, d.mass ≤ 1 := fun d hd => hc d (List.mem_cons_of_mem _ hd)
    have hcc := hc c (List.mem_cons_self ..)
    have hh := HeatJet.flatten_one_signed_error (hJ.schedule cs hcs)
      (hA.schedule cs) ha ha1 c.positive hcc hA0 c.time.coe_nonneg x
    have hi := ih hcs (A:=A+c.time) (by positivity)
    have he := HeatJet.flatten_schedule_energy hJ hA cs hcs
      ⟨ha.le,ha1⟩ (A:=A+c.time) (by positivity) x
    let F₀ := clockContinuation a (J.schedule (c::cs)).F A x
    let F₁ := clockContinuation a (J.schedule cs).F (A+c.time) x
    let F₂ := clockContinuation a J.F (A+c.time+clockLength cs) x
    let E₁ := (J.schedule cs).observedSquare a (A+c.time) x
    let E₂ := J.observedSquare a (A+c.time+clockLength cs) x
    let w := (c.mass-a)*(c.time:ℝ)
    have hw : |w| ≤ c.time := by
      dsimp only [w]
      rw [abs_mul,abs_of_nonneg c.time.coe_nonneg]
      apply mul_le_of_le_one_left c.time.coe_nonneg
      exact abs_le.mpr ⟨by linarith [c.positive],by linarith [c.positive]⟩
    have hL := clockLength_nonneg cs
    change |F₀-F₁-w/2*E₁| ≤ 2*(c.time:ℝ)^2 at hh
    change |F₁-F₂-clockExcess a cs/2*E₂| ≤ _ at hi
    change |E₁-E₂| ≤ _ at he
    have h3 : |w/2*(E₁-E₂)| ≤ 2*(c.time:ℝ)*clockLength cs := by
      rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      calc
        _ ≤ |w|/2*(4*clockLength cs) := mul_le_mul_of_nonneg_left he (by positivity)
        _ ≤ (c.time:ℝ)/2*(4*clockLength cs) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring
    have ht : |F₀-F₂-(w+clockExcess a cs)/2*E₂| ≤
        2*(c.time:ℝ)^2+2*(clockLength cs)^2+2*(c.time:ℝ)*clockLength cs := by
      calc
        _ = |(F₀-F₁-w/2*E₁)+(F₁-F₂-clockExcess a cs/2*E₂)+w/2*(E₁-E₂)| := by congr 1; ring
        _ ≤ |F₀-F₁-w/2*E₁|+|F₁-F₂-clockExcess a cs/2*E₂|+|w/2*(E₁-E₂)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ _ := add_le_add (add_le_add hh hi) h3
    have hb : 2*(c.time:ℝ)^2+2*(clockLength cs)^2+2*(c.time:ℝ)*clockLength cs ≤
        2*((c.time:ℝ)+clockLength cs)^2 := by
      nlinarith [mul_nonneg c.time.coe_nonneg hL]
    simpa only [clockLength_cons,clockExcess_cons,add_assoc,F₀,F₂,E₂,w] using ht.trans hb

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.flatten_profile_signed_error {J K : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    {a A l : ℝ} (t : ℝ≥0) (ha : 0 < a) (ha1 : a ≤ 1)
    (hA0 : 0 ≤ A) (hK : K.F = J.nonnegativeProfileValue α l t) (x : Fin 1 → ℝ) :
    |clockContinuation a K.F A x-clockContinuation a J.F (A+t) x-
      ((∫ s in l..l+t, α.mass s-a)/2)*J.observedSquare a (A+t) x| ≤
      2*(t:ℝ)^2 := by
  have hg (k : ℕ) (y : Fin 1 → ℝ) :
      |(J.schedule ((α.cappedApprox k).grid l t k)).F y-K.F y| ≤ (t:ℝ)*(1/2:ℝ)^k := by
    rw [hK,(α.cappedApprox k).grid_eq_linear]
    have he : ((2^k:ℕ):ℝ≥0)*(t/(2^k:ℝ≥0)) = t := by simp only [Nat.cast_pow,Nat.cast_ofNat]; field_simp
    have hh := J.capped_linear_error (fun _ => 1) (fun i y => by rw [Fin.eq_zero i]; exact hJ.gradient y) α hα k l (t/(2^k:ℝ≥0)) (2^k) y
    rw [he] at hh
    apply hh.trans_eq
    norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.reduceAdd,
      nsmul_eq_mul,Nat.cast_one,one_pow,one_mul,NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat,
      Nat.cast_pow,Nat.cast_ofNat,div_pow,one_div]
    field_simp
    ring
  have ht : Tendsto (fun k => clockContinuation a (J.schedule ((α.cappedApprox k).grid l t k)).F A x)
      atTop (𝓝 (clockContinuation a K.F A x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hdist (k : ℕ) : dist (clockContinuation a (J.schedule ((α.cappedApprox k).grid l t k)).F A x)
        (clockContinuation a K.F A x) ≤ (t:ℝ)*(1/2:ℝ)^k := by
      rw [Real.dist_eq]
      exact clockContinuation_abs_sub_le (J.schedule _).lipschitz K.lipschitz ha (hg k) A x
    exact squeeze_zero (fun _ => dist_nonneg) hdist
      (by simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul (t:ℝ))
  have hw := capped_grid_excess_tendsto α a l t
  apply le_of_tendsto_of_tendsto ((ht.sub_const _).sub ((hw.div_const 2).mul_const _)).abs
    tendsto_const_nhds
  apply Eventually.of_forall
  intro k
  have hh := HeatJet.flatten_schedule_signed_error hJ hA ((α.cappedApprox k).grid l t k) ha ha1
    (fun c hc => ((α.cappedApprox k).grid_mass_bounds l t k hc).2.trans
      (α.cappedApprox_le_one hα k _)) hA0 x
  simpa only [clockLength,PositiveMassProfile.grid_total_time] using hh

theorem scalarTailJet_flatten_signed_error {T q r m : ℝ} (hT : 0 < T) (hq : 0 ≤ q)
    (hqr : q ≤ r) (hr : r ≤ 1) (α : boundedMassProfiles) (hm : 0 < m)
    (hm1 : m ≤ 1) :
    |clockContinuation m (scalarTailJet hT α q).F (T*q) 0-
      clockContinuation m (scalarTailJet hT α r).F (T*r) 0-
      (T/2*(∫ s in q..r, α.val s-m))*(scalarTailJet hT α r).observedSquare m (T*r) 0| ≤
      2*T^2*(r-q)^2 := by
  have hs : 0 ≤ T*(r-q) := mul_nonneg hT.le (sub_nonneg.mpr hqr)
  have he : T*q+T*(r-q)=T*r := by ring
  have hi : (∫ s in T*q..T*r, (rescaledMassProfile α hT).mass s-m) =
      T*(∫ s in q..r, α.val s-m) := by
    change (∫ s in T*q..T*r, (fun z => α.val z-m) (s/T)) = _
    rw [intervalIntegral.integral_comp_div (fun z => α.val z-m) hT.ne']
    simp only [mul_div_cancel_left₀ _ hT.ne',smul_eq_mul]
  have hh := HeatJet.flatten_profile_signed_error (scalarTailJet_admissible hT α r)
    (scalarTailJet_gradientTest hT α r) (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) (A:=T*q) (l:=T*q)
    (Real.toNNReal (T*(r-q))) hm hm1
    (mul_nonneg hT.le hq) (scalarTailJet_restart hT hqr hr α) (0:Fin 1 → ℝ)
  simp only [Real.coe_toNNReal _ hs,he,hi] at hh
  rw [show T*(∫ s in q..r, α.val s-m)/2 = T/2*(∫ s in q..r, α.val s-m) by ring] at hh
  exact hh.trans_eq (by ring)

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem right_derivative_of_quadratic_remainder {F G H : ℝ → ℝ} {q C g : ℝ}
    (hG : HasDerivWithinAt G g (Ioi q) q)
    (hH : ContinuousWithinAt H (Ioi q) q)
    (herr : ∀ᶠ r in 𝓝[>] q, |F q-F r-(G r-G q)*H r| ≤ C*(r-q)^2) :
    HasDerivWithinAt F (-g*H q) (Ioi q) q := by
  let E : ℝ → ℝ := fun r => (F r-F q+(G r-G q)*H r)/(r-q)
  have hE : Tendsto E (𝓝[>] q) (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero E).mpr
    apply squeeze_zero' (Eventually.of_forall (fun r => abs_nonneg (E r)))
    · filter_upwards [herr,self_mem_nhdsWithin] with r he hr
      have hd : 0 < r-q := sub_pos.mpr hr
      show |(F r-F q+(G r-G q)*H r)/(r-q)| ≤ C*(r-q)
      rw [abs_div,abs_of_pos hd,div_le_iff₀ hd]
      have hn : |F r-F q+(G r-G q)*H r| = |F q-F r-(G r-G q)*H r| := by
        rw [show F r-F q+(G r-G q)*H r = -(F q-F r-(G r-G q)*H r) by ring,abs_neg]
      rw [hn]
      exact he.trans_eq (by ring)
    · simpa only [id_eq,sub_self,mul_zero] using
        ((tendsto_id : Tendsto (fun r : ℝ => r) (𝓝[>] q) (𝓝[>] q)).mono_right
          nhdsWithin_le_nhds).sub_const q |>.const_mul C
  apply (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mpr
  have hG' := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hG
  have hh := hE.sub (hG'.mul hH)
  simp only [zero_sub] at hh
  rw [show -g*H q = -(g*H q) by ring]
  apply hh.congr'
  exact Eventually.of_forall fun r => by dsimp [E]; simp only [slope_def_field]; ring

 

theorem scalarTailJet_flatten_hasDerivWithinAt {T q m : ℝ} (hT : 0 < T)
    (hq : 0 ≤ q) (hq1 : q < 1) (α : boundedMassProfiles)
    (hm : 0 < m) (hm1 : m ≤ 1) (hc : ContinuousWithinAt α.val (Ici q) q) :
    HasDerivWithinAt
      (fun r => clockContinuation m (scalarTailJet hT α r).F (T*r) 0)
      (T/2*(m-α.val q)*(scalarTailJet hT α q).observedSquare m (T*q) 0)
      (Ioi q) q := by
  have hi : HasDerivWithinAt (fun r => ∫ s in q..r, α.val s-m)
      (α.val q-m) (Ici q) q :=
    intervalIntegral.integral_hasDerivWithinAt_right
      (α.property.2.intervalIntegrable.sub intervalIntegrable_const)
      (α.property.2.measurable.sub measurable_const).stronglyMeasurable.stronglyMeasurableAtFilter
      ((hc.mono Ioi_subset_Ici_self).sub continuousWithinAt_const)
  have hd := right_derivative_of_quadratic_remainder
    ((hi.mono Ioi_subset_Ici_self).const_mul (T/2))
    ((scalarTailJet_observedSquare_continuous hT α m).continuousWithinAt (s:=Ioi q) (x:=q))
    (C:=2*T^2) (F:=fun r => clockContinuation m (scalarTailJet hT α r).F (T*r) 0)
    (by
      filter_upwards [self_mem_nhdsWithin,
        (show ∀ᶠ r : ℝ in 𝓝[>] q, r < 1 from
          Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hq1))] with r hr hr1
      simpa only [intervalIntegral.integral_same,mul_zero,sub_zero] using
        scalarTailJet_flatten_signed_error hT hq hr.le hr1.le α hm hm1)
  convert hd using 1; ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarTailJet_flatten_continuous {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (m : ℝ) :
    Continuous (fun q => clockContinuation m (scalarTailJet hT α q).F (T*q) 0) :=
  (dynamic_clockContinuation_continuous (scalarTailJet_lipschitz hT α)
    (scalarTailJet_F_continuous hT α) m 0).comp
    ((continuous_const.mul continuous_id).prodMk continuous_id)

 

theorem scalarTailJet_flatten_difference {T q r m : ℝ} (hT : 0 < T) (hq : 0 ≤ q)
    (hqr : q ≤ r) (hr : r ≤ 1) (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s) :
    clockContinuation m (scalarTailJet hT α r).F (T*r) 0-
      clockContinuation m (scalarTailJet hT α q).F (T*q) 0 =
      T/2*(∫ s in q..r, (m-α.val s)*(scalarTailJet hT α s).observedSquare m (T*s) 0) := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hqr
    (scalarTailJet_flatten_continuous hT α m).continuousOn
    (f':=fun s => T/2*(m-α.val s)*(scalarTailJet hT α s).observedSquare m (T*s) 0)
    (fun s hs => scalarTailJet_flatten_hasDerivWithinAt hT (hq.trans hs.1.le)
      (hs.2.trans_le hr) α hm hm1 (hc s))
    (((intervalIntegrable_const.sub α.property.2.intervalIntegrable).const_mul (T/2)).mul_continuousOn
      (scalarTailJet_observedSquare_continuous hT α m).continuousOn)
  rw [← hh,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  ring

theorem scalarTailJet_initial_value {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) :
    (scalarTailJet hT α 0).F 0 = scalarParisiValue hT α+T/2*scalarPenalty α+T/4 := by
  have hh := scalarProfileHeatJet_F (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) (T*0) (Real.toNNReal (T*(1-0))) (0:Fin 1 → ℝ)
  change (scalarTailJet hT α 0).F 0 = _ at hh
  rw [hh]
  simp only [mul_zero,sub_zero,mul_one]
  have he : Real.toNNReal T = (⟨T,hT.le⟩ : ℝ≥0) := by exact NNReal.eq (Real.coe_toNNReal _ hT.le)
  rw [he]
  unfold scalarParisiValue
  ring

theorem scalarPenalty_replace_head_general (α : boundedMassProfiles) {q b : ℝ}
    (hq : q ∈ Icc (0:ℝ) 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hbq : b ≤ α.val q) :
    scalarPenalty (replaceHeadProfile α hb0 hb1 hbq)-scalarPenalty α =
      ∫ s in (0:ℝ)..q, s*(b-α.val s) := by
  let β := replaceHeadProfile α hb0 hb1 hbq
  have hαi := weightedProfile_monotone α
  have hβi := weightedProfile_monotone β
  have hh : (∫ s in (0:ℝ)..q, weightedProfile β s-weightedProfile α s) =
      ∫ s in (0:ℝ)..q, s*(b-α.val s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hq.1
    intro s hs
    change max s 0*β.val s-max s 0*α.val s = s*(b-α.val s)
    rw [max_eq_left hs.1.le,replaceHeadProfile_head α hb0 hb1 hbq ⟨hs.1.le,hs.2⟩]
    ring
  have ht : (∫ s in q..1, weightedProfile β s-weightedProfile α s) = 0 := by
    trans ∫ _s in q..1, (0:ℝ)
    · apply intervalIntegral.integral_congr_Ioo_of_le hq.2
      intro s hs
      change max s 0*β.val s-max s 0*α.val s = 0
      rw [replaceHeadProfile_tail α hq.1 hb0 hb1 hbq hs.1.le,sub_self]
    · simp
  unfold scalarPenalty
  rw [← intervalIntegral.integral_sub hβi.intervalIntegrable hαi.intervalIntegrable,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hβi.intervalIntegrable.sub hαi.intervalIntegrable)
      (hβi.intervalIntegrable.sub hαi.intervalIntegrable),hh,ht,add_zero]

 

theorem scalarParisiValue_replace_head_general {T q m : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioc (0:ℝ) 1) (α : boundedMassProfiles) (hm : 0 < m)
    (hm1 : m ≤ 1) (hmq : m ≤ α.val q)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s) :
    scalarParisiValue hT (replaceHeadProfile α hm.le hm1 hmq)-scalarParisiValue hT α =
      T/2*(∫ s in (0:ℝ)..q, (m-α.val s)*
        ((scalarTailJet hT α s).observedSquare m (T*s) 0-s)) := by
  have he : (scalarTailJet hT (replaceHeadProfile α hm.le hm1 hmq) q).F =
      (scalarTailJet hT α q).F := scalarTailJet_congr hT hq.2 (fun r hr =>
        replaceHeadProfile_tail α hq.1.le hm.le hm1 hmq hr.1.le)
  rw [scalarParisiValue_constant_head hT hq _ hm (fun r hr =>
    replaceHeadProfile_head α hm.le hm1 hmq hr),he]
  have hd := scalarTailJet_flatten_difference hT (q:=0) (m:=m) le_rfl hq.1.le hq.2 α hm hm1 hc
  rw [mul_zero,clockContinuation_zero hm.ne',scalarTailJet_initial_value] at hd
  have hp := scalarPenalty_replace_head_general α ⟨hq.1.le,hq.2⟩ hm.le hm1 hmq
  have hi : IntervalIntegrable (fun s => m-α.val s) volume 0 q :=
    intervalIntegrable_const.sub α.property.2.intervalIntegrable
  have hw : (∫ s in (0:ℝ)..q, (m-α.val s)*
      ((scalarTailJet hT α s).observedSquare m (T*s) 0-s)) =
      (∫ s in (0:ℝ)..q, (m-α.val s)*(scalarTailJet hT α s).observedSquare m (T*s) 0)-
      (∫ s in (0:ℝ)..q, s*(m-α.val s)) := by
    rw [← intervalIntegral.integral_sub
      (hi.mul_continuousOn (scalarTailJet_observedSquare_continuous hT α m).continuousOn)
      (show IntervalIntegrable (fun s => s*(m-α.val s)) volume 0 q from
        hi.continuousOn_mul continuous_id.continuousOn)]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  rw [hw]
  nlinarith [congrArg (fun z : ℝ => T/2*z) hp]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

theorem parametric_testedPartition_continuous {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {F A : X → (ι → ℝ) → ℝ} {C : ℝ≥0} {K : ℝ}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : X × (ι → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : X × (ι → ℝ) => A p.1 p.2))
    (hb : ∀ r y, |A r y| ≤ K) (m : ℝ) (x : ι → ℝ) :
    Continuous (fun p : ℝ × X => ∫ z, A p.2 (x+Real.sqrt p.1 • z)*Real.exp (m*F p.2 (x+Real.sqrt p.1 • z))
      ∂Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let ν := Measure.pi fun _ : ι => gaussianReal 0 1
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  apply continuous_iff_continuousAt.mpr
  intro p
  let B := |F p.2 x|+1
  let Q := Real.sqrt p.1+1
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hcbase : Continuous (fun q : ℝ × X => F q.2 x) := hcF.comp (continuous_snd.prodMk continuous_const)
  have hbase : ∀ᶠ q in 𝓝 p, |F q.2 x| < B := hcbase.abs.continuousAt.eventually
    (eventually_lt_nhds (by dsimp [B]; linarith))
  have hscale : ∀ᶠ q in 𝓝 p, Real.sqrt q.1 < Q :=
    (Real.continuous_sqrt.comp continuous_fst).continuousAt.eventually
      (eventually_lt_nhds (by dsimp [Q]; linarith))
  apply continuousAt_of_dominated
    (bound := fun z => K*Real.exp (|m| *B)*Real.exp (|m| *C*Q*‖z‖))
  · exact Eventually.of_forall fun q => by
      have hmap : Continuous (fun z : ι → ℝ => (q.2,x+Real.sqrt q.1 • z)) := by fun_prop
      exact ((hcA.comp hmap).mul (((hcF.comp hmap).const_mul m).rexp)).aestronglyMeasurable
  · filter_upwards [hbase,hscale] with q hq hq'
    exact Eventually.of_forall fun z => by
      have hK : 0 ≤ K := (abs_nonneg (A q.2 x)).trans (hb q.2 x)
      have hdiff : |F q.2 (x+Real.sqrt q.1 • z)-F q.2 x| ≤ (C:ℝ)*Real.sqrt q.1*‖z‖ := by
        simpa only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _),mul_assoc] using (hF q.2).dist_le_mul (x+Real.sqrt q.1 • z) x
      have hale : |F q.2 (x+Real.sqrt q.1 • z)| ≤ B+(C:ℝ)*Q*‖z‖ := by
        have hh := abs_add_le (F q.2 (x+Real.sqrt q.1 • z)-F q.2 x) (F q.2 x)
        rw [sub_add_cancel] at hh
        have hcomp : (C:ℝ)*Real.sqrt q.1*‖z‖ ≤ (C:ℝ)*Q*‖z‖ := by gcongr
        linarith
      have hexp : Real.exp (m*F q.2 (x+Real.sqrt q.1 • z)) ≤
          Real.exp (|m| *B)*Real.exp (|m| *C*Q*‖z‖) := by
        rw [← Real.exp_add,Real.exp_le_exp]
        have h1 := (le_abs_self (m*F q.2 (x+Real.sqrt q.1 • z))).trans_eq (abs_mul m _)
        have h2 := mul_le_mul_of_nonneg_left hale (abs_nonneg m)
        nlinarith
      change |A q.2 (x+Real.sqrt q.1 • z)*Real.exp (m*F q.2 (x+Real.sqrt q.1 • z))| ≤ _
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul (hb q.2 _) hexp (Real.exp_nonneg _) hK).trans_eq (by ring)
  · exact (hν (|m| *C*Q)).const_mul _
  · exact Eventually.of_forall fun z => by
      have hmap : Continuous (fun q : ℝ × X => (q.2,x+Real.sqrt q.1 • z)) :=
        continuous_snd.prodMk (continuous_const.add ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
      exact ((hcA.comp hmap).mul (((hcF.comp hmap).const_mul m).rexp)).continuousAt

 theorem parametric_clockTest_continuous {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {F A : X → (ι → ℝ) → ℝ} {C : ℝ≥0} {K : ℝ}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : X × (ι → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : X × (ι → ℝ) => A p.1 p.2))
    (hb : ∀ r y, |A r y| ≤ K) (m : ℝ) (x : ι → ℝ) :
    Continuous (fun p : ℝ × X => clockTest m (F p.2) (A p.2) p.1 x) := by
  have hn := parametric_testedPartition_continuous hF hcF hcA hb m x
  have hd := parametric_testedPartition_continuous (A := fun _ _ => 1) hF hcF continuous_const
    (fun _ _ => le_refl |(1:ℝ)|) m x
  simp only [one_mul] at hd
  have hh := hn.div hd (fun p => (partition_pos m
    ((ExpNormBounded.exp_lipschitz (hF p.2) m).affine_integrable (exponentialIncrement_gaussian (fun _ : ι => 1)) x _)).ne')
  exact hh.congr fun p => (clockTest_eq_all (hF p.2).continuous
    (hcA.comp (continuous_const.prodMk continuous_id)) m p.1 x).symm

end SKFluctuations.Hierarchy

end

end OAI
