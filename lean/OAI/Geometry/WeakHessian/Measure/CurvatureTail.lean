import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.DriftHeatSobolevPointwise
import OAI.Geometry.WeakHessian.LocalBounds.LocalizedCertificate
import OAI.Geometry.WeakHessian.Measure.DaviesTail

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.weighted_heat_gamma_bounded {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
    {Lf : ℝ} (hLf : 0 ≤ Lf)
    (hDb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|weakGradient (exponentialMeasure m (fun x => a*F x)) f x| ≤ Lf)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),
      gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h t f) (cheegerHeat h t f) x ≤
        localizedHeatM K a CG T*Lf^2 := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hΓ : MemLp (gamma ν f f) 2 ν :=
    (memLp_mul_bounded hf.2.2 hf.2.2.aestronglyMeasurable hDb).ae_eq (by
      filter_upwards [gamma_self (m := ν) f] with x hx
      simp only [hx,pow_two]; rfl)
  have hΓb : ∀ᵐ x ∂ν,|hΓ.toLp _ x| ≤ Lf^2 := by
    filter_upwards [hΓ.coeFn_toLp,gamma_self (m := ν) f,hDb] with x hx hg hb
    rw [hx,hg,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hLf).mpr hb
  have HB := hHess.rcd_weighted_heat_gradient_sobolev_pointwise hN hrcd hfull hfin o hF hFb hGb hGc ha h hf hΓ ht
  have hBound := cheegerHeat_bounded h ht (sq_nonneg Lf) (hΓ.toLp _) hΓb
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hM : Real.exp (-(2*(K-a*CG))*t) ≤ localizedHeatM K a CG T := by
    apply Real.exp_le_exp.mpr
    have hKT : 0 ≤ |K|+a*CG := by positivity
    have hk : -(2*(K-a*CG)) ≤ 2*(|K|+a*CG) := by linarith [neg_le_abs K]
    exact (mul_le_mul_of_nonneg_right hk ht).trans (mul_le_mul_of_nonneg_left htT (by positivity))
  filter_upwards [HB,hBound] with x hx hb
  exact hx.trans ((mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_right hM (sq_nonneg Lf)))

omit [SigmaFinite m] in
lemma heatBridgeError_le_tail
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {f ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) (hξi : Integrable ξ m)
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ) (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂m,0 ≤ ξ x)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hB : 0 ≤ B)
    (hJb : ∀ᵐ x ∂m,|J x| ≤ B) (hJ0 : ∀ᵐ x ∂m,0 ≤ J x)
    {R : ℝ} (hJzero : ∀ᵐ x ∂m,dist x o < R → J x = 0)
    {T s C : ℝ} (hs : s ∈ Icc 0 T) (hC : 0 ≤ C)
    (hΓ : ∀ᵐ x ∂m,gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ≤ C) :
    heatBridgeError h f ξ J T s ≤ B*C*
      (∫ x,cheegerHeat h s ξ x*(Ici R).indicator (fun _ : ℝ => (1:ℝ)) (dist x o) ∂m) := by
  let η := fun x : X => (Ici R).indicator (fun _ : ℝ => (1:ℝ)) (dist x o)
  have hηm : AEStronglyMeasurable η m :=
    ((measurable_const.indicator measurableSet_Ici).comp (continuous_id.dist continuous_const).measurable).aestronglyMeasurable
  have hηb : ∀ᵐ x ∂m,‖η x‖ ≤ 1 := ae_of_all _ fun x => by
    dsimp [η]; by_cases hx : R ≤ dist x o <;> simp [hx]
  have hhi := (cheegerHeat_integrable hfin o h ξ hξi hs.1).1
  have hti := hhi.mul_bdd hηm hηb
  rw [← integral_const_mul]
  apply integral_mono_ae (heatBridgeError_integrable hfin hID h hf hCξ hξb hJm hJb T hs) (hti.const_mul (B*C))
  filter_upwards [cheegerHeat_nonneg h hs.1 ξ hξ0,hJb,hJ0,hJzero,hΓ,
    gamma_self (m := m) (cheegerHeat h (T-s) f)] with x hx hJ hJn hz hG hg
  dsimp only [η]
  by_cases hR : R ≤ dist x o
  · rw [indicator_of_mem (show dist x o ∈ Ici R from hR),mul_one]
    have H := mul_le_mul ((le_abs_self _).trans hJ) hG (by rw [hg]; positivity) hB
    nlinarith [mul_le_mul_of_nonneg_left H hx]
  · rw [hz (lt_of_not_ge hR),mul_zero,zero_mul]
    exact mul_nonneg (mul_nonneg hB hC) (mul_nonneg hx (by simp [hR]))

def curvatureTailBound (K a c CG U Lf Q d β R r : ℝ) : ℝ :=
  2*a*U*(CG+|c|)*localizedHeatM K a CG U*Lf^2*Q*Real.exp (β^2*U-β*(R-r)+d*R)

lemma WeakHessianUpperBound.localized_heatError_tail_bound {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
    {Lf : ℝ} (hLf : 0 ≤ Lf)
    (hDb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|weakGradient (exponentialMeasure m (fun x => a*F x)) f x| ≤ Lf)
    (hξi : Integrable ξ (exponentialMeasure m (fun x => a*F x)))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {d β r R T U Q c : ℝ} (hd : 0 ≤ d) (hdβ : d ≤ β)
    (hdecay : MemLp (fun x => Real.exp (-d*dist x o)) 2 (exponentialMeasure m (fun x => a*F x)))
    (hsupp : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),r ≤ dist x o → ξ x = 0)
    (hlocal : ∀ x,dist x o < R → G x ≤ c)
    (hT : 0 ≤ T) (hTU : T ≤ U)
    (hQ : ‖ξ‖*‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖ ≤ Q) :
    localizedHeatError h ξ G K a c CG T f ≤ curvatureTailBound K a c CG U Lf Q d β R r := by
  let ν := exponentialMeasure m (fun x => a*F x)
  let J := fun x => max (G x-c) 0
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (exponentialMeasure_comparable (m := m) hVB).1 (exponentialMeasure_comparable (m := m) hVB).2
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hJm : AEStronglyMeasurable J ν := ((hGc.sub continuous_const).max continuous_const).aestronglyMeasurable
  have hJb : ∀ᵐ x ∂ν,|J x| ≤ CG+|c| := ae_of_all _ fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · linarith [(abs_le.mp (hGb x)).2,neg_le_abs c]
    · positivity
  have hJ0 : ∀ᵐ x ∂ν,0 ≤ J x := ae_of_all _ fun _ => le_max_right _ _
  have hJz : ∀ᵐ x ∂ν,dist x o < R → J x = 0 := ae_of_all _ fun x hx => max_eq_right (sub_nonpos.mpr (hlocal x hx))
  have hIn := (hHess.localized_heat_gradient hN hrcd hfull hfin o hF hFb hGb hGc ha h (f := f) hf hCξ hξb hξ0 c hT).2.1
  let C := (CG+|c|)*(localizedHeatM K a CG U*Lf^2)*Q*Real.exp (β^2*U-β*(R-r)+d*R)
  have hQ0 : 0 ≤ Q := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hQ
  have hCn : 0 ≤ C := by dsimp [C,localizedHeatM]; positivity
  have hD (s : ℝ) (hs : s ∈ Icc 0 T) : heatBridgeError h f ξ J T s ≤ C := by
    have HG := hHess.weighted_heat_gamma_bounded hN hrcd hfull hfin o hF hFb hGb hGc ha.le h hf hLf hDb
      (sub_nonneg.mpr hs.2) (by linarith [hs.1] : T-s ≤ U)
    have HI := heatBridgeError_le_tail hnfin o hID h hf hξi hCξ hξb hξ0 hJm
      (by positivity : 0 ≤ CG+|c|) hJb hJ0 hJz hs (by dsimp [localizedHeatM]; positivity) HG
    have HT := identified_heat_tail_bound hID hpar hnfin o h ξ hd hdβ hdecay hsupp hs.1 (R := R)
    have HE := Real.exp_le_exp.mpr (show β^2*s-β*(R-r)+d*R ≤ β^2*U-β*(R-r)+d*R by
      nlinarith [sq_nonneg β,hs.2])
    have HQ := mul_le_mul hQ HE (Real.exp_pos _).le hQ0
    have HH := ((le_abs_self _).trans HT).trans HQ
    exact HI.trans ((mul_le_mul_of_nonneg_left HH (by dsimp [localizedHeatM]; positivity)).trans_eq (by dsimp [C]; ring))
  have HI := intervalIntegral.integral_mono_on hT hIn (intervalIntegrable_const (c := C)) hD
  rw [intervalIntegral.integral_const] at HI
  simp only [sub_zero,smul_eq_mul] at HI
  have HInonneg : 0 ≤ ∫ s in 0..T,heatBridgeError h f ξ J T s :=
    intervalIntegral.integral_nonneg hT (fun s hs => heatBridgeError_nonneg h f ξ hξ0 hJ0 T hs.1)
  have hDen := localizedHeatDen_one_le K a c CG hT
  have hθ : 2*a/localizedHeatDen K a c CG T ≤ 2*a := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hDen)).mpr
    nlinarith
  change (2*a/localizedHeatDen K a c CG T)*(∫ s in 0..T,heatBridgeError h f ξ J T s) ≤ _
  exact (mul_le_mul_of_nonneg_right hθ HInonneg).trans
    ((mul_le_mul_of_nonneg_left (HI.trans (mul_le_mul_of_nonneg_right hTU hCn)) (by positivity : 0 ≤ 2*a)).trans_eq
      (by dsimp [C,curvatureTailBound]; ring))

end WeakHessian

end
end

end OAI
