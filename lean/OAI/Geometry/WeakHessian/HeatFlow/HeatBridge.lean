import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.VariableDissipationSobolev
import OAI.Geometry.WeakHessian.Sobolev.HessianMonotone

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

def heatBridgeEnergy (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (T s : ℝ) : ℝ :=
  ∫ x,cheegerHeat h s ξ x*gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂m

def heatBridgeError (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (J : X → ℝ) (T s : ℝ) : ℝ :=
  ∫ x,(cheegerHeat h s ξ x*J x)*gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂m

lemma heatBridgeError_const (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (c T s : ℝ) :
    heatBridgeError h f ξ (fun _ => c) T s = c*heatBridgeEnergy h f ξ T s := by
  dsimp [heatBridgeError,heatBridgeEnergy]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

lemma heatBridgeEnergy_zero (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (T : ℝ) :
    heatBridgeEnergy h f ξ T 0 = ∫ x,ξ x*gamma m (cheegerHeat h T f) (cheegerHeat h T f) x ∂m := by
  simp [heatBridgeEnergy,cheegerHeat_zero]

lemma heatBridgeEnergy_end (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (T : ℝ) :
    heatBridgeEnergy h f ξ T T = ∫ x,cheegerHeat h T ξ x*gamma m f f x ∂m := by
  simp [heatBridgeEnergy,cheegerHeat_zero]

lemma heatBridgeEnergy_nonneg (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m)
    (hξ : ∀ᵐ x ∂m,0 ≤ ξ x) (T : ℝ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ heatBridgeEnergy h f ξ T s := by
  apply integral_nonneg_of_ae
  filter_upwards [cheegerHeat_nonneg h hs ξ hξ,
    gamma_self (m := m) (cheegerHeat h (T-s) f)] with x hx hg
  rw [hg]
  positivity

variable [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma WeakHessianUpperBound.heatBridge_integrable {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) : IntervalIntegrable (heatBridgeEnergy h f ξ T) volume 0 T := by
  let C := CG+(|K|+1)/a
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hGH (x : X) : G x ≤ C := by
    have H := (le_abs_self (G x)).trans (hGb x)
    have H' : 0 ≤ (|K|+1)/a := by positivity
    dsimp [C]; linarith
  have hH := hHess.mono_bounded hfin hGc.aestronglyMeasurable aestronglyMeasurable_const hGb
    (fun _ : X => (abs_of_nonneg hC).le) hGH
  have HC := (hH.rcd_weighted_heat_variable_sobolev hN hrcd hfull hfin o hF hFb
    (fun _ : X => (abs_of_nonneg hC).le) continuous_const ha.le h hf hCξ hξb hξ0 hT).1
  have hk : K-a*C ≠ 0 := by
    have he : a*C = a*CG+(|K|+1) := by dsimp [C]; field_simp
    rw [he]
    have : 0 ≤ a*CG := mul_nonneg ha.le hCG
    linarith [le_abs_self K]
  change IntervalIntegrable (heatBridgeError h f ξ (fun _ => K-a*C) T) volume 0 T at HC
  simp only [funext (heatBridgeError_const h f ξ (K-a*C) T)] at HC
  have H := HC.const_mul (K-a*C)⁻¹
  convert H using 1
  ext s
  simp only [← mul_assoc,inv_mul_cancel₀ hk,one_mul]

omit [SigmaFinite m] in
lemma heatBridgeError_decompose
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {f ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hJb : ∀ᵐ x ∂m,|J x| ≤ B)
    (κ a T : ℝ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    heatBridgeError h f ξ (fun x => κ-a*J x) T s =
      κ*heatBridgeEnergy h f ξ T s-a*heatBridgeError h f ξ J T s := by
  have hfs : Sobolev m (cheegerHeat h (T-s) f) := (identified_sobolev_iff_energy hfin hID).mpr
    ((cheegerHeat_energy_le h (sub_nonneg.mpr hs.2) f).trans_lt ((identified_sobolev_iff_energy hfin hID).mp hf))
  have hg := integrable_gamma hfin hfs hfs
  have hρb := cheegerHeat_bounded h hs.1 hCξ ξ hξb
  have hρm := (Lp.memLp (cheegerHeat h s ξ)).aestronglyMeasurable
  have hi : Integrable (fun x => cheegerHeat h s ξ x*gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x) m :=
    hg.bdd_mul hρm (by simpa only [Real.norm_eq_abs] using hρb)
  have hji : Integrable (fun x => (cheegerHeat h s ξ x*J x)*gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x) m := by
    apply hg.bdd_mul (hρm.mul hJm) (c := Cξ*max B 0)
    filter_upwards [hρb,hJb] with x hρ hJ
    change |cheegerHeat h s ξ x*J x| ≤ _
    rw [abs_mul]
    exact mul_le_mul hρ (hJ.trans (le_max_left _ _)) (abs_nonneg _) hCξ
  dsimp [heatBridgeError,heatBridgeEnergy]
  rw [← integral_const_mul,← integral_const_mul,← integral_sub (hi.const_mul κ) (hji.const_mul a)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

end WeakHessian

end
end

end OAI
