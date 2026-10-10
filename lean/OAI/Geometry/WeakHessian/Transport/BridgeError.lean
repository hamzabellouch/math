import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatBridge
import OAI.Geometry.WeakHessian.Transport.FormAction

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma heatBridgeError_nonneg (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m)
    (hξ : ∀ᵐ x ∂m,0 ≤ ξ x) {J : X → ℝ} (hJ : ∀ᵐ x ∂m,0 ≤ J x)
    (T : ℝ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ heatBridgeError h f ξ J T s := by
  apply integral_nonneg_of_ae
  filter_upwards [cheegerHeat_nonneg h hs ξ hξ,hJ,
    gamma_self (m := m) (cheegerHeat h (T-s) f)] with x hx hJ hg
  rw [hg]; positivity

lemma heatBridgeError_integrable
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {f ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hJb : ∀ᵐ x ∂m,|J x| ≤ B)
    (T : ℝ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    Integrable (fun x => (cheegerHeat h s ξ x*J x)*
      gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x) m := by
  have hfs : Sobolev m (cheegerHeat h (T-s) f) := (identified_sobolev_iff_energy hfin hID).mpr
    ((cheegerHeat_energy_le h (sub_nonneg.mpr hs.2) f).trans_lt ((identified_sobolev_iff_energy hfin hID).mp hf))
  apply (integrable_gamma hfin hfs hfs).bdd_mul
    ((Lp.memLp (cheegerHeat h s ξ)).aestronglyMeasurable.mul hJm) (c := Cξ*max B 0)
  filter_upwards [cheegerHeat_bounded h hs.1 hCξ ξ hξb,hJb] with x hρ hJ
  change |cheegerHeat h s ξ x*J x| ≤ _
  rw [abs_mul]
  exact mul_le_mul hρ (hJ.trans (le_max_left _ _)) (abs_nonneg _) hCξ

lemma heatBridgeError_le_energy
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {f ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ) (hξ0 : ∀ᵐ x ∂m,0 ≤ ξ x)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hJb : ∀ᵐ x ∂m,|J x| ≤ B)
    (T : ℝ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    heatBridgeError h f ξ J T s ≤ B*heatBridgeEnergy h f ξ T s := by
  rw [← heatBridgeError_const]
  apply integral_mono_ae (heatBridgeError_integrable hfin hID h hf hCξ hξb hJm hJb T hs)
    (heatBridgeError_integrable hfin hID h hf hCξ hξb aestronglyMeasurable_const
      (ae_of_all _ fun _ => le_refl |B|) T hs)
  filter_upwards [cheegerHeat_nonneg h hs.1 ξ hξ0,hJb,
    gamma_self (m := m) (cheegerHeat h (T-s) f)] with x hx hJ hg
  rw [hg]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hJ) hx) (sq_nonneg _)

lemma heatBridgeError_split
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m)
    (h : QuadraticCheegerEnergy m) {f g ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) (hg : Sobolev m (g : X → ℝ))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ) (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂m,0 ≤ ξ x)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hJb : ∀ᵐ x ∂m,|J x| ≤ B)
    (hJ0 : ∀ᵐ x ∂m,0 ≤ J x) (T c : ℝ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    heatBridgeError h (f+c•g) ξ J T s ≤
      2*heatBridgeError h f ξ J T s+2*c^2*heatBridgeError h g ξ J T s := by
  have hPS (f : Lp ℝ 2 m) (hf : Sobolev m (f : X → ℝ)) :
      Sobolev m (cheegerHeat h (T-s) f) := (identified_sobolev_iff_energy hfin hID).mpr
    ((cheegerHeat_energy_le h (sub_nonneg.mpr hs.2) f).trans_lt ((identified_sobolev_iff_energy hfin hID).mp hf))
  let ρ := fun x => cheegerHeat h s ξ x*J x
  have hρm : AEStronglyMeasurable ρ m :=
    (Lp.memLp (cheegerHeat h s ξ)).aestronglyMeasurable.mul hJm
  have hρb : ∀ᵐ x ∂m,|ρ x| ≤ Cξ*max B 0 := by
    filter_upwards [cheegerHeat_bounded h hs.1 hCξ ξ hξb,hJb] with x hρ hJ
    dsimp [ρ]; rw [abs_mul]
    exact mul_le_mul hρ (hJ.trans (le_max_left _ _)) (abs_nonneg _) hCξ
  have he (v : Lp ℝ 2 m) : heatBridgeError h v ξ J T s =
      ∫ x,ρ x*(weakGradient m (cheegerHeat h (T-s) v) x)^2 ∂m := by
    apply integral_congr_ae
    filter_upwards [gamma_self (m := m) (cheegerHeat h (T-s) v)] with x hx
    rw [hx]
  have Hp := weighted_gradient_add_smul hfin hpar (hPS f hf) (hPS g hg) hρm hρb c
  have Hm := weighted_gradient_add_smul hfin hpar (hPS f hf) (hPS g hg) hρm hρb (-c)
  have Hn := heatBridgeError_nonneg h (f+(-c)•g) ξ hξ0 hJ0 T hs.1
  rw [he,map_add,map_smul] at Hn
  rw [he,map_add,map_smul,he,he]
  rw [Hm] at Hn
  rw [Hp]
  nlinarith

lemma heatBridgeError_integral_split
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m)
    (h : QuadraticCheegerEnergy m) {f g ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) (hg : Sobolev m (g : X → ℝ))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ) (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂m,0 ≤ ξ x)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hJb : ∀ᵐ x ∂m,|J x| ≤ B)
    (hJ0 : ∀ᵐ x ∂m,0 ≤ J x) {T : ℝ} (hT : 0 ≤ T)
    (hDi : ∀ v : Lp ℝ 2 m, Sobolev m (v : X → ℝ) →
      IntervalIntegrable (heatBridgeError h v ξ J T) volume 0 T) (c : ℝ) :
    (∫ s in 0..T,heatBridgeError h (f+c•g) ξ J T s) ≤
      2*(∫ s in 0..T,heatBridgeError h f ξ J T s)+
        2*c^2*(∫ s in 0..T,heatBridgeError h g ξ J T s) := by
  have hfg : Sobolev m (f+c•g : Lp ℝ 2 m) := by
    apply (sobolev_congr_ae ?_).mpr (hf.add hfin (hg.const_mul c))
    filter_upwards [Lp.coeFn_add f (c•g),Lp.coeFn_smul c g] with x ha hc
    simp only [ha,hc,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have H := intervalIntegral.integral_mono_on hT (hDi _ hfg)
    (((hDi f hf).const_mul 2).add ((hDi g hg).const_mul (2*c^2)))
    (fun s hs => heatBridgeError_split hfin hID hpar h hf hg hCξ hξb hξ0 hJm hJb hJ0 T c hs)
  rw [intervalIntegral.integral_add ((hDi f hf).const_mul 2)
    ((hDi g hg).const_mul (2*c^2)),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at H
  exact H

lemma heatBridgeError_integral_le
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {f ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ) (hξ0 : ∀ᵐ x ∂m,0 ≤ ξ x)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hB : 0 ≤ B)
    (hJb : ∀ᵐ x ∂m,|J x| ≤ B) {T M : ℝ} (hT : 0 ≤ T)
    (hDi : IntervalIntegrable (heatBridgeError h f ξ J T) volume 0 T)
    (hEM : ∀ s ∈ Icc 0 T,heatBridgeEnergy h f ξ T s ≤ M*heatBridgeEnergy h f ξ T T) :
    (∫ s in 0..T,heatBridgeError h f ξ J T s) ≤ B*T*M*heatBridgeEnergy h f ξ T T := by
  have H := intervalIntegral.integral_mono_on hT hDi
    (intervalIntegrable_const (c := B*M*heatBridgeEnergy h f ξ T T)) (by
      intro s hs
      exact (heatBridgeError_le_energy hfin hID h hf hCξ hξb hξ0 hJm hJb T hs).trans
        ((mul_le_mul_of_nonneg_left (hEM s hs) hB).trans_eq (by ring)))
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_left_comm,mul_assoc] using H

end WeakHessian

end
end

end OAI
