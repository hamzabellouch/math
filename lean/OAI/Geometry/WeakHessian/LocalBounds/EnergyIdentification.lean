import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.SobolevCheegerEnergyTop

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile182
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable (hfin : FiniteOnBoundedSets m)
variable (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
  ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))

include hfin hID

lemma identified_sobolev_iff_energy {f : X → ℝ} :
    Sobolev m f ↔ cheegerEnergy m f < ∞ := by
  constructor
  · intro hf
    rw [hID f hf]
    exact ENNReal.ofReal_lt_top
  · exact sobolev_of_cheegerEnergy_lt_top hfin

omit hfin [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma identified_cheegerEnergy_toReal {f : X → ℝ} (hf : Sobolev m f) :
    (cheegerEnergy m f).toReal = (∫ x,(weakGradient m f x)^2 ∂m)/2 := by
  rw [hID f hf,ENNReal.toReal_ofReal (by positivity)]

lemma identified_integral_gamma_eq {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) :
    (∫ x,gamma m f g x ∂m) =
      ((cheegerEnergy m (fun x => f x+g x)).toReal-
        (cheegerEnergy m (fun x => f x-g x)).toReal)/2 := by
  have hp := hf.add hfin hg
  have hn := hf.sub hfin hg
  simp only [gamma,integral_div,integral_sub hp.2.2.integrable_sq hn.2.2.integrable_sq,
    identified_cheegerEnergy_toReal hID hp,identified_cheegerEnergy_toReal hID hn]
  ring

lemma identified_integral_gamma_form (h : QuadraticCheegerEnergy m)
    (f g : (cheeger_closedQuadraticEnergy h).domain) :
    (∫ x,gamma m (f.val : X → ℝ) (g.val : X → ℝ) x ∂m) =
      2*(cheeger_closedQuadraticEnergy h).form f g := by
  have hf := (identified_sobolev_iff_energy hfin hID).mpr f.property
  have hg := (identified_sobolev_iff_energy hfin hID).mpr g.property
  rw [identified_integral_gamma_eq hfin hID hf hg,ClosedQuadraticEnergy.form_apply]
  simp only [energyPolar,ClosedQuadraticEnergy.realEnergy,Submodule.coe_add,
    Submodule.coe_sub,cheegerEnergy_congr_ae (Lp.coeFn_add f.val g.val),
    cheegerEnergy_congr_ae (Lp.coeFn_sub f.val g.val)]
  change ((cheegerEnergy m (fun x => f.val x+g.val x)).toReal-
    (cheegerEnergy m (fun x => f.val x-g.val x)).toReal)/2 =
    2*(((cheegerEnergy m (fun x => f.val x+g.val x)).toReal-
      (cheegerEnergy m (fun x => f.val x-g.val x)).toReal)/4)
  ring

lemma identified_formGenerator_of_isLaplacian (h : QuadraticCheegerEnergy m)
    (u A : Lp ℝ 2 m) (hu : IsLaplacian m (u : X → ℝ) A) :
    (cheeger_closedQuadraticEnergy h).IsFormGenerator u A := by
  have huf := (identified_sobolev_iff_energy hfin hID).mp hu.1
  refine ⟨huf,fun v => ?_⟩
  rw [← identified_integral_gamma_form hfin hID h ⟨u,huf⟩ v]
  have hv := (identified_sobolev_iff_energy hfin hID).mpr v.property
  rw [hu.2.2 v.val hv,L2.inner_def]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => mul_comm (A x) (v.val x))

lemma identified_isLaplacian_of_formGenerator (h : QuadraticCheegerEnergy m)
    (u A : Lp ℝ 2 m) (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A) :
    IsLaplacian m (u : X → ℝ) A := by
  refine ⟨(identified_sobolev_iff_energy hfin hID).mpr hu.1,Lp.memLp A,?_⟩
  intro v hv
  let v' := hv.1.toLp v
  have hv' : cheegerEnergy m (v' : X → ℝ) < ∞ := by
    rw [cheegerEnergy_congr_ae hv.1.coeFn_toLp]
    exact (identified_sobolev_iff_energy hfin hID).mp hv
  have heq := identified_integral_gamma_form hfin hID h ⟨u,hu.1⟩ ⟨v',hv'⟩
  have heq' := hu.2 ⟨v',hv'⟩
  calc
    (∫ x,gamma m (u : X → ℝ) v x ∂m) =
        ∫ x,gamma m (u : X → ℝ) (v' : X → ℝ) x ∂m :=
      integral_congr_ae (gamma_congr_ae EventuallyEq.rfl hv.1.coeFn_toLp.symm)
    _ = -⟪A,v'⟫_ℝ := heq.trans heq'
    _ = -(∫ x,A x*v x ∂m) := by
      rw [L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [hv.1.coeFn_toLp] with x hx
      change v' x*A x=A x*v x
      rw [show v' x=v x from hx]
      exact mul_comm _ _
end WeakHessian

end
end InlinedFile182

end OAI
