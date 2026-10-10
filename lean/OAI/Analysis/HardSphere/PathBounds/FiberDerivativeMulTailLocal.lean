import Mathlib
import OAI.Analysis.HardSphere.Comparison.SafeMass

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.fiber_derivative_mul_tail_le_local {n : ℕ} {L : Length}
    (g : SmoothMultiplier (n+1) L) (r : SmoothMultiplier n L)
    (hr : ∀ X, conj (g.toFun X)=g.toFun X)
    (p : Direction (n+1)) (Y : Configuration n L)
    (hn : ∀ᶠ Z in 𝓝 Y, g.fiberMass Z=1) :
    ‖r.toFun Y‖^2 * (∫ x : Torus L, ‖coordDerivative (n+1) L g.toFun p (Fin.cons x Y)‖^2) ≤
      ∫ x : Torus L, ‖coordDerivative (n+1) L (fun X ↦ g.toFun X*r.toFun (Fin.tail X)) p
        (Fin.cons x Y)‖^2 := by
  have hd := coordDerivative_mul (g := fun X : Configuration (n+1) L ↦ r.toFun (Fin.tail X))
    (g.smooth.differentiable (by simp))
    ((smooth_tail r.smooth).differentiable (by simp)) p
  have hc : Continuous (fun x : Torus L ↦ (Fin.cons x Y : Configuration (n+1) L)) :=
    (continuous_id : Continuous (id : Torus L → Torus L)).finCons
      (continuous_const : Continuous (fun _ : Torus L ↦ Y))
  have hg := (continuous_of_continuous_lift g.smooth.continuous).comp hc
  have hdg := (continuous_coordDerivative g.smooth p).comp hc
  have hs := r.smooth.differentiable (by simp)
  rcases p with ⟨i,j⟩
  induction i using Fin.cases with
  | zero =>
    simp only [coordDerivative_tail_zero hs j,mul_zero,zero_add] at hd
    rw [show (fun X ↦ g.toFun X*r.toFun (Fin.tail X))=g.toFun*(fun X ↦ r.toFun (Fin.tail X)) from rfl,hd]
    simp only [Pi.mul_apply,Fin.tail_cons,norm_mul,mul_pow]
    rw [integral_const_mul]
  | succ k =>
    have he := g.insertion_orthogonal_local hr k j Y hn
    have ho : (∫ x : Torus L,
        conj (g.toFun (Fin.cons x Y)*coordDerivative n L r.toFun (k,j) Y)*
          (r.toFun Y*coordDerivative (n+1) L g.toFun (k.succ,j) (Fin.cons x Y)))=0 := by
      calc
        _ = (conj (coordDerivative n L r.toFun (k,j) Y)*r.toFun Y)*
            ∫ x : Torus L, conj (g.toFun (Fin.cons x Y))*
              coordDerivative (n+1) L g.toFun (k.succ,j) (Fin.cons x Y) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Eventually.of_forall fun x ↦ by simp only [map_mul]; ring
        _ = 0 := by rw [he,mul_zero]
    have heq := integral_norm_add_sq_orthogonal (hg.mul continuous_const) (continuous_const.mul hdg) ho
    simp only [Pi.mul_apply,Function.comp_def] at heq
    have hd' := coordDerivative_mul (g := fun X : Configuration (n+1) L ↦ r.toFun (Fin.tail X))
      (g.smooth.differentiable (by simp))
      ((smooth_tail r.smooth).differentiable (by simp)) (k.succ,j)
    rw [coordDerivative_tail_succ hs k j] at hd'
    rw [show (fun X ↦ g.toFun X*r.toFun (Fin.tail X))=g.toFun*(fun X ↦ r.toFun (Fin.tail X)) from rfl,hd']
    simp only [Pi.mul_apply,Pi.add_apply,Fin.tail_cons]
    rw [heq]
    simp only [norm_mul,mul_pow]
    rw [integral_const_mul]
    exact le_add_of_nonneg_left (integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma SmoothMultiplier.localNormalization_derivative_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (p : Direction (n+1)) (Y : Configuration n L) (hY : 1/2<f.fiberMass Y) :
    f.fiberMass Y * (∫ x : Torus L,
      ‖coordDerivative (n+1) L (f.localNormalization hr).toFun p (Fin.cons x Y)‖^2) ≤
      ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
  have he : (fun X ↦ (f.localNormalization hr).toFun X *
      (f.safeRoot hr).toFun (Fin.tail X))=f.toFun := by
    funext X
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (safeMass_pos (f.fiberMass_nonneg _))).ne')
  have hh := (f.localNormalization hr).fiber_derivative_mul_tail_le_local (f.safeRoot hr)
    (f.localNormalization_real hr) p Y (f.localNormalization_mass_eventually hr Y hY)
  rw [he] at hh
  have hn : ‖(f.safeRoot hr).toFun Y‖^2=f.fiberMass Y := by
    change ‖(Real.sqrt (safeMass (f.fiberMass Y)) : ℂ)‖^2=_
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (safeMass_pos (f.fiberMass_nonneg _)).le,safeMass_eq hY.le]
  rwa [hn] at hh

end HardSphere

end

end OAI
