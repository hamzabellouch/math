import Mathlib
import OAI.Analysis.HardSphere.Geometry.SmoothMultiplier

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

lemma coordinateLine_cons_succ {n : ℕ} {L : Length} (x : Torus L)
    (Y : Configuration n L) (i : Fin n) (j : Fin 3) (t : AddCircle L.val) :
    coordinateLine (Fin.cons x Y) (i.succ,j) t=Fin.cons x (coordinateLine Y (i,j) t) := by
  funext k q
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp [coordinateLine]
  · by_cases h : k=i
    · subst k; simp [coordinateLine]
    · simp [coordinateLine,Pi.single_eq_of_ne h,Pi.single_eq_of_ne (fun e ↦ h (Fin.succ_injective _ e))]

lemma SmoothMultiplier.hasDerivAt_fiberIntegral {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (Y : Configuration n L) (i : Fin n) (j : Fin 3) :
    HasDerivAt (fun t : ℝ ↦ ∫ x : Torus L,
      f.toFun (Fin.cons x (coordinateLine Y (i,j) (t : AddCircle L.val))))
      (∫ x : Torus L, coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)) 0 := by
  let F : ℝ → Torus L → ℂ := fun t x ↦
    f.toFun (Fin.cons x (coordinateLine Y (i,j) (t : AddCircle L.val)))
  let D : ℝ → Torus L → ℂ := fun t x ↦
    coordDerivative (n+1) L f.toFun (i.succ,j)
      (Fin.cons x (coordinateLine Y (i,j) (t : AddCircle L.val)))
  have cF (t) : Continuous (F t) :=
    (continuous_of_continuous_lift f.smooth.continuous).comp
      ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
        (continuous_const : Continuous (fun _ : Torus L ↦ coordinateLine Y (i,j) (t : AddCircle L.val))))
  have cD (t) : Continuous (D t) :=
    (continuous_coordDerivative f.smooth (i.succ,j)).comp
      ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
        (continuous_const : Continuous (fun _ : Torus L ↦ coordinateLine Y (i,j) (t : AddCircle L.val))))
  let d : C(Configuration (n+1) L,ℂ) :=
    ⟨_,continuous_coordDerivative f.smooth (i.succ,j)⟩
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (μ := (volume : Measure (Torus L))) (s := Set.univ) (x₀ := 0)
    (bound := fun _ ↦ ‖d‖) univ_mem
    (Eventually.of_forall fun t ↦ (cF t).aestronglyMeasurable)
    ((cF 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (cD 0).aestronglyMeasurable
    (Eventually.of_forall fun x t _ ↦ d.norm_coe_le_norm _)
    (integrable_const _) (Eventually.of_forall fun x t _ ↦ by
      have hh := hasDerivAt_coordinateLine (f.smooth.differentiable (by simp))
        (Fin.cons x Y) (i.succ,j) t
      simpa only [coordinateLine_cons_succ] using hh)
  simpa only [F,D,Complex.ofReal_zero,AddCircle.coe_zero,coordinateLine,Pi.single_zero,add_zero] using h.2

lemma SmoothMultiplier.insertion_orthogonal {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (i : Fin n) (j : Fin 3) (Y : Configuration n L) :
    ∫ x : Torus L, conj (f.toFun (Fin.cons x Y))*
      coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0 := by
  have he (X) : f.toFun X*f.toFun X = ((‖f.toFun X‖^2 : ℝ) : ℂ) := by
    calc
      _ = f.toFun X*conj (f.toFun X) := by rw [hr]
      _ = _ := by rw [Complex.mul_conj,Complex.sq_norm]
  have hc (Y) : (∫ x : Torus L, (f.mul f).toFun (Fin.cons x Y))=1 := by
    simp only [SmoothMultiplier.mul,Pi.mul_apply,he]
    rw [integral_complex_ofReal,hn,Complex.ofReal_one]
  have h := (f.mul f).hasDerivAt_fiberIntegral Y i j
  simp only [hc] at h
  have hz := h.unique (hasDerivAt_const (0:ℝ) (1:ℂ))
  have hd := coordDerivative_mul (f.smooth.differentiable (by simp))
    (f.smooth.differentiable (by simp)) (i.succ,j)
  change (∫ x : Torus L, coordDerivative (n+1) L (f.toFun*f.toFun) (i.succ,j) (Fin.cons x Y))=0 at hz
  rw [hd] at hz
  have hfactor : (∫ x : Torus L,
      (f.toFun * coordDerivative (n+1) L f.toFun (i.succ,j) +
        f.toFun * coordDerivative (n+1) L f.toFun (i.succ,j)) (Fin.cons x Y))=
      (2:ℂ)*(∫ x : Torus L, conj (f.toFun (Fin.cons x Y))*
      coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by simp only [Pi.add_apply,Pi.mul_apply,hr]; ring
  rw [hfactor] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

end HardSphere

end

end OAI
