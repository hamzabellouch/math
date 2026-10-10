import Mathlib
import OAI.Analysis.HardSphere.Comparison.FDerivIntegral
import OAI.Analysis.HardSphere.PathBounds.ConfigurationTailLp
import OAI.Analysis.HardSphere.Geometry.CoordinateLineConsSucc

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

def torusLiftBox (L : Length) : Set (Fin 3 → ℝ) := Set.univ.pi (fun _ ↦ Set.Icc 0 L.val)

lemma isCompact_torusLiftBox (L : Length) : IsCompact (torusLiftBox L) := by
  simpa only [torusLiftBox] using
    (isCompact_univ_pi (fun _ : Fin 3 ↦ (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) L.val))))

lemma torusLiftBox_preserving (L : Length) :
    MeasurePreserving (fun X : Fin 3 → ℝ ↦ (fun j ↦ (X j : AddCircle L.val)))
      (volume.restrict (torusLiftBox L)) (volume : Measure (Torus L)) := by
  have hp := measurePreserving_pi (fun _ : Fin 3 ↦ volume.restrict (Set.Icc 0 L.val))
    (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val)))
    (f := fun _ X ↦ (X : AddCircle L.val)) (fun _ ↦ ?_)
  · change MeasurePreserving _ ((Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ))).restrict _)
        (Measure.pi (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val))))
    simpa only [torusLiftBox,Measure.restrict_pi_pi] using hp
  · simpa only [zero_add,restrict_Ioc_eq_restrict_Icc] using AddCircle.measurePreserving_mk L.val 0

lemma integral_torusLiftBox {L : Length} (f : Torus L → ℂ) (hf : Continuous f) :
    (∫ X in torusLiftBox L, f (fun j ↦ (X j : AddCircle L.val)))=∫ x : Torus L, f x := by
  have hp := torusLiftBox_preserving L
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable]

lemma SmoothMultiplier.smooth_fiberIntegral {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun Y : LiftedConfiguration n ↦
      ∫ x : Torus L, f.toFun (Fin.cons x (project n L Y))) := by
  let c : LiftedConfiguration n × (Fin 3 → ℝ) →L[ℝ] LiftedConfiguration (n+1) :=
    (ContinuousLinearMap.snd ℝ (LiftedConfiguration n) (Fin 3 → ℝ)).finCons
      (M := fun _ : Fin (n+1) ↦ Fin 3 → ℝ) (ContinuousLinearMap.fst ℝ _ _)
  have hc (z : LiftedConfiguration n × (Fin 3 → ℝ)) :
      project (n+1) L (c z)=Fin.cons (fun j ↦ (z.2 j : AddCircle L.val)) (project n L z.1) := by
    ext i j
    refine Fin.cases ?_ (fun k ↦ ?_) i <;> rfl
  have hs := CompactParameterIntegral.contDiff_integral (μ := (volume : Measure (Fin 3 → ℝ)))
    (f.smooth.comp c.contDiff) (isCompact_torusLiftBox L)
  convert hs using 1
  funext Y
  simp only [Function.comp_def,hc]
  exact (integral_torusLiftBox _ ((continuous_of_continuous_lift f.smooth.continuous).comp
    ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
      (continuous_const : Continuous (fun _ : Torus L ↦ project n L Y))))).symm

def SmoothMultiplier.fiberMass {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (Y : Configuration n L) : ℝ := ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2

lemma SmoothMultiplier.smooth_fiberMass {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun Y : LiftedConfiguration n ↦ f.fiberMass (project n L Y)) := by
  have hs := Complex.reCLM.contDiff.comp (f.mul f).smooth_fiberIntegral
  convert hs using 1
  funext Y
  have he (X) : (f.mul f).toFun X=((‖f.toFun X‖^2:ℝ):ℂ) := by
    change f.toFun X*f.toFun X=_
    calc
      _ = f.toFun X*conj (f.toFun X) := by rw [hr]
      _ = _ := by rw [Complex.mul_conj,Complex.sq_norm]
  simp only [Function.comp_def,he,Complex.reCLM_apply,integral_complex_ofReal,Complex.ofReal_re,
    SmoothMultiplier.fiberMass]

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

def SmoothMultiplier.ofSmooth {n : ℕ} {L : Length} (f : Configuration n L → ℂ)
    (hs : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun X : LiftedConfiguration n ↦ f (project n L X))) :
    SmoothMultiplier n L where
  toFun := f
  smooth := hs
  memLp_top := (continuous_of_continuous_lift hs.continuous).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  partial_memLp_top := fun p ↦ (continuous_coordDerivative hs p).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def SmoothMultiplier.massRoot {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hp : ∀ Y, 0<f.fiberMass Y) : SmoothMultiplier n L :=
  .ofSmooth (fun Y ↦ (Real.sqrt (f.fiberMass Y) : ℂ))
    (Complex.ofRealCLM.contDiff.comp ((f.smooth_fiberMass hr).sqrt (fun _ ↦ (hp _).ne')))

def SmoothMultiplier.normalization {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hp : ∀ Y, 0<f.fiberMass Y) : SmoothMultiplier (n+1) L :=
  .ofSmooth (fun X ↦ f.toFun X/(Real.sqrt (f.fiberMass (Fin.tail X)) : ℂ))
    (by
      simp only [div_eq_mul_inv]
      exact f.smooth.mul ((smooth_tail (f.massRoot hr hp).smooth).inv (fun _ ↦
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp _)).ne')))

lemma SmoothMultiplier.normalization_real {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hp : ∀ Y, 0<f.fiberMass Y) (X) :
    conj ((f.normalization hr hp).toFun X)=(f.normalization hr hp).toFun X := by
  change conj (f.toFun X/(Real.sqrt (f.fiberMass (Fin.tail X)) : ℂ))=_
  rw [map_div₀,Complex.conj_ofReal,hr]
  rfl

lemma SmoothMultiplier.normalization_norm {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hp : ∀ Y, 0<f.fiberMass Y) (Y : Configuration n L) :
    ∫ x : Torus L, ‖(f.normalization hr hp).toFun (Fin.cons x Y)‖^2=1 := by
  change (∫ x : Torus L, ‖f.toFun (Fin.cons x Y)/(Real.sqrt (f.fiberMass Y) : ℂ)‖^2)=1
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),div_pow,Real.sq_sqrt (hp Y).le]
  rw [integral_div]
  exact div_self (hp Y).ne'

lemma SmoothMultiplier.normalization_clearance {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hp : ∀ Y, 0<f.fiberMass Y) (hc : InsertionClearance a f) :
    InsertionClearance a (f.normalization hr hp) := by
  apply Set.Subset.trans (b := tsupport f.toFun) _ hc
  change tsupport (fun X ↦ f.toFun X/(Real.sqrt (f.fiberMass (Fin.tail X)) : ℂ))⊆_
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left

lemma integral_norm_add_sq_orthogonal {A : Type*} [TopologicalSpace A] [CompactSpace A]
    [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    {μ : Measure A} [IsFiniteMeasure μ] {f g : A → ℂ} (hf : Continuous f) (hg : Continuous g)
    (ho : ∫ x, conj (f x)*g x ∂μ=0) :
    ∫ x, ‖f x+g x‖^2 ∂μ=(∫ x, ‖f x‖^2 ∂μ)+(∫ x, ‖g x‖^2 ∂μ) := by
  have hi {E : Type} [NormedAddCommGroup E] {h : A → E} (hc : Continuous h) : Integrable h μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (x : A) : ‖f x+g x‖^2=‖f x‖^2+2*(conj (f x)*g x).re+‖g x‖^2 := by
    simpa only [RCLike.inner_apply',RCLike.re_to_complex] using @norm_add_sq ℂ ℂ _ _ _ (f x) (g x)
  simp_rw [he]
  have hf2 : Integrable (fun x ↦ ‖f x‖^2) μ := hi (hf.norm.pow 2)
  have hg2 : Integrable (fun x ↦ ‖g x‖^2) μ := hi (hg.norm.pow 2)
  have hcross : Integrable (fun x ↦ conj (f x)*g x) μ := hi ((Complex.continuous_conj.comp hf).mul hg)
  have hre : Integrable (fun x ↦ 2*(conj (f x)*g x).re) μ := hcross.re.const_mul 2
  have hRe : (∫ x, (conj (f x)*g x).re ∂μ)=(∫ x, conj (f x)*g x ∂μ).re := by
    simpa only [RCLike.re_to_complex] using integral_re hcross
  rw [integral_add (f := fun x ↦ ‖f x‖^2+2*(conj (f x)*g x).re)
      (g := fun x ↦ ‖g x‖^2) (hf2.add hre) hg2, integral_add hf2 hre, integral_const_mul,
    hRe,ho]
  simp

lemma SmoothMultiplier.fiber_derivative_mul_tail_le {n : ℕ} {L : Length}
    (g : SmoothMultiplier (n+1) L) (r : SmoothMultiplier n L)
    (hr : ∀ X, conj (g.toFun X)=g.toFun X)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖g.toFun (Fin.cons x Y)‖^2=1)
    (p : Direction (n+1)) (Y : Configuration n L) :
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
    have he := g.insertion_orthogonal hr hn k j Y
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

end
end HardSphere

end
end
end
end
end
end

end OAI
