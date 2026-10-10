import Mathlib
import OAI.Analysis.HardSphere.Geometry.TorusLiftBox

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

def safeMass (z : ℝ) : ℝ := z + Real.smoothTransition (2-4*z)

lemma safeMass_ge (z : ℝ) : z ≤ safeMass z :=
  le_add_of_nonneg_right (Real.smoothTransition.nonneg _)

lemma safeMass_pos {z : ℝ} (hz : 0≤z) : 0<safeMass z := by
  by_cases h : z=0
  · subst z
    norm_num [safeMass,Real.smoothTransition.one_of_one_le]
  · exact (lt_of_le_of_ne hz (Ne.symm h)).trans_le (safeMass_ge z)

lemma safeMass_eq {z : ℝ} (hz : 1/2≤z) : safeMass z=z := by
  rw [safeMass,Real.smoothTransition.zero_of_nonpos (by linarith),add_zero]

lemma safeMass_smooth : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) safeMass :=
  contDiff_id.add (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))

lemma SmoothMultiplier.fiberMass_nonneg {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (Y : Configuration n L) : 0≤f.fiberMass Y :=
  integral_nonneg fun _ ↦ sq_nonneg _

def SmoothMultiplier.safeRoot {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) : SmoothMultiplier n L :=
  .ofSmooth (fun Y ↦ (Real.sqrt (safeMass (f.fiberMass Y)) : ℂ))
    (Complex.ofRealCLM.contDiff.comp ((safeMass_smooth.comp (f.smooth_fiberMass hr)).sqrt
      (fun _Y ↦ (safeMass_pos (f.fiberMass_nonneg _)).ne')))

def SmoothMultiplier.localNormalization {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) : SmoothMultiplier (n+1) L :=
  .ofSmooth (fun X ↦ f.toFun X/(Real.sqrt (safeMass (f.fiberMass (Fin.tail X))) : ℂ))
    (by
      simp only [div_eq_mul_inv]
      exact f.smooth.mul ((smooth_tail (f.safeRoot hr).smooth).inv (fun _ ↦
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (safeMass_pos (f.fiberMass_nonneg _))).ne')))

lemma SmoothMultiplier.localNormalization_real {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X) (X) :
    conj ((f.localNormalization hr).toFun X)=(f.localNormalization hr).toFun X := by
  change conj (f.toFun X/(Real.sqrt (safeMass (f.fiberMass (Fin.tail X))) : ℂ))=_
  rw [map_div₀,Complex.conj_ofReal,hr]
  rfl

lemma SmoothMultiplier.localNormalization_mass {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X) (Y : Configuration n L) :
    (f.localNormalization hr).fiberMass Y=f.fiberMass Y/safeMass (f.fiberMass Y) := by
  change (∫ x : Torus L, ‖f.toFun (Fin.cons x Y)/(Real.sqrt (safeMass (f.fiberMass Y)) : ℂ)‖^2)=_
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),div_pow,Real.sq_sqrt (safeMass_pos (f.fiberMass_nonneg Y)).le]
  exact integral_div _ _

lemma SmoothMultiplier.localNormalization_mass_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X) (Y : Configuration n L) :
    (f.localNormalization hr).fiberMass Y≤1 := by
  rw [f.localNormalization_mass hr,div_le_one (safeMass_pos (f.fiberMass_nonneg Y))]
  exact safeMass_ge _

lemma SmoothMultiplier.localNormalization_mass_eq {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X) (Y : Configuration n L)
    (hY : 1/2≤f.fiberMass Y) : (f.localNormalization hr).fiberMass Y=1 := by
  rw [f.localNormalization_mass hr,safeMass_eq hY]
  exact div_self (by linarith)

lemma SmoothMultiplier.localNormalization_clearance {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hc : InsertionClearance a f) : InsertionClearance a (f.localNormalization hr) := by
  apply Set.Subset.trans (b := tsupport f.toFun) _ hc
  change tsupport (fun X ↦ f.toFun X/(Real.sqrt (safeMass (f.fiberMass (Fin.tail X))) : ℂ))⊆_
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left

lemma SmoothMultiplier.insertion_orthogonal_local {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (i : Fin n) (j : Fin 3) (Y : Configuration n L)
    (hn : ∀ᶠ Z in 𝓝 Y, f.fiberMass Z=1) :
    ∫ x : Torus L, conj (f.toFun (Fin.cons x Y))*
      coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0 := by
  have he (X) : f.toFun X*f.toFun X = ((‖f.toFun X‖^2 : ℝ) : ℂ) := by
    calc
      _ = f.toFun X*conj (f.toFun X) := by rw [hr]
      _ = _ := by rw [Complex.mul_conj,Complex.sq_norm]
  have hc : ∀ᶠ Z in 𝓝 Y, (∫ x : Torus L, (f.mul f).toFun (Fin.cons x Z))=1 := by
    filter_upwards [hn] with Z hZ
    simp only [SmoothMultiplier.mul,Pi.mul_apply,he]
    rw [integral_complex_ofReal]
    change ((f.fiberMass Z : ℝ) : ℂ)=1
    rw [hZ,Complex.ofReal_one]
  have ht : Tendsto (fun t : ℝ ↦ coordinateLine Y (i,j) (t : AddCircle L.val)) (𝓝 0) (𝓝 Y) := by
    have cc : Continuous (fun t : ℝ ↦ coordinateLine Y (i,j) (t : AddCircle L.val)) :=
      (continuous_coordinateLine Y (i,j)).comp (AddCircle.continuous_mk' L.val)
    simpa only [AddCircle.coe_zero,coordinateLine,Pi.single_zero,add_zero] using cc.tendsto (0:ℝ)
  have h := (f.mul f).hasDerivAt_fiberIntegral Y i j
  have hz := h.unique ((hasDerivAt_const (0:ℝ) (1:ℂ)).congr_of_eventuallyEq (ht.eventually hc))
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

lemma SmoothMultiplier.localNormalization_mass_eventually {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X) (Y : Configuration n L)
    (hY : 1/2<f.fiberMass Y) : ∀ᶠ Z in 𝓝 Y, (f.localNormalization hr).fiberMass Z=1 := by
  have hc := continuous_of_continuous_lift (f.smooth_fiberMass hr).continuous
  filter_upwards [hc.continuousAt.eventually (eventually_gt_nhds hY)] with Z hZ
  exact f.localNormalization_mass_eq hr Z hZ.le

end HardSphere

end

end OAI
