import Mathlib
import OAI.Analysis.HardSphere.Geometry.NormalizationDerivative
import OAI.Analysis.HardSphere.Comparison.RawAngleLiftSumSquares

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
open PeriodicCutoff

lemma rawCutoff_gradient_integral_le (n : ℕ) (L : Length) {r M : ℝ} (hr : 0<r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (Y : Configuration n L) :
    (∑ p : Direction (n+1), ∫ y : Torus L,
      ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p (Fin.cons y Y)‖^2)≤
      48*Real.pi^5*M^2*(n:ℝ)*r := by
  have hf (p : Direction (n+1)) : Integrable (fun y : Torus L ↦
      ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p (Fin.cons y Y)‖^2) volume := by
    have hc : Continuous (fun y : Torus L ↦
        ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p (Fin.cons y Y)‖^2) :=
      (((continuous_coordDerivative (rawCutoff n L r).smooth p).comp
        ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
          (continuous_const : Continuous (fun _ : Torus L ↦ Y)))).norm).pow 2
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi (i : Fin n) : Integrable ((box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ))) volume :=
    (integrable_const (1:ℝ)).indicator (box_measurable L.val _ _)
  have hh := integral_mono (integrable_finsetSum Finset.univ (fun p _ ↦ hf p))
    ((integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).const_mul (6*Real.pi^2*M^2/r^2))
    (fun y : Torus L ↦ rawCutoff_gradient_le n L hr hM hb (Fin.cons y Y))
  rw [integral_finsetSum _ (fun p _ ↦ hf p),integral_const_mul,
    integral_finsetSum _ (fun i _ ↦ hi i)] at hh
  have hv : (∑ i : Fin n, ∫ y : Torus L, (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y)≤
      (n:ℝ)*(2*Real.pi*r)^3 := by
    calc
      _ = ∑ i : Fin n, volume.real (box L.val (Real.pi*r) (Y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_indicator_one (box_measurable L.val _ _)
      _ ≤ ∑ i : Fin n, (2*(Real.pi*r))^3 := Finset.sum_le_sum (fun i _ ↦ box_volume_le L.val (by positivity) (Y i))
      _ = _ := by simp [mul_assoc]
  calc
    _ ≤ (6*Real.pi^2*M^2/r^2)*∑ i : Fin n, ∫ y : Torus L,
        (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y := hh
    _ ≤ (6*Real.pi^2*M^2/r^2)*((n:ℝ)*(2*Real.pi*r)^3) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by field_simp [hr.ne']; ring

lemma uniform_insertion : ∃ C : ℝ, 0<C ∧ ∀ (n : ℕ) (L : Length) (r : ℝ), 0<r →
    (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
      ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L r ∧
        ‖v.1‖=‖u.1‖ ∧ energy v≤energy u+(C*(n:ℝ)*r/L.val^3)*‖u.1‖^2 := by
  obtain ⟨M,hM,hb⟩ := exists_transition_bound
  refine ⟨96*Real.pi^5*M^2,by positivity,fun n L r hr hs u hu ↦ ?_⟩
  have hL := L.property
  have hZ (Y : Configuration n L) : L.val^3/2≤(rawCutoff n L r).fiberMass Y := by
    linarith [rawCutoff_mass_lower n L hr Y]
  obtain ⟨v,hv,hn,he⟩ := (rawCutoff n L r).insertion_from_raw
    (rawCutoff_clearance n L hr) (rawCutoff_real n L r) (show 0<L.val^3/2 by positivity)
    hZ (rawCutoff_gradient_integral_le n L hr hM.le hb) hu
  refine ⟨v,hv,hn,?_⟩
  convert he using 1
  congr 2
  ring

end HardSphere

end

end OAI
