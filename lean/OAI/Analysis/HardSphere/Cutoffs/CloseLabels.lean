import Mathlib
import OAI.Analysis.HardSphere.Geometry.HeadLift
import OAI.Analysis.HardSphere.Cutoffs.RawAngleLift

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
namespace HardSphere.TightCutoff
open PeriodicCutoff MeasureTheory Set Filter
open scoped ComplexConjugate

def closeLabels {n : ℕ} {L : Length} (r : ℝ) (w : SmoothMultiplier 1 L)
    (Y : Configuration n L) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ ∃ y∈tsupport w.orbital, torusDistance L y (Y i)≤2*r)

lemma mem_closeLabels_of_near {n : ℕ} {L : Length} {r : ℝ} (hr : 0<r)
    (w : SmoothMultiplier 1 L) (Y : Configuration n L) {y : Torus L} (hy : w.orbital y≠0)
    (i : Fin n) (hi : y∈near L.val r (Y i)) : i∈closeLabels r w Y := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,subset_tsupport w.orbital hy,near_distance hr hi⟩

def orbitalCutoff {L : Length} (n : ℕ) (r : ℝ) (w : SmoothMultiplier 1 L) : SmoothMultiplier (n+1) L :=
  (w.liftHead n).mul (rawCutoff n L r)

lemma orbitalCutoff_real {L : Length} (n : ℕ) (r : ℝ) (w : SmoothMultiplier 1 L)
    (hw : ∀ X, conj (w.toFun X)=w.toFun X) (X : Configuration (n+1) L) :
    conj ((orbitalCutoff n r w).toFun X)=(orbitalCutoff n r w).toFun X := by
  change conj (w.orbital (X 0)*(rawCutoff n L r).toFun X)=_
  rw [map_mul,rawCutoff_real]
  change conj (w.toFun (fun _ ↦ X 0)) * _ = _
  rw [hw]
  rfl

lemma orbitalCutoff_clearance {L : Length} (n : ℕ) {r : ℝ} (hr : 0<r) (w : SmoothMultiplier 1 L) :
    InsertionClearance r (orbitalCutoff n r w) :=
  Set.Subset.trans tsupport_mul_subset_right (rawCutoff_clearance n L hr)

lemma weighted_near_le {n : ℕ} {L : Length} {r : ℝ} (hr : 0<r)
    (w : SmoothMultiplier 1 L) (Y : Configuration n L) (y : Torus L) :
    ‖w.orbital y‖^2 * ∑ i : Fin n, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y ≤
      w.orbitalBound * ∑ i ∈ closeLabels r w Y, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
  classical
  have hb (i : Fin n) : 0≤(near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y :=
    Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  by_cases hy : w.orbital y=0
  · simp only [hy,norm_zero,zero_pow (by decide : 2≠0),zero_mul]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ hb i)
  · have he : (∑ i : Fin n, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y)=
        ∑ i ∈ closeLabels r w Y, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact Set.indicator_of_notMem (fun hh ↦ hi (mem_closeLabels_of_near hr w Y hy i hh)) _
    rw [he]
    exact mul_le_mul_of_nonneg_right (w.orbital_le_bound y) (Finset.sum_nonneg fun i _ ↦ hb i)

lemma rawCutoff_mass_pointwise (n : ℕ) (L : Length) {r : ℝ} (hr : 0<r)
    (y : Torus L) (Y : Configuration n L) :
    1≤‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2+
      ∑ i : Fin n, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
  rw [rawCutoff_norm_sq]
  have hb (i : Fin n) : 0≤(near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y :=
    Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  by_cases hh : ∃ i, y∈near L.val r (Y i)
  · obtain ⟨i,hi⟩ := hh
    have hs := Finset.single_le_sum (f := fun i : Fin n ↦
      (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y) (fun i _ ↦ hb i) (Finset.mem_univ i)
    rw [Set.indicator_of_mem hi] at hs
    exact hs.trans (le_add_of_nonneg_left (sq_nonneg _))
  · have ha (i : Fin n) : angle L.val r y (Y i)=Real.pi/2 :=
      angle_one_outside L.val hr (fun hi ↦ hh ⟨i,hi⟩)
    have he : rawCutoffReal n L r (Fin.cons y Y)=1 := by
      simp only [rawCutoffReal,Fin.cons_zero,Fin.cons_succ,ha,Real.sin_pi_div_two,Finset.prod_const_one]
    rw [he,one_pow]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ ↦ hb i))

lemma localized_mass_pointwise {n : ℕ} {L : Length} {r : ℝ} (hr : 0<r)
    (w : SmoothMultiplier 1 L) (Y : Configuration n L) (y : Torus L) :
    ‖w.orbital y‖^2≤‖(orbitalCutoff n r w).toFun (Fin.cons y Y)‖^2+
      w.orbitalBound * ∑ i ∈ closeLabels r w Y, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
  have h := mul_le_mul_of_nonneg_left (rawCutoff_mass_pointwise n L hr y Y) (sq_nonneg ‖w.orbital y‖)
  simp only [mul_one,mul_add] at h
  have he : ‖(orbitalCutoff n r w).toFun (Fin.cons y Y)‖^2=
      ‖w.orbital y‖^2 * ‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2 := by
    change ‖w.orbital y*(rawCutoff n L r).toFun (Fin.cons y Y)‖^2=_
    rw [norm_mul,mul_pow]
  rw [he]
  exact h.trans (add_le_add_right (weighted_near_le hr w Y y) _)

lemma near_sum_integral_le {n : ℕ} {L : Length} {r : ℝ} (hr : 0<r)
    (Y : Configuration n L) (J : Finset (Fin n)) :
    (∫ y : Torus L, ∑ i ∈ J, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y)≤
      (J.card:ℝ)*(4*r)^3 := by
  rw [integral_finsetSum _ (fun i _ ↦ (integrable_const (1:ℝ)).indicator (near_measurable L.val r (Y i)))]
  calc
    _ = ∑ i ∈ J, volume.real (near L.val r (Y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_indicator_one (near_measurable L.val _ _)
    _ ≤ ∑ i ∈ J, (4*r)^3 := Finset.sum_le_sum fun i _ ↦ near_volume_le L.val hr (Y i)
    _ = _ := by simp

lemma localized_mass_lower {n : ℕ} {L : Length} {r : ℝ} (hr : 0<r)
    (w : SmoothMultiplier 1 L) (hw : ∫ y : Torus L, ‖w.orbital y‖^2=1)
    (Y : Configuration n L) :
    1-64*w.orbitalBound*(closeLabels r w Y).card*r^3≤(orbitalCutoff n r w).fiberMass Y := by
  have hf : Integrable (fun y : Torus L ↦ ‖(orbitalCutoff n r w).toFun (Fin.cons y Y)‖^2) volume :=
    (((continuous_of_continuous_lift (orbitalCutoff n r w).smooth.continuous).comp
      ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
        (continuous_const : Continuous (fun _ : Torus L ↦ Y)))).norm.pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hw' : Integrable (fun y : Torus L ↦ ‖w.orbital y‖^2) volume :=
    (w.orbital_continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun y : Torus L ↦ ∑ i ∈ closeLabels r w Y,
      (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y) volume :=
    integrable_finsetSum _ (fun i _ ↦ (integrable_const (1:ℝ)).indicator (near_measurable L.val r (Y i)))
  have h := integral_mono hw' (hf.add (hi.const_mul w.orbitalBound)) (localized_mass_pointwise hr w Y)
  change (∫ y : Torus L, ‖w.orbital y‖^2) ≤ ∫ y : Torus L,
    ‖(orbitalCutoff n r w).toFun (Fin.cons y Y)‖^2+
    w.orbitalBound * ∑ i ∈ closeLabels r w Y, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y at h
  rw [hw,integral_add hf (hi.const_mul w.orbitalBound),integral_const_mul] at h
  have hh := mul_le_mul_of_nonneg_left (near_sum_integral_le hr Y (closeLabels r w Y)) (show 0≤w.orbitalBound from sq_nonneg _)
  change 1-64*w.orbitalBound*(closeLabels r w Y).card*r^3≤∫ y : Torus L, ‖(orbitalCutoff n r w).toFun (Fin.cons y Y)‖^2
  nlinarith

end HardSphere.TightCutoff

namespace HardSphere.TightCutoff
open PeriodicCutoff MeasureTheory Set Filter

lemma norm_add_sq_le_two (z v : ℂ) : ‖z+v‖^2≤2*‖z‖^2+2*‖v‖^2 := by
  have h := norm_add_le z v
  have h' := sq_nonneg (‖z‖-‖v‖)
  nlinarith [norm_nonneg (z+v),norm_nonneg z,norm_nonneg v]

lemma orbitalCutoff_derivative_le {n : ℕ} {L : Length} (r : ℝ)
    (w : SmoothMultiplier 1 L) (X : Configuration (n+1) L) (p : Direction (n+1)) :
    ‖coordDerivative (n+1) L (orbitalCutoff n r w).toFun p X‖^2≤
      2*‖w.orbital (X 0)‖^2*‖coordDerivative (n+1) L (rawCutoff n L r).toFun p X‖^2+
      2*‖coordDerivative (n+1) L (w.liftHead n).toFun p X‖^2 := by
  change ‖coordDerivative (n+1) L ((w.liftHead n).toFun*(rawCutoff n L r).toFun) p X‖^2≤_
  rw [coordDerivative_mul ((w.liftHead n).smooth.differentiable (by simp))
    ((rawCutoff n L r).smooth.differentiable (by simp))]
  simp only [Pi.add_apply,Pi.mul_apply]
  have hh := norm_add_sq_le_two
    ((w.liftHead n).toFun X*coordDerivative (n+1) L (rawCutoff n L r).toFun p X)
    ((rawCutoff n L r).toFun X*coordDerivative (n+1) L (w.liftHead n).toFun p X)
  simp only [norm_mul,mul_pow] at hh
  have hb : ‖(rawCutoff n L r).toFun X‖^2≤1 := by
    rw [rawCutoff_norm_sq]
    nlinarith [(rawCutoffReal_bounds n L r X).1,(rawCutoffReal_bounds n L r X).2]
  have hc := mul_le_mul_of_nonneg_left hb
    (sq_nonneg ‖coordDerivative (n+1) L (w.liftHead n).toFun p X‖)
  change ‖coordDerivative (n+1) L (w.liftHead n).toFun p X‖^2 * ‖(rawCutoff n L r).toFun X‖^2≤_ at hc
  change _≤2*‖(w.liftHead n).toFun X‖^2*‖coordDerivative (n+1) L (rawCutoff n L r).toFun p X‖^2+_
  nlinarith

lemma localized_gradient_pointwise {n : ℕ} {L : Length} {r M : ℝ} (hr : 0<r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M)
    (w : SmoothMultiplier 1 L) (Y : Configuration n L) (y : Torus L) :
    (∑ p : Direction (n+1), ‖coordDerivative (n+1) L (orbitalCutoff n r w).toFun p (Fin.cons y Y)‖^2)≤
      2*(∑ j : Fin 3, ‖coordDerivative 1 L w.toFun (0,j) (fun _ ↦ y)‖^2)+
      (288*Real.pi^2*M^2/r^2)*w.orbitalBound *
        ∑ i ∈ closeLabels r w Y, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Direction (n+1))))
    (fun p _ ↦ orbitalCutoff_derivative_le r w (Fin.cons y Y) p)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,w.liftHead_gradient_sum,Fin.cons_zero] at hs
  have hg := rawCutoff_gradient_le n L hr hM hb (Fin.cons y Y)
  simp only [Fin.cons_zero,Fin.cons_succ] at hg
  have h1 := mul_le_mul_of_nonneg_left hg (show 0≤2*‖w.orbital y‖^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left (weighted_near_le hr w Y y)
    (show 0≤288*Real.pi^2*M^2/r^2 by positivity)
  have he : 2*‖w.orbital y‖^2 * (144*Real.pi^2*M^2/r^2 *
      ∑ i : Fin n, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y)=
      (288*Real.pi^2*M^2/r^2) * (‖w.orbital y‖^2 *
      ∑ i : Fin n, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y) := by ring
  rw [he] at h1
  have hh := h1.trans h2
  rw [← mul_assoc] at hh
  linarith

lemma derivative_fiber_integrable {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (Y : Configuration n L) (p : Direction (n+1)) :
    Integrable (fun y : Torus L ↦ ‖coordDerivative (n+1) L f.toFun p (Fin.cons y Y)‖^2) volume := by
  exact (((continuous_coordDerivative f.smooth p).comp
    ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
      (continuous_const : Continuous (fun _ : Torus L ↦ Y)))).norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

lemma orbital_derivative_integrable {L : Length} (w : SmoothMultiplier 1 L) (j : Fin 3) :
    Integrable (fun y : Torus L ↦ ‖coordDerivative 1 L w.toFun (0,j) (fun _ ↦ y)‖^2) volume :=
  (((continuous_coordDerivative w.smooth (0,j)).comp (continuous_pi fun _ ↦ continuous_id)).norm.pow 2
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma localized_gradient_integral_le {n : ℕ} {L : Length} {r M : ℝ} (hr : 0<r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M)
    (w : SmoothMultiplier 1 L) (Y : Configuration n L) :
    (∑ p : Direction (n+1), ∫ y : Torus L,
      ‖coordDerivative (n+1) L (orbitalCutoff n r w).toFun p (Fin.cons y Y)‖^2)≤
      2*w.orbitalEnergy+18432*Real.pi^2*M^2*w.orbitalBound*(closeLabels r w Y).card*r := by
  have hf := derivative_fiber_integrable (orbitalCutoff n r w) Y
  have hw := orbital_derivative_integrable w
  have hi : Integrable (fun y : Torus L ↦ ∑ i ∈ closeLabels r w Y,
      (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y) volume :=
    integrable_finsetSum _ (fun i _ ↦ (integrable_const (1:ℝ)).indicator (near_measurable L.val r (Y i)))
  have h := integral_mono (integrable_finsetSum Finset.univ (fun p _ ↦ hf p))
    (((integrable_finsetSum Finset.univ (fun j _ ↦ hw j)).const_mul 2).add
      (hi.const_mul ((288*Real.pi^2*M^2/r^2)*w.orbitalBound)))
    (localized_gradient_pointwise hr hM hb w Y)
  change (∫ y : Torus L, ∑ p : Direction (n+1),
    ‖coordDerivative (n+1) L (orbitalCutoff n r w).toFun p (Fin.cons y Y)‖^2)≤
    ∫ y : Torus L, 2*(∑ j : Fin 3, ‖coordDerivative 1 L w.toFun (0,j) (fun _ ↦ y)‖^2)+
      (288*Real.pi^2*M^2/r^2)*w.orbitalBound *
        ∑ i ∈ closeLabels r w Y, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y at h
  rw [integral_finsetSum _ (fun p _ ↦ hf p),integral_add
    ((integrable_finsetSum Finset.univ (fun j _ ↦ hw j)).const_mul 2)
    (hi.const_mul ((288*Real.pi^2*M^2/r^2)*w.orbitalBound)),
    integral_const_mul,integral_const_mul,integral_finsetSum _ (fun j _ ↦ hw j)] at h
  have hh := mul_le_mul_of_nonneg_left (near_sum_integral_le hr Y (closeLabels r w Y))
    (show 0≤(288*Real.pi^2*M^2/r^2)*w.orbitalBound from mul_nonneg (by positivity) (sq_nonneg _))
  have he : (288*Real.pi^2*M^2/r^2)*w.orbitalBound*((closeLabels r w Y).card*(4*r)^3)=
      18432*Real.pi^2*M^2*w.orbitalBound*(closeLabels r w Y).card*r := by
    field_simp [hr.ne']
    ring
  rw [he] at hh
  exact h.trans (add_le_add_right hh _)

end HardSphere.TightCutoff

end

end OAI
