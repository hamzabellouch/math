import Mathlib
import OAI.Analysis.HardSphere.PathBounds.ConfigurationTailLp
import OAI.Analysis.HardSphere.Geometry.TorusLiftBox
import OAI.Analysis.HardSphere.Cutoffs.ThreeTorus
import OAI.Analysis.HardSphere.Cutoffs.Failure

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
open scoped ComplexConjugate

def rawAngleLift (n : ℕ) (L : Length) (r : ℝ) (i : Fin n) (R : LiftedConfiguration (n+1)) : ℝ :=
  angleLift L.val r (R 0-R i.succ)

def rawCutoffReal (n : ℕ) (L : Length) (r : ℝ) (X : Configuration (n+1) L) : ℝ :=
  ∏ i : Fin n, Real.sin (angle L.val r (X 0) (X i.succ))

lemma rawAngleLift_smooth (n : ℕ) (L : Length) (r : ℝ) (i : Fin n) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (rawAngleLift n L r i) :=
  (angleLift_smooth L.val r).comp ((contDiff_apply ℝ (Fin 3 → ℝ) 0).sub
    (contDiff_apply ℝ (Fin 3 → ℝ) i.succ))

lemma angle_project (n : ℕ) (L : Length) (r : ℝ) (i : Fin n) (R : LiftedConfiguration (n+1)) :
    angle L.val r (project (n+1) L R 0) (project (n+1) L R i.succ)=rawAngleLift n L r i R := by
  change Real.pi/2*Real.smoothTransition ((pairQ L.val (fun j ↦ (R 0 j : AddCircle L.val))
    (fun j ↦ (R i.succ j : AddCircle L.val))-2*r^2)/(2*r^2))=_
  rw [pairQ_coe]
  rfl

lemma rawCutoffReal_smooth (n : ℕ) (L : Length) (r : ℝ) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun R : LiftedConfiguration (n+1) ↦
      rawCutoffReal n L r (project (n+1) L R)) := by
  simp only [rawCutoffReal,angle_project]
  exact contDiff_prod (fun i _ ↦ (rawAngleLift_smooth n L r i).sin)

def rawCutoff (n : ℕ) (L : Length) (r : ℝ) : SmoothMultiplier (n+1) L :=
  .ofSmooth (fun X ↦ (rawCutoffReal n L r X : ℂ))
    (Complex.ofRealCLM.contDiff.comp (rawCutoffReal_smooth n L r))

lemma rawCutoff_real (n : ℕ) (L : Length) (r : ℝ) (X : Configuration (n+1) L) :
    conj ((rawCutoff n L r).toFun X)=(rawCutoff n L r).toFun X := Complex.conj_ofReal _

lemma rawCutoff_norm_sq (n : ℕ) (L : Length) (r : ℝ) (X : Configuration (n+1) L) :
    ‖(rawCutoff n L r).toFun X‖^2=rawCutoffReal n L r X^2 := by
  change ‖(rawCutoffReal n L r X : ℂ)‖^2=_
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma rawCutoff_clearance (n : ℕ) (L : Length) {r : ℝ} (hr : 0<r) :
    InsertionClearance r (rawCutoff n L r) := by
  intro X hX i
  have hs : tsupport (rawCutoff n L r).toFun ⊆
      {X | 2*r^2≤pairQ L.val (X 0) (X i.succ)} := by
    have hc : Continuous (fun X : Configuration (n+1) L ↦ pairQ L.val (X 0) (X i.succ)) :=
      by
        have hp : Continuous (fun X : Configuration (n+1) L ↦ (X 0,X i.succ)) := by fun_prop
        exact (pairQ_continuous L.val).comp hp
    apply closure_minimal ?_ (isClosed_le continuous_const hc)
    intro R hR
    by_contra hn
    have hz : (rawCutoff n L r).toFun R=0 := by
      change ((∏ k : Fin n,Real.sin (angle L.val r (R 0) (R k.succ)) : ℝ) : ℂ)=0
      rw [Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [angle_zero L.val hr (not_le.mp hn).le,Real.sin_zero]),Complex.ofReal_zero]
    exact hR hz
  have hQ : 2*r^2≤pairQ L.val (X 0) (X i.succ) := hs hX
  have he : torusDistance L (X 0) (X i.succ)^2=
      ∑ j : Fin 3,dist (X 0 j) (X i.succ j)^2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hl := pairQ_le L.val (X 0) (X i.succ)
  have hd : 0≤torusDistance L (X 0) (X i.succ) := Real.sqrt_nonneg _
  nlinarith [sq_pos_of_pos hr]

end HardSphere

namespace HardSphere
open PeriodicCutoff

lemma torus_volume_real (L : Length) : volume.real (Set.univ : Set (Torus L))=L.val^3 := by
  rw [measureReal_def,volume_pi,Measure.pi_univ]
  simp only [AddCircle.measure_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal L.property.le]

lemma rawCutoffReal_bounds (n : ℕ) (L : Length) (r : ℝ) (X : Configuration (n+1) L) :
    0≤rawCutoffReal n L r X ∧ rawCutoffReal n L r X≤1 := by
  have hs (i : Fin n) : 0≤Real.sin (angle L.val r (X 0) (X i.succ)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (angle_bounds L.val r _ _).1
      ((angle_bounds L.val r _ _).2.trans (by linarith [Real.pi_pos]))
  exact ⟨Finset.prod_nonneg (fun i _ ↦ hs i),Finset.prod_le_one₀ (fun i _ ↦ hs i) (fun _ _ ↦ Real.sin_le_one _)⟩

lemma rawCutoff_mass_pointwise (n : ℕ) (L : Length) {r : ℝ} (hr : 0<r)
    (y : Torus L) (Y : Configuration n L) :
    1≤‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2+
      ∑ i : Fin n, (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
  rw [rawCutoff_norm_sq]
  have hb (i : Fin n) : 0≤(box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y :=
    Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  by_cases hh : ∃ i, y∈box L.val (Real.pi*r) (Y i)
  · obtain ⟨i,hi⟩ := hh
    have hs := Finset.single_le_sum (f := fun i : Fin n ↦
      (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y) (fun i _ ↦ hb i) (Finset.mem_univ i)
    rw [Set.indicator_of_mem hi] at hs
    exact hs.trans (le_add_of_nonneg_left (sq_nonneg _))
  · have ha (i : Fin n) : angle L.val r y (Y i)=Real.pi/2 :=
      angle_one_outside L.val hr (fun hi ↦ hh ⟨i,hi⟩)
    have he : rawCutoffReal n L r (Fin.cons y Y)=1 := by
      simp only [rawCutoffReal,Fin.cons_zero,Fin.cons_succ,ha,Real.sin_pi_div_two,Finset.prod_const_one]
    rw [he,one_pow]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ ↦ hb i))

lemma rawCutoff_mass_lower (n : ℕ) (L : Length) {r : ℝ} (hr : 0<r)
    (Y : Configuration n L) : L.val^3-(n:ℝ)*(2*Real.pi*r)^3≤(rawCutoff n L r).fiberMass Y := by
  have hc : Continuous (fun y : Torus L ↦ ‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2) :=
    (((continuous_of_continuous_lift (rawCutoff n L r).smooth.continuous).comp
      ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
        (continuous_const : Continuous (fun _ : Torus L ↦ Y)))).norm).pow 2
  have hf : Integrable (fun y : Torus L ↦ ‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2) volume :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi (i : Fin n) : Integrable ((box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ))) volume :=
    (integrable_const (1:ℝ)).indicator (box_measurable L.val _ _)
  have hh := integral_mono (integrable_const (1:ℝ)) (hf.add (integrable_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ ↦ hi i)))
    (fun y ↦ rawCutoff_mass_pointwise n L hr y Y)
  dsimp only [Pi.add_apply] at hh
  rw [integral_const,smul_eq_mul,mul_one,torus_volume_real,
    integral_add hf (integrable_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ ↦ hi i)),
    integral_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ ↦ hi i)] at hh
  have hv : (∑ i : Fin n, ∫ y : Torus L, (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y)≤
      (n:ℝ)*(2*Real.pi*r)^3 := by
    calc
      _ = ∑ i : Fin n, volume.real (box L.val (Real.pi*r) (Y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_indicator_one (box_measurable L.val _ _)
      _ ≤ ∑ i : Fin n, (2*(Real.pi*r))^3 := Finset.sum_le_sum (fun i _ ↦ box_volume_le L.val (by positivity) (Y i))
      _ = _ := by simp [mul_assoc]
  change L.val^3-(n:ℝ)*(2*Real.pi*r)^3≤∫ y : Torus L, ‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2
  linarith

lemma rawAngleLift_fderiv (n : ℕ) (L : Length) (r : ℝ) (i : Fin n)
    (R v : LiftedConfiguration (n+1)) :
    fderiv ℝ (rawAngleLift n L r i) R v =
      ∑ j : Fin 3, anglePartial L.val r (R 0-R i.succ) j*(v 0 j-v i.succ j) := by
  have hd : HasDerivAt (fun t : ℝ ↦ R+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add R
  have hf := (((rawAngleLift_smooth n L r i).differentiable (by simp)) R).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp)
  have ha := angleLift_derivative L.val r
    (fun j t ↦ (R 0 j+t*v 0 j)-(R i.succ j+t*v i.succ j))
    (fun j ↦ v 0 j-v i.succ j) 0 (fun j ↦ by
      convert (((hasDerivAt_id (0:ℝ)).mul_const (v 0 j)).const_add (R 0 j)).sub
        (((hasDerivAt_id (0:ℝ)).mul_const (v i.succ j)).const_add (R i.succ j)) using 1 <;> first | rfl | simp only [one_mul])
  have he : (rawAngleLift n L r i ∘ fun t : ℝ ↦ R+t • v)=
      (fun t : ℝ ↦ angleLift L.val r (fun j ↦ (R 0 j+t*v 0 j)-(R i.succ j+t*v i.succ j))) := rfl
  rw [he] at hf
  convert hf.unique ha using 1
  simp only [zero_mul,add_zero]
  rfl

lemma rawAngleLift_fderiv_coord (n : ℕ) (L : Length) (r : ℝ) (i : Fin n)
    (R : LiftedConfiguration (n+1)) (p : Direction (n+1)) :
    fderiv ℝ (rawAngleLift n L r i) R (Pi.single p.1 (Pi.single p.2 1)) =
      ((if p.1=0 then (1:ℝ) else 0)-(if p.1=i.succ then 1 else 0))*
        anglePartial L.val r (R 0-R i.succ) p.2 := by
  rw [rawAngleLift_fderiv]
  by_cases h0 : p.1=0 <;> by_cases hi : p.1=i.succ
  · exact False.elim (Fin.succ_ne_zero i (hi.symm.trans h0))
  · simp [h0,Pi.single_apply,eq_comm,Finset.sum_ite_eq',mul_comm]
  · simp [hi,Pi.single_apply,eq_comm,Finset.sum_ite_eq',mul_comm]
  · simp [h0,hi,Ne.symm h0,Ne.symm hi]

lemma rawCutoff_derivative_sq_le (n : ℕ) (L : Length) (r : ℝ)
    (X : Configuration (n+1) L) (p : Direction (n+1)) :
    ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p X‖^2≤
      ∑ i : Fin n, (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
        (Pi.single p.1 (Pi.single p.2 1)))^2 := by
  let R := representative (n+1) L X
  let v : LiftedConfiguration (n+1) := Pi.single p.1 (Pi.single p.2 1)
  have he : (fun Y : LiftedConfiguration (n+1) ↦ (rawCutoff n L r).toFun (project (n+1) L Y))=
      Complex.ofRealCLM ∘ (fun Y : LiftedConfiguration (n+1) ↦ ∏ i : Fin n, Real.sin (rawAngleLift n L r i Y)) := by
    funext Y
    change (rawCutoffReal n L r (project (n+1) L Y) : ℂ)=_
    simp only [rawCutoffReal,angle_project,Function.comp_apply,Complex.ofRealCLM_apply]
  have hd := (rawCutoffReal_smooth n L r).differentiable (by simp)
  simp only [rawCutoffReal,angle_project] at hd
  change ‖fderiv ℝ (fun Y ↦ (rawCutoff n L r).toFun (project (n+1) L Y)) R v‖^2≤_
  rw [he,fderiv_comp R Complex.ofRealCLM.differentiableAt (hd R),Complex.ofRealCLM.fderiv]
  simp only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact SineProduct.fderiv_sq_le Finset.univ (rawAngleLift n L r) R v
    (fun i _ ↦ (rawAngleLift_smooth n L r i).differentiable (by simp) R)

end HardSphere

end

end OAI
