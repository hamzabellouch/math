import Mathlib
import OAI.Analysis.HardSphere.Comparison.RawAngleLiftSumSquares
import OAI.Analysis.HardSphere.Cutoffs.Near

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
    (fun j ↦ (R i.succ j : AddCircle L.val))-(5/4)*r^2)/((1/4)*r^2))=_
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
      {X | (5/4)*r^2≤pairQ L.val (X 0) (X i.succ)} := by
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
  have hQ : (5/4)*r^2≤pairQ L.val (X 0) (X i.succ) := hs hX
  have he : torusDistance L (X 0) (X i.succ)^2=
      ∑ j : Fin 3,dist (X 0 j) (X i.succ j)^2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hl := pairQ_le L.val (X 0) (X i.succ)
  have hd : 0≤torusDistance L (X 0) (X i.succ) := Real.sqrt_nonneg _
  nlinarith [sq_pos_of_pos hr]

end HardSphere.TightCutoff

namespace HardSphere.TightCutoff
open PeriodicCutoff
lemma rawCutoffReal_bounds (n : ℕ) (L : Length) (r : ℝ) (X : Configuration (n+1) L) :
    0≤rawCutoffReal n L r X ∧ rawCutoffReal n L r X≤1 := by
  have hs (i : Fin n) : 0≤Real.sin (angle L.val r (X 0) (X i.succ)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (angle_bounds L.val r _ _).1
      ((angle_bounds L.val r _ _).2.trans (by linarith [Real.pi_pos]))
  exact ⟨Finset.prod_nonneg (fun i _ ↦ hs i),Finset.prod_le_one₀ (fun i _ ↦ hs i) (fun _ _ ↦ Real.sin_le_one _)⟩

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

lemma rawAngleLift_sum_squares (n : ℕ) (L : Length) (r : ℝ) (i : Fin n)
    (R : LiftedConfiguration (n+1)) :
    (∑ p : Direction (n+1), (fderiv ℝ (rawAngleLift n L r i) R
      (Pi.single p.1 (Pi.single p.2 1)))^2)=
      2*∑ j : Fin 3, anglePartial L.val r (R 0-R i.succ) j^2 := by
  simp only [rawAngleLift_fderiv_coord]
  rw [Fintype.sum_prod_type,Fin.sum_univ_succ]
  simp only [Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero i),ite_true,ite_false,sub_zero,one_mul,
    Fin.succ_inj,zero_sub,neg_mul,neg_sq]
  have he : (∑ k : Fin n, ∑ j : Fin 3,
      ((if k=i then (1:ℝ) else 0)*anglePartial L.val r (R 0-R i.succ) j)^2)=
      ∑ j : Fin 3, anglePartial L.val r (R 0-R i.succ) j^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp
  rw [he]
  ring

lemma pairQ_representative (n : ℕ) (L : Length) (i : Fin n) (X : Configuration (n+1) L) :
    pairQ L.val (X 0) (X i.succ)=qLift L.val
      (representative (n+1) L X 0-representative (n+1) L X i.succ) := by
  calc
    _ = pairQ L.val (project (n+1) L (representative (n+1) L X) 0)
      (project (n+1) L (representative (n+1) L X) i.succ) := by rw [project_representative]
    _ = _ := pairQ_coe L.val _ _

lemma rawAngleLift_gradient_le (n : ℕ) (L : Length) {r M : ℝ} (hr : 0<r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M)
    (i : Fin n) (X : Configuration (n+1) L) :
    (∑ p : Direction (n+1), (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
      (Pi.single p.1 (Pi.single p.2 1)))^2)≤
      (144*Real.pi^2*M^2/r^2)*(near L.val r (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) := by
  rw [rawAngleLift_sum_squares]
  by_cases hx : X 0∈near L.val r (X i.succ)
  · rw [Set.indicator_of_mem hx,mul_one]
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _ ↦ anglePartial_sq_le L.val hr hM hb
        (representative (n+1) L X 0-representative (n+1) L X i.succ) j)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    calc
      _ ≤ 2*((3:ℝ)*(24*Real.pi^2*M^2/r^2)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hx,mul_zero]
    have hq : (3/2)*r^2<pairQ L.val (X 0) (X i.succ) := not_le.mp hx
    rw [pairQ_representative] at hq
    have hz : qLift L.val (representative (n+1) L X 0-representative (n+1) L X i.succ)∉Icc ((5/4)*r^2) ((3/2)*r^2) :=
      fun hs ↦ (not_lt.mpr hs.2) hq
    simp [anglePartial_eq_zero L.val hr hz]

lemma rawCutoff_gradient_le (n : ℕ) (L : Length) {r M : ℝ} (hr : 0<r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (X : Configuration (n+1) L) :
    (∑ p : Direction (n+1), ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p X‖^2)≤
      (144*Real.pi^2*M^2/r^2)*∑ i : Fin n,
        (near L.val r (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) := by
  calc
    _ ≤ ∑ p : Direction (n+1), ∑ i : Fin n,
        (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
          (Pi.single p.1 (Pi.single p.2 1)))^2 :=
      Finset.sum_le_sum fun p _ ↦ rawCutoff_derivative_sq_le n L r X p
    _ = ∑ i : Fin n, ∑ p : Direction (n+1),
        (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
          (Pi.single p.1 (Pi.single p.2 1)))^2 := by rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin n, (144*Real.pi^2*M^2/r^2)*
        (near L.val r (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) :=
      Finset.sum_le_sum fun i _ ↦ rawAngleLift_gradient_le n L hr hM hb i X
    _ = _ := (Finset.mul_sum ..).symm

end HardSphere.TightCutoff

end

end OAI
