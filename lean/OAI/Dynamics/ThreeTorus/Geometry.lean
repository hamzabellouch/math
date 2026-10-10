import OAI.Dynamics.ThreeTorus.Basic
import OAI.Dynamics.ThreeTorus.PositiveLaws
import OAI.Dynamics.ThreeTorus.Twists

namespace OAI

/-! Torus coordinate equivalence, smooth passage geometry, and all-jet passage convergence. -/

section

/-! Torus coordinate equivalence and retained passage geometry. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

end ThreeTorus

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

def torusTriple : Torus ≃ᵐ TripleTorus :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => UnitAddCircle) 0).trans
    ((MeasurableEquiv.refl UnitAddCircle).prodCongr
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => UnitAddCircle)))

lemma torusTriple_apply (x : Torus) : torusTriple x = (x 0,x 1,x 2) := rfl

lemma torusTriple_symm_apply (x : TripleTorus) : torusTriple.symm x = ![x.1,x.2.1,x.2.2] := by
  ext i
  fin_cases i <;> rfl

lemma measurePreserving_torusTriple : MeasurePreserving torusTriple μ tripleVolume := by
  exact ((MeasurePreserving.id AddCircle.haarAddCircle).prod
    (measurePreserving_piFinTwo (fun _ : Fin 2 => AddCircle.haarAddCircle))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => AddCircle.haarAddCircle) 0)

def torusPassage (h s : UnitAddCircle → UnitAddCircle) : Equiv.Perm Torus :=
  (torusTriple.toEquiv.trans (passageMap h s)).trans torusTriple.symm.toEquiv

lemma torusPassage_apply (h s : UnitAddCircle → UnitAddCircle) (x : Torus) :
    torusPassage h s x = ![x 0+h (x 1+s (x 2))-h (x 1),x 1+s (x 2),x 2] := by
  rw [torusPassage,Equiv.trans_apply,Equiv.trans_apply]
  rw [show torusTriple.toEquiv x = (x 0,x 1,x 2) from rfl]
  exact torusTriple_symm_apply _

lemma torusPassage_symm_apply (h s : UnitAddCircle → UnitAddCircle) (x : Torus) :
    (torusPassage h s).symm x = ![x 0-h (x 1)+h (x 1-s (x 2)),x 1-s (x 2),x 2] := by
  change torusTriple.symm ((passageMap h s).symm (torusTriple x)) = _
  rw [torusTriple_apply,torusTriple_symm_apply]
  rfl

lemma measurePreserving_torusPassage {h s : UnitAddCircle → UnitAddCircle}
    (hh : Measurable h) (hs : Measurable s) : MeasurePreserving (torusPassage h s) μ μ := by
  exact (MeasurePreserving.symm torusTriple measurePreserving_torusTriple).comp
    ((measurePreserving_passageMap hh hs).comp measurePreserving_torusTriple)

def passageLift (h s : ℝ → ℝ) (x : Cover) : Cover :=
  ![x 0+h (x 1+s (x 2))-h (x 1),x 1+s (x 2),x 2]

def passageInverseLift (h s : ℝ → ℝ) (x : Cover) : Cover :=
  ![x 0-h (x 1)+h (x 1-s (x 2)),x 1-s (x 2),x 2]

lemma contDiff_passageLift {h s : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (passageLift h s) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact ((contDiff_apply ℝ ℝ 0).add (hh.comp ((contDiff_apply ℝ ℝ 1).add (hs.comp (contDiff_apply ℝ ℝ 2))))).sub
      (hh.comp (contDiff_apply ℝ ℝ 1))
  · exact (contDiff_apply ℝ ℝ 1).add (hs.comp (contDiff_apply ℝ ℝ 2))
  · exact contDiff_apply ℝ ℝ 2

lemma contDiff_passageInverseLift {h s : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (passageInverseLift h s) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact ((contDiff_apply ℝ ℝ 0).sub (hh.comp (contDiff_apply ℝ ℝ 1))).add
      (hh.comp ((contDiff_apply ℝ ℝ 1).sub (hs.comp (contDiff_apply ℝ ℝ 2))))
  · exact (contDiff_apply ℝ ℝ 1).sub (hs.comp (contDiff_apply ℝ ℝ 2))
  · exact contDiff_apply ℝ ℝ 2

lemma smooth_torusPassage {h s : UnitAddCircle → UnitAddCircle} {H S : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hH : ∀ x : ℝ, h (x : UnitAddCircle) = (H x : UnitAddCircle))
    (hS : ∀ x : ℝ, s (x : UnitAddCircle) = (S x : UnitAddCircle)) :
    Smooth (torusPassage h s) := by
  intro x
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ x,passageLift H S,
    (contDiff_passageLift hh hs).contDiffOn,?_⟩
  intro y _
  rw [torusPassage_apply]
  ext i
  fin_cases i <;> simp only [project,passageLift,hS,← AddCircle.coe_add,hH,← AddCircle.coe_sub] <;> rfl

lemma smooth_torusPassage_symm {h s : UnitAddCircle → UnitAddCircle} {H S : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hH : ∀ x : ℝ, h (x : UnitAddCircle) = (H x : UnitAddCircle))
    (hS : ∀ x : ℝ, s (x : UnitAddCircle) = (S x : UnitAddCircle)) :
    Smooth (torusPassage h s).symm := by
  intro x
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ x,passageInverseLift H S,
    (contDiff_passageInverseLift hh hs).contDiffOn,?_⟩
  intro y _
  rw [torusPassage_symm_apply]
  ext i
  fin_cases i <;> simp only [project,passageInverseLift,hS,← AddCircle.coe_sub,hH,← AddCircle.coe_add] <;> rfl

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology
namespace ThreeTorus

lemma contDiff_real_primitive {v : ℝ → ℝ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ t in 0..x, v t) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨intervalIntegral.differentiable_integral_of_continuous hv.continuous,?_⟩
  have hd : deriv (fun x => ∫ t in 0..x, v t) = v := by
    funext x
    exact (intervalIntegral.integral_hasDerivAt_right (hv.continuous.intervalIntegrable 0 x)
      hv.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuous.continuousAt).deriv
  rw [hd]
  exact hv

lemma primitive_translate_one {v : ℝ → ℝ} (hv : Function.Periodic v 1)
    (hc : Continuous v) (x : ℝ) :
    (∫ t in 0..x+1, v t) = (∫ t in 0..x, v t)+(∫ t in 0..1, v t) := by
  simpa only [zero_add] using hv.intervalIntegral_add_eq_add 0 x (fun a b => hc.intervalIntegrable a b)

lemma periodic_primitive_mod {v : ℝ → ℝ} (hv : Function.Periodic v 1)
    (hc : Continuous v) {k : ℤ} (hk : (∫ t in 0..1, v t) = k) :
    Function.Periodic (fun x => (↑(∫ t in 0..x, v t):UnitAddCircle)) 1 := by
  intro x
  dsimp only
  rw [primitive_translate_one hv hc,hk,AddCircle.coe_add]
  have hk0 : ((k:ℝ):UnitAddCircle) = 0 := by
    rw [show (k:ℝ) = k • (1:ℝ) by simp,AddCircle.coe_zsmul,AddCircle.coe_period,smul_zero]
  rw [hk0,add_zero]

lemma continuous_periodic_lift {X : Type*} [TopologicalSpace X] {f : ℝ → X}
    (hf : Function.Periodic f 1) (hc : Continuous f) : Continuous hf.lift := by
  exact hc.quotient_lift _

/-- The precise globally defined circle-valued primitive used by a passage. -/
def circlePrimitive {v : ℝ → ℝ} (hv : Function.Periodic v 1)
    (hc : Continuous v) {k : ℤ} (hk : (∫ t in 0..1, v t) = k) : UnitAddCircle → UnitAddCircle :=
  (periodic_primitive_mod hv hc hk).lift

lemma circlePrimitive_coe {v : ℝ → ℝ} (hv : Function.Periodic v 1)
    (hc : Continuous v) {k : ℤ} (hk : (∫ t in 0..1, v t) = k) (x : ℝ) :
    circlePrimitive hv hc hk (x:UnitAddCircle) = (↑(∫ t in 0..x, v t):UnitAddCircle) := rfl

lemma continuous_circlePrimitive {v : ℝ → ℝ} (hv : Function.Periodic v 1)
    (hc : Continuous v) {k : ℤ} (hk : (∫ t in 0..1, v t) = k) :
    Continuous (circlePrimitive hv hc hk) := by
  exact continuous_periodic_lift _ ((AddCircle.continuous_mk' 1).comp
    (intervalIntegral.differentiable_integral_of_continuous hc).continuous)

def circleSpeed {s : ℝ → ℝ} (hs : Function.Periodic s 1) : UnitAddCircle → UnitAddCircle :=
  fun z => (hs.lift z : UnitAddCircle)

lemma circleSpeed_coe {s : ℝ → ℝ} (hs : Function.Periodic s 1) (x : ℝ) :
    circleSpeed hs (x:UnitAddCircle) = (s x:UnitAddCircle) := rfl

lemma continuous_circleSpeed {s : ℝ → ℝ} (hs : Function.Periodic s 1) (hc : Continuous s) :
    Continuous (circleSpeed hs) := by
  exact (AddCircle.continuous_mk' 1).comp (continuous_periodic_lift hs hc)

/-- Global C-infinity, inverse C-infinity, and exact Haar preservation for the
manuscript passage, without assuming any geometric conclusion. -/
lemma primitive_passage_properties {v s : ℝ → ℝ}
    (hv : Function.Periodic v 1) (hs : Function.Periodic s 1)
    (hvc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hsc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s)
    {k : ℤ} (hk : (∫ t in 0..1, v t) = k) :
    let T := torusPassage (circlePrimitive hv hvc.continuous hk) (circleSpeed hs)
    Smooth T ∧ Smooth T.symm ∧ MeasurePreserving T μ μ := by
  exact ⟨smooth_torusPassage (contDiff_real_primitive hvc) hsc
      (circlePrimitive_coe hv hvc.continuous hk) (circleSpeed_coe hs),
    smooth_torusPassage_symm (contDiff_real_primitive hvc) hsc
      (circlePrimitive_coe hv hvc.continuous hk) (circleSpeed_coe hs),
    measurePreserving_torusPassage (continuous_circlePrimitive hv hvc.continuous hk).measurable
      (continuous_circleSpeed hs hsc.continuous).measurable⟩

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology
namespace ThreeTorus

/-- The bounded winding correction; no subsequence of passage integers is needed. -/
lemma passage_rounding (A : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ d : ℝ, ∃ k : ℤ, |d| ≤ (N:ℝ)⁻¹ ∧ (N:ℝ)*(A+d) = k := by
  let k : ℤ := ⌊(N:ℝ)*A⌋
  let d : ℝ := ((k:ℝ)-(N:ℝ)*A)/(N:ℝ)
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  refine ⟨d,k,?_,?_⟩
  · have hk1 : (k:ℝ) ≤ (N:ℝ)*A := Int.floor_le _
    have hk2 : (N:ℝ)*A-1 ≤ (k:ℝ) := (Int.sub_one_lt_floor _).le
    dsimp [d]
    rw [abs_div,abs_of_pos hn,abs_of_nonpos (sub_nonpos.mpr hk1),← one_div]
    exact div_le_div_of_nonneg_right (by linarith) hn.le
  · dsimp [d]
    field_simp
    ring

lemma passage_rounded_slope {v : ℝ → ℝ}
    (hv : Function.Periodic v 1) (hc : Continuous v) (N : ℕ) (d : ℝ) {k : ℤ}
    (hk : (N:ℝ)*((∫ t in 0..1, v t)+d) = k) :
    Function.Periodic (fun x => (N:ℝ)*(v x+d)) 1 ∧
    (∫ t in 0..1, (N:ℝ)*(v t+d)) = k := by
  constructor
  · intro x
    dsimp only
    rw [hv x]
  · rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hc.intervalIntegrable _ _) intervalIntegrable_const]
    simpa using hk

lemma passage_speed_smooth {J : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (N : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J x) := by fun_prop

/-- Existence of the exact smooth Haar-preserving passage for each integer N>0.
The map is the manuscript formula with H_N'=N(V+Delta_N) and
sigma_N=1/N+J/N^2. -/
lemma exists_rounded_passage {v J : ℝ → ℝ}
    (hv : Function.Periodic v 1) (hJ : Function.Periodic J 1)
    (hvc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hJc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    {N : ℕ} (hN : 0 < N) :
    ∃ d : ℝ, ∃ T : Equiv.Perm Torus,
      |d| ≤ (N:ℝ)⁻¹ ∧ Smooth T ∧ Smooth T.symm ∧ MeasurePreserving T μ μ ∧
      ∀ x : Cover, T (project x) = project (passageLift
        (fun u => ∫ t in 0..u, (N:ℝ)*(v t+d))
        (fun a => (N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a) x) := by
  obtain ⟨d,k,hd,hk⟩ := passage_rounding (∫ t in 0..1, v t) hN
  obtain ⟨hp,hi⟩ := passage_rounded_slope hv hvc.continuous N d hk
  have hsc := passage_speed_smooth hJc N
  have hsp : Function.Periodic (fun a => (N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a) 1 := by
    intro x
    dsimp only
    rw [hJ x]
  have hpc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (N:ℝ)*(v x+d)) := by fun_prop
  let H := circlePrimitive hp hpc.continuous hi
  let S := circleSpeed hsp
  let T := torusPassage H S
  have ht := primitive_passage_properties hp hsp hpc hsc hi
  refine ⟨d,T,hd,ht.1,ht.2.1,ht.2.2,?_⟩
  intro x
  rw [torusPassage_apply]
  ext i
  fin_cases i <;> simp only [project,passageLift,H,S,circleSpeed_coe,
    ← AddCircle.coe_add,circlePrimitive_coe,← AddCircle.coe_sub] <;> rfl

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

lemma iteratedFDeriv_slice
    {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : P × E → G} {n : ℕ} (hF : ContDiff ℝ n F) (p : P) (x : E) :
    iteratedFDeriv ℝ n (fun y => F (p,y)) x =
      (iteratedFDeriv ℝ n F (p,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  have hh : ContDiff ℝ n (fun q : P × E => F ((p,0)+q)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have he := (ContinuousLinearMap.inr ℝ P E).iteratedFDeriv_comp_right hh x (le_refl (n:WithTop ℕ∞))
  simpa only [Function.comp_def,ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk,add_zero,zero_add,iteratedFDeriv_comp_add_left] using he

lemma continuous_iteratedFDeriv_slice
    {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : P × E → G} {n : ℕ} (hF : ContDiff ℝ n F) :
    Continuous (fun q : P × E => iteratedFDeriv ℝ n (fun y => F (q.1,y)) q.2) := by
  simp_rw [iteratedFDeriv_slice hF]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ P E)).continuous.comp
      hF.continuous_iteratedFDeriv'

/-- Joint smoothness gives convergence in every C^k seminorm on compact sets. -/
lemma smooth_parameter_jets_tendsto
    {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : P × E → G} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (p : P) {K : Set E} (hK : IsCompact K) (n : ℕ) :
    TendstoUniformlyOn (fun a x => iteratedFDeriv ℝ n (fun y => F (a,y)) x)
      (fun x => iteratedFDeriv ℝ n (fun y => F (p,y)) x) (𝓝 p) K := by
  have hc := continuous_iteratedFDeriv_slice (hF.of_le
    (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤)))
  have hu := ((isCompact_closedBall p 1).prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  have ht := UniformContinuousOn.tendstoUniformlyOn
    (F := fun a x => iteratedFDeriv ℝ n (fun y => F (a,y)) x)
    hu (by simp : p ∈ Metric.closedBall p (1:ℝ))
  simpa only [nhdsWithin_eq_nhds.mpr (Metric.closedBall_mem_nhds p (by norm_num : (0:ℝ)<1))] using ht

end ThreeTorus

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

/-- A nonsingular two-parameter form of the exact passage lift (both signs). -/
def passageFamily (v J : ℝ → ℝ) (r : ℝ) (p : ℝ × ℝ) (x : Cover) : Cover :=
  let s := r*p.1*(1+p.1*J (x 2))
  ![x 0+r*(1+p.1*J (x 2))*(∫ t in (0:ℝ)..1, v (x 1+t*s)+p.2),
    x 1+s,x 2]

lemma smooth_passageFamily {v J : ℝ → ℝ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (r : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × ℝ) × Cover => passageFamily v J r q.1 q.2) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ((ℝ × ℝ) × Cover) × ℝ =>
        v (q.1.2 1+q.2*(r*q.1.1.1*(1+q.1.1.1*J (q.1.2 2))))+q.1.1.2) := by
    fun_prop
  have hi := smooth_compact_integral hc 0 1
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover =>
      q.2 0+r*(1+q.1.1*J (q.2 2))*(∫ t in (0:ℝ)..1,
        v (q.2 1+t*(r*q.1.1*(1+q.1.1*J (q.2 2))))+q.1.2))
    exact (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover => q.2 0)).add
      ((by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover => r*(1+q.1.1*J (q.2 2)))).mul hi)
  · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover =>
      q.2 1+r*q.1.1*(1+q.1.1*J (q.2 2)))
    fun_prop
  · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (ℝ × ℝ) × Cover => q.2 2)
    fun_prop

lemma passageFamily_zero (v J : ℝ → ℝ) (r : ℝ) :
    passageFamily v J r (0,0) = fun x : Cover => ![x 0+r*v (x 1),x 1,x 2] := by
  funext x
  simp [passageFamily]

lemma passageFamily_increment {v J : ℝ → ℝ} (hv : Continuous v)
    {N : ℕ} (hN : 0 < N) (d r u a : ℝ) :
    (∫ t in 0..u+r*((N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a), (N:ℝ)*(v t+d))
      -(∫ t in 0..u, (N:ℝ)*(v t+d)) =
    r*(1+(N:ℝ)⁻¹*J a)*(∫ t in (0:ℝ)..1,
      v (u+t*(r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a)))+d) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun t => (N:ℝ)*(v t+d)) volume a b :=
    fun a b => (continuous_const.mul (hv.add continuous_const)).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 u) (hi u _), add_sub_cancel_left]
  rw [intervalIntegral.integral_const_mul]
  have hs : r*((N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a) = r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a) := by ring
  rw [hs]
  have he := intervalIntegral.smul_integral_comp_add_mul (fun t => v t+d)
    (a := (0:ℝ)) (b := 1) (r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a)) u
  simp only [smul_eq_mul,mul_zero,add_zero,mul_one] at he
  rw [← he]
  have hf : (fun t => v (u+t*(r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a)))+d) =
      (fun t => v (u+r*(N:ℝ)⁻¹*(1+(N:ℝ)⁻¹*J a)*t)+d) := by
    funext t
    rw [mul_comm t]
  rw [hf]
  field_simp

/-- The passage and inverse are specializations of the same smooth family. -/
lemma passageLift_eq_family {v J : ℝ → ℝ} (hv : Continuous v)
    {N : ℕ} (hN : 0 < N) (d : ℝ) :
    passageLift (fun u => ∫ t in 0..u, (N:ℝ)*(v t+d))
      (fun a => (N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a) = passageFamily v J 1 ((N:ℝ)⁻¹,d) ∧
    passageInverseLift (fun u => ∫ t in 0..u, (N:ℝ)*(v t+d))
      (fun a => (N:ℝ)⁻¹+(N:ℝ)⁻¹^2*J a) = passageFamily v J (-1) ((N:ℝ)⁻¹,d) := by
  have h1 (u a : ℝ) := passageFamily_increment (J := J) hv hN d 1 u a
  have h2 (u a : ℝ) := passageFamily_increment (J := J) hv hN d (-1) u a
  constructor
  · funext x i
    fin_cases i
    · dsimp [passageLift,passageFamily]
      simp only [one_mul] at h1 ⊢
      linarith [h1 (x 1) (x 2)]
    · dsimp [passageLift,passageFamily]
      ring
    · rfl
  · funext x i
    fin_cases i
    · dsimp [passageInverseLift,passageFamily]
      simp only [neg_one_mul,← sub_eq_add_neg] at h2 ⊢
      linarith [h2 (x 1) (x 2)]
    · dsimp [passageInverseLift,passageFamily]
      ring
    · rfl

lemma passage_parameters_tendsto {d : ℕ → ℝ}
    (hd : ∀ N : ℕ, 0 < N → |d N| ≤ (N:ℝ)⁻¹) :
    Tendsto (fun N : ℕ => ((N:ℝ)⁻¹,d N)) atTop (𝓝 (0,0)) := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hnd : Tendsto d atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hn
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact hd N hN
  exact hn.prodMk_nhds hnd

/-- All spatial derivatives of each sign of the passage converge uniformly on
any fixed compact set. This is genuine C-infinity convergence, not C-zero. -/
lemma passage_Cinfty_limit {v J : ℝ → ℝ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    {d : ℕ → ℝ} (hd : ∀ N : ℕ, 0 < N → |d N| ≤ (N:ℝ)⁻¹)
    (r : ℝ) {K : Set Cover} (hK : IsCompact K) (n : ℕ) :
    TendstoUniformlyOn
      (fun (N : ℕ) x => iteratedFDeriv ℝ n (passageFamily v J r ((N:ℝ)⁻¹,d N)) x)
      (fun x => iteratedFDeriv ℝ n (fun y : Cover => ![y 0+r*v (y 1),y 1,y 2]) x)
      atTop K := by
  have ht := smooth_parameter_jets_tendsto (smooth_passageFamily hv hJ r) (0,0) hK n
  simp only [passageFamily_zero] at ht
  intro U hU
  exact (passage_parameters_tendsto hd).eventually (ht U hU)

end ThreeTorus
end
end
end
end
end
end
end

end OAI
