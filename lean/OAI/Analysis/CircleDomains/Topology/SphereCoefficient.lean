import OAI.Analysis.CircleDomains.Reflection.RoundDiskReflection
import OAI.Analysis.CircleDomains.Modulus.SphericalChartCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

namespace OAI

/-! Borel complex coefficient fields on the concrete sphere, with an explicit
value at infinity. -/
open Set Function MeasureTheory
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

def sphereCoefficient (a : ℂ) (f : ℂ → ℂ) : Sphere → ℂ := fun p => p.elim a f

@[simp] lemma sphereCoefficient_coe (a : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    sphereCoefficient a f (z : Sphere)=f z := rfl

@[simp] lemma sphereCoefficient_infty (a : ℂ) (f : ℂ → ℂ) :
    sphereCoefficient a f ∞=a := rfl

lemma sphereCoefficient_measurable (a : ℂ) {f : ℂ → ℂ} (hf : Measurable f) :
    Measurable (sphereCoefficient a f) := by
  classical
  have he : sphereCoefficient a f=({∞} : Set Sphere).piecewise (fun _ => a) (f ∘ finiteCoord) := by
    funext p
    induction p using OnePoint.rec with
    | infty => simp [sphereCoefficient]
    | coe z => simp [sphereCoefficient,OnePoint.coe_ne_infty]
  rw [he]
  exact measurable_const.piecewise (measurableSet_singleton _) (hf.comp measurable_finiteCoord)

def circleReflectionPhase (c z : ℂ) : ℂ :=
  if z=c then 1 else ((z-c)/(starRingEnd ℂ (z-c)))^2

def sphereReflectionPhase (c : ℂ) : Sphere → ℂ :=
  sphereCoefficient 1 (circleReflectionPhase c)

lemma circleReflectionPhase_norm (c z : ℂ) : ‖circleReflectionPhase c z‖=1 := by
  classical
  by_cases hz : z=c
  · simp [circleReflectionPhase,hz]
  · simp only [circleReflectionPhase,ite_eq_right hz,norm_pow,norm_div,Complex.norm_conj,
      div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)),one_pow]

lemma sphereReflectionPhase_norm (c : ℂ) (p : Sphere) : ‖sphereReflectionPhase c p‖=1 := by
  induction p using OnePoint.rec with
  | infty => exact norm_one (α := ℂ)
  | coe z => exact circleReflectionPhase_norm c z

lemma circleReflectionPhase_measurable (c : ℂ) : Measurable (circleReflectionPhase c) := by
  classical
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  exact ((measurable_id.sub_const c).div (Complex.continuous_conj.measurable.comp (measurable_id.sub_const c))).pow_const 2

lemma sphereReflectionPhase_measurable (c : ℂ) : Measurable (sphereReflectionPhase c) :=
  sphereCoefficient_measurable 1 (circleReflectionPhase_measurable c)

lemma roundDiskReflection_infty (c : ℂ) {r : ℝ} (hr : 0<r) :
    roundDiskReflection c r hr ∞=(c : Sphere) := by
  change affineSphere (r:ℂ) c (by exact_mod_cast hr.ne')
    (CannonSphereReflection.reflection ∞)=(c : Sphere)
  rw [CannonSphereReflection.reflection_infty,affineSphere_coe]
  simp only [mul_zero,zero_add]

lemma roundDiskReflection_center (c : ℂ) {r : ℝ} (hr : 0<r) :
    roundDiskReflection c r hr (c : Sphere)=∞ := by
  rw [←roundDiskReflection_infty c hr,roundDiskReflection_involutive c hr]

lemma sphereReflectionPhase_reflection (c : ℂ) {r : ℝ} (hr : 0<r) (p : Sphere) :
    sphereReflectionPhase c (roundDiskReflection c r hr p)=sphereReflectionPhase c p := by
  classical
  induction p using OnePoint.rec with
  | infty => simp [roundDiskReflection_infty,sphereReflectionPhase,circleReflectionPhase]
  | coe z =>
    by_cases hz : z=c
    · subst z
      simp [roundDiskReflection_center,sphereReflectionPhase,circleReflectionPhase]
    · rw [roundDiskReflection_coe c hr hz]
      have hn : c+(r:ℂ)^2/(starRingEnd ℂ (z-c))≠c := by
        have hrC : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
        intro hh
        have he : (r:ℂ)^2/(starRingEnd ℂ (z-c))=0 := by linear_combination hh
        exact (div_ne_zero (pow_ne_zero 2 hrC) (map_ne_zero (starRingEnd ℂ) |>.mpr (sub_ne_zero.mpr hz))) he
      simp only [sphereReflectionPhase,sphereCoefficient_coe,circleReflectionPhase,ite_eq_right hz,
        ite_eq_right hn,add_sub_cancel_left,map_div₀,map_pow,Complex.conj_ofReal,Complex.conj_conj]
      have hrC : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
      field_simp [hrC,sub_ne_zero.mpr hz]

end CircleDomainRigidity

end

end OAI
