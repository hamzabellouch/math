import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.PathCalculus
import OAI.Analysis.BiholderTransport.Regularity.UnitTime
import OAI.Analysis.BiholderTransport.Calculus.ImplicitNeighborhood

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

section ImplicitODE
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

lemma exists_smooth_rescaled_equation_on (N : P → P) (hN : ContDiff ℝ ∞ N)
    (c : E →L[ℝ] P) (A : P →L[ℝ] P) (a : E) :
    ∃ U : (ℝ × E) → P, ∃ S : Set (ℝ × E), IsOpen S ∧ (0,a) ∈ S ∧
      ContDiffOn ℝ ∞ U S ∧ U (0,a) = c a ∧
      ∀ z ∈ S, U z = c z.2 + z.1 • A (N (U z)) := by
  let F : (ℝ × E) × P → P := fun z => z.2 - c z.1.2 - z.1.1 • A (N z.2)
  let b : P := c a
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_snd.sub (c.contDiff.comp (contDiff_snd.comp contDiff_fst))).sub
      ((contDiff_fst.comp contDiff_fst).smul (A.contDiff.comp (hN.comp contDiff_snd)))
  have hpart : fderiv ℝ F ((0,a),b) ∘L inr ℝ (ℝ × E) P = ContinuousLinearMap.id ℝ P := by
    have hpair : HasFDerivAt (fun p : P => ((0,a),p)) (inr ℝ (ℝ × E) P) b :=
      (hasFDerivAt_const ((0:ℝ),a) b).prodMk (hasFDerivAt_id b)
    have hc := (hF.differentiable (by simp) ((0,a),b)).hasFDerivAt.comp b hpair
    have hd : HasFDerivAt (fun p : P => F ((0,a),p)) (ContinuousLinearMap.id ℝ P) b := by
      simpa only [F,zero_smul,sub_zero,id_eq] using (hasFDerivAt_id b).sub_const (c a)
    exact hc.unique hd
  have hi : (fderiv ℝ F ((0,a),b) ∘L inr ℝ (ℝ × E) P).IsInvertible := by
    rw [hpart]
    exact ⟨ContinuousLinearEquiv.refl ℝ P,rfl⟩
  obtain ⟨U,S,hS,ha,hU,hb,hEq⟩ := exists_smooth_implicit_neighborhood F hF (0,a) b hi
  refine ⟨U,S,hS,ha,hU,hb,?_⟩
  intro z hz
  have hz' : U z - c z.2 - z.1 • A (N (U z)) = 0 := by
    simpa only [F,b,zero_smul,sub_self,sub_zero] using hEq z hz
  simpa only [add_comm] using eq_add_of_sub_eq (sub_eq_zero.mp hz')

end ImplicitODE
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma exists_smooth_rescaled_ode_family_on (f : E → E) (hf : ContDiff ℝ ∞ f) (a : E) :
    ∃ U : (ℝ × E) → C(UnitTime,E), ∃ S : Set (ℝ × E), IsOpen S ∧ (0,a) ∈ S ∧
      ContDiffOn ℝ ∞ U S ∧ U (0,a) = ContinuousMap.const UnitTime a ∧
      ∀ z ∈ S, U z = ContinuousMap.const UnitTime z.2 +
        z.1 • unitPathIntegral ((⟨f,hf.continuous⟩ : C(E,E)).comp (U z)) := by
  let fC : C(E,E) := ⟨f,hf.continuous⟩
  exact exists_smooth_rescaled_equation_on (fun p => fC.comp p) (contDiff_path_comp fC hf)
    (ContinuousLinearMap.const ℝ UnitTime) unitPathIntegral a

end

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def rescaledIntegralCurve (f : C(E,E)) (t : ℝ) (x : E) (u : C(UnitTime,E)) (s : ℝ) : E :=
  x + t • ∫ r in (0:ℝ)..s, extendUnitPath (f.comp u) r

omit [CompleteSpace E] in
@[simp] lemma rescaledIntegralCurve_zero (f : C(E,E)) (t : ℝ) (x : E) (u : C(UnitTime,E)) :
    rescaledIntegralCurve f t x u 0 = x := by simp [rescaledIntegralCurve]

omit [CompleteSpace E] in
lemma rescaledIntegralCurve_eq (f : C(E,E)) (t : ℝ) (x : E) (u : C(UnitTime,E))
    (hu : u = ContinuousMap.const UnitTime x + t • unitPathIntegral (f.comp u)) (s : UnitTime) :
    rescaledIntegralCurve f t x u s = u s := by
  have h := congrArg (fun v : C(UnitTime,E) => v s) hu
  exact h.symm

lemma hasDerivAt_rescaledIntegralCurve (f : C(E,E)) (t : ℝ) (x : E) (u : C(UnitTime,E))
    (hu : u = ContinuousMap.const UnitTime x + t • unitPathIntegral (f.comp u))
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    HasDerivAt (rescaledIntegralCurve f t x u) (t • f (rescaledIntegralCurve f t x u s)) s := by
  have hd := ((hasDerivAt_unitPathPrimitive (f.comp u) s).const_smul t).const_add x
  have hc := rescaledIntegralCurve_eq f t x u hu ⟨s,hs⟩
  have he : extendUnitPath (f.comp u) s = f (rescaledIntegralCurve f t x u s) := by
    rw [hc]
    exact extendUnitPath_coe (f.comp u) ⟨s,hs⟩
  change HasDerivAt (rescaledIntegralCurve f t x u)
    (t • extendUnitPath (f.comp u) s) s at hd
  rw [he] at hd
  exact hd

omit [CompleteSpace E] in
lemma lipschitzOnWith_const_smul {f : E → E} {K : ℝ≥0} {B : Set E}
    (hf : LipschitzOnWith K f B) (t : ℝ) :
    LipschitzOnWith (‖t‖₊ * K) (fun x => t • f x) B := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm,←smul_sub,norm_smul,NNReal.coe_mul,coe_nnnorm,mul_assoc]
  simpa only [dist_eq_norm] using
    mul_le_mul_of_nonneg_left (hf.dist_le_mul x hx y hy) (norm_nonneg t)

lemma rescaled_ode_path_time_scaling (f : C(E,E)) (t : ℝ) (x : E)
    (u v : C(UnitTime,E)) (s : UnitTime) (K : ℝ≥0) (B : Set E)
    (hf : LipschitzOnWith K f B)
    (hu : u = ContinuousMap.const UnitTime x + t • unitPathIntegral (f.comp u))
    (hv : v = ContinuousMap.const UnitTime x + (t * s.val) • unitPathIntegral (f.comp v))
    (huB : ∀ r, u r ∈ B) (hvB : ∀ r, v r ∈ B) :
    u s = v ⟨1,by simp⟩ := by
  let U := rescaledIntegralCurve f t x u
  let V := rescaledIntegralCurve f (t*s.val) x v
  have hsr : ∀ r ∈ Icc (0:ℝ) 1, s.val * r ∈ Icc (0:ℝ) 1 := by
    intro r hr
    exact ⟨mul_nonneg s.property.1 hr.1,
      (mul_le_of_le_one_left hr.1 s.property.2).trans hr.2⟩
  have hU : ∀ r ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun q => U (s.val*q)) ((t*s.val) • f (U (s.val*r))) r := by
    intro r hr
    have h := (hasDerivAt_rescaledIntegralCurve f t x u hu (s.val*r) (hsr r hr)).scomp r
      ((hasDerivAt_id r).const_mul s.val)
    simpa only [mul_one,smul_smul,mul_comm,Function.comp_def,U] using h
  have hV : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt V ((t*s.val) • f (V r)) r :=
    hasDerivAt_rescaledIntegralCurve f (t*s.val) x v hv
  have hEq : EqOn (fun q => U (s.val*q)) V (Icc (0:ℝ) 1) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun (_ : ℝ) z => (t*s.val) • f z) (s := fun _ => B) (K := ‖t*s.val‖₊ * K)
    · intro r hr; exact lipschitzOnWith_const_smul hf (t*s.val)
    · exact HasDerivAt.continuousOn hU
    · intro r hr; exact (hU r (Ico_subset_Icc_self hr)).hasDerivWithinAt
    · intro r hr
      dsimp only [U]
      rw [rescaledIntegralCurve_eq f t x u hu ⟨s.val*r,hsr r (Ico_subset_Icc_self hr)⟩]
      exact huB _
    · exact HasDerivAt.continuousOn hV
    · intro r hr; exact (hV r (Ico_subset_Icc_self hr)).hasDerivWithinAt
    · intro r hr
      dsimp only [V]
      rw [rescaledIntegralCurve_eq f (t*s.val) x v hv ⟨r,Ico_subset_Icc_self hr⟩]
      exact hvB _
    · simp only [U,V,mul_zero,rescaledIntegralCurve_zero]
  have h := hEq (by simp : (1:ℝ) ∈ Icc (0:ℝ) 1)
  change U (s.val*1) = V 1 at h
  simpa only [mul_one,U,V,rescaledIntegralCurve_eq f t x u hu s,
    rescaledIntegralCurve_eq f (t*s.val) x v hv ⟨1,by simp⟩] using h

end WeakMTWTransport

end

end OAI
