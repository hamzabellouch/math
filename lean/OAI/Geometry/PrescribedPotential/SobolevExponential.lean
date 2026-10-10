import Mathlib
import OAI.Geometry.PrescribedPotential.CompletedProduct
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealPoisson
import OAI.Geometry.PrescribedPotential.RealSobolev

namespace OAI

/-! Sobolev Exponential. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical BoundedContinuousFunction
namespace ExponentialEvaluation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma apply_exp (L : E →L[ℝ] E) (q : E →L[ℝ] ℝ) (a : ℝ)
    (hq : ∀ v, q (L v) = a * q v) (v : E) :
    q (NormedSpace.exp L v) = Real.exp a * q v := by
  have hp (n : ℕ) : q ((L^n) v) = a^n * q v := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [pow_succ']
      change q (L ((L^n) v)) = _
      rw [hq, hn, pow_succ']
      ring
  let e := q.comp (ContinuousLinearMap.apply ℝ E v)
  have hl := e.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) L)
  have hr := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).mul_right (q v)
  rw [← Real.exp_eq_exp_ℝ] at hr
  have ht : (fun n : ℕ => e ((n.factorial : ℝ)⁻¹ • L^n)) =
      (fun n : ℕ => (n.factorial : ℝ)⁻¹ • a^n * q v) := by
    funext n
    change q (((n.factorial : ℝ)⁻¹ • L^n) v) = (n.factorial : ℝ)⁻¹ * a^n * q v
    rw [_root_.smul_apply, map_smul, hp]
    simp only [smul_eq_mul]
    ring
  rw [ht] at hl
  exact hl.unique hr

def orbit (L : E →L[ℝ] E) (v : E) (t : ℝ) : E :=
  NormedSpace.exp (t • L) v

omit [CompleteSpace E] in
lemma orbit_zero (L : E →L[ℝ] E) (v : E) : orbit L v 0 = v := by
  simp [orbit, NormedSpace.exp_zero]

lemma orbit_continuous (L : E →L[ℝ] E) (v : E) : Continuous (orbit L v) := by
  have ht : Continuous (fun t : ℝ => t • L) := continuous_id.smul continuous_const
  have he : Continuous (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) :=
    continuous_iff_continuousAt.mpr (fun w => (NormedSpace.exp_analytic (𝕂 := ℝ) w).continuousAt)
  exact (ContinuousLinearMap.apply ℝ E v).continuous.comp (he.comp ht)
end ExponentialEvaluation

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace RealSmooth

def mul (F h : RealSmooth A) : RealSmooth A :=
  ⟨F.val.mul h.val, fun x => by
    change (F.val x * h.val x).im = 0
    rw [Complex.mul_im, F.property, h.property]
    ring⟩
end RealSmooth
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance expRealNormedGroup (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance expRealNormedSpace (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance expRealTopologicalGroup (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance expRealContinuousSMul (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

def realMultiplier (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (F : RealSmooth A) :
    D.localizers.RealSobolev (k : ℝ) →L[ℝ] D.localizers.RealSobolev (k : ℝ) :=
  ((D.product k hk (D.localizers.embed (k : ℝ) F.val)).comp
    (D.localizers.realCompletion (k : ℝ)).subtypeL).codRestrict
      (D.localizers.realCompletion (k : ℝ)) (fun u =>
    D.localizers.maps_realCompletion (D.product k hk (D.localizers.embed (k : ℝ) F.val))
      (fun h => ⟨F.mul h,D.product_embed k hk F.val h.val⟩) u.val u.property)

lemma realMultiplier_evaluation (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (F : RealSmooth A) (u : D.localizers.RealSobolev (k : ℝ)) (x : X) :
    D.realEvaluation (k : ℝ) x (D.realMultiplier k hk F u) =
      F.source.value x * D.realEvaluation (k : ℝ) x u := by
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  change (D.localizers.strong (k : ℝ)
    (D.product k hk (D.localizers.embed (k : ℝ) F.val) u.val) x).re = _
  rw [D.product_strong, BoundedContinuousFunction.mul_apply, D.localizers.strong_embed _ hs]
  change (F.val x * D.localizers.strong (k : ℝ) u.val x).re = _
  rw [Complex.mul_re, F.property, zero_mul, sub_zero]
  rfl

 

def exponentialDensity (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (F : RealSmooth A) (t : ℝ) : D.localizers.RealSobolev (k : ℝ) :=
  ExponentialEvaluation.orbit (D.realMultiplier k hk F) (D.realConstants (k : ℝ) 1) t

lemma exponentialDensity_zero (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (F : RealSmooth A) : D.exponentialDensity k hk F 0 = D.realConstants (k : ℝ) 1 := by
  exact ExponentialEvaluation.orbit_zero _ _

lemma exponentialDensity_continuous (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (F : RealSmooth A) : Continuous (D.exponentialDensity k hk F) := by
  exact ExponentialEvaluation.orbit_continuous _ _

lemma exponentialDensity_strong [ConnectedSpace X] (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (F : RealSmooth A) (t : ℝ) (x : X) :
    D.localizers.strong (k : ℝ) (D.exponentialDensity k hk F t).val x =
      (Real.exp (t * F.source.value x) : ℂ) := by
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hh := ExponentialEvaluation.apply_exp (t • D.realMultiplier k hk F)
    (D.realEvaluation (k : ℝ) x) (t * F.source.value x) (fun u => by
      rw [_root_.smul_apply, map_smul, D.realMultiplier_evaluation]
      simp only [smul_eq_mul]
      ring) (D.realConstants (k : ℝ) 1)
  rw [D.realEvaluation_constants hs, mul_one] at hh
  apply Complex.ext
  · exact hh
  · exact D.localizers.real_strong hs (D.exponentialDensity k hk F t) x

end GluingData
end GlobalElliptic

end
end

end OAI
