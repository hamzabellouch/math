import OAI.Analysis.Mahler.WedgeCalculus
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

open ContinuousAlternatingMap
open scoped TensorProduct

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The shuffle product bundled with its actual joint-vector continuity. -/
def continuousWedge (a : E [⋀^ι]→L[ℝ] ℂ) (b : E [⋀^κ]→L[ℝ] ℂ) :
    E [⋀^ι ⊕ κ]→L[ℝ] ℂ :=
  { wedge a.toAlternatingMap b.toAlternatingMap with
    cont := by
      change Continuous (fun v => wedge a.toAlternatingMap b.toAlternatingMap v)
      have ht (σ : Equiv.Perm.ModSumCongr ι κ) : Continuous
          (fun v : ι ⊕ κ → E => (LinearMap.mul' ℝ ℂ)
            (AlternatingMap.domCoprod.summand a.toAlternatingMap b.toAlternatingMap σ v)) := by
        induction σ using Quotient.inductionOn' with
        | h σ =>
          simp only [wedge_summand_eval]
          exact continuous_const.mul
            ((a.cont.comp (continuous_pi (fun i => continuous_apply _))).mul
              (b.cont.comp (continuous_pi (fun i => continuous_apply _))))
      simpa only [wedge, LinearMap.compAlternatingMap_apply, AlternatingMap.domCoprod_apply,
        _root_.sum_apply, _root_.map_sum] using
          continuous_finsetSum Finset.univ (fun σ _ => ht σ) }

@[simp] lemma continuousWedge_apply (a : E [⋀^ι]→L[ℝ] ℂ)
    (b : E [⋀^κ]→L[ℝ] ℂ) (v : ι ⊕ κ → E) :
    continuousWedge a b v = wedge a.toAlternatingMap b.toAlternatingMap v := rfl

instance finiteDimensional_continuousAlternatingMap [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (E [⋀^ι]→L[ℝ] ℂ) := by
  let L : (E [⋀^ι]→L[ℝ] ℂ) →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ :=
    { toFun := fun a => a.toAlternatingMap.toMultilinearMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective L (fun a b h => by
    ext v
    exact congrArg (fun c : MultilinearMap ℝ (fun _ : ι => E) ℂ => c v) h)

lemma continuousWedge_add_left (a a' : E [⋀^ι]→L[ℝ] ℂ) (b : E [⋀^κ]→L[ℝ] ℂ) :
    continuousWedge (a+a') b = continuousWedge a b + continuousWedge a' b := by
  ext v
  change wedge (a.toAlternatingMap + a'.toAlternatingMap) b.toAlternatingMap v =
    wedge a.toAlternatingMap b.toAlternatingMap v + wedge a'.toAlternatingMap b.toAlternatingMap v
  simp only [wedge, ← AlternatingMap.domCoprod'_apply,
    ← LinearMap.compAlternatingMapₗ_apply ℝ, TensorProduct.add_tmul, map_add]
  rfl

lemma continuousWedge_add_right (a : E [⋀^ι]→L[ℝ] ℂ) (b b' : E [⋀^κ]→L[ℝ] ℂ) :
    continuousWedge a (b+b') = continuousWedge a b + continuousWedge a b' := by
  ext v
  change wedge a.toAlternatingMap (b.toAlternatingMap + b'.toAlternatingMap) v =
    wedge a.toAlternatingMap b.toAlternatingMap v + wedge a.toAlternatingMap b'.toAlternatingMap v
  simp only [wedge, ← AlternatingMap.domCoprod'_apply,
    ← LinearMap.compAlternatingMapₗ_apply ℝ, TensorProduct.tmul_add, map_add]
  rfl

lemma continuousWedge_smul_left (r : ℝ) (a : E [⋀^ι]→L[ℝ] ℂ) (b : E [⋀^κ]→L[ℝ] ℂ) :
    continuousWedge (r • a) b = r • continuousWedge a b := by
  have he : (r • a).toAlternatingMap = (r : ℂ) • a.toAlternatingMap := by
    ext v; simp [Complex.real_smul]
  ext v
  simp only [continuousWedge_apply, he, wedge_smul_left, AlternatingMap.smul_apply,
    ContinuousAlternatingMap.smul_apply, Complex.real_smul, smul_eq_mul]

lemma continuousWedge_smul_right (r : ℝ) (a : E [⋀^ι]→L[ℝ] ℂ) (b : E [⋀^κ]→L[ℝ] ℂ) :
    continuousWedge a (r • b) = r • continuousWedge a b := by
  have he : (r • b).toAlternatingMap = (r : ℂ) • b.toAlternatingMap := by
    ext v; simp [Complex.real_smul]
  ext v
  simp only [continuousWedge_apply, he, wedge_smul_right, AlternatingMap.smul_apply,
    ContinuousAlternatingMap.smul_apply, Complex.real_smul, smul_eq_mul]

/-- Exterior multiplication is an actual continuous bilinear map. -/
def continuousWedgeCLM [FiniteDimensional ℝ E] :
    (E [⋀^ι]→L[ℝ] ℂ) →L[ℝ] (E [⋀^κ]→L[ℝ] ℂ) →L[ℝ] E [⋀^ι ⊕ κ]→L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => LinearMap.toContinuousLinearMap
        { toFun := continuousWedge a
          map_add' := continuousWedge_add_right a
          map_smul' := fun r b => continuousWedge_smul_right r a b }
      map_add' := fun a a' => by ext b v; exact congrArg (fun c => c v) (continuousWedge_add_left a a' b)
      map_smul' := fun r a => by ext b v; exact congrArg (fun c => c v) (continuousWedge_smul_left r a b) }

lemma contDiffAt_continuousWedge [FiniteDimensional ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {r : WithTop ℕ∞}
    {a : X → E [⋀^ι]→L[ℝ] ℂ} {b : X → E [⋀^κ]→L[ℝ] ℂ} {x : X}
    (ha : ContDiffAt ℝ r a x) (hb : ContDiffAt ℝ r b x) :
    ContDiffAt ℝ r (fun y => continuousWedge (a y) (b y)) x := by
  let W := continuousWedgeCLM (E := E) (ι := ι) (κ := κ)
  have hw := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := r)
    (E := E [⋀^ι]→L[ℝ] ℂ)
    (F := (E [⋀^κ]→L[ℝ] ℂ) →L[ℝ] E [⋀^ι ⊕ κ]→L[ℝ] ℂ) W
  have hw' := hw.contDiffAt.comp x ha
  exact hw'.clm_apply hb

end
end Mahler

end OAI
