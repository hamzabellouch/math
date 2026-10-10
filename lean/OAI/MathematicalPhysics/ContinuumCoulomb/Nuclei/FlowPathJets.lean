import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowLocalModel

namespace OAI

/-! Spatial derivatives as continuous paths. Taking derivatives in this
Banach space preserves the integral equation through order four without
requiring a fifth joint derivative of the vector field. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb
open WeakMTWTransport

abbrev SpatialPath := C(UnitTime, Position)

def modelPath (H : ℝ × Position → Position) (hH : Continuous H)
    (y : Position) : SpatialPath :=
  ⟨fun t => H (t,y), hH.comp (continuous_subtype_val.prodMk continuous_const)⟩

theorem modelPath_C4 (H : ℝ × Position → Position) (hH : ContDiff ℝ 4 H) :
    ContDiff ℝ 4 (modelPath H hH.continuous) := by
  let T : C(UnitTime, ℝ × Position) :=
    ⟨fun s => (s,0), continuous_subtype_val.prodMk continuous_const⟩
  let L : Position →L[ℝ] C(UnitTime, ℝ × Position) :=
    (ContinuousLinearMap.const ℝ UnitTime).comp (inr ℝ ℝ Position)
  have hA : ContDiff ℝ 4 (fun y => T + L y) := contDiff_const.add L.contDiff
  have hc := (contDiff_path_comp_nat 4 (⟨H,hH.continuous⟩ : C(ℝ × Position,Position)) hH).comp hA
  have heq : ((fun v : C(UnitTime,ℝ × Position) =>
      (⟨H,hH.continuous⟩ : C(ℝ × Position,Position)).comp v) ∘ (fun y => T + L y)) =
      modelPath H hH.continuous := by
    funext y
    apply ContinuousMap.ext
    intro s
    change H ((s.val,(0:Position)) + ((0:ℝ),y)) = H (s,y)
    simp
  rwa [heq] at hc

theorem modelPath_iterated_apply (H : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (n : ℕ) (hn : n ≤ 4) (x : Position)
    (e : Fin n → Position) (t : UnitTime) :
    (iteratedFDeriv ℝ n (modelPath H hH.continuous) x e) t =
      iteratedFDeriv ℝ n (fun y => H (t,y)) x e := by
  have h := (ContinuousMap.evalCLM (R := ℝ) t).iteratedFDeriv_comp_left (x := x)
    (modelPath_C4 H hH).contDiffAt (show (n : WithTop ℕ∞) ≤ 4 by exact_mod_cast hn)
  have heq : (ContinuousMap.evalCLM (R := ℝ) t) ∘ modelPath H hH.continuous =
      (fun y => H (t,y)) := rfl
  rw [heq] at h
  exact (congrArg (fun M => M e) h).symm

end ContinuumCoulomb

end

end OAI
