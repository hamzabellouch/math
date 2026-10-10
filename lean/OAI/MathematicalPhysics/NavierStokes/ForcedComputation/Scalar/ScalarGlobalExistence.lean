import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarBounds

namespace OAI

/-! Consistent finite-cylinder solutions give one scalar evolution for all
nonnegative time, with compatibility supplied by uniqueness. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem TorusScalarSolution.restrict {T S ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : TorusScalarSolution T ν a h w w₀) (hST : S ≤ T) :
    TorusScalarSolution S ν a h w w₀ := by
  have hsub : Icc (0 : ℝ) S ⊆ Icc 0 T := Icc_subset_Icc le_rfl hST
  refine ⟨hw.smooth.mono (fun _ hp => ⟨hsub hp.1, hp.2⟩),
    fun t ht => hw.periodic t (hsub ht), hw.initial, ?_⟩
  intro t ht x
  exact (hw.equation t (hsub ht) x).mono hsub

theorem TorusScalarSolution.congr {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w v : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : TorusScalarSolution T ν a h w w₀) (hT : 0 ≤ T)
    (he : ∀ t ∈ Icc 0 T, v t = w t) : TorusScalarSolution T ν a h v w₀ := by
  refine ⟨hw.smooth.congr (fun p hp => congrFun (he p.1 hp.1) p.2), ?_, ?_, ?_⟩
  · intro t ht
    rw [he t ht]
    exact hw.periodic t ht
  · rw [he 0 ⟨le_rfl, hT⟩]
    exact hw.initial
  · intro t ht x
    rw [he t ht]
    exact (hw.equation t ht x).congr_of_mem (fun s hs => congrFun (he s hs) x) ht

/-- Smoothness and the equation on every finite closed time cylinder. -/
def GlobalTorusScalarSolution (ν : ℝ) (a : ℝ → Plane → Plane)
    (h w : ℝ → Plane → ℝ) (w₀ : Plane → ℝ) : Prop :=
  ∀ T, 0 ≤ T → TorusScalarSolution T ν a h w w₀

theorem TorusScalarExistence.global (hE : TorusScalarExistence)
    (ν : ℝ) (hν : 0 < ν) (a : ℝ → Plane → Plane)
    (h : ℝ → Plane → ℝ) (w₀ : Plane → ℝ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hw₀ : ContDiff ℝ ∞ w₀)
    (hpa : ∀ t, PlanePeriodic (a t)) (hph : ∀ t, PlanePeriodic (h t))
    (hp₀ : PlanePeriodic w₀) :
    ∃ w, GlobalTorusScalarSolution ν a h w w₀ := by
  have hex (n : ℕ) : ∃ w, TorusScalarSolution ((n : ℝ) + 1) ν a h w w₀ :=
    hE _ ν (by positivity) hν a h w₀ ha hh hw₀ hpa hph hp₀
  choose v hv using hex
  have hcompat (m n : ℕ) {s : ℝ} (hs : 0 ≤ s)
      (hm : s ≤ (m : ℝ) + 1) (hn : s ≤ (n : ℝ) + 1) : v m s = v n s := by
    let T := min ((m : ℝ) + 1) ((n : ℝ) + 1)
    have hT : 0 ≤ T := le_min (by positivity) (by positivity)
    have hsm : T ≤ (m : ℝ) + 1 := min_le_left _ _
    have hsn : T ≤ (n : ℝ) + 1 := min_le_right _ _
    exact ((hv m).restrict hsm).unique ((hv n).restrict hsn) hT hν.le s
      ⟨hs, le_min hm hn⟩
  let w : ℝ → Plane → ℝ := fun t => v ⌈t⌉₊ t
  refine ⟨w, fun T hT => ?_⟩
  let N : ℕ := ⌈T⌉₊
  have hTN : T ≤ (N : ℝ) + 1 := (Nat.le_ceil T).trans (by linarith)
  apply ((hv N).restrict hTN).congr hT
  intro t ht
  exact hcompat ⌈t⌉₊ N ht.1 ((Nat.le_ceil t).trans (by linarith)) (ht.2.trans hTN)

theorem GlobalTorusScalarSolution.nonnegative {ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : GlobalTorusScalarSolution ν a h w w₀) (hν : 0 ≤ ν)
    (hh : ∀ t, 0 ≤ t → ∀ x, 0 ≤ h t x) (h₀ : ∀ x, 0 ≤ w₀ x) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x := by
  intro t ht x
  exact (hw t ht).nonnegative ht hν (fun s hs => hh s hs.1) h₀ t ⟨ht, le_rfl⟩ x

theorem GlobalTorusScalarSolution.unique {ν : ℝ} {a : ℝ → Plane → Plane}
    {h w v : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : GlobalTorusScalarSolution ν a h w w₀)
    (hv : GlobalTorusScalarSolution ν a h v w₀) (hν : 0 ≤ ν) :
    ∀ t, 0 ≤ t → w t = v t := by
  intro t ht
  exact (hw t ht).unique (hv t ht) ht hν t ⟨ht, le_rfl⟩

end ForcedComputation.VelocityDetector

end

end OAI
