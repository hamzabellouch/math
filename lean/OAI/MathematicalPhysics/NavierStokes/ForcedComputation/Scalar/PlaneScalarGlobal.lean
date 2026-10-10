import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarComparison

namespace OAI

/-! Consistent finite-cylinder solutions give one scalar evolution for all
nonnegative time, with compatibility supplied by uniqueness. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem PlaneScalarSolution.restrict {T S ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} (hw : PlaneScalarSolution T ν a h w) (hST : S ≤ T) :
    PlaneScalarSolution S ν a h w := by
  have hsub : Icc (0 : ℝ) S ⊆ Icc 0 T := Icc_subset_Icc le_rfl hST
  refine ⟨hw.smooth.mono (fun _ hp => ⟨hsub hp.1, hp.2⟩), hw.initial, ?_, ?_⟩
  · intro t ht x
    exact (hw.equation t (hsub ht) x).mono hsub
  · obtain ⟨B, hB⟩ := hw.bounded
    exact ⟨B, fun t ht => hB t (hsub ht)⟩

theorem PlaneScalarSolution.congr {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w v : ℝ → Plane → ℝ} (hw : PlaneScalarSolution T ν a h w) (hT : 0 ≤ T)
    (he : ∀ t ∈ Icc 0 T, v t = w t) : PlaneScalarSolution T ν a h v := by
  refine ⟨hw.smooth.congr (fun p hp => congrFun (he p.1 hp.1) p.2), ?_, ?_, ?_⟩
  · rw [he 0 ⟨le_rfl, hT⟩]
    exact hw.initial
  · intro t ht x
    rw [he t ht]
    exact (hw.equation t ht x).congr_of_mem (fun s hs => congrFun (he s hs) x) ht
  · obtain ⟨B, hB⟩ := hw.bounded
    refine ⟨B, ?_⟩
    intro t ht x
    rw [he t ht]
    exact hB t ht x

/-- Bounded smooth solutions on every finite closed time cylinder. -/
def GlobalPlaneScalarSolution (ν : ℝ) (a : ℝ → Plane → Plane)
    (h w : ℝ → Plane → ℝ) : Prop := ∀ T, 0 ≤ T → PlaneScalarSolution T ν a h w

theorem PlaneScalarExistence.global (hE : PlaneScalarExistence)
    (ν : ℝ) (hν : 0 < ν) (a : ℝ → Plane → Plane) (h : ℝ → Plane → ℝ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h) :
    ∃ w, GlobalPlaneScalarSolution ν a h w := by
  have hex (n : ℕ) : ∃ w, PlaneScalarSolution ((n : ℝ) + 1) ν a h w := by
    obtain ⟨w, hw, _⟩ := hE ((n : ℝ) + 1) ν (by positivity) hν a h ha hh hc
    exact ⟨w, hw⟩
  choose v hv using hex
  have hcompat (m n : ℕ) {s : ℝ} (hs : 0 ≤ s)
      (hm : s ≤ (m : ℝ) + 1) (hn : s ≤ (n : ℝ) + 1) : v m s = v n s := by
    let T := min ((m : ℝ) + 1) ((n : ℝ) + 1)
    have hT : 0 ≤ T := le_min (by positivity) (by positivity)
    have hsm : T ≤ (m : ℝ) + 1 := min_le_left _ _
    have hsn : T ≤ (n : ℝ) + 1 := min_le_right _ _
    exact ((hv m).restrict hsm).unique ((hv n).restrict hsn) hT hν.le ha hc s
      ⟨hs, le_min hm hn⟩
  let w : ℝ → Plane → ℝ := fun t => v ⌈t⌉₊ t
  refine ⟨w, fun T hT => ?_⟩
  let N : ℕ := ⌈T⌉₊
  have hTN : T ≤ (N : ℝ) + 1 := (Nat.le_ceil T).trans (by linarith)
  apply ((hv N).restrict hTN).congr hT
  intro t ht
  exact hcompat ⌈t⌉₊ N ht.1 ((Nat.le_ceil t).trans (by linarith)) (ht.2.trans hTN)

theorem GlobalPlaneScalarSolution.nonnegative {ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} (hw : GlobalPlaneScalarSolution ν a h w)
    (hν : 0 ≤ ν) (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hc : CompactPlaneCoefficients a h) (hh : ∀ t, 0 ≤ t → ∀ x, 0 ≤ h t x) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x := by
  intro t ht x
  exact (hw t ht).nonnegative ht hν ha hc (fun s hs => hh s hs.1) t ⟨ht, le_rfl⟩ x

theorem GlobalPlaneScalarSolution.unique {ν : ℝ} {a : ℝ → Plane → Plane}
    {h w v : ℝ → Plane → ℝ} (hw : GlobalPlaneScalarSolution ν a h w)
    (hv : GlobalPlaneScalarSolution ν a h v) (hν : 0 ≤ ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (hc : CompactPlaneCoefficients a h) :
    ∀ t, 0 ≤ t → w t = v t := by
  intro t ht
  exact (hw t ht).unique (hv t ht) ht hν ha hc t ⟨ht, le_rfl⟩

end ForcedComputation.VelocityDetector

end

end OAI
