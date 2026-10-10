import OAI.Probability.InvariantIsing.Cavity.CavityRoundedSelfConsistency
import OAI.Probability.InvariantIsing.Cavity.CavityFieldPath
import OAI.Probability.InvariantIsing.Fields.FieldMagnetizationFiber

namespace OAI

/-! The actual finite scalar fields satisfy the tied-fiber hypothesis
away from their countably many grid endpoints. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavityFieldStep_height_on_rounded_cell {ι : Type*} [Fintype ι]
    (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p pbase : OverlapPath) (round : ℝ → ℝ)
    {n : ℕ} (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) (hq0 : ∀ i, 0 ≤ q i)
    (hround : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → q i = round (pbase s))
    (i : Fin (n + 1)) {s : ℝ} (hs : s ∈ Ioo (cut i.castSucc) (cut i.succ)) :
    (cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq hq0).height i =
      cavityFieldPrimitive rho lam hrho hsum p (round (pbase s)) := by
  change cavityFieldPrimitive rho lam hrho hsum p (q i) = _
  rw [hround i s hs]

/-- Once the rounded cavity-spin tests converge, the actual scalar
magnetization paths converge in L1. Grid endpoints need no convention. -/
theorem cavity_field_self_consistency_l1 (p : OverlapPath)
    (q : ℕ → OverlapPath) (h : ℕ → FieldStep) (height : ℕ → ℝ → ℝ)
    (hheight : ∀ n i s, s ∈ Ioo ((h n).cut i.castSucc) ((h n).cut i.succ) →
      (h n).height i = height n (p s))
    (hq : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => q n s) atTop (𝓝 (p s)))
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto
      (fun n => ∫ s, Φ (q n s) * (fieldMagnetizationPath (h n) s - q n s) ∂pathMeasure)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, |fieldMagnetizationPath (h n) s - p s| ∂pathMeasure)
      atTop (𝓝 0) := by
  let D := {s | ∀ n, ∃ i : Fin ((h n).depth + 1),
    s ∈ Ioo ((h n).cut i.castSucc) ((h n).cut i.succ)}
  have hDae : ∀ᵐ s ∂pathMeasure, s ∈ D :=
    ae_all_iff.mpr (fun n => ae_finite_overlap_cell (h n).cut (h n).first (h n).last)
  apply cavity_rounded_self_consistency_l1_on p q (fun n => fieldMagnetizationPath (h n))
    hq D hDae ?_ htest
  intro n x hx y hy hxy
  obtain ⟨i, hi⟩ := hx n
  obtain ⟨j, hj⟩ := hy n
  apply fieldMagnetizationPath_eq_of_cell_height_eq (h n) i j hi hj
  rw [hheight n i x hi, hheight n j y hj, hxy]

end InvariantIsing

end

end OAI
