import OAI.Analysis.KadisonKastler.RealPartDualBound
import OAI.Analysis.FactorGeneration.OperatorLimits
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Group.Pointwise

namespace OAI

/-! # Weak operator separation and operator-norm distance

A dual estimate on weak-operator continuous functionals annihilating a
closed subspace gives strict norm approximants in that subspace.
-/

namespace KadisonKastler

open scoped Pointwise

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def wotNormBall (r : ℝ) : Set (H →WOT[ℂ] H) := {T | ‖T.toCLM‖ ≤ r}

theorem wotNormBall_compact (r : ℝ) : IsCompact (wotNormBall (H := H) r) := by
  let M : VonNeumannAlgebra H :=
    { toStarSubalgebra := StarSubalgebra.centralizer ℂ (∅ : Set (H →L[ℂ] H))
      centralizer_centralizer' := Set.centralizer_centralizer_centralizer _ }
  have he : Generator.Tracial.weakOperatorBall M r = wotNormBall (H := H) r := by
    ext T
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      change T.toCLM ∈ StarSubalgebra.centralizer ℂ (∅ : Set (H →L[ℂ] H))
      simp [StarSubalgebra.mem_centralizer_iff]
  rw [← he]
  exact Generator.Tracial.weakOperatorBall_isCompact M r

omit [CompleteSpace H] in
theorem wotNormBall_convex (r : ℝ) : Convex ℝ (wotNormBall (H := H) r) := by
  have he : wotNormBall (H := H) r =
      ContinuousLinearMapWOT.ofCLM '' Metric.closedBall (0 : H →L[ℂ] H) r := by
    ext T
    constructor
    · intro hT
      exact ⟨T.toCLM, by simpa [wotNormBall, Metric.mem_closedBall] using hT, rfl⟩
    · rintro ⟨T, hT, rfl⟩
      simpa [wotNormBall, Metric.mem_closedBall] using hT
  rw [he]
  exact (convex_closedBall (0 : H →L[ℂ] H) r).linear_image
    ((ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ)).restrictScalars ℝ).toLinearMap

theorem exists_near_subspace_of_wot_dual_bound
    (S : Submodule ℂ (H →L[ℂ] H))
    (hS : IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ S})
    (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hdual : ∀ f : (H →WOT[ℂ] H) →L[ℂ] ℂ,
      (∀ D ∈ S, f (ContinuousLinearMapWOT.ofCLM D) = 0) →
      ‖f (ContinuousLinearMapWOT.ofCLM T)‖ ≤
        c * ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖)
    {r : ℝ} (hr : c < r) : ∃ D ∈ S, ‖D - T‖ < r := by
  classical
  let s := (c + r) / 2
  have hcs : c < s := by dsimp [s]; linarith
  have hsr : s < r := by dsimp [s]; linarith
  have hs : 0 < s := lt_of_le_of_lt hc hcs
  let C : Submodule ℂ (H →WOT[ℂ] H) :=
    S.comap (ContinuousLinearMapWOT.linearEquiv ℂ).toLinearMap
  let B := wotNormBall (H := H) s
  have hclosed : IsClosed ((C : Set (H →WOT[ℂ] H)) + B) :=
    hS.add_right_of_isCompact (wotNormBall_compact s)
  have hconvex : Convex ℝ ((C : Set (H →WOT[ℂ] H)) + B) :=
    (C.restrictScalars ℝ).convex.add (wotNormBall_convex s)
  by_contra hn
  have hnot : ContinuousLinearMapWOT.ofCLM T ∉ (C : Set (H →WOT[ℂ] H)) + B := by
    rintro ⟨D, hD, E, hE, hsum⟩
    apply hn
    refine ⟨D.toCLM, hD, ?_⟩
    have he : D.toCLM - T = -E.toCLM := by
      have hh := congrArg ContinuousLinearMapWOT.toCLM hsum
      change D.toCLM + E.toCLM = T at hh
      rw [← hh]
      abel
    rw [he, norm_neg]
    exact (show ‖E.toCLM‖ ≤ s from hE).trans_lt hsr
  obtain ⟨f, u, hfu, hut⟩ := RCLike.geometric_hahn_banach_closed_point
    (𝕜 := ℂ) hconvex hclosed hnot
  have hzero : ∀ D ∈ S, f (ContinuousLinearMapWOT.ofCLM D) = 0 := by
    intro D hD
    by_contra hne
    let z : ℂ := (u + 1) / f (ContinuousLinearMapWOT.ofCLM D)
    have hmem : ContinuousLinearMapWOT.ofCLM (z • D) ∈
        (C : Set (H →WOT[ℂ] H)) + B := by
      refine ⟨ContinuousLinearMapWOT.ofCLM (z • D), S.smul_mem z hD, 0, ?_, add_zero _⟩
      change ‖(0 : H →L[ℂ] H)‖ ≤ s
      simpa using hs.le
    have hh := hfu _ hmem
    have he : f (ContinuousLinearMapWOT.ofCLM (z • D)) = (u + 1 : ℂ) := by
      rw [ContinuousLinearMapWOT.ofCLM_smul, map_smul, smul_eq_mul]
      exact div_mul_cancel₀ _ hne
    rw [he] at hh
    norm_num at hh
  have hball : ∀ X : H →L[ℂ] H, ‖X‖ ≤ s →
      (f (ContinuousLinearMapWOT.ofCLM X)).re ≤ u := by
    intro X hX
    exact (hfu _ ⟨0, S.zero_mem, ContinuousLinearMapWOT.ofCLM X, hX, zero_add _⟩).le
  have hnorm : s * ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ ≤ u :=
    norm_mul_le_of_real_bound _ hs hball
  have hbound := hdual f hzero
  have hre := Complex.re_le_norm (f (ContinuousLinearMapWOT.ofCLM T))
  have hcmp := mul_le_mul_of_nonneg_right hcs.le
    (norm_nonneg (f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))))
  change u < (f (ContinuousLinearMapWOT.ofCLM T)).re at hut
  linarith

end

end KadisonKastler

end OAI
