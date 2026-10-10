import OAI.Analysis.CircleDomains.Topology.CollarExtension
import OAI.Analysis.CircleDomains.Selection.WedgeEstimate

namespace OAI

/-!
# Rank-one smooth filling of a collar

If at most one coordinate varies on a collar, extend that coordinate by
a smooth cutoff and all the others constantly. Every pairwise wedge of
the resulting coordinate gradients vanishes throughout the filling.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def planarGradient (f : (ℝ × ℝ) → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (fderiv ℝ f x (1, 0), fderiv ℝ f x (0, 1))

@[simp] theorem planarGradient_const (c : ℝ) (x : ℝ × ℝ) :
    planarGradient (fun _ => c) x = 0 := by
  simp [planarGradient]

/-- The scalar collar extension gives a simultaneous smooth extension
with zero pairwise wedges when only one boundary coordinate is active. -/
theorem exists_rank_one_collar_extension {ι : Type*} (k : ι)
    {U A : Set (ℝ × ℝ)} (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U)
    (f : ι → (ℝ × ℝ) → ℝ) (c : ι → ℝ)
    (hfk : ContDiffOn ℝ ∞ (f k) U)
    (hinactive : ∀ i, i ≠ k → EqOn (f i) (fun _ => c i) U) :
    ∃ F : ι → (ℝ × ℝ) → ℝ,
      (∀ i, ContDiff ℝ ∞ (F i)) ∧
      (∀ᶠ x in 𝓝ˢ A, ∀ i, F i x = f i x) ∧
      (∀ i x, x ∉ U → F i x = c i) ∧
      (∀ i j, i ≠ j → ∀ x, planarWedge (planarGradient (F i) x)
        (planarGradient (F j) x) = 0) := by
  classical
  obtain ⟨g, hg, hag, hgc⟩ := exists_smooth_collar_extension hU hA hAU hfk (c k)
  let F : ι → (ℝ × ℝ) → ℝ := fun i => if i = k then g else fun _ => c i
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = k
    · simpa [F, hi] using hg
    · simpa [F, hi] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => c i))
  · have hUnhds : U ∈ 𝓝ˢ A := hU.mem_nhdsSet.mpr hAU
    filter_upwards [hag, hUnhds] with x hx hxU i
    by_cases hi : i = k
    · simpa [F, hi] using hx
    · simpa [F, hi] using (hinactive i hi hxU).symm
  · intro i x hx
    by_cases hi : i = k
    · simpa [F, hi] using hgc x hx
    · simp [F, hi]
  · intro i j hij x
    by_cases hi : i = k
    · have hj : j ≠ k := fun hj => hij (hi.trans hj.symm)
      simp [F, hj, planarWedge]
    · simp [F, hi, planarWedge]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
