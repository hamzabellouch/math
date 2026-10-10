import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Semicontinuity.Basic

namespace OAI

/-! # Unique centers of compact convex Hilbert images

Only compactness for the lower semicontinuous squared distances is used.
This form applies directly to weak operator compact sets of implementers.
-/

namespace KadisonKastler

noncomputable section

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A compact family whose Hilbert image is bounded and midpoint convex
has a unique image minimizing its squared covering radius. -/
theorem exists_unique_compact_hilbert_center
    (K : Set X) (hK : IsCompact K) (hne : K.Nonempty) (v : X → E)
    (hdist : ∀ y, LowerSemicontinuous (fun x => ‖v x - y‖ ^ 2))
    (hmid : ∀ x ∈ K, ∀ y ∈ K,
      ∃ z ∈ K, v z = (1 / 2 : ℝ) • (v x + v y))
    (C : ℝ) (hC : ∀ x ∈ K, ‖v x‖ ≤ C) :
    ∃ x ∈ K, ∀ y ∈ K,
      (∀ z ∈ K, ‖v y - v z‖ ^ 2 ≤ ⨆ w : K, ‖v x - v w‖ ^ 2) → v y = v x := by
  classical
  let : Nonempty K := hne.to_subtype
  let R (x : X) : ℝ := ⨆ y : K, ‖v x - v y‖ ^ 2
  have hb (x : X) : BddAbove (Set.range (fun y : K => ‖v x - v y‖ ^ 2)) := by
    refine ⟨(‖v x‖ + C) ^ 2, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg (v x - v y))
      ((norm_sub_le (v x) (v y)).trans (by linarith [hC y y.property])) 2
  have hR : LowerSemicontinuous R :=
    lowerSemicontinuous_ciSup hb (fun y => hdist (v y))
  obtain ⟨x, hx, hm⟩ := (hR.lowerSemicontinuousOn K).exists_isMinOn hne hK
  have hmin := isMinOn_iff.mp hm
  have hle (a : X) (b : K) : ‖v a - v b‖ ^ 2 ≤ R a := le_ciSup (hb a) b
  refine ⟨x, hx, ?_⟩
  intro y hy hyr
  obtain ⟨z, hz, he⟩ := hmid x hx y hy
  have hupper : R z ≤ R x - ‖v x - v y‖ ^ 2 / 4 := by
    apply ciSup_le
    intro w
    have hp := parallelogram_law_with_norm ℂ (v x - v w) (v y - v w)
    have headd : (v x - v w) + (v y - v w) = (2 : ℝ) • (v z - v w) := by
      rw [he]
      module
    have hesub : (v x - v w) - (v y - v w) = v x - v y := by abel
    rw [headd, hesub, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hp
    have hwx := hle x w
    have hwy := hyr w w.property
    nlinarith
  have hzm : R x ≤ R z := hmin z hz
  have hn : ‖v x - v y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v x - v y‖]
  have hh : v x - v y = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  exact (sub_eq_zero.mp hh).symm

end

end KadisonKastler

end OAI
