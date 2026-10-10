import OAI.Analysis.SphereIsometry.KuratowskiConvexHull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace OAI

/-!
# The closed-convex image iteration

Starting from a closed convex invariant set `C`, the actual successor set is
the closure of the convex hull of its image under `g`. All boundedness claims
come from containment in `C`. No boundedness-preservation property of an
arbitrary continuous map is used.
-/

noncomputable section

namespace Tingley

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The literal closed-convex image operator used in the condensing argument. -/
def condensingStep (g : E → E) (H : Set E) : Set E :=
  closure (convexHull ℝ (g '' H))

/-- The iteration begins at `C` and takes actual closed-convex images. -/
def condensingSequence (C : Set E) (g : E → E) : ℕ → Set E
  | 0 => C
  | n + 1 => condensingStep g (condensingSequence C g n)

@[simp] theorem condensingSequence_zero (C : Set E) (g : E → E) :
    condensingSequence C g 0 = C := rfl

@[simp] theorem condensingSequence_succ (C : Set E) (g : E → E) (n : ℕ) :
    condensingSequence C g (n + 1) = condensingStep g (condensingSequence C g n) := rfl

theorem condensingStep_mono (g : E → E) : Monotone (condensingStep g) := by
  intro H J hHJ
  exact closure_mono (convexHull_mono (image_mono hHJ))

theorem image_subset_condensingStep (g : E → E) (H : Set E) :
    g '' H ⊆ condensingStep g H :=
  (subset_convexHull ℝ (g '' H)).trans subset_closure

theorem condensingStep_subset {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) :
    condensingStep g C ⊆ C := by
  apply closure_minimal _ hclosed
  apply convexHull_min _ hconv
  rintro y ⟨x, hx, rfl⟩
  exact hmap hx

theorem condensingSequence_succ_subset {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) (n : ℕ) :
    condensingSequence C g (n + 1) ⊆ condensingSequence C g n := by
  induction n with
  | zero => exact condensingStep_subset hclosed hconv hmap
  | succ n ih => exact condensingStep_mono g ih

theorem condensingSequence_antitone {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) :
    Antitone (condensingSequence C g) :=
  antitone_nat_of_succ_le (condensingSequence_succ_subset hclosed hconv hmap)

theorem condensingSequence_subset {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) (n : ℕ) :
    condensingSequence C g n ⊆ C :=
  condensingSequence_antitone hclosed hconv hmap (Nat.zero_le n)

/-- Every image point belongs to the next set, before using antitonicity. -/
theorem condensingSequence_image_subset_succ (C : Set E) (g : E → E) (n : ℕ) :
    g '' condensingSequence C g n ⊆ condensingSequence C g (n + 1) :=
  image_subset_condensingStep g (condensingSequence C g n)

theorem condensingSequence_nonempty {C : Set E} (g : E → E)
    (hne : C.Nonempty) (n : ℕ) : (condensingSequence C g n).Nonempty := by
  induction n with
  | zero => exact hne
  | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      exact ⟨g x, condensingSequence_image_subset_succ C g n (mem_image_of_mem g hx)⟩

theorem condensingSequence_isClosed {C : Set E} (g : E → E)
    (hclosed : IsClosed C) (n : ℕ) : IsClosed (condensingSequence C g n) := by
  cases n with
  | zero => exact hclosed
  | succ n => exact isClosed_closure

theorem condensingSequence_convex {C : Set E} (g : E → E)
    (hconv : Convex ℝ C) (n : ℕ) : Convex ℝ (condensingSequence C g n) := by
  cases n with
  | zero => exact hconv
  | succ n => exact (convex_convexHull ℝ (g '' condensingSequence C g n)).closure

theorem condensingSequence_isBounded {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) (n : ℕ) :
    Bornology.IsBounded (condensingSequence C g n) :=
  hbounded.subset (condensingSequence_subset hclosed hconv hmap n)

theorem condensingSequence_mapsTo {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) (n : ℕ) :
    MapsTo g (condensingSequence C g n) (condensingSequence C g n) := by
  intro x hx
  exact condensingSequence_succ_subset hclosed hconv hmap n
    (condensingSequence_image_subset_succ C g n (mem_image_of_mem g hx))

theorem condensingSequence_image_subset {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) (n : ℕ) :
    g '' condensingSequence C g n ⊆ C := by
  rintro y ⟨x, hx, rfl⟩
  exact hmap (condensingSequence_subset hclosed hconv hmap n hx)

theorem condensingSequence_image_isBounded {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) (n : ℕ) :
    Bornology.IsBounded (g '' condensingSequence C g n) :=
  hbounded.subset (condensingSequence_image_subset hclosed hconv hmap n)

/-- The hull step leaves the actual Kuratowski measure of its bounded image unchanged. -/
theorem condensingSequence_chi_succ_eq {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) (n : ℕ) :
    chi (condensingSequence C g (n + 1)) = chi (g '' condensingSequence C g n) := by
  exact chi_closedConvexHull
    (condensingSequence_image_isBounded hclosed hconv hmap hbounded n)

theorem condensingSequence_chi_succ_le {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) {γ : ℝ}
    (hχ : ∀ H : Set E, H ⊆ C → chi (g '' H) ≤ γ * chi H) (n : ℕ) :
    chi (condensingSequence C g (n + 1)) ≤ γ * chi (condensingSequence C g n) := by
  rw [condensingSequence_chi_succ_eq hclosed hconv hmap hbounded n]
  exact hχ _ (condensingSequence_subset hclosed hconv hmap n)

/-- Geometric decay allows `γ = 0`; no division by the contraction factor occurs. -/
theorem condensingSequence_chi_le {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hχ : ∀ H : Set E, H ⊆ C → chi (g '' H) ≤ γ * chi H) (n : ℕ) :
    chi (condensingSequence C g n) ≤ γ ^ n * chi C := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        chi (condensingSequence C g (n + 1)) ≤ γ * chi (condensingSequence C g n) :=
          condensingSequence_chi_succ_le hclosed hconv hmap hbounded hχ n
        _ ≤ γ * (γ ^ n * chi C) := mul_le_mul_of_nonneg_left ih hγ0
        _ = γ ^ (n + 1) * chi C := by rw [pow_succ', mul_assoc]

theorem condensingSequence_chi_nonneg {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) (n : ℕ) :
    0 ≤ chi (condensingSequence C g n) :=
  chi_nonneg (condensingSequence_isBounded hclosed hconv hmap hbounded n)

/-- The actual sequence has Kuratowski measure tending to zero for `0 ≤ γ < 1`. -/
theorem condensingSequence_chi_tendsto_zero {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hχ : ∀ H : Set E, H ⊆ C → chi (g '' H) ≤ γ * chi H) :
    Tendsto (fun n => chi (condensingSequence C g n)) atTop (𝓝 0) := by
  apply squeeze_zero
    (condensingSequence_chi_nonneg hclosed hconv hmap hbounded)
    (condensingSequence_chi_le hclosed hconv hmap hbounded hγ0 hχ)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (chi C)

end Tingley

end

end OAI
