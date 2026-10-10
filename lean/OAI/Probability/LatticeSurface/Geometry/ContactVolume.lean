import Mathlib
import OAI.Probability.LatticeSurface.Convexity.AffineVolume
import OAI.Probability.LatticeSurface.Geometry.StrictFilling

namespace OAI

namespace StrictFilling

section Metric

variable {X : Type*} [PseudoMetricSpace X]

end Metric

end StrictFilling

noncomputable section

open MeasureTheory MeasureTheory.Measure

open scoped ENNReal Pointwise

namespace StrictFilling

attribute [local instance] Classical.propDecidable

abbrev FreeCoord {V : Type*} (fixed : Set V) := {x : V // x ∉ fixed}

def restore {V : Type*} (fixed : Set V) (b : V → ℝ)
    (a : FreeCoord fixed → ℝ) (x : V) : ℝ :=
  if hx : x ∈ fixed then b x else a ⟨x, hx⟩

def conditionalBody {V : Type*} (G : SimpleGraph V) (fixed : Set V)
    (b : V → ℝ) (I : V → Set ℝ) : Set (FreeCoord fixed → ℝ) :=
  {a | (∀ x y, G.Adj x y → |restore fixed b a x - restore fixed b a y| ≤ 1) ∧
    ∀ x ∉ fixed, restore fixed b a x ∈ I x}

def contactRegion {V : Type*} (G : SimpleGraph V) (fixed : Set V)
    (b : V → ℝ) (I : V → Set ℝ) (u v : V) (s : ℝ) : Set (FreeCoord fixed → ℝ) :=
  conditionalBody G fixed b I ∩
    {a | 1 - s < |restore fixed b a u - restore fixed b a v|}

def restoreAffine {V : Type*} (fixed : Set V) (b : V → ℝ) (x : V) :
    (FreeCoord fixed → ℝ) →ᵃ[ℝ] ℝ :=
  if hx : x ∈ fixed then AffineMap.const ℝ _ (b x)
  else (LinearMap.proj (⟨x, hx⟩ : FreeCoord fixed)).toAffineMap

@[simp] lemma restoreAffine_apply {V : Type*} (fixed : Set V) (b : V → ℝ)
    (x : V) (a : FreeCoord fixed → ℝ) :
    restoreAffine fixed b x a = restore fixed b a x := by
  unfold restoreAffine restore
  split_ifs <;> rfl

@[simp] lemma restore_fixed {V : Type*} (fixed : Set V) (b : V → ℝ)
    (a : FreeCoord fixed → ℝ) {x : V} (hx : x ∈ fixed) :
    restore fixed b a x = b x := dite_eq_left hx

@[simp] lemma restore_free {V : Type*} (fixed : Set V) (b : V → ℝ)
    (a : FreeCoord fixed → ℝ) (x : FreeCoord fixed) :
    restore fixed b a x = a x := dite_eq_right x.property

lemma conditionalBody_convex {V : Type*} (G : SimpleGraph V) (fixed : Set V)
    (b : V → ℝ) (I : V → Set ℝ)
    (hI : ∀ x ∉ fixed, (I x).OrdConnected) :
    Convex ℝ (conditionalBody G fixed b I) := by
  intro a ha c hc α β hα hβ hsum
  constructor
  · intro x y hxy
    let φ := restoreAffine fixed b x - restoreAffine fixed b y
    have hx : φ a ∈ Set.Icc (-1) 1 := by
      simpa only [φ, AffineMap.coe_sub, Pi.sub_apply, restoreAffine_apply, Set.mem_Icc, ← abs_le] using ha.1 x y hxy
    have hy : φ c ∈ Set.Icc (-1) 1 := by
      simpa only [φ, AffineMap.coe_sub, Pi.sub_apply, restoreAffine_apply, Set.mem_Icc, ← abs_le] using hc.1 x y hxy
    have h := ((convex_Icc (-1 : ℝ) 1).affine_preimage φ) hx hy hα hβ hsum
    simpa only [φ, Set.mem_preimage, AffineMap.coe_sub, Pi.sub_apply, restoreAffine_apply, Set.mem_Icc, ← abs_le] using h
  · intro x hx
    have h := ((hI x hx).convex.affine_preimage (restoreAffine fixed b x))
      (show restoreAffine fixed b x a ∈ I x by simpa using ha.2 x hx)
      (show restoreAffine fixed b x c ∈ I x by simpa using hc.2 x hx)
      hα hβ hsum
    simpa only [Set.mem_preimage, restoreAffine_apply] using h

theorem graph_conditional_contact_volume {V : Type*} [Fintype V]
    (G : SimpleGraph V) (shell pins : Set V) (b : V → ℝ) (I : V → Set ℝ)
    (u v : V) (hedge : G.Adj u v)
    (hpin : ∀ x ∈ pins, |b x| ≤ 1 / 2)
    (hI : ∀ x ∉ shell ∪ pins, (I x).OrdConnected ∧ 0 ∈ I x)
    (hnotfixed : ¬ (u ∈ shell ∪ pins ∧ v ∈ shell ∪ pins))
    (hroom : ∃ a ∈ conditionalBody G (shell ∪ pins) b I,
      ∀ x, (x = u ∨ x = v) → x ∉ shell ∪ pins → ∀ t ∈ shell,
        G.Reachable x t →
          |restore (shell ∪ pins) b a x - b t| ≤ (G.dist x t : ℝ) - 2)
    (hfinite : volume (conditionalBody G (shell ∪ pins) b I) ≠ ⊤)
    (hpositive : volume (conditionalBody G (shell ∪ pins) b I) ≠ 0)
    (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) :
    (volume (contactRegion G (shell ∪ pins) b I u v s)).toReal /
        (volume (conditionalBody G (shell ∪ pins) b I)).toReal ≤
      1 - (1 - 2 * s) ^ Fintype.card (FreeCoord (shell ∪ pins)) ∧
    1 - (1 - 2 * s) ^ Fintype.card (FreeCoord (shell ∪ pins)) ≤
      2 * (Fintype.card (FreeCoord (shell ∪ pins)) : ℝ) * s := by
  classical
  obtain ⟨a, ha, haroom⟩ := hroom
  obtain ⟨g, hgedge, hgfixed, hginterval, hgstrict⟩ :=
    graph_strict_filling G (restore (shell ∪ pins) b a) shell pins I u v hedge ha.1
      (by
        intro x hx
        simpa only [restore_fixed (shell ∪ pins) b a (Set.mem_union_right shell hx)] using hpin x hx)
      (by
        intro x hx
        exact ⟨(hI x hx).1, (hI x hx).2, ha.2 x hx⟩)
      hnotfixed
      (by
        intro x hxu hx t ht hxt
        simpa only [restore_fixed (shell ∪ pins) b a (Set.mem_union_left pins ht)] using
          haroom x hxu hx t ht hxt)
  let ag : FreeCoord (shell ∪ pins) → ℝ := fun x => g x
  have hgrestore : ∀ x, restore (shell ∪ pins) b ag x = g x := by
    intro x
    by_cases hx : x ∈ shell ∪ pins
    · rw [restore_fixed _ _ _ hx, hgfixed x hx, restore_fixed _ _ _ hx]
    · simp only [restore, dite_eq_right hx, ag]
  have hag : ag ∈ conditionalBody G (shell ∪ pins) b I := by
    constructor
    · intro x y hxy
      simpa only [hgrestore] using hgedge x y hxy
    · intro x hx
      simpa only [hgrestore] using hginterval x hx
  let φ : (FreeCoord (shell ∪ pins) → ℝ) →ᵃ[ℝ] ℝ :=
    restoreAffine (shell ∪ pins) b u - restoreAffine (shell ∪ pins) b v
  have hφ : ∀ c, φ c = restore (shell ∪ pins) b c u - restore (shell ∪ pins) b c v := by
    intro c
    simp only [φ, AffineMap.coe_sub, Pi.sub_apply, restoreAffine_apply]
  have hconv := conditionalBody_convex G (shell ∪ pins) b I (fun x hx => (hI x hx).1)
  have hvol := contact_volume_contraction volume _ hconv φ
    (fun c hc => by rw [hφ]; exact hc.1 u v hedge) ag hag
    (by simpa only [hφ, hgrestore] using hgstrict) hfinite hpositive s hs hs'
  constructor
  · simpa only [contactRegion, hφ, Module.finrank_pi] using hvol
  · exact contraction_volume_bound _ s hs hs'

end StrictFilling

end

end OAI
