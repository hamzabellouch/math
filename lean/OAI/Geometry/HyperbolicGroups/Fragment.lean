import Mathlib
import OAI.Geometry.HyperbolicGroups.RankCollection
import OAI.Geometry.HyperbolicGroups.FanApex
import OAI.Geometry.HyperbolicGroups.WeightedRank

namespace OAI

section
section


noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction
namespace IncidenceTemplate.Occurrences.Shape

/-- Exact source defect constant. It depends on the fixed parameters, not on
alphabet size, the picture or fragment. -/
def defectConstant (α β δ : ℝ) : ℝ := min (β-7*α) (min (α/5) δ)

lemma defectConstant_pos {α β δ : ℝ} (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    0 < defectConstant α β δ := by
  exact lt_min (sub_pos.mpr hb) (lt_min (div_pos ha (by norm_num)) hd)

/-- Per-fan normal link data, all indexed sides, and elementary side counts of
an actual fragment. No filling or area inequality is a field of this structure. -/
structure FragmentData {s u q v : ℕ} (T : Shape s u q) (W : T.Weights (v := v)) where
  r : Fin u → ℕ
  slots : Fin u → ℕ
  links : (b : Fin u) → FanLink.FanData (r b) (slots b) s
  weight_eq : ∀ b, (links b).weight = W.fan b
  slots_eq : (∑ b, slots b) = 7 * ∑ a, W.top a
  turns_ge : 3 * (∑ a, W.top a) ≤ ∑ b, (links b).turns
  contacts : ℕ
  left : Fin contacts → T.Pos v
  right : Fin contacts → T.Pos v
  different : ∀ e, left e ≠ right e
  capacity : ∀ p, (Finset.univ.filter (fun e => left e = p ∨ right e = p)).card ≤ W.position p
  rawBoundary : ℕ
  radialBoundary : ℕ
  raw_sides : rawBoundary + 2*contacts = (∑ b, (links b).triangles) +
    (∑ b, (links b).payments) + 4*(∑ e, W.square e) + 6*(∑ e, W.six e)
  radial_sides : (∑ b, (links b).boundary) ≤ radialBoundary

namespace FragmentData
variable {s u q v : ℕ} {T : Shape s u q} {W : T.Weights (v := v)} (F : FragmentData T W)

def tops (_F : FragmentData T W) : ℕ := ∑ a, W.top a
def triangles : ℕ := ∑ b, (F.links b).triangles
def squares (_F : FragmentData T W) : ℕ := ∑ e, W.square e
def hexagons (_F : FragmentData T W) : ℕ := ∑ e, W.six e
def fanWeight (_F : FragmentData T W) : ℕ := ∑ b, W.fan b
def payments : ℕ := ∑ b, (F.links b).payments
def partialCount : ℕ := ∑ b, (F.links b).partialCount
def area : ℕ := F.tops + F.triangles + F.squares + F.hexagons
def boundary : ℕ := F.rawBoundary + F.radialBoundary

def defect (α β δ : ℝ) : ℝ := (β-7*α)*F.tops + α*F.fanWeight + δ*(F.squares+F.hexagons)

lemma nominal_apex :
    3*(F.tops:ℝ) + 2*((F.fanWeight:ℝ)-7*F.tops) ≤
      ((F.triangles:ℝ)+F.payments)/2 + 2*F.partialCount := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun b _ => (F.links b).apex_bound)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_div,← Finset.mul_sum,
    F.weight_eq] at hh
  have hs : (∑ b, (F.slots b:ℝ)) = 7*(F.tops:ℝ) := by
    exact_mod_cast F.slots_eq
  have ht : 3*(F.tops:ℝ) ≤ ∑ b, ((F.links b).turns:ℝ) := by
    exact_mod_cast F.turns_ge
  simp only [hs] at hh
  have hh' : (∑ b, ((F.links b).turns:ℝ)) + 2*((F.fanWeight:ℝ)-7*F.tops) ≤
    ((F.triangles:ℝ)+F.payments)/2+2*F.partialCount := by
    simpa only [fanWeight,triangles,payments,partialCount,Nat.cast_sum] using hh
  linarith

lemma triangles_le : F.triangles ≤ 5*F.fanWeight := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ => (F.links b).triangles_le)
  simpa only [triangles,fanWeight,F.weight_eq,← Finset.mul_sum] using h

lemma partial_le : 2*F.partialCount ≤ F.radialBoundary := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ => (F.links b).partial_le_boundary)
  have h' : 2*F.partialCount ≤ ∑ b, (F.links b).boundary := by
    simpa only [partialCount,← Finset.mul_sum] using h
  exact h'.trans F.radial_sides

lemma defect_ge {α β δ : ℝ} (ha : 0 ≤ α) :
    defectConstant α β δ * F.area ≤ F.defect α β δ := by
  have h1 : defectConstant α β δ ≤ β-7*α := min_le_left _ _
  have h2 : defectConstant α β δ ≤ α/5 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : defectConstant α β δ ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  have ht := F.triangles_le
  have ht' : (F.triangles:ℝ) ≤ 5*F.fanWeight := by exact_mod_cast ht
  have hq : α/5*(F.triangles:ℝ) ≤ α*F.fanWeight := by nlinarith
  have ht1 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg F.tops)
  have ht2 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg F.triangles)
  have ht3 := mul_le_mul_of_nonneg_right h3 (show (0:ℝ) ≤ F.squares+F.hexagons by positivity)
  dsimp [defect,area]
  push_cast
  dsimp [tops,triangles,squares,hexagons,fanWeight] at *
  push_cast at *
  nlinarith

/-- Full source fragment inequality, derived from the produced rank event on
the actual same arrays and the normal links/indexed side data above. -/
theorem bound {M n K : ℕ} {α β δ : ℝ} {w : Entry (SymmetricAlphabet n) → Bool}
    (ha : 0 ≤ α) (h : GoodUpTo M α β δ w)
    (hs : s ≤ M) (hu : u ≤ M) (hq : q ≤ M) (hv : v ≤ M)
    (σ : T.Pos v → SymmetricAlphabet n) (hi : Function.Injective (T.row σ))
    (hp : BernoulliCandidates.Present T.row w σ)
    (htK : ∀ a, W.top a ≤ K) (hfK : ∀ b, W.fan b ≤ K)
    (hqK : ∀ e, W.square e ≤ K) (hdK : ∀ e, W.six e ≤ K)
    (hc : ∀ e, (σ (F.left e)).1 = (σ (F.right e)).1) :
    defectConstant α β δ * F.area ≤ F.boundary := by
  have hcontact := W.contact_bound h hs hu hq hv σ hi hp htK hfK hqK hdK
    F.left F.right F.different hc (fun p => by
      convert F.capacity p using 1
      congr 1
      exact Finset.filter_congr_decidable _ _ _)
  simp only [Fintype.card_fin] at hcontact
  have hcontact' : (F.contacts:ℝ) ≤ ((3-β)-7*(2-α))*F.tops + (2-α)*F.fanWeight +
    (2-δ)*F.squares+(3-δ)*F.hexagons := by
    simpa only [tops,fanWeight,squares,hexagons,Nat.cast_sum] using hcontact
  have hapex := F.nominal_apex
  have hd := F.defect_ge (β := β) (δ := δ) ha
  have hj : 2*(F.partialCount:ℝ) ≤ F.radialBoundary := by exact_mod_cast F.partial_le
  have hr : (F.rawBoundary:ℝ)+2*F.contacts = (F.triangles:ℝ)+F.payments+
      4*F.squares+6*F.hexagons := by exact_mod_cast F.raw_sides
  have hb : (0:ℝ) ≤ F.rawBoundary := Nat.cast_nonneg _
  dsimp [defect] at hd
  simp only [boundary,Nat.cast_add]
  nlinarith

theorem area_le {κ C : ℝ} (hk : 0 < κ) (hC : C = 1/κ)
    (h : κ * F.area ≤ F.boundary) : (F.area:ℝ) ≤ C*F.boundary := by
  rw [hC,one_div,← div_eq_inv_mul]
  exact (le_div_iff₀ hk).mpr (by simpa [mul_comm] using h)

end FragmentData
end IncidenceTemplate.Occurrences.Shape
end HyperbolicObstruction
end
end

section

end
end

end OAI
