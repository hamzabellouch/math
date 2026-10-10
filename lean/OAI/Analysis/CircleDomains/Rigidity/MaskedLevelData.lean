import OAI.Analysis.CircleDomains.Selection.RestrictedCoordinateMarks
import OAI.Analysis.CircleDomains.Selection.PriorLevelFamily
import OAI.Analysis.CircleDomains.Selection.RealTestLevelData

namespace OAI

/-! The actual marked band widths supply the level weights for the next
endpoint-law construction. This uses the full dust as a temporary label
set; the common countable mark restriction is performed after selection. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

namespace FiniteTransfer.MaskedCoordinateData
variable {G U B : Set Sphere} {π : Sphere → Sphere}
  (C : MaskedCoordinateData G U π (fun x : B => x.val))

def dustWeight (x : Sphere) : ℝ≥0∞ := by
  classical
  exact if hx : x ∈ B then ENNReal.ofReal (C.upper ⟨x, hx⟩ - C.lower ⟨x, hx⟩) else 0

theorem dustWeight_square_sum : (∑' x, C.dustWeight x ^ 2) < ∞ := by
  classical
  have he : (∑' x, C.dustWeight x ^ 2) =
      ∑' s : B, ENNReal.ofReal ((C.upper s - C.lower s) ^ 2) := by
    have hsupp : support (fun x => C.dustWeight x ^ 2) ⊆ B := by
      intro x hx
      by_contra hn
      exact hx (by simp only [dustWeight, dite_eq_right hn, zero_pow (by decide : 2 ≠ 0)])
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    apply tsum_congr
    intro s
    simp only [dustWeight, dite_eq_left s.property,
      ENNReal.ofReal_pow (C.width_nonneg s)]
  rw [he, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) C.width_summable]
  exact ENNReal.ofReal_lt_top

theorem incidence_le_dustWeight
    (hBU : Bᶜ ⊆ U)
    (hU : ∀ x ∈ U, {t : UnitAddCircle | (x, t) ∈ C.graph}.Subsingleton)
    (x : Sphere) : volume {t : UnitAddCircle | (x, t) ∈ C.graph} ≤ C.dustWeight x := by
  classical
  by_cases hx : x ∈ B
  · rw [dustWeight, dite_eq_left hx]
    exact (measure_mono (C.marked_fiber ⟨x, hx⟩)).trans
      ((volume_addCircle_image_Icc_le _ _).trans
        (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  · let : NullSingletonClass (volume : Measure UnitAddCircle) :=
      ⟨unitAddCircle_volume_singleton⟩
    rw [dustWeight, dite_eq_right hx, (hU x (hBU hx)).measure_zero volume]

theorem unique_of_dustWeight_eq_zero {x : Sphere} (hx : x ∈ B)
    (hw : C.dustWeight x = 0) : {t : UnitAddCircle | (x, t) ∈ C.graph}.Subsingleton := by
  have hle : C.upper ⟨x, hx⟩ - C.lower ⟨x, hx⟩ ≤ 0 := by
    apply ENNReal.ofReal_eq_zero.mp
    simpa only [dustWeight, dite_eq_left hx] using hw
  have he : C.lower ⟨x, hx⟩ = C.upper ⟨x, hx⟩ :=
    (sub_eq_zero.mp (le_antisymm hle (C.width_nonneg ⟨x, hx⟩))).symm
  have hb := C.marked_fiber ⟨x, hx⟩
  rw [he, Icc_self, image_singleton] at hb
  intro a ha b hb'
  exact (mem_singleton_iff.mp (hb ha)).trans (mem_singleton_iff.mp (hb hb')).symm

end FiniteTransfer.MaskedCoordinateData

variable [MeasurableSpace C(PathTime, Sphere)]

def maskedLevelData (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (C : ℕ → MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val)) : PathCodeData Sphere Sphere :=
  { d with
    levels := fun i => Prod.swap ⁻¹' (C i).graph
    levelWeights := fun i => (C i).dustWeight }

namespace maskedLevelData
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  (C : ℕ → MaskedCoordinateData d.physicalDomain d.quotientDomain π
    (fun x : d.dust => x.val))

theorem weight_finite (i : ℕ) : (∑' x, (maskedLevelData d π C).levelWeights i x ^ 2) < ∞ :=
  (C i).dustWeight_square_sum

theorem point_bound (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (hU : ∀ i x, x ∈ d.quotientDomain →
      {t : UnitAddCircle | (x, t) ∈ (C i).graph}.Subsingleton) (i : ℕ) (x : Sphere) :
    volume {t | (t, x) ∈ (maskedLevelData d π C).levels i} ≤
      (maskedLevelData d π C).levelWeights i x :=
  (C i).incidence_le_dustWeight hBU (hU i) x

theorem unique_free_trace (flags : Set Sphere)
    (hflags : ∀ i, support ((maskedLevelData d π C).levelWeights i) ⊆ flags)
    (x : Sphere) (hx : x ∈ d.dust \ flags) (i : ℕ) (a b : UnitAddCircle)
    (ha : (a, x) ∈ (maskedLevelData d π C).levels i)
    (hb : (b, x) ∈ (maskedLevelData d π C).levels i) : a = b := by
  have hw : (C i).dustWeight x = 0 := by
    by_contra h
    exact hx.2 (hflags i h)
  exact (C i).unique_of_dustWeight_eq_zero hx.1 hw ha hb

theorem level_relation (i : ℕ) :
    levelRelation (maskedLevelData d π C).levels i = (C i).graph := by
  ext p
  rfl

theorem exists_countable_flags (B₀ : Set Sphere) (hB₀ : B₀.Countable)
    (hB₀B : B₀ ⊆ d.dust) :
    ∃ flags : Set Sphere, flags.Countable ∧ B₀ ⊆ flags ∧ flags ⊆ d.dust ∧
      (∀ i, ((C i).singular : Sphere) ∈ flags) ∧
      ∀ i, support ((maskedLevelData d π C).levelWeights i) ⊆ flags := by
  obtain ⟨A, hA, hBA, hs, hw⟩ := exists_common_countable_coordinate_marks C
    (Subtype.val ⁻¹' B₀) (hB₀.preimage Subtype.val_injective)
  refine ⟨Subtype.val '' A, hA.image _, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hB₀B hx⟩, hBA hx, rfl⟩
  · rintro x ⟨s, _, rfl⟩
    exact s.property
  · intro i
    exact ⟨(C i).singular, hs i, rfl⟩
  · intro i x hx
    change (C i).dustWeight x ≠ 0 at hx
    by_cases hxB : x ∈ d.dust
    · refine ⟨⟨x, hxB⟩, hw i ⟨x, hxB⟩ ?_, rfl⟩
      intro he
      exact hx (by simp only [MaskedCoordinateData.dustWeight, dite_eq_left hxB, he,
        ENNReal.ofReal_zero])
    · exact (hx (by simp only [MaskedCoordinateData.dustWeight, dite_eq_right hxB])).elim

end maskedLevelData

end CircleDomainRigidity

end

end OAI
