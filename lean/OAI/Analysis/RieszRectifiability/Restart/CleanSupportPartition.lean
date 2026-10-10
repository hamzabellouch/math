import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.SupportCellOverlaps

namespace OAI

/-!
# Cleaning the support lattice partition

Removing the union of all cell overlaps produces nested, disjoint measurable cells that
cover the support outside one exceptional set. Net centers avoid that set, so cleaning
preserves the closed cells as closures. Under the growth bounds, it also preserves cell
mass and gives a unique cell at every scale almost everywhere.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

def supportLatticeExceptional {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) :
    Set (Ambient d) := ⋃ k : ℕ, supportLatticeOverlap μ R hR k

def cleanSupportCell {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : Set (Ambient d) :=
  supportLatticeCell μ R hR k z \ supportLatticeExceptional μ R hR

theorem supportLatticeExceptional_measurable {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) : MeasurableSet (supportLatticeExceptional μ R hR) :=
  MeasurableSet.iUnion (supportLatticeOverlap_measurable μ R hR)

theorem supportLatticeExceptional_null {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) : μ (supportLatticeExceptional μ R hR) = 0 :=
  measure_iUnion_null (fun k => supportLatticeOverlap_null μ C G hC hG hg hlower R hR k)

theorem cleanSupportCell_measurable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    MeasurableSet (cleanSupportCell μ R hR k z) :=
  (supportLatticeCell_closed μ R hR k z).measurableSet.diff
    (supportLatticeExceptional_measurable μ R hR)

theorem cleanSupportCell_disjoint {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) (z w : (supportLatticeNets μ R hR k).points) (hne : z ≠ w) :
    Disjoint (cleanSupportCell μ R hR k z) (cleanSupportCell μ R hR k w) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨hz, hgood⟩ ⟨hw, _⟩
  apply hgood
  exact mem_iUnion.mpr ⟨k, (mem_supportLatticeOverlap μ R hR k x).mpr ⟨z, w, hne, hz, hw⟩⟩

theorem cleanSupportCell_nested {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k t : ℕ) (z : (supportLatticeNets μ R hR (k + t)).points) :
    cleanSupportCell μ R hR (k + t) z ⊆
      cleanSupportCell μ R hR k (supportLatticeAncestor μ R hR k t z) :=
  sdiff_subset_sdiff_left (supportLatticeCell_nested μ R hR k t z)

theorem cleanSupportCell_cover {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (x : Ambient d) (hx : x ∈ μ.support) (hgood : x ∉ supportLatticeExceptional μ R hR) :
    ∃ z : (supportLatticeNets μ R hR k).points, x ∈ cleanSupportCell μ R hR k z := by
  obtain ⟨z, hz⟩ := supportLatticeCell_cover μ R hR k x hx
  exact ⟨z, hz, hgood⟩

theorem net_center_not_exceptional {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    (z : Ambient d) ∉ supportLatticeExceptional μ R hR := by
  intro hz
  obtain ⟨l, hl⟩ := mem_iUnion.mp hz
  by_cases hkl : k ≤ l
  · let w : (supportLatticeNets μ R hR (l + 0)).points :=
      ⟨z, supportLatticeNets_monotone μ R hR hkl z.property⟩
    have hd := supportLatticeOverlap_disjoint_deep_core μ R hR l 0 w
    exact Set.disjoint_left.mp hd hl (mem_ball_self (div_pos (latticeRadius_pos R hR (l + 0)) (by norm_num)))
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hkl))
    have hd := supportLatticeOverlap_disjoint_deep_core μ R hR l q z
    exact Set.disjoint_left.mp hd hl (mem_ball_self (div_pos (latticeRadius_pos R hR (l + q)) (by norm_num)))

theorem center_mem_cleanSupportCell {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : (z : Ambient d) ∈ cleanSupportCell μ R hR k z :=
  ⟨subset_closure (center_mem_netDescendants (supportLatticeNets μ R hR) k
    (supportLatticeCenter μ R hR k z) z.property), net_center_not_exceptional μ R hR k z⟩

theorem cleanSupportCell_closure {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    closure (cleanSupportCell μ R hR k z) = supportLatticeCell μ R hR k z := by
  apply le_antisymm
  · exact (supportLatticeCell_closed μ R hR k z).closure_subset_iff.mpr sdiff_subset
  · apply closure_mono
    rintro x hx
    refine ⟨subset_closure hx, ?_⟩
    obtain ⟨t, _, hxN, _⟩ := hx
    exact net_center_not_exceptional μ R hR (k + t) ⟨x, hxN⟩

theorem cleanSupportCell_measure_eq {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    μ (cleanSupportCell μ R hR k z) = μ (supportLatticeCell μ R hR k z) :=
  measure_sdiff_null (supportLatticeExceptional_null μ C G hC hG hg hlower R hR)

theorem cleanSupportCell_ae_unique {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) :
    ∀ᵐ x ∂μ, ∀ k : ℕ, ∃! z : (supportLatticeNets μ R hR k).points, x ∈ cleanSupportCell μ R hR k z := by
  have hgood : (supportLatticeExceptional μ R hR)ᶜ ∈ ae μ :=
    compl_mem_ae_iff.mpr (supportLatticeExceptional_null μ C G hC hG hg hlower R hR)
  filter_upwards [μ.support_mem_ae, hgood] with x hx hxgood
  intro k
  obtain ⟨z, hz⟩ := cleanSupportCell_cover μ R hR k x hx hxgood
  refine ⟨z, hz, ?_⟩
  intro w hw
  by_contra hne
  exact Set.disjoint_left.mp (cleanSupportCell_disjoint μ R hR k w z hne) hw hz

end

end RieszRectifiability

end OAI
