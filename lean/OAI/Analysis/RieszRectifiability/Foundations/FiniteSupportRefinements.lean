import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.CleanSupportPartition

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def supportDescendantsAt {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k t : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    Set (supportLatticeNets μ R hR (k + t)).points :=
  {w | supportLatticeAncestor μ R hR k t w = z}

theorem supportDescendantsAt_finite {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k t : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    (supportDescendantsAt μ R hR k t z).Finite := by
  have hf := separated_set_finite_inter_compact (supportLatticeNets μ R hR (k + t)).points
    (closedBall (z : Ambient d) (2 * latticeRadius R k)) (latticeRadius R (k + t))
    (latticeRadius_pos R hR (k + t)) (supportLatticeNets μ R hR (k + t)).separated
    (isCompact_closedBall _ _)
  have hpre := hf.preimage (f := fun w : (supportLatticeNets μ R hR (k + t)).points =>
    (w : Ambient d)) Subtype.val_injective.injOn
  apply hpre.subset
  intro w hw
  refine ⟨w.property, ?_⟩
  have hcenter : (w : Ambient d) ∈ supportLatticeCell μ R hR (k + t) w :=
    (center_mem_cleanSupportCell μ R hR (k + t) w).1
  have hp := supportLatticeCell_nested μ R hR k t w hcenter
  change supportLatticeAncestor μ R hR k t w = z at hw
  rw [hw] at hp
  exact (supportLatticeCell_bounds μ R hR k z).2 hp

theorem cleanSupportCell_eq_iUnion_descendants {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k t : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    cleanSupportCell μ R hR k z =
      ⋃ w ∈ supportDescendantsAt μ R hR k t z, cleanSupportCell μ R hR (k + t) w := by
  ext x
  constructor
  · intro hx
    have hxE := supportLatticeCell_subset_support μ R hR k z hx.1
    obtain ⟨w, hw⟩ := cleanSupportCell_cover μ R hR (k + t) x hxE hx.2
    have hp := cleanSupportCell_nested μ R hR k t w hw
    have hanc : supportLatticeAncestor μ R hR k t w = z := by
      by_contra hne
      exact Set.disjoint_left.mp (cleanSupportCell_disjoint μ R hR k _ z hne) hp hx
    exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨hanc, hw⟩⟩
  · intro hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    obtain ⟨hanc, hxw⟩ := mem_iUnion.mp hw
    have hp := cleanSupportCell_nested μ R hR k t w hxw
    change supportLatticeAncestor μ R hR k t w = z at hanc
    simpa only [hanc] using! hp

theorem cleanSupportCell_measure_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    ENNReal.ofReal ((latticeRadius R k / 8) ^ n / C) ≤ μ (cleanSupportCell μ R hR k z) ∧
      μ (cleanSupportCell μ R hR k z) ≤ ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := by
  rw [cleanSupportCell_measure_eq μ C G hC hG hg hlower R hR k z]
  exact supportLatticeCell_measure_bounds μ C G hg hlower R hR k hcore z

theorem cleanSupportCell_measure_pos_finite {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    0 < μ (cleanSupportCell μ R hR k z) ∧ μ (cleanSupportCell μ R hR k z) < ∞ := by
  have hb := cleanSupportCell_measure_bounds μ C G hC hG hg hlower R hR k hcore z
  exact ⟨(ENNReal.ofReal_pos.mpr (div_pos (pow_pos hcore.1 n) hC)).trans_le hb.1,
    hb.2.trans_lt ENNReal.ofReal_lt_top⟩

end

end RieszRectifiability

end OAI
