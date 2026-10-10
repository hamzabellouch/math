import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.CriticalRescaleH1

namespace OAI

section
section
section

section
noncomputable section
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set MeasureTheory ComplexMatrix
open scoped Manifold ContDiff SchwartzMap ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [MeasurableSpace X] [BorelSpace X] in
lemma pairLinear_compact (p : A.centers) (a : smoothForms X 2) :
    HasCompactSupport (pairLinear A J α ht D hD p a : Space → ScalarPair.F) := by
  have h₀ := ((scalar_smooth_compact A J α ht D hD p a.val a.property 2).2).comp_left
    (map_zero (ScalarPair.inject 0))
  have h₁ := ((scalar_smooth_compact A J α ht D hD p a.val a.property 3).2).comp_left
    (map_zero (ScalarPair.inject 1))
  exact h₀.add h₁

lemma pair_energy_L4_bound (p : A.centers) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a : antiPre A J α hs ht,
      ‖(pairLinear A J α ht D hD p a.val).toLp 4 (volume : Measure Space)‖ ≤
        C * ‖antiToEnergy A J α hs ht a‖ := by
  obtain ⟨C,hC,hb⟩ := ScalarPair.critical_sobolev_jet
  let T := energyToScalarJet A J α hs ht D hD p
  refine ⟨C*‖T‖,mul_nonneg hC (norm_nonneg T),fun a => ?_⟩
  have hj : ScalarPair.jet (pairLinear A J α ht D hD p a.val) = T (antiToEnergy A J α hs ht a) :=
    (energyToScalarJet_smooth A J α hs ht D hD p a).symm
  calc
    _ ≤ C * ‖ScalarPair.jet (pairLinear A J α ht D hD p a.val)‖ :=
      hb _ (pairLinear_compact A J α ht D hD p a.val)
    _ ≤ C * (‖T‖ * ‖antiToEnergy A J α hs ht a‖) := by
      rw [hj]
      exact mul_le_mul_of_nonneg_left (T.le_opNorm _) hC
    _ = _ := by ring

lemma component_energy_L4_bound (p : A.centers) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a : antiPre A J α hs ht, ∀ j : Fin 2,
      ‖(realComponent (realPairSchwartz A J α ht D hD p a.val) j).toLp 4 (volume : Measure Space)‖ ≤
        C * ‖antiToEnergy A J α hs ht a‖ := by
  obtain ⟨C,hC,hb⟩ := pair_energy_L4_bound A J α hs ht D hD p
  refine ⟨C,hC,fun a j => ?_⟩
  apply le_trans _ (hb a)
  rw [SchwartzMap.norm_toLp,SchwartzMap.norm_toLp]
  apply ENNReal.toReal_mono ((pairLinear A J α ht D hD p a.val).memLp 4 volume).eLpNorm_ne_top
  apply eLpNorm_mono
    ((realComponent (realPairSchwartz A J α ht D hD p a.val) j).memLp 4 volume).aestronglyMeasurable
  intro x
  change |((pairLinear A J α ht D hD p a.val) x j).re| ≤
    ‖(pairLinear A J α ht D hD p a.val) x‖
  exact (Complex.abs_re_le_norm _).trans (PiLp.norm_apply_le _ _)

def energyToL4 (p : A.centers) :
    antiEnergy A J α hs ht →L[ℝ] Lp ScalarPair.F 4 (volume : Measure Space) :=
  ((SchwartzMap.toLpCLM ℝ ScalarPair.F 4 volume).toLinearMap.comp
    ((pairLinear A J α ht D hD p).comp (antiPre A J α hs ht).subtype)).extendOfNorm
    (antiToEnergy A J α hs ht)

lemma energyToL4_smooth (p : A.centers) (a : antiPre A J α hs ht) :
    energyToL4 A J α hs ht D hD p (antiToEnergy A J α hs ht a) =
      (pairLinear A J α ht D hD p a.val).toLp 4 volume := by
  apply LinearMap.extendOfNorm_eq (antiToEnergy_dense A J α hs ht)
  obtain ⟨C,-,hC⟩ := pair_energy_L4_bound A J α hs ht D hD p
  exact ⟨C,hC⟩
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
