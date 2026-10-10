import OAI.Geometry.TranslativeCovering.PeriodicEquality

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering
open Set MeasureTheory Module
open scoped ENNReal Classical

structure PeriodicCover {n : ℕ} (K : Set (Space n)) where
  lattice : Submodule ℤ (Space n)
  discrete : DiscreteTopology lattice
  fullrank : IsZLattice ℝ lattice
  m : ℕ
  offsets : Fin m → Space n
  covers : ∀ y,∃ (i : Fin m) (l : lattice),y-offsets i-l.val∈K

noncomputable def PeriodicCover.intensity {n : ℕ} {K : Set (Space n)} (P : PeriodicCover K) : ℝ≥0∞ :=
  (P.m:ℝ≥0∞)/ENNReal.ofReal (ZLattice.covolume P.lattice volume)

noncomputable def thetaPerListed {n : ℕ} (K : Set (Space n)) : ℝ≥0∞ :=
  ⨅ P : PeriodicCover K,volume K*P.intensity

lemma PeriodicCover.cubic_le {n : ℕ} {K : Set (Space n)} (P : PeriodicCover K) (hK : IsCompact K) :
    cubicCenterInfimum K ≤ P.intensity := by
  let := P.discrete
  let := P.fullrank
  let b := Module.Free.chooseBasis ℤ P.lattice
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have hF : IsAddFundamentalDomain P.lattice F volume := ZLattice.isAddFundamentalDomain b volume
  have hF0 : volume F≠0 := ZSpan.measure_fundamentalDomain_ne_zero _
  have hFtop : volume F≠∞ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have he : ENNReal.ofReal (ZLattice.covolume P.lattice volume)=volume F := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF,Measure.real,ENNReal.ofReal_toReal hFtop]
  simpa only [PeriodicCover.intensity,he,Fintype.card_fin] using
    PeriodicEquality.cubic_le_periodic P.lattice P.offsets hF hF0 hFtop hK P.covers

noncomputable def CubicCover.toPeriodic {n : ℕ} {K : Set (Space n)} (P : CubicCover K) : PeriodicCover K where
  lattice := Submodule.span ℤ (Set.range (CubicLattice.basis n P.L P.positive))
  discrete := inferInstance
  fullrank := inferInstance
  m := P.centers.card
  offsets := fun i => ((Finset.equivFin P.centers).symm i).val
  covers := by
    intro y
    obtain ⟨i,l,hy⟩ := CubicLattice.covering P y
    refine ⟨Finset.equivFin P.centers i,l,?_⟩
    simpa only [Equiv.symm_apply_apply] using hy

lemma CubicCover.toPeriodic_intensity {n : ℕ} {K : Set (Space n)} (P : CubicCover K) :
    P.toPeriodic.intensity = (P.centers.card:ℝ≥0∞)/ENNReal.ofReal ((2*P.L)^n) := by
  dsimp only [PeriodicCover.intensity,CubicCover.toPeriodic]
  congr 1
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZSpan.isAddFundamentalDomain (CubicLattice.basis n P.L P.positive) volume),
    Measure.real,CubicLattice.volume_domain P.positive,ENNReal.ofReal_toReal ENNReal.ofReal_ne_top]

theorem periodization_all {n : ℕ} {K : Set (Space n)} (hK : ConvexBody K) :
    thetaT K = thetaPerListed K := by
  have hKtop : volume K≠∞ := hK.1.measure_ne_top
  have hK0 : volume K≠0 := ne_of_gt ((isOpen_interior.measure_pos volume hK.2.2).trans_le (measure_mono interior_subset))
  rw [periodization hK]
  apply le_antisymm
  · apply le_iInf
    intro P
    exact mul_le_mul le_rfl (P.cubic_le hK.1) bot_le bot_le
  · rw [cubicCenterInfimum,ENNReal.mul_iInf_of_ne hK0 hKtop]
    apply le_iInf
    intro P
    have hh := iInf_le (fun Q : PeriodicCover K => volume K*Q.intensity) P.toPeriodic
    simpa only [thetaPerListed,CubicCover.toPeriodic_intensity] using hh
end TranslativeCovering

end OAI
