import OAI.Geometry.TranslativeCovering.DistinctCosets

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

namespace SourceMain
open Set Metric MeasureTheory Filter TranslativeCovering SourceParameters LocalizationRates
open scoped ENNReal Topology Classical
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

theorem main : TranslativeCovering.MainStatement := by
  obtain ⟨c,hc,n₁,hselect⟩ := BodySelection.uniform
  obtain ⟨n₂,hn₂⟩ := eventually_atTop.mp ((SourceScale.dimension hc).and LocalizationRates.dimension)
  refine ⟨c/2,by positivity,max n₁ n₂,?_⟩
  intro n hn
  have hdim := hn₂ n (le_trans (le_max_right _ _) hn)
  let : NeZero n := ⟨by omega⟩
  let : Fact (2≤n) := ⟨hdim.1.1⟩
  let e : SphericalLaw.Sphere n := ⟨(EuclideanSpace.basisFun (Fin n) ℝ) (0:Fin n),by
    simp only [mem_sphere_zero_iff_norm]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one _⟩
  let R := c*(n:ℝ)*Real.log n
  obtain ⟨U,hvol,hbad⟩ := hselect n (le_trans (le_max_left _ _) hn) e R hdim.1.2.1 le_rfl hdim.1.2.2
  let K := RandomBody.body (b n) 1 U
  have hb : 0<b n := by have ha := a_pos; dsimp [b]; positivity
  have hbody : ConvexBody K := RandomBody.body_isBody _ _ _ hb (by norm_num)
  have hKtop : volume K≠∞ := hbody.1.measure_ne_top
  have hK0 : volume K≠0 := ne_of_gt ((isOpen_interior.measure_pos volume hbody.2.2).trans_le (measure_mono interior_subset))
  have hP (P : PeriodicCover K) : ENNReal.ofReal R ≤ volume K*P.intensity := by
    apply le_of_not_gt
    intro hlt
    let := P.discrete
    let := P.fullrank
    let B := Module.Free.chooseBasis ℤ P.lattice
    let F := ZSpan.fundamentalDomain (B.ofZLatticeBasis ℝ)
    have hF : IsAddFundamentalDomain P.lattice F volume := ZLattice.isAddFundamentalDomain B volume
    have hF0 : volume F≠0 := ZSpan.measure_fundamentalDomain_ne_zero _
    have hFtop : volume F≠∞ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    have hFvol : ENNReal.ofReal (ZLattice.covolume P.lattice volume)=volume F := by
      rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF,Measure.real,ENNReal.ofReal_toReal hFtop]
    have hdensity : volume K*((Fintype.card (Fin P.m):ℝ≥0∞)/volume F)≤ENNReal.ofReal R := by
      simpa only [PeriodicCover.intensity,Fintype.card_fin,hFvol] using hlt.le
    have hno := AllLatticeExclusion.no_cover hdim.1.2.1 hdim.1.2.2 hdim.2.1 hdim.2.2.1 hdim.2.2.2.1
      hdim.2.2.2.2.1 hdim.2.2.2.2.2.1 hdim.2.2.2.2.2.2 U hvol hbad P.lattice
      P.offsets hF hF0 hFtop hdensity
    exact hno P.covers
  have hlower : ENNReal.ofReal R≤thetaT K := by
    rw [periodization_exact hbody,thetaPer]
    exact le_iInf fun P => hP P.val
  refine ⟨K,hbody,RandomBody.body_symm _ _ _,?_⟩
  apply lt_of_lt_of_le _ hlower
  have hRpos : 0<R := lt_of_lt_of_le (by norm_num) hdim.1.2.1
  have hhalf : c/2*(n:ℝ)*Real.log n=R/2 := by dsimp [R]; ring
  rw [hhalf]
  exact ENNReal.ofReal_lt_ofReal_iff hRpos |>.mpr (by linarith only [hRpos])
end SourceMain

theorem TranslativeCovering.main : TranslativeCovering.MainStatement := SourceMain.main

end OAI
