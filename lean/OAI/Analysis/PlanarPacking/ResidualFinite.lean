import OAI.Analysis.PlanarPacking.Certificate.Residual1
import OAI.Analysis.PlanarPacking.Certificate.Residual3
import OAI.Analysis.PlanarPacking.Certificate.Residual4
import OAI.Analysis.PlanarPacking.Certificate.Residual7
import OAI.Analysis.PlanarPacking.Certificate.Residual9
import OAI.Analysis.PlanarPacking.Certificate.Residual12
import OAI.Analysis.PlanarPacking.Certificate.Residual13
import OAI.Analysis.PlanarPacking.Certificate.Residual15
import OAI.Analysis.PlanarPacking.Certificate.Residual16
import OAI.Analysis.PlanarPacking.Certificate.Residual19
import OAI.Analysis.PlanarPacking.Certificate.Residual21
import OAI.Analysis.PlanarPacking.Certificate.Residual24
import OAI.Analysis.PlanarPacking.Certificate.Residual25
import OAI.Analysis.PlanarPacking.Certificate.Residual27
import OAI.Analysis.PlanarPacking.Certificate.Residual28
import OAI.Analysis.PlanarPacking.Certificate.Residual31
import OAI.Analysis.PlanarPacking.Certificate.Residual33
import OAI.Analysis.PlanarPacking.Certificate.Residual36
import OAI.Analysis.PlanarPacking.Certificate.Residual37
import OAI.Analysis.PlanarPacking.Certificate.Residual39
import OAI.Analysis.PlanarPacking.Certificate.Residual40
import OAI.Analysis.PlanarPacking.Certificate.Residual43
import OAI.Analysis.PlanarPacking.Certificate.Residual45
import OAI.Analysis.PlanarPacking.Certificate.Residual48
import OAI.Analysis.PlanarPacking.Certificate.Residual49
import OAI.Analysis.PlanarPacking.Certificate.Residual51
import OAI.Analysis.PlanarPacking.Certificate.Residual52
import OAI.Analysis.PlanarPacking.Certificate.Residual55
import OAI.Analysis.PlanarPacking.Certificate.Residual57
import OAI.Analysis.PlanarPacking.Certificate.Residual60
import OAI.Analysis.PlanarPacking.Certificate.Residual61
import OAI.Analysis.PlanarPacking.Certificate.Residual63
import OAI.Analysis.PlanarPacking.Certificate.Residual64
import OAI.Analysis.PlanarPacking.Certificate.Residual67
import OAI.Analysis.PlanarPacking.Certificate.Residual69
import OAI.Analysis.PlanarPacking.Certificate.Residual72
import OAI.Analysis.PlanarPacking.Certificate.Residual73
import OAI.Analysis.PlanarPacking.Certificate.Residual75
import OAI.Analysis.PlanarPacking.Certificate.Residual76
import OAI.Analysis.PlanarPacking.Certificate.Residual79
import OAI.Analysis.PlanarPacking.Certificate.Residual81
import OAI.Analysis.PlanarPacking.Certificate.Residual84
import OAI.Analysis.PlanarPacking.Certificate.Residual85
import OAI.Analysis.PlanarPacking.Certificate.Residual87
import OAI.Analysis.PlanarPacking.Certificate.Residual88
import OAI.Analysis.PlanarPacking.Certificate.Residual91
import OAI.Analysis.PlanarPacking.Certificate.Residual93
import OAI.Analysis.PlanarPacking.Certificate.Residual96
import OAI.Analysis.PlanarPacking.Certificate.Residual97
import OAI.Analysis.PlanarPacking.Certificate.Residual99
import OAI.Analysis.PlanarPacking.Certificate.Residual100

namespace OAI

namespace SharpPlanar
open Numerical
open scoped BigOperators
lemma residual_finite_central_0 (i : Fin 6) : |tableResidual false (centralIndex i)|<(1:ℝ)/10^9 := by
  fin_cases i
  · exact Residual1.bound0_0
  · exact Residual3.bound0_0
  · exact Residual4.bound0_0
  · exact Residual1.bound0_1
  · exact Residual3.bound0_1
  · exact Residual4.bound0_1
lemma residual_finite_exterior_0 (i : Fin 48 × Fin 2) : |tableResidual false (exteriorIndex i)|<(1:ℝ)/10^9 := by
  rcases i with ⟨i,d⟩
  fin_cases i
  · fin_cases d
    · exact Residual7.bound0_0
    · exact Residual7.bound0_1
  · fin_cases d
    · exact Residual9.bound0_0
    · exact Residual9.bound0_1
  · fin_cases d
    · exact Residual12.bound0_0
    · exact Residual12.bound0_1
  · fin_cases d
    · exact Residual13.bound0_0
    · exact Residual13.bound0_1
  · fin_cases d
    · exact Residual15.bound0_0
    · exact Residual15.bound0_1
  · fin_cases d
    · exact Residual16.bound0_0
    · exact Residual16.bound0_1
  · fin_cases d
    · exact Residual19.bound0_0
    · exact Residual19.bound0_1
  · fin_cases d
    · exact Residual21.bound0_0
    · exact Residual21.bound0_1
  · fin_cases d
    · exact Residual24.bound0_0
    · exact Residual24.bound0_1
  · fin_cases d
    · exact Residual25.bound0_0
    · exact Residual25.bound0_1
  · fin_cases d
    · exact Residual27.bound0_0
    · exact Residual27.bound0_1
  · fin_cases d
    · exact Residual28.bound0_0
    · exact Residual28.bound0_1
  · fin_cases d
    · exact Residual31.bound0_0
    · exact Residual31.bound0_1
  · fin_cases d
    · exact Residual33.bound0_0
    · exact Residual33.bound0_1
  · fin_cases d
    · exact Residual36.bound0_0
    · exact Residual36.bound0_1
  · fin_cases d
    · exact Residual37.bound0_0
    · exact Residual37.bound0_1
  · fin_cases d
    · exact Residual39.bound0_0
    · exact Residual39.bound0_1
  · fin_cases d
    · exact Residual40.bound0_0
    · exact Residual40.bound0_1
  · fin_cases d
    · exact Residual43.bound0_0
    · exact Residual43.bound0_1
  · fin_cases d
    · exact Residual45.bound0_0
    · exact Residual45.bound0_1
  · fin_cases d
    · exact Residual48.bound0_0
    · exact Residual48.bound0_1
  · fin_cases d
    · exact Residual49.bound0_0
    · exact Residual49.bound0_1
  · fin_cases d
    · exact Residual51.bound0_0
    · exact Residual51.bound0_1
  · fin_cases d
    · exact Residual52.bound0_0
    · exact Residual52.bound0_1
  · fin_cases d
    · exact Residual55.bound0_0
    · exact Residual55.bound0_1
  · fin_cases d
    · exact Residual57.bound0_0
    · exact Residual57.bound0_1
  · fin_cases d
    · exact Residual60.bound0_0
    · exact Residual60.bound0_1
  · fin_cases d
    · exact Residual61.bound0_0
    · exact Residual61.bound0_1
  · fin_cases d
    · exact Residual63.bound0_0
    · exact Residual63.bound0_1
  · fin_cases d
    · exact Residual64.bound0_0
    · exact Residual64.bound0_1
  · fin_cases d
    · exact Residual67.bound0_0
    · exact Residual67.bound0_1
  · fin_cases d
    · exact Residual69.bound0_0
    · exact Residual69.bound0_1
  · fin_cases d
    · exact Residual72.bound0_0
    · exact Residual72.bound0_1
  · fin_cases d
    · exact Residual73.bound0_0
    · exact Residual73.bound0_1
  · fin_cases d
    · exact Residual75.bound0_0
    · exact Residual75.bound0_1
  · fin_cases d
    · exact Residual76.bound0_0
    · exact Residual76.bound0_1
  · fin_cases d
    · exact Residual79.bound0_0
    · exact Residual79.bound0_1
  · fin_cases d
    · exact Residual81.bound0_0
    · exact Residual81.bound0_1
  · fin_cases d
    · exact Residual84.bound0_0
    · exact Residual84.bound0_1
  · fin_cases d
    · exact Residual85.bound0_0
    · exact Residual85.bound0_1
  · fin_cases d
    · exact Residual87.bound0_0
    · exact Residual87.bound0_1
  · fin_cases d
    · exact Residual88.bound0_0
    · exact Residual88.bound0_1
  · fin_cases d
    · exact Residual91.bound0_0
    · exact Residual91.bound0_1
  · fin_cases d
    · exact Residual93.bound0_0
    · exact Residual93.bound0_1
  · fin_cases d
    · exact Residual96.bound0_0
    · exact Residual96.bound0_1
  · fin_cases d
    · exact Residual97.bound0_0
    · exact Residual97.bound0_1
  · fin_cases d
    · exact Residual99.bound0_0
    · exact Residual99.bound0_1
  · fin_cases d
    · exact Residual100.bound0_0
    · exact Residual100.bound0_1
lemma residual_finite_central_1 (i : Fin 6) : |tableResidual true (centralIndex i)|<(1:ℝ)/10^9 := by
  fin_cases i
  · exact Residual1.bound1_0
  · exact Residual3.bound1_0
  · exact Residual4.bound1_0
  · exact Residual1.bound1_1
  · exact Residual3.bound1_1
  · exact Residual4.bound1_1
lemma residual_finite_exterior_1 (i : Fin 48 × Fin 2) : |tableResidual true (exteriorIndex i)|<(1:ℝ)/10^9 := by
  rcases i with ⟨i,d⟩
  fin_cases i
  · fin_cases d
    · exact Residual7.bound1_0
    · exact Residual7.bound1_1
  · fin_cases d
    · exact Residual9.bound1_0
    · exact Residual9.bound1_1
  · fin_cases d
    · exact Residual12.bound1_0
    · exact Residual12.bound1_1
  · fin_cases d
    · exact Residual13.bound1_0
    · exact Residual13.bound1_1
  · fin_cases d
    · exact Residual15.bound1_0
    · exact Residual15.bound1_1
  · fin_cases d
    · exact Residual16.bound1_0
    · exact Residual16.bound1_1
  · fin_cases d
    · exact Residual19.bound1_0
    · exact Residual19.bound1_1
  · fin_cases d
    · exact Residual21.bound1_0
    · exact Residual21.bound1_1
  · fin_cases d
    · exact Residual24.bound1_0
    · exact Residual24.bound1_1
  · fin_cases d
    · exact Residual25.bound1_0
    · exact Residual25.bound1_1
  · fin_cases d
    · exact Residual27.bound1_0
    · exact Residual27.bound1_1
  · fin_cases d
    · exact Residual28.bound1_0
    · exact Residual28.bound1_1
  · fin_cases d
    · exact Residual31.bound1_0
    · exact Residual31.bound1_1
  · fin_cases d
    · exact Residual33.bound1_0
    · exact Residual33.bound1_1
  · fin_cases d
    · exact Residual36.bound1_0
    · exact Residual36.bound1_1
  · fin_cases d
    · exact Residual37.bound1_0
    · exact Residual37.bound1_1
  · fin_cases d
    · exact Residual39.bound1_0
    · exact Residual39.bound1_1
  · fin_cases d
    · exact Residual40.bound1_0
    · exact Residual40.bound1_1
  · fin_cases d
    · exact Residual43.bound1_0
    · exact Residual43.bound1_1
  · fin_cases d
    · exact Residual45.bound1_0
    · exact Residual45.bound1_1
  · fin_cases d
    · exact Residual48.bound1_0
    · exact Residual48.bound1_1
  · fin_cases d
    · exact Residual49.bound1_0
    · exact Residual49.bound1_1
  · fin_cases d
    · exact Residual51.bound1_0
    · exact Residual51.bound1_1
  · fin_cases d
    · exact Residual52.bound1_0
    · exact Residual52.bound1_1
  · fin_cases d
    · exact Residual55.bound1_0
    · exact Residual55.bound1_1
  · fin_cases d
    · exact Residual57.bound1_0
    · exact Residual57.bound1_1
  · fin_cases d
    · exact Residual60.bound1_0
    · exact Residual60.bound1_1
  · fin_cases d
    · exact Residual61.bound1_0
    · exact Residual61.bound1_1
  · fin_cases d
    · exact Residual63.bound1_0
    · exact Residual63.bound1_1
  · fin_cases d
    · exact Residual64.bound1_0
    · exact Residual64.bound1_1
  · fin_cases d
    · exact Residual67.bound1_0
    · exact Residual67.bound1_1
  · fin_cases d
    · exact Residual69.bound1_0
    · exact Residual69.bound1_1
  · fin_cases d
    · exact Residual72.bound1_0
    · exact Residual72.bound1_1
  · fin_cases d
    · exact Residual73.bound1_0
    · exact Residual73.bound1_1
  · fin_cases d
    · exact Residual75.bound1_0
    · exact Residual75.bound1_1
  · fin_cases d
    · exact Residual76.bound1_0
    · exact Residual76.bound1_1
  · fin_cases d
    · exact Residual79.bound1_0
    · exact Residual79.bound1_1
  · fin_cases d
    · exact Residual81.bound1_0
    · exact Residual81.bound1_1
  · fin_cases d
    · exact Residual84.bound1_0
    · exact Residual84.bound1_1
  · fin_cases d
    · exact Residual85.bound1_0
    · exact Residual85.bound1_1
  · fin_cases d
    · exact Residual87.bound1_0
    · exact Residual87.bound1_1
  · fin_cases d
    · exact Residual88.bound1_0
    · exact Residual88.bound1_1
  · fin_cases d
    · exact Residual91.bound1_0
    · exact Residual91.bound1_1
  · fin_cases d
    · exact Residual93.bound1_0
    · exact Residual93.bound1_1
  · fin_cases d
    · exact Residual96.bound1_0
    · exact Residual96.bound1_1
  · fin_cases d
    · exact Residual97.bound1_0
    · exact Residual97.bound1_1
  · fin_cases d
    · exact Residual99.bound1_0
    · exact Residual99.bound1_1
  · fin_cases d
    · exact Residual100.bound1_0
    · exact Residual100.bound1_1
lemma residual_finite_coordinate (a : Bool) (i : FiniteIndex) :
    |tableResidual a (finiteIndex i)|<(1:ℝ)/10^9 := by
  cases a <;> rcases i with i | i
  · exact residual_finite_central_0 i
  · exact residual_finite_exterior_0 i
  · exact residual_finite_central_1 i
  · exact residual_finite_exterior_1 i
lemma residual_finite_bound (a : Bool) : ‖RF (tableResidual a)‖ < (11:ℝ)/10^8 := by
  rw [l1Finite_norm]
  change (∑ i : FiniteIndex, |tableResidual a (finiteIndex i)|)<_
  calc
    _<(∑ i : FiniteIndex, (1:ℝ)/10^9) := by
      apply Finset.sum_lt_sum (fun i _ => (residual_finite_coordinate a i).le)
      exact ⟨Sum.inl 0,Finset.mem_univ _,residual_finite_coordinate a (Sum.inl 0)⟩
    _<_ := by norm_num [FiniteIndex,Fintype.card_sum,Fintype.card_prod]
end SharpPlanar

end OAI
