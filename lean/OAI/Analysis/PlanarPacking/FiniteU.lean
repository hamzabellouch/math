import OAI.Analysis.PlanarPacking.MatrixInverse
import OAI.Analysis.PlanarPacking.FiniteInverse
import OAI.Analysis.PlanarPacking.Indices
import OAI.Analysis.PlanarPacking.Certificate.WUCert7
import OAI.Analysis.PlanarPacking.Certificate.WUCert9
import OAI.Analysis.PlanarPacking.Certificate.WUCert12
import OAI.Analysis.PlanarPacking.Certificate.WUCert13
import OAI.Analysis.PlanarPacking.Certificate.WUCert15
import OAI.Analysis.PlanarPacking.Certificate.WUCert16
import OAI.Analysis.PlanarPacking.Certificate.WUCert19
import OAI.Analysis.PlanarPacking.Certificate.WUCert21
import OAI.Analysis.PlanarPacking.Certificate.WUCert24
import OAI.Analysis.PlanarPacking.Certificate.WUCert25
import OAI.Analysis.PlanarPacking.Certificate.WUCert27
import OAI.Analysis.PlanarPacking.Certificate.WUCert28
import OAI.Analysis.PlanarPacking.Certificate.WUCert31
import OAI.Analysis.PlanarPacking.Certificate.WUCert33
import OAI.Analysis.PlanarPacking.Certificate.WUCert36
import OAI.Analysis.PlanarPacking.Certificate.WUCert37
import OAI.Analysis.PlanarPacking.Certificate.WUCert39
import OAI.Analysis.PlanarPacking.Certificate.WUCert40
import OAI.Analysis.PlanarPacking.Certificate.WUCert43
import OAI.Analysis.PlanarPacking.Certificate.WUCert45
import OAI.Analysis.PlanarPacking.Certificate.WUCert48
import OAI.Analysis.PlanarPacking.Certificate.WUCert49
import OAI.Analysis.PlanarPacking.Certificate.WUCert51
import OAI.Analysis.PlanarPacking.Certificate.WUCert52
import OAI.Analysis.PlanarPacking.Certificate.WUCert55
import OAI.Analysis.PlanarPacking.Certificate.WUCert57
import OAI.Analysis.PlanarPacking.Certificate.WUCert60
import OAI.Analysis.PlanarPacking.Certificate.WUCert61
import OAI.Analysis.PlanarPacking.Certificate.WUCert63
import OAI.Analysis.PlanarPacking.Certificate.WUCert64
import OAI.Analysis.PlanarPacking.Certificate.WUCert67
import OAI.Analysis.PlanarPacking.Certificate.WUCert69
import OAI.Analysis.PlanarPacking.Certificate.WUCert72
import OAI.Analysis.PlanarPacking.Certificate.WUCert73
import OAI.Analysis.PlanarPacking.Certificate.WUCert75
import OAI.Analysis.PlanarPacking.Certificate.WUCert76
import OAI.Analysis.PlanarPacking.Certificate.WUCert79
import OAI.Analysis.PlanarPacking.Certificate.WUCert81
import OAI.Analysis.PlanarPacking.Certificate.WUCert84
import OAI.Analysis.PlanarPacking.Certificate.WUCert85
import OAI.Analysis.PlanarPacking.Certificate.WUCert87
import OAI.Analysis.PlanarPacking.Certificate.WUCert88
import OAI.Analysis.PlanarPacking.Certificate.WUCert91
import OAI.Analysis.PlanarPacking.Certificate.WUCert93
import OAI.Analysis.PlanarPacking.Certificate.WUCert96
import OAI.Analysis.PlanarPacking.Certificate.WUCert97
import OAI.Analysis.PlanarPacking.Certificate.WUCert99
import OAI.Analysis.PlanarPacking.Certificate.WUCert100

namespace OAI

/-!
# Exterior coupling in the finite interpolation system

Column estimates control the coupling between the central and exterior coordinates.
-/

namespace SharpPlanar.Numerical
open scoped BigOperators
noncomputable def Umat : Matrix (Fin 6) (Fin 48 × Fin 2) ℝ := fun i j => S (columnVector (eNode j.1) (decide (j.2.val=1))) (jNode i,jDeriv i)
lemma WUplus_column (j : Fin 48 × Fin 2) : ∑ i, |((Wplus*Umat) i j)| < (354:ℝ)/100 := by
  rcases j with ⟨n,d⟩
  fin_cases n
  · change ∑ i, |((Wplus*U7.umat) i d)| < (354:ℝ)/100
    exact (U7.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U9.umat) i d)| < (354:ℝ)/100
    exact (U9.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U12.umat) i d)| < (354:ℝ)/100
    exact (U12.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U13.umat) i d)| < (354:ℝ)/100
    exact (U13.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U15.umat) i d)| < (354:ℝ)/100
    exact (U15.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U16.umat) i d)| < (354:ℝ)/100
    exact (U16.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U19.umat) i d)| < (354:ℝ)/100
    exact (U19.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U21.umat) i d)| < (354:ℝ)/100
    exact (U21.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U24.umat) i d)| < (354:ℝ)/100
    exact (U24.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U25.umat) i d)| < (354:ℝ)/100
    exact (U25.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U27.umat) i d)| < (354:ℝ)/100
    exact (U27.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U28.umat) i d)| < (354:ℝ)/100
    exact (U28.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U31.umat) i d)| < (354:ℝ)/100
    exact (U31.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U33.umat) i d)| < (354:ℝ)/100
    exact (U33.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U36.umat) i d)| < (354:ℝ)/100
    exact (U36.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U37.umat) i d)| < (354:ℝ)/100
    exact (U37.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U39.umat) i d)| < (354:ℝ)/100
    exact (U39.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U40.umat) i d)| < (354:ℝ)/100
    exact (U40.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U43.umat) i d)| < (354:ℝ)/100
    exact (U43.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U45.umat) i d)| < (354:ℝ)/100
    exact (U45.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U48.umat) i d)| < (354:ℝ)/100
    exact (U48.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U49.umat) i d)| < (354:ℝ)/100
    exact (U49.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U51.umat) i d)| < (354:ℝ)/100
    exact (U51.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U52.umat) i d)| < (354:ℝ)/100
    exact (U52.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U55.umat) i d)| < (354:ℝ)/100
    exact (U55.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U57.umat) i d)| < (354:ℝ)/100
    exact (U57.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U60.umat) i d)| < (354:ℝ)/100
    exact (U60.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U61.umat) i d)| < (354:ℝ)/100
    exact (U61.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U63.umat) i d)| < (354:ℝ)/100
    exact (U63.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U64.umat) i d)| < (354:ℝ)/100
    exact (U64.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U67.umat) i d)| < (354:ℝ)/100
    exact (U67.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U69.umat) i d)| < (354:ℝ)/100
    exact (U69.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U72.umat) i d)| < (354:ℝ)/100
    exact (U72.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U73.umat) i d)| < (354:ℝ)/100
    exact (U73.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U75.umat) i d)| < (354:ℝ)/100
    exact (U75.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U76.umat) i d)| < (354:ℝ)/100
    exact (U76.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U79.umat) i d)| < (354:ℝ)/100
    exact (U79.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U81.umat) i d)| < (354:ℝ)/100
    exact (U81.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U84.umat) i d)| < (354:ℝ)/100
    exact (U84.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U85.umat) i d)| < (354:ℝ)/100
    exact (U85.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U87.umat) i d)| < (354:ℝ)/100
    exact (U87.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U88.umat) i d)| < (354:ℝ)/100
    exact (U88.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U91.umat) i d)| < (354:ℝ)/100
    exact (U91.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U93.umat) i d)| < (354:ℝ)/100
    exact (U93.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U96.umat) i d)| < (354:ℝ)/100
    exact (U96.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U97.umat) i d)| < (354:ℝ)/100
    exact (U97.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U99.umat) i d)| < (354:ℝ)/100
    exact (U99.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U100.umat) i d)| < (354:ℝ)/100
    exact (U100.wuplus_column d).trans_le (by norm_num)
lemma WUplus_norm : ‖(matrixL1 Wplus).comp (matrixL1 Umat)‖ < (354:ℝ)/100 := by
  rw [← matrixL1_mul]
  exact matrixL1_norm_lt WUplus_column
lemma inversePlus_U_norm : ‖inversePlusEquiv.toContinuousLinearMap.comp (matrixL1 Umat)‖ < (37:ℝ)/10 := by
  have hh := certified_inverse_comp_norm_le (matrixL1 Aplus) (matrixL1 Wplus) (matrixL1 Umat)
    (by norm_num : (1:ℝ)/1000 < 1) defectplus_norm.le
  change ‖inversePlusEquiv.toContinuousLinearMap.comp (matrixL1 Umat)‖ ≤ _ at hh
  apply hh.trans_lt
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-1/1000)).mpr
  nlinarith [WUplus_norm]
lemma WUminus_column (j : Fin 48 × Fin 2) : ∑ i, |((Wminus*Umat) i j)| < (73:ℝ)/100 := by
  rcases j with ⟨n,d⟩
  fin_cases n
  · change ∑ i, |((Wminus*U7.umat) i d)| < (73:ℝ)/100
    exact (U7.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U9.umat) i d)| < (73:ℝ)/100
    exact (U9.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U12.umat) i d)| < (73:ℝ)/100
    exact (U12.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U13.umat) i d)| < (73:ℝ)/100
    exact (U13.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U15.umat) i d)| < (73:ℝ)/100
    exact (U15.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U16.umat) i d)| < (73:ℝ)/100
    exact (U16.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U19.umat) i d)| < (73:ℝ)/100
    exact (U19.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U21.umat) i d)| < (73:ℝ)/100
    exact (U21.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U24.umat) i d)| < (73:ℝ)/100
    exact (U24.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U25.umat) i d)| < (73:ℝ)/100
    exact (U25.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U27.umat) i d)| < (73:ℝ)/100
    exact (U27.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U28.umat) i d)| < (73:ℝ)/100
    exact (U28.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U31.umat) i d)| < (73:ℝ)/100
    exact (U31.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U33.umat) i d)| < (73:ℝ)/100
    exact (U33.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U36.umat) i d)| < (73:ℝ)/100
    exact (U36.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U37.umat) i d)| < (73:ℝ)/100
    exact (U37.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U39.umat) i d)| < (73:ℝ)/100
    exact (U39.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U40.umat) i d)| < (73:ℝ)/100
    exact (U40.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U43.umat) i d)| < (73:ℝ)/100
    exact (U43.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U45.umat) i d)| < (73:ℝ)/100
    exact (U45.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U48.umat) i d)| < (73:ℝ)/100
    exact (U48.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U49.umat) i d)| < (73:ℝ)/100
    exact (U49.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U51.umat) i d)| < (73:ℝ)/100
    exact (U51.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U52.umat) i d)| < (73:ℝ)/100
    exact (U52.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U55.umat) i d)| < (73:ℝ)/100
    exact (U55.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U57.umat) i d)| < (73:ℝ)/100
    exact (U57.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U60.umat) i d)| < (73:ℝ)/100
    exact (U60.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U61.umat) i d)| < (73:ℝ)/100
    exact (U61.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U63.umat) i d)| < (73:ℝ)/100
    exact (U63.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U64.umat) i d)| < (73:ℝ)/100
    exact (U64.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U67.umat) i d)| < (73:ℝ)/100
    exact (U67.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U69.umat) i d)| < (73:ℝ)/100
    exact (U69.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U72.umat) i d)| < (73:ℝ)/100
    exact (U72.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U73.umat) i d)| < (73:ℝ)/100
    exact (U73.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U75.umat) i d)| < (73:ℝ)/100
    exact (U75.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U76.umat) i d)| < (73:ℝ)/100
    exact (U76.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U79.umat) i d)| < (73:ℝ)/100
    exact (U79.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U81.umat) i d)| < (73:ℝ)/100
    exact (U81.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U84.umat) i d)| < (73:ℝ)/100
    exact (U84.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U85.umat) i d)| < (73:ℝ)/100
    exact (U85.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U87.umat) i d)| < (73:ℝ)/100
    exact (U87.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U88.umat) i d)| < (73:ℝ)/100
    exact (U88.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U91.umat) i d)| < (73:ℝ)/100
    exact (U91.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U93.umat) i d)| < (73:ℝ)/100
    exact (U93.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U96.umat) i d)| < (73:ℝ)/100
    exact (U96.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U97.umat) i d)| < (73:ℝ)/100
    exact (U97.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U99.umat) i d)| < (73:ℝ)/100
    exact (U99.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U100.umat) i d)| < (73:ℝ)/100
    exact (U100.wuminus_column d).trans_le (by norm_num)
lemma WUminus_norm : ‖(matrixL1 Wminus).comp (matrixL1 Umat)‖ < (73:ℝ)/100 := by
  rw [← matrixL1_mul]
  exact matrixL1_norm_lt WUminus_column
lemma inverseMinus_U_norm : ‖inverseMinusEquiv.toContinuousLinearMap.comp (matrixL1 Umat)‖ < (37:ℝ)/10 := by
  have hh := certified_inverse_comp_norm_le (matrixL1 Aminus) (matrixL1 Wminus) (matrixL1 Umat)
    (by norm_num : (1:ℝ)/1000 < 1) defectminus_norm.le
  change ‖inverseMinusEquiv.toContinuousLinearMap.comp (matrixL1 Umat)‖ ≤ _ at hh
  apply hh.trans_lt
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-1/1000)).mpr
  nlinarith [WUminus_norm]
end SharpPlanar.Numerical

end OAI
