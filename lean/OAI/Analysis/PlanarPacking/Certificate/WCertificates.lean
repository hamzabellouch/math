import OAI.Analysis.PlanarPacking.MatrixIntervals
import OAI.Analysis.PlanarPacking.Certificate.DEntries

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open IntegerIntervals
open scoped BigOperators
noncomputable def WplusInt : Matrix (Fin 6) (Fin 6) ℤ := ![![4159,4452,(-2003),(-10467),(-2421),(-1683)],
![2714,6573,1689,8258,104,(-335)],
![(-4675),4785,7003,(-13100),(-1355),(-1163)],
![36853,(-37142),27514,105973,1100,2012],
![57838,(-56941),36296,158623,29097,17293],
![(-4705),3589,(-3311),(-11932),(-2562),6919]]
noncomputable def Wplus : Matrix (Fin 6) (Fin 6) ℝ := fun i j => (WplusInt i j:ℝ)/10000
noncomputable def WplusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => RBox.rat (WplusInt i j) 10000
lemma WplusBox_contains (i j : Fin 6) : (WplusBox i j).Contains (Wplus i j) := RBox.contains_rat _ _ (by norm_num)
noncomputable def Aplus : Matrix (Fin 6) (Fin 6) ℝ := 1 - Dmat
noncomputable def AplusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => (RBox.rat (if i=j then 1 else 0) 1).add ((dEntries i j).neg)
lemma AplusBox_contains (i j : Fin 6) : (AplusBox i j).Contains (Aplus i j) := by
  have hi : (RBox.rat (if i=j then 1 else 0) 1).Contains ((1:Matrix (Fin 6) (Fin 6) ℝ) i j) := by
    by_cases h : i=j <;> simp [Matrix.one_apply,h] <;> convert RBox.contains_rat _ 1 (by norm_num) using 1 <;> norm_num
  simpa only [AplusBox,Aplus,Matrix.sub_apply,sub_eq_add_neg] using RBox.contains_add hi (RBox.neg_contains (dEntries_contains i j))
noncomputable def defectplusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => (RBox.rat (if i=j then 1 else 0) 1).add ((matrixMulBox WplusBox AplusBox i j).neg)
lemma defectplusBox_contains (i j : Fin 6) : (defectplusBox i j).Contains ((1-Wplus*Aplus) i j) := by
  have hi : (RBox.rat (if i=j then 1 else 0) 1).Contains ((1:Matrix (Fin 6) (Fin 6) ℝ) i j) := by
    by_cases h : i=j <;> simp [Matrix.one_apply,h] <;> convert RBox.contains_rat _ 1 (by norm_num) using 1 <;> norm_num
  simpa only [defectplusBox,Matrix.sub_apply,sub_eq_add_neg] using RBox.contains_add hi (RBox.neg_contains (matrixMulBox_contains WplusBox_contains AplusBox_contains i j))
lemma defectplus_column (j : Fin 6) : ∑ i, |((1-Wplus*Aplus) i j)| < (1:ℝ)/1000 := by
  have hh := column_bound_lt (u:=1) (v:=1000) (a:=defectplusBox) (by norm_num) defectplusBox_contains (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
lemma Wplus_column (j : Fin 6) : ∑ i, |Wplus i j| < (3084:ℝ)/100 := by
  apply column_bound_lt (u:=3084) (v:=100) (a:=WplusBox) (by norm_num) WplusBox_contains _ j
  intro k
  fin_cases k <;> decide +kernel
noncomputable def WminusInt : Matrix (Fin 6) (Fin 6) ℤ := ![![13265,(-1358),(-385),(-381),815,(-164)],
![616,10426,686,(-484),182,775],
![(-146),4,9842,215,267,179],
![(-2761),2483,(-958),5174,(-328),206],
![(-615),(-861),730,(-1388),5619,(-4370)],
![874,820,1148,(-431),905,11927]]
noncomputable def Wminus : Matrix (Fin 6) (Fin 6) ℝ := fun i j => (WminusInt i j:ℝ)/10000
noncomputable def WminusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => RBox.rat (WminusInt i j) 10000
lemma WminusBox_contains (i j : Fin 6) : (WminusBox i j).Contains (Wminus i j) := RBox.contains_rat _ _ (by norm_num)
noncomputable def Aminus : Matrix (Fin 6) (Fin 6) ℝ := 1 + Dmat
noncomputable def AminusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => (RBox.rat (if i=j then 1 else 0) 1).add ((dEntries i j))
lemma AminusBox_contains (i j : Fin 6) : (AminusBox i j).Contains (Aminus i j) := by
  have hi : (RBox.rat (if i=j then 1 else 0) 1).Contains ((1:Matrix (Fin 6) (Fin 6) ℝ) i j) := by
    by_cases h : i=j <;> simp [Matrix.one_apply,h] <;> convert RBox.contains_rat _ 1 (by norm_num) using 1 <;> norm_num
  simpa only [AminusBox,Aminus,Matrix.add_apply,add_zero] using RBox.contains_add hi ((dEntries_contains i j))
noncomputable def defectminusBox : Matrix (Fin 6) (Fin 6) RBox := fun i j => (RBox.rat (if i=j then 1 else 0) 1).add ((matrixMulBox WminusBox AminusBox i j).neg)
lemma defectminusBox_contains (i j : Fin 6) : (defectminusBox i j).Contains ((1-Wminus*Aminus) i j) := by
  have hi : (RBox.rat (if i=j then 1 else 0) 1).Contains ((1:Matrix (Fin 6) (Fin 6) ℝ) i j) := by
    by_cases h : i=j <;> simp [Matrix.one_apply,h] <;> convert RBox.contains_rat _ 1 (by norm_num) using 1 <;> norm_num
  simpa only [defectminusBox,Matrix.sub_apply,sub_eq_add_neg] using RBox.contains_add hi (RBox.neg_contains (matrixMulBox_contains WminusBox_contains AminusBox_contains i j))
lemma defectminus_column (j : Fin 6) : ∑ i, |((1-Wminus*Aminus) i j)| < (1:ℝ)/1000 := by
  have hh := column_bound_lt (u:=1) (v:=1000) (a:=defectminusBox) (by norm_num) defectminusBox_contains (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
lemma Wminus_column (j : Fin 6) : ∑ i, |Wminus i j| < (183:ℝ)/100 := by
  apply column_bound_lt (u:=183) (v:=100) (a:=WminusBox) (by norm_num) WminusBox_contains _ j
  intro k
  fin_cases k <;> decide +kernel
end SharpPlanar.Numerical

end OAI
