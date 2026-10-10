import OAI.Analysis.PlanarPacking.Certificate.WCertificates
import OAI.Analysis.PlanarPacking.Certificate.UMoments99

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical.U99
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨99,by norm_num [residues]⟩
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
noncomputable def entry0_0 : RBox := ⟨17054153344218146115296913,19920493832963153098644698⟩
lemma entry0_0_contains : entry0_0.Contains (umat 0 0) := by
  have h0 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) false false cm99_1_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) false true cm99_1_0_1.contains
  have hh := S_column_value_contains (m:=node1) h0
  change entry0_0.Contains (S (columnVector node false) (node1,false))
  convert hh using 1
  decide +kernel
noncomputable def entry3_0 : RBox := ⟨(-7032495784590371389638405),9907216631776212413538007⟩
lemma entry3_0_contains : entry3_0.Contains (umat 3 0) := by
  have h0 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) false false cm99_1_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) false true cm99_1_0_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  change entry3_0.Contains (S (columnVector node false) (node1,true))
  convert hh using 1
  decide +kernel
noncomputable def entry1_0 : RBox := ⟨44284890090173736410714602,44711878122094923968391024⟩
lemma entry1_0_contains : entry1_0.Contains (umat 1 0) := by
  have h0 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) false false cm99_3_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) false true cm99_3_0_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  change entry1_0.Contains (S (columnVector node false) (node3,false))
  convert hh using 1
  decide +kernel
noncomputable def entry4_0 : RBox := ⟨64865958846679133205546001,67044257184185437692686868⟩
lemma entry4_0_contains : entry4_0.Contains (umat 4 0) := by
  have h0 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) false false cm99_3_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) false true cm99_3_0_1.contains
  have hh := S_column_derivative_contains (m:=node3) h0 h1
  change entry4_0.Contains (S (columnVector node false) (node3,true))
  convert hh using 1
  decide +kernel
noncomputable def entry2_0 : RBox := ⟨(-25797072134934088623003537),(-25717568594770032992344542)⟩
lemma entry2_0_contains : entry2_0.Contains (umat 2 0) := by
  have h0 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) false false cm99_4_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) false true cm99_4_0_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  change entry2_0.Contains (S (columnVector node false) (node4,false))
  convert hh using 1
  decide +kernel
noncomputable def entry5_0 : RBox := ⟨101238765297876400652392955,101765305944157033321839773⟩
lemma entry5_0_contains : entry5_0.Contains (umat 5 0) := by
  have h0 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) false false cm99_4_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) false true cm99_4_0_1.contains
  have hh := S_column_derivative_contains (m:=node4) h0 h1
  change entry5_0.Contains (S (columnVector node false) (node4,true))
  convert hh using 1
  decide +kernel
noncomputable def entry0_1 : RBox := ⟨(-1799475741262405681133375653),(-1791156051417881422127050140)⟩
lemma entry0_1_contains : entry0_1.Contains (umat 0 1) := by
  have h0 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) true false cm99_1_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) true true cm99_1_1_1.contains
  have hh := S_column_value_contains (m:=node1) h0
  change entry0_1.Contains (S (columnVector node true) (node1,false))
  convert hh using 1
  decide +kernel
noncomputable def entry3_1 : RBox := ⟨(-191253504081492375884200029),(-142141461603194799729733828)⟩
lemma entry3_1_contains : entry3_1.Contains (umat 3 1) := by
  have h0 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) true false cm99_1_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) true true cm99_1_1_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  change entry3_1.Contains (S (columnVector node true) (node1,true))
  convert hh using 1
  decide +kernel
noncomputable def entry1_1 : RBox := ⟨(-4270785954148737438115081601),(-4269523925969082705075490567)⟩
lemma entry1_1_contains : entry1_1.Contains (umat 1 1) := by
  have h0 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) true false cm99_3_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) true true cm99_3_1_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  change entry1_1.Contains (S (columnVector node true) (node3,false))
  convert hh using 1
  decide +kernel
noncomputable def entry4_1 : RBox := ⟨(-6449003221571201814028171068),(-6442563045446121378844000521)⟩
lemma entry4_1_contains : entry4_1.Contains (umat 4 1) := by
  have h0 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) true false cm99_3_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) true true cm99_3_1_1.contains
  have hh := S_column_derivative_contains (m:=node3) h0 h1
  change entry4_1.Contains (S (columnVector node true) (node3,true))
  convert hh using 1
  decide +kernel
noncomputable def entry2_1 : RBox := ⟨2480124794031989901696434847,2480359606821274880440530557⟩
lemma entry2_1_contains : entry2_1.Contains (umat 2 1) := by
  have h0 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) true false cm99_4_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) true true cm99_4_1_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  change entry2_1.Contains (S (columnVector node true) (node4,false))
  convert hh using 1
  decide +kernel
noncomputable def entry5_1 : RBox := ⟨(-9487305878114569505909443245),(-9485749779782296144196224326)⟩
lemma entry5_1_contains : entry5_1.Contains (umat 5 1) := by
  have h0 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) true false cm99_4_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) true true cm99_4_1_1.contains
  have hh := S_column_derivative_contains (m:=node4) h0 h1
  change entry5_1.Contains (S (columnVector node true) (node4,true))
  convert hh using 1
  decide +kernel
noncomputable def entries : Matrix (Fin 6) (Fin 2) RBox := ![![entry0_0,entry0_1],
![entry1_0,entry1_1],
![entry2_0,entry2_1],
![entry3_0,entry3_1],
![entry4_0,entry4_1],
![entry5_0,entry5_1]]
lemma entries_contains (i : Fin 6) (j : Fin 2) : (entries i j).Contains (umat i j) := by
  fin_cases i <;> fin_cases j
  · exact entry0_0_contains
  · exact entry0_1_contains
  · exact entry1_0_contains
  · exact entry1_1_contains
  · exact entry2_0_contains
  · exact entry2_1_contains
  · exact entry3_0_contains
  · exact entry3_1_contains
  · exact entry4_0_contains
  · exact entry4_1_contains
  · exact entry5_0_contains
  · exact entry5_1_contains
noncomputable def wuplusBox := matrixMulBox WplusBox entries
lemma wuplus_contains (i : Fin 6) (j : Fin 2) : (wuplusBox i j).Contains ((Wplus*umat) i j) := matrixMulBox_contains WplusBox_contains entries_contains i j
lemma wuplus_column (j : Fin 2) : ∑ i, |((Wplus*umat) i j)| < (25:ℝ)/100 := by
  have hh := column_bound_lt (u:=25) (v:=100) (a:=wuplusBox) (by norm_num) wuplus_contains (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
noncomputable def wuminusBox := matrixMulBox WminusBox entries
lemma wuminus_contains (i : Fin 6) (j : Fin 2) : (wuminusBox i j).Contains ((Wminus*umat) i j) := matrixMulBox_contains WminusBox_contains entries_contains i j
lemma wuminus_column (j : Fin 2) : ∑ i, |((Wminus*umat) i j)| < (17:ℝ)/100 := by
  have hh := column_bound_lt (u:=17) (v:=100) (a:=wuminusBox) (by norm_num) wuminus_contains (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
end SharpPlanar.Numerical.U99

end OAI
