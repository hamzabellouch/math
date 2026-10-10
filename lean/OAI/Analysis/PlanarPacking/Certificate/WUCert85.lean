import OAI.Analysis.PlanarPacking.Certificate.WCertificates
import OAI.Analysis.PlanarPacking.Certificate.UMoments85

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical.U85
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨85,by norm_num [residues]⟩
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
noncomputable def entry0_0 : RBox := ⟨25231071068719851404578709,25255349313996943168416177⟩
lemma entry0_0_contains : entry0_0.Contains (umat 0 0) := by
  have h0 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) false false cm85_1_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) false true cm85_1_0_1.contains
  have hh := S_column_value_contains (m:=node1) h0
  change entry0_0.Contains (S (columnVector node false) (node1,false))
  convert hh using 1
  decide +kernel
noncomputable def entry3_0 : RBox := ⟨1753391962944408970701623,1896310424620706477456032⟩
lemma entry3_0_contains : entry3_0.Contains (umat 3 0) := by
  have h0 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) false false cm85_1_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) false true cm85_1_0_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  change entry3_0.Contains (S (columnVector node false) (node1,true))
  convert hh using 1
  decide +kernel
noncomputable def entry1_0 : RBox := ⟨61001930332276108877402118,61005550505355022533736532⟩
lemma entry1_0_contains : entry1_0.Contains (umat 1 0) := by
  have h0 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) false false cm85_3_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) false true cm85_3_0_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  change entry1_0.Contains (S (columnVector node false) (node3,false))
  convert hh using 1
  decide +kernel
noncomputable def entry4_0 : RBox := ⟨89847625010406581505911855,89866160671803456106707375⟩
lemma entry4_0_contains : entry4_0.Contains (umat 4 0) := by
  have h0 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) false false cm85_3_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) false true cm85_3_0_1.contains
  have hh := S_column_derivative_contains (m:=node3) h0 h1
  change entry4_0.Contains (S (columnVector node false) (node3,true))
  convert hh using 1
  decide +kernel
noncomputable def entry2_0 : RBox := ⟨(-35260899591246753688092550),(-35260216953111999671585543)⟩
lemma entry2_0_contains : entry2_0.Contains (umat 2 0) := by
  have h0 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) false false cm85_4_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) false true cm85_4_0_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  change entry2_0.Contains (S (columnVector node false) (node4,false))
  convert hh using 1
  decide +kernel
noncomputable def entry5_0 : RBox := ⟨140390505058273719270312734,140395008452464428675301805⟩
lemma entry5_0_contains : entry5_0.Contains (umat 5 0) := by
  have h0 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) false false cm85_4_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) false true cm85_4_0_1.contains
  have hh := S_column_derivative_contains (m:=node4) h0 h1
  change entry5_0.Contains (S (columnVector node false) (node4,true))
  convert hh using 1
  decide +kernel
noncomputable def entry0_1 : RBox := ⟨(-2097788512945288765066997904),(-2097718264417475033662753142)⟩
lemma entry0_1_contains : entry0_1.Contains (umat 0 1) := by
  have h0 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) true false cm85_1_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) true true cm85_1_1_1.contains
  have hh := S_column_value_contains (m:=node1) h0
  change entry0_1.Contains (S (columnVector node true) (node1,false))
  convert hh using 1
  decide +kernel
noncomputable def entry3_1 : RBox := ⟨(-189596642125929614652028869),(-189183545437274374819625980)⟩
lemma entry3_1_contains : entry3_1.Contains (umat 3 1) := by
  have h0 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) true false cm85_1_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) true true cm85_1_1_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  change entry3_1.Contains (S (columnVector node true) (node1,true))
  convert hh using 1
  decide +kernel
noncomputable def entry1_1 : RBox := ⟨(-4999579181483676639568768056),(-4999568494333555214254380621)⟩
lemma entry1_1_contains : entry1_1.Contains (umat 1 1) := by
  have h0 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) true false cm85_3_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) true true cm85_3_1_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  change entry1_1.Contains (S (columnVector node true) (node3,false))
  convert hh using 1
  decide +kernel
noncomputable def entry4_1 : RBox := ⟨(-7523584424665376201239346106),(-7523529702625845941147875745)⟩
lemma entry4_1_contains : entry4_1.Contains (umat 4 1) := by
  have h0 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) true false cm85_3_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) true true cm85_3_1_1.contains
  have hh := S_column_derivative_contains (m:=node3) h0 h1
  change entry4_1.Contains (S (columnVector node true) (node3,true))
  convert hh using 1
  decide +kernel
noncomputable def entry2_1 : RBox := ⟨2902156808558552618644536340,2902158819463200260094093913⟩
lemma entry2_1_contains : entry2_1.Contains (umat 2 1) := by
  have h0 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) true false cm85_4_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) true true cm85_4_1_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  change entry2_1.Contains (S (columnVector node true) (node4,false))
  convert hh using 1
  decide +kernel
noncomputable def entry5_1 : RBox := ⟨(-11157780530099753802763251033),(-11157767254491668280634953253)⟩
lemma entry5_1_contains : entry5_1.Contains (umat 5 1) := by
  have h0 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) true false cm85_4_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) true true cm85_4_1_1.contains
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
end SharpPlanar.Numerical.U85

end OAI
