import OAI.Analysis.PlanarPacking.Certificate.WCertificates
import OAI.Analysis.PlanarPacking.Certificate.UMoments27

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical.U27
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def node : Node := ⟨27,by norm_num [residues]⟩
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
noncomputable def entry0_0 : RBox := ⟨278990510479936712403226109,278990510480021405447007896⟩
lemma entry0_0_contains : entry0_0.Contains (umat 0 0) := by
  have h0 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) false false cm27_1_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) false true cm27_1_0_1.contains
  have hh := S_column_value_contains (m:=node1) h0
  change entry0_0.Contains (S (columnVector node false) (node1,false))
  convert hh using 1
  decide +kernel
noncomputable def entry3_0 : RBox := ⟨(-10873029152966477351440904),(-10873029152489746509988316)⟩
lemma entry3_0_contains : entry3_0.Contains (umat 3 0) := by
  have h0 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) false false cm27_1_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) false true cm27_1_0_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  change entry3_0.Contains (S (columnVector node false) (node1,true))
  convert hh using 1
  decide +kernel
noncomputable def entry1_0 : RBox := ⟨719383639276547676356262135,719383639276561177049384890⟩
lemma entry1_0_contains : entry1_0.Contains (umat 1 0) := by
  have h0 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) false false cm27_3_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) false true cm27_3_0_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  change entry1_0.Contains (S (columnVector node false) (node3,false))
  convert hh using 1
  decide +kernel
noncomputable def entry4_0 : RBox := ⟨952303372127389678880776151,952303372127459233741271076⟩
lemma entry4_0_contains : entry4_0.Contains (umat 4 0) := by
  have h0 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) false false cm27_3_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) false true cm27_3_0_1.contains
  have hh := S_column_derivative_contains (m:=node3) h0 h1
  change entry4_0.Contains (S (columnVector node false) (node3,true))
  convert hh using 1
  decide +kernel
noncomputable def entry2_0 : RBox := ⟨(-398736274042741587092780032),(-398736274042738477592431984)⟩
lemma entry2_0_contains : entry2_0.Contains (umat 2 0) := by
  have h0 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) false false cm27_4_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) false true cm27_4_0_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  change entry2_0.Contains (S (columnVector node false) (node4,false))
  convert hh using 1
  decide +kernel
noncomputable def entry5_0 : RBox := ⟨1900443575246792638162255771,1900443575246812426686586162⟩
lemma entry5_0_contains : entry5_0.Contains (umat 5 0) := by
  have h0 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) false false cm27_4_0_0.contains
  have h1 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) false true cm27_4_0_1.contains
  have hh := S_column_derivative_contains (m:=node4) h0 h1
  change entry5_0.Contains (S (columnVector node false) (node4,true))
  convert hh using 1
  decide +kernel
noncomputable def entry0_1 : RBox := ⟨(-6959561865246361327217453820),(-6959561865246132060634644946)⟩
lemma entry0_1_contains : entry0_1.Contains (umat 0 1) := by
  have h0 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) true false cm27_1_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) true true cm27_1_1_1.contains
  have hh := S_column_value_contains (m:=node1) h0
  change entry0_1.Contains (S (columnVector node true) (node1,false))
  convert hh using 1
  decide +kernel
noncomputable def entry3_1 : RBox := ⟨(-289413124349156839881543258),(-289413124347865335965726789)⟩
lemma entry3_1_contains : entry3_1.Contains (umat 3 1) := by
  have h0 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) true false cm27_1_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=1) (by decide) (by decide) true true cm27_1_1_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  change entry3_1.Contains (S (columnVector node true) (node1,true))
  convert hh using 1
  decide +kernel
noncomputable def entry1_1 : RBox := ⟨(-17136771796223399386248855538),(-17136771796223360893755434176)⟩
lemma entry1_1_contains : entry1_1.Contains (umat 1 1) := by
  have h0 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) true false cm27_3_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) true true cm27_3_1_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  change entry1_1.Contains (S (columnVector node true) (node3,false))
  convert hh using 1
  decide +kernel
noncomputable def entry4_1 : RBox := ⟨(-24489813837920627876059576684),(-24489813837920430082653551426)⟩
lemma entry4_1_contains : entry4_1.Contains (umat 4 1) := by
  have h0 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) true false cm27_3_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=3) (by decide) (by decide) true true cm27_3_1_1.contains
  have hh := S_column_derivative_contains (m:=node3) h0 h1
  change entry4_1.Contains (S (columnVector node true) (node3,true))
  convert hh using 1
  decide +kernel
noncomputable def entry2_1 : RBox := ⟨9793258629831515550378575395,9793258629831524288911413105⟩
lemma entry2_1_contains : entry2_1.Contains (umat 2 1) := by
  have h0 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) true false cm27_4_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) true true cm27_4_1_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  change entry2_1.Contains (S (columnVector node true) (node4,false))
  convert hh using 1
  decide +kernel
noncomputable def entry5_1 : RBox := ⟨(-41153229096449685758068078648),(-41153229096449630112530202299)⟩
lemma entry5_1_contains : entry5_1.Contains (umat 5 1) := by
  have h0 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) true false cm27_4_1_0.contains
  have h1 := K_column_contains (n:=node) (m:=4) (by decide) (by decide) true true cm27_4_1_1.contains
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
end SharpPlanar.Numerical.U27

end OAI
