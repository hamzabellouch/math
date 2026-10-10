import OAI.Analysis.PlanarPacking.Certificate.Columns10
import OAI.Analysis.PlanarPacking.Certificate.Columns20
import OAI.Analysis.PlanarPacking.Certificate.Columns30
import OAI.Analysis.PlanarPacking.Certificate.Columns40
import OAI.Analysis.PlanarPacking.Certificate.Columns50
import OAI.Analysis.PlanarPacking.Certificate.Columns60
import OAI.Analysis.PlanarPacking.Certificate.Columns70
import OAI.Analysis.PlanarPacking.Certificate.Columns80
import OAI.Analysis.PlanarPacking.Certificate.Columns90
import OAI.Analysis.PlanarPacking.Certificate.Columns100
import OAI.Analysis.PlanarPacking.TableDensityBase

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
noncomputable def allColumns (n : Fin 101) (d : Bool) (j : Fin 6) (i k : Fin 16) : CBox := match n.val with
  | 0 => if d then column0_1 j i k else column0_0 j i k
  | 1 => if d then column1_1 j i k else column1_0 j i k
  | 3 => if d then column3_1 j i k else column3_0 j i k
  | 4 => if d then column4_1 j i k else column4_0 j i k
  | 7 => if d then column7_1 j i k else column7_0 j i k
  | 9 => if d then column9_1 j i k else column9_0 j i k
  | 12 => if d then column12_1 j i k else column12_0 j i k
  | 13 => if d then column13_1 j i k else column13_0 j i k
  | 15 => if d then column15_1 j i k else column15_0 j i k
  | 16 => if d then column16_1 j i k else column16_0 j i k
  | 19 => if d then column19_1 j i k else column19_0 j i k
  | 21 => if d then column21_1 j i k else column21_0 j i k
  | 24 => if d then column24_1 j i k else column24_0 j i k
  | 25 => if d then column25_1 j i k else column25_0 j i k
  | 27 => if d then column27_1 j i k else column27_0 j i k
  | 28 => if d then column28_1 j i k else column28_0 j i k
  | 31 => if d then column31_1 j i k else column31_0 j i k
  | 33 => if d then column33_1 j i k else column33_0 j i k
  | 36 => if d then column36_1 j i k else column36_0 j i k
  | 37 => if d then column37_1 j i k else column37_0 j i k
  | 39 => if d then column39_1 j i k else column39_0 j i k
  | 40 => if d then column40_1 j i k else column40_0 j i k
  | 43 => if d then column43_1 j i k else column43_0 j i k
  | 45 => if d then column45_1 j i k else column45_0 j i k
  | 48 => if d then column48_1 j i k else column48_0 j i k
  | 49 => if d then column49_1 j i k else column49_0 j i k
  | 51 => if d then column51_1 j i k else column51_0 j i k
  | 52 => if d then column52_1 j i k else column52_0 j i k
  | 55 => if d then column55_1 j i k else column55_0 j i k
  | 57 => if d then column57_1 j i k else column57_0 j i k
  | 60 => if d then column60_1 j i k else column60_0 j i k
  | 61 => if d then column61_1 j i k else column61_0 j i k
  | 63 => if d then column63_1 j i k else column63_0 j i k
  | 64 => if d then column64_1 j i k else column64_0 j i k
  | 67 => if d then column67_1 j i k else column67_0 j i k
  | 69 => if d then column69_1 j i k else column69_0 j i k
  | 72 => if d then column72_1 j i k else column72_0 j i k
  | 73 => if d then column73_1 j i k else column73_0 j i k
  | 75 => if d then column75_1 j i k else column75_0 j i k
  | 76 => if d then column76_1 j i k else column76_0 j i k
  | 79 => if d then column79_1 j i k else column79_0 j i k
  | 81 => if d then column81_1 j i k else column81_0 j i k
  | 84 => if d then column84_1 j i k else column84_0 j i k
  | 85 => if d then column85_1 j i k else column85_0 j i k
  | 87 => if d then column87_1 j i k else column87_0 j i k
  | 88 => if d then column88_1 j i k else column88_0 j i k
  | 91 => if d then column91_1 j i k else column91_0 j i k
  | 93 => if d then column93_1 j i k else column93_0 j i k
  | 96 => if d then column96_1 j i k else column96_0 j i k
  | 97 => if d then column97_1 j i k else column97_0 j i k
  | 99 => if d then column99_1 j i k else column99_0 j i k
  | 100 => if d then column100_1 j i k else column100_0 j i k
  | _ => CBox.rat 0 1 0 1
noncomputable def tableTerm (a d : Bool) (n : Fin 101) (j : Fin 6) (i k : Fin 16) : CBox := (allColumns n d j i k).scale (tableNum a d n.val) 10000000000
lemma tableTerm0_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 0 j i k).Contains (((if d then (tableD a 0:ℝ) else (tableC a 0:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 0 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column0_0_contains j i k) a
  · exact scaled_table_basis (column0_1_contains j i k) a
lemma tableTerm1_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 1 j i k).Contains (((if d then (tableD a 1:ℝ) else (tableC a 1:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 1 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column1_0_contains j i k) a
  · exact scaled_table_basis (column1_1_contains j i k) a
lemma tableTerm2_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 2 j i k).Contains (((if d then (tableD a 2:ℝ) else (tableC a 2:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 2 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm3_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 3 j i k).Contains (((if d then (tableD a 3:ℝ) else (tableC a 3:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 3 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column3_0_contains j i k) a
  · exact scaled_table_basis (column3_1_contains j i k) a
lemma tableTerm4_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 4 j i k).Contains (((if d then (tableD a 4:ℝ) else (tableC a 4:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 4 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column4_0_contains j i k) a
  · exact scaled_table_basis (column4_1_contains j i k) a
lemma tableTerm5_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 5 j i k).Contains (((if d then (tableD a 5:ℝ) else (tableC a 5:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 5 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm6_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 6 j i k).Contains (((if d then (tableD a 6:ℝ) else (tableC a 6:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 6 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm7_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 7 j i k).Contains (((if d then (tableD a 7:ℝ) else (tableC a 7:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 7 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column7_0_contains j i k) a
  · exact scaled_table_basis (column7_1_contains j i k) a
lemma tableTerm8_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 8 j i k).Contains (((if d then (tableD a 8:ℝ) else (tableC a 8:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 8 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm9_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 9 j i k).Contains (((if d then (tableD a 9:ℝ) else (tableC a 9:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 9 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column9_0_contains j i k) a
  · exact scaled_table_basis (column9_1_contains j i k) a
lemma tableTerm10_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 10 j i k).Contains (((if d then (tableD a 10:ℝ) else (tableC a 10:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 10 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm11_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 11 j i k).Contains (((if d then (tableD a 11:ℝ) else (tableC a 11:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 11 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm12_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 12 j i k).Contains (((if d then (tableD a 12:ℝ) else (tableC a 12:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 12 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column12_0_contains j i k) a
  · exact scaled_table_basis (column12_1_contains j i k) a
lemma tableTerm13_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 13 j i k).Contains (((if d then (tableD a 13:ℝ) else (tableC a 13:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 13 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column13_0_contains j i k) a
  · exact scaled_table_basis (column13_1_contains j i k) a
lemma tableTerm14_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 14 j i k).Contains (((if d then (tableD a 14:ℝ) else (tableC a 14:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 14 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm15_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 15 j i k).Contains (((if d then (tableD a 15:ℝ) else (tableC a 15:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 15 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column15_0_contains j i k) a
  · exact scaled_table_basis (column15_1_contains j i k) a
lemma tableTerm16_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 16 j i k).Contains (((if d then (tableD a 16:ℝ) else (tableC a 16:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 16 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column16_0_contains j i k) a
  · exact scaled_table_basis (column16_1_contains j i k) a
lemma tableTerm17_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 17 j i k).Contains (((if d then (tableD a 17:ℝ) else (tableC a 17:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 17 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm18_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 18 j i k).Contains (((if d then (tableD a 18:ℝ) else (tableC a 18:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 18 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm19_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 19 j i k).Contains (((if d then (tableD a 19:ℝ) else (tableC a 19:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 19 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column19_0_contains j i k) a
  · exact scaled_table_basis (column19_1_contains j i k) a
lemma tableTerm20_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 20 j i k).Contains (((if d then (tableD a 20:ℝ) else (tableC a 20:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 20 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm21_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 21 j i k).Contains (((if d then (tableD a 21:ℝ) else (tableC a 21:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 21 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column21_0_contains j i k) a
  · exact scaled_table_basis (column21_1_contains j i k) a
lemma tableTerm22_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 22 j i k).Contains (((if d then (tableD a 22:ℝ) else (tableC a 22:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 22 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm23_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 23 j i k).Contains (((if d then (tableD a 23:ℝ) else (tableC a 23:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 23 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm24_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 24 j i k).Contains (((if d then (tableD a 24:ℝ) else (tableC a 24:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 24 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column24_0_contains j i k) a
  · exact scaled_table_basis (column24_1_contains j i k) a
lemma tableTerm25_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 25 j i k).Contains (((if d then (tableD a 25:ℝ) else (tableC a 25:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 25 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column25_0_contains j i k) a
  · exact scaled_table_basis (column25_1_contains j i k) a
lemma tableTerm26_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 26 j i k).Contains (((if d then (tableD a 26:ℝ) else (tableC a 26:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 26 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm27_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 27 j i k).Contains (((if d then (tableD a 27:ℝ) else (tableC a 27:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 27 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column27_0_contains j i k) a
  · exact scaled_table_basis (column27_1_contains j i k) a
lemma tableTerm28_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 28 j i k).Contains (((if d then (tableD a 28:ℝ) else (tableC a 28:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 28 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column28_0_contains j i k) a
  · exact scaled_table_basis (column28_1_contains j i k) a
lemma tableTerm29_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 29 j i k).Contains (((if d then (tableD a 29:ℝ) else (tableC a 29:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 29 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm30_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 30 j i k).Contains (((if d then (tableD a 30:ℝ) else (tableC a 30:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 30 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm31_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 31 j i k).Contains (((if d then (tableD a 31:ℝ) else (tableC a 31:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 31 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column31_0_contains j i k) a
  · exact scaled_table_basis (column31_1_contains j i k) a
lemma tableTerm32_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 32 j i k).Contains (((if d then (tableD a 32:ℝ) else (tableC a 32:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 32 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm33_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 33 j i k).Contains (((if d then (tableD a 33:ℝ) else (tableC a 33:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 33 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column33_0_contains j i k) a
  · exact scaled_table_basis (column33_1_contains j i k) a
lemma tableTerm34_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 34 j i k).Contains (((if d then (tableD a 34:ℝ) else (tableC a 34:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 34 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm35_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 35 j i k).Contains (((if d then (tableD a 35:ℝ) else (tableC a 35:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 35 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm36_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 36 j i k).Contains (((if d then (tableD a 36:ℝ) else (tableC a 36:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 36 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column36_0_contains j i k) a
  · exact scaled_table_basis (column36_1_contains j i k) a
lemma tableTerm37_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 37 j i k).Contains (((if d then (tableD a 37:ℝ) else (tableC a 37:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 37 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column37_0_contains j i k) a
  · exact scaled_table_basis (column37_1_contains j i k) a
lemma tableTerm38_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 38 j i k).Contains (((if d then (tableD a 38:ℝ) else (tableC a 38:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 38 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm39_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 39 j i k).Contains (((if d then (tableD a 39:ℝ) else (tableC a 39:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 39 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column39_0_contains j i k) a
  · exact scaled_table_basis (column39_1_contains j i k) a
lemma tableTerm40_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 40 j i k).Contains (((if d then (tableD a 40:ℝ) else (tableC a 40:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 40 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column40_0_contains j i k) a
  · exact scaled_table_basis (column40_1_contains j i k) a
lemma tableTerm41_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 41 j i k).Contains (((if d then (tableD a 41:ℝ) else (tableC a 41:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 41 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm42_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 42 j i k).Contains (((if d then (tableD a 42:ℝ) else (tableC a 42:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 42 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm43_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 43 j i k).Contains (((if d then (tableD a 43:ℝ) else (tableC a 43:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 43 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column43_0_contains j i k) a
  · exact scaled_table_basis (column43_1_contains j i k) a
lemma tableTerm44_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 44 j i k).Contains (((if d then (tableD a 44:ℝ) else (tableC a 44:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 44 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm45_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 45 j i k).Contains (((if d then (tableD a 45:ℝ) else (tableC a 45:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 45 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column45_0_contains j i k) a
  · exact scaled_table_basis (column45_1_contains j i k) a
lemma tableTerm46_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 46 j i k).Contains (((if d then (tableD a 46:ℝ) else (tableC a 46:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 46 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm47_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 47 j i k).Contains (((if d then (tableD a 47:ℝ) else (tableC a 47:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 47 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm48_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 48 j i k).Contains (((if d then (tableD a 48:ℝ) else (tableC a 48:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 48 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column48_0_contains j i k) a
  · exact scaled_table_basis (column48_1_contains j i k) a
lemma tableTerm49_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 49 j i k).Contains (((if d then (tableD a 49:ℝ) else (tableC a 49:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 49 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column49_0_contains j i k) a
  · exact scaled_table_basis (column49_1_contains j i k) a
lemma tableTerm50_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 50 j i k).Contains (((if d then (tableD a 50:ℝ) else (tableC a 50:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 50 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm51_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 51 j i k).Contains (((if d then (tableD a 51:ℝ) else (tableC a 51:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 51 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column51_0_contains j i k) a
  · exact scaled_table_basis (column51_1_contains j i k) a
lemma tableTerm52_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 52 j i k).Contains (((if d then (tableD a 52:ℝ) else (tableC a 52:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 52 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column52_0_contains j i k) a
  · exact scaled_table_basis (column52_1_contains j i k) a
lemma tableTerm53_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 53 j i k).Contains (((if d then (tableD a 53:ℝ) else (tableC a 53:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 53 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm54_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 54 j i k).Contains (((if d then (tableD a 54:ℝ) else (tableC a 54:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 54 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm55_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 55 j i k).Contains (((if d then (tableD a 55:ℝ) else (tableC a 55:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 55 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column55_0_contains j i k) a
  · exact scaled_table_basis (column55_1_contains j i k) a
lemma tableTerm56_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 56 j i k).Contains (((if d then (tableD a 56:ℝ) else (tableC a 56:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 56 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm57_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 57 j i k).Contains (((if d then (tableD a 57:ℝ) else (tableC a 57:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 57 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column57_0_contains j i k) a
  · exact scaled_table_basis (column57_1_contains j i k) a
lemma tableTerm58_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 58 j i k).Contains (((if d then (tableD a 58:ℝ) else (tableC a 58:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 58 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm59_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 59 j i k).Contains (((if d then (tableD a 59:ℝ) else (tableC a 59:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 59 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm60_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 60 j i k).Contains (((if d then (tableD a 60:ℝ) else (tableC a 60:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 60 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column60_0_contains j i k) a
  · exact scaled_table_basis (column60_1_contains j i k) a
lemma tableTerm61_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 61 j i k).Contains (((if d then (tableD a 61:ℝ) else (tableC a 61:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 61 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column61_0_contains j i k) a
  · exact scaled_table_basis (column61_1_contains j i k) a
lemma tableTerm62_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 62 j i k).Contains (((if d then (tableD a 62:ℝ) else (tableC a 62:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 62 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm63_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 63 j i k).Contains (((if d then (tableD a 63:ℝ) else (tableC a 63:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 63 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column63_0_contains j i k) a
  · exact scaled_table_basis (column63_1_contains j i k) a
lemma tableTerm64_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 64 j i k).Contains (((if d then (tableD a 64:ℝ) else (tableC a 64:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 64 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column64_0_contains j i k) a
  · exact scaled_table_basis (column64_1_contains j i k) a
lemma tableTerm65_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 65 j i k).Contains (((if d then (tableD a 65:ℝ) else (tableC a 65:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 65 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm66_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 66 j i k).Contains (((if d then (tableD a 66:ℝ) else (tableC a 66:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 66 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm67_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 67 j i k).Contains (((if d then (tableD a 67:ℝ) else (tableC a 67:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 67 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column67_0_contains j i k) a
  · exact scaled_table_basis (column67_1_contains j i k) a
lemma tableTerm68_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 68 j i k).Contains (((if d then (tableD a 68:ℝ) else (tableC a 68:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 68 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm69_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 69 j i k).Contains (((if d then (tableD a 69:ℝ) else (tableC a 69:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 69 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column69_0_contains j i k) a
  · exact scaled_table_basis (column69_1_contains j i k) a
lemma tableTerm70_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 70 j i k).Contains (((if d then (tableD a 70:ℝ) else (tableC a 70:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 70 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm71_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 71 j i k).Contains (((if d then (tableD a 71:ℝ) else (tableC a 71:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 71 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm72_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 72 j i k).Contains (((if d then (tableD a 72:ℝ) else (tableC a 72:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 72 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column72_0_contains j i k) a
  · exact scaled_table_basis (column72_1_contains j i k) a
lemma tableTerm73_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 73 j i k).Contains (((if d then (tableD a 73:ℝ) else (tableC a 73:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 73 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column73_0_contains j i k) a
  · exact scaled_table_basis (column73_1_contains j i k) a
lemma tableTerm74_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 74 j i k).Contains (((if d then (tableD a 74:ℝ) else (tableC a 74:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 74 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm75_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 75 j i k).Contains (((if d then (tableD a 75:ℝ) else (tableC a 75:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 75 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column75_0_contains j i k) a
  · exact scaled_table_basis (column75_1_contains j i k) a
lemma tableTerm76_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 76 j i k).Contains (((if d then (tableD a 76:ℝ) else (tableC a 76:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 76 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column76_0_contains j i k) a
  · exact scaled_table_basis (column76_1_contains j i k) a
lemma tableTerm77_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 77 j i k).Contains (((if d then (tableD a 77:ℝ) else (tableC a 77:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 77 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm78_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 78 j i k).Contains (((if d then (tableD a 78:ℝ) else (tableC a 78:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 78 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm79_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 79 j i k).Contains (((if d then (tableD a 79:ℝ) else (tableC a 79:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 79 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column79_0_contains j i k) a
  · exact scaled_table_basis (column79_1_contains j i k) a
lemma tableTerm80_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 80 j i k).Contains (((if d then (tableD a 80:ℝ) else (tableC a 80:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 80 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm81_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 81 j i k).Contains (((if d then (tableD a 81:ℝ) else (tableC a 81:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 81 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column81_0_contains j i k) a
  · exact scaled_table_basis (column81_1_contains j i k) a
lemma tableTerm82_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 82 j i k).Contains (((if d then (tableD a 82:ℝ) else (tableC a 82:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 82 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm83_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 83 j i k).Contains (((if d then (tableD a 83:ℝ) else (tableC a 83:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 83 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm84_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 84 j i k).Contains (((if d then (tableD a 84:ℝ) else (tableC a 84:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 84 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column84_0_contains j i k) a
  · exact scaled_table_basis (column84_1_contains j i k) a
lemma tableTerm85_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 85 j i k).Contains (((if d then (tableD a 85:ℝ) else (tableC a 85:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 85 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column85_0_contains j i k) a
  · exact scaled_table_basis (column85_1_contains j i k) a
lemma tableTerm86_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 86 j i k).Contains (((if d then (tableD a 86:ℝ) else (tableC a 86:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 86 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm87_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 87 j i k).Contains (((if d then (tableD a 87:ℝ) else (tableC a 87:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 87 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column87_0_contains j i k) a
  · exact scaled_table_basis (column87_1_contains j i k) a
lemma tableTerm88_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 88 j i k).Contains (((if d then (tableD a 88:ℝ) else (tableC a 88:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 88 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column88_0_contains j i k) a
  · exact scaled_table_basis (column88_1_contains j i k) a
lemma tableTerm89_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 89 j i k).Contains (((if d then (tableD a 89:ℝ) else (tableC a 89:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 89 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm90_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 90 j i k).Contains (((if d then (tableD a 90:ℝ) else (tableC a 90:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 90 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm91_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 91 j i k).Contains (((if d then (tableD a 91:ℝ) else (tableC a 91:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 91 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column91_0_contains j i k) a
  · exact scaled_table_basis (column91_1_contains j i k) a
lemma tableTerm92_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 92 j i k).Contains (((if d then (tableD a 92:ℝ) else (tableC a 92:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 92 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm93_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 93 j i k).Contains (((if d then (tableD a 93:ℝ) else (tableC a 93:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 93 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column93_0_contains j i k) a
  · exact scaled_table_basis (column93_1_contains j i k) a
lemma tableTerm94_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 94 j i k).Contains (((if d then (tableD a 94:ℝ) else (tableC a 94:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 94 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm95_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 95 j i k).Contains (((if d then (tableD a 95:ℝ) else (tableC a 95:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 95 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm96_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 96 j i k).Contains (((if d then (tableD a 96:ℝ) else (tableC a 96:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 96 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column96_0_contains j i k) a
  · exact scaled_table_basis (column96_1_contains j i k) a
lemma tableTerm97_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 97 j i k).Contains (((if d then (tableD a 97:ℝ) else (tableC a 97:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 97 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column97_0_contains j i k) a
  · exact scaled_table_basis (column97_1_contains j i k) a
lemma tableTerm98_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 98 j i k).Contains (((if d then (tableD a 98:ℝ) else (tableC a 98:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 98 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm99_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 99 j i k).Contains (((if d then (tableD a 99:ℝ) else (tableC a 99:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 99 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column99_0_contains j i k) a
  · exact scaled_table_basis (column99_1_contains j i k) a
lemma tableTerm100_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 100 j i k).Contains (((if d then (tableD a 100:ℝ) else (tableC a 100:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 100 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column100_0_contains j i k) a
  · exact scaled_table_basis (column100_1_contains j i k) a
lemma tableTerm_contains (a d : Bool) (n : Fin 101) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d n j i k).Contains (((if d then (tableD a n:ℝ) else (tableC a n:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d n j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  fin_cases n
  · exact tableTerm0_contains a d j i k
  · exact tableTerm1_contains a d j i k
  · exact tableTerm2_contains a d j i k
  · exact tableTerm3_contains a d j i k
  · exact tableTerm4_contains a d j i k
  · exact tableTerm5_contains a d j i k
  · exact tableTerm6_contains a d j i k
  · exact tableTerm7_contains a d j i k
  · exact tableTerm8_contains a d j i k
  · exact tableTerm9_contains a d j i k
  · exact tableTerm10_contains a d j i k
  · exact tableTerm11_contains a d j i k
  · exact tableTerm12_contains a d j i k
  · exact tableTerm13_contains a d j i k
  · exact tableTerm14_contains a d j i k
  · exact tableTerm15_contains a d j i k
  · exact tableTerm16_contains a d j i k
  · exact tableTerm17_contains a d j i k
  · exact tableTerm18_contains a d j i k
  · exact tableTerm19_contains a d j i k
  · exact tableTerm20_contains a d j i k
  · exact tableTerm21_contains a d j i k
  · exact tableTerm22_contains a d j i k
  · exact tableTerm23_contains a d j i k
  · exact tableTerm24_contains a d j i k
  · exact tableTerm25_contains a d j i k
  · exact tableTerm26_contains a d j i k
  · exact tableTerm27_contains a d j i k
  · exact tableTerm28_contains a d j i k
  · exact tableTerm29_contains a d j i k
  · exact tableTerm30_contains a d j i k
  · exact tableTerm31_contains a d j i k
  · exact tableTerm32_contains a d j i k
  · exact tableTerm33_contains a d j i k
  · exact tableTerm34_contains a d j i k
  · exact tableTerm35_contains a d j i k
  · exact tableTerm36_contains a d j i k
  · exact tableTerm37_contains a d j i k
  · exact tableTerm38_contains a d j i k
  · exact tableTerm39_contains a d j i k
  · exact tableTerm40_contains a d j i k
  · exact tableTerm41_contains a d j i k
  · exact tableTerm42_contains a d j i k
  · exact tableTerm43_contains a d j i k
  · exact tableTerm44_contains a d j i k
  · exact tableTerm45_contains a d j i k
  · exact tableTerm46_contains a d j i k
  · exact tableTerm47_contains a d j i k
  · exact tableTerm48_contains a d j i k
  · exact tableTerm49_contains a d j i k
  · exact tableTerm50_contains a d j i k
  · exact tableTerm51_contains a d j i k
  · exact tableTerm52_contains a d j i k
  · exact tableTerm53_contains a d j i k
  · exact tableTerm54_contains a d j i k
  · exact tableTerm55_contains a d j i k
  · exact tableTerm56_contains a d j i k
  · exact tableTerm57_contains a d j i k
  · exact tableTerm58_contains a d j i k
  · exact tableTerm59_contains a d j i k
  · exact tableTerm60_contains a d j i k
  · exact tableTerm61_contains a d j i k
  · exact tableTerm62_contains a d j i k
  · exact tableTerm63_contains a d j i k
  · exact tableTerm64_contains a d j i k
  · exact tableTerm65_contains a d j i k
  · exact tableTerm66_contains a d j i k
  · exact tableTerm67_contains a d j i k
  · exact tableTerm68_contains a d j i k
  · exact tableTerm69_contains a d j i k
  · exact tableTerm70_contains a d j i k
  · exact tableTerm71_contains a d j i k
  · exact tableTerm72_contains a d j i k
  · exact tableTerm73_contains a d j i k
  · exact tableTerm74_contains a d j i k
  · exact tableTerm75_contains a d j i k
  · exact tableTerm76_contains a d j i k
  · exact tableTerm77_contains a d j i k
  · exact tableTerm78_contains a d j i k
  · exact tableTerm79_contains a d j i k
  · exact tableTerm80_contains a d j i k
  · exact tableTerm81_contains a d j i k
  · exact tableTerm82_contains a d j i k
  · exact tableTerm83_contains a d j i k
  · exact tableTerm84_contains a d j i k
  · exact tableTerm85_contains a d j i k
  · exact tableTerm86_contains a d j i k
  · exact tableTerm87_contains a d j i k
  · exact tableTerm88_contains a d j i k
  · exact tableTerm89_contains a d j i k
  · exact tableTerm90_contains a d j i k
  · exact tableTerm91_contains a d j i k
  · exact tableTerm92_contains a d j i k
  · exact tableTerm93_contains a d j i k
  · exact tableTerm94_contains a d j i k
  · exact tableTerm95_contains a d j i k
  · exact tableTerm96_contains a d j i k
  · exact tableTerm97_contains a d j i k
  · exact tableTerm98_contains a d j i k
  · exact tableTerm99_contains a d j i k
  · exact tableTerm100_contains a d j i k
noncomputable def density0Expr (j : Fin 6) (i k : Fin 16) : CBox := finSum (fun n : Fin 101 => (tableTerm false false n j i k).add (tableTerm false true n j i k))
noncomputable def density1Expr (j : Fin 6) (i k : Fin 16) : CBox := finSum (fun n : Fin 101 => (tableTerm true false n j i k).add (tableTerm true true n j i k))
end SharpPlanar.CachedData

end OAI
