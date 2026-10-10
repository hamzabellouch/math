import OAI.Analysis.PlanarPacking.MatrixIntervals
import OAI.Analysis.PlanarPacking.Certificate.DEntries
import OAI.Analysis.PlanarPacking.Certificate.LMoments7
import OAI.Analysis.PlanarPacking.Certificate.LMoments9
import OAI.Analysis.PlanarPacking.Certificate.LMoments12
import OAI.Analysis.PlanarPacking.Certificate.LMoments13
import OAI.Analysis.PlanarPacking.Certificate.LMoments15
import OAI.Analysis.PlanarPacking.Certificate.LMoments16
import OAI.Analysis.PlanarPacking.Indices

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def Lmat : Matrix (Fin 12) (Fin 6) ℝ := fun i j => S (columnVector (jNode j) (jDeriv j)) (lNode i,lDeriv i)
noncomputable def lentry0_0 : RBox := ⟨386164739228853845759773052,386164739228853847338729471⟩
lemma lentry0_0_contains : lentry0_0.Contains (Lmat 0 0) := by
  have h0 := K_column_contains (n:=node1) (m:=7) (by decide) (by decide) false false cm1_7_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=7) (by decide) (by decide) false true cm1_7_0_1.contains
  have hh := S_column_value_contains (m:=node7) h0
  change lentry0_0.Contains (S (columnVector node1 false) (node7,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry6_0 : RBox := ⟨(-428037821451401034679013730),(-428037821451401027790023895)⟩
lemma lentry6_0_contains : lentry6_0.Contains (Lmat 6 0) := by
  have h0 := K_column_contains (n:=node1) (m:=7) (by decide) (by decide) false false cm1_7_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=7) (by decide) (by decide) false true cm1_7_0_1.contains
  have hh := S_column_derivative_contains (m:=node7) h0 h1
  change lentry6_0.Contains (S (columnVector node1 false) (node7,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry1_0 : RBox := ⟨49064967585188068869174563,49064967585188069987341210⟩
lemma lentry1_0_contains : lentry1_0.Contains (Lmat 1 0) := by
  have h0 := K_column_contains (n:=node1) (m:=9) (by decide) (by decide) false false cm1_9_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=9) (by decide) (by decide) false true cm1_9_0_1.contains
  have hh := S_column_value_contains (m:=node9) h0
  change lentry1_0.Contains (S (columnVector node1 false) (node9,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry7_0 : RBox := ⟨(-596386320756599937937491488),(-596386320756599933047674875)⟩
lemma lentry7_0_contains : lentry7_0.Contains (Lmat 7 0) := by
  have h0 := K_column_contains (n:=node1) (m:=9) (by decide) (by decide) false false cm1_9_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=9) (by decide) (by decide) false true cm1_9_0_1.contains
  have hh := S_column_derivative_contains (m:=node9) h0 h1
  change lentry7_0.Contains (S (columnVector node1 false) (node9,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry2_0 : RBox := ⟨349955633020704232195660108,349955633020704238293079170⟩
lemma lentry2_0_contains : lentry2_0.Contains (Lmat 2 0) := by
  have h0 := K_column_contains (n:=node1) (m:=12) (by decide) (by decide) false false cm1_12_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=12) (by decide) (by decide) false true cm1_12_0_1.contains
  have hh := S_column_value_contains (m:=node12) h0
  change lentry2_0.Contains (S (columnVector node1 false) (node12,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry8_0 : RBox := ⟨1156450605893201085971615858,1156450605893201123879614487⟩
lemma lentry8_0_contains : lentry8_0.Contains (Lmat 8 0) := by
  have h0 := K_column_contains (n:=node1) (m:=12) (by decide) (by decide) false false cm1_12_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=12) (by decide) (by decide) false true cm1_12_0_1.contains
  have hh := S_column_derivative_contains (m:=node12) h0 h1
  change lentry8_0.Contains (S (columnVector node1 false) (node12,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry3_0 : RBox := ⟨(-497900663495165887403278912),(-497900663495165876692203228)⟩
lemma lentry3_0_contains : lentry3_0.Contains (Lmat 3 0) := by
  have h0 := K_column_contains (n:=node1) (m:=13) (by decide) (by decide) false false cm1_13_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=13) (by decide) (by decide) false true cm1_13_0_1.contains
  have hh := S_column_value_contains (m:=node13) h0
  change lentry3_0.Contains (S (columnVector node1 false) (node13,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry9_0 : RBox := ⟨726695844980284058022282278,726695844980284110485485687⟩
lemma lentry9_0_contains : lentry9_0.Contains (Lmat 9 0) := by
  have h0 := K_column_contains (n:=node1) (m:=13) (by decide) (by decide) false false cm1_13_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=13) (by decide) (by decide) false true cm1_13_0_1.contains
  have hh := S_column_derivative_contains (m:=node13) h0 h1
  change lentry9_0.Contains (S (columnVector node1 false) (node13,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry4_0 : RBox := ⟨(-129722376498730229479424854),(-129722376498730219846221208)⟩
lemma lentry4_0_contains : lentry4_0.Contains (Lmat 4 0) := by
  have h0 := K_column_contains (n:=node1) (m:=15) (by decide) (by decide) false false cm1_15_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=15) (by decide) (by decide) false true cm1_15_0_1.contains
  have hh := S_column_value_contains (m:=node15) h0
  change lentry4_0.Contains (S (columnVector node1 false) (node15,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry10_0 : RBox := ⟨735342424357373673845647416,735342424357373720939652077⟩
lemma lentry10_0_contains : lentry10_0.Contains (Lmat 10 0) := by
  have h0 := K_column_contains (n:=node1) (m:=15) (by decide) (by decide) false false cm1_15_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=15) (by decide) (by decide) false true cm1_15_0_1.contains
  have hh := S_column_derivative_contains (m:=node15) h0 h1
  change lentry10_0.Contains (S (columnVector node1 false) (node15,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry5_0 : RBox := ⟨5192157766382216813328101,5192157766382221815251673⟩
lemma lentry5_0_contains : lentry5_0.Contains (Lmat 5 0) := by
  have h0 := K_column_contains (n:=node1) (m:=16) (by decide) (by decide) false false cm1_16_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=16) (by decide) (by decide) false true cm1_16_0_1.contains
  have hh := S_column_value_contains (m:=node16) h0
  change lentry5_0.Contains (S (columnVector node1 false) (node16,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry11_0 : RBox := ⟨(-373604188084837902044523338),(-373604188084837871188935056)⟩
lemma lentry11_0_contains : lentry11_0.Contains (Lmat 11 0) := by
  have h0 := K_column_contains (n:=node1) (m:=16) (by decide) (by decide) false false cm1_16_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=16) (by decide) (by decide) false true cm1_16_0_1.contains
  have hh := S_column_derivative_contains (m:=node16) h0 h1
  change lentry11_0.Contains (S (columnVector node1 false) (node16,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry0_3 : RBox := ⟨1237841529233122015925964342,1237841529233122021272149662⟩
lemma lentry0_3_contains : lentry0_3.Contains (Lmat 0 3) := by
  have h0 := K_column_contains (n:=node1) (m:=7) (by decide) (by decide) true false cm1_7_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=7) (by decide) (by decide) true true cm1_7_1_1.contains
  have hh := S_column_value_contains (m:=node7) h0
  change lentry0_3.Contains (S (columnVector node1 true) (node7,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry6_3 : RBox := ⟨(-10884852847347014469371491535),(-10884852847347014445864444233)⟩
lemma lentry6_3_contains : lentry6_3.Contains (Lmat 6 3) := by
  have h0 := K_column_contains (n:=node1) (m:=7) (by decide) (by decide) true false cm1_7_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=7) (by decide) (by decide) true true cm1_7_1_1.contains
  have hh := S_column_derivative_contains (m:=node7) h0 h1
  change lentry6_3.Contains (S (columnVector node1 true) (node7,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry1_3 : RBox := ⟨(-945531822378341432500259730),(-945531822378341427352180742)⟩
lemma lentry1_3_contains : lentry1_3.Contains (Lmat 1 3) := by
  have h0 := K_column_contains (n:=node1) (m:=9) (by decide) (by decide) true false cm1_9_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=9) (by decide) (by decide) true true cm1_9_1_1.contains
  have hh := S_column_value_contains (m:=node9) h0
  change lentry1_3.Contains (S (columnVector node1 true) (node9,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry7_3 : RBox := ⟨(-4465708184822282113792278974),(-4465708184822282091488397712)⟩
lemma lentry7_3_contains : lentry7_3.Contains (Lmat 7 3) := by
  have h0 := K_column_contains (n:=node1) (m:=9) (by decide) (by decide) true false cm1_9_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=9) (by decide) (by decide) true true cm1_9_1_1.contains
  have hh := S_column_derivative_contains (m:=node9) h0 h1
  change lentry7_3.Contains (S (columnVector node1 true) (node9,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry2_3 : RBox := ⟨4605024524144134428523673830,4605024524144134467976903087⟩
lemma lentry2_3_contains : lentry2_3.Contains (Lmat 2 3) := by
  have h0 := K_column_contains (n:=node1) (m:=12) (by decide) (by decide) true false cm1_12_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=12) (by decide) (by decide) true true cm1_12_1_1.contains
  have hh := S_column_value_contains (m:=node12) h0
  change lentry2_3.Contains (S (columnVector node1 true) (node12,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry8_3 : RBox := ⟨9348829383490770441808543,9348829383491012494286692⟩
lemma lentry8_3_contains : lentry8_3.Contains (Lmat 8 3) := by
  have h0 := K_column_contains (n:=node1) (m:=12) (by decide) (by decide) true false cm1_12_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=12) (by decide) (by decide) true true cm1_12_1_1.contains
  have hh := S_column_derivative_contains (m:=node12) h0 h1
  change lentry8_3.Contains (S (columnVector node1 true) (node12,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry3_3 : RBox := ⟨(-4308649990873823136416589661),(-4308649990873823060803451595)⟩
lemma lentry3_3_contains : lentry3_3.Contains (Lmat 3 3) := by
  have h0 := K_column_contains (n:=node1) (m:=13) (by decide) (by decide) true false cm1_13_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=13) (by decide) (by decide) true true cm1_13_1_1.contains
  have hh := S_column_value_contains (m:=node13) h0
  change lentry3_3.Contains (S (columnVector node1 true) (node13,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry9_3 : RBox := ⟨26226240502596733865099430434,26226240502596734231105827117⟩
lemma lentry9_3_contains : lentry9_3.Contains (Lmat 9 3) := by
  have h0 := K_column_contains (n:=node1) (m:=13) (by decide) (by decide) true false cm1_13_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=13) (by decide) (by decide) true true cm1_13_1_1.contains
  have hh := S_column_derivative_contains (m:=node13) h0 h1
  change lentry9_3.Contains (S (columnVector node1 true) (node13,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry4_3 : RBox := ⟨1369022879160941407076210245,1369022879160941487324115228⟩
lemma lentry4_3_contains : lentry4_3.Contains (Lmat 4 3) := by
  have h0 := K_column_contains (n:=node1) (m:=15) (by decide) (by decide) true false cm1_15_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=15) (by decide) (by decide) true true cm1_15_1_1.contains
  have hh := S_column_value_contains (m:=node15) h0
  change lentry4_3.Contains (S (columnVector node1 true) (node15,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry10_3 : RBox := ⟨15723242855704063078702190943,15723242855704063465727922119⟩
lemma lentry10_3_contains : lentry10_3.Contains (Lmat 10 3) := by
  have h0 := K_column_contains (n:=node1) (m:=15) (by decide) (by decide) true false cm1_15_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=15) (by decide) (by decide) true true cm1_15_1_1.contains
  have hh := S_column_derivative_contains (m:=node15) h0 h1
  change lentry10_3.Contains (S (columnVector node1 true) (node15,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry5_3 : RBox := ⟨(-1289552013974452050024155783),(-1289552013974452005347604255)⟩
lemma lentry5_3_contains : lentry5_3.Contains (Lmat 5 3) := by
  have h0 := K_column_contains (n:=node1) (m:=16) (by decide) (by decide) true false cm1_16_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=16) (by decide) (by decide) true true cm1_16_1_1.contains
  have hh := S_column_value_contains (m:=node16) h0
  change lentry5_3.Contains (S (columnVector node1 true) (node16,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry11_3 : RBox := ⟨(-1539994406308444939497564809),(-1539994406308444667344235719)⟩
lemma lentry11_3_contains : lentry11_3.Contains (Lmat 11 3) := by
  have h0 := K_column_contains (n:=node1) (m:=16) (by decide) (by decide) true false cm1_16_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=16) (by decide) (by decide) true true cm1_16_1_1.contains
  have hh := S_column_derivative_contains (m:=node16) h0 h1
  change lentry11_3.Contains (S (columnVector node1 true) (node16,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry0_1 : RBox := ⟨486118439120750072856567422,486118439120750074559192952⟩
lemma lentry0_1_contains : lentry0_1.Contains (Lmat 0 1) := by
  have h0 := K_column_contains (n:=node3) (m:=7) (by decide) (by decide) false false cm3_7_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=7) (by decide) (by decide) false true cm3_7_0_1.contains
  have hh := S_column_value_contains (m:=node7) h0
  change lentry0_1.Contains (S (columnVector node3 false) (node7,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry6_1 : RBox := ⟨257993788917541150498000107,257993788917541157888863267⟩
lemma lentry6_1_contains : lentry6_1.Contains (Lmat 6 1) := by
  have h0 := K_column_contains (n:=node3) (m:=7) (by decide) (by decide) false false cm3_7_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=7) (by decide) (by decide) false true cm3_7_0_1.contains
  have hh := S_column_derivative_contains (m:=node7) h0 h1
  change lentry6_1.Contains (S (columnVector node3 false) (node7,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry1_1 : RBox := ⟨119087850140090609779608152,119087850140090611010500019⟩
lemma lentry1_1_contains : lentry1_1.Contains (Lmat 1 1) := by
  have h0 := K_column_contains (n:=node3) (m:=9) (by decide) (by decide) false false cm3_9_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=9) (by decide) (by decide) false true cm3_9_0_1.contains
  have hh := S_column_value_contains (m:=node9) h0
  change lentry1_1.Contains (S (columnVector node3 false) (node9,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry7_1 : RBox := ⟨(-663777977784782234746612750),(-663777977784782229394005574)⟩
lemma lentry7_1_contains : lentry7_1.Contains (Lmat 7 1) := by
  have h0 := K_column_contains (n:=node3) (m:=9) (by decide) (by decide) false false cm3_9_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=9) (by decide) (by decide) false true cm3_9_0_1.contains
  have hh := S_column_derivative_contains (m:=node9) h0 h1
  change lentry7_1.Contains (S (columnVector node3 false) (node9,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry2_1 : RBox := ⟨358967247032856833332163871,358967247032856840141352766⟩
lemma lentry2_1_contains : lentry2_1.Contains (Lmat 2 1) := by
  have h0 := K_column_contains (n:=node3) (m:=12) (by decide) (by decide) false false cm3_12_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=12) (by decide) (by decide) false true cm3_12_0_1.contains
  have hh := S_column_value_contains (m:=node12) h0
  change lentry2_1.Contains (S (columnVector node3 false) (node12,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry8_1 : RBox := ⟨1619108661149769913016706898,1619108661149769955303200794⟩
lemma lentry8_1_contains : lentry8_1.Contains (Lmat 8 1) := by
  have h0 := K_column_contains (n:=node3) (m:=12) (by decide) (by decide) false false cm3_12_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=12) (by decide) (by decide) false true cm3_12_0_1.contains
  have hh := S_column_derivative_contains (m:=node12) h0 h1
  change lentry8_1.Contains (S (columnVector node3 false) (node12,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry3_1 : RBox := ⟨(-579591941864548585450896356),(-579591941864548573447403574)⟩
lemma lentry3_1_contains : lentry3_1.Contains (Lmat 3 1) := by
  have h0 := K_column_contains (n:=node3) (m:=13) (by decide) (by decide) false false cm3_13_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=13) (by decide) (by decide) false true cm3_13_0_1.contains
  have hh := S_column_value_contains (m:=node13) h0
  change lentry3_1.Contains (S (columnVector node3 false) (node13,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry9_1 : RBox := ⟨377184322890016097180070227,377184322890016155875518461⟩
lemma lentry9_1_contains : lentry9_1.Contains (Lmat 9 1) := by
  have h0 := K_column_contains (n:=node3) (m:=13) (by decide) (by decide) false false cm3_13_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=13) (by decide) (by decide) false true cm3_13_0_1.contains
  have hh := S_column_derivative_contains (m:=node13) h0 h1
  change lentry9_1.Contains (S (columnVector node3 false) (node13,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry4_1 : RBox := ⟨(-195228355766339276704702654),(-195228355766339265841016551)⟩
lemma lentry4_1_contains : lentry4_1.Contains (Lmat 4 1) := by
  have h0 := K_column_contains (n:=node3) (m:=15) (by decide) (by decide) false false cm3_15_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=15) (by decide) (by decide) false true cm3_15_0_1.contains
  have hh := S_column_value_contains (m:=node15) h0
  change lentry4_1.Contains (S (columnVector node3 false) (node15,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry10_1 : RBox := ⟨710843065811023928625760408,710843065811023981701947655⟩
lemma lentry10_1_contains : lentry10_1.Contains (Lmat 10 1) := by
  have h0 := K_column_contains (n:=node3) (m:=15) (by decide) (by decide) false false cm3_15_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=15) (by decide) (by decide) false true cm3_15_0_1.contains
  have hh := S_column_derivative_contains (m:=node15) h0 h1
  change lentry10_1.Contains (S (columnVector node3 false) (node15,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry5_1 : RBox := ⟨25977920002013968828483999,25977920002013974478303761⟩
lemma lentry5_1_contains : lentry5_1.Contains (Lmat 5 1) := by
  have h0 := K_column_contains (n:=node3) (m:=16) (by decide) (by decide) false false cm3_16_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=16) (by decide) (by decide) false true cm3_16_0_1.contains
  have hh := S_column_value_contains (m:=node16) h0
  change lentry5_1.Contains (S (columnVector node3 false) (node16,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry11_1 : RBox := ⟨(-467966495451986099247977206),(-467966495451986064390183177)⟩
lemma lentry11_1_contains : lentry11_1.Contains (Lmat 11 1) := by
  have h0 := K_column_contains (n:=node3) (m:=16) (by decide) (by decide) false false cm3_16_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=16) (by decide) (by decide) false true cm3_16_0_1.contains
  have hh := S_column_derivative_contains (m:=node16) h0 h1
  change lentry11_1.Contains (S (columnVector node3 false) (node16,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry0_4 : RBox := ⟨2125600111687210926303952134,2125600111687210932405875170⟩
lemma lentry0_4_contains : lentry0_4.Contains (Lmat 0 4) := by
  have h0 := K_column_contains (n:=node3) (m:=7) (by decide) (by decide) true false cm3_7_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=7) (by decide) (by decide) true true cm3_7_1_1.contains
  have hh := S_column_value_contains (m:=node7) h0
  change lentry0_4.Contains (S (columnVector node3 true) (node7,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry6_4 : RBox := ⟨(-11139267443296261033356468182),(-11139267443296261006716194412)⟩
lemma lentry6_4_contains : lentry6_4.Contains (Lmat 6 4) := by
  have h0 := K_column_contains (n:=node3) (m:=7) (by decide) (by decide) true false cm3_7_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=7) (by decide) (by decide) true true cm3_7_1_1.contains
  have hh := S_column_derivative_contains (m:=node7) h0 h1
  change lentry6_4.Contains (S (columnVector node3 true) (node7,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry1_4 : RBox := ⟨(-780891265784406832000933468),(-780891265784406826200208949)⟩
lemma lentry1_4_contains : lentry1_4.Contains (Lmat 1 4) := by
  have h0 := K_column_contains (n:=node3) (m:=9) (by decide) (by decide) true false cm3_9_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=9) (by decide) (by decide) true true cm3_9_1_1.contains
  have hh := S_column_value_contains (m:=node9) h0
  change lentry1_4.Contains (S (columnVector node3 true) (node9,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry7_4 : RBox := ⟨(-5743618610332307669422004880),(-5743618610332307644322228913)⟩
lemma lentry7_4_contains : lentry7_4.Contains (Lmat 7 4) := by
  have h0 := K_column_contains (n:=node3) (m:=9) (by decide) (by decide) true false cm3_9_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=9) (by decide) (by decide) true true cm3_9_1_1.contains
  have hh := S_column_derivative_contains (m:=node9) h0 h1
  change lentry7_4.Contains (S (columnVector node3 true) (node9,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry2_4 : RBox := ⟨5321012643203737848682181032,5321012643203737892803135677⟩
lemma lentry2_4_contains : lentry2_4.Contains (Lmat 2 4) := by
  have h0 := K_column_contains (n:=node3) (m:=12) (by decide) (by decide) true false cm3_12_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=12) (by decide) (by decide) true true cm3_12_1_1.contains
  have hh := S_column_value_contains (m:=node12) h0
  change lentry2_4.Contains (S (columnVector node3 true) (node12,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry8_4 : RBox := ⟨2776571492109706045337114003,2776571492109706316069623773⟩
lemma lentry8_4_contains : lentry8_4.Contains (Lmat 8 4) := by
  have h0 := K_column_contains (n:=node3) (m:=12) (by decide) (by decide) true false cm3_12_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=12) (by decide) (by decide) true true cm3_12_1_1.contains
  have hh := S_column_derivative_contains (m:=node12) h0 h1
  change lentry8_4.Contains (S (columnVector node3 true) (node12,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry3_4 : RBox := ⟨(-5389978260281014816719222713),(-5389978260281014732262209926)⟩
lemma lentry3_4_contains : lentry3_4.Contains (Lmat 3 4) := by
  have h0 := K_column_contains (n:=node3) (m:=13) (by decide) (by decide) true false cm3_13_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=13) (by decide) (by decide) true true cm3_13_1_1.contains
  have hh := S_column_value_contains (m:=node13) h0
  change lentry3_4.Contains (S (columnVector node3 true) (node13,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry9_4 : RBox := ⟨27368681932658456888679605519,27368681932658457297208750387⟩
lemma lentry9_4_contains : lentry9_4.Contains (Lmat 9 4) := by
  have h0 := K_column_contains (n:=node3) (m:=13) (by decide) (by decide) true false cm3_13_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=13) (by decide) (by decide) true true cm3_13_1_1.contains
  have hh := S_column_derivative_contains (m:=node13) h0 h1
  change lentry9_4.Contains (S (columnVector node3 true) (node13,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry4_4 : RBox := ⟨1046331030113728873277846982,1046331030113728962453513129⟩
lemma lentry4_4_contains : lentry4_4.Contains (Lmat 4 4) := by
  have h0 := K_column_contains (n:=node3) (m:=15) (by decide) (by decide) true false cm3_15_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=15) (by decide) (by decide) true true cm3_15_1_1.contains
  have hh := S_column_value_contains (m:=node15) h0
  change lentry4_4.Contains (S (columnVector node3 true) (node15,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry10_4 : RBox := ⟨17181475429765936689474771825,17181475429765937119960748674⟩
lemma lentry10_4_contains : lentry10_4.Contains (Lmat 10 4) := by
  have h0 := K_column_contains (n:=node3) (m:=15) (by decide) (by decide) true false cm3_15_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=15) (by decide) (by decide) true true cm3_15_1_1.contains
  have hh := S_column_derivative_contains (m:=node15) h0 h1
  change lentry10_4.Contains (S (columnVector node3 true) (node15,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry5_4 : RBox := ⟨(-1259566801050796385474280065),(-1259566801050796335904409976)⟩
lemma lentry5_4_contains : lentry5_4.Contains (Lmat 5 4) := by
  have h0 := K_column_contains (n:=node3) (m:=16) (by decide) (by decide) true false cm3_16_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=16) (by decide) (by decide) true true cm3_16_1_1.contains
  have hh := S_column_value_contains (m:=node16) h0
  change lentry5_4.Contains (S (columnVector node3 true) (node16,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry11_4 : RBox := ⟨(-2380512632259958830256652294),(-2380512632259958528106206527)⟩
lemma lentry11_4_contains : lentry11_4.Contains (Lmat 11 4) := by
  have h0 := K_column_contains (n:=node3) (m:=16) (by decide) (by decide) true false cm3_16_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=16) (by decide) (by decide) true true cm3_16_1_1.contains
  have hh := S_column_derivative_contains (m:=node16) h0 h1
  change lentry11_4.Contains (S (columnVector node3 true) (node16,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry0_2 : RBox := ⟨485328626881395931714985849,485328626881395932971229801⟩
lemma lentry0_2_contains : lentry0_2.Contains (Lmat 0 2) := by
  have h0 := K_column_contains (n:=node4) (m:=7) (by decide) (by decide) false false cm4_7_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=7) (by decide) (by decide) false true cm4_7_0_1.contains
  have hh := S_column_value_contains (m:=node7) h0
  change lentry0_2.Contains (S (columnVector node4 false) (node7,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry6_2 : RBox := ⟨767399171832372983257164636,767399171832372988906161653⟩
lemma lentry6_2_contains : lentry6_2.Contains (Lmat 6 2) := by
  have h0 := K_column_contains (n:=node4) (m:=7) (by decide) (by decide) false false cm4_7_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=7) (by decide) (by decide) false true cm4_7_0_1.contains
  have hh := S_column_derivative_contains (m:=node7) h0 h1
  change lentry6_2.Contains (S (columnVector node4 false) (node7,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry1_2 : RBox := ⟨159432915114858452138511907,159432915114858453113123532⟩
lemma lentry1_2_contains : lentry1_2.Contains (Lmat 1 2) := by
  have h0 := K_column_contains (n:=node4) (m:=9) (by decide) (by decide) false false cm4_9_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=9) (by decide) (by decide) false true cm4_9_0_1.contains
  have hh := S_column_value_contains (m:=node9) h0
  change lentry1_2.Contains (S (columnVector node4 false) (node9,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry7_2 : RBox := ⟨(-644392944651544272181557039),(-644392944651544267855959278)⟩
lemma lentry7_2_contains : lentry7_2.Contains (Lmat 7 2) := by
  have h0 := K_column_contains (n:=node4) (m:=9) (by decide) (by decide) false false cm4_9_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=9) (by decide) (by decide) false true cm4_9_0_1.contains
  have hh := S_column_derivative_contains (m:=node9) h0 h1
  change lentry7_2.Contains (S (columnVector node4 false) (node9,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry2_2 : RBox := ⟨344129241302690651571586296,344129241302690657533194559⟩
lemma lentry2_2_contains : lentry2_2.Contains (Lmat 2 2) := by
  have h0 := K_column_contains (n:=node4) (m:=12) (by decide) (by decide) false false cm4_12_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=12) (by decide) (by decide) false true cm4_12_0_1.contains
  have hh := S_column_value_contains (m:=node12) h0
  change lentry2_2.Contains (S (columnVector node4 false) (node12,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry8_2 : RBox := ⟨1856497232206901564546533917,1856497232206901601841142359⟩
lemma lentry8_2_contains : lentry8_2.Contains (Lmat 8 2) := by
  have h0 := K_column_contains (n:=node4) (m:=12) (by decide) (by decide) false false cm4_12_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=12) (by decide) (by decide) false true cm4_12_0_1.contains
  have hh := S_column_derivative_contains (m:=node12) h0 h1
  change lentry8_2.Contains (S (columnVector node4 false) (node12,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry3_2 : RBox := ⟨(-607660233060482493251090964),(-607660233060482482498102625)⟩
lemma lentry3_2_contains : lentry3_2.Contains (Lmat 3 2) := by
  have h0 := K_column_contains (n:=node4) (m:=13) (by decide) (by decide) false false cm4_13_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=13) (by decide) (by decide) false true cm4_13_0_1.contains
  have hh := S_column_value_contains (m:=node13) h0
  change lentry3_2.Contains (S (columnVector node4 false) (node13,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry9_2 : RBox := ⟨109451628144957371825678763,109451628144957424719076512⟩
lemma lentry9_2_contains : lentry9_2.Contains (Lmat 9 2) := by
  have h0 := K_column_contains (n:=node4) (m:=13) (by decide) (by decide) false false cm4_13_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=13) (by decide) (by decide) false true cm4_13_0_1.contains
  have hh := S_column_derivative_contains (m:=node13) h0 h1
  change lentry9_2.Contains (S (columnVector node4 false) (node13,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry4_2 : RBox := ⟨(-232443036487199701392321254),(-232443036487199691183528398)⟩
lemma lentry4_2_contains : lentry4_2.Contains (Lmat 4 2) := by
  have h0 := K_column_contains (n:=node4) (m:=15) (by decide) (by decide) false false cm4_15_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=15) (by decide) (by decide) false true cm4_15_0_1.contains
  have hh := S_column_value_contains (m:=node15) h0
  change lentry4_2.Contains (S (columnVector node4 false) (node15,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry10_2 : RBox := ⟨667100822413377830267050569,667100822413377880297221997⟩
lemma lentry10_2_contains : lentry10_2.Contains (Lmat 10 2) := by
  have h0 := K_column_contains (n:=node4) (m:=15) (by decide) (by decide) false false cm4_15_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=15) (by decide) (by decide) false true cm4_15_0_1.contains
  have hh := S_column_derivative_contains (m:=node15) h0 h1
  change lentry10_2.Contains (S (columnVector node4 false) (node15,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry5_2 : RBox := ⟨39065964993206543259829543,39065964993206548649635729⟩
lemma lentry5_2_contains : lentry5_2.Contains (Lmat 5 2) := by
  have h0 := K_column_contains (n:=node4) (m:=16) (by decide) (by decide) false false cm4_16_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=16) (by decide) (by decide) false true cm4_16_0_1.contains
  have hh := S_column_value_contains (m:=node16) h0
  change lentry5_2.Contains (S (columnVector node4 false) (node16,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry11_2 : RBox := ⟨(-515958726858467410477971212),(-515958726858467377164471438)⟩
lemma lentry11_2_contains : lentry11_2.Contains (Lmat 11 2) := by
  have h0 := K_column_contains (n:=node4) (m:=16) (by decide) (by decide) false false cm4_16_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=16) (by decide) (by decide) false true cm4_16_0_1.contains
  have hh := S_column_derivative_contains (m:=node16) h0 h1
  change lentry11_2.Contains (S (columnVector node4 false) (node16,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry0_5 : RBox := ⟨2615176994895548135832210442,2615176994895548142063566693⟩
lemma lentry0_5_contains : lentry0_5.Contains (Lmat 0 5) := by
  have h0 := K_column_contains (n:=node4) (m:=7) (by decide) (by decide) true false cm4_7_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=7) (by decide) (by decide) true true cm4_7_1_1.contains
  have hh := S_column_value_contains (m:=node7) h0
  change lentry0_5.Contains (S (columnVector node4 true) (node7,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry6_5 : RBox := ⟨(-10633079943167156175729829310),(-10633079943167156148566371119)⟩
lemma lentry6_5_contains : lentry6_5.Contains (Lmat 6 5) := by
  have h0 := K_column_contains (n:=node4) (m:=7) (by decide) (by decide) true false cm4_7_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=7) (by decide) (by decide) true true cm4_7_1_1.contains
  have hh := S_column_derivative_contains (m:=node7) h0 h1
  change lentry6_5.Contains (S (columnVector node4 true) (node7,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry1_5 : RBox := ⟨(-641704209447256286883620943),(-641704209447256281007240349)⟩
lemma lentry1_5_contains : lentry1_5.Contains (Lmat 1 5) := by
  have h0 := K_column_contains (n:=node4) (m:=9) (by decide) (by decide) true false cm4_9_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=9) (by decide) (by decide) true true cm4_9_1_1.contains
  have hh := S_column_value_contains (m:=node9) h0
  change lentry1_5.Contains (S (columnVector node4 true) (node9,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry7_5 : RBox := ⟨(-6401538002129311513332102913),(-6401538002129311487912931512)⟩
lemma lentry7_5_contains : lentry7_5.Contains (Lmat 7 5) := by
  have h0 := K_column_contains (n:=node4) (m:=9) (by decide) (by decide) true false cm4_9_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=9) (by decide) (by decide) true true cm4_9_1_1.contains
  have hh := S_column_derivative_contains (m:=node9) h0 h1
  change lentry7_5.Contains (S (columnVector node4 true) (node9,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry2_5 : RBox := ⟨5673870684468758906815253281,5673870684468758951656584385⟩
lemma lentry2_5_contains : lentry2_5.Contains (Lmat 2 5) := by
  have h0 := K_column_contains (n:=node4) (m:=12) (by decide) (by decide) true false cm4_12_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=12) (by decide) (by decide) true true cm4_12_1_1.contains
  have hh := S_column_value_contains (m:=node12) h0
  change lentry2_5.Contains (S (columnVector node4 true) (node12,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry8_5 : RBox := ⟨4515061100882060574473274188,4515061100882060849421864762⟩
lemma lentry8_5_contains : lentry8_5.Contains (Lmat 8 5) := by
  have h0 := K_column_contains (n:=node4) (m:=12) (by decide) (by decide) true false cm4_12_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=12) (by decide) (by decide) true true cm4_12_1_1.contains
  have hh := S_column_derivative_contains (m:=node12) h0 h1
  change lentry8_5.Contains (S (columnVector node4 true) (node12,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry3_5 : RBox := ⟨(-5984619825577872881362402157),(-5984619825577872795340231432)⟩
lemma lentry3_5_contains : lentry3_5.Contains (Lmat 3 5) := by
  have h0 := K_column_contains (n:=node4) (m:=13) (by decide) (by decide) true false cm4_13_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=13) (by decide) (by decide) true true cm4_13_1_1.contains
  have hh := S_column_value_contains (m:=node13) h0
  change lentry3_5.Contains (S (columnVector node4 true) (node13,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry9_5 : RBox := ⟨27617495594282279521247988788,27617495594282279936739730868⟩
lemma lentry9_5_contains : lentry9_5.Contains (Lmat 9 5) := by
  have h0 := K_column_contains (n:=node4) (m:=13) (by decide) (by decide) true false cm4_13_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=13) (by decide) (by decide) true true cm4_13_1_1.contains
  have hh := S_column_derivative_contains (m:=node13) h0 h1
  change lentry9_5.Contains (S (columnVector node4 true) (node13,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry4_5 : RBox := ⟨832688775810658666830659423,832688775810658757889595712⟩
lemma lentry4_5_contains : lentry4_5.Contains (Lmat 4 5) := by
  have h0 := K_column_contains (n:=node4) (m:=15) (by decide) (by decide) true false cm4_15_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=15) (by decide) (by decide) true true cm4_15_1_1.contains
  have hh := S_column_value_contains (m:=node15) h0
  change lentry4_5.Contains (S (columnVector node4 true) (node15,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry10_5 : RBox := ⟨17872500092793652677529018879,17872500092793653116898410653⟩
lemma lentry10_5_contains : lentry10_5.Contains (Lmat 10 5) := by
  have h0 := K_column_contains (n:=node4) (m:=15) (by decide) (by decide) true false cm4_15_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=15) (by decide) (by decide) true true cm4_15_1_1.contains
  have hh := S_column_derivative_contains (m:=node15) h0 h1
  change lentry10_5.Contains (S (columnVector node4 true) (node15,true))
  convert hh using 1
  decide +kernel
noncomputable def lentry5_5 : RBox := ⟨(-1227193748716980633078098857),(-1227193748716980582381799584)⟩
lemma lentry5_5_contains : lentry5_5.Contains (Lmat 5 5) := by
  have h0 := K_column_contains (n:=node4) (m:=16) (by decide) (by decide) true false cm4_16_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=16) (by decide) (by decide) true true cm4_16_1_1.contains
  have hh := S_column_value_contains (m:=node16) h0
  change lentry5_5.Contains (S (columnVector node4 true) (node16,false))
  convert hh using 1
  decide +kernel
noncomputable def lentry11_5 : RBox := ⟨(-2872552850724879556441069579),(-2872552850724879247571465752)⟩
lemma lentry11_5_contains : lentry11_5.Contains (Lmat 11 5) := by
  have h0 := K_column_contains (n:=node4) (m:=16) (by decide) (by decide) true false cm4_16_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=16) (by decide) (by decide) true true cm4_16_1_1.contains
  have hh := S_column_derivative_contains (m:=node16) h0 h1
  change lentry11_5.Contains (S (columnVector node4 true) (node16,true))
  convert hh using 1
  decide +kernel
noncomputable def lEntries : Matrix (Fin 12) (Fin 6) RBox := ![![lentry0_0,lentry0_1,lentry0_2,lentry0_3,lentry0_4,lentry0_5],
![lentry1_0,lentry1_1,lentry1_2,lentry1_3,lentry1_4,lentry1_5],
![lentry2_0,lentry2_1,lentry2_2,lentry2_3,lentry2_4,lentry2_5],
![lentry3_0,lentry3_1,lentry3_2,lentry3_3,lentry3_4,lentry3_5],
![lentry4_0,lentry4_1,lentry4_2,lentry4_3,lentry4_4,lentry4_5],
![lentry5_0,lentry5_1,lentry5_2,lentry5_3,lentry5_4,lentry5_5],
![lentry6_0,lentry6_1,lentry6_2,lentry6_3,lentry6_4,lentry6_5],
![lentry7_0,lentry7_1,lentry7_2,lentry7_3,lentry7_4,lentry7_5],
![lentry8_0,lentry8_1,lentry8_2,lentry8_3,lentry8_4,lentry8_5],
![lentry9_0,lentry9_1,lentry9_2,lentry9_3,lentry9_4,lentry9_5],
![lentry10_0,lentry10_1,lentry10_2,lentry10_3,lentry10_4,lentry10_5],
![lentry11_0,lentry11_1,lentry11_2,lentry11_3,lentry11_4,lentry11_5]]
lemma lEntries_contains (i : Fin 12) (j : Fin 6) : (lEntries i j).Contains (Lmat i j) := by
  fin_cases i <;> fin_cases j
  · exact lentry0_0_contains
  · exact lentry0_1_contains
  · exact lentry0_2_contains
  · exact lentry0_3_contains
  · exact lentry0_4_contains
  · exact lentry0_5_contains
  · exact lentry1_0_contains
  · exact lentry1_1_contains
  · exact lentry1_2_contains
  · exact lentry1_3_contains
  · exact lentry1_4_contains
  · exact lentry1_5_contains
  · exact lentry2_0_contains
  · exact lentry2_1_contains
  · exact lentry2_2_contains
  · exact lentry2_3_contains
  · exact lentry2_4_contains
  · exact lentry2_5_contains
  · exact lentry3_0_contains
  · exact lentry3_1_contains
  · exact lentry3_2_contains
  · exact lentry3_3_contains
  · exact lentry3_4_contains
  · exact lentry3_5_contains
  · exact lentry4_0_contains
  · exact lentry4_1_contains
  · exact lentry4_2_contains
  · exact lentry4_3_contains
  · exact lentry4_4_contains
  · exact lentry4_5_contains
  · exact lentry5_0_contains
  · exact lentry5_1_contains
  · exact lentry5_2_contains
  · exact lentry5_3_contains
  · exact lentry5_4_contains
  · exact lentry5_5_contains
  · exact lentry6_0_contains
  · exact lentry6_1_contains
  · exact lentry6_2_contains
  · exact lentry6_3_contains
  · exact lentry6_4_contains
  · exact lentry6_5_contains
  · exact lentry7_0_contains
  · exact lentry7_1_contains
  · exact lentry7_2_contains
  · exact lentry7_3_contains
  · exact lentry7_4_contains
  · exact lentry7_5_contains
  · exact lentry8_0_contains
  · exact lentry8_1_contains
  · exact lentry8_2_contains
  · exact lentry8_3_contains
  · exact lentry8_4_contains
  · exact lentry8_5_contains
  · exact lentry9_0_contains
  · exact lentry9_1_contains
  · exact lentry9_2_contains
  · exact lentry9_3_contains
  · exact lentry9_4_contains
  · exact lentry9_5_contains
  · exact lentry10_0_contains
  · exact lentry10_1_contains
  · exact lentry10_2_contains
  · exact lentry10_3_contains
  · exact lentry10_4_contains
  · exact lentry10_5_contains
  · exact lentry11_0_contains
  · exact lentry11_1_contains
  · exact lentry11_2_contains
  · exact lentry11_3_contains
  · exact lentry11_4_contains
  · exact lentry11_5_contains
lemma Lmat_column (j : Fin 6) : ∑ i, |Lmat i j| < (88:ℝ)/1000 := by
  have hh := column_bound_lt (u:=88) (v:=1000) (a:=lEntries) (by norm_num) lEntries_contains (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
end SharpPlanar.Numerical

end OAI
