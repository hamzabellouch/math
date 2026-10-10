import OAI.Analysis.PlanarPacking.NodeIntervals
import OAI.Analysis.PlanarPacking.Certificate.DMoments1
import OAI.Analysis.PlanarPacking.Certificate.DMoments3
import OAI.Analysis.PlanarPacking.Certificate.DMoments4
import OAI.Analysis.PlanarPacking.Indices

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def Dmat : Matrix (Fin 6) (Fin 6) ℝ := fun i j => S (columnVector (jNode j) (jDeriv j)) (jNode i,jDeriv i)
noncomputable def dentry0_0 : RBox := ⟨(-245926663229645305249767762805),(-245926663229645304859284756738)⟩
lemma dentry0_0_contains : dentry0_0.Contains (S (columnVector node1 false) (node1,false)) := by
  have h0 := K_column_contains (n:=node1) (m:=1) (by decide) (by decide) false false cm1_1_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=1) (by decide) (by decide) false true cm1_1_0_1.contains
  have hh := S_column_value_contains (m:=node1) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry3_0 : RBox := ⟨424700589287547025857931921651,424700589287547027999275868645⟩
lemma dentry3_0_contains : dentry3_0.Contains (S (columnVector node1 false) (node1,true)) := by
  have h0 := K_column_contains (n:=node1) (m:=1) (by decide) (by decide) false false cm1_1_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=1) (by decide) (by decide) false true cm1_1_0_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry0_3 : RBox := ⟨30452555066926640622749259400,30452555066926640828004301927⟩
lemma dentry0_3_contains : dentry0_3.Contains (S (columnVector node1 true) (node1,false)) := by
  have h0 := K_column_contains (n:=node1) (m:=1) (by decide) (by decide) true false cm1_1_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=1) (by decide) (by decide) true true cm1_1_1_1.contains
  have hh := S_column_value_contains (m:=node1) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry3_3 : RBox := ⟨931968827424315928087138852293,931968827424315929373850684394⟩
lemma dentry3_3_contains : dentry3_3.Contains (S (columnVector node1 true) (node1,true)) := by
  have h0 := K_column_contains (n:=node1) (m:=1) (by decide) (by decide) true false cm1_1_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=1) (by decide) (by decide) true true cm1_1_1_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry1_0 : RBox := ⟨(-23655100336718873202242240942),(-23655100336718873120273669237)⟩
lemma dentry1_0_contains : dentry1_0.Contains (S (columnVector node1 false) (node3,false)) := by
  have h0 := K_column_contains (n:=node1) (m:=3) (by decide) (by decide) false false cm1_3_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=3) (by decide) (by decide) false true cm1_3_0_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry4_0 : RBox := ⟨145671047970350036773325436387,145671047970350037199231909594⟩
lemma dentry4_0_contains : dentry4_0.Contains (S (columnVector node1 false) (node3,true)) := by
  have h0 := K_column_contains (n:=node1) (m:=3) (by decide) (by decide) false false cm1_3_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=3) (by decide) (by decide) false true cm1_3_0_1.contains
  have hh := S_column_derivative_contains (m:=node3) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry1_3 : RBox := ⟨80528838586735272363974753180,80528838586735272472281451816⟩
lemma dentry1_3_contains : dentry1_3.Contains (S (columnVector node1 true) (node3,false)) := by
  have h0 := K_column_contains (n:=node1) (m:=3) (by decide) (by decide) true false cm1_3_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=3) (by decide) (by decide) true true cm1_3_1_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry4_3 : RBox := ⟨521756342810954494199096553637,521756342810954494790549200675⟩
lemma dentry4_3_contains : dentry4_3.Contains (S (columnVector node1 true) (node3,true)) := by
  have h0 := K_column_contains (n:=node1) (m:=3) (by decide) (by decide) true false cm1_3_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=3) (by decide) (by decide) true true cm1_3_1_1.contains
  have hh := S_column_derivative_contains (m:=node3) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry2_0 : RBox := ⟨(-1097737034296297013723665259),(-1097737034296296987012474958)⟩
lemma dentry2_0_contains : dentry2_0.Contains (S (columnVector node1 false) (node4,false)) := by
  have h0 := K_column_contains (n:=node1) (m:=4) (by decide) (by decide) false false cm1_4_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=4) (by decide) (by decide) false true cm1_4_0_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry5_0 : RBox := ⟨(-49222269312866616533668297810),(-49222269312866616362895656546)⟩
lemma dentry5_0_contains : dentry5_0.Contains (S (columnVector node1 false) (node4,true)) := by
  have h0 := K_column_contains (n:=node1) (m:=4) (by decide) (by decide) false false cm1_4_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=4) (by decide) (by decide) false true cm1_4_0_1.contains
  have hh := S_column_derivative_contains (m:=node4) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry2_3 : RBox := ⟨(-56406703537031364478831607653),(-56406703537031364430188588560)⟩
lemma dentry2_3_contains : dentry2_3.Contains (S (columnVector node1 true) (node4,false)) := by
  have h0 := K_column_contains (n:=node1) (m:=4) (by decide) (by decide) true false cm1_4_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=4) (by decide) (by decide) true true cm1_4_1_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry5_3 : RBox := ⟨27834593699646376815605650731,27834593699646377127655114131⟩
lemma dentry5_3_contains : dentry5_3.Contains (S (columnVector node1 true) (node4,true)) := by
  have h0 := K_column_contains (n:=node1) (m:=4) (by decide) (by decide) true false cm1_4_1_0.contains
  have h1 := K_column_contains (n:=node1) (m:=4) (by decide) (by decide) true true cm1_4_1_1.contains
  have hh := S_column_derivative_contains (m:=node4) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry0_1 : RBox := ⟨84919083920626310662179677360,84919083920626310963649378583⟩
lemma dentry0_1_contains : dentry0_1.Contains (S (columnVector node3 false) (node1,false)) := by
  have h0 := K_column_contains (n:=node3) (m:=1) (by decide) (by decide) false false cm3_1_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=1) (by decide) (by decide) false true cm3_1_0_1.contains
  have hh := S_column_value_contains (m:=node1) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry3_1 : RBox := ⟨(-401818617642335374122553965636),(-401818617642335372392607050014)⟩
lemma dentry3_1_contains : dentry3_1.Contains (S (columnVector node3 false) (node1,true)) := by
  have h0 := K_column_contains (n:=node3) (m:=1) (by decide) (by decide) false false cm3_1_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=1) (by decide) (by decide) false true cm3_1_0_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry0_4 : RBox := ⟨(-106450383559834775553375548749),(-106450383559834775291307669099)⟩
lemma dentry0_4_contains : dentry0_4.Contains (S (columnVector node3 true) (node1,false)) := by
  have h0 := K_column_contains (n:=node3) (m:=1) (by decide) (by decide) true false cm3_1_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=1) (by decide) (by decide) true true cm3_1_1_1.contains
  have hh := S_column_value_contains (m:=node1) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry3_4 : RBox := ⟨51160635846592449630662157438,51160635846592451095925214287⟩
lemma dentry3_4_contains : dentry3_4.Contains (S (columnVector node3 true) (node1,true)) := by
  have h0 := K_column_contains (n:=node3) (m:=1) (by decide) (by decide) true false cm3_1_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=1) (by decide) (by decide) true true cm3_1_1_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry1_1 : RBox := ⟨(-58681970988985215880538687120),(-58681970988985215799134371859)⟩
lemma dentry1_1_contains : dentry1_1.Contains (S (columnVector node3 false) (node3,false)) := by
  have h0 := K_column_contains (n:=node3) (m:=3) (by decide) (by decide) false false cm3_3_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=3) (by decide) (by decide) false true cm3_3_0_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry4_1 : RBox := ⟨(-13628559633735631908901705881),(-13628559633735631522414018748)⟩
lemma dentry4_1_contains : dentry4_1.Contains (S (columnVector node3 false) (node3,true)) := by
  have h0 := K_column_contains (n:=node3) (m:=3) (by decide) (by decide) false false cm3_3_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=3) (by decide) (by decide) false true cm3_3_0_1.contains
  have hh := S_column_derivative_contains (m:=node3) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry1_4 : RBox := ⟨(-9335195132489238242468768282),(-9335195132489238117842659765)⟩
lemma dentry1_4_contains : dentry1_4.Contains (S (columnVector node3 true) (node3,false)) := by
  have h0 := K_column_contains (n:=node3) (m:=3) (by decide) (by decide) true false cm3_3_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=3) (by decide) (by decide) true true cm3_3_1_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry4_4 : RBox := ⟨696603759878277757337123237275,696603759878277758050967540167⟩
lemma dentry4_4_contains : dentry4_4.Contains (S (columnVector node3 true) (node3,true)) := by
  have h0 := K_column_contains (n:=node3) (m:=3) (by decide) (by decide) true false cm3_3_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=3) (by decide) (by decide) true true cm3_3_1_1.contains
  have hh := S_column_derivative_contains (m:=node3) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry2_1 : RBox := ⟨11552892703545774298548951595,11552892703545774325348299103⟩
lemma dentry2_1_contains : dentry2_1.Contains (S (columnVector node3 false) (node4,false)) := by
  have h0 := K_column_contains (n:=node3) (m:=4) (by decide) (by decide) false false cm3_4_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=4) (by decide) (by decide) false true cm3_4_0_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry5_1 : RBox := ⟨(-85515720483106714613961869326),(-85515720483106714442684097804)⟩
lemma dentry5_1_contains : dentry5_1.Contains (S (columnVector node3 false) (node4,true)) := by
  have h0 := K_column_contains (n:=node3) (m:=4) (by decide) (by decide) false false cm3_4_0_0.contains
  have h1 := K_column_contains (n:=node3) (m:=4) (by decide) (by decide) false true cm3_4_0_1.contains
  have hh := S_column_derivative_contains (m:=node4) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry2_4 : RBox := ⟨(-46599334773430376018515334202),(-46599334773430375961386819313)⟩
lemma dentry2_4_contains : dentry2_4.Contains (S (columnVector node3 true) (node4,false)) := by
  have h0 := K_column_contains (n:=node3) (m:=4) (by decide) (by decide) true false cm3_4_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=4) (by decide) (by decide) true true cm3_4_1_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry5_4 : RBox := ⟨(-113965371204432533744771266896),(-113965371204432533377810928653)⟩
lemma dentry5_4_contains : dentry5_4.Contains (S (columnVector node3 true) (node4,true)) := by
  have h0 := K_column_contains (n:=node3) (m:=4) (by decide) (by decide) true false cm3_4_1_0.contains
  have h1 := K_column_contains (n:=node3) (m:=4) (by decide) (by decide) true true cm3_4_1_1.contains
  have hh := S_column_derivative_contains (m:=node4) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry0_2 : RBox := ⟨38513567412242708706244438853,38513567412242709174634148764⟩
lemma dentry0_2_contains : dentry0_2.Contains (S (columnVector node4 false) (node1,false)) := by
  have h0 := K_column_contains (n:=node4) (m:=1) (by decide) (by decide) false false cm4_1_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=1) (by decide) (by decide) false true cm4_1_0_1.contains
  have hh := S_column_value_contains (m:=node1) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry3_2 : RBox := ⟨227145133131591005392854971615,227145133131591008209757733306⟩
lemma dentry3_2_contains : dentry3_2.Contains (S (columnVector node4 false) (node1,true)) := by
  have h0 := K_column_contains (n:=node4) (m:=1) (by decide) (by decide) false false cm4_1_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=1) (by decide) (by decide) false true cm4_1_0_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry0_5 : RBox := ⟨(-35236824314615944648195425884),(-35236824314615944265946143652)⟩
lemma dentry0_5_contains : dentry0_5.Contains (S (columnVector node4 true) (node1,false)) := by
  have h0 := K_column_contains (n:=node4) (m:=1) (by decide) (by decide) true false cm4_1_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=1) (by decide) (by decide) true true cm4_1_1_1.contains
  have hh := S_column_value_contains (m:=node1) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry3_5 : RBox := ⟨13947539579869521084614770631,13947539579869523328647289424⟩
lemma dentry3_5_contains : dentry3_5.Contains (S (columnVector node4 true) (node1,true)) := by
  have h0 := K_column_contains (n:=node4) (m:=1) (by decide) (by decide) true false cm4_1_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=1) (by decide) (by decide) true true cm4_1_1_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry1_2 : RBox := ⟨(-50367220418701310824260347488),(-50367220418701310746671987499)⟩
lemma dentry1_2_contains : dentry1_2.Contains (S (columnVector node4 false) (node3,false)) := by
  have h0 := K_column_contains (n:=node4) (m:=3) (by decide) (by decide) false false cm4_3_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=3) (by decide) (by decide) false true cm4_3_0_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry4_2 : RBox := ⟨(-140501438496878817810768594789),(-140501438496878817401660852855)⟩
lemma dentry4_2_contains : dentry4_2.Contains (S (columnVector node4 false) (node3,true)) := by
  have h0 := K_column_contains (n:=node4) (m:=3) (by decide) (by decide) false false cm4_3_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=3) (by decide) (by decide) false true cm4_3_0_1.contains
  have hh := S_column_derivative_contains (m:=node3) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry1_5 : RBox := ⟨(-65563767968601851989120599895),(-65563767968601851839857744056)⟩
lemma dentry1_5_contains : dentry1_5.Contains (S (columnVector node4 true) (node3,false)) := by
  have h0 := K_column_contains (n:=node4) (m:=3) (by decide) (by decide) true false cm4_3_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=3) (by decide) (by decide) true true cm4_3_1_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry4_5 : RBox := ⟨617641971506705838665457646400,617641971506705839485675654971⟩
lemma dentry4_5_contains : dentry4_5.Contains (S (columnVector node4 true) (node3,true)) := by
  have h0 := K_column_contains (n:=node4) (m:=3) (by decide) (by decide) true false cm4_3_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=3) (by decide) (by decide) true true cm4_3_1_1.contains
  have hh := S_column_derivative_contains (m:=node3) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry2_2 : RBox := ⟨16906689819273463213216826620,16906689819273463235453873264⟩
lemma dentry2_2_contains : dentry2_2.Contains (S (columnVector node4 false) (node4,false)) := by
  have h0 := K_column_contains (n:=node4) (m:=4) (by decide) (by decide) false false cm4_4_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=4) (by decide) (by decide) false true cm4_4_0_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry5_2 : RBox := ⟨(-78390776109438054485518877398),(-78390776109438054339396429593)⟩
lemma dentry5_2_contains : dentry5_2.Contains (S (columnVector node4 false) (node4,true)) := by
  have h0 := K_column_contains (n:=node4) (m:=4) (by decide) (by decide) false false cm4_4_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=4) (by decide) (by decide) false true cm4_4_0_1.contains
  have hh := S_column_derivative_contains (m:=node4) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dentry2_5 : RBox := ⟨(-32138315292585356201983505971),(-32138315292585356140057198794)⟩
lemma dentry2_5_contains : dentry2_5.Contains (S (columnVector node4 true) (node4,false)) := by
  have h0 := K_column_contains (n:=node4) (m:=4) (by decide) (by decide) true false cm4_4_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=4) (by decide) (by decide) true true cm4_4_1_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  convert hh using 1
  decide +kernel
noncomputable def dentry5_5 : RBox := ⟨(-197772066238261852433723686168),(-197772066238261852031962127069)⟩
lemma dentry5_5_contains : dentry5_5.Contains (S (columnVector node4 true) (node4,true)) := by
  have h0 := K_column_contains (n:=node4) (m:=4) (by decide) (by decide) true false cm4_4_1_0.contains
  have h1 := K_column_contains (n:=node4) (m:=4) (by decide) (by decide) true true cm4_4_1_1.contains
  have hh := S_column_derivative_contains (m:=node4) h0 h1
  convert hh using 1
  decide +kernel
noncomputable def dEntries : Matrix (Fin 6) (Fin 6) RBox := ![![dentry0_0,dentry0_1,dentry0_2,dentry0_3,dentry0_4,dentry0_5],
![dentry1_0,dentry1_1,dentry1_2,dentry1_3,dentry1_4,dentry1_5],
![dentry2_0,dentry2_1,dentry2_2,dentry2_3,dentry2_4,dentry2_5],
![dentry3_0,dentry3_1,dentry3_2,dentry3_3,dentry3_4,dentry3_5],
![dentry4_0,dentry4_1,dentry4_2,dentry4_3,dentry4_4,dentry4_5],
![dentry5_0,dentry5_1,dentry5_2,dentry5_3,dentry5_4,dentry5_5]]
lemma dEntries_contains (i j : Fin 6) : (dEntries i j).Contains (Dmat i j) := by
  fin_cases i <;> fin_cases j
  · exact dentry0_0_contains
  · exact dentry0_1_contains
  · exact dentry0_2_contains
  · exact dentry0_3_contains
  · exact dentry0_4_contains
  · exact dentry0_5_contains
  · exact dentry1_0_contains
  · exact dentry1_1_contains
  · exact dentry1_2_contains
  · exact dentry1_3_contains
  · exact dentry1_4_contains
  · exact dentry1_5_contains
  · exact dentry2_0_contains
  · exact dentry2_1_contains
  · exact dentry2_2_contains
  · exact dentry2_3_contains
  · exact dentry2_4_contains
  · exact dentry2_5_contains
  · exact dentry3_0_contains
  · exact dentry3_1_contains
  · exact dentry3_2_contains
  · exact dentry3_3_contains
  · exact dentry3_4_contains
  · exact dentry3_5_contains
  · exact dentry4_0_contains
  · exact dentry4_1_contains
  · exact dentry4_2_contains
  · exact dentry4_3_contains
  · exact dentry4_4_contains
  · exact dentry4_5_contains
  · exact dentry5_0_contains
  · exact dentry5_1_contains
  · exact dentry5_2_contains
  · exact dentry5_3_contains
  · exact dentry5_4_contains
  · exact dentry5_5_contains
end SharpPlanar.Numerical

end OAI
