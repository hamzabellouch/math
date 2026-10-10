import OAI.Analysis.PlanarPacking.Certificate.Powers30
import OAI.Analysis.PlanarPacking.Certificate.KernelValues30
import OAI.Analysis.PlanarPacking.HighRuleBridge
import OAI.Analysis.PlanarPacking.Certificate.MomentPowers30

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
noncomputable def hk27_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_0 j i k)
lemma hk27_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_0 j i k).Contains (fullFactor false 27 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 0 (power27_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha27_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999677,1000000000000000000000000000431⟩,⟨(-431),431⟩⟩,⟨⟨(-81403453103),60193902703⟩,⟨999999999999999999929227690160,1000000000000000000070772309877⟩⟩,⟨⟨(-1000000000000000000193424181923),(-999999999999999999806575818095)⟩,⟨(-214614432606),172195331664⟩⟩,⟨⟨(-56385898307),120014549693⟩,⟨(-1000000000000000000088200224000),(-999999999999999999911799776027)⟩⟩,⟨⟨999999999999999999471081323067,1000000000000000000528918676871⟩,⟨(-486513685039),571351886994⟩⟩,⟨⟨(-718728105770),612680353424⟩,⟨999999999999999999334281766862,1000000000000000000665718233058⟩⟩,⟨⟨(-1000000000000000000176936340221),(-999999999999999999823063659887)⟩,⟨(-240564991661),113307688673⟩⟩]
lemma ha27_0_0_eq (j : Fin 7) : ha27_0_0 j = ((atomPoints j).direct.powBin 7 27).conj := by fin_cases j <;> decide +kernel
lemma ha27_0_0_contains (j : Fin 7) : (ha27_0_0 j).Contains (fullFactor false 27 0 ((j.val:ℝ)/6)) := by
  rw [ha27_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 27) ((j.val:ℝ)/6) 27 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 27 (by norm_num))
noncomputable def hk27_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_1 j i k)
lemma hk27_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_1 j i k).Contains (fullFactor false 27 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 1 (power27_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha27_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-523598775598298873115389628133),(-523598775598298873039610371885)⟩,⟨(-42622748375),31517453754⟩⟩,⟨⟨(-180322529647),224743708277⟩,⟨(-1047197551196597746359219996321),(-1047197551196597745950780003698)⟩⟩,⟨⟨1570796326794896619091455412160,1570796326794896619373544587882⟩,⟨(-88570761944),188518413820⟩⟩,⟨⟨(-1196636593864),1018951879193⟩,⟨2094395102393195491198901980131,2094395102393195493421098019738⟩⟩,⟨⟨(-2617993877991494367134512925283),(-2617993877991494363640487074509)⟩,⟨(-1881625780847),1603993414430⟩⟩,⟨⟨(-355966602331),755757210514⟩,⟨(-3141592653589793239025861906592),(-3141592653589793237904138093747)⟩⟩]
lemma ha27_0_1_eq (j : Fin 7) : ha27_0_1 j = ((ha27_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha27_0_1_contains (j : Fin 7) : (ha27_0_1 j).Contains (fullFactor false 27 1 ((j.val:ℝ)/6)) := by
  rw [ha27_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_0 j) false 27 0 j (ha27_0_0_contains j)
noncomputable def hk27_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_2 j i k)
lemma hk27_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_2 j i k).Contains (fullFactor false 27 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 2 (power27_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha27_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-8251250098),11158609431⟩,⟨(-137077838904018869716377898432),(-137077838904018869696102603223)⟩⟩,⟨⟨548311355616075478717158998658,548311355616075478932763007956⟩,⟨(-94416655736),117675530478⟩⟩,⟨⟨(-148062015981),69563313762⟩,⟨1233700550136169827243422601773,1233700550136169827468901913117⟩⟩,⟨⟨(-2193245422464301916466873797122),(-2193245422464301914132814229153)⟩,⟨(-1253114910767),1067043912679⟩⟩,⟨⟨(-2099622469659),2463042387465⟩,⟨(-3426945972600471744948294996133),(-3426945972600471740363717544867)⟩⟩,⟨⟨4934802200544679308535795225899,4934802200544679310313502834063⟩,⟨(-559151031404),1187140650225⟩⟩]
lemma ha27_0_2_eq (j : Fin 7) : ha27_0_2 j = ((ha27_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha27_0_2_contains (j : Fin 7) : (ha27_0_2 j).Contains (fullFactor false 27 2 ((j.val:ℝ)/6)) := by
  rw [ha27_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_1 j) false 27 1 j (ha27_0_1_contains j)
noncomputable def hk27_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_3 j i k)
lemma hk27_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_3 j i k).Contains (fullFactor false 27 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 3 (power27_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha27_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨23924596203935046429941097071,23924596203935046433555958009⟩,⟨(-1440114817),1947544746⟩⟩,⟨⟨(-41076509118),32957630227⟩,⟨191396769631480371416053604471,191396769631480371491922836167⟩⟩,⟨⟨(-645964097506246253717268673042),(-645964097506246253597151814115)⟩,⟨(-77525090281),36423265913⟩⟩,⟨⟨(-744937181585),874839243949⟩,⟨(-1531174157051842972449083189823),(-1531174157051842970814728335153)⟩⟩,⟨⟨2990574525491880801963407011719,2990574525491880805973724872956⟩,⟨(-1832266257221),2149409963873⟩⟩,⟨⟨(-1243170781842),585541590836⟩,⟨5167712780049970028318651751500,5167712780049970030196712146182⟩⟩]
lemma ha27_0_3_eq (j : Fin 7) : ha27_0_3 j = ((ha27_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha27_0_3_contains (j : Fin 7) : (ha27_0_3 j).Contains (fullFactor false 27 3 ((j.val:ℝ)/6)) := by
  rw [ha27_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_2 j) false 27 2 j (ha27_0_2_contains j)
noncomputable def hk27_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_4 j i k)
lemma hk27_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_4 j i k).Contains (fullFactor false 27 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 4 (power27_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha27_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-254933012),188510589⟩,⟨3131722319766024859478479308,3131722319766024859961632081⟩⟩,⟨⟨(-50107557116256397765531898976),(-50107557116256397745509883256)⟩,⟨(-10753804941),8628287417⟩⟩,⟨⟨(-14303383077),30444031762⟩,⟨(-253669507901048013661313128937),(-253669507901048013613335893617)⟩⟩,⟨⟨801720913860102363659185178961,801720913860102364517483336691⟩,⟨(-390048196176),458064756978⟩⟩,⟨⟨(-1406785531679),1199215461064⟩,⟨1957326449853765536009546176143,1957326449853765538640523442121⟩⟩,⟨⟨(-4058712126416768218941164413935),(-4058712126416768217453219947251)⟩,⟨(-976384048849),459883290036⟩⟩]
lemma ha27_0_4_eq (j : Fin 7) : ha27_0_4 j = ((ha27_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha27_0_4_contains (j : Fin 7) : (ha27_0_4 j).Contains (fullFactor false 27 4 ((j.val:ℝ)/6)) := by
  rw [ha27_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_3 j) false 27 3 j (ha27_0_3_contains j)
noncomputable def hk27_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_5 j i k)
lemma hk27_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_5 j i k).Contains (fullFactor false 27 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 5 (power27_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha27_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-327953194428670967601146731),(-327953194428670967549507182)⟩,⟨(-26696523),19740783⟩⟩,⟨⟨(-1807104291),2252271641⟩,⟨(-10494502221717470964523865706),(-10494502221717470960297059500)⟩⟩,⟨⟨79692626246167045113141369138,79692626246167045128467531649⟩,⟨(-4493540320),9564274653⟩⟩,⟨⟨(-191873716719),163383006354⟩,⟨335824071094959070616838776884,335824071094959070977430829693⟩⟩,⟨⟨(-1024853732589596774363316081468),(-1024853732589596772982477395623)⟩,⟨(-736591181917),627907747092⟩⟩,⟨⟨(-288953193098),613480190990⟩,⟨(-2550164039877345444337252665369),(-2550164039877345443394232160019)⟩⟩]
lemma ha27_0_5_eq (j : Fin 7) : ha27_0_5 j = ((ha27_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha27_0_5_contains (j : Fin 7) : (ha27_0_5 j).Contains (fullFactor false 27 5 ((j.val:ℝ)/6)) := by
  rw [ha27_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_4 j) false 27 4 j (ha27_0_4_contains j)
noncomputable def hk27_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_6 j i k)
lemma hk27_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_6 j i k).Contains (fullFactor false 27 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 6 (power27_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha27_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1722709),2329712⟩,⟨(-28619315176067161693856418),(-28619315176067161689258918)⟩⟩,⟨⟨1831636171268298347887917164,1831636171268298348631464296⟩,⟨(-315399199),393095558⟩⟩,⟨⟨(-2503921249),1176406105⟩,⟨20863480763352960871106144477,20863480763352960875184934963⟩⟩,⟨⟨(-117224714961171094351741961416),(-117224714961171094225498451998)⟩,⟨(-66976562096),57031428054⟩⟩,⟨⟨(-273976439639),321398534141⟩,⟨(-447176799626049401732552529895),(-447176799626049401128624584259)⟩⟩,⟨⟨1335262768854589495632307214456,1335262768854589496130321869822⟩,⟨(-151295538112),321217476857⟩⟩]
lemma ha27_0_6_eq (j : Fin 7) : ha27_0_6 j = ((ha27_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha27_0_6_contains (j : Fin 7) : (ha27_0_6 j).Contains (fullFactor false 27 6 ((j.val:ℝ)/6)) := by
  rw [ha27_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_5 j) false 27 5 j (ha27_0_5_contains j)
noncomputable def hk27_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_7 j i k)
lemma hk27_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_7 j i k).Contains (fullFactor false 27 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 7 (power27_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha27_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2140719769235797028041403,2140719769235797028392111⟩,⟨(-128859),174263⟩⟩,⟨⟨(-58806958),47183610⟩,⟨274012130462182019555691596,274012130462182019667798195⟩⟩,⟨⟨(-4681754135318688101175138014),(-4681754135318688100244957082)⟩,⟨(-561878615),263984913⟩⟩,⟨⟨(-17063763372),20039340519⟩,⟨(-35073552699159298529245152741),(-35073552699159298491361540464)⟩⟩,⟨⟨167243731971546642716233701805,167243731971546642942634578629⟩,⟨(-102466948813),120202770683⟩⟩,⟨⟨(-144162066500),67901278722⟩,⟨599264529320792076778178099690,599264529320792077003594072601⟩⟩]
lemma ha27_0_7_eq (j : Fin 7) : ha27_0_7 j = ((ha27_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha27_0_7_contains (j : Fin 7) : (ha27_0_7 j).Contains (fullFactor false 27 7 ((j.val:ℝ)/6)) := by
  rw [ha27_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_6 j) false 27 6 j (ha27_0_6_contains j)
noncomputable def hk27_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_8 j i k)
lemma hk27_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_8 j i k).Contains (fullFactor false 27 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 8 (power27_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha27_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-11406),8434⟩,⟨140109781258867029442229,140109781258867029465630⟩⟩,⟨⟨(-35868104002269959547600450),(-35868104002269959532811558)⟩,⟨(-7697813),6176321⟩⟩,⟨⟨(-51833317),110324609⟩,⟨(-919260274839426580340016120),(-919260274839426580154449424)⟩⟩,⟨⟨9182234624581109637319169688,9182234624581109647266304152⟩,⟨(-4467282805),5246287080⟩⟩,⟨⟨(-39336264721),33532230587⟩,⟨54730383304244933343309426708,54730383304244933417573152617⟩⟩,⟨⟨(-235330630358893204587926452710),(-235330630358893204498656726485)⟩,⟨(-56612311131),26664769801⟩⟩]
lemma ha27_0_8_eq (j : Fin 7) : ha27_0_8 j = ((ha27_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha27_0_8_contains (j : Fin 7) : (ha27_0_8 j).Contains (fullFactor false 27 8 ((j.val:ℝ)/6)) := by
  rw [ha27_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_7 j) false 27 7 j (ha27_0_7_contains j)
noncomputable def hk27_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_9 j i k)
lemma hk27_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_9 j i k).Contains (fullFactor false 27 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 9 (power27_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha27_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-8151256657387584305614),(-8151256657387584304226)⟩,⟨(-664),491⟩⟩,⟨⟨(-718648),895682⟩,⟨(-4173443408582443164986161),(-4173443408582443163252110)⟩⟩,⟨⟨160441184787359821857294943,160441184787359821890193142⟩,⟨(-9046621),19255277⟩⟩,⟨⟨(-1220866441),1039583915⟩,⟨2136803025194210898868195043,2136803025194210901189799999⟩⟩,⟨⟨(-15920423158960125606373799624),(-15920423158960125584720681143)⟩,⟨(-11442455581),9754130489⟩⟩,⟨⟨(-9307760547),19761424528⟩,⟨(-82145886611128228815068195316),(-82145886611128228783645703937)⟩⟩]
lemma ha27_0_9_eq (j : Fin 7) : ha27_0_9 j = ((ha27_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha27_0_9_contains (j : Fin 7) : (ha27_0_9 j).Contains (fullFactor false 27 9 ((j.val:ℝ)/6)) := by
  rw [ha27_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_8 j) false 27 8 j (ha27_0_8_contains j)
noncomputable def hk27_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_10 j i k)
lemma hk27_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_10 j i k).Contains (fullFactor false 27 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 10 (power27_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha27_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-26),35⟩,⟨(-426798800539562151492),(-426798800539562151417)⟩⟩,⟨⟨437041971752511642998009,437041971752511643180991⟩,⟨(-75257),93796⟩⟩,⟨⟨(-3024612),1421040⟩,⟨25202042373060605478618142,25202042373060605483866000⟩⟩,⟨⟨(-447530979074571922767478086),(-447530979074571922279817745)⟩,⟨(-255697670),217729947⟩⟩,⟨⟨(-2553625391),2995627867⟩,⟨(-4167957036519161638139748246),(-4167957036519161632457708064)⟩⟩,⟨⟨25806891390014060007814974277,25806891390014060017768786972⟩,⟨(-2924119216),6208234613⟩⟩]
lemma ha27_0_10_eq (j : Fin 7) : ha27_0_10 j = ((ha27_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha27_0_10_contains (j : Fin 7) : (ha27_0_10 j).Contains (fullFactor false 27 10 ((j.val:ℝ)/6)) := by
  rw [ha27_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_9 j) false 27 9 j (ha27_0_9_contains j)
noncomputable def hk27_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_11 j i k)
lemma hk27_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_11 j i k).Contains (fullFactor false 27 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 11 (power27_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha27_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨20315575399030665719,20315575399030665723⟩,⟨(-2),2⟩⟩,⟨⟨(-8930),7165⟩,⟨41606298417214803387950,41606298417214803405503⟩⟩,⟨⟨(-3598843235212085340868660),(-3598843235212085340107811)⟩,⟨(-431914),202925⟩⟩,⟨⟨(-41455685),48684723⟩,⟨(-85209699158455917403056616),(-85209699158455917309935073)⟩⟩,⟨⟨991971455030794223983288091,991971455030794225338768037⟩,⟨(-607761422),712957766⟩⟩,⟨⟨(-1773067660),835126496⟩,⟨7370430945714350775886775375,7370430945714350778753038444⟩⟩]
lemma ha27_0_11_eq (j : Fin 7) : ha27_0_11 j = ((ha27_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha27_0_11_contains (j : Fin 7) : (ha27_0_11 j).Contains (fullFactor false 27 11 ((j.val:ℝ)/6)) := by
  rw [ha27_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_10 j) false 27 10 j (ha27_0_10_contains j)
noncomputable def hk27_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_12 j i k)
lemma hk27_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_12 j i k).Contains (fullFactor false 27 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 12 (power27_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha27_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨886434200375614885,886434200375614886⟩⟩,⟨⟨(-3630834484738518571828),(-3630834484738518570284)⟩,⟨(-780),626⟩⟩,⟨⟨(-26563),56538⟩,⟨(-471087477881817150421816),(-471087477881817150320721)⟩⟩,⟨⟨14871898049488972058896422,14871898049488972075196537⟩,⟨(-7235382),8497088⟩⟩,⟨⟨(-155543256),132592974⟩,⟨216414599701077852759946155,216414599701077853056354876⟩⟩,⟨⟨(-1929574309403923048298978816),(-1929574309403923047542450873)⟩,⟨(-464188028),218635606⟩⟩]
lemma ha27_0_12_eq (j : Fin 7) : ha27_0_12 j = ((ha27_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha27_0_12_contains (j : Fin 7) : (ha27_0_12 j).Contains (fullFactor false 27 12 ((j.val:ℝ)/6)) := by
  rw [ha27_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_11 j) false 27 11 j (ha27_0_11_contains j)
noncomputable def hk27_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_13 j i k)
lemma hk27_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_13 j i k).Contains (fullFactor false 27 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 13 (power27_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha27_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-35702758612702237),(-35702758612702236)⟩,⟨(-1),1⟩⟩,⟨⟨(-51),63⟩,⟨(-292476998555256723089),(-292476998555256722963)⟩⟩,⟨⟨56921729219679268112109,56921729219679268124506⟩,⟨(-3210),6832⟩⟩,⟨⟨(-1368944),1165673⟩,⟨2395971572164663073713145,2395971572164663076346841⟩⟩,⟨⟨(-43582469009646285061073428),(-43582469009646285001242683)⟩,⟨(-31323946),26702123⟩⟩,⟨⟨(-52835694),112176131⟩,⟨(-466302805767612564517329966),(-466302805767612564333022398)⟩⟩]
lemma ha27_0_13_eq (j : Fin 7) : ha27_0_13 j = ((ha27_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha27_0_13_contains (j : Fin 7) : (ha27_0_13 j).Contains (fullFactor false 27 13 ((j.val:ℝ)/6)) := by
  rw [ha27_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_12 j) false 27 12 j (ha27_0_12_contains j)
noncomputable def hk27_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_14 j i k)
lemma hk27_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_14 j i k).Contains (fullFactor false 27 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 14 (power27_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha27_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1335280049649466),(-1335280049649465)⟩⟩,⟨⟨21877228333456835512,21877228333456835523⟩,⟨(-4),5⟩⟩,⟨⟨(-767),361⟩,⟨6386603083791852240451,6386603083791852241863⟩⟩,⟨⟨(-358436509015356793319080),(-358436509015356792923938)⟩,⟨(-204794),174385⟩⟩,⟨⟨(-4993286),5857565⟩,⟨(-8149902646786285762757717),(-8149902646786285751543451)⟩⟩,⟨⟨104638104924845707098269827,104638104924845707139961423⟩,⟨(-11856303),25172265⟩⟩]
lemma ha27_0_14_eq (j : Fin 7) : ha27_0_14 j = ((ha27_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha27_0_14_contains (j : Fin 7) : (ha27_0_14 j).Contains (fullFactor false 27 14 ((j.val:ℝ)/6)) := by
  rw [ha27_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_13 j) false 27 13 j (ha27_0_13_contains j)
noncomputable def hk27_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_15 j i k)
lemma hk27_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_15 j i k).Contains (fullFactor false 27 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 15 (power27_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha27_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨46610066605153,46610066605154⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1527318662517654886,1527318662517654888⟩⟩,⟨⟨(-668803510981146723331),(-668803510981146723180)⟩,⟨(-81),38⟩⟩,⟨⟨(-24349),28595⟩,⟨(-50047177933378515355685),(-50047177933378515300353)⟩⟩,⟨⟨1422426349034211491854961,1422426349034211493816748⟩,⟨(-871493),1022338⟩⟩,⟨⟨(-5272067),2483179⟩,⟨21915353447830215823230430,21915353447830215832032057⟩⟩]
lemma ha27_0_15_eq (j : Fin 7) : ha27_0_15 j = ((ha27_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha27_0_15_contains (j : Fin 7) : (ha27_0_15 j).Contains (fullFactor false 27 15 ((j.val:ℝ)/6)) := by
  rw [ha27_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_14 j) false 27 14 j (ha27_0_14_contains j)
noncomputable def hk27_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_16 j i k)
lemma hk27_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_16 j i k).Contains (fullFactor false 27 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 16 (power27_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha27_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨1525310862813,1525310862814⟩⟩,⟨⟨(-99962772705334444),(-99962772705334443)⟩,⟨(-1),1⟩⟩,⟨⟨(-4),8⟩,⟨(-65659631149794723631),(-65659631149794723615)⟩⟩,⟨⟨6551160272016798095197,6551160272016798102462⟩,⟨(-3188),3744⟩⟩,⟨⟨(-167280),142598⟩,⟨232743967104084891214970,232743967104084891536709⟩⟩,⟨⟨(-4303069587032947008220416),(-4303069587032947006478523)⟩,⟨(-1035168),487572⟩⟩]
lemma ha27_0_16_eq (j : Fin 7) : ha27_0_16 j = ((ha27_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha27_0_16_contains (j : Fin 7) : (ha27_0_16 j).Contains (fullFactor false 27 16 ((j.val:ℝ)/6)) := by
  rw [ha27_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_15 j) false 27 15 j (ha27_0_15_contains j)
noncomputable def hk27_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_17 j i k)
lemma hk27_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_17 j i k).Contains (fullFactor false 27 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 17 (power27_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha27_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-46979464717),(-46979464716)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-6157692399285196),(-6157692399285195)⟩⟩,⟨⟨6066935731106195666,6066935731106195668⟩,⟨(-1),1⟩⟩,⟨⟨(-462),393⟩,⟨807101058159109192978,807101058159109193877⟩⟩,⟨⟨(-35842487118702823511407),(-35842487118702823461745)⟩,⟨(-25762),21961⟩⟩,⟨⟨(-90104),191299⟩,⟨(-795205400147551278650678),(-795205400147551278326245)⟩⟩]
lemma ha27_0_17_eq (j : Fin 7) : ha27_0_17 j = ((ha27_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha27_0_17_contains (j : Fin 7) : (ha27_0_17 j).Contains (fullFactor false 27 17 ((j.val:ℝ)/6)) := by
  rw [ha27_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_16 j) false 27 16 j (ha27_0_16_contains j)
noncomputable def hk27_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_18 j i k)
lemma hk27_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_18 j i k).Contains (fullFactor false 27 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 18 (power27_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha27_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1366577234),(-1366577233)⟩⟩,⟨⟨358240022308519,358240022308520⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨529440020073462376,529440020073462377⟩⟩,⟨⟨(-93910472408044662792),(-93910472408044662686)⟩,⟨(-54),46⟩⟩,⟨⟨(-3195),3747⟩,⟨(-5213078436041832675295),(-5213078436041832668054)⟩⟩,⟨⟨138789524622137721118021,138789524622137721175088⟩,⟨(-15727),33388⟩⟩]
lemma ha27_0_18_eq (j : Fin 7) : ha27_0_18 j = ((ha27_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha27_0_18_contains (j : Fin 7) : (ha27_0_18 j).Contains (fullFactor false 27 18 ((j.val:ℝ)/6)) := by
  rw [ha27_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_17 j) false 27 17 j (ha27_0_17_contains j)
noncomputable def hk27_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_19 j i k)
lemma hk27_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_19 j i k).Contains (fullFactor false 27 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 19 (power27_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha27_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨37659903,37659904⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨19744635479057,19744635479058⟩⟩,⟨⟨(-43770654673137423),(-43770654673137422)⟩,⟨(-1),1⟩⟩,⟨⟨(-6),6⟩,⟨(-10351875446044213768),(-10351875446044213755)⟩⟩,⟨⟨718305654265631154550,718305654265631155551⟩,⟨(-441),517⟩⟩,⟨⟨(-5521),2601⟩,⟨22948428997269873105776,22948428997269873115286⟩⟩]
lemma ha27_0_19_eq (j : Fin 7) : ha27_0_19 j = ((ha27_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha27_0_19_contains (j : Fin 7) : (ha27_0_19 j).Contains (fullFactor false 27 19 ((j.val:ℝ)/6)) := by
  rw [ha27_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_18 j) false 27 18 j (ha27_0_18_contains j)
noncomputable def hk27_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_20 j i k)
lemma hk27_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_20 j i k).Contains (fullFactor false 27 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 20 (power27_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha27_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨985933,985934⟩⟩,⟨⟨(-1033826696147),(-1033826696146)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-3437739179098608),(-3437739179098606)⟩⟩,⟨⟨1084045861738968866,1084045861738968868⟩,⟨(-1),1⟩⟩,⟨⟨(-68),58⟩,⟨94025990269704865148,94025990269704865281⟩⟩,⟨⟨(-3604730797462500934667),(-3604730797462500933160)⟩,⟨(-868),409⟩⟩]
lemma ha27_0_20_eq (j : Fin 7) : ha27_0_20 j = ((ha27_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha27_0_20_contains (j : Fin 7) : (ha27_0_20 j).Contains (fullFactor false 27 20 ((j.val:ℝ)/6)) := by
  rw [ha27_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_19 j) false 27 19 j (ha27_0_19_contains j)
noncomputable def hk27_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_21 j i k)
lemma hk27_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_21 j i k).Contains (fullFactor false 27 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 21 (power27_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha27_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-24583),(-24582)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-51553370694),(-51553370693)⟩⟩,⟨⟨257142289286047,257142289286048⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨108115254456938454,108115254456938455⟩⟩,⟨⟨(-11721879376103578832),(-11721879376103578814)⟩,⟨(-9),8⟩⟩,⟨⟨(-62),130⟩,⟨(-539266466260812849058),(-539266466260812848830)⟩⟩]
lemma ha27_0_21_eq (j : Fin 7) : ha27_0_21 j = ((ha27_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha27_0_21_contains (j : Fin 7) : (ha27_0_21 j).Contains (fullFactor false 27 21 ((j.val:ℝ)/6)) := by
  rw [ha27_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_20 j) false 27 20 j (ha27_0_20_contains j)
noncomputable def hk27_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_22 j i k)
lemma hk27_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_22 j i k).Contains (fullFactor false 27 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 22 (power27_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha27_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-586),(-585)⟩⟩,⟨⟨2453934706,2453934707⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨18359916521552,18359916521553⟩⟩,⟨⟨(-10292548155845728),(-10292548155845727)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),2⟩,⟨(-1394900383872451221),(-1394900383872451218)⟩⟩,⟨⟨77007071306013533782,77007071306013533816⟩,⟨(-9),19⟩⟩]
lemma ha27_0_22_eq (j : Fin 7) : ha27_0_22 j = ((ha27_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha27_0_22_contains (j : Fin 7) : (ha27_0_22 j).Contains (fullFactor false 27 22 ((j.val:ℝ)/6)) := by
  rw [ha27_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_21 j) false 27 21 j (ha27_0_21_contains j)
noncomputable def hk27_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_23 j i k)
lemma hk27_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_23 j i k).Contains (fullFactor false 27 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 23 (power27_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha27_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨13,14⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨111728452,111728453⟩⟩,⟨⟨(-1253899540536),(-1253899540535)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-937246193423888),(-937246193423887)⟩⟩,⟨⟨158775681103741856,158775681103741858⟩,⟨(-1),1⟩⟩,⟨⟨(-3),2⟩,⟨10518471716932064452,10518471716932064458⟩⟩]
lemma ha27_0_23_eq (j : Fin 7) : ha27_0_23 j = ((ha27_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha27_0_23_contains (j : Fin 7) : (ha27_0_23 j).Contains (fullFactor false 27 23 ((j.val:ℝ)/6)) := by
  rw [ha27_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_22 j) false 27 22 j (ha27_0_22_contains j)
noncomputable def hk27_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_24 j i k)
lemma hk27_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_24 j i k).Contains (fullFactor false 27 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 24 (power27_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha27_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-4875074),(-4875073)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-82067533019),(-82067533018)⟩⟩,⟨⟨81790159885152,81790159885153⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨17319740045980248,17319740045980250⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha27_0_24_eq (j : Fin 7) : ha27_0_24 j = ((ha27_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha27_0_24_contains (j : Fin 7) : (ha27_0_24 j).Contains (fullFactor false 27 24 ((j.val:ℝ)/6)) := by
  rw [ha27_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_23 j) false 27 23 j (ha27_0_23_contains j)
noncomputable def hk27_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_25 j i k)
lemma hk27_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_25 j i k).Contains (fullFactor false 27 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 25 (power27_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha27_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-204207),(-204206)⟩⟩,⟨⟨5156455176,5156455177⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨6852036411496,6852036411497⟩⟩,⟨⟨(-1813718936351217),(-1813718936351216)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha27_0_25_eq (j : Fin 7) : ha27_0_25 j = ((ha27_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha27_0_25_contains (j : Fin 7) : (ha27_0_25 j).Contains (fullFactor false 27 25 ((j.val:ℝ)/6)) := by
  rw [ha27_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_24 j) false 27 24 j (ha27_0_24_contains j)
noncomputable def hk27_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_26 j i k)
lemma hk27_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_26 j i k).Contains (fullFactor false 27 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 26 (power27_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha27_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨8224,8225⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨311528494,311528495⟩⟩,⟨⟨(-551956596218),(-551956596217)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-182627118144798),(-182627118144797)⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha27_0_26_eq (j : Fin 7) : ha27_0_26 j = ((ha27_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha27_0_26_contains (j : Fin 7) : (ha27_0_26 j).Contains (fullFactor false 27 26 ((j.val:ℝ)/6)) := by
  rw [ha27_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_25 j) false 27 25 j (ha27_0_25_contains j)
noncomputable def hk27_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_27 j i k)
lemma hk27_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_27 j i k).Contains (fullFactor false 27 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 27 (power27_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha27_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨318,320⟩⟩,⟨⟨(-18123994),(-18123993)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-42815377477),(-42815377475)⟩⟩,⟨⟨17708025083641,17708025083642⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha27_0_27_eq (j : Fin 7) : ha27_0_27 j = ((ha27_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha27_0_27_contains (j : Fin 7) : (ha27_0_27 j).Contains (fullFactor false 27 27 ((j.val:ℝ)/6)) := by
  rw [ha27_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_26 j) false 27 26 j (ha27_0_26_contains j)
noncomputable def hk27_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_28 j i k)
lemma hk27_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_28 j i k).Contains (fullFactor false 27 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 28 (power27_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha27_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-12),(-11)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1016754),(-1016753)⟩⟩,⟨⟨3202582746,3202582747⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1655696473581,1655696473582⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha27_0_28_eq (j : Fin 7) : ha27_0_28 j = ((ha27_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha27_0_28_contains (j : Fin 7) : (ha27_0_28 j).Contains (fullFactor false 27 28 ((j.val:ℝ)/6)) := by
  rw [ha27_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_27 j) false 27 27 j (ha27_0_27_contains j)
noncomputable def hk27_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_29 j i k)
lemma hk27_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_29 j i k).Contains (fullFactor false 27 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 29 (power27_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha27_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨55072,55073⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨231292193,231292194⟩⟩,⟨⟨(-149469076954),(-149469076953)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha27_0_29_eq (j : Fin 7) : ha27_0_29 j = ((ha27_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha27_0_29_contains (j : Fin 7) : (ha27_0_29 j).Contains (fullFactor false 27 29 ((j.val:ℝ)/6)) := by
  rw [ha27_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_28 j) false 27 28 j (ha27_0_28_contains j)
noncomputable def hk27_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power27 j i k).conj.mul (mpower0_30 j i k)
lemma hk27_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_0_30 j i k).Contains (fullFactor false 27 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power27 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 30 (power27_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha27_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨2883,2884⟩⟩,⟨⟨(-16147242),(-16147241)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-13043637614),(-13043637613)⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha27_0_30_eq (j : Fin 7) : ha27_0_30 j = ((ha27_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha27_0_30_contains (j : Fin 7) : (ha27_0_30 j).Contains (fullFactor false 27 30 ((j.val:ℝ)/6)) := by
  rw [ha27_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_0_29 j) false 27 29 j (ha27_0_29_contains j)
noncomputable def hk27_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_0 j i k)
lemma hk27_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_0 j i k).Contains (fullFactor true 27 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 0 (kernel27_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha27_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),3⟩,⟨(-2),4⟩⟩,⟨⟨0,4⟩,⟨(-2),2⟩⟩,⟨⟨(-2),2⟩,⟨0,3⟩⟩,⟨⟨(-946122032372),(-946122032369)⟩,⟨2344393842845,2344393842848⟩⟩,⟨⟨(-4914715484280113312030),(-4914715484280113277429)⟩,⟨(-4823446996496663396948),(-4823446996496663362281)⟩⟩,⟨⟨(-3163347492825092488356998232),(-3163347492825092453738357979)⟩,⟨(-5947311263201831421663297862),(-5947311263201831386929852948)⟩⟩]
lemma ha27_1_0_eq (j : Fin 7) : ha27_1_0 j = atomKernel27_0 j := by fin_cases j <;> decide +kernel
lemma ha27_1_0_contains (j : Fin 7) : (ha27_1_0 j).Contains (fullFactor true 27 0 ((j.val:ℝ)/6)) := by
  rw [ha27_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel27_0_contains j
noncomputable def hk27_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_1 j i k)
lemma hk27_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_1 j i k).Contains (fullFactor true 27 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 1 (kernel27_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha27_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-31),46⟩,⟨(-42),31⟩⟩,⟨⟨(-30),11⟩,⟨(-31),10⟩⟩,⟨⟨(-6),21⟩,⟨(-19),11⟩⟩,⟨⟨12264786356508,12264786356528⟩,⟨818481221881,818481221900⟩⟩,⟨⟨(-16243750035431970811935),(-16243750035431970645865)⟩,⟨23475245713674834422464,23475245713674834588311⟩⟩,⟨⟨(-20881903462514637627417506508),(-20881903462514637495423423685)⟩,⟨12539676748978747560769434746,12539676748978747692340176601⟩⟩]
lemma ha27_1_1_eq (j : Fin 7) : ha27_1_1 j = ((ha27_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha27_1_1_contains (j : Fin 7) : (ha27_1_1 j).Contains (fullFactor true 27 1 ((j.val:ℝ)/6)) := by
  rw [ha27_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_0 j) true 27 0 j (ha27_1_0_contains j)
noncomputable def hk27_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_2 j i k)
lemma hk27_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_2 j i k).Contains (fullFactor true 27 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 2 (kernel27_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha27_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-255),177⟩,⟨(-205),219⟩⟩,⟨⟨(-107),100⟩,⟨(-53),154⟩⟩,⟨⟨(-79),37⟩,⟨(-70),43⟩⟩,⟨⟨(-7402074394800),(-7402074394740)⟩,⟨(-28951735634038),(-28951735633976)⟩⟩,⟨⟨53671941643325120508479,53671941643325120905900⟩,⟨24913396934018834537390,24913396934018834935149⟩⟩,⟨⟨24601082153761121970449348705,24601082153761122220472829581⟩,⟨36525239988765613792927511352,36525239988765614043721044534⟩⟩]
lemma ha27_1_2_eq (j : Fin 7) : ha27_1_2 j = ((ha27_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha27_1_2_contains (j : Fin 7) : (ha27_1_2 j).Contains (fullFactor true 27 2 ((j.val:ℝ)/6)) := by
  rw [ha27_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_1 j) true 27 1 j (ha27_1_1_contains j)
noncomputable def hk27_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_3 j i k)
lemma hk27_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_3 j i k).Contains (fullFactor true 27 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 3 (kernel27_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha27_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-707),924⟩,⟨(-779),840⟩⟩,⟨⟨(-256),440⟩,⟨(-425),271⟩⟩,⟨⟨(-155),148⟩,⟨(-104),201⟩⟩,⟨⟨(-40846641540932),(-40846641540805)⟩,⟨26023234417691,26023234417816⟩⟩,⟨⟨21325727650937897969276,21325727650937898604382⟩,⟨(-78937467174387176132642),(-78937467174387175497815)⟩⟩,⟨⟨42424721652547976666625516367,42424721652547976984293603254⟩,⟨(-31897871684604996148844397440),(-31897871684604995832098315828)⟩⟩]
lemma ha27_1_3_eq (j : Fin 7) : ha27_1_3 j = ((ha27_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha27_1_3_contains (j : Fin 7) : (ha27_1_3 j).Contains (fullFactor true 27 3 ((j.val:ℝ)/6)) := by
  rw [ha27_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_2 j) true 27 2 j (ha27_1_2_contains j)
noncomputable def hk27_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_4 j i k)
lemma hk27_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_4 j i k).Contains (fullFactor true 27 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 4 (kernel27_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha27_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2495),2136⟩,⟨(-2469),2151⟩⟩,⟨⟨(-1089),665⟩,⟨(-901),853⟩⟩,⟨⟨(-238),367⟩,⟨(-332),272⟩⟩,⟨⟨45531070962301,45531070962495⟩,⟨37319141584397,37319141584592⟩⟩,⟨⟨(-84375684834499056560829),(-84375684834499055800368)⟩,⟨(-7881463737110887351982),(-7881463737110886591440)⟩⟩,⟨⟨(-30787569376714149173502672879),(-30787569376714148872547685384)⟩,⟨(-36801801054040890938650385258),(-36801801054040890636877656915)⟩⟩]
lemma ha27_1_4_eq (j : Fin 7) : ha27_1_4 j = ((ha27_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha27_1_4_contains (j : Fin 7) : (ha27_1_4 j).Contains (fullFactor true 27 4 ((j.val:ℝ)/6)) := by
  rw [ha27_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_3 j) true 27 3 j (ha27_1_3_contains j)
noncomputable def hk27_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_5 j i k)
lemma hk27_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_5 j i k).Contains (fullFactor true 27 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 5 (kernel27_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha27_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-5111),5425⟩,⟨(-4887),5641⟩⟩,⟨⟨(-1583),1951⟩,⟨(-1525),2009⟩⟩,⟨⟨(-547),413⟩,⟨(-529),432⟩⟩,⟨⟨20683645717876,20683645718116⟩,⟨(-53380971619739),(-53380971619500)⟩⟩,⟨⟨5445621449894507270751,5445621449894507999338⟩,⟨70050121121503144302193,70050121121503145030889⟩⟩,⟨⟨(-25422235342047785484843690583),(-25422235342047785255511306948)⟩,⟨23617022460446931986099165676,23617022460446932214858575723⟩⟩]
lemma ha27_1_5_eq (j : Fin 7) : ha27_1_5 j = ((ha27_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha27_1_5_contains (j : Fin 7) : (ha27_1_5 j).Contains (fullFactor true 27 5 ((j.val:ℝ)/6)) := by
  rw [ha27_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_4 j) true 27 4 j (ha27_1_4_contains j)
noncomputable def hk27_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_6 j i k)
lemma hk27_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_6 j i k).Contains (fullFactor true 27 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 6 (kernel27_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha27_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-9960),10026⟩,⟨(-10570),9412⟩⟩,⟨⟨(-2910),3024⟩,⟨(-3324),2611⟩⟩,⟨⟨(-646),626⟩,⟨(-556),716⟩⟩,⟨⟨(-46327101376852),(-46327101376606)⟩,⟨(-2444503294417),(-2444503294171)⟩⟩,⟨⟨47056683949276816179125,47056683949276816760961⟩,⟨(-11930604814499768636747),(-11930604814499768055088)⟩⟩,⟨⟨15009216909272499496012443215,15009216909272499640913335223⟩,⟨14560951043451159946126790752,14560951043451160091357866755⟩⟩]
lemma ha27_1_6_eq (j : Fin 7) : ha27_1_6 j = ((ha27_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha27_1_6_contains (j : Fin 7) : (ha27_1_6 j).Contains (fullFactor true 27 6 ((j.val:ℝ)/6)) := by
  rw [ha27_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_5 j) true 27 5 j (ha27_1_5_contains j)
noncomputable def hk27_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_7 j i k)
lemma hk27_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_7 j i k).Contains (fullFactor true 27 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 7 (kernel27_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha27_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-16595),15907⟩,⟨(-15633),16866⟩⟩,⟨⟨(-4573),3968⟩,⟨(-4062),4479⟩⟩,⟨⟨(-659),784⟩,⟨(-747),697⟩⟩,⟨⟨8415499052594,8415499052811⟩,⟨31105000244660,31105000244877⟩⟩,⟨⟨(-11697473159557446073521),(-11697473159557445675477)⟩,⟨(-26262528493742091003563),(-26262528493742090605379)⟩⟩,⟨⟨7108806052104249030070971144,7108806052104249108902122835⟩,⟨(-8133261670497586310531484572),(-8133261670497586231861106979)⟩⟩]
lemma ha27_1_7_eq (j : Fin 7) : ha27_1_7 j = ((ha27_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha27_1_7_contains (j : Fin 7) : (ha27_1_7 j).Contains (fullFactor true 27 7 ((j.val:ℝ)/6)) := by
  rw [ha27_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_6 j) true 27 6 j (ha27_1_6_contains j)
noncomputable def hk27_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_8 j i k)
lemma hk27_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_8 j i k).Contains (fullFactor true 27 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 8 (kernel27_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha27_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-22509),23741⟩,⟨(-23555),22694⟩⟩,⟨⟨(-5058),5698⟩,⟨(-5312),5444⟩⟩,⟨⟨(-755),679⟩,⟨(-748),686⟩⟩,⟨⟨16369035532782,16369035532949⟩,⟨(-10751834706917),(-10751834706749)⟩⟩,⟨⟨(-12381451793633135993903),(-12381451793633135755475)⟩,⟨8285558982791051397800,8285558982791051636149⟩⟩,⟨⟨(-3838033003297572698839076306),(-3838033003297572661466463003)⟩,⟨(-3017859241834758516627504289),(-3017859241834758479187490069)⟩⟩]
lemma ha27_1_8_eq (j : Fin 7) : ha27_1_8 j = ((ha27_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha27_1_8_contains (j : Fin 7) : (ha27_1_8 j).Contains (fullFactor true 27 8 ((j.val:ℝ)/6)) := by
  rw [ha27_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_7 j) true 27 7 j (ha27_1_7_contains j)
noncomputable def hk27_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_9 j i k)
lemma hk27_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_9 j i k).Contains (fullFactor true 27 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 9 (kernel27_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha27_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-29954),28549⟩,⟨(-29139),29363⟩⟩,⟨⟨(-6157),5883⟩,⟨(-6239),5801⟩⟩,⟨⟨(-639),627⟩,⟨(-602),664⟩⟩,⟨⟨(-8275364874283),(-8275364874167)⟩,⟨(-6592433908578),(-6592433908463)⟩⟩,⟨⟨4729920017002173327627,4729920017002173454493⟩,⟨4971815004102221930309,4971815004102222057210⟩⟩,⟨⟨(-1130765330366744530449225351),(-1130765330366744514643510993)⟩,⟨1602878962634490966017942454,1602878962634490981799013112⟩⟩]
lemma ha27_1_9_eq (j : Fin 7) : ha27_1_9 j = ((ha27_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha27_1_9_contains (j : Fin 7) : (ha27_1_9 j).Contains (fullFactor true 27 9 ((j.val:ℝ)/6)) := by
  rw [ha27_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_8 j) true 27 8 j (ha27_1_8_contains j)
noncomputable def hk27_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_10 j i k)
lemma hk27_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_10 j i k).Contains (fullFactor true 27 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 10 (kernel27_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha27_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-32720),33881⟩,⟨(-33125),33476⟩⟩,⟨⟨(-6110),6020⟩,⟨(-5886),6243⟩⟩,⟨⟨(-485),521⟩,⟨(-509),497⟩⟩,⟨⟨(-1791684584454),(-1791684584382)⟩,⟨4822198360220,4822198360292⟩⟩,⟨⟨1698002964756471452403,1698002964756471513190⟩,⟨(-2282479785836676778143),(-2282479785836676717369)⟩⟩,⟨⟨600036526949021140589603125,600036526949021146586888008⟩,⟨378224509262836843606915678,378224509262836849612122280⟩⟩]
lemma ha27_1_10_eq (j : Fin 7) : ha27_1_10 j = ((ha27_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha27_1_10_contains (j : Fin 7) : (ha27_1_10 j).Contains (fullFactor true 27 10 ((j.val:ℝ)/6)) := by
  rw [ha27_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_9 j) true 27 9 j (ha27_1_9_contains j)
noncomputable def hk27_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_11 j i k)
lemma hk27_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_11 j i k).Contains (fullFactor true 27 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 11 (kernel27_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha27_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-34809),34119⟩,⟨(-34782),34145⟩⟩,⟨⟨(-5451),5658⟩,⟨(-5613),5496⟩⟩,⟨⟨(-371),356⟩,⟨(-370),357⟩⟩,⟨⟨2272140466384,2272140466425⟩,⟨88201273073,88201273114⟩⟩,⟨⟨(-956410697087398034270),(-956410697087398007803)⟩,⟨(-484480252286519094184),(-484480252286519067714)⟩⟩,⟨⟨113918880017806356639463334,113918880017806358713626403⟩,⟨(-203433455236507935165474206),(-203433455236507933093556687)⟩⟩]
lemma ha27_1_11_eq (j : Fin 7) : ha27_1_11 j = ((ha27_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha27_1_11_contains (j : Fin 7) : (ha27_1_11 j).Contains (fullFactor true 27 11 ((j.val:ℝ)/6)) := by
  rw [ha27_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_10 j) true 27 10 j (ha27_1_10_contains j)
noncomputable def hk27_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_12 j i k)
lemma hk27_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_12 j i k).Contains (fullFactor true 27 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 12 (kernel27_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha27_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-32574),32817⟩,⟨(-32385),33006⟩⟩,⟨⟨(-4731),4596⟩,⟨(-4684),4643⟩⟩,⟨⟨(-242),240⟩,⟨(-236),246⟩⟩,⟨⟨(-252967816419),(-252967816397)⟩,⟨(-885910064700),(-885910064678)⟩⟩,⟨⟨(-108803365329629026293),(-108803365329629015727)⟩,⟨354036892833176947317,354036892833176957883⟩⟩,⟨⟨(-62999536180746694972691122),(-62999536180746694316555532)⟩,⟨(-31097054985528417558369122),(-31097054985528416901674224)⟩⟩]
lemma ha27_1_12_eq (j : Fin 7) : ha27_1_12 j = ((ha27_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha27_1_12_contains (j : Fin 7) : (ha27_1_12 j).Contains (fullFactor true 27 12 ((j.val:ℝ)/6)) := by
  rw [ha27_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_11 j) true 27 11 j (ha27_1_11_contains j)
noncomputable def hk27_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_13 j i k)
lemma hk27_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_13 j i k).Contains (fullFactor true 27 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 13 (kernel27_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha27_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-28615),28649⟩,⟨(-28850),28414⟩⟩,⟨⟨(-3597),3632⟩,⟨(-3580),3649⟩⟩,⟨⟨(-145),150⟩,⟨(-148),147⟩⟩,⟨⟨(-285350654931),(-285350654920)⟩,⟨193167547318,193167547329⟩⟩,⟨⟨117152021078031221078,117152021078031224972⟩,⟨15011076187391322393,15011076187391326287⟩⟩,⟨⟨(-7727895466708578649946224),(-7727895466708578458027588)⟩,⟨17948627991027455320342923,17948627991027455512141019⟩⟩]
lemma ha27_1_13_eq (j : Fin 7) : ha27_1_13 j = ((ha27_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha27_1_13_contains (j : Fin 7) : (ha27_1_13 j).Contains (fullFactor true 27 13 ((j.val:ℝ)/6)) := by
  rw [ha27_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_12 j) true 27 12 j (ha27_1_12_contains j)
noncomputable def hk27_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_14 j i k)
lemma hk27_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_14 j i k).Contains (fullFactor true 27 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 14 (kernel27_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha27_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-23350),23215⟩,⟨(-23168),23397⟩⟩,⟨⟨(-2595),2608⟩,⟨(-2620),2583⟩⟩,⟨⟨(-85),83⟩,⟨(-85),83⟩⟩,⟨⟨94631424214,94631424219⟩,⟨73257089493,73257089499⟩⟩,⟨⟨(-1513290604448923457),(-1513290604448922123)⟩,⟨(-34940933155705711228),(-34940933155705709894)⟩⟩,⟨⟨4733146848865016657736977,4733146848865016709796695⟩,⟨1752525548301550207148789,1752525548301550259230027⟩⟩]
lemma ha27_1_14_eq (j : Fin 7) : ha27_1_14 j = ((ha27_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha27_1_14_contains (j : Fin 7) : (ha27_1_14 j).Contains (fullFactor true 27 14 ((j.val:ℝ)/6)) := by
  rw [ha27_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_13 j) true 27 13 j (ha27_1_13_contains j)
noncomputable def hk27_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_15 j i k)
lemma hk27_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_15 j i k).Contains (fullFactor true 27 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 15 (kernel27_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha27_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-17608),17733⟩,⟨(-17712),17629⟩⟩,⟨⟨(-1756),1739⟩,⟨(-1744),1751⟩⟩,⟨⟨(-45),45⟩,⟨(-44),45⟩⟩,⟨⟨13003108156,13003108159⟩,⟨(-36547117406),(-36547117403)⟩⟩,⟨⟨(-9445215840435310910),(-9445215840435310483)⟩,⟨2052754355442755580,2052754355442756007⟩⟩,⟨⟨362643768628142655287578,362643768628142668478587⟩,⟨(-1161372941066681208714626),(-1161372941066681195526364)⟩⟩]
lemma ha27_1_15_eq (j : Fin 7) : ha27_1_15 j = ((ha27_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha27_1_15_contains (j : Fin 7) : (ha27_1_15 j).Contains (fullFactor true 27 15 ((j.val:ℝ)/6)) := by
  rw [ha27_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_14 j) true 27 14 j (ha27_1_14_contains j)
noncomputable def hk27_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_16 j i k)
lemma hk27_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_16 j i k).Contains (fullFactor true 27 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 16 (kernel27_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha27_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-12613),12534⟩,⟨(-12568),12579⟩⟩,⟨⟨(-1097),1104⟩,⟨(-1099),1102⟩⟩,⟨⟨(-23),23⟩,⟨(-23),23⟩⟩,⟨⟨(-11784476968),(-11784476966)⟩,⟨(-293269306),(-293269304)⟩⟩,⟨⟨939901395534247847,939901395534247976⟩,⟨2321296101448219740,2321296101448219869⟩⟩,⟨⟨(-266365172967058666868116),(-266365172967058663736012)⟩,⟨(-68215074928604220346403),(-68215074928604217214255)⟩⟩]
lemma ha27_1_16_eq (j : Fin 7) : ha27_1_16 j = ((ha27_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha27_1_16_contains (j : Fin 7) : (ha27_1_16 j).Contains (fullFactor true 27 16 ((j.val:ℝ)/6)) := by
  rw [ha27_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_15 j) true 27 15 j (ha27_1_15_contains j)
noncomputable def hk27_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_17 j i k)
lemma hk27_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_17 j i k).Contains (fullFactor true 27 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 17 (kernel27_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha27_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-8401),8439⟩,⟨(-8414),8427⟩⟩,⟨⟨(-653),652⟩,⟨(-654),651⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨970751895,970751897⟩,⟨3228739047,3228739048⟩⟩,⟨⟨518894381187749601,518894381187749638⟩,⟨(-322039763790166568),(-322039763790166530)⟩⟩,⟨⟨(-11547654698470252306706),(-11547654698470251606744)⟩,⟨57332973457403290230006,57332973457403290930087⟩⟩]
lemma ha27_1_17_eq (j : Fin 7) : ha27_1_17 j = ((ha27_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha27_1_17_contains (j : Fin 7) : (ha27_1_17 j).Contains (fullFactor true 27 17 ((j.val:ℝ)/6)) := by
  rw [ha27_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_16 j) true 27 16 j (ha27_1_16_contains j)
noncomputable def hk27_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_18 j i k)
lemma hk27_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_18 j i k).Contains (fullFactor true 27 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 18 (kernel27_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha27_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-5333),5319⟩,⟨(-5333),5319⟩⟩,⟨⟨(-366),365⟩,⟨(-365),366⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨746983575,746983577⟩,⟨(-520975214),(-520975212)⟩⟩,⟨⟨(-93393760977968894),(-93393760977968883)⟩,⟨(-105167940671800377),(-105167940671800366)⟩⟩,⟨⟨11622177882178536833071,11622177882178536980856⟩,⟨1718515393317336430833,1718515393317336578567⟩⟩]
lemma ha27_1_18_eq (j : Fin 7) : ha27_1_18 j = ((ha27_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha27_1_18_contains (j : Fin 7) : (ha27_1_18 j).Contains (fullFactor true 27 18 ((j.val:ℝ)/6)) := by
  rw [ha27_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_17 j) true 27 17 j (ha27_1_17_contains j)
noncomputable def hk27_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_19 j i k)
lemma hk27_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_19 j i k).Contains (fullFactor true 27 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 19 (kernel27_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha27_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-3190),3193⟩,⟨(-3187),3196⟩⟩,⟨⟨(-194),195⟩,⟨(-194),194⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-186255066),(-186255064)⟩,⟨(-140083838),(-140083836)⟩⟩,⟨⟨(-19150761848269666),(-19150761848269662)⟩,⟨23979551162709931,23979551162709935⟩⟩,⟨⟨211750974274149593096,211750974274149622636⟩,⟨(-2225825176695200406198),(-2225825176695200376643)⟩⟩]
lemma ha27_1_19_eq (j : Fin 7) : ha27_1_19 j = ((ha27_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha27_1_19_contains (j : Fin 7) : (ha27_1_19 j).Contains (fullFactor true 27 19 ((j.val:ℝ)/6)) := by
  rw [ha27_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_18 j) true 27 18 j (ha27_1_18_contains j)
noncomputable def hk27_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_20 j i k)
lemma hk27_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_20 j i k).Contains (fullFactor true 27 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 20 (kernel27_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha27_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-1817),1817⟩,⟨(-1819),1815⟩⟩,⟨⟨(-98),98⟩,⟨(-98),98⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-18247151),(-18247149)⟩,⟨53638666,53638668⟩⟩,⟨⟨5572577170113712,5572577170113714⟩,⟨3067380642143704,3067380642143706⟩⟩,⟨⟨(-403863693054580048447),(-403863693054580042831)⟩,⟨(-17334381147100334316),(-17334381147100328704)⟩⟩]
lemma ha27_1_20_eq (j : Fin 7) : ha27_1_20 j = ((ha27_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha27_1_20_contains (j : Fin 7) : (ha27_1_20 j).Contains (fullFactor true 27 20 ((j.val:ℝ)/6)) := by
  rw [ha27_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_19 j) true 27 19 j (ha27_1_19_contains j)
noncomputable def hk27_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_21 j i k)
lemma hk27_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_21 j i k).Contains (fullFactor true 27 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 21 (kernel27_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha27_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-986),985⟩,⟨(-985),986⟩⟩,⟨⟨(-48),48⟩,⟨(-48),48⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨13117190,13117191⟩,⟨143806,143807⟩⟩,⟨⟨409826848365942,409826848365943⟩,⟨(-1186952336854351),(-1186952336854350)⟩⟩,⟨⟨630473262925210382,630473262925211399⟩,⟨69600821264595356753,69600821264595357770⟩⟩]
lemma ha27_1_21_eq (j : Fin 7) : ha27_1_21 j = ((ha27_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha27_1_21_contains (j : Fin 7) : (ha27_1_21 j).Contains (fullFactor true 27 21 ((j.val:ℝ)/6)) := by
  rw [ha27_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_20 j) true 27 20 j (ha27_1_20_contains j)
noncomputable def hk27_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_22 j i k)
lemma hk27_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_22 j i k).Contains (fullFactor true 27 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 22 (kernel27_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha27_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-510),511⟩,⟨(-511),510⟩⟩,⟨⟨(-22),22⟩,⟨(-22),22⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-873311),(-873310)⟩,⟨(-2764510),(-2764508)⟩⟩,⟨⟨(-233531581510427),(-233531581510425)⟩,⟨(-38103976842093),(-38103976842092)⟩⟩,⟨⟨11418726900719557094,11418726900719557271⟩,⟨(-697537955436855816),(-697537955436855639)⟩⟩]
lemma ha27_1_22_eq (j : Fin 7) : ha27_1_22 j = ((ha27_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha27_1_22_contains (j : Fin 7) : (ha27_1_22 j).Contains (fullFactor true 27 22 ((j.val:ℝ)/6)) := by
  rw [ha27_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_21 j) true 27 21 j (ha27_1_21_contains j)
noncomputable def hk27_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_23 j i k)
lemma hk27_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_23 j i k).Contains (fullFactor true 27 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 23 (kernel27_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha27_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-253),253⟩,⟨(-253),253⟩⟩,⟨⟨(-10),10⟩,⟨(-10),10⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-497767),(-497766)⟩,⟨357560,357562⟩⟩,⟨⟨383106240041,383106240042⟩,⟨42647063809782,42647063809784⟩⟩,⟨⟨(-202737407332443963),(-202737407332443933)⟩,⟨(-1787058309774906797),(-1787058309774906767)⟩⟩]
lemma ha27_1_23_eq (j : Fin 7) : ha27_1_23 j = ((ha27_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha27_1_23_contains (j : Fin 7) : (ha27_1_23 j).Contains (fullFactor true 27 23 ((j.val:ℝ)/6)) := by
  rw [ha27_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_22 j) true 27 22 j (ha27_1_22_contains j)
noncomputable def hk27_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_24 j i k)
lemma hk27_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_24 j i k).Contains (fullFactor true 27 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 24 (kernel27_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha27_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-121),121⟩,⟨(-121),121⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨100259,100260⟩,⟨73243,73244⟩⟩,⟨⟨7248169049177,7248169049178⟩,⟨(-1316735177529),(-1316735177528)⟩⟩,⟨⟨(-267293558589669585),(-267293558589669579)⟩,⟨44485499562967922,44485499562967928⟩⟩]
lemma ha27_1_24_eq (j : Fin 7) : ha27_1_24 j = ((ha27_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha27_1_24_contains (j : Fin 7) : (ha27_1_24 j).Contains (fullFactor true 27 24 ((j.val:ℝ)/6)) := by
  rw [ha27_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_23 j) true 27 23 j (ha27_1_23_contains j)
noncomputable def hk27_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_25 j i k)
lemma hk27_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_25 j i k).Contains (fullFactor true 27 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 25 (kernel27_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha27_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-56),56⟩,⟨(-56),56⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨7458,7459⟩,⟨(-22968),(-22967)⟩⟩,⟨⟨(-419366999004),(-419366999003)⟩,⟨(-1147341323395),(-1147341323394)⟩⟩,⟨⟨8433156210537254,8433156210537256⟩,⟨38274032342484034,38274032342484035⟩⟩]
lemma ha27_1_25_eq (j : Fin 7) : ha27_1_25 j = ((ha27_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha27_1_25_contains (j : Fin 7) : (ha27_1_25 j).Contains (fullFactor true 27 25 ((j.val:ℝ)/6)) := by
  rw [ha27_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_24 j) true 27 24 j (ha27_1_24_contains j)
noncomputable def hk27_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_26 j i k)
lemma hk27_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_26 j i k).Contains (fullFactor true 27 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 26 (kernel27_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha27_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-4516),(-4515)⟩,⟨13,14⟩⟩,⟨⟨(-168917948981),(-168917948979)⟩,⟨96973715883,96973715884⟩⟩,⟨⟨5254807898644157,5254807898644158⟩,⟨(-1447661157240500),(-1447661157240499)⟩⟩]
lemma ha27_1_26_eq (j : Fin 7) : ha27_1_26 j = ((ha27_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha27_1_26_contains (j : Fin 7) : (ha27_1_26 j).Contains (fullFactor true 27 26 ((j.val:ℝ)/6)) := by
  rw [ha27_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_25 j) true 27 25 j (ha27_1_25_contains j)
noncomputable def hk27_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_27 j i k)
lemma hk27_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_27 j i k).Contains (fullFactor true 27 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 27 (kernel27_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha27_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨255,256⟩,⟨771,773⟩⟩,⟨⟨19079114801,19079114802⟩,⟨23028916712,23028916713⟩⟩,⟨⟨(-230157593987875),(-230157593987874)⟩,⟨(-692719109590016),(-692719109590014)⟩⟩]
lemma ha27_1_27_eq (j : Fin 7) : ha27_1_27 j = ((ha27_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha27_1_27_contains (j : Fin 7) : (ha27_1_27 j).Contains (fullFactor true 27 27 ((j.val:ℝ)/6)) := by
  rw [ha27_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_26 j) true 27 26 j (ha27_1_26_contains j)
noncomputable def hk27_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_28 j i k)
lemma hk27_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_28 j i k).Contains (fullFactor true 27 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 28 (kernel27_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha27_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨113,114⟩,⟨(-85),(-83)⟩⟩,⟨⟨2880086627,2880086628⟩,⟨(-3362971935),(-3362971933)⟩⟩,⟨⟨(-87793188528505),(-87793188528504)⟩,⟨34327830552382,34327830552384⟩⟩]
lemma ha27_1_28_eq (j : Fin 7) : ha27_1_28 j = ((ha27_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha27_1_28_contains (j : Fin 7) : (ha27_1_28 j).Contains (fullFactor true 27 28 ((j.val:ℝ)/6)) := by
  rw [ha27_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_27 j) true 27 27 j (ha27_1_27_contains j)
noncomputable def hk27_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_29 j i k)
lemma hk27_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_29 j i k).Contains (fullFactor true 27 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 29 (kernel27_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha27_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-20),(-19)⟩,⟨(-14),(-13)⟩⟩,⟨⟨(-543696395),(-543696394)⟩,⟨(-324049946),(-324049945)⟩⟩,⟨⟨4842893498021,4842893498023⟩,⟨10709573721045,10709573721046⟩⟩]
lemma ha27_1_29_eq (j : Fin 7) : ha27_1_29 j = ((ha27_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha27_1_29_contains (j : Fin 7) : (ha27_1_29 j).Contains (fullFactor true 27 29 ((j.val:ℝ)/6)) := by
  rw [ha27_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_28 j) true 27 28 j (ha27_1_28_contains j)
noncomputable def hk27_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_30 j i k)
lemma hk27_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk27_1_30 j i k).Contains (fullFactor true 27 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk27_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel27_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 27 30 (kernel27_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha27_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),0⟩,⟨3,4⟩⟩,⟨⟨(-31363729),(-31363728)⟩,⟨81646357,81646358⟩⟩,⟨⟨1258772773795,1258772773796⟩,⟨(-649959570039),(-649959570038)⟩⟩]
lemma ha27_1_30_eq (j : Fin 7) : ha27_1_30 j = ((ha27_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha27_1_30_contains (j : Fin 7) : (ha27_1_30 j).Contains (fullFactor true 27 30 ((j.val:ℝ)/6)) := by
  rw [ha27_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha27_1_29 j) true 27 29 j (ha27_1_29_contains j)
end SharpPlanar.CachedData

end OAI
