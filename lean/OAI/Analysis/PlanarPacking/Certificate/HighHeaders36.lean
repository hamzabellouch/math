import OAI.Analysis.PlanarPacking.Certificate.Powers40
import OAI.Analysis.PlanarPacking.Certificate.KernelValues40
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
noncomputable def hk36_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_0 j i k)
lemma hk36_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_0 j i k).Contains (fullFactor false 36 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 0 (power36_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha36_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999569,1000000000000000000000000000575⟩,⟨(-575),575⟩⟩,⟨⟨999999999999999999924329150121,1000000000000000000075670849935⟩,⟨(-61924777171),90204177703⟩⟩,⟨⟨999999999999999999792554873861,1000000000000000000207445126155⟩,⟨(-178877614491),235436415747⟩⟩,⟨⟨999999999999999999882399701369,1000000000000000000117600298667⟩,⟨(-75181197743),160019399591⟩⟩,⟨⟨999999999999999999433204421429,1000000000000000000566795578487⟩,⟨(-510447400947),623565003555⟩⟩,⟨⟨999999999999999999286388329077,1000000000000000000713611670831⟩,⟨(-642704122203),784101125327⟩⟩,⟨⟨999999999999999999764084879849,1000000000000000000235915120295⟩,⟨(-151076918231),320753322215⟩⟩]
lemma ha36_0_0_eq (j : Fin 7) : ha36_0_0 j = ((atomPoints j).direct.powBin 7 36).conj := by fin_cases j <;> decide +kernel
lemma ha36_0_0_contains (j : Fin 7) : (ha36_0_0 j).Contains (fullFactor false 36 0 ((j.val:ℝ)/6)) := by
  rw [ha36_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 36) ((j.val:ℝ)/6) 36 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 36 (by norm_num))
noncomputable def hk36_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_1 j i k)
lemma hk36_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_1 j i k).Contains (fullFactor false 36 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 1 (power36_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha36_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-47230797000),32423737506⟩,⟨523598775598298873037045502318,523598775598298873117954497710⟩⟩,⟨⟨(-246548438033),187320199859⟩,⟨1047197551196597745936097305231,1047197551196597746373902694787⟩⟩,⟨⟨(-251357885094),118094349259⟩,⟨1570796326794896619045273882880,1570796326794896619419726117177⟩⟩,⟨⟨(-1305991489470),1069078536573⟩,⟨2094395102393195491119572782846,2094395102393195493500427216977⟩⟩,⟨⟨(-2052771945833),1682595457288⟩,⟨2617993877991494363515102347592,2617993877991494367259897652168⟩⟩,⟨⟨(-1007676280686),474622136442⟩,⟨3141592653589793237718850791662,3141592653589793239211149208790⟩⟩]
lemma ha36_0_1_eq (j : Fin 7) : ha36_0_1 j = ((ha36_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha36_0_1_contains (j : Fin 7) : (ha36_0_1 j).Contains (fullFactor false 36 1 ((j.val:ℝ)/6)) := by
  rw [ha36_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_0 j) false 36 0 j (ha36_0_0_contains j)
noncomputable def hk36_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_2 j i k)
lemma hk36_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_2 j i k).Contains (fullFactor false 36 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 2 (power36_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha36_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-137077838904018869717049379717),(-137077838904018869695431121941)⟩,⟨(-12364993740),8488514630⟩⟩,⟨⟨(-548311355616075478940450850895),(-548311355616075478709471155718)⟩,⟨(-129092460280),98080627292⟩⟩,⟨⟨(-1233700550136169827505172801408),(-1233700550136169827207151713494)⟩,⟨(-197416021309),92751085016⟩⟩,⟨⟨(-2193245422464301916549947138209),(-2193245422464301914049740888018)⟩,⟨(-1367631089657),1119536425537⟩⟩,⟨⟨(-3426945972600471745112423219822),(-3426945972600471740199589321135)⟩,⟨(-2687072193552),2202512303159⟩⟩,⟨⟨(-4934802200544679310604551447757),(-4934802200544679308244746612382)⟩,⟨(-1582854200300),745534708539⟩⟩]
lemma ha36_0_2_eq (j : Fin 7) : ha36_0_2 j = ((ha36_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha36_0_2_contains (j : Fin 7) : (ha36_0_2 j).Contains (fullFactor false 36 2 ((j.val:ℝ)/6)) := by
  rw [ha36_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_1 j) false 36 1 j (ha36_0_1_contains j)
noncomputable def hk36_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_3 j i k)
lemma hk36_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_3 j i k).Contains (fullFactor false 36 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 3 (power36_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha36_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1481525289),2158098528⟩,⟨(-23924596203935046433673153602),(-23924596203935046429823901478)⟩⟩,⟨⟨(-34236597574),45061769428⟩,⟨(-191396769631480371494606399600),(-191396769631480371413370041037)⟩⟩,⟨⟨(-48564354550),103366787041⟩,⟨(-645964097506246253736260065741),(-645964097506246253578160421423)⟩⟩,⟨⟨(-781583868866),954786618687⟩,⟨(-1531174157051842972507079322727),(-1531174157051842970756732202216)⟩⟩,⟨⟨(-1922054575291),2344912850814⟩,⟨(-2990574525491880806116953767897),(-2990574525491880801820178116740)⟩⟩,⟨⟨(-780722121115),1657561042456⟩,⟨(-5167712780049970030501497541721),(-5167712780049970028013866356145)⟩⟩]
lemma ha36_0_3_eq (j : Fin 7) : ha36_0_3 j = ((ha36_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha36_0_3_contains (j : Fin 7) : (ha36_0_3 j).Contains (fullFactor false 36 3 ((j.val:ℝ)/6)) := by
  rw [ha36_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_2 j) false 36 2 j (ha36_0_2_contains j)
noncomputable def hk36_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_4 j i k)
lemma hk36_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_4 j i k).Contains (fullFactor false 36 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 4 (power36_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha36_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨3131722319766024859463138441,3131722319766024859976972949⟩,⟨(-193931207),282494437⟩⟩,⟨⟨50107557116256397744807327992,50107557116256397766234454240⟩,⟨(-8963120286),11797143650⟩⟩,⟨⟨253669507901048013605877991146,253669507901048013668771031410⟩,⟨(-19071177436),40592042350⟩⟩,⟨⟨801720913860102363628818474766,801720913860102364547850040869⟩,⟨(-409236356766),499925104503⟩⟩,⟨⟨1957326449853765535915803083591,1957326449853765538734266534647⟩,⟨(-1257981777820),1534741871964⟩⟩,⟨⟨4058712126416768217213842057509,4058712126416768219180542303822⟩,⟨(-613177720048),1301845398465⟩⟩]
lemma ha36_0_4_eq (j : Fin 7) : ha36_0_4 j = ((ha36_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha36_0_4_contains (j : Fin 7) : (ha36_0_4 j).Contains (fullFactor false 36 4 ((j.val:ℝ)/6)) := by
  rw [ha36_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_3 j) false 36 3 j (ha36_0_3_contains j)
noncomputable def hk36_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_5 j i k)
lemma hk36_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_5 j i k).Contains (fullFactor false 36 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 5 (power36_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha36_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-29582749),20308429⟩,⟨327953194428670967547900690,327953194428670967602753223⟩⟩,⟨⟨(-2470787989),1877231523⟩,⟨10494502221717470960149916670,10494502221717470964671008536⟩⟩,⟨⟨(-12752366205),5991387093⟩,⟨79692626246167045110798399977,79692626246167045130810500811⟩⟩,⟨⟨(-209408138087),171420524267⟩,⟨335824071094959070604118801576,335824071094959070990150804994⟩⟩,⟨⟨(-803588965020),658677718592⟩,⟨1024853732589596772933393627142,1024853732589596774412399849936⟩⟩,⟨⟨(-817973587986),385270924130⟩,⟨2550164039877345443243826596050,2550164039877345444487658229429⟩⟩]
lemma ha36_0_5_eq (j : Fin 7) : ha36_0_5 j = ((ha36_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha36_0_5_contains (j : Fin 7) : (ha36_0_5 j).Contains (fullFactor false 36 5 ((j.val:ℝ)/6)) := by
  rw [ha36_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_4 j) false 36 4 j (ha36_0_4_contains j)
noncomputable def hk36_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_6 j i k)
lemma hk36_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_6 j i k).Contains (fullFactor false 36 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 6 (power36_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha36_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-28619315176067161693996610),(-28619315176067161689118725)⟩,⟨(-2581582),1772245⟩⟩,⟨⟨(-1831636171268298348657145564),(-1831636171268298347862235896)⟩,⟨(-431233856),327638709⟩⟩,⟨⟨(-20863480763352960875798322855),(-20863480763352960870492756585)⟩,⟨(-3338561666),1568541474⟩⟩,⟨⟨(-117224714961171094356182070412),(-117224714961171094221058343000)⟩,⟨(-73097229802),59837051080⟩⟩,⟨⟨(-447176799626049401753969364122),(-447176799626049401107207750027)⟩,⟨(-350631831808),287402372474⟩⟩,⟨⟨(-1335262768854589496209074039007),(-1335262768854589495553555045319)⟩,⟨(-428289969142),201727384149⟩⟩]
lemma ha36_0_6_eq (j : Fin 7) : ha36_0_6 j = ((ha36_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha36_0_6_contains (j : Fin 7) : (ha36_0_6 j).Contains (fullFactor false 36 6 ((j.val:ℝ)/6)) := by
  rw [ha36_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_5 j) false 36 5 j (ha36_0_5_contains j)
noncomputable def hk36_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_7 j i k)
lemma hk36_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_7 j i k).Contains (fullFactor false 36 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 7 (power36_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha36_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-132564),193102⟩,⟨(-2140719769235797028402597),(-2140719769235797028030917)⟩⟩,⟨⟨(-49014637),64512434⟩,⟨(-274012130462182019671640104),(-274012130462182019551849687)⟩⟩,⟨⟨(-351979884),749171486⟩,⟨(-4681754135318688101312781935),(-4681754135318688100107313161)⟩⟩,⟨⟨(-17903203818),21870640014⟩,⟨(-35073552699159298530573630246),(-35073552699159298490033062958)⟩⟩,⟨⟨(-107488235952),131135998444⟩,⟨(-167243731971546642950644455899),(-167243731971546642708223824533)⟩⟩,⟨⟨(-90535038296),192216088667⟩,⟨(-599264529320792077038937963482),(-599264529320792076742834208831)⟩⟩]
lemma ha36_0_7_eq (j : Fin 7) : ha36_0_7 j = ((ha36_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha36_0_7_contains (j : Fin 7) : (ha36_0_7 j).Contains (fullFactor false 36 7 ((j.val:ℝ)/6)) := by
  rw [ha36_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_6 j) false 36 6 j (ha36_0_6_contains j)
noncomputable def hk36_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_8 j i k)
lemma hk36_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_8 j i k).Contains (fullFactor false 36 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 8 (power36_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha36_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨140109781258867029441543,140109781258867029466316⟩,⟨(-8677),12639⟩⟩,⟨⟨35868104002269959532308653,35868104002269959548103354⟩,⟨(-6416001),8444658⟩⟩,⟨⟨919260274839426580127423103,919260274839426580367042441⟩,⟨(-69111089),147099478⟩⟩,⟨⟨9182234624581109636971375090,9182234624581109647614098749⟩,⟨(-4687047800),5725720167⟩⟩,⟨⟨54730383304244933340688200501,54730383304244933420194378824⟩,⟨(-35175442960),42914155139⟩⟩,⟨⟨235330630358893204484777213001,235330630358893204601805966203⟩,⟨(-35553026401),75483081508⟩⟩]
lemma ha36_0_8_eq (j : Fin 7) : ha36_0_8 j = ((ha36_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha36_0_8_contains (j : Fin 7) : (ha36_0_8 j).Contains (fullFactor false 36 8 ((j.val:ℝ)/6)) := by
  rw [ha36_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_7 j) false 36 7 j (ha36_0_7_contains j)
noncomputable def hk36_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_9 j i k)
lemma hk36_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_9 j i k).Contains (fullFactor false 36 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 9 (power36_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha36_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-736),505⟩,⟨8151256657387584304186,8151256657387584305654⟩⟩,⟨⟨(-982581),746536⟩,⟨4173443408582443163193595,4173443408582443165044677⟩⟩,⟨⟨(-25673703),12062161⟩,⟨160441184787359821852577960,160441184787359821894910125⟩⟩,⟨⟨(-1332435587),1090725551⟩,⟨2136803025194210898787259565,2136803025194210901270735477⟩⟩,⟨⟨(-12483221715),10232121592⟩,⟨15920423158960125583958197347,15920423158960125607136283420⟩⟩,⟨⟨(-26348566038),12410347395⟩,⟨82145886611128228778800839760,82145886611128228819913059496⟩⟩]
lemma ha36_0_9_eq (j : Fin 7) : ha36_0_9 j = ((ha36_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha36_0_9_contains (j : Fin 7) : (ha36_0_9 j).Contains (fullFactor false 36 9 ((j.val:ℝ)/6)) := by
  rw [ha36_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_8 j) false 36 8 j (ha36_0_8_contains j)
noncomputable def hk36_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_10 j i k)
lemma hk36_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_10 j i k).Contains (fullFactor false 36 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 10 (power36_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha36_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-426798800539562151494),(-426798800539562151415)⟩,⟨(-39),27⟩⟩,⟨⟨(-437041971752511643187118),(-437041971752511642991881)⟩,⟨(-102896),78178⟩⟩,⟨⟨(-25202042373060605484606942),(-25202042373060605477877200)⟩,⟨(-4032816),1894720⟩⟩,⟨⟨(-447530979074571922784429173),(-447530979074571922262866658)⟩,⟨(-279064657),228441026⟩⟩,⟨⟨(-4167957036519161638339366037),(-4167957036519161632258090273)⟩,⟨(-3268099803),2678763169⟩⟩,⟨⟨(-25806891390014060019290845943),(-25806891390014060006292915306)⟩,⟨(-8277646150),3898825621⟩⟩]
lemma ha36_0_10_eq (j : Fin 7) : ha36_0_10 j = ((ha36_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha36_0_10_contains (j : Fin 7) : (ha36_0_10 j).Contains (fullFactor false 36 10 ((j.val:ℝ)/6)) := by
  rw [ha36_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_9 j) false 36 9 j (ha36_0_9_contains j)
noncomputable def hk36_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_11 j i k)
lemma hk36_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_11 j i k).Contains (fullFactor false 36 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 11 (power36_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha36_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-2),2⟩,⟨(-20315575399030665723),(-20315575399030665719)⟩⟩,⟨⟨(-7443),9796⟩,⟨(-41606298417214803406086),(-41606298417214803387366)⟩⟩,⟨⟨(-270566),575885⟩,⟨(-3598843235212085340974466),(-3598843235212085340002005)⟩⟩,⟨⟨(-43495070),53133787⟩,⟨(-85209699158455917406284096),(-85209699158455917306707593)⟩⟩,⟨⟨(-637544144),777805935⟩,⟨(-991971455030794225386276960),(-991971455030794223935779168)⟩⟩,⟨⟨(-1113501994),2364090213⟩,⟨(-7370430945714350779187737470),(-7370430945714350775452076349)⟩⟩]
lemma ha36_0_11_eq (j : Fin 7) : ha36_0_11 j = ((ha36_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha36_0_11_contains (j : Fin 7) : (ha36_0_11 j).Contains (fullFactor false 36 11 ((j.val:ℝ)/6)) := by
  rw [ha36_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_10 j) false 36 10 j (ha36_0_10_contains j)
noncomputable def hk36_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_12 j i k)
lemma hk36_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_12 j i k).Contains (fullFactor false 36 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 12 (power36_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha36_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨886434200375614885,886434200375614886⟩,⟨(-1),1⟩⟩,⟨⟨3630834484738518570233,3630834484738518571879⟩,⟨(-650),855⟩⟩,⟨⟨471087477881817150306871,471087477881817150435666⟩,⟨(-35418),75384⟩⟩,⟨⟨14871898049488972058333120,14871898049488972075759838⟩,⟨(-7591322),9273596⟩⟩,⟨⟨216414599701077852749581316,216414599701077853066719715⟩,⟨(-139090556),169690932⟩⟩,⟨⟨1929574309403923047428646934,1929574309403923048412782755⟩,⟨(-291514141),618917371⟩⟩]
lemma ha36_0_12_eq (j : Fin 7) : ha36_0_12 j = ((ha36_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha36_0_12_contains (j : Fin 7) : (ha36_0_12 j).Contains (fullFactor false 36 12 ((j.val:ℝ)/6)) := by
  rw [ha36_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_11 j) false 36 11 j (ha36_0_11_contains j)
noncomputable def hk36_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_13 j i k)
lemma hk36_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_13 j i k).Contains (fullFactor false 36 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 13 (power36_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha36_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨35702758612702236,35702758612702237⟩⟩,⟨⟨(-69),53⟩,⟨292476998555256722959,292476998555256723093⟩⟩,⟨⟨(-9109),4280⟩,⟨56921729219679268110435,56921729219679268126180⟩⟩,⟨⟨(-1494045),1223018⟩,⟨2395971572164663073622393,2395971572164663076437592⟩⟩,⟨⟨(-34173064),28010633⟩,⟨43582469009646284999155369,43582469009646285063160743⟩⟩,⟨⟨(-149568175),70447592⟩,⟨466302805767612564305520427,466302805767612564544831936⟩⟩]
lemma ha36_0_13_eq (j : Fin 7) : ha36_0_13 j = ((ha36_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha36_0_13_contains (j : Fin 7) : (ha36_0_13 j).Contains (fullFactor false 36 13 ((j.val:ℝ)/6)) := by
  rw [ha36_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_12 j) false 36 12 j (ha36_0_12_contains j)
noncomputable def hk36_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_14 j i k)
lemma hk36_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_14 j i k).Contains (fullFactor false 36 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 14 (power36_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha36_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1335280049649466),(-1335280049649465)⟩,⟨(-1),1⟩⟩,⟨⟨(-21877228333456835523),(-21877228333456835512)⟩,⟨(-6),4⟩⟩,⟨⟨(-6386603083791852242051),(-6386603083791852240263)⟩,⟨(-1023),481⟩⟩,⟨⟨(-358436509015356793332656),(-358436509015356792910362)⟩,⟨(-223509),182964⟩⟩,⟨⟨(-8149902646786285763148044),(-8149902646786285751153124)⟩,⟨(-6390349),5237977⟩⟩,⟨⟨(-104638104924845707146132851),(-104638104924845707092098400)⟩,⟨(-33563020),15808403⟩⟩]
lemma ha36_0_14_eq (j : Fin 7) : ha36_0_14 j = ((ha36_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha36_0_14_contains (j : Fin 7) : (ha36_0_14 j).Contains (fullFactor false 36 14 ((j.val:ℝ)/6)) := by
  rw [ha36_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_13 j) false 36 13 j (ha36_0_13_contains j)
noncomputable def hk36_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_15 j i k)
lemma hk36_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_15 j i k).Contains (fullFactor false 36 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 15 (power36_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha36_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-46610066605154),(-46610066605153)⟩⟩,⟨⟨(-1),1⟩,⟨(-1527318662517654888),(-1527318662517654886)⟩⟩,⟨⟨(-51),108⟩,⟨(-668803510981146723351),(-668803510981146723160)⟩⟩,⟨⟨(-25547),31208⟩,⟨(-50047177933378515357581),(-50047177933378515298457)⟩⟩,⟨⟨(-914200),1115327⟩,⟨(-1422426349034211493884873),(-1422426349034211491786836)⟩⟩,⟨⟨(-3310905),7029423⟩,⟨(-21915353447830215833324598),(-21915353447830215821937890)⟩⟩]
lemma ha36_0_15_eq (j : Fin 7) : ha36_0_15 j = ((ha36_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha36_0_15_contains (j : Fin 7) : (ha36_0_15 j).Contains (fullFactor false 36 15 ((j.val:ℝ)/6)) := by
  rw [ha36_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_14 j) false 36 14 j (ha36_0_14_contains j)
noncomputable def hk36_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_16 j i k)
lemma hk36_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_16 j i k).Contains (fullFactor false 36 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 16 (power36_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha36_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1525310862813,1525310862814⟩,⟨(-1),1⟩⟩,⟨⟨99962772705334443,99962772705334444⟩,⟨(-1),1⟩⟩,⟨⟨65659631149794723613,65659631149794723633⟩,⟨(-6),11⟩⟩,⟨⟨6551160272016798094949,6551160272016798102710⟩,⟨(-3345),4086⟩⟩,⟨⟨232743967104084891203823,232743967104084891547856⟩,⟨(-149586),182495⟩⟩,⟨⟨4303069587032947006224733,4303069587032947008474206⟩,⟨(-650095),1380224⟩⟩]
lemma ha36_0_16_eq (j : Fin 7) : ha36_0_16 j = ((ha36_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha36_0_16_contains (j : Fin 7) : (ha36_0_16 j).Contains (fullFactor false 36 16 ((j.val:ℝ)/6)) := by
  rw [ha36_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_15 j) false 36 15 j (ha36_0_15_contains j)
noncomputable def hk36_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_17 j i k)
lemma hk36_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_17 j i k).Contains (fullFactor false 36 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 17 (power36_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha36_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨46979464716,46979464717⟩⟩,⟨⟨(-1),1⟩,⟨6157692399285195,6157692399285196⟩⟩,⟨⟨(-2),1⟩,⟨6066935731106195666,6066935731106195669⟩⟩,⟨⟨(-504),413⟩,⟨807101058159109192948,807101058159109193907⟩⟩,⟨⟨(-28105),23037⟩,⟨35842487118702823460028,35842487118702823513124⟩⟩,⟨⟨(-255065),120138⟩,⟨795205400147551278279344,795205400147551278697578⟩⟩]
lemma ha36_0_17_eq (j : Fin 7) : ha36_0_17 j = ((ha36_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha36_0_17_contains (j : Fin 7) : (ha36_0_17 j).Contains (fullFactor false 36 17 ((j.val:ℝ)/6)) := by
  rw [ha36_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_16 j) false 36 16 j (ha36_0_16_contains j)
noncomputable def hk36_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_18 j i k)
lemma hk36_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_18 j i k).Contains (fullFactor false 36 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 18 (power36_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha36_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1366577234),(-1366577233)⟩,⟨(-1),1⟩⟩,⟨⟨(-358240022308520),(-358240022308519)⟩,⟨(-1),1⟩⟩,⟨⟨(-529440020073462377),(-529440020073462376)⟩,⟨(-1),1⟩⟩,⟨⟨(-93910472408044662796),(-93910472408044662683)⟩,⟨(-59),49⟩⟩,⟨⟨(-5213078436041832675544),(-5213078436041832667804)⟩,⟨(-4088),3351⟩⟩,⟨⟨(-138789524622137721183274),(-138789524622137721109836)⟩,⟨(-44518),20969⟩⟩]
lemma ha36_0_18_eq (j : Fin 7) : ha36_0_18 j = ((ha36_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha36_0_18_contains (j : Fin 7) : (ha36_0_18 j).Contains (fullFactor false 36 18 ((j.val:ℝ)/6)) := by
  rw [ha36_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_17 j) false 36 17 j (ha36_0_17_contains j)
noncomputable def hk36_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_19 j i k)
lemma hk36_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_19 j i k).Contains (fullFactor false 36 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 19 (power36_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha36_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-37659904),(-37659903)⟩⟩,⟨⟨(-1),1⟩,⟨(-19744635479058),(-19744635479057)⟩⟩,⟨⟨(-1),1⟩,⟨(-43770654673137423),(-43770654673137422)⟩⟩,⟨⟨(-6),7⟩,⟨(-10351875446044213768),(-10351875446044213755)⟩⟩,⟨⟨(-462),564⟩,⟨(-718305654265631155585),(-718305654265631154516)⟩⟩,⟨⟨(-3468),7361⟩,⟨(-22948428997269873116639),(-22948428997269873104423)⟩⟩]
lemma ha36_0_19_eq (j : Fin 7) : ha36_0_19 j = ((ha36_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha36_0_19_contains (j : Fin 7) : (ha36_0_19 j).Contains (fullFactor false 36 19 ((j.val:ℝ)/6)) := by
  rw [ha36_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_18 j) false 36 18 j (ha36_0_18_contains j)
noncomputable def hk36_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_20 j i k)
lemma hk36_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_20 j i k).Contains (fullFactor false 36 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 20 (power36_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha36_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨985933,985934⟩,⟨(-1),1⟩⟩,⟨⟨1033826696146,1033826696147⟩,⟨(-1),1⟩⟩,⟨⟨3437739179098606,3437739179098608⟩,⟨(-1),1⟩⟩,⟨⟨1084045861738968866,1084045861738968868⟩,⟨(-1),1⟩⟩,⟨⟨94025990269704865144,94025990269704865285⟩,⟨(-61),74⟩⟩,⟨⟨3604730797462500932948,3604730797462500934879⟩,⟨(-545),1157⟩⟩]
lemma ha36_0_20_eq (j : Fin 7) : ha36_0_20 j = ((ha36_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha36_0_20_contains (j : Fin 7) : (ha36_0_20 j).Contains (fullFactor false 36 20 ((j.val:ℝ)/6)) := by
  rw [ha36_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_19 j) false 36 19 j (ha36_0_19_contains j)
noncomputable def hk36_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_21 j i k)
lemma hk36_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_21 j i k).Contains (fullFactor false 36 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 21 (power36_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha36_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨24582,24583⟩⟩,⟨⟨(-1),1⟩,⟨51553370693,51553370694⟩⟩,⟨⟨(-1),1⟩,⟨257142289286047,257142289286048⟩⟩,⟨⟨(-1),1⟩,⟨108115254456938454,108115254456938455⟩⟩,⟨⟨(-10),8⟩,⟨11721879376103578814,11721879376103578832⟩⟩,⟨⟨(-174),82⟩,⟨539266466260812848798,539266466260812849090⟩⟩]
lemma ha36_0_21_eq (j : Fin 7) : ha36_0_21 j = ((ha36_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha36_0_21_contains (j : Fin 7) : (ha36_0_21 j).Contains (fullFactor false 36 21 ((j.val:ℝ)/6)) := by
  rw [ha36_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_20 j) false 36 20 j (ha36_0_20_contains j)
noncomputable def hk36_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_22 j i k)
lemma hk36_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_22 j i k).Contains (fullFactor false 36 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 22 (power36_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha36_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-586),(-585)⟩,⟨(-1),1⟩⟩,⟨⟨(-2453934707),(-2453934706)⟩,⟨(-1),1⟩⟩,⟨⟨(-18359916521553),(-18359916521552)⟩,⟨(-1),1⟩⟩,⟨⟨(-10292548155845728),(-10292548155845727)⟩,⟨(-1),1⟩⟩,⟨⟨(-1394900383872451221),(-1394900383872451218)⟩,⟨(-2),1⟩⟩,⟨⟨(-77007071306013533821),(-77007071306013533778)⟩,⟨(-25),12⟩⟩]
lemma ha36_0_22_eq (j : Fin 7) : ha36_0_22 j = ((ha36_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha36_0_22_contains (j : Fin 7) : (ha36_0_22 j).Contains (fullFactor false 36 22 ((j.val:ℝ)/6)) := by
  rw [ha36_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_21 j) false 36 21 j (ha36_0_21_contains j)
noncomputable def hk36_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_23 j i k)
lemma hk36_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_23 j i k).Contains (fullFactor false 36 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 23 (power36_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha36_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-14),(-13)⟩⟩,⟨⟨(-1),1⟩,⟨(-111728453),(-111728452)⟩⟩,⟨⟨(-1),1⟩,⟨(-1253899540536),(-1253899540535)⟩⟩,⟨⟨(-1),1⟩,⟨(-937246193423888),(-937246193423887)⟩⟩,⟨⟨(-1),1⟩,⟨(-158775681103741858),(-158775681103741856)⟩⟩,⟨⟨(-2),4⟩,⟨(-10518471716932064459),(-10518471716932064452)⟩⟩]
lemma ha36_0_23_eq (j : Fin 7) : ha36_0_23 j = ((ha36_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha36_0_23_contains (j : Fin 7) : (ha36_0_23 j).Contains (fullFactor false 36 23 ((j.val:ℝ)/6)) := by
  rw [ha36_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_22 j) false 36 22 j (ha36_0_22_contains j)
noncomputable def hk36_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_24 j i k)
lemma hk36_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_24 j i k).Contains (fullFactor false 36 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 24 (power36_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha36_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨4875073,4875074⟩,⟨(-1),1⟩⟩,⟨⟨82067533018,82067533019⟩,⟨(-1),1⟩⟩,⟨⟨81790159885152,81790159885153⟩,⟨(-1),1⟩⟩,⟨⟨17319740045980248,17319740045980250⟩,⟨(-1),1⟩⟩,⟨⟨1376864728037741370,1376864728037741371⟩,⟨(-1),1⟩⟩]
lemma ha36_0_24_eq (j : Fin 7) : ha36_0_24 j = ((ha36_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha36_0_24_contains (j : Fin 7) : (ha36_0_24 j).Contains (fullFactor false 36 24 ((j.val:ℝ)/6)) := by
  rw [ha36_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_23 j) false 36 23 j (ha36_0_23_contains j)
noncomputable def hk36_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_25 j i k)
lemma hk36_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_25 j i k).Contains (fullFactor false 36 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 25 (power36_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha36_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-1),1⟩,⟨204206,204207⟩⟩,⟨⟨(-1),1⟩,⟨5156455176,5156455177⟩⟩,⟨⟨(-1),1⟩,⟨6852036411496,6852036411497⟩⟩,⟨⟨(-1),1⟩,⟨1813718936351216,1813718936351217⟩⟩,⟨⟨(-1),1⟩,⟨173021924583611076,173021924583611077⟩⟩]
lemma ha36_0_25_eq (j : Fin 7) : ha36_0_25 j = ((ha36_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha36_0_25_contains (j : Fin 7) : (ha36_0_25 j).Contains (fullFactor false 36 25 ((j.val:ℝ)/6)) := by
  rw [ha36_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_24 j) false 36 24 j (ha36_0_24_contains j)
noncomputable def hk36_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_26 j i k)
lemma hk36_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_26 j i k).Contains (fullFactor false 36 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 26 (power36_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha36_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-8225),(-8224)⟩,⟨(-1),1⟩⟩,⟨⟨(-311528495),(-311528494)⟩,⟨(-1),1⟩⟩,⟨⟨(-551956596218),(-551956596217)⟩,⟨(-1),1⟩⟩,⟨⟨(-182627118144798),(-182627118144797)⟩,⟨(-1),1⟩⟩,⟨⟨(-20906323353147685),(-20906323353147684)⟩,⟨(-1),1⟩⟩]
lemma ha36_0_26_eq (j : Fin 7) : ha36_0_26 j = ((ha36_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha36_0_26_contains (j : Fin 7) : (ha36_0_26 j).Contains (fullFactor false 36 26 ((j.val:ℝ)/6)) := by
  rw [ha36_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_25 j) false 36 25 j (ha36_0_25_contains j)
noncomputable def hk36_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_27 j i k)
lemma hk36_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_27 j i k).Contains (fullFactor false 36 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 27 (power36_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha36_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨(-320),(-318)⟩⟩,⟨⟨(-1),1⟩,⟨(-18123994),(-18123993)⟩⟩,⟨⟨(-1),1⟩,⟨(-42815377477),(-42815377475)⟩⟩,⟨⟨(-1),1⟩,⟨(-17708025083642),(-17708025083641)⟩⟩,⟨⟨(-1),1⟩,⟨(-2432561179993389),(-2432561179993388)⟩⟩]
lemma ha36_0_27_eq (j : Fin 7) : ha36_0_27 j = ((ha36_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha36_0_27_contains (j : Fin 7) : (ha36_0_27 j).Contains (fullFactor false 36 27 ((j.val:ℝ)/6)) := by
  rw [ha36_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_26 j) false 36 26 j (ha36_0_26_contains j)
noncomputable def hk36_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_28 j i k)
lemma hk36_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_28 j i k).Contains (fullFactor false 36 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 28 (power36_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha36_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨11,12⟩,⟨(-1),1⟩⟩,⟨⟨1016753,1016754⟩,⟨(-1),1⟩⟩,⟨⟨3202582746,3202582747⟩,⟨(-1),1⟩⟩,⟨⟨1655696473581,1655696473582⟩,⟨(-1),1⟩⟩,⟨⟨272932726159819,272932726159820⟩,⟨(-1),1⟩⟩]
lemma ha36_0_28_eq (j : Fin 7) : ha36_0_28 j = ((ha36_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha36_0_28_contains (j : Fin 7) : (ha36_0_28 j).Contains (fullFactor false 36 28 ((j.val:ℝ)/6)) := by
  rw [ha36_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_27 j) false 36 27 j (ha36_0_27_contains j)
noncomputable def hk36_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_29 j i k)
lemma hk36_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_29 j i k).Contains (fullFactor false 36 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 29 (power36_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha36_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-1),1⟩,⟨55072,55073⟩⟩,⟨⟨(-1),1⟩,⟨231292193,231292194⟩⟩,⟨⟨(-1),1⟩,⟨149469076953,149469076954⟩⟩,⟨⟨(-1),1⟩,⟨29567015428549,29567015428550⟩⟩]
lemma ha36_0_29_eq (j : Fin 7) : ha36_0_29 j = ((ha36_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha36_0_29_contains (j : Fin 7) : (ha36_0_29 j).Contains (fullFactor false 36 29 ((j.val:ℝ)/6)) := by
  rw [ha36_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_28 j) false 36 28 j (ha36_0_28_contains j)
noncomputable def hk36_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_30 j i k)
lemma hk36_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_0_30 j i k).Contains (fullFactor false 36 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power36 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 30 (power36_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha36_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-2884),(-2883)⟩,⟨(-1),1⟩⟩,⟨⟨(-16147242),(-16147241)⟩,⟨(-1),1⟩⟩,⟨⟨(-13043637614),(-13043637613)⟩,⟨(-1),1⟩⟩,⟨⟨(-3096250615297),(-3096250615296)⟩,⟨(-1),1⟩⟩]
lemma ha36_0_30_eq (j : Fin 7) : ha36_0_30 j = ((ha36_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha36_0_30_contains (j : Fin 7) : (ha36_0_30 j).Contains (fullFactor false 36 30 ((j.val:ℝ)/6)) := by
  rw [ha36_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_0_29 j) false 36 29 j (ha36_0_29_contains j)
noncomputable def hk36_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_0 j i k)
lemma hk36_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_0 j i k).Contains (fullFactor true 36 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 0 (kernel36_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha36_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),2⟩,⟨(-2),4⟩⟩,⟨⟨(-2),2⟩,⟨(-3),0⟩⟩,⟨⟨(-1050972),(-1050969)⟩,⟨(-2829675),(-2829672)⟩⟩,⟨⟨1657458069911691374,1657458069911691465⟩,⟨(-12051186734807603617),(-12051186734807603525)⟩⟩,⟨⟨(-1243020940282687197299659347),(-1243020940282687190617026701)⟩,⟨1676392578950671605784059,1676392578950678274948786⟩⟩]
lemma ha36_1_0_eq (j : Fin 7) : ha36_1_0 j = atomKernel36_0 j := by fin_cases j <;> decide +kernel
lemma ha36_1_0_contains (j : Fin 7) : (ha36_1_0 j).Contains (fullFactor true 36 0 ((j.val:ℝ)/6)) := by
  rw [ha36_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel36_0_contains j
noncomputable def hk36_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_1 j i k)
lemma hk36_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_1 j i k).Contains (fullFactor true 36 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 1 (kernel36_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha36_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-21),41⟩,⟨(-30),31⟩⟩,⟨⟨(-21),6⟩,⟨(-11),19⟩⟩,⟨⟨(-11480476),(-11480456)⟩,⟨9143427,9143446⟩⟩,⟨⟨(-50400021493982320839),(-50400021493982320398)⟩,⟨1716504632604075338,1716504632604075776⟩⟩,⟨⟨239459708312164333399207818,239459708312164358737317874⟩,⟨4488266200039790625597273898,4488266200039790650995014418⟩⟩]
lemma ha36_1_1_eq (j : Fin 7) : ha36_1_1 j = ((ha36_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha36_1_1_contains (j : Fin 7) : (ha36_1_1 j).Contains (fullFactor true 36 1 ((j.val:ℝ)/6)) := by
  rw [ha36_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_0 j) true 36 0 j (ha36_1_0_contains j)
noncomputable def hk36_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_2 j i k)
lemma hk36_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_2 j i k).Contains (fullFactor true 36 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 2 (kernel36_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha36_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-262),262⟩,⟨(-262),262⟩⟩,⟨⟨(-179),132⟩,⟨(-182),128⟩⟩,⟨⟨(-37),79⟩,⟨(-43),70⟩⟩,⟨⟨29819758,29819818⟩,⟨19592001,19592062⟩⟩,⟨⟨21254709290211619583,21254709290211620634⟩,⟨102345032644875607971,102345032644875609027⟩⟩,⟨⟨8081140981986346309651619020,8081140981986346357912347341⟩,⟨(-853736019986821981515687197),(-853736019986821933380172618)⟩⟩]
lemma ha36_1_2_eq (j : Fin 7) : ha36_1_2 j = ((ha36_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha36_1_2_contains (j : Fin 7) : (ha36_1_2 j).Contains (fullFactor true 36 2 ((j.val:ℝ)/6)) := by
  rw [ha36_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_1 j) true 36 1 j (ha36_1_1_contains j)
noncomputable def hk36_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_3 j i k)
lemma hk36_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_3 j i k).Contains (fullFactor true 36 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 3 (kernel36_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha36_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-995),995⟩,⟨(-995),995⟩⟩,⟨⟨(-530),514⟩,⟨(-437),606⟩⟩,⟨⟨(-148),155⟩,⟨(-201),104⟩⟩,⟨⟨15109059,15109184⟩,⟨(-55818732),(-55818608)⟩⟩,⟨⟨134379985869419321407,134379985869419323093⟩,⟨(-52971300556489538639),(-52971300556489536958)⟩⟩,⟨⟨(-1533428648222390008220618540),(-1533428648222389947255512367)⟩,⟨(-9673633877237525963043062824),(-9673633877237525901908825961)⟩⟩]
lemma ha36_1_3_eq (j : Fin 7) : ha36_1_3 j = ((ha36_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha36_1_3_contains (j : Fin 7) : (ha36_1_3 j).Contains (fullFactor true 36 3 ((j.val:ℝ)/6)) := by
  rw [ha36_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_2 j) true 36 2 j (ha36_1_2_contains j)
noncomputable def hk36_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_4 j i k)
lemma hk36_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_4 j i k).Contains (fullFactor true 36 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 4 (kernel36_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha36_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2832),2832⟩,⟨(-2832),2832⟩⟩,⟨⟨(-1196),1433⟩,⟨(-1408),1221⟩⟩,⟨⟨(-367),238⟩,⟨(-272),332⟩⟩,⟨⟨(-70194435),(-70194244)⟩,⟨3695205,3695397⟩⟩,⟨⟨(-77761986310203023071),(-77761986310203021056)⟩,⟨(-127918517530736520708),(-127918517530736518689)⟩⟩,⟨⟨(-8660951694566569194698053396),(-8660951694566569136618790557)⟩,⟨1838425363912764107234955115,1838425363912764165147298640⟩⟩]
lemma ha36_1_4_eq (j : Fin 7) : ha36_1_4 j = ((ha36_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha36_1_4_contains (j : Fin 7) : (ha36_1_4 j).Contains (fullFactor true 36 4 ((j.val:ℝ)/6)) := by
  rw [ha36_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_3 j) true 36 3 j (ha36_1_3_contains j)
noncomputable def hk36_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_5 j i k)
lemma hk36_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_5 j i k).Contains (fullFactor true 36 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 5 (kernel36_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha36_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-6448),6448⟩,⟨(-6448),6448⟩⟩,⟨⟨(-2862),2436⟩,⟨(-2679),2619⟩⟩,⟨⟨(-413),547⟩,⟨(-432),529⟩⟩,⟨⟨24688221,24688457⟩,⟨63739361,63739596⟩⟩,⟨⟨(-93563370853662712696),(-93563370853662710761)⟩,⟨81554878168809960889,81554878168809962821⟩⟩,⟨⟨1652979561543056305367785294,1652979561543056349378790574⟩,⟨6185942958307918919258611250,6185942958307918963398766330⟩⟩]
lemma ha36_1_5_eq (j : Fin 7) : ha36_1_5 j = ((ha36_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha36_1_5_contains (j : Fin 7) : (ha36_1_5 j).Contains (fullFactor true 36 5 ((j.val:ℝ)/6)) := by
  rw [ha36_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_4 j) true 36 4 j (ha36_1_4_contains j)
noncomputable def hk36_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_6 j i k)
lemma hk36_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_6 j i k).Contains (fullFactor true 36 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 6 (kernel36_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha36_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-12235),12235⟩,⟨(-12235),12235⟩⟩,⟨⟨(-4299),4597⟩,⟨(-4241),4655⟩⟩,⟨⟨(-626),646⟩,⟨(-716),556⟩⟩,⟨⟨42843891,42844132⟩,⟨(-35108103),(-35107861)⟩⟩,⟨⟨66512162345950022257,66512162345950023801⟩,⟨54132426134363842678,54132426134363844224⟩⟩,⟨⟨3671202596570426832402027179,3671202596570426860356599547⟩,⟨(-1188417915833662494959927313),(-1188417915833662467087272624)⟩⟩]
lemma ha36_1_6_eq (j : Fin 7) : ha36_1_6 j = ((ha36_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha36_1_6_contains (j : Fin 7) : (ha36_1_6 j).Contains (fullFactor true 36 6 ((j.val:ℝ)/6)) := by
  rw [ha36_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_5 j) true 36 5 j (ha36_1_5_contains j)
noncomputable def hk36_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_7 j i k)
lemma hk36_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_7 j i k).Contains (fullFactor true 36 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 7 (kernel36_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha36_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-19898),19898⟩,⟨(-19898),19898⟩⟩,⟨⟨(-6354),6449⟩,⟨(-6657),6146⟩⟩,⟨⟨(-784),659⟩,⟨(-697),747⟩⟩,⟨⟨(-32446170),(-32445957)⟩,⟨(-20676930),(-20676717)⟩⟩,⟨⟨24900305010811665133,24900305010811666191⟩,⟨(-44263944819402599810),(-44263944819402598752)⟩⟩,⟨⟨(-711537437660632100651439641),(-711537437660632085520888223)⟩,⟨(-1861950707315105923518842250),(-1861950707315105908344365302)⟩⟩]
lemma ha36_1_7_eq (j : Fin 7) : ha36_1_7 j = ((ha36_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha36_1_7_contains (j : Fin 7) : (ha36_1_7 j).Contains (fullFactor true 36 7 ((j.val:ℝ)/6)) := by
  rw [ha36_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_6 j) true 36 6 j (ha36_1_6_contains j)
noncomputable def hk36_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_8 j i k)
lemma hk36_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_8 j i k).Contains (fullFactor true 36 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 8 (kernel36_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha36_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-28316),28316⟩,⟨(-28316),28316⟩⟩,⟨⟨(-8255),7868⟩,⟨(-7935),8188⟩⟩,⟨⟨(-679),755⟩,⟨(-686),748⟩⟩,⟨⟨(-5795001),(-5794836)⟩,⟨22654070,22654235⟩⟩,⟨⟨(-24796091082614424477),(-24796091082614423843)⟩,⟨(-8818724765285580462),(-8818724765285579827)⟩⟩,⟨⟨(-823743089443707069894563242),(-823743089443707062687266642)⟩,⟨364875618018392952534002726,364875618018392959720936360⟩⟩]
lemma ha36_1_8_eq (j : Fin 7) : ha36_1_8 j = ((ha36_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha36_1_8_contains (j : Fin 7) : (ha36_1_8 j).Contains (fullFactor true 36 8 ((j.val:ℝ)/6)) := by
  rw [ha36_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_7 j) true 36 7 j (ha36_1_7_contains j)
noncomputable def hk36_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_9 j i k)
lemma hk36_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_9 j i k).Contains (fullFactor true 36 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 9 (kernel36_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha36_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-35817),35817⟩,⟨(-35817),35817⟩⟩,⟨⟨(-8845),9202⟩,⟨(-8982),9065⟩⟩,⟨⟨(-627),639⟩,⟨(-664),602⟩⟩,⟨⟨12604755,12604869⟩,⟨(-839685),(-839572)⟩⟩,⟨⟨(-2062565499980090153),(-2062565499980089814)⟩,⟨11945604993550582903,11945604993550583242⟩⟩,⟨⟨163583595584826029955734431,163583595584826032990204328⟩,⟨322893758501608925428064268,322893758501608928470835016⟩⟩]
lemma ha36_1_9_eq (j : Fin 7) : ha36_1_9 j = ((ha36_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha36_1_9_contains (j : Fin 7) : (ha36_1_9 j).Contains (fullFactor true 36 9 ((j.val:ℝ)/6)) := by
  rw [ha36_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_8 j) true 36 8 j (ha36_1_8_contains j)
noncomputable def hk36_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_10 j i k)
lemma hk36_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_10 j i k).Contains (fullFactor true 36 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 10 (kernel36_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha36_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-40775),40775⟩,⟨(-40775),40775⟩⟩,⟨⟨(-9157),9024⟩,⟨(-9203),8978⟩⟩,⟨⟨(-521),485⟩,⟨(-497),509⟩⟩,⟨⟨(-2298021),(-2297951)⟩,⟨(-5696211),(-5696140)⟩⟩,⟨⟨5025400802822630782,5025400802822630945⟩,⟨1284089879857054,1284089879857217⟩⟩,⟨⟨113526112925002597448124151,113526112925002598604236771⟩,⟨(-65133546716807250313451225),(-65133546716807249160353789)⟩⟩]
lemma ha36_1_10_eq (j : Fin 7) : ha36_1_10 j = ((ha36_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha36_1_10_contains (j : Fin 7) : (ha36_1_10 j).Contains (fullFactor true 36 10 ((j.val:ℝ)/6)) := by
  rw [ha36_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_9 j) true 36 9 j (ha36_1_9_contains j)
noncomputable def hk36_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_11 j i k)
lemma hk36_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_11 j i k).Contains (fullFactor true 36 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 11 (kernel36_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha36_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-42199),42199⟩,⟨(-42199),42199⟩⟩,⟨⟨(-8348),8303⟩,⟨(-8244),8407⟩⟩,⟨⟨(-356),371⟩,⟨(-357),370⟩⟩,⟨⟨(-2075839),(-2075798)⟩,⟨1749835,1749875⟩⟩,⟨⟨(-321288110112883670),(-321288110112883598)⟩,⟨(-1866468580227929348),(-1866468580227929276)⟩⟩,⟨⟨(-23319646561156793459441722),(-23319646561156793061099128)⟩,⟨(-36155945937165040388754121),(-36155945937165039989425250)⟩⟩]
lemma ha36_1_11_eq (j : Fin 7) : ha36_1_11 j = ((ha36_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha36_1_11_contains (j : Fin 7) : (ha36_1_11 j).Contains (fullFactor true 36 11 ((j.val:ℝ)/6)) := by
  rw [ha36_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_10 j) true 36 10 j (ha36_1_10_contains j)
noncomputable def hk36_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_12 j i k)
lemma hk36_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_12 j i k).Contains (fullFactor true 36 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 12 (kernel36_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha36_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-40034),40034⟩,⟨(-40034),40034⟩⟩,⟨⟨(-6945),7034⟩,⟨(-7013),6966⟩⟩,⟨⟨(-240),242⟩,⟨(-246),236⟩⟩,⟨⟨935816,935837⟩,⟨578206,578228⟩⟩,⟨⟨(-616565988538150186),(-616565988538150156)⟩,⟨218926688831159953,218926688831159982⟩⟩,⟨⟨(-10515104498381581258562209),(-10515104498381581132127658)⟩,⟨7583081181619694641421321,7583081181619694767562860⟩⟩]
lemma ha36_1_12_eq (j : Fin 7) : ha36_1_12 j = ((ha36_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha36_1_12_contains (j : Fin 7) : (ha36_1_12 j).Contains (fullFactor true 36 12 ((j.val:ℝ)/6)) := by
  rw [ha36_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_11 j) true 36 11 j (ha36_1_11_contains j)
noncomputable def hk36_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_13 j i k)
lemma hk36_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_13 j i k).Contains (fullFactor true 36 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 13 (kernel36_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha36_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-35058),35058⟩,⟨(-35058),35058⟩⟩,⟨⟨(-5443),5390⟩,⟨(-5425),5408⟩⟩,⟨⟨(-150),145⟩,⟨(-147),148⟩⟩,⟨⟨96398,96409⟩,⟨(-399983),(-399972)⟩⟩,⟨⟨102202374306935182,102202374306935194⟩,⟨181897186211573896,181897186211573908⟩⟩,⟨⟨2258243079932038781620552,2258243079932038818492466⟩,⟨2811262735012686847048983,2811262735012686884000513⟩⟩]
lemma ha36_1_13_eq (j : Fin 7) : ha36_1_13 j = ((ha36_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha36_1_13_contains (j : Fin 7) : (ha36_1_13 j).Contains (fullFactor true 36 13 ((j.val:ℝ)/6)) := by
  rw [ha36_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_12 j) true 36 12 j (ha36_1_12_contains j)
noncomputable def hk36_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_14 j i k)
lemma hk36_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_14 j i k).Contains (fullFactor true 36 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 14 (kernel36_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha36_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-28508),28508⟩,⟨(-28508),28508⟩⟩,⟨⟨(-3892),3904⟩,⟨(-3885),3911⟩⟩,⟨⟨(-83),85⟩,⟨(-83),85⟩⟩,⟨⟨(-142430),(-142424)⟩,⟨11477,11483⟩⟩,⟨⟨47937300515665319,47937300515665324⟩,⟨(-38974147096446877),(-38974147096446872)⟩⟩,⟨⟨694821790015600458193723,694821790015600468221593⟩,⟨(-620175342563798435203016),(-620175342563798425195044)⟩⟩]
lemma ha36_1_14_eq (j : Fin 7) : ha36_1_14 j = ((ha36_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha36_1_14_contains (j : Fin 7) : (ha36_1_14 j).Contains (fullFactor true 36 14 ((j.val:ℝ)/6)) := by
  rw [ha36_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_13 j) true 36 13 j (ha36_1_13_contains j)
noncomputable def hk36_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_15 j i k)
lemma hk36_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_15 j i k).Contains (fullFactor true 36 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 15 (kernel36_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha36_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-21636),21636⟩,⟨(-21636),21636⟩⟩,⟨⟨(-2616),2621⟩,⟨(-2625),2612⟩⟩,⟨⟨(-45),45⟩,⟨(-45),44⟩⟩,⟨⟨17923,17926⟩,⟨42706,42709⟩⟩,⟨⟨(-12865560730077539),(-12865560730077536)⟩,⟨(-11225891718524800),(-11225891718524797)⟩⟩,⟨⟨(-157995888563329718871937),(-157995888563329716336632)⟩,⟨(-159504478119544086433528),(-159504478119544083893627)⟩⟩]
lemma ha36_1_15_eq (j : Fin 7) : ha36_1_15 j = ((ha36_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha36_1_15_contains (j : Fin 7) : (ha36_1_15 j).Contains (fullFactor true 36 15 ((j.val:ℝ)/6)) := by
  rw [ha36_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_14 j) true 36 14 j (ha36_1_14_contains j)
noncomputable def hk36_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_16 j i k)
lemma hk36_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_16 j i k).Contains (fullFactor true 36 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 16 (kernel36_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha36_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-15395),15395⟩,⟨(-15395),15395⟩⟩,⟨⟨(-1652),1646⟩,⟨(-1648),1650⟩⟩,⟨⟨(-23),23⟩,⟨(-23),23⟩⟩,⟨⟨10633,10635⟩,⟨(-9222),(-9219)⟩⟩,⟨⟨(-2299988233726216),(-2299988233726214)⟩,⟨3779129772871176,3779129772871178⟩⟩,⟨⟨(-34144212865590539538085),(-34144212865590538934982)⟩,⟨37529872401943248324859,37529872401943248926978⟩⟩]
lemma ha36_1_16_eq (j : Fin 7) : ha36_1_16 j = ((ha36_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha36_1_16_contains (j : Fin 7) : (ha36_1_16 j).Contains (fullFactor true 36 16 ((j.val:ℝ)/6)) := by
  rw [ha36_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_15 j) true 36 15 j (ha36_1_15_contains j)
noncomputable def hk36_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_17 j i k)
lemma hk36_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_17 j i k).Contains (fullFactor true 36 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 17 (kernel36_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha36_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-10310),10310⟩,⟨(-10310),10310⟩⟩,⟨⟨(-976),979⟩,⟨(-977),978⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-3455),(-3453)⟩,⟨(-2069),(-2067)⟩⟩,⟨⟨1003456305184554,1003456305184556⟩,⟨396145452067724,396145452067726⟩⟩,⟨⟨8348983519930141615789,8348983519930141750376⟩,⟨6838148924062458626834,6838148924062458761617⟩⟩]
lemma ha36_1_17_eq (j : Fin 7) : ha36_1_17 j = ((ha36_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha36_1_17_contains (j : Fin 7) : (ha36_1_17 j).Contains (fullFactor true 36 17 ((j.val:ℝ)/6)) := by
  rw [ha36_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_16 j) true 36 16 j (ha36_1_16_contains j)
noncomputable def hk36_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_18 j i k)
lemma hk36_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_18 j i k).Contains (fullFactor true 36 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 18 (kernel36_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha36_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-6521),6521⟩,⟨(-6521),6521⟩⟩,⟨⟨(-548),547⟩,⟨(-548),547⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-241),(-239)⟩,⟨1060,1061⟩⟩,⟨⟨50646228656044,50646228656045⟩,⟨(-243245739202544),(-243245739202543)⟩⟩,⟨⟨1284723176810186464885,1284723176810186493334⟩,⟨(-1746245502503329503895),(-1746245502503329475482)⟩⟩]
lemma ha36_1_18_eq (j : Fin 7) : ha36_1_18 j = ((ha36_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha36_1_18_contains (j : Fin 7) : (ha36_1_18 j).Contains (fullFactor true 36 18 ((j.val:ℝ)/6)) := by
  rw [ha36_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_17 j) true 36 17 j (ha36_1_17_contains j)
noncomputable def hk36_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_19 j i k)
lemma hk36_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_19 j i k).Contains (fullFactor true 36 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 19 (kernel36_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha36_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-3908),3908⟩,⟨(-3908),3908⟩⟩,⟨⟨(-291),291⟩,⟨(-291),291⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨276,278⟩,⟨(-27),(-25)⟩⟩,⟨⟨(-54179013088952),(-54179013088951)⟩,⟨(-1872928312373),(-1872928312372)⟩⟩,⟨⟨(-344577618906544153580),(-344577618906544147897)⟩,⟨(-226908972049481652362),(-226908972049481646673)⟩⟩]
lemma ha36_1_19_eq (j : Fin 7) : ha36_1_19 j = ((ha36_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha36_1_19_contains (j : Fin 7) : (ha36_1_19 j).Contains (fullFactor true 36 19 ((j.val:ℝ)/6)) := by
  rw [ha36_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_18 j) true 36 18 j (ha36_1_18_contains j)
noncomputable def hk36_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_20 j i k)
lemma hk36_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_20 j i k).Contains (fullFactor true 36 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 20 (kernel36_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha36_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-2225),2225⟩,⟨(-2225),2225⟩⟩,⟨⟨(-147),147⟩,⟨(-147),147⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-28),(-26)⟩,⟨(-63),(-61)⟩⟩,⟨⟨1525354260258,1525354260259⟩,⟨11132821019268,11132821019269⟩⟩,⟨⟨(-37733585562330668793),(-37733585562330667711)⟩,⟨64344310646478403937,64344310646478405017⟩⟩]
lemma ha36_1_20_eq (j : Fin 7) : ha36_1_20 j = ((ha36_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha36_1_20_contains (j : Fin 7) : (ha36_1_20 j).Contains (fullFactor true 36 20 ((j.val:ℝ)/6)) := by
  rw [ha36_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_19 j) true 36 19 j (ha36_1_19_contains j)
noncomputable def hk36_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_21 j i k)
lemma hk36_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_21 j i k).Contains (fullFactor true 36 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 21 (kernel36_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha36_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-1207),1207⟩,⟨(-1207),1207⟩⟩,⟨⟨(-71),71⟩,⟨(-71),71⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-12),(-11)⟩,⟨10,11⟩⟩,⟨⟨2114597853254,2114597853255⟩,⟨(-670115506523),(-670115506522)⟩⟩,⟨⟨11401635385740531415,11401635385740531611⟩,⟨5913086332107364907,5913086332107365104⟩⟩]
lemma ha36_1_21_eq (j : Fin 7) : ha36_1_21 j = ((ha36_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha36_1_21_contains (j : Fin 7) : (ha36_1_21 j).Contains (fullFactor true 36 21 ((j.val:ℝ)/6)) := by
  rw [ha36_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_20 j) true 36 20 j (ha36_1_20_contains j)
noncomputable def hk36_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_22 j i k)
lemma hk36_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_22 j i k).Contains (fullFactor true 36 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 22 (kernel36_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha36_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-625),625⟩,⟨(-625),625⟩⟩,⟨⟨(-33),33⟩,⟨(-33),33⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨2,4⟩,⟨1,2⟩⟩,⟨⟨(-192133733795),(-192133733793)⟩,⟨(-371217841193),(-371217841192)⟩⟩,⟨⟨873244790737701987,873244790737702022⟩,⟨(-1921905559715956097),(-1921905559715956062)⟩⟩]
lemma ha36_1_22_eq (j : Fin 7) : ha36_1_22 j = ((ha36_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha36_1_22_contains (j : Fin 7) : (ha36_1_22 j).Contains (fullFactor true 36 22 ((j.val:ℝ)/6)) := by
  rw [ha36_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_21 j) true 36 21 j (ha36_1_21_contains j)
noncomputable def hk36_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_23 j i k)
lemma hk36_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_23 j i k).Contains (fullFactor true 36 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 23 (kernel36_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha36_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-310),310⟩,⟨(-310),310⟩⟩,⟨⟨(-15),15⟩,⟨(-15),15⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-60052783459),(-60052783458)⟩,⟨45494512039,45494512040⟩⟩,⟨⟨(-308870570569920922),(-308870570569920915)⟩,⟨(-121409870626070744),(-121409870626070737)⟩⟩]
lemma ha36_1_23_eq (j : Fin 7) : ha36_1_23 j = ((ha36_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha36_1_23_contains (j : Fin 7) : (ha36_1_23 j).Contains (fullFactor true 36 23 ((j.val:ℝ)/6)) := by
  rw [ha36_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_22 j) true 36 22 j (ha36_1_22_contains j)
noncomputable def hk36_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_24 j i k)
lemma hk36_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_24 j i k).Contains (fullFactor true 36 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 24 (kernel36_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha36_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-148),148⟩,⟨(-148),148⟩⟩,⟨⟨(-7),7⟩,⟨(-7),7⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨9506417820,9506417821⟩,⟨8887141015,8887141016⟩⟩,⟨⟨(-15850689216029618),(-15850689216029616)⟩,⟨47422383812711839,47422383812711841⟩⟩]
lemma ha36_1_24_eq (j : Fin 7) : ha36_1_24 j = ((ha36_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha36_1_24_contains (j : Fin 7) : (ha36_1_24 j).Contains (fullFactor true 36 24 ((j.val:ℝ)/6)) := by
  rw [ha36_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_23 j) true 36 23 j (ha36_1_23_contains j)
noncomputable def hk36_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_25 j i k)
lemma hk36_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_25 j i k).Contains (fullFactor true 36 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 25 (kernel36_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha36_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-68),68⟩,⟨(-68),68⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨1184447361,1184447362⟩,⟨(-1803831570),(-1803831569)⟩⟩,⟨⟨6968791993521496,6968791993521497⟩,⟨1933303657017176,1933303657017177⟩⟩]
lemma ha36_1_25_eq (j : Fin 7) : ha36_1_25 j = ((ha36_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha36_1_25_contains (j : Fin 7) : (ha36_1_25 j).Contains (fullFactor true 36 25 ((j.val:ℝ)/6)) := by
  rw [ha36_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_24 j) true 36 24 j (ha36_1_24_contains j)
noncomputable def hk36_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_26 j i k)
lemma hk36_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_26 j i k).Contains (fullFactor true 36 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 26 (kernel36_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha36_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-30),30⟩,⟨(-30),30⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-315515316),(-315515315)⟩,⟨(-137245018),(-137245017)⟩⟩,⟨⟨218179092308524,218179092308525⟩,⟨(-981827394548045),(-981827394548044)⟩⟩]
lemma ha36_1_26_eq (j : Fin 7) : ha36_1_26 j = ((ha36_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha36_1_26_contains (j : Fin 7) : (ha36_1_26 j).Contains (fullFactor true 36 26 ((j.val:ℝ)/6)) := by
  rw [ha36_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_25 j) true 36 25 j (ha36_1_25_contains j)
noncomputable def hk36_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_27 j i k)
lemma hk36_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_27 j i k).Contains (fullFactor true 36 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 27 (kernel36_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha36_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-13),13⟩,⟨(-13),13⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-12535834),(-12535833)⟩,⟨51319845,51319846⟩⟩,⟨⟨(-132828611372952),(-132828611372951)⟩,⟨(-22351457795380),(-22351457795379)⟩⟩]
lemma ha36_1_27_eq (j : Fin 7) : ha36_1_27 j = ((ha36_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha36_1_27_contains (j : Fin 7) : (ha36_1_27 j).Contains (fullFactor true 36 27 ((j.val:ℝ)/6)) := by
  rw [ha36_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_26 j) true 36 26 j (ha36_1_26_contains j)
noncomputable def hk36_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_28 j i k)
lemma hk36_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_28 j i k).Contains (fullFactor true 36 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 28 (kernel36_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha36_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-6),6⟩,⟨(-6),6⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨7803064,7803065⟩,⟨538134,538135⟩⟩,⟨⟨(-1991786508369),(-1991786508367)⟩,⟨17280163662042,17280163662043⟩⟩]
lemma ha36_1_28_eq (j : Fin 7) : ha36_1_28 j = ((ha36_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha36_1_28_contains (j : Fin 7) : (ha36_1_28 j).Contains (fullFactor true 36 28 ((j.val:ℝ)/6)) := by
  rw [ha36_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_27 j) true 36 27 j (ha36_1_27_contains j)
noncomputable def hk36_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_29 j i k)
lemma hk36_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_29 j i k).Contains (fullFactor true 36 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 29 (kernel36_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha36_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-113701),(-113699)⟩,⟨(-1112305),(-1112304)⟩⟩,⟨⟨2164590529937,2164590529939⟩,⟨136125470911,136125470912⟩⟩]
lemma ha36_1_29_eq (j : Fin 7) : ha36_1_29 j = ((ha36_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha36_1_29_contains (j : Fin 7) : (ha36_1_29 j).Contains (fullFactor true 36 29 ((j.val:ℝ)/6)) := by
  rw [ha36_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_28 j) true 36 28 j (ha36_1_28_contains j)
noncomputable def hk36_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_30 j i k)
lemma hk36_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk36_1_30 j i k).Contains (fullFactor true 36 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk36_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel36_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 36 30 (kernel36_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha36_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-148801),(-148800)⟩,⟨41596,41597⟩⟩,⟨⟨2836673203,2836673205⟩,⟨(-261398450093),(-261398450092)⟩⟩]
lemma ha36_1_30_eq (j : Fin 7) : ha36_1_30 j = ((ha36_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha36_1_30_contains (j : Fin 7) : (ha36_1_30 j).Contains (fullFactor true 36 30 ((j.val:ℝ)/6)) := by
  rw [ha36_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha36_1_29 j) true 36 29 j (ha36_1_29_contains j)
end SharpPlanar.CachedData

end OAI
