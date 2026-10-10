import Mathlib
import OAI.Analysis.LaughlinFock.EntryEnumeration
import OAI.Analysis.LaughlinFock.TableTrace

namespace OAI

/-! Numeric Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

structure NumericRowEntry where
  p : ℕ
  j : ℕ
  i : ℕ
  a : ℤ
  deriving DecidableEq

def rowToNumeric (t : Fin 8) (b : RowEntry t.val) : NumericRowEntry :=
  ⟨rowP b, rowJ b, rowI b, certificateAlphaData t b.val.1 b.val.2⟩

def numericRowData_0 : List NumericRowEntry := [
  ⟨0, 0, 0, -1458000⟩,
  ⟨0, 1, 1, -1303000⟩,
  ⟨0, 2, 2, 1475944⟩,
  ⟨0, 3, 3, 3608220⟩,
  ⟨0, 4, 4, 43844714⟩,
  ⟨0, 5, 5, -184490641⟩,
  ⟨0, 6, 6, -142169573⟩,
  ⟨0, 7, 7, 1489137⟩,
  ⟨0, 8, 8, -100397507⟩,
  ⟨1, 0, 1, 781353⟩,
  ⟨1, 1, 2, -3890972⟩,
  ⟨1, 2, 3, -194326⟩,
  ⟨1, 3, 4, -13071015⟩,
  ⟨1, 4, 5, -49364910⟩,
  ⟨1, 5, 6, 44700932⟩,
  ⟨1, 6, 7, 51534774⟩,
  ⟨1, 7, 8, -41946820⟩,
  ⟨2, 0, 2, 2056486⟩,
  ⟨2, 1, 3, -760626⟩,
  ⟨2, 2, 4, 4305543⟩,
  ⟨2, 3, 5, -36416268⟩,
  ⟨2, 4, 6, -8021896⟩,
  ⟨2, 5, 7, -2613330⟩,
  ⟨2, 6, 8, -1141300⟩,
  ⟨3, 0, 3, 3923145⟩,
  ⟨3, 1, 4, -4779646⟩,
  ⟨3, 2, 5, 49466660⟩,
  ⟨3, 3, 6, -6088990⟩,
  ⟨3, 4, 7, 5250044⟩,
  ⟨3, 5, 8, -9079480⟩,
  ⟨4, 0, 4, 3991791⟩,
  ⟨4, 1, 5, -6855540⟩,
  ⟨4, 2, 6, 9257380⟩,
  ⟨4, 3, 7, -9310399⟩,
  ⟨4, 4, 8, 6494980⟩,
  ⟨5, 0, 5, -39241199⟩,
  ⟨5, 1, 6, -7152680⟩,
  ⟨5, 2, 7, 9042278⟩,
  ⟨5, 3, 8, -4542700⟩,
  ⟨6, 0, 6, 5245792⟩,
  ⟨6, 1, 7, -12421683⟩,
  ⟨6, 2, 8, 8099967⟩,
  ⟨7, 0, 7, 21052655⟩,
  ⟨7, 1, 8, -7572580⟩
]

theorem numericRowDataChecked_0 :
    rowEntryList_0.map (rowToNumeric ⟨0, by decide⟩) = numericRowData_0 := by
  decide +kernel

def numericRowData_1 : List NumericRowEntry := [
  ⟨0, 1, 0, -2158090⟩,
  ⟨0, 2, 1, 10930045⟩,
  ⟨0, 3, 2, -20794124⟩,
  ⟨0, 4, 3, -10149386⟩,
  ⟨0, 5, 4, 597895303⟩,
  ⟨0, 6, 5, 834366316⟩,
  ⟨0, 7, 6, 765947384⟩,
  ⟨0, 8, 7, 1283859555⟩,
  ⟨1, 0, 0, -5627000⟩,
  ⟨1, 1, 1, -5402022⟩,
  ⟨1, 2, 2, 9973000⟩,
  ⟨1, 3, 3, 24359402⟩,
  ⟨1, 4, 4, 91996112⟩,
  ⟨1, 5, 5, -136745470⟩,
  ⟨1, 6, 6, -141127842⟩,
  ⟨1, 7, 7, -50782825⟩,
  ⟨1, 8, 8, -366942013⟩,
  ⟨2, 0, 1, -5127489⟩,
  ⟨2, 1, 2, 6909968⟩,
  ⟨2, 2, 3, -9505204⟩,
  ⟨2, 3, 4, 72222049⟩,
  ⟨2, 4, 5, 51361561⟩,
  ⟨2, 5, 6, -1267754⟩,
  ⟨2, 6, 7, -15925422⟩,
  ⟨2, 7, 8, -78778293⟩,
  ⟨3, 0, 2, -5983211⟩,
  ⟨3, 1, 3, -106483⟩,
  ⟨3, 2, 4, -96337602⟩,
  ⟨3, 3, 5, -7668424⟩,
  ⟨3, 4, 6, 10264188⟩,
  ⟨3, 5, 7, -19098454⟩,
  ⟨3, 6, 8, 2115155⟩,
  ⟨4, 0, 3, 10208704⟩,
  ⟨4, 1, 4, 618400⟩,
  ⟨4, 2, 5, -7918740⟩,
  ⟨4, 3, 6, -6479832⟩,
  ⟨4, 4, 7, 4936997⟩,
  ⟨4, 5, 8, 14394828⟩,
  ⟨5, 0, 4, 99243497⟩,
  ⟨5, 1, 5, -1336744⟩,
  ⟨5, 2, 6, 7033004⟩,
  ⟨5, 3, 7, 2815777⟩,
  ⟨5, 4, 8, 3603042⟩,
  ⟨6, 0, 5, 35489766⟩,
  ⟨6, 1, 6, -6585714⟩,
  ⟨6, 2, 7, 9964326⟩,
  ⟨6, 3, 8, -9564997⟩,
  ⟨7, 0, 6, -977099⟩,
  ⟨7, 1, 7, -25775399⟩,
  ⟨7, 2, 8, 1881084⟩
]

theorem numericRowDataChecked_1 :
    rowEntryList_1.map (rowToNumeric ⟨1, by decide⟩) = numericRowData_1 := by
  decide +kernel

def numericRowData_2 : List NumericRowEntry := [
  ⟨0, 2, 0, 2286849⟩,
  ⟨0, 3, 1, 19304798⟩,
  ⟨0, 4, 2, 72232229⟩,
  ⟨0, 5, 3, -661988975⟩,
  ⟨0, 6, 4, -694800860⟩,
  ⟨0, 7, 5, -7185493⟩,
  ⟨0, 8, 6, -295108017⟩,
  ⟨1, 1, 0, -8424424⟩,
  ⟨1, 2, 1, 2832670⟩,
  ⟨1, 3, 2, -21562963⟩,
  ⟨1, 4, 3, 316632327⟩,
  ⟨1, 5, 4, 538338959⟩,
  ⟨1, 6, 5, 592775303⟩,
  ⟨1, 7, 6, 493483565⟩,
  ⟨1, 8, 7, 530121321⟩,
  ⟨2, 0, 0, -677288⟩,
  ⟨2, 1, 1, 5188364⟩,
  ⟨2, 2, 2, -2632251⟩,
  ⟨2, 3, 3, -109820524⟩,
  ⟨2, 4, 4, -71765788⟩,
  ⟨2, 5, 5, -51844671⟩,
  ⟨2, 6, 6, -17032491⟩,
  ⟨2, 7, 7, -15649485⟩,
  ⟨2, 8, 8, -126493796⟩,
  ⟨3, 0, 1, 2276756⟩,
  ⟨3, 1, 2, -7542800⟩,
  ⟨3, 2, 3, 36208527⟩,
  ⟨3, 3, 4, 45768030⟩,
  ⟨3, 4, 5, 35084799⟩,
  ⟨3, 5, 6, 20746753⟩,
  ⟨3, 6, 7, -6109724⟩,
  ⟨3, 7, 8, -38742315⟩,
  ⟨4, 0, 2, 14442833⟩,
  ⟨4, 1, 3, -16716287⟩,
  ⟨4, 2, 4, -76293178⟩,
  ⟨4, 3, 5, -1636292⟩,
  ⟨4, 4, 6, -4793945⟩,
  ⟨4, 5, 7, -10517615⟩,
  ⟨4, 6, 8, 24708653⟩,
  ⟨5, 0, 3, 10039299⟩,
  ⟨5, 1, 4, 36778073⟩,
  ⟨5, 2, 5, -63545981⟩,
  ⟨5, 3, 6, -887901⟩,
  ⟨5, 4, 7, 3332305⟩,
  ⟨5, 5, 8, 4129678⟩,
  ⟨6, 0, 4, 57374228⟩,
  ⟨6, 1, 5, 40592205⟩,
  ⟨6, 2, 6, -31810373⟩,
  ⟨6, 3, 7, 4995989⟩,
  ⟨6, 4, 8, -3075894⟩,
  ⟨7, 0, 5, 88550482⟩,
  ⟨7, 1, 6, 31531302⟩,
  ⟨7, 2, 7, -4435968⟩,
  ⟨7, 3, 8, -7365918⟩
]

theorem numericRowDataChecked_2 :
    rowEntryList_2.map (rowToNumeric ⟨2, by decide⟩) = numericRowData_2 := by
  decide +kernel

def numericRowData_3 : List NumericRowEntry := [
  ⟨0, 3, 0, 39091021⟩,
  ⟨0, 4, 1, -4327630⟩,
  ⟨0, 5, 2, 213162965⟩,
  ⟨0, 6, 3, 45619843⟩,
  ⟨0, 7, 4, -654459233⟩,
  ⟨0, 8, 5, -49355411⟩,
  ⟨1, 2, 0, -7645272⟩,
  ⟨1, 3, 1, 8738979⟩,
  ⟨1, 4, 2, -367337826⟩,
  ⟨1, 5, 3, -305799567⟩,
  ⟨1, 6, 4, -733169191⟩,
  ⟨1, 7, 5, 195732122⟩,
  ⟨1, 8, 6, 71375471⟩,
  ⟨2, 1, 0, -3949210⟩,
  ⟨2, 2, 1, 762818⟩,
  ⟨2, 3, 2, 68452276⟩,
  ⟨2, 4, 3, 199108377⟩,
  ⟨2, 5, 4, 46517664⟩,
  ⟨2, 6, 5, 68403288⟩,
  ⟨2, 7, 6, 47754272⟩,
  ⟨2, 8, 7, 127976176⟩,
  ⟨3, 0, 0, 11033607⟩,
  ⟨3, 1, 1, -2140475⟩,
  ⟨3, 2, 2, 18301715⟩,
  ⟨3, 3, 3, -133068288⟩,
  ⟨3, 4, 4, -15957882⟩,
  ⟨3, 5, 5, -12923425⟩,
  ⟨3, 6, 6, -63267429⟩,
  ⟨3, 7, 7, -35729612⟩,
  ⟨3, 8, 8, -80840875⟩,
  ⟨4, 0, 1, 8563509⟩,
  ⟨4, 1, 2, 21124181⟩,
  ⟨4, 2, 3, 91082225⟩,
  ⟨4, 3, 4, -17834095⟩,
  ⟨4, 4, 5, 23279016⟩,
  ⟨4, 5, 6, 25167823⟩,
  ⟨4, 6, 7, 5867255⟩,
  ⟨4, 7, 8, -14358409⟩,
  ⟨5, 0, 2, -78804551⟩,
  ⟨5, 1, 3, -37818356⟩,
  ⟨5, 2, 4, 61096591⟩,
  ⟨5, 3, 5, -30356506⟩,
  ⟨5, 4, 6, 14193156⟩,
  ⟨5, 5, 7, 7769542⟩,
  ⟨5, 6, 8, -14948988⟩,
  ⟨6, 0, 3, -10297948⟩,
  ⟨6, 1, 4, -16392402⟩,
  ⟨6, 2, 5, -224637⟩,
  ⟨6, 3, 6, -26277133⟩,
  ⟨6, 4, 7, -1390692⟩,
  ⟨6, 5, 8, 7844148⟩,
  ⟨7, 0, 4, -156393617⟩,
  ⟨7, 1, 5, 5235902⟩,
  ⟨7, 2, 6, 12966156⟩,
  ⟨7, 3, 7, -29134694⟩,
  ⟨7, 4, 8, -7754810⟩
]

theorem numericRowDataChecked_3 :
    rowEntryList_3.map (rowToNumeric ⟨3, by decide⟩) = numericRowData_3 := by
  decide +kernel

def numericRowData_4 : List NumericRowEntry := [
  ⟨0, 4, 0, 19350310⟩,
  ⟨0, 5, 1, -256570426⟩,
  ⟨0, 6, 2, 437882921⟩,
  ⟨0, 7, 3, -166877023⟩,
  ⟨0, 8, 4, 644065588⟩,
  ⟨1, 3, 0, 7604311⟩,
  ⟨1, 4, 1, -56036955⟩,
  ⟨1, 5, 2, -106906398⟩,
  ⟨1, 6, 3, 395640853⟩,
  ⟨1, 7, 4, -375570014⟩,
  ⟨1, 8, 5, -1474842820⟩,
  ⟨2, 2, 0, 3171752⟩,
  ⟨2, 3, 1, -42320168⟩,
  ⟨2, 4, 2, -196928392⟩,
  ⟨2, 5, 3, 84182344⟩,
  ⟨2, 6, 4, 123805380⟩,
  ⟨2, 7, 5, -377993673⟩,
  ⟨2, 8, 6, 446685144⟩,
  ⟨3, 1, 0, 5083588⟩,
  ⟨3, 2, 1, 54525539⟩,
  ⟨3, 3, 2, 112160315⟩,
  ⟨3, 4, 3, -4586199⟩,
  ⟨3, 5, 4, 169842096⟩,
  ⟨3, 6, 5, 129314466⟩,
  ⟨3, 7, 6, 473546⟩,
  ⟨3, 8, 7, -43309042⟩,
  ⟨4, 0, 0, 8117035⟩,
  ⟨4, 1, 1, -12273926⟩,
  ⟨4, 2, 2, -13371505⟩,
  ⟨4, 3, 3, -33864426⟩,
  ⟨4, 4, 4, -63645420⟩,
  ⟨4, 5, 5, 39205032⟩,
  ⟨4, 6, 6, 47849173⟩,
  ⟨4, 7, 7, -57278002⟩,
  ⟨4, 8, 8, 30676490⟩,
  ⟨5, 0, 1, -32345547⟩,
  ⟨5, 1, 2, 6924448⟩,
  ⟨5, 2, 3, -21143042⟩,
  ⟨5, 3, 4, -30323348⟩,
  ⟨5, 4, 5, 13003067⟩,
  ⟨5, 5, 6, 19986152⟩,
  ⟨5, 6, 7, 9072780⟩,
  ⟨5, 7, 8, -25147087⟩,
  ⟨6, 0, 2, -62327236⟩,
  ⟨6, 1, 3, -2573763⟩,
  ⟨6, 2, 4, 19203739⟩,
  ⟨6, 3, 5, -59245571⟩,
  ⟨6, 4, 6, -6662966⟩,
  ⟨6, 5, 7, 28341971⟩,
  ⟨6, 6, 8, 18781561⟩,
  ⟨7, 0, 3, 135264167⟩,
  ⟨7, 1, 4, 9223722⟩,
  ⟨7, 2, 5, 1641094⟩,
  ⟨7, 3, 6, -16817961⟩,
  ⟨7, 4, 7, 11019210⟩,
  ⟨7, 5, 8, 24257380⟩
]

theorem numericRowDataChecked_4 :
    rowEntryList_4.map (rowToNumeric ⟨4, by decide⟩) = numericRowData_4 := by
  decide +kernel

def numericRowData_5 : List NumericRowEntry := [
  ⟨0, 5, 0, 160543938⟩,
  ⟨0, 6, 1, -772096646⟩,
  ⟨0, 7, 2, 150680285⟩,
  ⟨0, 8, 3, -122410154⟩,
  ⟨1, 4, 0, 57714191⟩,
  ⟨1, 5, 1, -84055787⟩,
  ⟨1, 6, 2, -173419469⟩,
  ⟨1, 7, 3, 817621606⟩,
  ⟨1, 8, 4, -1272768087⟩,
  ⟨2, 3, 0, 11295230⟩,
  ⟨2, 4, 1, 36541316⟩,
  ⟨2, 5, 2, -181828330⟩,
  ⟨2, 6, 3, -133076448⟩,
  ⟨2, 7, 4, 86288265⟩,
  ⟨2, 8, 5, -861124623⟩,
  ⟨3, 2, 0, -24815988⟩,
  ⟨3, 3, 1, -50599547⟩,
  ⟨3, 4, 2, 6698654⟩,
  ⟨3, 5, 3, -132907956⟩,
  ⟨3, 6, 4, 35137762⟩,
  ⟨3, 7, 5, 33919179⟩,
  ⟨3, 8, 6, -293036253⟩,
  ⟨4, 1, 0, -10241680⟩,
  ⟨4, 2, 1, 43618923⟩,
  ⟨4, 3, 2, 71239842⟩,
  ⟨4, 4, 3, 27177342⟩,
  ⟨4, 5, 4, -45431218⟩,
  ⟨4, 6, 5, 41533885⟩,
  ⟨4, 7, 6, 63934128⟩,
  ⟨4, 8, 7, -214411360⟩,
  ⟨5, 0, 0, 31688993⟩,
  ⟨5, 1, 1, 9888664⟩,
  ⟨5, 2, 2, -4845107⟩,
  ⟨5, 3, 3, 34212037⟩,
  ⟨5, 4, 4, -3172205⟩,
  ⟨5, 5, 5, 5715090⟩,
  ⟨5, 6, 6, 54142081⟩,
  ⟨5, 7, 7, -48900364⟩,
  ⟨5, 8, 8, -147596784⟩,
  ⟨6, 0, 1, -53903546⟩,
  ⟨6, 1, 2, 40649652⟩,
  ⟨6, 2, 3, 19129337⟩,
  ⟨6, 3, 4, 39646640⟩,
  ⟨6, 4, 5, -23829198⟩,
  ⟨6, 5, 6, -2574933⟩,
  ⟨6, 6, 7, -7391939⟩,
  ⟨6, 7, 8, -19892913⟩,
  ⟨7, 0, 2, -165809403⟩,
  ⟨7, 1, 3, -87926915⟩,
  ⟨7, 2, 4, -20371590⟩,
  ⟨7, 3, 5, -16611293⟩,
  ⟨7, 4, 6, -44679775⟩,
  ⟨7, 5, 7, 13277906⟩,
  ⟨7, 6, 8, -14870629⟩
]

theorem numericRowDataChecked_5 :
    rowEntryList_5.map (rowToNumeric ⟨5, by decide⟩) = numericRowData_5 := by
  decide +kernel

def numericRowData_6 : List NumericRowEntry := [
  ⟨0, 6, 0, -67829135⟩,
  ⟨0, 7, 1, 720057917⟩,
  ⟨0, 8, 2, -875530193⟩,
  ⟨1, 5, 0, -51790296⟩,
  ⟨1, 6, 1, 175876646⟩,
  ⟨1, 7, 2, -200676925⟩,
  ⟨1, 8, 3, -10152433⟩,
  ⟨2, 4, 0, -7378820⟩,
  ⟨2, 5, 1, 52323471⟩,
  ⟨2, 6, 2, -211371229⟩,
  ⟨2, 7, 3, 182388432⟩,
  ⟨2, 8, 4, -61003176⟩,
  ⟨3, 3, 0, -656201⟩,
  ⟨3, 4, 1, 14264883⟩,
  ⟨3, 5, 2, 26191317⟩,
  ⟨3, 6, 3, -100136184⟩,
  ⟨3, 7, 4, -183883082⟩,
  ⟨3, 8, 5, 121658379⟩,
  ⟨4, 2, 0, 2431803⟩,
  ⟨4, 3, 1, -22478098⟩,
  ⟨4, 4, 2, 1654355⟩,
  ⟨4, 5, 3, -93663294⟩,
  ⟨4, 6, 4, 109018199⟩,
  ⟨4, 7, 5, 36347410⟩,
  ⟨4, 8, 6, -91971370⟩,
  ⟨5, 1, 0, 937204⟩,
  ⟨5, 2, 1, -2276330⟩,
  ⟨5, 3, 2, 13793516⟩,
  ⟨5, 4, 3, 47941518⟩,
  ⟨5, 5, 4, 28279597⟩,
  ⟨5, 6, 5, -40367840⟩,
  ⟨5, 7, 6, 55740134⟩,
  ⟨5, 8, 7, 13007596⟩,
  ⟨6, 0, 0, -10808966⟩,
  ⟨6, 1, 1, -25113301⟩,
  ⟨6, 2, 2, -4615426⟩,
  ⟨6, 3, 3, 31886801⟩,
  ⟨6, 4, 4, -27442867⟩,
  ⟨6, 5, 5, 40912313⟩,
  ⟨6, 6, 6, -18147728⟩,
  ⟨6, 7, 7, -21491028⟩,
  ⟨6, 8, 8, 127556721⟩,
  ⟨7, 0, 1, 78650298⟩,
  ⟨7, 1, 2, 34037298⟩,
  ⟨7, 2, 3, 58687256⟩,
  ⟨7, 3, 4, 49941189⟩,
  ⟨7, 4, 5, 61860018⟩,
  ⟨7, 5, 6, 9377295⟩,
  ⟨7, 6, 7, 26910871⟩,
  ⟨7, 7, 8, 48292819⟩
]

theorem numericRowDataChecked_6 :
    rowEntryList_6.map (rowToNumeric ⟨6, by decide⟩) = numericRowData_6 := by
  decide +kernel

def numericRowData_7 : List NumericRowEntry := [
  ⟨0, 7, 0, 90151251⟩,
  ⟨0, 8, 1, 41493601⟩,
  ⟨1, 6, 0, 5671034⟩,
  ⟨1, 7, 1, 217565363⟩,
  ⟨1, 8, 2, -239274251⟩,
  ⟨2, 5, 0, -13713832⟩,
  ⟨2, 6, 1, 128996036⟩,
  ⟨2, 7, 2, -145424091⟩,
  ⟨2, 8, 3, -81564855⟩,
  ⟨3, 4, 0, 4354537⟩,
  ⟨3, 5, 1, 53285313⟩,
  ⟨3, 6, 2, -28885070⟩,
  ⟨3, 7, 3, -101829212⟩,
  ⟨3, 8, 4, -59154681⟩,
  ⟨4, 3, 0, 8355807⟩,
  ⟨4, 4, 1, -30008008⟩,
  ⟨4, 5, 2, -6707391⟩,
  ⟨4, 6, 3, -116951489⟩,
  ⟨4, 7, 4, -67400418⟩,
  ⟨4, 8, 5, 234283414⟩,
  ⟨5, 2, 0, -7051082⟩,
  ⟨5, 3, 1, -28653824⟩,
  ⟨5, 4, 2, 17782076⟩,
  ⟨5, 5, 3, -19218169⟩,
  ⟨5, 6, 4, 30912487⟩,
  ⟨5, 7, 5, -3984978⟩,
  ⟨5, 8, 6, 110000521⟩,
  ⟨6, 1, 0, 2562590⟩,
  ⟨6, 2, 1, 35701498⟩,
  ⟨6, 3, 2, 4486260⟩,
  ⟨6, 4, 3, 45335753⟩,
  ⟨6, 5, 4, -25079048⟩,
  ⟨6, 6, 5, 18952126⟩,
  ⟨6, 7, 6, 51942067⟩,
  ⟨6, 8, 7, 32561769⟩,
  ⟨7, 0, 0, -12496841⟩,
  ⟨7, 1, 1, -51081249⟩,
  ⟨7, 2, 2, -10849108⟩,
  ⟨7, 3, 3, -40398862⟩,
  ⟨7, 4, 4, -51858623⟩,
  ⟨7, 5, 5, -10716483⟩,
  ⟨7, 6, 6, -28108965⟩,
  ⟨7, 7, 7, -5754196⟩,
  ⟨7, 8, 8, -77199525⟩
]

theorem numericRowDataChecked_7 :
    rowEntryList_7.map (rowToNumeric ⟨7, by decide⟩) = numericRowData_7 := by
  decide +kernel

def numericRowData (t : Fin 8) : List NumericRowEntry :=
 ![numericRowData_0, numericRowData_1, numericRowData_2, numericRowData_3, numericRowData_4, numericRowData_5, numericRowData_6, numericRowData_7] t

theorem sum_table {α β : Type*} [Fintype α] (ls : List α) (hn : ls.Nodup)
    (tabs : List β) (g : α → β) (hu : (Finset.univ : Finset α) = ⟨(ls : Multiset α), Multiset.coe_nodup.mpr hn⟩)
    (hg : ls.map g = tabs) (f : β → ℤ) :
    ∑ x, f (g x) = (tabs.map f).sum := by
  rw [hu, Finset.sum_mk, Multiset.map_coe, Multiset.sum_coe, ← hg]
  simp only [List.map_map, Function.comp_def]

theorem numericRow_sum (t : Fin 8) (f : NumericRowEntry → ℤ) :
    ∑ b : RowEntry t.val, f (rowToNumeric t b) = ((numericRowData t).map f).sum := by
  fin_cases t
  · exact sum_table rowEntryList_0 (by decide) numericRowData_0 _ rowEntryChecked_0 numericRowDataChecked_0 f
  · exact sum_table rowEntryList_1 (by decide) numericRowData_1 _ rowEntryChecked_1 numericRowDataChecked_1 f
  · exact sum_table rowEntryList_2 (by decide) numericRowData_2 _ rowEntryChecked_2 numericRowDataChecked_2 f
  · exact sum_table rowEntryList_3 (by decide) numericRowData_3 _ rowEntryChecked_3 numericRowDataChecked_3 f
  · exact sum_table rowEntryList_4 (by decide) numericRowData_4 _ rowEntryChecked_4 numericRowDataChecked_4 f
  · exact sum_table rowEntryList_5 (by decide) numericRowData_5 _ rowEntryChecked_5 numericRowDataChecked_5 f
  · exact sum_table rowEntryList_6 (by decide) numericRowData_6 _ rowEntryChecked_6 numericRowDataChecked_6 f
  · exact sum_table rowEntryList_7 (by decide) numericRowData_7 _ rowEntryChecked_7 numericRowDataChecked_7 f

def numericRowFactor (D t : ℕ) (b c : NumericRowEntry) : ℕ :=
  2 * 2^(53+b.p+c.p-(t+2*(b.p+b.j+c.i))) *
    t.factorial * b.i.factorial * c.i.factorial *
      ((23).factorial / ((b.p+b.j+c.i)-D).factorial)

def numericRowTerm (D t r s : ℕ) (b c : NumericRowEntry) : ℤ :=
  if D ≤ b.p+b.j+c.i then
    b.a*c.a * (numericRowFactor D t b c : ℤ) *
      memoIntegerCopyPolynomial D (b.p+b.j+c.i) r b.p b.j c.i *
      memoIntegerCopyPolynomial D (b.p+b.j+c.i) s c.p c.j b.i
  else 0

def numericFourTrace (D : ℕ) (t : Fin 8) (r s : ℕ) : ℤ :=
  -(((numericRowData t).map (fun b => ((numericRowData t).map (fun c =>
    numericRowTerm D t.val r s b c)).sum)).sum)

theorem memoScaledFourTrace_numeric (D : ℕ) (t : Fin 8) (r s : CopyLabel D) :
    memoScaledFourTrace D t r s = numericFourTrace D t r.val.val s.val.val := by
  unfold memoScaledFourTrace numericFourTrace
  congr 1
  rw [← numericRow_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← numericRow_sum]
  rfl

def numericRowsFourTrace (D r s : ℕ) : ℤ :=
  ∑ t : Fin 8, numericFourTrace D t r s

theorem integerRowsFourTrace_numeric {D : ℕ} (hD : D ≤ 23) (r s : CopyLabel D) :
    integerRowsFourTrace D r s = (numericRowsFourTrace D r.val.val s.val.val : ℚ) / fourCommonDenominator := by
  rw [integerRowsFourTrace_memo hD]
  unfold memoScaledRowsFourTrace numericRowsFourTrace
  simp only [memoScaledFourTrace_numeric]

end LaughlinFock
end

end OAI
