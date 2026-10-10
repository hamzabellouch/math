import OAI.Analysis.MutuallyUnbiased.Certificate.MixedTargetBasic
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values5

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm256 : Integer.Sparse Master := [(Sum.inl 0, -39759154569953280000), (Sum.inl 1, -36144685972684800000), (Sum.inl 2, -18072342986342400000), (Sum.inl 5, 72289371945369600000), (Sum.inl 26, 289157487781478400000), (Sum.inl 34, 289157487781478400000), (Sum.inl 67, 289157487781478400000)]

def originalTerm256 : Integer.Sparse OriginalKey := [(Sum.inl 342, -41502110400)]

theorem reducedTermArithmetic256 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm256 x = (-1561450434019983360000 : ℝ) * Sparse.eval nodeValue342 x := by
  norm_num [reducedTerm256, nodeValue342, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm257 : Integer.Sparse Master := [(Sum.inl 0, -244968768737280000000), (Sum.inl 1, -1143187587440640000000), (Sum.inl 2, -81656256245760000000), (Sum.inl 3, 1306500099932160000000), (Sum.inl 5, 326625024983040000000), (Sum.inl 7, 1306500099932160000000)]

def originalTerm257 : Integer.Sparse OriginalKey := [(Sum.inl 343, -187518960000)]

theorem reducedTermArithmetic257 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm257 x = (-7055100539633664000000 : ℝ) * Sparse.eval nodeValue343 x := by
  norm_num [reducedTerm257, nodeValue343, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm258 : Integer.Sparse Master := [(Sum.inl 0, 3893389661306880000), (Sum.inl 1, -3244491384422400000), (Sum.inl 5, -3244491384422400000), (Sum.inl 8, -12977965537689600000)]

def originalTerm258 : Integer.Sparse OriginalKey := [(Sum.inl 344, 1862697600)]

theorem reducedTermArithmetic258 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm258 x = (70081013903523840000 : ℝ) * Sparse.eval nodeValue344 x := by
  norm_num [reducedTerm258, nodeValue344, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm259 : Integer.Sparse Master := [(Sum.inl 0, 22364660908800000000), (Sum.inl 1, 47924273376000000000), (Sum.inl 2, -101173466016000000000), (Sum.inl 3, -851987082240000000000), (Sum.inl 5, 42599354112000000000), (Sum.inl 6, -5324919264000000000), (Sum.inl 7, -85198708224000000000), (Sum.inl 12, -340794832896000000000), (Sum.inl 13, -596390957568000000000), (Sum.inl 34, -85198708224000000000), (Sum.inl 35, -85198708224000000000), (Sum.inl 51, 511192249344000000000), (Sum.inl 52, -255596124672000000000), (Sum.inl 54, 255596124672000000000), (Sum.inl 64, 255596124672000000000)]

def originalTerm259 : Integer.Sparse OriginalKey := [(Sum.inl 345, 24456750000)]

theorem reducedTermArithmetic259 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm259 x = (920146048819200000000 : ℝ) * Sparse.eval nodeValue345 x := by
  norm_num [reducedTerm259, nodeValue345, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm260 : Integer.Sparse Master := [(Sum.inl 0, 125095232928153600000), (Sum.inl 1, -218916657624268800000), (Sum.inl 2, 281464274088345600000), (Sum.inl 3, 500380931712614400000), (Sum.inl 5, -250190465856307200000), (Sum.inl 7, 500380931712614400000), (Sum.inl 51, -1501142795137843200000), (Sum.inl 54, -1501142795137843200000), (Sum.inl 64, -1501142795137843200000)]

def originalTerm260 : Integer.Sparse OriginalKey := [(Sum.inl 346, 143637052800)]

theorem reducedTermArithmetic260 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm260 x = (5404114062496235520000 : ℝ) * Sparse.eval nodeValue346 x := by
  norm_num [reducedTerm260, nodeValue346, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm261 : Integer.Sparse Master := [(Sum.inl 0, -22364660908800000000), (Sum.inl 2, 85198708224000000000), (Sum.inl 3, 596390957568000000000), (Sum.inl 4, 170397416448000000000), (Sum.inl 5, 63899031168000000000), (Sum.inl 6, -15974757792000000000), (Sum.inl 12, 170397416448000000000), (Sum.inl 13, 170397416448000000000), (Sum.inl 25, -255596124672000000000), (Sum.inl 26, 170397416448000000000), (Sum.inl 31, -511192249344000000000), (Sum.inl 33, -511192249344000000000), (Sum.inl 34, 85198708224000000000), (Sum.inl 51, -511192249344000000000), (Sum.inl 52, 85198708224000000000), (Sum.inl 64, -255596124672000000000), (Sum.inl 123, -511192249344000000000)]

def originalTerm261 : Integer.Sparse OriginalKey := [(Sum.inl 347, -24456750000)]

theorem reducedTermArithmetic261 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm261 x = (-920146048819200000000 : ℝ) * Sparse.eval nodeValue347 x := by
  norm_num [reducedTerm261, nodeValue347, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm262 : Integer.Sparse Master := [(Sum.inl 0, 195647888946585600000), (Sum.inl 1, -419245476314112000000), (Sum.inl 2, 326079814910976000000), (Sum.inl 3, 745325291225088000000), (Sum.inl 5, 186331322806272000000), (Sum.inl 6, -46582830701568000000), (Sum.inl 25, -2235975873675264000000), (Sum.inl 26, 745325291225088000000), (Sum.inl 64, -2235975873675264000000), (Sum.inl 123, -2235975873675264000000)]

def originalTerm262 : Integer.Sparse OriginalKey := [(Sum.inl 348, 213949656000)]

theorem reducedTermArithmetic262 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm262 x = (8049513145230950400000 : ℝ) * Sparse.eval nodeValue348 x := by
  norm_num [reducedTerm262, nodeValue348, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm263 : Integer.Sparse Master := [(Sum.inl 0, 15974757792000000000), (Sum.inl 1, 21299677056000000000), (Sum.inl 2, 10649838528000000000), (Sum.inl 5, 21299677056000000000), (Sum.inl 6, -5324919264000000000), (Sum.inl 31, -255596124672000000000), (Sum.inl 33, -255596124672000000000), (Sum.inl 51, -255596124672000000000), (Sum.inl 123, -255596124672000000000)]

def originalTerm263 : Integer.Sparse OriginalKey := [(Sum.inl 349, 24456750000)]

theorem reducedTermArithmetic263 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm263 x = (920146048819200000000 : ℝ) * Sparse.eval nodeValue349 x := by
  norm_num [reducedTerm263, nodeValue349, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm264 : Integer.Sparse Master := [(Sum.inl 0, -93165661403136000000), (Sum.inl 1, 139748492104704000000), (Sum.inl 6, -46582830701568000000), (Sum.inl 123, -2235975873675264000000)]

def originalTerm264 : Integer.Sparse OriginalKey := [(Sum.inl 350, -106974828000)]

theorem reducedTermArithmetic264 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm264 x = (-4024756572615475200000 : ℝ) * Sparse.eval nodeValue350 x := by
  norm_num [reducedTerm264, nodeValue350, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm265 : Integer.Sparse Master := [(Sum.inl 0, -9171361769472000000), (Sum.inl 1, -11005634123366400000), (Sum.inl 2, 55028170616832000000), (Sum.inl 3, 264135218960793600000), (Sum.inl 4, 88045072986931200000), (Sum.inl 5, 22011268246732800000), (Sum.inl 6, -5502817061683200000), (Sum.inl 12, 88045072986931200000), (Sum.inl 13, 58696715324620800000), (Sum.inl 51, -264135218960793600000), (Sum.inl 52, 88045072986931200000)]

def originalTerm265 : Integer.Sparse OriginalKey := [(Sum.inl 351, -8424604800)]

theorem reducedTermArithmetic265 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm265 x = (-316962262752952320000 : ℝ) * Sparse.eval nodeValue351 x := by
  norm_num [reducedTerm265, nodeValue351, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm266 : Integer.Sparse Master := [(Sum.inl 0, 7337089415577600000), (Sum.inl 1, 3668544707788800000), (Sum.inl 2, 9171361769472000000), (Sum.inl 3, 58696715324620800000), (Sum.inl 4, 29348357662310400000), (Sum.inl 5, 7337089415577600000), (Sum.inl 6, -1834272353894400000), (Sum.inl 51, -88045072986931200000), (Sum.inl 52, 29348357662310400000)]

def originalTerm266 : Integer.Sparse OriginalKey := [(Sum.inl 352, 8424604800)]

theorem reducedTermArithmetic266 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm266 x = (316962262752952320000 : ℝ) * Sparse.eval nodeValue352 x := by
  norm_num [reducedTerm266, nodeValue352, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm267 : Integer.Sparse Master := [(Sum.inl 0, -296377098135552000000), (Sum.inl 1, 548846478028800000000), (Sum.inl 2, -439077182423040000000), (Sum.inl 3, -1756308729692160000000), (Sum.inl 5, -219538591211520000000), (Sum.inl 6, 54884647802880000000), (Sum.inl 12, -878154364846080000000), (Sum.inl 13, -878154364846080000000), (Sum.inl 51, 2634463094538240000000), (Sum.inl 52, -878154364846080000000)]

def originalTerm267 : Integer.Sparse OriginalKey := [(Sum.inl 353, -252078960000)]

theorem reducedTermArithmetic267 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm267 x = (-9484067140337664000000 : ℝ) * Sparse.eval nodeValue353 x := by
  norm_num [reducedTerm267, nodeValue353, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm268 : Integer.Sparse Master := [(Sum.inl 0, -6712348286730240000), (Sum.inl 1, 9153202209177600000), (Sum.inl 5, 12204269612236800000), (Sum.inl 64, -146451235346841600000)]

def originalTerm268 : Integer.Sparse OriginalKey := [(Sum.inl 354, -7006603200)]

theorem reducedTermArithmetic268 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm268 x = (-263612223624314880000 : ℝ) * Sparse.eval nodeValue354 x := by
  norm_num [reducedTerm268, nodeValue354, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm269 : Integer.Sparse Master := [(Sum.inl 0, 305874420668006400000), (Sum.inl 1, -327722593572864000000), (Sum.inl 2, 327722593572864000000), (Sum.inl 5, -436963458097152000000), (Sum.inl 51, 5243561497165824000000)]

def originalTerm269 : Integer.Sparse OriginalKey := [(Sum.inl 355, 250865448000)]

theorem reducedTermArithmetic269 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm269 x = (9438410694898483200000 : ℝ) * Sparse.eval nodeValue355 x := by
  norm_num [reducedTerm269, nodeValue355, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm270 : Integer.Sparse Master := [(Sum.inl 0, -18066028525977600000), (Sum.inl 1, 23771090165760000000), (Sum.inl 2, -47542180331520000000), (Sum.inl 3, 152134977060864000000), (Sum.inl 5, 76067488530432000000), (Sum.inl 12, 76067488530432000000), (Sum.inl 13, 76067488530432000000), (Sum.inl 23, -456404931182592000000), (Sum.inl 25, -228202465591296000000), (Sum.inl 26, 76067488530432000000), (Sum.inl 27, -114101232795648000000), (Sum.inl 33, -228202465591296000000), (Sum.inl 35, 76067488530432000000), (Sum.inl 54, -456404931182592000000), (Sum.inl 55, -456404931182592000000), (Sum.inl 63, -456404931182592000000), (Sum.inl 64, -228202465591296000000), (Sum.inl 65, -456404931182592000000), (Sum.inl 68, -228202465591296000000), (Sum.inl 125, -228202465591296000000), (Sum.inl 196, -228202465591296000000), (Sum.inl 264, -228202465591296000000), (Sum.inl 266, -228202465591296000000)]

def originalTerm270 : Integer.Sparse OriginalKey := [(Sum.inl 356, -21835584000)]

theorem reducedTermArithmetic270 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm270 x = (-821528876128665600000 : ℝ) * Sparse.eval nodeValue356 x := by
  norm_num [reducedTerm270, nodeValue356, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm271 : Integer.Sparse Master := [(Sum.inl 0, 11103917727006720000), (Sum.inl 1, 22712558987059200000), (Sum.inl 2, -12618088326144000000), (Sum.inl 3, -323023061149286400000), (Sum.inl 5, 10094470660915200000), (Sum.inl 7, -40377882643660800000), (Sum.inl 12, -121133647930982400000), (Sum.inl 13, -242267295861964800000), (Sum.inl 23, 121133647930982400000), (Sum.inl 26, -161511530574643200000), (Sum.inl 27, -30283411982745600000), (Sum.inl 34, -80755765287321600000), (Sum.inl 35, -121133647930982400000), (Sum.inl 55, 242267295861964800000), (Sum.inl 63, 121133647930982400000), (Sum.inl 65, 121133647930982400000), (Sum.inl 67, -40377882643660800000)]

def originalTerm271 : Integer.Sparse OriginalKey := [(Sum.inl 357, 11590689600)]

theorem reducedTermArithmetic271 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm271 x = (436081132551536640000 : ℝ) * Sparse.eval nodeValue357 x := by
  norm_num [reducedTerm271, nodeValue357, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm272 : Integer.Sparse Master := [(Sum.inl 0, 67004361126420480000), (Sum.inl 1, -151300170285465600000), (Sum.inl 2, 10807155020390400000), (Sum.inl 3, -1037486881957478400000), (Sum.inl 5, -129685860244684800000), (Sum.inl 12, -345828960652492800000), (Sum.inl 13, -518743440978739200000), (Sum.inl 25, 518743440978739200000), (Sum.inl 26, -172914480326246400000), (Sum.inl 27, 389057580734054400000), (Sum.inl 33, 1556230322936217600000), (Sum.inl 35, -172914480326246400000), (Sum.inl 55, 1037486881957478400000), (Sum.inl 63, 518743440978739200000), (Sum.inl 64, 1037486881957478400000)]

def originalTerm272 : Integer.Sparse OriginalKey := [(Sum.inl 358, 49636036800)]

theorem reducedTermArithmetic272 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm272 x = (1867476387523461120000 : ℝ) * Sparse.eval nodeValue358 x := by
  norm_num [reducedTerm272, nodeValue358, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm273 : Integer.Sparse Master := [(Sum.inl 0, -8960584204615680000), (Sum.inl 1, -72182483870515200000), (Sum.inl 2, 12445255839744000000), (Sum.inl 3, 398248186871808000000), (Sum.inl 4, 159299274748723200000), (Sum.inl 5, -9956204671795200000), (Sum.inl 7, 39824818687180800000), (Sum.inl 12, 39824818687180800000), (Sum.inl 13, 39824818687180800000), (Sum.inl 24, -119474456061542400000), (Sum.inl 26, 238948912123084800000), (Sum.inl 27, 29868614015385600000), (Sum.inl 33, -119474456061542400000), (Sum.inl 34, 79649637374361600000), (Sum.inl 35, 79649637374361600000), (Sum.inl 55, -358423368184627200000), (Sum.inl 64, -119474456061542400000), (Sum.inl 66, -119474456061542400000), (Sum.inl 67, 39824818687180800000)]

def originalTerm273 : Integer.Sparse OriginalKey := [(Sum.inl 359, -11431929600)]

theorem reducedTermArithmetic273 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm273 x = (-430108041821552640000 : ℝ) * Sparse.eval nodeValue359 x := by
  norm_num [reducedTerm273, nodeValue359, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm274 : Integer.Sparse Master := [(Sum.inl 0, -30805224690401280000), (Sum.inl 1, -67952701522944000000), (Sum.inl 2, -95133782132121600000), (Sum.inl 3, 869794579493683200000), (Sum.inl 4, 434897289746841600000), (Sum.inl 5, 54362161218355200000), (Sum.inl 12, 217448644873420800000), (Sum.inl 13, 144965763248947200000), (Sum.inl 26, 434897289746841600000), (Sum.inl 27, -163086483655065600000), (Sum.inl 35, 217448644873420800000), (Sum.inl 55, -652345934620262400000)]

def originalTerm274 : Integer.Sparse OriginalKey := [(Sum.inl 360, -20806603200)]

theorem reducedTermArithmetic274 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm274 x = (-782815121544314880000 : ℝ) * Sparse.eval nodeValue360 x := by
  norm_num [reducedTerm274, nodeValue360, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm275 : Integer.Sparse Master := [(Sum.inl 0, -101826617879347200000), (Sum.inl 1, 246354720675840000000), (Sum.inl 2, 197083776540672000000), (Sum.inl 3, -525556737441792000000), (Sum.inl 5, -65694592180224000000), (Sum.inl 12, -262778368720896000000), (Sum.inl 13, -262778368720896000000), (Sum.inl 26, -262778368720896000000), (Sum.inl 27, 197083776540672000000), (Sum.inl 35, -262778368720896000000), (Sum.inl 55, 788335106162688000000)]

def originalTerm275 : Integer.Sparse OriginalKey := [(Sum.inl 361, -75431952000)]

theorem reducedTermArithmetic275 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm275 x = (-2838006382185676800000 : ℝ) * Sparse.eval nodeValue361 x := by
  norm_num [reducedTerm275, nodeValue361, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm276 : Integer.Sparse Master := [(Sum.inl 0, -73488654138654720000), (Sum.inl 1, -129685860244684800000), (Sum.inl 2, 194528790367027200000), (Sum.inl 3, -345828960652492800000), (Sum.inl 5, -86457240163123200000), (Sum.inl 27, 259371720489369600000), (Sum.inl 33, 1037486881957478400000), (Sum.inl 55, 1037486881957478400000), (Sum.inl 64, 1037486881957478400000)]

def originalTerm276 : Integer.Sparse OriginalKey := [(Sum.inl 362, -99272073600)]

theorem reducedTermArithmetic276 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm276 x = (-3734952775046922240000 : ℝ) * Sparse.eval nodeValue362 x := by
  norm_num [reducedTerm276, nodeValue362, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm277 : Integer.Sparse Master := [(Sum.inl 0, 26816045856768000000), (Sum.inl 1, 32179255028121600000), (Sum.inl 2, -5363209171353600000), (Sum.inl 3, -600679427191603200000), (Sum.inl 4, -171622693483315200000), (Sum.inl 5, 21452836685414400000), (Sum.inl 7, -85811346741657600000), (Sum.inl 12, -85811346741657600000), (Sum.inl 13, -85811346741657600000), (Sum.inl 23, 257434040224972800000), (Sum.inl 25, 514868080449945600000), (Sum.inl 26, -343245386966630400000), (Sum.inl 27, -64358510056243200000), (Sum.inl 33, 514868080449945600000), (Sum.inl 34, -171622693483315200000), (Sum.inl 35, -85811346741657600000), (Sum.inl 55, 257434040224972800000), (Sum.inl 63, 514868080449945600000), (Sum.inl 64, 514868080449945600000), (Sum.inl 65, 257434040224972800000), (Sum.inl 67, -85811346741657600000)]

def originalTerm277 : Integer.Sparse OriginalKey := [(Sum.inl 363, 24632611200)]

theorem reducedTermArithmetic277 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm277 x = (926762544809902080000 : ℝ) * Sparse.eval nodeValue363 x := by
  norm_num [reducedTerm277, nodeValue363, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm278 : Integer.Sparse Master := [(Sum.inl 0, -153380792709365760000), (Sum.inl 1, 348592710703104000000), (Sum.inl 2, 139437084281241600000), (Sum.inl 23, 1673245011374899200000), (Sum.inl 27, -836622505687449600000), (Sum.inl 55, 1673245011374899200000), (Sum.inl 63, 1673245011374899200000), (Sum.inl 65, 1673245011374899200000)]

def originalTerm278 : Integer.Sparse OriginalKey := [(Sum.inl 364, -160104676800)]

theorem reducedTermArithmetic278 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm278 x = (-6023682040949637120000 : ℝ) * Sparse.eval nodeValue364 x := by
  norm_num [reducedTerm278, nodeValue364, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm279 : Integer.Sparse Master := [(Sum.inl 0, -1768209428643840000), (Sum.inl 1, 2947015714406400000), (Sum.inl 2, 2947015714406400000), (Sum.inl 5, -1473507857203200000), (Sum.inl 25, 17682094286438400000), (Sum.inl 27, 4420523571609600000), (Sum.inl 33, 17682094286438400000), (Sum.inl 63, 17682094286438400000), (Sum.inl 64, 17682094286438400000)]

def originalTerm279 : Integer.Sparse OriginalKey := [(Sum.inl 365, -1691913600)]

theorem reducedTermArithmetic279 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm279 x = (-63655539431178240000 : ℝ) * Sparse.eval nodeValue365 x := by
  norm_num [reducedTerm279, nodeValue365, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm280 : Integer.Sparse Master := [(Sum.inl 0, -77745385499443200000), (Sum.inl 1, 70677623181312000000), (Sum.inl 2, -459404550678528000000), (Sum.inl 27, -424065739087872000000), (Sum.inl 63, -1696262956351488000000)]

def originalTerm280 : Integer.Sparse OriginalKey := [(Sum.inl 366, -81153576000)]

theorem reducedTermArithmetic280 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm280 x = (-3053273321432678400000 : ℝ) * Sparse.eval nodeValue366 x := by
  norm_num [reducedTerm280, nodeValue366, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm281 : Integer.Sparse Master := [(Sum.inl 0, 6969343270256640000), (Sum.inl 1, 29868614015385600000), (Sum.inl 2, 4978102335897600000), (Sum.inl 24, -119474456061542400000), (Sum.inl 27, 59737228030771200000), (Sum.inl 55, -238948912123084800000), (Sum.inl 66, -119474456061542400000)]

def originalTerm281 : Integer.Sparse OriginalKey := [(Sum.inl 367, 11431929600)]

theorem reducedTermArithmetic281 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm281 x = (430108041821552640000 : ℝ) * Sparse.eval nodeValue367 x := by
  norm_num [reducedTerm281, nodeValue367, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm282 : Integer.Sparse Master := [(Sum.inl 0, 19499786217676800000), (Sum.inl 1, -3362032106496000000), (Sum.inl 3, 161377541111808000000), (Sum.inl 4, 107585027407872000000), (Sum.inl 5, 13448128425984000000), (Sum.inl 26, 107585027407872000000), (Sum.inl 27, -40344385277952000000), (Sum.inl 35, 53792513703936000000), (Sum.inl 55, -161377541111808000000)]

def originalTerm282 : Integer.Sparse OriginalKey := [(Sum.inl 368, 15441432000)]

theorem reducedTermArithmetic282 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm282 x = (580959148002508800000 : ℝ) * Sparse.eval nodeValue368 x := by
  norm_num [reducedTerm282, nodeValue368, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm283 : Integer.Sparse Master := [(Sum.inl 0, 82917618300518400000), (Sum.inl 1, -165835236601036800000), (Sum.inl 2, -82917618300518400000), (Sum.inl 27, 331670473202073600000), (Sum.inl 55, 1326681892808294400000)]

def originalTerm283 : Integer.Sparse OriginalKey := [(Sum.inl 369, 63471868800)]

theorem reducedTermArithmetic283 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm283 x = (2388027407054929920000 : ℝ) * Sparse.eval nodeValue369 x := by
  norm_num [reducedTerm283, nodeValue369, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm284 : Integer.Sparse Master := [(Sum.inl 0, -278981671152844800000), (Sum.inl 1, -1634035502466662400000), (Sum.inl 2, -318836195603251200000), (Sum.inl 3, 4463706738445516800000), (Sum.inl 4, 2550689564826009600000), (Sum.inl 5, 159418097801625600000), (Sum.inl 26, 2550689564826009600000), (Sum.inl 27, -478254293404876800000), (Sum.inl 35, 637672391206502400000), (Sum.inl 55, -1913017173619507200000)]

def originalTerm284 : Integer.Sparse OriginalKey := [(Sum.inl 371, -183047308800)]

theorem reducedTermArithmetic284 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm284 x = (-6886861825030225920000 : ℝ) * Sparse.eval nodeValue371 x := by
  norm_num [reducedTerm284, nodeValue371, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm285 : Integer.Sparse Master := [(Sum.inl 0, -5993222226647040000), (Sum.inl 1, -24517727290828800000), (Sum.inl 2, 21793535369625600000), (Sum.inl 3, 130761212217753600000), (Sum.inl 12, 87174141478502400000), (Sum.inl 13, 217935353696256000000), (Sum.inl 26, 87174141478502400000), (Sum.inl 34, 87174141478502400000)]

def originalTerm285 : Integer.Sparse OriginalKey := [(Sum.inl 373, -12511904400)]

theorem reducedTermArithmetic285 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm285 x = (-470740363983912960000 : ℝ) * Sparse.eval nodeValue373 x := by
  norm_num [reducedTerm285, nodeValue373, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm286 : Integer.Sparse Master := [(Sum.inl 0, -18179750891151360000), (Sum.inl 1, -68174065841817600000), (Sum.inl 2, -68174065841817600000), (Sum.inl 13, -363595017823027200000)]

def originalTerm286 : Integer.Sparse OriginalKey := [(Sum.inl 374, -52185958200)]

theorem reducedTermArithmetic286 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm286 x = (-1963413096244346880000 : ℝ) * Sparse.eval nodeValue374 x := by
  norm_num [reducedTerm286, nodeValue374, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm287 : Integer.Sparse Master := []

def originalTerm287 : Integer.Sparse OriginalKey := [(Sum.inl 375, 66564864000)]

theorem reducedTermArithmetic287 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm287 x = (2504396397713817600000 : ℝ) * Sparse.eval nodeValue375 x := by
  norm_num [reducedTerm287, nodeValue375, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
