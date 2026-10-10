import Mathlib
import OAI.Analysis.LaughlinGap.CachedIntegerRows
import OAI.Analysis.LaughlinGap.FastFourKeys
import OAI.Analysis.LaughlinGap.FourTables
import OAI.Analysis.LaughlinGap.SumTable9

namespace OAI

/-! Certificate9. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate9

def keys : Fin 5 → Finset (Fin 25) := ![{0,1,2,7}, {0,1,3,6}, {0,1,4,5}, {0,2,3,5}, {1,2,3,4}]
def fibers : Fin 5 → Finset (FourTerm 9) := ![{⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}]
def columns : Matrix (Fin 5) (Fin 5) ℚ := ![![7560, -7560, 10080, -2520, 2520], ![1890, -1890, 1080, 810, -810], ![-945, 945, -540, -405, 405], ![-945, 945, -1260, 315, -315], ![22680, -22680, 22680, 0, 0]]
def Y : Matrix (Fin 5) (Fin 5) ℚ := ![![(-1993356271308944354745267/3355443200000000000000), (-3284709033344580598207581/3355443200000000000000), (220435709772188372765463/3355443200000000000000), (18025848804266699467101/20971520000000000000), (-5110372706225052814324011/419430400000000000000)], ![(-3284709033344580598207581/3355443200000000000000), (-6303681221439531121448661/46976204800000000000000), (3680632002651070355996409/23488102400000000000000), (-4180244998969476023589/33554432000000000000), (-101619883073527424950473/83886080000000000000)], ![(220435709772188372765463/3355443200000000000000), (3680632002651070355996409/23488102400000000000000), (-7301855792057631625658517/23488102400000000000000), (221714838839488589341929/419430400000000000000), (72921350514083330593971/83886080000000000000)], ![(18025848804266699467101/20971520000000000000), (-4180244998969476023589/33554432000000000000), (221714838839488589341929/419430400000000000000), (-351953897925137600168457/209715200000000000000), (-3864463501759889910633/2621440000000000000)], ![(-5110372706225052814324011/419430400000000000000), (-101619883073527424950473/83886080000000000000), (72921350514083330593971/83886080000000000000), (-3864463501759889910633/2621440000000000000), (-4006946887530397561029987/52428800000000000000)]]
def Z : Matrix (Fin 5) (Fin 5) ℚ := ![![80640, 0, 0, -10080, 136080], ![0, 4320, -2160, 0, 22680], ![0, -2160, 1080, 0, -11340], ![-10080, 0, 0, 1260, -17010], ![136080, 22680, -11340, -17010, 348705]]
def W : Matrix (Fin 5) (Fin 5) ℚ := ![![(187789732893557986355732909/45097156608000000000000000), (852854645877236107590373/1610612736000000000000000), (26558559273364667810549/1073741824000000000000000), (-66283059844861654687943/234881024000000000000000), (114410356059279766804427/805306368000000000000000)], ![(76256789444904740126269/1717986918400000000000000), (3418297737558505895268851/45097156608000000000000000), (-662438168393439514960939/4294967296000000000000000), (114303922948592796181173/1879048192000000000000000), (137534591949037451604679/7516192768000000000000000)], ![(-76256789444904740126269/3435973836800000000000000), (-3418297737558505895268851/90194313216000000000000000), (662438168393439514960939/8589934592000000000000000), (-114303922948592796181173/3758096384000000000000000), (-137534591949037451604679/15032385536000000000000000)], ![(-187789732893557986355732909/360777252864000000000000000), (-852854645877236107590373/12884901888000000000000000), (-26558559273364667810549/8589934592000000000000000), (66283059844861654687943/1879048192000000000000000), (-114410356059279766804427/6442450944000000000000000)], ![(218269542035503357649300487/30064771072000000000000000), (10833974170364873890217/8388608000000000000000), (-824632527242586486455931/1073741824000000000000000), (-1178902849702080633344289/7516192768000000000000000), (36057424509515756401347/107374182400000000000000)]]
def M : Matrix (Fin 5) (Fin 5) ℚ := ![![(240230765972923924837514271/671088640000000000000), (73232800741607405694442011/13421772800000000000000), (-73232800741607405694442011/26843545600000000000000), (-240230765972923924837514271/5368709120000000000000), (2123065138869905335790481801/3355443200000000000000)], ![(73232800741607405694442011/13421772800000000000000), (404223759648674750677002093/375809638400000000000000), (-404223759648674750677002093/751619276800000000000000), (-73232800741607405694442011/107374182400000000000000), (99686153092794506430654393/6710886400000000000000)], ![(-73232800741607405694442011/26843545600000000000000), (-404223759648674750677002093/751619276800000000000000), (404223759648674750677002093/1503238553600000000000000), (73232800741607405694442011/214748364800000000000000), (-99686153092794506430654393/13421772800000000000000)], ![(-240230765972923924837514271/5368709120000000000000), (-73232800741607405694442011/107374182400000000000000), (73232800741607405694442011/214748364800000000000000), (240230765972923924837514271/42949672960000000000000), (-2123065138869905335790481801/26843545600000000000000)], ![(2123065138869905335790481801/3355443200000000000000), (99686153092794506430654393/6710886400000000000000), (-99686153092794506430654393/13421772800000000000000), (-2123065138869905335790481801/26843545600000000000000), (61509577179384813336430493133/53687091200000000000000)]]
def L : Matrix (Fin 5) (Fin 5) ℚ := ![![1, 0, 0, 0, 0], ![(24410933580535801898147337/1601538439819492832250095140), 1, 0, 0, 0], ![(-24410933580535801898147337/3203076879638985664500190280), (-1/2), 1, 0, 0], ![(-1/8), 0, 0, 1, 0], ![(707688379623301778596827267/400384609954873208062523785), (21/4), 0, 0, 1]]
def diag : Fin 5 → ℚ := ![(240230765972923924837514271/671088640000000000000), (9333200318605444737087413951811823601046190946453691/9404274718004121289989064264515584000000000000000), 0, 0, 0]

def keyIndexTable : Fin 10 → Fin 13 → Fin 13 → Fin 5 := ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def keyIndex (n : Fin 10) (j : Fin ((n.val+1)/2)) (x : Fin ((9-n.val+2)/2)) : Fin 5 :=
  keyIndexTable n ⟨j.val,by have := j.isLt; have := n.isLt; omega⟩ ⟨x.val,by have := x.isLt; omega⟩
def representatives : Fin 5 → FourTerm 9 := ![⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩]
lemma cover_0 : ∀ j : Fin 0, ∀ x : Fin 5,
  (fourTermLabels (by omega : 9 ≤ 23) ⟨0,j,x⟩).Nodup →
    (fourTermLabels (by omega : 9 ≤ 23) ⟨0,j,x⟩).toFinset=keys (keyIndex 0 j x) := by decide +kernel
lemma cover_1 : ∀ j : Fin 1, ∀ x : Fin 5,
  (fourTermLabels (by omega : 9 ≤ 23) ⟨1,j,x⟩).Nodup →
    (fourTermLabels (by omega : 9 ≤ 23) ⟨1,j,x⟩).toFinset=keys (keyIndex 1 j x) := by decide +kernel
lemma cover_2 : ∀ j : Fin 1, ∀ x : Fin 4,
  (fourTermLabels (by omega : 9 ≤ 23) ⟨2,j,x⟩).Nodup →
    (fourTermLabels (by omega : 9 ≤ 23) ⟨2,j,x⟩).toFinset=keys (keyIndex 2 j x) := by decide +kernel
lemma cover_3 : ∀ j : Fin 2, ∀ x : Fin 4,
  (fourTermLabels (by omega : 9 ≤ 23) ⟨3,j,x⟩).Nodup →
    (fourTermLabels (by omega : 9 ≤ 23) ⟨3,j,x⟩).toFinset=keys (keyIndex 3 j x) := by decide +kernel
lemma cover_4 : ∀ j : Fin 2, ∀ x : Fin 3,
  (fourTermLabels (by omega : 9 ≤ 23) ⟨4,j,x⟩).Nodup →
    (fourTermLabels (by omega : 9 ≤ 23) ⟨4,j,x⟩).toFinset=keys (keyIndex 4 j x) := by decide +kernel
lemma cover_5 : ∀ j : Fin 3, ∀ x : Fin 3,
  (fourTermLabels (by omega : 9 ≤ 23) ⟨5,j,x⟩).Nodup →
    (fourTermLabels (by omega : 9 ≤ 23) ⟨5,j,x⟩).toFinset=keys (keyIndex 5 j x) := by decide +kernel
lemma cover_6 : ∀ j : Fin 3, ∀ x : Fin 2,
  (fourTermLabels (by omega : 9 ≤ 23) ⟨6,j,x⟩).Nodup →
    (fourTermLabels (by omega : 9 ≤ 23) ⟨6,j,x⟩).toFinset=keys (keyIndex 6 j x) := by decide +kernel
lemma cover_7 : ∀ j : Fin 4, ∀ x : Fin 2,
  (fourTermLabels (by omega : 9 ≤ 23) ⟨7,j,x⟩).Nodup →
    (fourTermLabels (by omega : 9 ≤ 23) ⟨7,j,x⟩).toFinset=keys (keyIndex 7 j x) := by decide +kernel
lemma cover_8 : ∀ j : Fin 4, ∀ x : Fin 1,
  (fourTermLabels (by omega : 9 ≤ 23) ⟨8,j,x⟩).Nodup →
    (fourTermLabels (by omega : 9 ≤ 23) ⟨8,j,x⟩).toFinset=keys (keyIndex 8 j x) := by decide +kernel
lemma cover_9 : ∀ j : Fin 5, ∀ x : Fin 1,
  (fourTermLabels (by omega : 9 ≤ 23) ⟨9,j,x⟩).Nodup →
    (fourTermLabels (by omega : 9 ≤ 23) ⟨9,j,x⟩).toFinset=keys (keyIndex 9 j x) := by decide +kernel
lemma cover : ∀ b : FourTerm 9, (fourTermLabels (by omega : 9 ≤ 23) b).Nodup →
    (fourTermLabels (by omega : 9 ≤ 23) b).toFinset=keys (keyIndex b.1 b.2.1 b.2.2) := by
  rintro ⟨n,j,x⟩
  fin_cases n
  · exact cover_0 j x
  · exact cover_1 j x
  · exact cover_2 j x
  · exact cover_3 j x
  · exact cover_4 j x
  · exact cover_5 j x
  · exact cover_6 j x
  · exact cover_7 j x
  · exact cover_8 j x
  · exact cover_9 j x
lemma representatives_checked : ∀ a : Fin 5,
  (fourTermLabels (by omega : 9 ≤ 23) (representatives a)).Nodup ∧
  (fourTermLabels (by omega : 9 ≤ 23) (representatives a)).toFinset=keys a := by decide +kernel
lemma keys_checked : fourKeys (by omega : 9 ≤ 23) = Finset.univ.image keys :=
  fourKeys_of_index (by omega : 9 ≤ 23) keys (fun b => keyIndex b.1 b.2.1 b.2.2)
    representatives cover representatives_checked
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma keys_card : ∀ a : Fin 5, (keys a).card=4 := by decide +kernel
lemma fibers_cover : ∀ b : FourTerm 9,
    (fourTermLabels (by omega : 9 ≤ 23) b).Nodup →
      b ∈ fibers (keyIndex b.1 b.2.1 b.2.2) := by
  apply checkFourTerms_sound
  decide +kernel
lemma fibers_sound : ∀ a : Fin 5, ∀ b ∈ fibers a,
    (fourTermLabels (by omega : 9 ≤ 23) b).toFinset=keys a := by
  apply checkFourFibersSound_sound
  decide +kernel
lemma fibers_checked : ∀ a : Fin 5, ∀ b : FourTerm 9,
    (fourTermLabels (by omega : 9 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a :=
  fourFibers_of_index (by omega : 9 ≤ 23) keys
    (fun b => keyIndex b.1 b.2.1 b.2.2) fibers keys_injective keys_card cover fibers_cover fibers_sound
lemma columns_checked_0 : ∀ v : Fin 5, (∑ b ∈ fibers v, fourTermEval 9 (2*(0 : Fin 5).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 9 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 5, (∑ b ∈ fibers v, fourTermEval 9 (2*(1 : Fin 5).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 9 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 5, (∑ b ∈ fibers v, fourTermEval 9 (2*(2 : Fin 5).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 9 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_3 : ∀ v : Fin 5, (∑ b ∈ fibers v, fourTermEval 9 (2*(3 : Fin 5).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 9 ≤ 23) b)) = columns 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_4 : ∀ v : Fin 5, (∑ b ∈ fibers v, fourTermEval 9 (2*(4 : Fin 5).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 9 ≤ 23) b)) = columns 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 5, ∀ v : Fin 5, (∑ b ∈ fibers v, fourTermEval 9 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 9 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
  · exact columns_checked_3
  · exact columns_checked_4
lemma gram_checked_0 : ∀ v : Fin 5, (∑ a : Fin 5, columns (0 : Fin 5) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 5, (∑ a : Fin 5, columns (1 : Fin 5) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 5, (∑ a : Fin 5, columns (2 : Fin 5) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_3 : ∀ v : Fin 5, (∑ a : Fin 5, columns (3 : Fin 5) a * columns v a / setFactorial (keys a)) = Z 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_4 : ∀ v : Fin 5, (∑ a : Fin 5, columns (4 : Fin 5) a * columns v a / setFactorial (keys a)) = Z 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked : ∀ u : Fin 5, ∀ v : Fin 5, (∑ a : Fin 5, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
  · exact gram_checked_3
  · exact gram_checked_4
lemma rows_table_checked_0 : ∀ v : Fin 5, integerTableEval 9 SumTable9.sums (0 : Fin 5) v = Y 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_1 : ∀ v : Fin 5, integerTableEval 9 SumTable9.sums (1 : Fin 5) v = Y 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_2 : ∀ v : Fin 5, integerTableEval 9 SumTable9.sums (2 : Fin 5) v = Y 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_3 : ∀ v : Fin 5, integerTableEval 9 SumTable9.sums (3 : Fin 5) v = Y 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_4 : ∀ v : Fin 5, integerTableEval 9 SumTable9.sums (4 : Fin 5) v = Y 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked : ∀ u : Fin 5, ∀ v : Fin 5, integerTableEval 9 SumTable9.sums u v = Y u v := by
  intro u
  fin_cases u
  · exact rows_table_checked_0
  · exact rows_table_checked_1
  · exact rows_table_checked_2
  · exact rows_table_checked_3
  · exact rows_table_checked_4
lemma rows_checked (u v : Fin 5) : exactFourEval 9 (2*u.val+1) (2*v.val+1) = Y u v := by
  rw [exactFourEval_table 9 SumTable9.sums SumTable9.sums_checked]
  exact rows_table_checked u v
lemma product_checked_0 : ∀ v : Fin 5, (Z * tableComparison 9 (1/200000) Y) (0 : Fin 5) v = W 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_1 : ∀ v : Fin 5, (Z * tableComparison 9 (1/200000) Y) (1 : Fin 5) v = W 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_2 : ∀ v : Fin 5, (Z * tableComparison 9 (1/200000) Y) (2 : Fin 5) v = W 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_3 : ∀ v : Fin 5, (Z * tableComparison 9 (1/200000) Y) (3 : Fin 5) v = W 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_4 : ∀ v : Fin 5, (Z * tableComparison 9 (1/200000) Y) (4 : Fin 5) v = W 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked : ∀ u : Fin 5, ∀ v : Fin 5, (Z * tableComparison 9 (1/200000) Y) u v = W u v := by
  intro u
  fin_cases u
  · exact product_checked_0
  · exact product_checked_1
  · exact product_checked_2
  · exact product_checked_3
  · exact product_checked_4
lemma compression_checked_0 : ∀ v : Fin 5, (W * Z) (0 : Fin 5) v = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_1 : ∀ v : Fin 5, (W * Z) (1 : Fin 5) v = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_2 : ∀ v : Fin 5, (W * Z) (2 : Fin 5) v = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_3 : ∀ v : Fin 5, (W * Z) (3 : Fin 5) v = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_4 : ∀ v : Fin 5, (W * Z) (4 : Fin 5) v = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked : ∀ u : Fin 5, ∀ v : Fin 5, (W * Z) u v = M u v := by
  intro u
  fin_cases u
  · exact compression_checked_0
  · exact compression_checked_1
  · exact compression_checked_2
  · exact compression_checked_3
  · exact compression_checked_4
lemma ldl_checked_0 : ∀ v : Fin 5, (∑ k : Fin 5, L (0 : Fin 5) k * diag k * L v k) = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_1 : ∀ v : Fin 5, (∑ k : Fin 5, L (1 : Fin 5) k * diag k * L v k) = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_2 : ∀ v : Fin 5, (∑ k : Fin 5, L (2 : Fin 5) k * diag k * L v k) = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_3 : ∀ v : Fin 5, (∑ k : Fin 5, L (3 : Fin 5) k * diag k * L v k) = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_4 : ∀ v : Fin 5, (∑ k : Fin 5, L (4 : Fin 5) k * diag k * L v k) = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked : ∀ u : Fin 5, ∀ v : Fin 5, (∑ k : Fin 5, L u k * diag k * L v k) = M u v := by
  intro u
  fin_cases u
  · exact ldl_checked_0
  · exact ldl_checked_1
  · exact ldl_checked_2
  · exact ldl_checked_3
  · exact ldl_checked_4
lemma diag_checked : ∀ u : Fin 5, 0 ≤ diag u := by decide +kernel
lemma certificate : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 9 (by omega) := by
  have hh := fourCertificate_of_tables exactRows (1/200000) (by omega : 9 ≤ 23) Y Z
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 9 (by omega) by simpa using this
  apply hh
  · intro u v
    rw [exactFourEval_eq (by omega)]
    exact rows_checked u v
  · intro u v
    rw [rationalCreatedGram_of_columns (by omega : 9 ≤ 23) keys columns keys_checked keys_injective]
    · exact gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 9 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  · rw [Matrix.ext product_checked, Matrix.ext compression_checked]
    apply rational_ldl_positive M L diag diag_checked
    ext u v
    rw [Matrix.mul_apply]
    simpa only [Matrix.mul_diagonal,Matrix.transpose_apply] using (ldl_checked u v).symm
end Certificate9
end LaughlinGap.RealOccupation

end

end OAI
