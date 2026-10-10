import Mathlib
import OAI.Analysis.LaughlinGap.Certificate11
import OAI.Analysis.LaughlinGap.SumTable12

namespace OAI

/-! Certificate12. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate12

def keys : Fin 11 → Finset (Fin 25) := ![{0,1,2,10}, {0,1,3,9}, {0,1,4,8}, {0,1,5,7}, {0,2,3,8}, {0,2,4,7}, {0,2,5,6}, {0,3,4,6}, {1,2,3,7}, {1,2,4,6}, {1,3,4,5}]
def fibers : Fin 11 → Finset (FourTerm 12) := ![{⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}]
def columns : Matrix (Fin 6) (Fin 11) ℚ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-680400, 680400, -544320, 340200, -136080, 204120, -340200, 68040, -68040, 68040, -68040], ![-340200, 340200, -151200, 18900, -189000, 132300, -18900, -56700, 56700, -56700, 56700], ![255150, -255150, 113400, -14175, 141750, -99225, 14175, 42525, -42525, 42525, -42525], ![340200, -340200, 272160, -170100, 68040, -102060, 170100, -34020, 34020, -34020, 34020], ![-3742200, 3742200, -2494800, 1247400, -1247400, 1247400, -1247400, 0, 0, 0, 0]]
def Y : Matrix (Fin 6) (Fin 6) ℚ := ![![(-25480875896934727535824239/671088640000000000000), (89493563396161211226564537/335544320000000000000), (166617976074040701955346877/671088640000000000000), (-68908946150186095152447963/335544320000000000000), (-25261277378610897429618879/83886080000000000000), (24314236929984946889366037/41943040000000000000)], ![(89493563396161211226564537/335544320000000000000), (-84840177041796958213951827/838860800000000000000), (1570462128759565556774181/335544320000000000000), (2675787208095664591891893/167772160000000000000), (5394085570915940511708381/209715200000000000000), (-4711060210477871245903083/20971520000000000000)], ![(166617976074040701955346877/671088640000000000000), (1570462128759565556774181/335544320000000000000), (-4242903069423142887860187/671088640000000000000), (2505282131696810822676621/335544320000000000000), (-2309313931847977215171231/83886080000000000000), (7605543623364889538589/1677721600000000000)], ![(-68908946150186095152447963/335544320000000000000), (2675787208095664591891893/167772160000000000000), (2505282131696810822676621/335544320000000000000), (-4977035602351515226990971/167772160000000000000), (-611262446479920805714839/41943040000000000000), (6855650584852976870654493/20971520000000000000)], ![(-25261277378610897429618879/83886080000000000000), (5394085570915940511708381/209715200000000000000), (-2309313931847977215171231/83886080000000000000), (-611262446479920805714839/41943040000000000000), (1163227959375792088481937/52428800000000000000), (-776247942028571351610579/1048576000000000000)], ![(24314236929984946889366037/41943040000000000000), (-4711060210477871245903083/20971520000000000000), (7605543623364889538589/1677721600000000000), (6855650584852976870654493/20971520000000000000), (-776247942028571351610579/1048576000000000000), (-5553844753995143389657467/2621440000000000000)]]
def Z : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 0, 0, 0], ![0, 2177280, 0, 0, -1088640, 7484400], ![0, 0, 604800, -453600, 0, 2494800], ![0, 0, -453600, 340200, 0, -1871100], ![0, -1088640, 0, 0, 544320, -3742200], ![0, 7484400, 2494800, -1871100, -3742200, 36018675]]
def W : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 0, 0, 0], ![(-396155945114164818001911/30064771072000000000000000), (1077945941863588424540261/15032385536000000000000000), (-479577620617163210726943/15032385536000000000000000), (-1050502813209997889578023/7516192768000000000000000), (30617903177108088595711/536870912000000000000000), (11852149758487795318257/1879048192000000000000000)], ![(-283112681317272526766123/25769803776000000000000000), (58882953858944877176681/6012954214400000000000000), (1736159344095910418535643/90194313216000000000000000), (-3739388252132182340848349/45097156608000000000000000), (26042765295165198837787/901943132160000000000000), (105371752445598966041579/11274289152000000000000000)], ![(283112681317272526766123/34359738368000000000000000), (-176648861576834631530043/24051816857600000000000000), (-1736159344095910418535643/120259084288000000000000000), (3739388252132182340848349/60129542144000000000000000), (-26042765295165198837787/1202590842880000000000000), (-105371752445598966041579/15032385536000000000000000)], ![(396155945114164818001911/60129542144000000000000000), (-1077945941863588424540261/30064771072000000000000000), (479577620617163210726943/30064771072000000000000000), (1050502813209997889578023/15032385536000000000000000), (-30617903177108088595711/1073741824000000000000000), (-11852149758487795318257/3758096384000000000000000)], ![(-170266615010582224808971/1879048192000000000000000), (431266963682645425524167/1503238553600000000000000), (-113734630451390031032653/3758096384000000000000000), (-441566631696445936054121/536870912000000000000000), (29608833092745380921469/93952409600000000000000), (56592422300575542780047/939524096000000000000000)]]
def M : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 0, 0, 0], ![0, (473961496050849923949854007/3355443200000000000000), (16062813445261653386739783/268435456000000000000), (-48188440335784960160219349/1073741824000000000000), (-473961496050849923949854007/6710886400000000000000), (245748146094610061633139321/335544320000000000000)], ![0, (16062813445261653386739783/268435456000000000000), (194805171953981096565244923/2684354560000000000000), (-584415515861943289695734769/10737418240000000000000), (-16062813445261653386739783/536870912000000000000), (338932636622760339625203837/671088640000000000000)], ![0, (-48188440335784960160219349/1073741824000000000000), (-584415515861943289695734769/10737418240000000000000), (1753246547585829869087204307/42949672960000000000000), (48188440335784960160219349/2147483648000000000000), (-1016797909868281018875611511/2684354560000000000000)], ![0, (-473961496050849923949854007/6710886400000000000000), (-16062813445261653386739783/536870912000000000000), (48188440335784960160219349/2147483648000000000000), (473961496050849923949854007/13421772800000000000000), (-245748146094610061633139321/671088640000000000000)], ![0, (245748146094610061633139321/335544320000000000000), (338932636622760339625203837/671088640000000000000), (-1016797909868281018875611511/2684354560000000000000), (-245748146094610061633139321/671088640000000000000), (6175231260938661149363597319/1342177280000000000000)]]
def L : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, (4957658470759769563808575/11702752988909874665428494), 1, 0, 0, 0], ![0, (-4957658470759769563808575/15603670651879832887237992), (-3/4), 1, 0, 0], ![0, (-1/2), 0, 0, 1, 0], ![0, (10113092431876957268853470/1950458831484979110904749), (33/8), 0, 0, 1]]
def diag : Fin 6 → ℚ := ![0, (473961496050849923949854007/3355443200000000000000), (643844347625087164297573368870578086732258837953/13634695464554623041307053916160000000000000), 0, 0, 0]

def keyIndexTable : Fin 13 → Fin 13 → Fin 13 → Fin 11 := ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 4, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 8, 9, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 5, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 9, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![7, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def keyIndex (n : Fin 13) (j : Fin ((n.val+1)/2)) (x : Fin ((12-n.val+2)/2)) : Fin 11 :=
  keyIndexTable n ⟨j.val,by have := j.isLt; have := n.isLt; omega⟩ ⟨x.val,by have := x.isLt; omega⟩
def representatives : Fin 11 → FourTerm 12 := ![⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩]
lemma cover_0 : ∀ j : Fin 0, ∀ x : Fin 7,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨0,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨0,j,x⟩).toFinset=keys (keyIndex 0 j x) := by decide +kernel
lemma cover_1 : ∀ j : Fin 1, ∀ x : Fin 6,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨1,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨1,j,x⟩).toFinset=keys (keyIndex 1 j x) := by decide +kernel
lemma cover_2 : ∀ j : Fin 1, ∀ x : Fin 6,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨2,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨2,j,x⟩).toFinset=keys (keyIndex 2 j x) := by decide +kernel
lemma cover_3 : ∀ j : Fin 2, ∀ x : Fin 5,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨3,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨3,j,x⟩).toFinset=keys (keyIndex 3 j x) := by decide +kernel
lemma cover_4 : ∀ j : Fin 2, ∀ x : Fin 5,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨4,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨4,j,x⟩).toFinset=keys (keyIndex 4 j x) := by decide +kernel
lemma cover_5 : ∀ j : Fin 3, ∀ x : Fin 4,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨5,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨5,j,x⟩).toFinset=keys (keyIndex 5 j x) := by decide +kernel
lemma cover_6 : ∀ j : Fin 3, ∀ x : Fin 4,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨6,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨6,j,x⟩).toFinset=keys (keyIndex 6 j x) := by decide +kernel
lemma cover_7 : ∀ j : Fin 4, ∀ x : Fin 3,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨7,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨7,j,x⟩).toFinset=keys (keyIndex 7 j x) := by decide +kernel
lemma cover_8 : ∀ j : Fin 4, ∀ x : Fin 3,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨8,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨8,j,x⟩).toFinset=keys (keyIndex 8 j x) := by decide +kernel
lemma cover_9 : ∀ j : Fin 5, ∀ x : Fin 2,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨9,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨9,j,x⟩).toFinset=keys (keyIndex 9 j x) := by decide +kernel
lemma cover_10 : ∀ j : Fin 5, ∀ x : Fin 2,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨10,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨10,j,x⟩).toFinset=keys (keyIndex 10 j x) := by decide +kernel
lemma cover_11 : ∀ j : Fin 6, ∀ x : Fin 1,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨11,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨11,j,x⟩).toFinset=keys (keyIndex 11 j x) := by decide +kernel
lemma cover_12 : ∀ j : Fin 6, ∀ x : Fin 1,
  (fourTermLabels (by omega : 12 ≤ 23) ⟨12,j,x⟩).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) ⟨12,j,x⟩).toFinset=keys (keyIndex 12 j x) := by decide +kernel
lemma cover : ∀ b : FourTerm 12, (fourTermLabels (by omega : 12 ≤ 23) b).Nodup →
    (fourTermLabels (by omega : 12 ≤ 23) b).toFinset=keys (keyIndex b.1 b.2.1 b.2.2) := by
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
  · exact cover_10 j x
  · exact cover_11 j x
  · exact cover_12 j x
lemma representatives_checked : ∀ a : Fin 11,
  (fourTermLabels (by omega : 12 ≤ 23) (representatives a)).Nodup ∧
  (fourTermLabels (by omega : 12 ≤ 23) (representatives a)).toFinset=keys a := by decide +kernel
lemma keys_checked : fourKeys (by omega : 12 ≤ 23) = Finset.univ.image keys :=
  fourKeys_of_index (by omega : 12 ≤ 23) keys (fun b => keyIndex b.1 b.2.1 b.2.2)
    representatives cover representatives_checked
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma keys_card : ∀ a : Fin 11, (keys a).card=4 := by decide +kernel
lemma fibers_cover : ∀ b : FourTerm 12,
    (fourTermLabels (by omega : 12 ≤ 23) b).Nodup →
      b ∈ fibers (keyIndex b.1 b.2.1 b.2.2) := by
  apply checkFourTerms_sound
  decide +kernel
lemma fibers_sound : ∀ a : Fin 11, ∀ b ∈ fibers a,
    (fourTermLabels (by omega : 12 ≤ 23) b).toFinset=keys a := by
  apply checkFourFibersSound_sound
  decide +kernel
lemma fibers_checked : ∀ a : Fin 11, ∀ b : FourTerm 12,
    (fourTermLabels (by omega : 12 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a :=
  fourFibers_of_index (by omega : 12 ≤ 23) keys
    (fun b => keyIndex b.1 b.2.1 b.2.2) fibers keys_injective keys_card cover fibers_cover fibers_sound
lemma columns_checked_0 : ∀ v : Fin 11, (∑ b ∈ fibers v, fourTermEval 12 (2*(0 : Fin 6).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 12 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 11, (∑ b ∈ fibers v, fourTermEval 12 (2*(1 : Fin 6).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 12 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 11, (∑ b ∈ fibers v, fourTermEval 12 (2*(2 : Fin 6).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 12 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_3 : ∀ v : Fin 11, (∑ b ∈ fibers v, fourTermEval 12 (2*(3 : Fin 6).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 12 ≤ 23) b)) = columns 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_4 : ∀ v : Fin 11, (∑ b ∈ fibers v, fourTermEval 12 (2*(4 : Fin 6).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 12 ≤ 23) b)) = columns 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_5 : ∀ v : Fin 11, (∑ b ∈ fibers v, fourTermEval 12 (2*(5 : Fin 6).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 12 ≤ 23) b)) = columns 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 6, ∀ v : Fin 11, (∑ b ∈ fibers v, fourTermEval 12 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 12 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
  · exact columns_checked_3
  · exact columns_checked_4
  · exact columns_checked_5
lemma gram_checked_0 : ∀ v : Fin 6, (∑ a : Fin 11, columns (0 : Fin 6) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 6, (∑ a : Fin 11, columns (1 : Fin 6) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 6, (∑ a : Fin 11, columns (2 : Fin 6) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_3 : ∀ v : Fin 6, (∑ a : Fin 11, columns (3 : Fin 6) a * columns v a / setFactorial (keys a)) = Z 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_4 : ∀ v : Fin 6, (∑ a : Fin 11, columns (4 : Fin 6) a * columns v a / setFactorial (keys a)) = Z 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_5 : ∀ v : Fin 6, (∑ a : Fin 11, columns (5 : Fin 6) a * columns v a / setFactorial (keys a)) = Z 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked : ∀ u : Fin 6, ∀ v : Fin 6, (∑ a : Fin 11, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
  · exact gram_checked_3
  · exact gram_checked_4
  · exact gram_checked_5
lemma rows_table_checked_0 : ∀ v : Fin 6, integerTableEval 12 SumTable12.sums (0 : Fin 6) v = Y 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_1 : ∀ v : Fin 6, integerTableEval 12 SumTable12.sums (1 : Fin 6) v = Y 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_2 : ∀ v : Fin 6, integerTableEval 12 SumTable12.sums (2 : Fin 6) v = Y 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_3 : ∀ v : Fin 6, integerTableEval 12 SumTable12.sums (3 : Fin 6) v = Y 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_4 : ∀ v : Fin 6, integerTableEval 12 SumTable12.sums (4 : Fin 6) v = Y 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_5 : ∀ v : Fin 6, integerTableEval 12 SumTable12.sums (5 : Fin 6) v = Y 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked : ∀ u : Fin 6, ∀ v : Fin 6, integerTableEval 12 SumTable12.sums u v = Y u v := by
  intro u
  fin_cases u
  · exact rows_table_checked_0
  · exact rows_table_checked_1
  · exact rows_table_checked_2
  · exact rows_table_checked_3
  · exact rows_table_checked_4
  · exact rows_table_checked_5
lemma rows_checked (u v : Fin 6) : exactFourEval 12 (2*u.val+1) (2*v.val+1) = Y u v := by
  rw [exactFourEval_table 12 SumTable12.sums SumTable12.sums_checked]
  exact rows_table_checked u v
lemma product_checked_0 : ∀ v : Fin 6, (Z * tableComparison 12 (1/200000) Y) (0 : Fin 6) v = W 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_1 : ∀ v : Fin 6, (Z * tableComparison 12 (1/200000) Y) (1 : Fin 6) v = W 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_2 : ∀ v : Fin 6, (Z * tableComparison 12 (1/200000) Y) (2 : Fin 6) v = W 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_3 : ∀ v : Fin 6, (Z * tableComparison 12 (1/200000) Y) (3 : Fin 6) v = W 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_4 : ∀ v : Fin 6, (Z * tableComparison 12 (1/200000) Y) (4 : Fin 6) v = W 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_5 : ∀ v : Fin 6, (Z * tableComparison 12 (1/200000) Y) (5 : Fin 6) v = W 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked : ∀ u : Fin 6, ∀ v : Fin 6, (Z * tableComparison 12 (1/200000) Y) u v = W u v := by
  intro u
  fin_cases u
  · exact product_checked_0
  · exact product_checked_1
  · exact product_checked_2
  · exact product_checked_3
  · exact product_checked_4
  · exact product_checked_5
lemma compression_checked_0 : ∀ v : Fin 6, (W * Z) (0 : Fin 6) v = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_1 : ∀ v : Fin 6, (W * Z) (1 : Fin 6) v = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_2 : ∀ v : Fin 6, (W * Z) (2 : Fin 6) v = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_3 : ∀ v : Fin 6, (W * Z) (3 : Fin 6) v = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_4 : ∀ v : Fin 6, (W * Z) (4 : Fin 6) v = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_5 : ∀ v : Fin 6, (W * Z) (5 : Fin 6) v = M 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked : ∀ u : Fin 6, ∀ v : Fin 6, (W * Z) u v = M u v := by
  intro u
  fin_cases u
  · exact compression_checked_0
  · exact compression_checked_1
  · exact compression_checked_2
  · exact compression_checked_3
  · exact compression_checked_4
  · exact compression_checked_5
lemma ldl_checked_0 : ∀ v : Fin 6, (∑ k : Fin 6, L (0 : Fin 6) k * diag k * L v k) = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_1 : ∀ v : Fin 6, (∑ k : Fin 6, L (1 : Fin 6) k * diag k * L v k) = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_2 : ∀ v : Fin 6, (∑ k : Fin 6, L (2 : Fin 6) k * diag k * L v k) = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_3 : ∀ v : Fin 6, (∑ k : Fin 6, L (3 : Fin 6) k * diag k * L v k) = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_4 : ∀ v : Fin 6, (∑ k : Fin 6, L (4 : Fin 6) k * diag k * L v k) = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_5 : ∀ v : Fin 6, (∑ k : Fin 6, L (5 : Fin 6) k * diag k * L v k) = M 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked : ∀ u : Fin 6, ∀ v : Fin 6, (∑ k : Fin 6, L u k * diag k * L v k) = M u v := by
  intro u
  fin_cases u
  · exact ldl_checked_0
  · exact ldl_checked_1
  · exact ldl_checked_2
  · exact ldl_checked_3
  · exact ldl_checked_4
  · exact ldl_checked_5
lemma diag_checked : ∀ u : Fin 6, 0 ≤ diag u := by decide +kernel
lemma certificate : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 12 (by omega) := by
  have hh := fourCertificate_of_tables exactRows (1/200000) (by omega : 12 ≤ 23) Y Z
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 12 (by omega) by simpa using this
  apply hh
  · intro u v
    rw [exactFourEval_eq (by omega)]
    exact rows_checked u v
  · intro u v
    rw [rationalCreatedGram_of_columns (by omega : 12 ≤ 23) keys columns keys_checked keys_injective]
    · exact gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 12 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  · rw [Matrix.ext product_checked, Matrix.ext compression_checked]
    apply rational_ldl_positive M L diag diag_checked
    ext u v
    rw [Matrix.mul_apply]
    simpa only [Matrix.mul_diagonal,Matrix.transpose_apply] using (ldl_checked u v).symm
end Certificate12
end LaughlinGap.RealOccupation

end

end OAI
