import Mathlib
import OAI.Analysis.LaughlinGap.Certificate9
import OAI.Analysis.LaughlinGap.SumTable10

namespace OAI

/-! Certificate10. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate10

def keys : Fin 6 → Finset (Fin 25) := ![{0,1,2,8}, {0,1,3,7}, {0,1,4,6}, {0,2,3,6}, {0,2,4,5}, {1,2,3,5}]
def fibers : Fin 6 → Finset (FourTerm 10) := ![{⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}]
def columns : Matrix (Fin 5) (Fin 6) ℚ := ![![0, 0, 0, 0, 0, 0], ![-15120, 15120, -7560, -7560, 7560, 0], ![0, 0, 0, 0, 0, 0], ![11340, -11340, 5670, 5670, -5670, 0], ![-45360, 45360, -22680, -22680, 22680, 0]]
def Y : Matrix (Fin 5) (Fin 5) ℚ := ![![(200175459945085632193532343/6710886400000000000000), (-19934932341438578630554461/1677721600000000000000), (10688091490272052643120847/1342177280000000000000), (-25539656102181318071634093/3355443200000000000000), (20785777850578541715752031/838860800000000000000)], ![(-19934932341438578630554461/1677721600000000000000), (-23824125720222220870749/671088640000000000000), (-423999878564625416871237/335544320000000000000), (3981191132086811594405091/838860800000000000000), (-581783066891519285684403/41943040000000000000)], ![(10688091490272052643120847/1342177280000000000000), (-423999878564625416871237/335544320000000000000), (13103624809638522434317689/9395240960000000000000), (-2284683579713664648267057/671088640000000000000), (1918711872693053907602859/167772160000000000000)], ![(-25539656102181318071634093/3355443200000000000000), (3981191132086811594405091/838860800000000000000), (-2284683579713664648267057/671088640000000000000), (3925235702466226344344823/1677721600000000000000), (-1818861828136206279263793/419430400000000000000)], ![(20785777850578541715752031/838860800000000000000), (-581783066891519285684403/41943040000000000000), (1918711872693053907602859/167772160000000000000), (-1818861828136206279263793/419430400000000000000), (-7907022897840128737456029/104857600000000000000)]]
def Z : Matrix (Fin 5) (Fin 5) ℚ := ![![0, 0, 0, 0, 0], ![0, 30240, 0, -22680, 90720], ![0, 0, 0, 0, 0], ![0, -22680, 0, 17010, -68040], ![0, 90720, 0, -68040, 272160]]
def W : Matrix (Fin 5) (Fin 5) ℚ := ![![0, 0, 0, 0, 0], ![(-2093488721107348396109/36077725286400000000000000), (438867827883403177801057/1879048192000000000000000), (-1237433244599578471138079/4294967296000000000000000), (-474042061158101800190781/7516192768000000000000000), (1831244066560386205163291/22548578304000000000000000)], ![0, 0, 0, 0, 0], ![(2093488721107348396109/48103633715200000000000000), (-1316603483650209533403171/7516192768000000000000000), (3712299733798735413414237/17179869184000000000000000), (1422126183474305400572343/30064771072000000000000000), (-1831244066560386205163291/30064771072000000000000000)], ![(-2093488721107348396109/12025908428800000000000000), (1316603483650209533403171/1879048192000000000000000), (-3712299733798735413414237/4294967296000000000000000), (-1422126183474305400572343/7516192768000000000000000), (1831244066560386205163291/7516192768000000000000000)]]
def M : Matrix (Fin 5) (Fin 5) ℚ := ![![0, 0, 0, 0, 0], ![0, (425762667787958128783145313/26843545600000000000000), 0, (-1277288003363874386349435939/107374182400000000000000), (1277288003363874386349435939/26843545600000000000000)], ![0, 0, 0, 0, 0], ![0, (-1277288003363874386349435939/107374182400000000000000), 0, (3831864010091623159048307817/429496729600000000000000), (-3831864010091623159048307817/107374182400000000000000)], ![0, (1277288003363874386349435939/26843545600000000000000), 0, (-3831864010091623159048307817/107374182400000000000000), (3831864010091623159048307817/26843545600000000000000)]]
def L : Matrix (Fin 5) (Fin 5) ℚ := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, (-3/4), 0, 1, 0], ![0, 3, 0, 0, 1]]
def diag : Fin 5 → ℚ := ![0, (425762667787958128783145313/26843545600000000000000), 0, 0, 0]

def keyIndexTable : Fin 11 → Fin 13 → Fin 13 → Fin 6 := ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def keyIndex (n : Fin 11) (j : Fin ((n.val+1)/2)) (x : Fin ((10-n.val+2)/2)) : Fin 6 :=
  keyIndexTable n ⟨j.val,by have := j.isLt; have := n.isLt; omega⟩ ⟨x.val,by have := x.isLt; omega⟩
def representatives : Fin 6 → FourTerm 10 := ![⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩]
lemma cover_0 : ∀ j : Fin 0, ∀ x : Fin 6,
  (fourTermLabels (by omega : 10 ≤ 23) ⟨0,j,x⟩).Nodup →
    (fourTermLabels (by omega : 10 ≤ 23) ⟨0,j,x⟩).toFinset=keys (keyIndex 0 j x) := by decide +kernel
lemma cover_1 : ∀ j : Fin 1, ∀ x : Fin 5,
  (fourTermLabels (by omega : 10 ≤ 23) ⟨1,j,x⟩).Nodup →
    (fourTermLabels (by omega : 10 ≤ 23) ⟨1,j,x⟩).toFinset=keys (keyIndex 1 j x) := by decide +kernel
lemma cover_2 : ∀ j : Fin 1, ∀ x : Fin 5,
  (fourTermLabels (by omega : 10 ≤ 23) ⟨2,j,x⟩).Nodup →
    (fourTermLabels (by omega : 10 ≤ 23) ⟨2,j,x⟩).toFinset=keys (keyIndex 2 j x) := by decide +kernel
lemma cover_3 : ∀ j : Fin 2, ∀ x : Fin 4,
  (fourTermLabels (by omega : 10 ≤ 23) ⟨3,j,x⟩).Nodup →
    (fourTermLabels (by omega : 10 ≤ 23) ⟨3,j,x⟩).toFinset=keys (keyIndex 3 j x) := by decide +kernel
lemma cover_4 : ∀ j : Fin 2, ∀ x : Fin 4,
  (fourTermLabels (by omega : 10 ≤ 23) ⟨4,j,x⟩).Nodup →
    (fourTermLabels (by omega : 10 ≤ 23) ⟨4,j,x⟩).toFinset=keys (keyIndex 4 j x) := by decide +kernel
lemma cover_5 : ∀ j : Fin 3, ∀ x : Fin 3,
  (fourTermLabels (by omega : 10 ≤ 23) ⟨5,j,x⟩).Nodup →
    (fourTermLabels (by omega : 10 ≤ 23) ⟨5,j,x⟩).toFinset=keys (keyIndex 5 j x) := by decide +kernel
lemma cover_6 : ∀ j : Fin 3, ∀ x : Fin 3,
  (fourTermLabels (by omega : 10 ≤ 23) ⟨6,j,x⟩).Nodup →
    (fourTermLabels (by omega : 10 ≤ 23) ⟨6,j,x⟩).toFinset=keys (keyIndex 6 j x) := by decide +kernel
lemma cover_7 : ∀ j : Fin 4, ∀ x : Fin 2,
  (fourTermLabels (by omega : 10 ≤ 23) ⟨7,j,x⟩).Nodup →
    (fourTermLabels (by omega : 10 ≤ 23) ⟨7,j,x⟩).toFinset=keys (keyIndex 7 j x) := by decide +kernel
lemma cover_8 : ∀ j : Fin 4, ∀ x : Fin 2,
  (fourTermLabels (by omega : 10 ≤ 23) ⟨8,j,x⟩).Nodup →
    (fourTermLabels (by omega : 10 ≤ 23) ⟨8,j,x⟩).toFinset=keys (keyIndex 8 j x) := by decide +kernel
lemma cover_9 : ∀ j : Fin 5, ∀ x : Fin 1,
  (fourTermLabels (by omega : 10 ≤ 23) ⟨9,j,x⟩).Nodup →
    (fourTermLabels (by omega : 10 ≤ 23) ⟨9,j,x⟩).toFinset=keys (keyIndex 9 j x) := by decide +kernel
lemma cover_10 : ∀ j : Fin 5, ∀ x : Fin 1,
  (fourTermLabels (by omega : 10 ≤ 23) ⟨10,j,x⟩).Nodup →
    (fourTermLabels (by omega : 10 ≤ 23) ⟨10,j,x⟩).toFinset=keys (keyIndex 10 j x) := by decide +kernel
lemma cover : ∀ b : FourTerm 10, (fourTermLabels (by omega : 10 ≤ 23) b).Nodup →
    (fourTermLabels (by omega : 10 ≤ 23) b).toFinset=keys (keyIndex b.1 b.2.1 b.2.2) := by
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
lemma representatives_checked : ∀ a : Fin 6,
  (fourTermLabels (by omega : 10 ≤ 23) (representatives a)).Nodup ∧
  (fourTermLabels (by omega : 10 ≤ 23) (representatives a)).toFinset=keys a := by decide +kernel
lemma keys_checked : fourKeys (by omega : 10 ≤ 23) = Finset.univ.image keys :=
  fourKeys_of_index (by omega : 10 ≤ 23) keys (fun b => keyIndex b.1 b.2.1 b.2.2)
    representatives cover representatives_checked
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma keys_card : ∀ a : Fin 6, (keys a).card=4 := by decide +kernel
lemma fibers_cover : ∀ b : FourTerm 10,
    (fourTermLabels (by omega : 10 ≤ 23) b).Nodup →
      b ∈ fibers (keyIndex b.1 b.2.1 b.2.2) := by
  apply checkFourTerms_sound
  decide +kernel
lemma fibers_sound : ∀ a : Fin 6, ∀ b ∈ fibers a,
    (fourTermLabels (by omega : 10 ≤ 23) b).toFinset=keys a := by
  apply checkFourFibersSound_sound
  decide +kernel
lemma fibers_checked : ∀ a : Fin 6, ∀ b : FourTerm 10,
    (fourTermLabels (by omega : 10 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a :=
  fourFibers_of_index (by omega : 10 ≤ 23) keys
    (fun b => keyIndex b.1 b.2.1 b.2.2) fibers keys_injective keys_card cover fibers_cover fibers_sound
lemma columns_checked_0 : ∀ v : Fin 6, (∑ b ∈ fibers v, fourTermEval 10 (2*(0 : Fin 5).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 10 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 6, (∑ b ∈ fibers v, fourTermEval 10 (2*(1 : Fin 5).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 10 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 6, (∑ b ∈ fibers v, fourTermEval 10 (2*(2 : Fin 5).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 10 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_3 : ∀ v : Fin 6, (∑ b ∈ fibers v, fourTermEval 10 (2*(3 : Fin 5).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 10 ≤ 23) b)) = columns 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_4 : ∀ v : Fin 6, (∑ b ∈ fibers v, fourTermEval 10 (2*(4 : Fin 5).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 10 ≤ 23) b)) = columns 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 5, ∀ v : Fin 6, (∑ b ∈ fibers v, fourTermEval 10 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 10 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
  · exact columns_checked_3
  · exact columns_checked_4
lemma gram_checked_0 : ∀ v : Fin 5, (∑ a : Fin 6, columns (0 : Fin 5) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 5, (∑ a : Fin 6, columns (1 : Fin 5) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 5, (∑ a : Fin 6, columns (2 : Fin 5) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_3 : ∀ v : Fin 5, (∑ a : Fin 6, columns (3 : Fin 5) a * columns v a / setFactorial (keys a)) = Z 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_4 : ∀ v : Fin 5, (∑ a : Fin 6, columns (4 : Fin 5) a * columns v a / setFactorial (keys a)) = Z 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked : ∀ u : Fin 5, ∀ v : Fin 5, (∑ a : Fin 6, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
  · exact gram_checked_3
  · exact gram_checked_4
lemma rows_table_checked_0 : ∀ v : Fin 5, integerTableEval 10 SumTable10.sums (0 : Fin 5) v = Y 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_1 : ∀ v : Fin 5, integerTableEval 10 SumTable10.sums (1 : Fin 5) v = Y 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_2 : ∀ v : Fin 5, integerTableEval 10 SumTable10.sums (2 : Fin 5) v = Y 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_3 : ∀ v : Fin 5, integerTableEval 10 SumTable10.sums (3 : Fin 5) v = Y 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_4 : ∀ v : Fin 5, integerTableEval 10 SumTable10.sums (4 : Fin 5) v = Y 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked : ∀ u : Fin 5, ∀ v : Fin 5, integerTableEval 10 SumTable10.sums u v = Y u v := by
  intro u
  fin_cases u
  · exact rows_table_checked_0
  · exact rows_table_checked_1
  · exact rows_table_checked_2
  · exact rows_table_checked_3
  · exact rows_table_checked_4
lemma rows_checked (u v : Fin 5) : exactFourEval 10 (2*u.val+1) (2*v.val+1) = Y u v := by
  rw [exactFourEval_table 10 SumTable10.sums SumTable10.sums_checked]
  exact rows_table_checked u v
lemma product_checked_0 : ∀ v : Fin 5, (Z * tableComparison 10 (1/200000) Y) (0 : Fin 5) v = W 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_1 : ∀ v : Fin 5, (Z * tableComparison 10 (1/200000) Y) (1 : Fin 5) v = W 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_2 : ∀ v : Fin 5, (Z * tableComparison 10 (1/200000) Y) (2 : Fin 5) v = W 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_3 : ∀ v : Fin 5, (Z * tableComparison 10 (1/200000) Y) (3 : Fin 5) v = W 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_4 : ∀ v : Fin 5, (Z * tableComparison 10 (1/200000) Y) (4 : Fin 5) v = W 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked : ∀ u : Fin 5, ∀ v : Fin 5, (Z * tableComparison 10 (1/200000) Y) u v = W u v := by
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
lemma certificate : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 10 (by omega) := by
  have hh := fourCertificate_of_tables exactRows (1/200000) (by omega : 10 ≤ 23) Y Z
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 10 (by omega) by simpa using this
  apply hh
  · intro u v
    rw [exactFourEval_eq (by omega)]
    exact rows_checked u v
  · intro u v
    rw [rationalCreatedGram_of_columns (by omega : 10 ≤ 23) keys columns keys_checked keys_injective]
    · exact gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 10 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  · rw [Matrix.ext product_checked, Matrix.ext compression_checked]
    apply rational_ldl_positive M L diag diag_checked
    ext u v
    rw [Matrix.mul_apply]
    simpa only [Matrix.mul_diagonal,Matrix.transpose_apply] using (ldl_checked u v).symm
end Certificate10
end LaughlinGap.RealOccupation

end

end OAI
