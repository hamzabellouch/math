import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Part8

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

def node288 : Integer.Sparse (Fin 2886) := [(2104, -425156256), (2108, -1700625024), (2199, 425156256), (2264, -425156256), (2279, 1700625024), (2309, 425156256), (2337, 138097584), (2347, -138097584), (2511, 138097584), (2515, 414292752), (2587, -138097584), (2622, 138097584), (2634, -414292752), (2655, -138097584), (2676, 138097584), (2712, -138097584)]

theorem node288_check : node288 =
    Integer.Sparse.merge (Integer.Sparse.scale (2952474) entry_11_4) (Integer.Sparse.scale (-959011) entry_11_5) := by decide +kernel

theorem node288_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node288 x = (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x) := by
  rw [node288_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node289 : Integer.Sparse (Fin 2886) := [(2104, -425156256), (2108, -1700625024), (2119, -962700480), (2134, 962700480), (2147, -3850801920), (2181, -962700480), (2199, 425156256), (2224, 3850801920), (2247, 962700480), (2264, -425156256), (2279, 1700625024), (2309, 425156256), (2337, 138097584), (2347, -138097584), (2511, 138097584), (2515, 414292752), (2587, -138097584), (2622, 138097584), (2634, -414292752), (2655, -138097584), (2676, 138097584), (2712, -138097584)]

theorem node289_check : node289 =
    Integer.Sparse.merge (Integer.Sparse.scale (6685420) entry_11_3) node288 := by decide +kernel

theorem node289_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node289 x = (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x)) := by
  rw [node289_check, Integer.Sparse.eval_merge]
  rw [node288_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node290 : Integer.Sparse (Fin 2886) := [(841, -217779840), (844, -166542768), (849, -666171072), (952, 166542768), (1028, -166542768), (1043, 217779840), (1047, 666171072), (1083, 166542768), (2104, -425156256), (2108, -1700625024), (2111, 809850816), (2114, -809850816), (2119, -962700480), (2134, 962700480), (2147, -3850801920), (2181, -962700480), (2199, 425156256), (2206, 3239403264), (2224, 3850801920), (2247, 962700480), (2264, -425156256), (2270, -3239403264), (2279, 1700625024), (2281, 809850816), (2309, 425156256), (2311, -809850816), (2337, 138097584), (2347, -138097584), (2511, 138097584), (2515, 414292752), (2587, -138097584), (2622, 138097584), (2634, -414292752), (2655, -138097584), (2676, 138097584), (2712, -138097584)]

theorem node290_check : node290 =
    Integer.Sparse.merge node287 node289 := by decide +kernel

theorem node290_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node290 x = ((((5623964 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x)) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x))) := by
  rw [node290_check, Integer.Sparse.eval_merge]
  rw [node287_eval, node289_eval]

def node291 : Integer.Sparse (Fin 2886) := [(1120, -358882848), (1127, 358882848), (1363, -358882848), (1368, -1076648544), (1436, 358882848), (1464, -358882848), (1473, 1076648544), (1496, 358882848), (1583, -358882848), (1621, 358882848), (2333, 475391088), (2337, 950782176), (2347, 950782176), (2511, -475391088), (2515, -950782176), (2634, 950782176), (2655, 475391088), (2676, -950782176), (2712, -950782176), (2733, -475391088)]

theorem node291_check : node291 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3301327) entry_11_7) (Integer.Sparse.scale (2492242) entry_11_8) := by decide +kernel

theorem node291_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node291 x = (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x) := by
  rw [node291_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node292 : Integer.Sparse (Fin 2886) := [(1120, -358882848), (1127, 358882848), (1363, -358882848), (1368, -1076648544), (1436, 358882848), (1464, -358882848), (1473, 1076648544), (1496, 358882848), (1583, -358882848), (1621, 358882848), (2102, 2219898240), (2261, -2219898240), (2333, 475391088), (2337, 950782176), (2347, 950782176), (2511, -475391088), (2515, -950782176), (2634, 950782176), (2655, 475391088), (2676, -950782176), (2712, -950782176), (2733, -475391088)]

theorem node292_check : node292 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3083192) entry_11_6) node291 := by decide +kernel

theorem node292_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node292 x = (((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x)) := by
  rw [node292_check, Integer.Sparse.eval_merge]
  rw [node291_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node293 : Integer.Sparse (Fin 2886) := [(1113, -330983424), (1124, 330983424), (1360, -1323933696), (1469, 1323933696), (1580, -330983424), (1618, 330983424), (2333, 568253664), (2337, -568253664), (2511, 568253664), (2515, -568253664), (2587, 1704760992), (2622, -1704760992), (2634, 568253664), (2655, -568253664), (2712, 568253664), (2733, -568253664)]

theorem node293_check : node293 =
    Integer.Sparse.merge (Integer.Sparse.scale (3946206) entry_11_9) (Integer.Sparse.scale (2298496) entry_11_10) := by decide +kernel

theorem node293_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node293 x = (((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x) := by
  rw [node293_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node294 : Integer.Sparse (Fin 2886) := [(2103, 3252384288), (2104, 1110369600), (2106, 4878576432), (2108, 1665554400), (2198, 4878576432), (2199, 1665554400), (2264, -1665554400), (2277, -9757152864), (2279, -1665554400), (2308, -3252384288), (2309, -1110369600)]

theorem node294_check : node294 =
    Integer.Sparse.merge (Integer.Sparse.scale (11293001) entry_11_11) (Integer.Sparse.scale (3855450) entry_11_12) := by decide +kernel

theorem node294_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node294 x = (((11293001 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x) := by
  rw [node294_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node295 : Integer.Sparse (Fin 2886) := [(1113, -330983424), (1124, 330983424), (1360, -1323933696), (1469, 1323933696), (1580, -330983424), (1618, 330983424), (2103, 3252384288), (2104, 1110369600), (2106, 4878576432), (2108, 1665554400), (2198, 4878576432), (2199, 1665554400), (2264, -1665554400), (2277, -9757152864), (2279, -1665554400), (2308, -3252384288), (2309, -1110369600), (2333, 568253664), (2337, -568253664), (2511, 568253664), (2515, -568253664), (2587, 1704760992), (2622, -1704760992), (2634, 568253664), (2655, -568253664), (2712, 568253664), (2733, -568253664)]

theorem node295_check : node295 =
    Integer.Sparse.merge node293 node294 := by decide +kernel

theorem node295_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node295 x = ((((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x) + (((11293001 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x)) := by
  rw [node295_check, Integer.Sparse.eval_merge]
  rw [node293_eval, node294_eval]

def node296 : Integer.Sparse (Fin 2886) := [(1113, -330983424), (1120, -358882848), (1124, 330983424), (1127, 358882848), (1360, -1323933696), (1363, -358882848), (1368, -1076648544), (1436, 358882848), (1464, -358882848), (1469, 1323933696), (1473, 1076648544), (1496, 358882848), (1580, -330983424), (1583, -358882848), (1618, 330983424), (1621, 358882848), (2102, 2219898240), (2103, 3252384288), (2104, 1110369600), (2106, 4878576432), (2108, 1665554400), (2198, 4878576432), (2199, 1665554400), (2261, -2219898240), (2264, -1665554400), (2277, -9757152864), (2279, -1665554400), (2308, -3252384288), (2309, -1110369600), (2333, 1043644752), (2337, 382528512), (2347, 950782176), (2511, 92862576), (2515, -1519035840), (2587, 1704760992), (2622, -1704760992), (2634, 1519035840), (2655, -92862576), (2676, -950782176), (2712, -382528512), (2733, -1043644752)]

theorem node296_check : node296 =
    Integer.Sparse.merge node292 node295 := by decide +kernel

theorem node296_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node296 x = ((((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x)) + ((((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x) + (((11293001 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x))) := by
  rw [node296_check, Integer.Sparse.eval_merge]
  rw [node292_eval, node295_eval]

def node297 : Integer.Sparse (Fin 2886) := [(841, -217779840), (844, -166542768), (849, -666171072), (952, 166542768), (1028, -166542768), (1043, 217779840), (1047, 666171072), (1083, 166542768), (1113, -330983424), (1120, -358882848), (1124, 330983424), (1127, 358882848), (1360, -1323933696), (1363, -358882848), (1368, -1076648544), (1436, 358882848), (1464, -358882848), (1469, 1323933696), (1473, 1076648544), (1496, 358882848), (1580, -330983424), (1583, -358882848), (1618, 330983424), (1621, 358882848), (2102, 2219898240), (2103, 3252384288), (2104, 685213344), (2106, 4878576432), (2108, -35070624), (2111, 809850816), (2114, -809850816), (2119, -962700480), (2134, 962700480), (2147, -3850801920), (2181, -962700480), (2198, 4878576432), (2199, 2090710656), (2206, 3239403264), (2224, 3850801920), (2247, 962700480), (2261, -2219898240), (2264, -2090710656), (2270, -3239403264), (2277, -9757152864), (2279, 35070624), (2281, 809850816), (2308, -3252384288), (2309, -685213344), (2311, -809850816), (2333, 1043644752), (2337, 520626096), (2347, 812684592), (2511, 230960160), (2515, -1104743088), (2587, 1566663408), (2622, -1566663408), (2634, 1104743088), (2655, -230960160), (2676, -812684592), (2712, -520626096), (2733, -1043644752)]

theorem node297_check : node297 =
    Integer.Sparse.merge node290 node296 := by decide +kernel

theorem node297_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node297 x = (((((5623964 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x)) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x))) + ((((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x)) + ((((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x) + (((11293001 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x)))) := by
  rw [node297_check, Integer.Sparse.eval_merge]
  rw [node290_eval, node296_eval]

def node298 : Integer.Sparse (Fin 2886) := [(844, 264840768), (849, 397261152), (952, 397261152), (1028, -397261152), (1047, -397261152), (1083, -264840768), (2103, 213103728), (2106, 852414912), (2198, -213103728), (2277, -639311184), (2308, -213103728)]

theorem node298_check : node298 =
    Integer.Sparse.merge (Integer.Sparse.scale (919586) entry_11_14) (Integer.Sparse.scale (-1479887) entry_11_15) := by decide +kernel

theorem node298_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node298 x = (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x) := by
  rw [node298_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node299 : Integer.Sparse (Fin 2886) := [(844, 264840768), (849, 397261152), (952, 397261152), (1028, -397261152), (1047, -397261152), (1083, -264840768), (1799, -29895264), (1800, -119581056), (2053, 29895264), (2067, -29895264), (2090, 119581056), (2099, 29895264), (2103, 213103728), (2106, 852414912), (2198, -213103728), (2277, -639311184), (2308, -213103728)]

theorem node299_check : node299 =
    Integer.Sparse.merge (Integer.Sparse.scale (207606) entry_11_13) node298 := by decide +kernel

theorem node299_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node299 x = (((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x)) := by
  rw [node299_check, Integer.Sparse.eval_merge]
  rw [node298_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node300 : Integer.Sparse (Fin 2886) := [(2119, 836897616), (2134, 557931744), (2147, -836897616), (2181, -557931744), (2224, 836897616), (2247, -836897616), (2342, -437936112), (2349, 437936112), (2518, -875872224), (2521, -875872224), (2594, 875872224), (2627, -875872224), (2636, 875872224), (2657, 875872224), (2678, -437936112), (2714, 437936112)]

theorem node300_check : node300 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1937263) entry_11_16) (Integer.Sparse.scale (3041223) entry_11_17) := by decide +kernel

theorem node300_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node300 x = (((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x) := by
  rw [node300_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node301 : Integer.Sparse (Fin 2886) := [(852, -282021120), (856, 282021120), (961, -1128084480), (1036, 1128084480), (1050, -282021120), (1086, 282021120), (2163, -4301709120), (2240, 4301709120)]

theorem node301_check : node301 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1958480) entry_11_18) (Integer.Sparse.scale (5974596) entry_11_19) := by decide +kernel

theorem node301_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node301 x = (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + ((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x) := by
  rw [node301_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node302 : Integer.Sparse (Fin 2886) := [(852, -282021120), (856, 282021120), (961, -1128084480), (1036, 1128084480), (1050, -282021120), (1086, 282021120), (2119, 836897616), (2134, 557931744), (2147, -836897616), (2163, -4301709120), (2181, -557931744), (2224, 836897616), (2240, 4301709120), (2247, -836897616), (2342, -437936112), (2349, 437936112), (2518, -875872224), (2521, -875872224), (2594, 875872224), (2627, -875872224), (2636, 875872224), (2657, 875872224), (2678, -437936112), (2714, 437936112)]

theorem node302_check : node302 =
    Integer.Sparse.merge node300 node301 := by decide +kernel

theorem node302_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node302 x = ((((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + ((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x)) := by
  rw [node302_check, Integer.Sparse.eval_merge]
  rw [node300_eval, node301_eval]

def node303 : Integer.Sparse (Fin 2886) := [(844, 264840768), (849, 397261152), (852, -282021120), (856, 282021120), (952, 397261152), (961, -1128084480), (1028, -397261152), (1036, 1128084480), (1047, -397261152), (1050, -282021120), (1083, -264840768), (1086, 282021120), (1799, -29895264), (1800, -119581056), (2053, 29895264), (2067, -29895264), (2090, 119581056), (2099, 29895264), (2103, 213103728), (2106, 852414912), (2119, 836897616), (2134, 557931744), (2147, -836897616), (2163, -4301709120), (2181, -557931744), (2198, -213103728), (2224, 836897616), (2240, 4301709120), (2247, -836897616), (2277, -639311184), (2308, -213103728), (2342, -437936112), (2349, 437936112), (2518, -875872224), (2521, -875872224), (2594, 875872224), (2627, -875872224), (2636, 875872224), (2657, 875872224), (2678, -437936112), (2714, 437936112)]

theorem node303_check : node303 =
    Integer.Sparse.merge node299 node302 := by decide +kernel

theorem node303_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node303 x = ((((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x)) + ((((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + ((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x))) := by
  rw [node303_check, Integer.Sparse.eval_merge]
  rw [node299_eval, node302_eval]

def node304 : Integer.Sparse (Fin 2886) := [(2120, 338487120), (2148, -2101394304), (2151, -4879762848), (2183, -2439881424), (2214, 3568171824), (2217, 3116855664), (2226, 3116855664), (2249, 3116855664), (2284, -1353948480), (2290, -676974240), (2301, -676974240), (2332, 338487120), (2335, -3116855664), (2345, 2439881424), (2510, 338487120), (2513, -3116855664), (2586, 902632320), (2589, -3116855664), (2621, -3116855664), (2632, 4879762848), (2654, 2439881424)]

theorem node304_check : node304 =
    Integer.Sparse.merge (Integer.Sparse.scale (4701210) entry_11_21) (Integer.Sparse.scale (16943621) entry_11_22) := by decide +kernel

theorem node304_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node304 x = (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x + ((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_22 x) := by
  rw [node304_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node305 : Integer.Sparse (Fin 2886) := [(1729, 1135280880), (1749, -1135280880), (2120, 338487120), (2148, -2101394304), (2151, -4879762848), (2183, -2439881424), (2214, 3568171824), (2217, 3116855664), (2226, 3116855664), (2249, 3116855664), (2284, -1353948480), (2290, -676974240), (2301, -676974240), (2332, 338487120), (2335, -3116855664), (2345, 2439881424), (2510, 338487120), (2513, -3116855664), (2586, 902632320), (2589, -3116855664), (2621, -3116855664), (2632, 4879762848), (2654, 2439881424)]

theorem node305_check : node305 =
    Integer.Sparse.merge (Integer.Sparse.scale (1576779) entry_11_20) node304 := by decide +kernel

theorem node305_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node305 x = (((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x + ((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_22 x)) := by
  rw [node305_check, Integer.Sparse.eval_merge]
  rw [node304_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node306 : Integer.Sparse (Fin 2886) := [(1133, -1795630320), (1656, 1795630320), (2111, 212255712), (2114, 318383568), (2206, -212255712), (2270, 212255712), (2281, -318383568), (2311, -212255712)]

theorem node306_check : node306 =
    Integer.Sparse.merge (Integer.Sparse.scale (-736999) entry_11_23) (Integer.Sparse.scale (2493931) entry_11_24) := by decide +kernel

theorem node306_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node306 x = (((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_23 x + ((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_24 x) := by
  rw [node306_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node307 : Integer.Sparse (Fin 2886) := [(1141, -250340976), (1144, 250340976), (1524, -1001363904), (1576, 1001363904), (1663, -250340976), (1693, 250340976), (2164, 65954304), (2237, 82442880), (2242, 197862912), (2296, -65954304), (2298, -197862912), (2777, 131908608), (2779, -197862912), (2859, 49465728), (2867, -65954304)]

theorem node307_check : node307 =
    Integer.Sparse.merge (Integer.Sparse.scale (458016) entry_11_25) (Integer.Sparse.scale (-1738479) entry_11_26) := by decide +kernel

theorem node307_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node307 x = (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_25 x + ((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_26 x) := by
  rw [node307_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node308 : Integer.Sparse (Fin 2886) := [(1133, -1795630320), (1141, -250340976), (1144, 250340976), (1524, -1001363904), (1576, 1001363904), (1656, 1795630320), (1663, -250340976), (1693, 250340976), (2111, 212255712), (2114, 318383568), (2164, 65954304), (2206, -212255712), (2237, 82442880), (2242, 197862912), (2270, 212255712), (2281, -318383568), (2296, -65954304), (2298, -197862912), (2311, -212255712), (2777, 131908608), (2779, -197862912), (2859, 49465728), (2867, -65954304)]

theorem node308_check : node308 =
    Integer.Sparse.merge node306 node307 := by decide +kernel

theorem node308_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node308 x = ((((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_23 x + ((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_24 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_25 x + ((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_26 x)) := by
  rw [node308_check, Integer.Sparse.eval_merge]
  rw [node306_eval, node307_eval]

def node309 : Integer.Sparse (Fin 2886) := [(1133, -1795630320), (1141, -250340976), (1144, 250340976), (1524, -1001363904), (1576, 1001363904), (1656, 1795630320), (1663, -250340976), (1693, 250340976), (1729, 1135280880), (1749, -1135280880), (2111, 212255712), (2114, 318383568), (2120, 338487120), (2148, -2101394304), (2151, -4879762848), (2164, 65954304), (2183, -2439881424), (2206, -212255712), (2214, 3568171824), (2217, 3116855664), (2226, 3116855664), (2237, 82442880), (2242, 197862912), (2249, 3116855664), (2270, 212255712), (2281, -318383568), (2284, -1353948480), (2290, -676974240), (2296, -65954304), (2298, -197862912), (2301, -676974240), (2311, -212255712), (2332, 338487120), (2335, -3116855664), (2345, 2439881424), (2510, 338487120), (2513, -3116855664), (2586, 902632320), (2589, -3116855664), (2621, -3116855664), (2632, 4879762848), (2654, 2439881424), (2777, 131908608), (2779, -197862912), (2859, 49465728), (2867, -65954304)]

theorem node309_check : node309 =
    Integer.Sparse.merge node305 node308 := by decide +kernel

theorem node309_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node309 x = ((((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x + ((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_22 x)) + ((((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_23 x + ((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_24 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_25 x + ((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_26 x))) := by
  rw [node309_check, Integer.Sparse.eval_merge]
  rw [node305_eval, node308_eval]

def node310 : Integer.Sparse (Fin 2886) := [(844, 264840768), (849, 397261152), (852, -282021120), (856, 282021120), (952, 397261152), (961, -1128084480), (1028, -397261152), (1036, 1128084480), (1047, -397261152), (1050, -282021120), (1083, -264840768), (1086, 282021120), (1133, -1795630320), (1141, -250340976), (1144, 250340976), (1524, -1001363904), (1576, 1001363904), (1656, 1795630320), (1663, -250340976), (1693, 250340976), (1729, 1135280880), (1749, -1135280880), (1799, -29895264), (1800, -119581056), (2053, 29895264), (2067, -29895264), (2090, 119581056), (2099, 29895264), (2103, 213103728), (2106, 852414912), (2111, 212255712), (2114, 318383568), (2119, 836897616), (2120, 338487120), (2134, 557931744), (2147, -836897616), (2148, -2101394304), (2151, -4879762848), (2163, -4301709120), (2164, 65954304), (2181, -557931744), (2183, -2439881424), (2198, -213103728), (2206, -212255712), (2214, 3568171824), (2217, 3116855664), (2224, 836897616), (2226, 3116855664), (2237, 82442880), (2240, 4301709120), (2242, 197862912), (2247, -836897616), (2249, 3116855664), (2270, 212255712), (2277, -639311184), (2281, -318383568), (2284, -1353948480), (2290, -676974240), (2296, -65954304), (2298, -197862912), (2301, -676974240), (2308, -213103728), (2311, -212255712), (2332, 338487120), (2335, -3116855664), (2342, -437936112), (2345, 2439881424), (2349, 437936112), (2510, 338487120), (2513, -3116855664), (2518, -875872224), (2521, -875872224), (2586, 902632320), (2589, -3116855664), (2594, 875872224), (2621, -3116855664), (2627, -875872224), (2632, 4879762848), (2636, 875872224), (2654, 2439881424), (2657, 875872224), (2678, -437936112), (2714, 437936112), (2777, 131908608), (2779, -197862912), (2859, 49465728), (2867, -65954304)]

theorem node310_check : node310 =
    Integer.Sparse.merge node303 node309 := by decide +kernel

theorem node310_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node310 x = (((((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x)) + ((((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + ((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x))) + ((((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x + ((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_22 x)) + ((((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_23 x + ((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_24 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_25 x + ((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_26 x)))) := by
  rw [node310_check, Integer.Sparse.eval_merge]
  rw [node303_eval, node309_eval]

def node311 : Integer.Sparse (Fin 2886) := [(841, -217779840), (844, 98298000), (849, -268909920), (852, -282021120), (856, 282021120), (952, 563803920), (961, -1128084480), (1028, -563803920), (1036, 1128084480), (1043, 217779840), (1047, 268909920), (1050, -282021120), (1083, -98298000), (1086, 282021120), (1113, -330983424), (1120, -358882848), (1124, 330983424), (1127, 358882848), (1133, -1795630320), (1141, -250340976), (1144, 250340976), (1360, -1323933696), (1363, -358882848), (1368, -1076648544), (1436, 358882848), (1464, -358882848), (1469, 1323933696), (1473, 1076648544), (1496, 358882848), (1524, -1001363904), (1576, 1001363904), (1580, -330983424), (1583, -358882848), (1618, 330983424), (1621, 358882848), (1656, 1795630320), (1663, -250340976), (1693, 250340976), (1729, 1135280880), (1749, -1135280880), (1799, -29895264), (1800, -119581056), (2053, 29895264), (2067, -29895264), (2090, 119581056), (2099, 29895264), (2102, 2219898240), (2103, 3465488016), (2104, 685213344), (2106, 5730991344), (2108, -35070624), (2111, 1022106528), (2114, -491467248), (2119, -125802864), (2120, 338487120), (2134, 1520632224), (2147, -4687699536), (2148, -2101394304), (2151, -4879762848), (2163, -4301709120), (2164, 65954304), (2181, -1520632224), (2183, -2439881424), (2198, 4665472704), (2199, 2090710656), (2206, 3027147552), (2214, 3568171824), (2217, 3116855664), (2224, 4687699536), (2226, 3116855664), (2237, 82442880), (2240, 4301709120), (2242, 197862912), (2247, 125802864), (2249, 3116855664), (2261, -2219898240), (2264, -2090710656), (2270, -3027147552), (2277, -10396464048), (2279, 35070624), (2281, 491467248), (2284, -1353948480), (2290, -676974240), (2296, -65954304), (2298, -197862912), (2301, -676974240), (2308, -3465488016), (2309, -685213344), (2311, -1022106528), (2332, 338487120), (2333, 1043644752), (2335, -3116855664), (2337, 520626096), (2342, -437936112), (2345, 2439881424), (2347, 812684592), (2349, 437936112), (2510, 338487120), (2511, 230960160), (2513, -3116855664), (2515, -1104743088), (2518, -875872224), (2521, -875872224), (2586, 902632320), (2587, 1566663408), (2589, -3116855664), (2594, 875872224), (2621, -3116855664), (2622, -1566663408), (2627, -875872224), (2632, 4879762848), (2634, 1104743088), (2636, 875872224), (2654, 2439881424), (2655, -230960160), (2657, 875872224), (2676, -812684592), (2678, -437936112), (2712, -520626096), (2714, 437936112), (2733, -1043644752), (2777, 131908608), (2779, -197862912), (2859, 49465728), (2867, -65954304)]

theorem node311_check : node311 =
    Integer.Sparse.merge node297 node310 := by decide +kernel

theorem node311_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node311 x = ((((((5623964 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x)) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x))) + ((((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x)) + ((((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x) + (((11293001 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x)))) + (((((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x)) + ((((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + ((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x))) + ((((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x + ((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_22 x)) + ((((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_23 x + ((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_24 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_25 x + ((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_26 x))))) := by
  rw [node311_check, Integer.Sparse.eval_merge]
  rw [node297_eval, node310_eval]

def node312 : Integer.Sparse (Fin 2886) := [(842, -147175920), (843, -6153984), (851, -24615936), (951, 6153984), (1030, -6153984), (1091, 147175920), (1093, 24615936), (1110, 6153984)]

theorem node312_check : node312 =
    Integer.Sparse.merge (Integer.Sparse.scale (204411) entry_12_1) (Integer.Sparse.scale (42736) entry_12_2) := by decide +kernel

theorem node312_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node312 x = (((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x) := by
  rw [node312_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node313 : Integer.Sparse (Fin 2886) := [(842, -147175920), (843, -6153984), (851, -24615936), (951, 6153984), (1030, -6153984), (1091, 147175920), (1093, 24615936), (1110, 6153984), (2111, 1199755440), (2116, -1199755440), (2202, 2399510880), (2206, 2399510880), (2208, 1199755440), (2211, -1199755440), (2267, 1199755440), (2269, 1199755440), (2273, -2399510880), (2278, -1199755440), (2280, -2399510880), (2310, -1199755440)]

theorem node313_check : node313 =
    Integer.Sparse.merge (Integer.Sparse.scale (8331635) entry_12_0) node312 := by decide +kernel

theorem node313_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node313 x = (((8331635 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + (((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x)) := by
  rw [node313_check, Integer.Sparse.eval_merge]
  rw [node312_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node314 : Integer.Sparse (Fin 2886) := [(2103, -567239904), (2109, -2268959616), (2148, 185646528), (2154, 371293056), (2185, 185646528), (2198, 567239904), (2214, -185646528), (2220, -185646528), (2228, -185646528), (2251, -185646528), (2316, 1701719712), (2328, 567239904), (2338, 185646528), (2352, -185646528), (2516, 185646528), (2592, 185646528), (2623, 185646528), (2662, -371293056), (2671, -185646528)]

theorem node314_check : node314 =
    Integer.Sparse.merge (Integer.Sparse.scale (3939166) entry_12_4) (Integer.Sparse.scale (-1289212) entry_12_5) := by decide +kernel

theorem node314_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node314 x = (((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x) := by
  rw [node314_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node315 : Integer.Sparse (Fin 2886) := [(2103, -567239904), (2109, -2268959616), (2122, -194773968), (2135, 194773968), (2148, 185646528), (2150, -779095872), (2154, 371293056), (2182, -194773968), (2185, 185646528), (2198, 567239904), (2214, -185646528), (2220, -185646528), (2225, 779095872), (2228, -185646528), (2248, 194773968), (2251, -185646528), (2316, 1701719712), (2328, 567239904), (2338, 185646528), (2352, -185646528), (2516, 185646528), (2592, 185646528), (2623, 185646528), (2662, -371293056), (2671, -185646528)]

theorem node315_check : node315 =
    Integer.Sparse.merge (Integer.Sparse.scale (1352597) entry_12_3) node314 := by decide +kernel

theorem node315_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node315 x = (((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + (((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x)) := by
  rw [node315_check, Integer.Sparse.eval_merge]
  rw [node314_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node316 : Integer.Sparse (Fin 2886) := [(842, -147175920), (843, -6153984), (851, -24615936), (951, 6153984), (1030, -6153984), (1091, 147175920), (1093, 24615936), (1110, 6153984), (2103, -567239904), (2109, -2268959616), (2111, 1199755440), (2116, -1199755440), (2122, -194773968), (2135, 194773968), (2148, 185646528), (2150, -779095872), (2154, 371293056), (2182, -194773968), (2185, 185646528), (2198, 567239904), (2202, 2399510880), (2206, 2399510880), (2208, 1199755440), (2211, -1199755440), (2214, -185646528), (2220, -185646528), (2225, 779095872), (2228, -185646528), (2248, 194773968), (2251, -185646528), (2267, 1199755440), (2269, 1199755440), (2273, -2399510880), (2278, -1199755440), (2280, -2399510880), (2310, -1199755440), (2316, 1701719712), (2328, 567239904), (2338, 185646528), (2352, -185646528), (2516, 185646528), (2592, 185646528), (2623, 185646528), (2662, -371293056), (2671, -185646528)]

theorem node316_check : node316 =
    Integer.Sparse.merge node313 node315 := by decide +kernel

theorem node316_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node316 x = ((((8331635 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + (((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x)) + (((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + (((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x))) := by
  rw [node316_check, Integer.Sparse.eval_merge]
  rw [node313_eval, node315_eval]

def node317 : Integer.Sparse (Fin 2886) := [(1121, -621784080), (1131, 621784080), (1362, -621784080), (1370, -1865352240), (1435, 621784080), (1466, -621784080), (1501, 1865352240), (1514, 621784080), (1698, -621784080), (1716, 621784080), (2120, 509876640), (2126, 1019753280), (2138, 509876640), (2148, -509876640), (2154, -1019753280), (2185, -509876640), (2352, 509876640), (2662, 1019753280), (2671, 509876640), (2750, -509876640), (2764, -1019753280), (2773, -509876640)]

theorem node317_check : node317 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3540810) entry_12_7) (Integer.Sparse.scale (4317945) entry_12_8) := by decide +kernel

theorem node317_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node317 x = (((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x + ((4317945 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x) := by
  rw [node317_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node318 : Integer.Sparse (Fin 2886) := [(1121, -621784080), (1131, 621784080), (1362, -621784080), (1370, -1865352240), (1435, 621784080), (1466, -621784080), (1501, 1865352240), (1514, 621784080), (1698, -621784080), (1716, 621784080), (2105, 274836240), (2120, 509876640), (2126, 1019753280), (2138, 509876640), (2148, -509876640), (2154, -1019753280), (2185, -509876640), (2262, -274836240), (2352, 509876640), (2662, 1019753280), (2671, 509876640), (2750, -509876640), (2764, -1019753280), (2773, -509876640)]

theorem node318_check : node318 =
    Integer.Sparse.merge (Integer.Sparse.scale (-381717) entry_12_6) node317 := by decide +kernel

theorem node318_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node318 x = (((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x + (((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x + ((4317945 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x)) := by
  rw [node318_check, Integer.Sparse.eval_merge]
  rw [node317_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node319 : Integer.Sparse (Fin 2886) := [(1114, -96481728), (1130, 96481728), (1361, -385926912), (1499, 385926912), (1697, -96481728), (1715, 96481728), (2120, 360855000), (2148, 360855000), (2214, 1202850000), (2220, 721710000), (2228, 721710000), (2251, 721710000), (2318, -1443420000), (2320, -721710000), (2325, -721710000), (2332, 360855000), (2338, -721710000), (2510, 360855000), (2516, -721710000), (2586, 962280000), (2592, -721710000), (2623, -721710000)]

theorem node319_check : node319 =
    Integer.Sparse.merge (Integer.Sparse.scale (5011875) entry_12_9) (Integer.Sparse.scale (670012) entry_12_10) := by decide +kernel

theorem node319_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node319 x = (((5011875 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x + ((670012 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x) := by
  rw [node319_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
