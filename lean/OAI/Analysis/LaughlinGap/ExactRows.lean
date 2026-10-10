import Mathlib
import OAI.Analysis.LaughlinGap.GlobalBoundCore
import OAI.Analysis.LaughlinGap.RationalRowComputable

namespace OAI

/-! Exact Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def rowLambdaInteger : Fin 8 → ℤ := ![6971289, 4543418, 2122516, 3473755, 1187195, 1558861, -522862, 1523334]

def rowAlphaInteger : Fin 8 → Fin 8 → Fin 9 → ℤ := ![
  ![![0, 0, 2967, -8940, 597844, -3700599, -1482135, -1339330, -1774974], ![0, -1484, 0, -400546, -727512, 452505, 336757, -687973, 0], ![742, 2235, 200273, -333763, -26754, 152623, 53954, 0, 0], ![-2235, -74731, 515641, -77419, 104592, -28049, 0, 0, 0], ![11959, 64406, 79631, -160154, 59858, 0, 0, 0, 0], ![-689922, -67178, 66061, -77891, 0, 0, 0, 0, 0], ![59862, -44385, 84784, 0, 0, 0, 0, 0, 0], ![153877, -34627, 0, 0, 0, 0, 0, 0, 0]],
  ![![0, 0, -25023, -53790, 766486, 9140658, 6404627, 13809118, 23999206], ![0, 12512, 0, -81797, -655373, -2080938, -2714428, 2099732, -5178959], ![-6256, 13448, 40899, 710335, 786050, -693550, 623937, -1143911, 0], ![-13448, -95811, -546491, -138110, 34419, -267131, -144692, 0, 0], ![123267, -216124, -122255, 80152, -24553, 132133, 0, 0, 0], ![937778, 118499, 304496, 31238, 59346, 0, 0, 0, 0], ![1417, -356711, 56605, -65505, 0, 0, 0, 0, 0], ![-131919, -496957, 74692, 0, 0, 0, 0, 0, 0]],
  ![![0, 0, 40292, 23298, -1528688, 1746358, -12625070, -2802951, -6221618], ![0, -20146, 0, 520862, 3752616, 3182905, 4997631, 2764684, 861720], ![10073, -5824, -260431, -498930, 791582, 797383, 224990, -770365, 257970], ![5824, 191086, -439224, -64123, 275842, 867800, 34013, 364701, 0], ![-156414, -358613, -895366, -226478, -106557, 44603, 621822, 0, 0], ![1390987, 809119, -671849, -312442, 38220, 292352, 0, 0, 0], ![-51065, 534431, -193959, -39966, 151939, 0, 0, 0, 0], ![996138, 485619, -35844, 2051, 0, 0, 0, 0, 0]],
  ![![0, 0, 0, 260793, 1619513, -9479213, -9905866, -2635931, -19784496], ![0, 0, 0, -921422, -5959267, -3855561, -5424538, -3111939, 8971929], ![0, -65198, 460711, 981829, 1266048, 467412, 2221895, 5826028, -4062050], ![65198, -202439, 507988, -1218507, -969129, -1457246, 510645, -2757862, -105174], ![73303, 1083365, 1360170, 496901, 546989, 591478, -1611153, 541242, 0], ![-3047173, -422296, 565219, 51950, -138923, -157439, 384768, 0, 0], ![-1096705, -516126, -272886, -590124, 310843, 424224, 0, 0, 0], ![-907772, 513824, -898660, 386231, 250109, 0, 0, 0, 0]],
  ![![0, 0, 0, 0, 105594, -4061461, 6356394, 10585121, -6662244], ![0, 0, 0, 110095, -1847081, -3073897, -2667170, -8745701, 5964734], ![0, 0, -55047, -433408, -2935870, -4255122, -2157050, -4954706, -4844675], ![0, -13199, 895178, 1245604, -560549, -1093209, -872791, 718839, 1986698], ![47323, 37137, 717733, 1000936, -51292, -45155, -380146, 602091, 78888], ![-1084895, -476551, 1133209, 876644, -325993, -113185, 946782, -228390, 0], ![-1146443, -1427889, 250513, 803576, -775332, 795845, 94822, 0, 0], ![-1103184, -439205, 578684, -576406, 521912, 2369, 0, 0, 0]],
  ![![0, 0, 0, 0, 0, 1307234, 1613443, -12951363, 31680953], ![0, 0, 0, 0, 281037, 661119, -2279616, 5048517, -23313511], ![0, 0, 0, 58302, -216885, -757322, -7019672, -5556231, -4399124], ![0, 0, -128561, -217031, 206708, -4699975, -3183010, -1044281, 2334083], ![0, -52551, 405571, 290575, 700566, -1549534, 387879, 5277042, -3807459], ![251228, -457263, -370075, 2178628, 928006, -250704, 3565738, -1838288, -1006797], ![447635, 843581, 712865, 1465846, 157586, 2126100, -1099955, 74867, 0], ![-1885572, -2909636, 386414, 199797, 509416, -417784, -153850, 0, 0]],
  ![![0, 0, 0, 0, 0, 0, 962082, -4231547, 6336802], ![0, 0, 0, 0, 0, 554480, 519996, -3314368, -8609585], ![0, 0, 0, 0, 8439, 936902, -1855598, -3611338, -2870966], ![0, 0, 0, -22438, 326366, -903827, -684137, -5872845, 530800], ![0, 0, -41983, -291963, 67578, 107968, -4215760, 473171, -2108792], ![0, -52838, -406574, 473590, 277799, -2954710, 85152, -1038229, 12413], ![245134, 588941, 460312, 152807, -910473, 428359, -647302, 35163, -1436712], ![-2025, -885233, -317059, -405381, -399637, -622199, -249650, -812670, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 4582620, -21402093], ![0, 0, 0, 0, 0, 0, 2744534, -4053241, 2091862], ![0, 0, 0, 0, 0, 1254615, 119326, -1351192, 846998], ![0, 0, 0, 0, 251416, 819674, -831726, 1116146, -3026818], ![0, 0, 0, -366503, -138643, -262993, -69789, -2014575, 2467955], ![0, 0, -442958, -386858, 237177, 21361, -945799, 490916, 623063], ![0, 312317, 378534, 414641, -381651, -1214503, 525474, 331451, -671780], ![1126574, 51881, -475448, -1232794, -905053, 27808, -429230, -574069, -776706]]
 ]

def exactRows (a : Fin 8) : RationalRow where
  t := a
  lam := (rowLambdaInteger a : ℚ)/10000000
  alpha p j := (rowAlphaInteger a p j : ℚ)/10000000

def etaRational : ℚ := ∑ a : Fin 8, (exactRows a).lam^2

lemma etaRational_value : etaRational = (11530872018309/12500000000000:ℚ) := by decide +kernel

lemma small_margin : (1/25:ℚ) < 1-etaRational-61/4096-1222*(1/200000) := by
  rw [etaRational_value]
  norm_num

lemma test_sum : (exactRows 0).threeSumFast 2 0 = (0:ℚ) := by decide +kernel
lemma test_trace : (∑ i : Fin 9, threeRowFactor 0 2 i.val * (exactRows 0).threeSumFast 2 i *
  ((exactRows 0).threeSumFast 2 i + 2*(exactRows 0).lam*uCoefficient 2 2 (0+i.val) 0)) = (3805540785952177/16402500000000000:ℚ) := by decide +kernel

end LaughlinGap.RealOccupation

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def traceRational (z : ℕ) : ℚ :=
  ∑ a : Fin 8, ∑ i : Fin 9, threeRowFactor a.val z i.val *
    (exactRows a).threeSumFast z i *
      ((exactRows a).threeSumFast z i + 2*(exactRows a).lam*uCoefficient 2 z (a.val+i.val) a.val)

lemma traceRational_eq (z : ℕ) :
    (traceRational z : ℝ) = ∑ a : Fin 8, rowTrace threeWeightCoefficientStar z (exactRows a).toReal := by
  simp only [RationalRow.threeTrace_eq,RationalRow.threeTrace,RationalRow.threeSum_eq_fast,
    traceRational, exactRows, Rat.cast_sum,Rat.cast_mul,Rat.cast_add,Rat.cast_ofNat]

lemma trace_bound_2 : traceRational 2 < (3/2:ℚ)*(3*2-1)*(-1/2:ℚ)^2 := by decide +kernel
lemma trace_bound_4 : traceRational 4 < (3/2:ℚ)*(3*4-1)*(-1/2:ℚ)^4 := by decide +kernel
lemma trace_bound_5 : traceRational 5 < (3/2:ℚ)*(3*5-1)*(-1/2:ℚ)^5 := by decide +kernel
lemma trace_bound_6 : traceRational 6 < (3/2:ℚ)*(3*6-1)*(-1/2:ℚ)^6 := by decide +kernel
lemma trace_bound_7 : traceRational 7 < (3/2:ℚ)*(3*7-1)*(-1/2:ℚ)^7 := by decide +kernel
lemma trace_bound_8 : traceRational 8 < (3/2:ℚ)*(3*8-1)*(-1/2:ℚ)^8 := by decide +kernel
lemma trace_bound_9 : traceRational 9 < (3/2:ℚ)*(3*9-1)*(-1/2:ℚ)^9 := by decide +kernel
lemma trace_bound_10 : traceRational 10 < (3/2:ℚ)*(3*10-1)*(-1/2:ℚ)^10 := by decide +kernel
lemma trace_bound_11 : traceRational 11 < (3/2:ℚ)*(3*11-1)*(-1/2:ℚ)^11 := by decide +kernel
lemma trace_bound_12 : traceRational 12 < (3/2:ℚ)*(3*12-1)*(-1/2:ℚ)^12 := by decide +kernel
lemma trace_bound_13 : traceRational 13 < (3/2:ℚ)*(3*13-1)*(-1/2:ℚ)^13 := by decide +kernel
lemma trace_bound_14 : traceRational 14 < (3/2:ℚ)*(3*14-1)*(-1/2:ℚ)^14 := by decide +kernel
lemma trace_bound_15 : traceRational 15 < (3/2:ℚ)*(3*15-1)*(-1/2:ℚ)^15 := by decide +kernel

lemma exact_three (z : Fin 16) (h0 : z.val ≠ 0) (h1 : z.val ≠ 1) (h3 : z.val ≠ 3) :
    (∑ a : Fin 8, rowTrace threeWeightCoefficientStar z.val (exactRows a).toReal) <
      (3/2:ℝ)*((3*(z.val:ℝ)-1)*(-1/2:ℝ)^z.val) := by
  rw [← traceRational_eq]
  have h : traceRational z.val < (3/2:ℚ)*(3*(z.val:ℚ)-1)*(-1/2:ℚ)^z.val := by
    fin_cases z
    · exact False.elim (h0 rfl)
    · exact False.elim (h1 rfl)
    · exact trace_bound_2
    · exact False.elim (h3 rfl)
    · exact trace_bound_4
    · exact trace_bound_5
    · exact trace_bound_6
    · exact trace_bound_7
    · exact trace_bound_8
    · exact trace_bound_9
    · exact trace_bound_10
    · exact trace_bound_11
    · exact trace_bound_12
    · exact trace_bound_13
    · exact trace_bound_14
    · exact trace_bound_15
  have hh := (Rat.cast_lt (K := ℝ)).mpr h
  push_cast at hh
  nlinarith only [hh]

lemma exact_margin : (1/25:ℝ) <
    1-rowEta (fun a : Fin 8 => (exactRows a).toReal) -61/4096-1222*(1/200000) := by
  have he : rowEta (fun a : Fin 8 => (exactRows a).toReal) = (etaRational:ℝ) := by
    simp [rowEta,etaRational,RationalRow.toReal]
  rw [he]
  have h := (Rat.cast_lt (K := ℝ)).mpr small_margin
  push_cast at h
  exact h

end LaughlinGap.RealOccupation

end

end OAI
