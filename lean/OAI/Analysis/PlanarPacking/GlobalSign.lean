import OAI.Analysis.PlanarPacking.HalfSign0
import OAI.Analysis.PlanarPacking.HalfSign1
import OAI.Analysis.PlanarPacking.HalfSign3
import OAI.Analysis.PlanarPacking.HalfSign4
import OAI.Analysis.PlanarPacking.HalfSign7
import OAI.Analysis.PlanarPacking.HalfSign9
import OAI.Analysis.PlanarPacking.HalfSign12
import OAI.Analysis.PlanarPacking.HalfSign13
import OAI.Analysis.PlanarPacking.HalfSign15
import OAI.Analysis.PlanarPacking.HalfSign16
import OAI.Analysis.PlanarPacking.HalfSign19
import OAI.Analysis.PlanarPacking.HalfSign21
import OAI.Analysis.PlanarPacking.HalfSign24
import OAI.Analysis.PlanarPacking.HalfSign25
import OAI.Analysis.PlanarPacking.HalfSign27
import OAI.Analysis.PlanarPacking.HalfSign28
import OAI.Analysis.PlanarPacking.HalfSign31
import OAI.Analysis.PlanarPacking.HalfSign33
import OAI.Analysis.PlanarPacking.HalfSign36
import OAI.Analysis.PlanarPacking.HalfSign37
import OAI.Analysis.PlanarPacking.HalfSign39
import OAI.Analysis.PlanarPacking.HalfSign40
import OAI.Analysis.PlanarPacking.TailSign

namespace OAI

namespace SharpPlanar
lemma finite_sign_false {s : ℝ} (hs : s ∈ Set.Icc 1 (83/2)) :
    0 ≤ (if false then (1:ℝ) else -1)*exactJet false 0 s := by
  by_cases h0 : s ≤ 2
  · exact halfSign_1_N0_right ⟨hs.1,h0⟩
  by_cases h1 : s ≤ 3
  · exact halfSign_3_N0_left ⟨le_of_lt (lt_of_not_ge h0),h1⟩
  by_cases h2 : s ≤ (7/2)
  · exact halfSign_3_N0_right ⟨le_of_lt (lt_of_not_ge h1),h2⟩
  by_cases h3 : s ≤ 4
  · exact halfSign_4_N0_left ⟨le_of_lt (lt_of_not_ge h2),h3⟩
  by_cases h4 : s ≤ (11/2)
  · exact halfSign_4_N0_right ⟨le_of_lt (lt_of_not_ge h3),h4⟩
  by_cases h5 : s ≤ 7
  · exact halfSign_7_N0_left ⟨le_of_lt (lt_of_not_ge h4),h5⟩
  by_cases h6 : s ≤ 8
  · exact halfSign_7_N0_right ⟨le_of_lt (lt_of_not_ge h5),h6⟩
  by_cases h7 : s ≤ 9
  · exact halfSign_9_N0_left ⟨le_of_lt (lt_of_not_ge h6),h7⟩
  by_cases h8 : s ≤ (21/2)
  · exact halfSign_9_N0_right ⟨le_of_lt (lt_of_not_ge h7),h8⟩
  by_cases h9 : s ≤ 12
  · exact halfSign_12_N0_left ⟨le_of_lt (lt_of_not_ge h8),h9⟩
  by_cases h10 : s ≤ (25/2)
  · exact halfSign_12_N0_right ⟨le_of_lt (lt_of_not_ge h9),h10⟩
  by_cases h11 : s ≤ 13
  · exact halfSign_13_N0_left ⟨le_of_lt (lt_of_not_ge h10),h11⟩
  by_cases h12 : s ≤ 14
  · exact halfSign_13_N0_right ⟨le_of_lt (lt_of_not_ge h11),h12⟩
  by_cases h13 : s ≤ 15
  · exact halfSign_15_N0_left ⟨le_of_lt (lt_of_not_ge h12),h13⟩
  by_cases h14 : s ≤ (31/2)
  · exact halfSign_15_N0_right ⟨le_of_lt (lt_of_not_ge h13),h14⟩
  by_cases h15 : s ≤ 16
  · exact halfSign_16_N0_left ⟨le_of_lt (lt_of_not_ge h14),h15⟩
  by_cases h16 : s ≤ (35/2)
  · exact halfSign_16_N0_right ⟨le_of_lt (lt_of_not_ge h15),h16⟩
  by_cases h17 : s ≤ 19
  · exact halfSign_19_N0_left ⟨le_of_lt (lt_of_not_ge h16),h17⟩
  by_cases h18 : s ≤ 20
  · exact halfSign_19_N0_right ⟨le_of_lt (lt_of_not_ge h17),h18⟩
  by_cases h19 : s ≤ 21
  · exact halfSign_21_N0_left ⟨le_of_lt (lt_of_not_ge h18),h19⟩
  by_cases h20 : s ≤ (45/2)
  · exact halfSign_21_N0_right ⟨le_of_lt (lt_of_not_ge h19),h20⟩
  by_cases h21 : s ≤ 24
  · exact halfSign_24_N0_left ⟨le_of_lt (lt_of_not_ge h20),h21⟩
  by_cases h22 : s ≤ (49/2)
  · exact halfSign_24_N0_right ⟨le_of_lt (lt_of_not_ge h21),h22⟩
  by_cases h23 : s ≤ 25
  · exact halfSign_25_N0_left ⟨le_of_lt (lt_of_not_ge h22),h23⟩
  by_cases h24 : s ≤ 26
  · exact halfSign_25_N0_right ⟨le_of_lt (lt_of_not_ge h23),h24⟩
  by_cases h25 : s ≤ 27
  · exact halfSign_27_N0_left ⟨le_of_lt (lt_of_not_ge h24),h25⟩
  by_cases h26 : s ≤ (55/2)
  · exact halfSign_27_N0_right ⟨le_of_lt (lt_of_not_ge h25),h26⟩
  by_cases h27 : s ≤ 28
  · exact halfSign_28_N0_left ⟨le_of_lt (lt_of_not_ge h26),h27⟩
  by_cases h28 : s ≤ (59/2)
  · exact halfSign_28_N0_right ⟨le_of_lt (lt_of_not_ge h27),h28⟩
  by_cases h29 : s ≤ 31
  · exact halfSign_31_N0_left ⟨le_of_lt (lt_of_not_ge h28),h29⟩
  by_cases h30 : s ≤ 32
  · exact halfSign_31_N0_right ⟨le_of_lt (lt_of_not_ge h29),h30⟩
  by_cases h31 : s ≤ 33
  · exact halfSign_33_N0_left ⟨le_of_lt (lt_of_not_ge h30),h31⟩
  by_cases h32 : s ≤ (69/2)
  · exact halfSign_33_N0_right ⟨le_of_lt (lt_of_not_ge h31),h32⟩
  by_cases h33 : s ≤ 36
  · exact halfSign_36_N0_left ⟨le_of_lt (lt_of_not_ge h32),h33⟩
  by_cases h34 : s ≤ (73/2)
  · exact halfSign_36_N0_right ⟨le_of_lt (lt_of_not_ge h33),h34⟩
  by_cases h35 : s ≤ 37
  · exact halfSign_37_N0_left ⟨le_of_lt (lt_of_not_ge h34),h35⟩
  by_cases h36 : s ≤ 38
  · exact halfSign_37_N0_right ⟨le_of_lt (lt_of_not_ge h35),h36⟩
  by_cases h37 : s ≤ 39
  · exact halfSign_39_N0_left ⟨le_of_lt (lt_of_not_ge h36),h37⟩
  by_cases h38 : s ≤ (79/2)
  · exact halfSign_39_N0_right ⟨le_of_lt (lt_of_not_ge h37),h38⟩
  by_cases h39 : s ≤ 40
  · exact halfSign_40_N0_left ⟨le_of_lt (lt_of_not_ge h38),h39⟩
  exact halfSign_40_N0_right ⟨le_of_lt (lt_of_not_ge h39),hs.2⟩
lemma global_sign_false {s : ℝ} (hs : (1:ℝ) ≤ s) :
    0 ≤ (if false then (1:ℝ) else -1)*exactJet false 0 s := by
  by_cases hh : s ≤ 83/2
  · exact finite_sign_false ⟨hs,hh⟩
  · exact exact_sign_tail false (le_of_lt (lt_of_not_ge hh))
lemma finite_sign_true {s : ℝ} (hs : s ∈ Set.Icc 0 (83/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  by_cases h0 : s ≤ (1/2)
  · exact halfSign_0_N1_right ⟨hs.1,h0⟩
  by_cases h1 : s ≤ 1
  · exact halfSign_1_N1_left ⟨le_of_lt (lt_of_not_ge h0),h1⟩
  by_cases h2 : s ≤ 2
  · exact halfSign_1_N1_right ⟨le_of_lt (lt_of_not_ge h1),h2⟩
  by_cases h3 : s ≤ 3
  · exact halfSign_3_N1_left ⟨le_of_lt (lt_of_not_ge h2),h3⟩
  by_cases h4 : s ≤ (7/2)
  · exact halfSign_3_N1_right ⟨le_of_lt (lt_of_not_ge h3),h4⟩
  by_cases h5 : s ≤ 4
  · exact halfSign_4_N1_left ⟨le_of_lt (lt_of_not_ge h4),h5⟩
  by_cases h6 : s ≤ (11/2)
  · exact halfSign_4_N1_right ⟨le_of_lt (lt_of_not_ge h5),h6⟩
  by_cases h7 : s ≤ 7
  · exact halfSign_7_N1_left ⟨le_of_lt (lt_of_not_ge h6),h7⟩
  by_cases h8 : s ≤ 8
  · exact halfSign_7_N1_right ⟨le_of_lt (lt_of_not_ge h7),h8⟩
  by_cases h9 : s ≤ 9
  · exact halfSign_9_N1_left ⟨le_of_lt (lt_of_not_ge h8),h9⟩
  by_cases h10 : s ≤ (21/2)
  · exact halfSign_9_N1_right ⟨le_of_lt (lt_of_not_ge h9),h10⟩
  by_cases h11 : s ≤ 12
  · exact halfSign_12_N1_left ⟨le_of_lt (lt_of_not_ge h10),h11⟩
  by_cases h12 : s ≤ (25/2)
  · exact halfSign_12_N1_right ⟨le_of_lt (lt_of_not_ge h11),h12⟩
  by_cases h13 : s ≤ 13
  · exact halfSign_13_N1_left ⟨le_of_lt (lt_of_not_ge h12),h13⟩
  by_cases h14 : s ≤ 14
  · exact halfSign_13_N1_right ⟨le_of_lt (lt_of_not_ge h13),h14⟩
  by_cases h15 : s ≤ 15
  · exact halfSign_15_N1_left ⟨le_of_lt (lt_of_not_ge h14),h15⟩
  by_cases h16 : s ≤ (31/2)
  · exact halfSign_15_N1_right ⟨le_of_lt (lt_of_not_ge h15),h16⟩
  by_cases h17 : s ≤ 16
  · exact halfSign_16_N1_left ⟨le_of_lt (lt_of_not_ge h16),h17⟩
  by_cases h18 : s ≤ (35/2)
  · exact halfSign_16_N1_right ⟨le_of_lt (lt_of_not_ge h17),h18⟩
  by_cases h19 : s ≤ 19
  · exact halfSign_19_N1_left ⟨le_of_lt (lt_of_not_ge h18),h19⟩
  by_cases h20 : s ≤ 20
  · exact halfSign_19_N1_right ⟨le_of_lt (lt_of_not_ge h19),h20⟩
  by_cases h21 : s ≤ 21
  · exact halfSign_21_N1_left ⟨le_of_lt (lt_of_not_ge h20),h21⟩
  by_cases h22 : s ≤ (45/2)
  · exact halfSign_21_N1_right ⟨le_of_lt (lt_of_not_ge h21),h22⟩
  by_cases h23 : s ≤ 24
  · exact halfSign_24_N1_left ⟨le_of_lt (lt_of_not_ge h22),h23⟩
  by_cases h24 : s ≤ (49/2)
  · exact halfSign_24_N1_right ⟨le_of_lt (lt_of_not_ge h23),h24⟩
  by_cases h25 : s ≤ 25
  · exact halfSign_25_N1_left ⟨le_of_lt (lt_of_not_ge h24),h25⟩
  by_cases h26 : s ≤ 26
  · exact halfSign_25_N1_right ⟨le_of_lt (lt_of_not_ge h25),h26⟩
  by_cases h27 : s ≤ 27
  · exact halfSign_27_N1_left ⟨le_of_lt (lt_of_not_ge h26),h27⟩
  by_cases h28 : s ≤ (55/2)
  · exact halfSign_27_N1_right ⟨le_of_lt (lt_of_not_ge h27),h28⟩
  by_cases h29 : s ≤ 28
  · exact halfSign_28_N1_left ⟨le_of_lt (lt_of_not_ge h28),h29⟩
  by_cases h30 : s ≤ (59/2)
  · exact halfSign_28_N1_right ⟨le_of_lt (lt_of_not_ge h29),h30⟩
  by_cases h31 : s ≤ 31
  · exact halfSign_31_N1_left ⟨le_of_lt (lt_of_not_ge h30),h31⟩
  by_cases h32 : s ≤ 32
  · exact halfSign_31_N1_right ⟨le_of_lt (lt_of_not_ge h31),h32⟩
  by_cases h33 : s ≤ 33
  · exact halfSign_33_N1_left ⟨le_of_lt (lt_of_not_ge h32),h33⟩
  by_cases h34 : s ≤ (69/2)
  · exact halfSign_33_N1_right ⟨le_of_lt (lt_of_not_ge h33),h34⟩
  by_cases h35 : s ≤ 36
  · exact halfSign_36_N1_left ⟨le_of_lt (lt_of_not_ge h34),h35⟩
  by_cases h36 : s ≤ (73/2)
  · exact halfSign_36_N1_right ⟨le_of_lt (lt_of_not_ge h35),h36⟩
  by_cases h37 : s ≤ 37
  · exact halfSign_37_N1_left ⟨le_of_lt (lt_of_not_ge h36),h37⟩
  by_cases h38 : s ≤ 38
  · exact halfSign_37_N1_right ⟨le_of_lt (lt_of_not_ge h37),h38⟩
  by_cases h39 : s ≤ 39
  · exact halfSign_39_N1_left ⟨le_of_lt (lt_of_not_ge h38),h39⟩
  by_cases h40 : s ≤ (79/2)
  · exact halfSign_39_N1_right ⟨le_of_lt (lt_of_not_ge h39),h40⟩
  by_cases h41 : s ≤ 40
  · exact halfSign_40_N1_left ⟨le_of_lt (lt_of_not_ge h40),h41⟩
  exact halfSign_40_N1_right ⟨le_of_lt (lt_of_not_ge h41),hs.2⟩
lemma global_sign_true {s : ℝ} (hs : (0:ℝ) ≤ s) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  by_cases hh : s ≤ 83/2
  · exact finite_sign_true ⟨hs,hh⟩
  · exact exact_sign_tail true (le_of_lt (lt_of_not_ge hh))
end SharpPlanar

end OAI
