import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates022
import OAI.Combinatorics.Ramsey.CycleClique.Certificates023
import OAI.Combinatorics.Ramsey.CycleClique.Certificates024
import OAI.Combinatorics.Ramsey.CycleClique.Certificates025
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits
import OAI.Combinatorics.Ramsey.CycleClique.PatternReduction

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_13_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[],[3]],[[],[],[],[],[],[4]],[[],[],[],[],[],[5]],[[],[],[],[],[],[6]],[[],[],[],[],[1,1]],[[],[],[],[],[1,2]],[[],[],[],[],[1,3]],[[],[],[],[],[1,4]],[[],[],[],[],[1,5]],[[],[],[],[],[2,2]],[[],[],[],[],[2,3]],[[],[],[],[],[2,4]],[[],[],[],[],[3,3]]]

theorem patterns_13_7_0_verified : ∀ D ∈ patterns_13_7_0, PatternVerified 13 7 D := by

  simp only [patterns_13_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_677, certificate_677_valid⟩, ⟨⟨certificate_678, certificate_678_valid⟩, ⟨⟨certificate_679, certificate_679_valid⟩, ⟨⟨certificate_680, certificate_680_valid⟩, ⟨⟨certificate_681, certificate_681_valid⟩, ⟨⟨certificate_682, certificate_682_valid⟩, ⟨⟨certificate_683, certificate_683_valid⟩, ⟨⟨certificate_684, certificate_684_valid⟩, ⟨⟨certificate_685, certificate_685_valid⟩, ⟨⟨certificate_686, certificate_686_valid⟩, ⟨⟨certificate_687, certificate_687_valid⟩, ⟨⟨certificate_688, certificate_688_valid⟩, ⟨⟨certificate_689, certificate_689_valid⟩, ⟨⟨certificate_690, certificate_690_valid⟩, ⟨⟨certificate_691, certificate_691_valid⟩, ⟨⟨certificate_692, certificate_692_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_7_1 : List (List (List ℕ)) := [[[],[],[],[1],[1]],[[],[],[],[1],[2]],[[],[],[],[1],[3]],[[],[],[],[1],[4]],[[],[],[],[1],[5]],[[],[],[],[1,1,1]],[[],[],[],[1,1,2]],[[],[],[],[1,1,3]],[[],[],[],[1,1,4]],[[],[],[],[1,2,1]],[[],[],[],[1,2,2]],[[],[],[],[1,2,3]],[[],[],[],[1,3,1]],[[],[],[],[1,3,2]],[[],[],[],[1,4,1]],[[],[],[],[2],[2]]]

theorem patterns_13_7_1_verified : ∀ D ∈ patterns_13_7_1, PatternVerified 13 7 D := by

  simp only [patterns_13_7_1, List.forall_mem_cons]

  exact ⟨⟨certificate_693, certificate_693_valid⟩, ⟨⟨certificate_694, certificate_694_valid⟩, ⟨⟨certificate_695, certificate_695_valid⟩, ⟨⟨certificate_696, certificate_696_valid⟩, ⟨⟨certificate_697, certificate_697_valid⟩, ⟨⟨certificate_698, certificate_698_valid⟩, ⟨⟨certificate_699, certificate_699_valid⟩, ⟨⟨certificate_700, certificate_700_valid⟩, ⟨⟨certificate_701, certificate_701_valid⟩, ⟨⟨certificate_702, certificate_702_valid⟩, ⟨⟨certificate_703, certificate_703_valid⟩, ⟨⟨certificate_704, certificate_704_valid⟩, ⟨⟨certificate_705, certificate_705_valid⟩, ⟨⟨certificate_706, certificate_706_valid⟩, ⟨⟨certificate_707, certificate_707_valid⟩, ⟨⟨certificate_708, certificate_708_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_7_2 : List (List (List ℕ)) := [[[],[],[],[2],[3]],[[],[],[],[2],[4]],[[],[],[],[2,1,2]],[[],[],[],[2,1,3]],[[],[],[],[2,2,2]],[[],[],[],[3],[3]],[[],[],[1],[1,1]],[[],[],[1],[1,2]],[[],[],[1],[1,3]],[[],[],[1],[1,4]],[[],[],[1],[2,2]],[[],[],[1],[2,3]],[[],[],[1,1],[2]],[[],[],[1,1],[3]],[[],[],[1,1],[4]],[[],[],[1,1,1,1]]]

theorem patterns_13_7_2_verified : ∀ D ∈ patterns_13_7_2, PatternVerified 13 7 D := by

  simp only [patterns_13_7_2, List.forall_mem_cons]

  exact ⟨⟨certificate_709, certificate_709_valid⟩, ⟨⟨certificate_710, certificate_710_valid⟩, ⟨⟨certificate_711, certificate_711_valid⟩, ⟨⟨certificate_712, certificate_712_valid⟩, ⟨⟨certificate_713, certificate_713_valid⟩, ⟨⟨certificate_714, certificate_714_valid⟩, ⟨⟨certificate_715, certificate_715_valid⟩, ⟨⟨certificate_716, certificate_716_valid⟩, ⟨⟨certificate_717, certificate_717_valid⟩, ⟨⟨certificate_718, certificate_718_valid⟩, ⟨⟨certificate_719, certificate_719_valid⟩, ⟨⟨certificate_720, certificate_720_valid⟩, ⟨⟨certificate_721, certificate_721_valid⟩, ⟨⟨certificate_722, certificate_722_valid⟩, ⟨⟨certificate_723, certificate_723_valid⟩, ⟨⟨certificate_724, certificate_724_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_7_3 : List (List (List ℕ)) := [[[],[],[1,1,1,2]],[[],[],[1,1,1,3]],[[],[],[1,1,2,1]],[[],[],[1,1,2,2]],[[],[],[1,1,3,1]],[[],[],[1,2],[2]],[[],[],[1,2],[3]],[[],[],[1,2,1,2]],[[],[],[1,2,2,1]],[[],[],[1,3],[2]],[[],[],[2],[2,2]],[[],[],[2,1,1,2]],[[],[1],[1],[1]],[[],[1],[1],[2]],[[],[1],[1],[3]],[[],[1],[1],[4]]]

theorem patterns_13_7_3_verified : ∀ D ∈ patterns_13_7_3, PatternVerified 13 7 D := by

  simp only [patterns_13_7_3, List.forall_mem_cons]

  exact ⟨⟨certificate_725, certificate_725_valid⟩, ⟨⟨certificate_726, certificate_726_valid⟩, ⟨⟨certificate_727, certificate_727_valid⟩, ⟨⟨certificate_728, certificate_728_valid⟩, ⟨⟨certificate_729, certificate_729_valid⟩, ⟨⟨certificate_730, certificate_730_valid⟩, ⟨⟨certificate_731, certificate_731_valid⟩, ⟨⟨certificate_732, certificate_732_valid⟩, ⟨⟨certificate_733, certificate_733_valid⟩, ⟨⟨certificate_734, certificate_734_valid⟩, ⟨⟨certificate_735, certificate_735_valid⟩, ⟨⟨certificate_736, certificate_736_valid⟩, ⟨⟨certificate_737, certificate_737_valid⟩, ⟨⟨certificate_738, certificate_738_valid⟩, ⟨⟨certificate_739, certificate_739_valid⟩, ⟨⟨certificate_740, certificate_740_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_7_4 : List (List (List ℕ)) := [[[],[1],[1,1,1]],[[],[1],[1,1,2]],[[],[1],[1,1,3]],[[],[1],[1,2,1]],[[],[1],[1,2,2]],[[],[1],[1,3,1]],[[],[1],[2],[2]],[[],[1],[2],[3]],[[],[1],[2,1,2]],[[],[1,1],[1,1]],[[],[1,1],[1,2]],[[],[1,1],[1,3]],[[],[1,1],[2,2]],[[],[1,1,1],[2]],[[],[1,1,1],[3]],[[],[1,1,1,1,1]]]

theorem patterns_13_7_4_verified : ∀ D ∈ patterns_13_7_4, PatternVerified 13 7 D := by

  simp only [patterns_13_7_4, List.forall_mem_cons]

  exact ⟨⟨certificate_741, certificate_741_valid⟩, ⟨⟨certificate_742, certificate_742_valid⟩, ⟨⟨certificate_743, certificate_743_valid⟩, ⟨⟨certificate_744, certificate_744_valid⟩, ⟨⟨certificate_745, certificate_745_valid⟩, ⟨⟨certificate_746, certificate_746_valid⟩, ⟨⟨certificate_747, certificate_747_valid⟩, ⟨⟨certificate_748, certificate_748_valid⟩, ⟨⟨certificate_749, certificate_749_valid⟩, ⟨⟨certificate_750, certificate_750_valid⟩, ⟨⟨certificate_751, certificate_751_valid⟩, ⟨⟨certificate_752, certificate_752_valid⟩, ⟨⟨certificate_753, certificate_753_valid⟩, ⟨⟨certificate_754, certificate_754_valid⟩, ⟨⟨certificate_755, certificate_755_valid⟩, ⟨⟨certificate_756, certificate_756_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_7_5 : List (List (List ℕ)) := [[[],[1,1,1,1,2]],[[],[1,1,1,2,1]],[[],[1,1,2],[2]],[[],[1,1,2,1,1]],[[],[1,2],[1,2]],[[],[1,2,1],[2]],[[],[2],[2],[2]],[[1],[1],[1,1]],[[1],[1],[1,2]],[[1],[1],[1,3]],[[1],[1],[2,2]],[[1],[1,1],[2]],[[1],[1,1],[3]],[[1],[1,1,1,1]],[[1],[1,1,1,2]],[[1],[1,1,2,1]]]

theorem patterns_13_7_5_verified : ∀ D ∈ patterns_13_7_5, PatternVerified 13 7 D := by

  simp only [patterns_13_7_5, List.forall_mem_cons]

  exact ⟨⟨certificate_757, certificate_757_valid⟩, ⟨⟨certificate_758, certificate_758_valid⟩, ⟨⟨certificate_759, certificate_759_valid⟩, ⟨⟨certificate_760, certificate_760_valid⟩, ⟨⟨certificate_761, certificate_761_valid⟩, ⟨⟨certificate_762, certificate_762_valid⟩, ⟨⟨certificate_763, certificate_763_valid⟩, ⟨⟨certificate_764, certificate_764_valid⟩, ⟨⟨certificate_765, certificate_765_valid⟩, ⟨⟨certificate_766, certificate_766_valid⟩, ⟨⟨certificate_767, certificate_767_valid⟩, ⟨⟨certificate_768, certificate_768_valid⟩, ⟨⟨certificate_769, certificate_769_valid⟩, ⟨⟨certificate_770, certificate_770_valid⟩, ⟨⟨certificate_771, certificate_771_valid⟩, ⟨⟨certificate_772, certificate_772_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_7_6 : List (List (List ℕ)) := [[[1],[1,2],[2]],[[1,1],[1,1,1]],[[1,1],[1,1,2]],[[1,1],[1,2,1]],[[1,1],[2],[2]],[[1,1,1],[1,2]],[[1,1,1,1],[2]],[[1,1,1,1,1,1]]]

theorem patterns_13_7_6_verified : ∀ D ∈ patterns_13_7_6, PatternVerified 13 7 D := by

  simp only [patterns_13_7_6, List.forall_mem_cons]

  exact ⟨⟨certificate_773, certificate_773_valid⟩, ⟨⟨certificate_774, certificate_774_valid⟩, ⟨⟨certificate_775, certificate_775_valid⟩, ⟨⟨certificate_776, certificate_776_valid⟩, ⟨⟨certificate_777, certificate_777_valid⟩, ⟨⟨certificate_778, certificate_778_valid⟩, ⟨⟨certificate_779, certificate_779_valid⟩, ⟨⟨certificate_780, certificate_780_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_7 : List (List (List ℕ)) := patterns_13_7_0 ++ (patterns_13_7_1 ++ (patterns_13_7_2 ++ (patterns_13_7_3 ++ (patterns_13_7_4 ++ (patterns_13_7_5 ++ (patterns_13_7_6 ++ ([])))))))

theorem patterns_13_7_verified : ∀ D ∈ patterns_13_7, PatternVerified 13 7 D := by

  simp only [patterns_13_7, List.forall_mem_append]

  exact ⟨patterns_13_7_0_verified, ⟨patterns_13_7_1_verified, ⟨patterns_13_7_2_verified, ⟨patterns_13_7_3_verified, ⟨patterns_13_7_4_verified, ⟨patterns_13_7_5_verified, ⟨patterns_13_7_6_verified, by simp⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_7_coverage : patternChoices 7 6 [] = patterns_13_7 := by decide +kernel

theorem finite_patterns_13_7 : ∀ D ∈ patternChoices 7 (13-7) [], PatternVerified 13 7 D := by

  rw [patterns_13_7_coverage]

  exact patterns_13_7_verified

end CycleClique

end OAI
