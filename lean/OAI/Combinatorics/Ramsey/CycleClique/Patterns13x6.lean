import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates017
import OAI.Combinatorics.Ramsey.CycleClique.Certificates018
import OAI.Combinatorics.Ramsey.CycleClique.Certificates019
import OAI.Combinatorics.Ramsey.CycleClique.Certificates020
import OAI.Combinatorics.Ramsey.CycleClique.Certificates021
import OAI.Combinatorics.Ramsey.CycleClique.Certificates022
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

noncomputable def patterns_13_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]],[[],[],[],[],[2]],[[],[],[],[],[3]],[[],[],[],[],[4]],[[],[],[],[],[5]],[[],[],[],[],[6]],[[],[],[],[],[7]],[[],[],[],[1,1]],[[],[],[],[1,2]],[[],[],[],[1,3]],[[],[],[],[1,4]],[[],[],[],[1,5]],[[],[],[],[1,6]],[[],[],[],[2,2]],[[],[],[],[2,3]]]

theorem patterns_13_6_0_verified : ∀ D ∈ patterns_13_6_0, PatternVerified 13 6 D := by

  simp only [patterns_13_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_525, certificate_525_valid⟩, ⟨⟨certificate_526, certificate_526_valid⟩, ⟨⟨certificate_527, certificate_527_valid⟩, ⟨⟨certificate_528, certificate_528_valid⟩, ⟨⟨certificate_529, certificate_529_valid⟩, ⟨⟨certificate_530, certificate_530_valid⟩, ⟨⟨certificate_531, certificate_531_valid⟩, ⟨⟨certificate_532, certificate_532_valid⟩, ⟨⟨certificate_533, certificate_533_valid⟩, ⟨⟨certificate_534, certificate_534_valid⟩, ⟨⟨certificate_535, certificate_535_valid⟩, ⟨⟨certificate_536, certificate_536_valid⟩, ⟨⟨certificate_537, certificate_537_valid⟩, ⟨⟨certificate_538, certificate_538_valid⟩, ⟨⟨certificate_539, certificate_539_valid⟩, ⟨⟨certificate_540, certificate_540_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_6_1 : List (List (List ℕ)) := [[[],[],[],[2,4]],[[],[],[],[2,5]],[[],[],[],[3,3]],[[],[],[],[3,4]],[[],[],[1],[1]],[[],[],[1],[2]],[[],[],[1],[3]],[[],[],[1],[4]],[[],[],[1],[5]],[[],[],[1],[6]],[[],[],[1,1,1]],[[],[],[1,1,2]],[[],[],[1,1,3]],[[],[],[1,1,4]],[[],[],[1,1,5]],[[],[],[1,2,1]]]

theorem patterns_13_6_1_verified : ∀ D ∈ patterns_13_6_1, PatternVerified 13 6 D := by

  simp only [patterns_13_6_1, List.forall_mem_cons]

  exact ⟨⟨certificate_541, certificate_541_valid⟩, ⟨⟨certificate_542, certificate_542_valid⟩, ⟨⟨certificate_543, certificate_543_valid⟩, ⟨⟨certificate_544, certificate_544_valid⟩, ⟨⟨certificate_545, certificate_545_valid⟩, ⟨⟨certificate_546, certificate_546_valid⟩, ⟨⟨certificate_547, certificate_547_valid⟩, ⟨⟨certificate_548, certificate_548_valid⟩, ⟨⟨certificate_549, certificate_549_valid⟩, ⟨⟨certificate_550, certificate_550_valid⟩, ⟨⟨certificate_551, certificate_551_valid⟩, ⟨⟨certificate_552, certificate_552_valid⟩, ⟨⟨certificate_553, certificate_553_valid⟩, ⟨⟨certificate_554, certificate_554_valid⟩, ⟨⟨certificate_555, certificate_555_valid⟩, ⟨⟨certificate_556, certificate_556_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_6_2 : List (List (List ℕ)) := [[[],[],[1,2,2]],[[],[],[1,2,3]],[[],[],[1,2,4]],[[],[],[1,3,1]],[[],[],[1,3,2]],[[],[],[1,3,3]],[[],[],[1,4,1]],[[],[],[1,4,2]],[[],[],[1,5,1]],[[],[],[2],[2]],[[],[],[2],[3]],[[],[],[2],[4]],[[],[],[2],[5]],[[],[],[2,1,2]],[[],[],[2,1,3]],[[],[],[2,1,4]]]

theorem patterns_13_6_2_verified : ∀ D ∈ patterns_13_6_2, PatternVerified 13 6 D := by

  simp only [patterns_13_6_2, List.forall_mem_cons]

  exact ⟨⟨certificate_557, certificate_557_valid⟩, ⟨⟨certificate_558, certificate_558_valid⟩, ⟨⟨certificate_559, certificate_559_valid⟩, ⟨⟨certificate_560, certificate_560_valid⟩, ⟨⟨certificate_561, certificate_561_valid⟩, ⟨⟨certificate_562, certificate_562_valid⟩, ⟨⟨certificate_563, certificate_563_valid⟩, ⟨⟨certificate_564, certificate_564_valid⟩, ⟨⟨certificate_565, certificate_565_valid⟩, ⟨⟨certificate_566, certificate_566_valid⟩, ⟨⟨certificate_567, certificate_567_valid⟩, ⟨⟨certificate_568, certificate_568_valid⟩, ⟨⟨certificate_569, certificate_569_valid⟩, ⟨⟨certificate_570, certificate_570_valid⟩, ⟨⟨certificate_571, certificate_571_valid⟩, ⟨⟨certificate_572, certificate_572_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_6_3 : List (List (List ℕ)) := [[[],[],[2,2,2]],[[],[],[2,2,3]],[[],[],[2,3,2]],[[],[],[3],[3]],[[],[],[3],[4]],[[],[],[3,1,3]],[[],[1],[1,1]],[[],[1],[1,2]],[[],[1],[1,3]],[[],[1],[1,4]],[[],[1],[1,5]],[[],[1],[2,2]],[[],[1],[2,3]],[[],[1],[2,4]],[[],[1],[3,3]],[[],[1,1],[2]]]

theorem patterns_13_6_3_verified : ∀ D ∈ patterns_13_6_3, PatternVerified 13 6 D := by

  simp only [patterns_13_6_3, List.forall_mem_cons]

  exact ⟨⟨certificate_573, certificate_573_valid⟩, ⟨⟨certificate_574, certificate_574_valid⟩, ⟨⟨certificate_575, certificate_575_valid⟩, ⟨⟨certificate_576, certificate_576_valid⟩, ⟨⟨certificate_577, certificate_577_valid⟩, ⟨⟨certificate_578, certificate_578_valid⟩, ⟨⟨certificate_579, certificate_579_valid⟩, ⟨⟨certificate_580, certificate_580_valid⟩, ⟨⟨certificate_581, certificate_581_valid⟩, ⟨⟨certificate_582, certificate_582_valid⟩, ⟨⟨certificate_583, certificate_583_valid⟩, ⟨⟨certificate_584, certificate_584_valid⟩, ⟨⟨certificate_585, certificate_585_valid⟩, ⟨⟨certificate_586, certificate_586_valid⟩, ⟨⟨certificate_587, certificate_587_valid⟩, ⟨⟨certificate_588, certificate_588_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_6_4 : List (List (List ℕ)) := [[[],[1,1],[3]],[[],[1,1],[4]],[[],[1,1],[5]],[[],[1,1,1,1]],[[],[1,1,1,2]],[[],[1,1,1,3]],[[],[1,1,1,4]],[[],[1,1,2,1]],[[],[1,1,2,2]],[[],[1,1,2,3]],[[],[1,1,3,1]],[[],[1,1,3,2]],[[],[1,1,4,1]],[[],[1,2],[2]],[[],[1,2],[3]],[[],[1,2],[4]]]

theorem patterns_13_6_4_verified : ∀ D ∈ patterns_13_6_4, PatternVerified 13 6 D := by

  simp only [patterns_13_6_4, List.forall_mem_cons]

  exact ⟨⟨certificate_589, certificate_589_valid⟩, ⟨⟨certificate_590, certificate_590_valid⟩, ⟨⟨certificate_591, certificate_591_valid⟩, ⟨⟨certificate_592, certificate_592_valid⟩, ⟨⟨certificate_593, certificate_593_valid⟩, ⟨⟨certificate_594, certificate_594_valid⟩, ⟨⟨certificate_595, certificate_595_valid⟩, ⟨⟨certificate_596, certificate_596_valid⟩, ⟨⟨certificate_597, certificate_597_valid⟩, ⟨⟨certificate_598, certificate_598_valid⟩, ⟨⟨certificate_599, certificate_599_valid⟩, ⟨⟨certificate_600, certificate_600_valid⟩, ⟨⟨certificate_601, certificate_601_valid⟩, ⟨⟨certificate_602, certificate_602_valid⟩, ⟨⟨certificate_603, certificate_603_valid⟩, ⟨⟨certificate_604, certificate_604_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_6_5 : List (List (List ℕ)) := [[[],[1,2,1,2]],[[],[1,2,1,3]],[[],[1,2,2,1]],[[],[1,2,2,2]],[[],[1,2,3,1]],[[],[1,3],[2]],[[],[1,3],[3]],[[],[1,3,1,2]],[[],[1,4],[2]],[[],[2],[2,2]],[[],[2],[2,3]],[[],[2,1,1,2]],[[],[2,1,1,3]],[[],[2,1,2,2]],[[],[2,2],[3]],[[1],[1],[1]]]

theorem patterns_13_6_5_verified : ∀ D ∈ patterns_13_6_5, PatternVerified 13 6 D := by

  simp only [patterns_13_6_5, List.forall_mem_cons]

  exact ⟨⟨certificate_605, certificate_605_valid⟩, ⟨⟨certificate_606, certificate_606_valid⟩, ⟨⟨certificate_607, certificate_607_valid⟩, ⟨⟨certificate_608, certificate_608_valid⟩, ⟨⟨certificate_609, certificate_609_valid⟩, ⟨⟨certificate_610, certificate_610_valid⟩, ⟨⟨certificate_611, certificate_611_valid⟩, ⟨⟨certificate_612, certificate_612_valid⟩, ⟨⟨certificate_613, certificate_613_valid⟩, ⟨⟨certificate_614, certificate_614_valid⟩, ⟨⟨certificate_615, certificate_615_valid⟩, ⟨⟨certificate_616, certificate_616_valid⟩, ⟨⟨certificate_617, certificate_617_valid⟩, ⟨⟨certificate_618, certificate_618_valid⟩, ⟨⟨certificate_619, certificate_619_valid⟩, ⟨⟨certificate_620, certificate_620_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_6_6 : List (List (List ℕ)) := [[[1],[1],[2]],[[1],[1],[3]],[[1],[1],[4]],[[1],[1],[5]],[[1],[1,1,1]],[[1],[1,1,2]],[[1],[1,1,3]],[[1],[1,1,4]],[[1],[1,2,1]],[[1],[1,2,2]],[[1],[1,2,3]],[[1],[1,3,1]],[[1],[1,3,2]],[[1],[1,4,1]],[[1],[2],[2]],[[1],[2],[3]]]

theorem patterns_13_6_6_verified : ∀ D ∈ patterns_13_6_6, PatternVerified 13 6 D := by

  simp only [patterns_13_6_6, List.forall_mem_cons]

  exact ⟨⟨certificate_621, certificate_621_valid⟩, ⟨⟨certificate_622, certificate_622_valid⟩, ⟨⟨certificate_623, certificate_623_valid⟩, ⟨⟨certificate_624, certificate_624_valid⟩, ⟨⟨certificate_625, certificate_625_valid⟩, ⟨⟨certificate_626, certificate_626_valid⟩, ⟨⟨certificate_627, certificate_627_valid⟩, ⟨⟨certificate_628, certificate_628_valid⟩, ⟨⟨certificate_629, certificate_629_valid⟩, ⟨⟨certificate_630, certificate_630_valid⟩, ⟨⟨certificate_631, certificate_631_valid⟩, ⟨⟨certificate_632, certificate_632_valid⟩, ⟨⟨certificate_633, certificate_633_valid⟩, ⟨⟨certificate_634, certificate_634_valid⟩, ⟨⟨certificate_635, certificate_635_valid⟩, ⟨⟨certificate_636, certificate_636_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_6_7 : List (List (List ℕ)) := [[[1],[2],[4]],[[1],[2,1,2]],[[1],[2,1,3]],[[1],[2,2,2]],[[1],[3],[3]],[[1,1],[1,1]],[[1,1],[1,2]],[[1,1],[1,3]],[[1,1],[1,4]],[[1,1],[2,2]],[[1,1],[2,3]],[[1,1,1],[2]],[[1,1,1],[3]],[[1,1,1],[4]],[[1,1,1,1,1]],[[1,1,1,1,2]]]

theorem patterns_13_6_7_verified : ∀ D ∈ patterns_13_6_7, PatternVerified 13 6 D := by

  simp only [patterns_13_6_7, List.forall_mem_cons]

  exact ⟨⟨certificate_637, certificate_637_valid⟩, ⟨⟨certificate_638, certificate_638_valid⟩, ⟨⟨certificate_639, certificate_639_valid⟩, ⟨⟨certificate_640, certificate_640_valid⟩, ⟨⟨certificate_641, certificate_641_valid⟩, ⟨⟨certificate_642, certificate_642_valid⟩, ⟨⟨certificate_643, certificate_643_valid⟩, ⟨⟨certificate_644, certificate_644_valid⟩, ⟨⟨certificate_645, certificate_645_valid⟩, ⟨⟨certificate_646, certificate_646_valid⟩, ⟨⟨certificate_647, certificate_647_valid⟩, ⟨⟨certificate_648, certificate_648_valid⟩, ⟨⟨certificate_649, certificate_649_valid⟩, ⟨⟨certificate_650, certificate_650_valid⟩, ⟨⟨certificate_651, certificate_651_valid⟩, ⟨⟨certificate_652, certificate_652_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_6_8 : List (List (List ℕ)) := [[[1,1,1,1,3]],[[1,1,1,2,1]],[[1,1,1,2,2]],[[1,1,1,3,1]],[[1,1,2],[2]],[[1,1,2],[3]],[[1,1,2,1,1]],[[1,1,2,1,2]],[[1,1,2,2,1]],[[1,1,3],[2]],[[1,1,3,1,1]],[[1,2],[1,2]],[[1,2],[1,3]],[[1,2],[2,2]],[[1,2,1],[2]],[[1,2,1],[3]]]

theorem patterns_13_6_8_verified : ∀ D ∈ patterns_13_6_8, PatternVerified 13 6 D := by

  simp only [patterns_13_6_8, List.forall_mem_cons]

  exact ⟨⟨certificate_653, certificate_653_valid⟩, ⟨⟨certificate_654, certificate_654_valid⟩, ⟨⟨certificate_655, certificate_655_valid⟩, ⟨⟨certificate_656, certificate_656_valid⟩, ⟨⟨certificate_657, certificate_657_valid⟩, ⟨⟨certificate_658, certificate_658_valid⟩, ⟨⟨certificate_659, certificate_659_valid⟩, ⟨⟨certificate_660, certificate_660_valid⟩, ⟨⟨certificate_661, certificate_661_valid⟩, ⟨⟨certificate_662, certificate_662_valid⟩, ⟨⟨certificate_663, certificate_663_valid⟩, ⟨⟨certificate_664, certificate_664_valid⟩, ⟨⟨certificate_665, certificate_665_valid⟩, ⟨⟨certificate_666, certificate_666_valid⟩, ⟨⟨certificate_667, certificate_667_valid⟩, ⟨⟨certificate_668, certificate_668_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_6_9 : List (List (List ℕ)) := [[[1,2,1,1,2]],[[1,2,1,2,1]],[[1,2,2],[2]],[[1,3,1],[2]],[[2],[2],[2]],[[2],[2],[3]],[[2],[2,1,2]],[[2,1,1,1,2]]]

theorem patterns_13_6_9_verified : ∀ D ∈ patterns_13_6_9, PatternVerified 13 6 D := by

  simp only [patterns_13_6_9, List.forall_mem_cons]

  exact ⟨⟨certificate_669, certificate_669_valid⟩, ⟨⟨certificate_670, certificate_670_valid⟩, ⟨⟨certificate_671, certificate_671_valid⟩, ⟨⟨certificate_672, certificate_672_valid⟩, ⟨⟨certificate_673, certificate_673_valid⟩, ⟨⟨certificate_674, certificate_674_valid⟩, ⟨⟨certificate_675, certificate_675_valid⟩, ⟨⟨certificate_676, certificate_676_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_6 : List (List (List ℕ)) := patterns_13_6_0 ++ (patterns_13_6_1 ++ (patterns_13_6_2 ++ (patterns_13_6_3 ++ (patterns_13_6_4 ++ (patterns_13_6_5 ++ (patterns_13_6_6 ++ (patterns_13_6_7 ++ (patterns_13_6_8 ++ (patterns_13_6_9 ++ ([]))))))))))

theorem patterns_13_6_verified : ∀ D ∈ patterns_13_6, PatternVerified 13 6 D := by

  simp only [patterns_13_6, List.forall_mem_append]

  exact ⟨patterns_13_6_0_verified, ⟨patterns_13_6_1_verified, ⟨patterns_13_6_2_verified, ⟨patterns_13_6_3_verified, ⟨patterns_13_6_4_verified, ⟨patterns_13_6_5_verified, ⟨patterns_13_6_6_verified, ⟨patterns_13_6_7_verified, ⟨patterns_13_6_8_verified, ⟨patterns_13_6_9_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_6_coverage : patternChoices 6 7 [] = patterns_13_6 := by decide +kernel

theorem finite_patterns_13_6 : ∀ D ∈ patternChoices 6 (13-6) [], PatternVerified 13 6 D := by

  rw [patterns_13_6_coverage]

  exact patterns_13_6_verified

end CycleClique

end OAI
