import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_0_q : Finset ℕ := ([0,1,2] : List ℕ).toFinset
noncomputable def certificate_0_edges : List (ℕ × ℕ) := [(0,1),(0,2),(1,2)]

noncomputable def certificate_0 : FiniteCertificate := .forbid 0 1 1 (.system [[0,3,1],[2]]) (.forbid 0 1 2 (.system [[0,3,4,1],[2]]) (.forbid 0 1 3 (.system [[0,3,4,5,1],[2]]) (.forbid 0 1 4 (.system [[0,3,4,5,6,1],[2]]) (.packing {.ball 0 (.succ (.zero ∅ 3 2) ∅ 8 3), .ball 1 (.succ (.zero ∅ 3 2) ∅ 8 3)}))))

theorem certificate_0_checked : certificate_0.Valid 5 3 3 certificate_0_q certificate_0_edges 0 0 [] := by decide +kernel
theorem certificate_0_valid : certificate_0.Valid 5 3 (patternOrder [[],[],[]]) (patternClique [[],[],[]]) (patternEdges [[],[],[]]) (patternAmount [[],[],[]]) (patternEdgeCount [[],[],[]]) [] := certificate_0_checked

noncomputable def certificate_1_q : Finset ℕ := ([0,1,3] : List ℕ).toFinset

noncomputable def certificate_1_edges : List (ℕ × ℕ) := [(1,2),(2,3),(0,1),(0,3),(1,3)]

noncomputable def certificate_1_E : List (ℕ × ℕ) := certificate_1_edges

noncomputable def certificate_1_M : ForbiddenMatrix := []

noncomputable def certificate_1_part_1_E : List (ℕ × ℕ) := certificate_1_E

noncomputable def certificate_1_part_1_M : ForbiddenMatrix := ((1,2,1) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_1_M))))))))))))))))

noncomputable def certificate_1_part_1 : FiniteCertificate := .forbid 1 2 2 (.system [[0],[1,4,5,2,3]]) (.forbid 1 2 3 (.system [[0],[1,4,5,6,2,3]]) (.forbid 1 2 4 (.cycle [1,2,7,6,5,4]) (.forbid 0 2 0 (.forbid 0 2 4 (.cycle [0,2,7,6,5,4]) (.packing {.ball 0 (.succ (.zero ∅ 2 1) {1,2} 4 2), .ball 1 (.succ (.zero ∅ 2 1) {0,2} 4 2), .ball 2 (.succ (.zero ∅ 2 1) {0,1} 4 2)})) (.packing {.ball 0 (.succ (.zero {2} 3 2) ∅ 7 3), .ball 2 (.zero {0} 3 2), .ball 1 (.succ (.zero ∅ 2 1) {0,2} 4 2)}))))

theorem certificate_1_part_1_checked : certificate_1_part_1.Valid 5 3 4 certificate_1_q certificate_1_part_1_E 1 1 certificate_1_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩⟩⟩⟩

noncomputable def certificate_1 : FiniteCertificate := .forbid 0 1 1 (.system [[0,4,1,2,3]]) (.forbid 0 1 2 (.system [[0,4,5,1],[3]]) (.forbid 0 1 3 (.system [[0,4,5,6,1],[3]]) (.forbid 0 1 4 (.system [[0,4,5,6,7,1],[3]]) (.forbid 0 2 1 (.system [[0,4,2,1],[3]]) (.forbid 0 2 2 (.system [[0,4,5,2,1],[3]]) (.forbid 0 2 3 (.system [[0,4,5,6,2,1],[3]]) (.forbid 1 2 1 (.system [[0],[1,4,2,3]]) (certificate_1_part_1))))))))

theorem certificate_1_checked : certificate_1.Valid 5 3 4 certificate_1_q certificate_1_E 1 1 certificate_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_1_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_1_valid : certificate_1.Valid 5 3 (patternOrder [[],[1]]) (patternClique [[],[1]]) (patternEdges [[],[1]]) (patternAmount [[],[1]]) (patternEdgeCount [[],[1]]) [] := certificate_1_checked

noncomputable def certificate_2_q : Finset ℕ := ([0,1,4] : List ℕ).toFinset

noncomputable def certificate_2_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(0,1),(0,4),(1,4)]

noncomputable def certificate_2_E : List (ℕ × ℕ) := certificate_2_edges

noncomputable def certificate_2_M : ForbiddenMatrix := []

noncomputable def certificate_2_part_1_E : List (ℕ × ℕ) := certificate_2_E

noncomputable def certificate_2_part_1_M : ForbiddenMatrix := ((0,4,3) :: (((0,4,1) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (certificate_2_M))))))))))))))))

noncomputable def certificate_2_part_2_E : List (ℕ × ℕ) := (augmentedEdges 5 (certificate_2_part_1_E) 1 3 0)

noncomputable def certificate_2_part_2_M : ForbiddenMatrix := ((0,4,2) :: (((3,4,2) :: (((3,4,1) :: (((2,4,2) :: (((0,1,1) :: (((2,3,1) :: (((0,4,4) :: (certificate_2_part_1_M))))))))))))))

noncomputable def certificate_2_part_2 : FiniteCertificate := .forbid 2 4 1 (.cycle [2,3,1,0,4,5]) (.forbid 3 4 3 (.cycle [3,1,4,7,6,5]) (.packing {.ball 0 (.succ (.zero ∅ 1 1) {2,3,4} 4 2), .ball 4 (.succ (.zero ∅ 1 1) {0,2,3} 4 2), .singleton 2, .ball 3 (.zero ∅ 1 1)}))

theorem certificate_2_part_2_checked : certificate_2_part_2.Valid 5 3 5 certificate_2_q certificate_2_part_2_E 2 1 certificate_2_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

noncomputable def certificate_2_part_3_E : List (ℕ × ℕ) := certificate_2_part_1_E

noncomputable def certificate_2_part_3_M : ForbiddenMatrix := ((2,3,2) :: (((1,3,0) :: (((3,4,2) :: (((3,4,1) :: (((2,4,2) :: (((0,1,1) :: (((2,3,1) :: (((0,4,4) :: (certificate_2_part_1_M))))))))))))))))

noncomputable def certificate_2_part_4_E : List (ℕ × ℕ) := (augmentedEdges 5 (certificate_2_part_3_E) 2 4 0)

noncomputable def certificate_2_part_4_M : ForbiddenMatrix := ((0,1,2) :: (((1,3,3) :: (((1,3,2) :: (((1,2,2) :: (((1,2,1) :: (((0,1,4) :: (((0,1,3) :: (certificate_2_part_3_M))))))))))))))

noncomputable def certificate_2_part_4 : FiniteCertificate := .forbid 1 3 1 (.cycle [1,0,4,2,3,5]) (.packing {.ball 0 (.succ (.zero ∅ 1 1) {1,2,3} 4 2), .ball 1 (.succ (.zero ∅ 1 1) {0,2,3} 4 2), .singleton 2, .ball 3 (.zero ∅ 1 1)})

theorem certificate_2_part_4_checked : certificate_2_part_4.Valid 5 3 5 certificate_2_q certificate_2_part_4_E 2 1 certificate_2_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

noncomputable def certificate_2_part_5_E : List (ℕ × ℕ) := (augmentedEdges 5 (certificate_2_part_3_E) 2 4 1)

noncomputable def certificate_2_part_5_M : ForbiddenMatrix := ((2,4,0) :: (((1,3,3) :: (((1,3,2) :: (((1,2,2) :: (((1,2,1) :: (((0,1,4) :: (((0,1,3) :: (certificate_2_part_3_M))))))))))))))

noncomputable def certificate_2_part_5 : FiniteCertificate := .forbid 0 3 0 (.cycle [0,1,2,5,4,3]) (.forbid 0 5 1 (.cycle [0,4,1,2,5,6]) (.forbid 0 5 2 (.cycle [0,1,2,5,7,6]) (.forbid 2 5 1 (.cycle [2,1,0,4,5,6]) (.forbid 3 5 0 (.cycle [3,2,1,0,4,5]) (.forbid 3 5 1 (.cycle [3,2,1,4,5,6]) (.packing {.ball 0 (.succ (.zero {3} 1 1) {1,2,3,5} 4 2), .ball 3 (.zero {0,1,5} 3 2), .singleton 5, .ball 2 (.zero {4} 1 1)}))))))

theorem certificate_2_part_5_checked : certificate_2_part_5.Valid 5 3 6 certificate_2_q certificate_2_part_5_E 2 1 certificate_2_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

noncomputable def certificate_2_part_6_E : List (ℕ × ℕ) := certificate_2_part_3_E

noncomputable def certificate_2_part_6_M : ForbiddenMatrix := ((2,4,1) :: (((2,4,0) :: (((1,3,3) :: (((1,3,2) :: (((1,2,2) :: (((1,2,1) :: (((0,1,4) :: (((0,1,3) :: (certificate_2_part_3_M))))))))))))))))

noncomputable def certificate_2_part_6 : FiniteCertificate := .forbid 0 2 0 (.forbid 0 2 4 (.cycle [0,2,8,7,6,5]) (.forbid 0 4 2 (.cycle [0,2,1,4,6,5]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {2,3,4} 4 2) {2} 7 3), .singleton 3, .ball 2 (.zero ∅ 1 1), .ball 4 (.zero ∅ 1 1)}))) (.forbid 1 3 1 (.forbid 0 5 1 (.cycle [0,1,2,3,5,6]) (.forbid 0 5 2 (.cycle [0,4,1,5,7,6]) (.forbid 2 5 0 (.cycle [2,1,0,4,3,5]) (.forbid 2 5 1 (.cycle [2,1,4,3,5,6]) (.forbid 3 5 1 (.cycle [3,4,0,1,5,6]) (.packing {.ball 0 (.succ (.zero {2} 1 1) {1,2,3,5} 4 2), .ball 2 (.zero {0,4,5} 3 2), .singleton 5, .ball 3 (.zero {1} 1 1)})))))) (.forbid 0 3 0 (.forbid 0 1 2 (.cycle [0,3,2,1,6,5]) (.forbid 0 3 4 (.cycle [0,3,8,7,6,5]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3} 4 2) {1} 7 3), .singleton 2, .ball 1 (.zero ∅ 1 1), .ball 3 (.zero ∅ 1 1)}))) (.packing {.ball 0 (.succ (.zero {2,3} 3 2) {2} 7 3), .ball 2 (.zero {0,4} 3 2), .ball 3 (.zero {0,1} 3 2)})))

theorem certificate_2_part_6_checked : certificate_2_part_6.Valid 5 3 5 certificate_2_q certificate_2_part_6_E 2 1 certificate_2_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, by decide +kernel⟩⟩⟩

noncomputable def certificate_2_part_3 : FiniteCertificate := .forbid 0 1 3 (.system [[0,5,6,7,1],[4]]) (.forbid 0 1 4 (.system [[0,5,6,7,8,1],[4]]) (.forbid 1 2 1 (.system [[0],[1,5,2,3,4]]) (.forbid 1 2 2 (.system [[0],[1,5,6,2,3,4]]) (.forbid 1 3 2 (.system [[0],[1,5,6,3,4]]) (.forbid 1 3 3 (.system [[0],[1,5,6,7,3,4]]) (.forbid 2 4 0 (.forbid 0 1 2 (.cycle [0,4,2,1,6,5]) (certificate_2_part_4)) (.forbid 2 4 1 (certificate_2_part_5) (certificate_2_part_6))))))))

theorem certificate_2_part_3_checked : certificate_2_part_3.Valid 5 3 5 certificate_2_q certificate_2_part_3_E 2 1 certificate_2_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_2_part_4_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_2_part_5_checked, certificate_2_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_2_part_1 : FiniteCertificate := .forbid 0 4 4 (.system [[0,5,6,7,8,4],[1]]) (.forbid 2 3 1 (.system [[0],[1,2,5,3,4]]) (.forbid 0 1 1 (.system [[0,5,1,2,3,4]]) (.forbid 2 4 2 (.system [[0],[1,2,5,6,4]]) (.forbid 3 4 1 (.system [[0],[1,2,3,5,4]]) (.forbid 3 4 2 (.system [[0],[1,2,3,5,6,4]]) (.forbid 1 3 0 (.forbid 0 4 2 (.cycle [0,1,3,4,6,5]) (certificate_2_part_2)) (.forbid 2 3 2 (.system [[0],[1,2,5,6,3,4]]) (certificate_2_part_3))))))))

theorem certificate_2_part_1_checked : certificate_2_part_1.Valid 5 3 5 certificate_2_q certificate_2_part_1_E 2 1 certificate_2_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_2_part_2_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_2_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_2 : FiniteCertificate := .forbid 0 2 1 (.system [[0,5,2,3,4],[1]]) (.forbid 0 2 2 (.system [[0,5,6,2,1],[4]]) (.forbid 0 2 3 (.system [[0,5,6,7,2,1],[4]]) (.forbid 0 3 1 (.system [[0,5,3,2,1],[4]]) (.forbid 0 3 2 (.system [[0,5,6,3,2,1],[4]]) (.forbid 0 3 3 (.system [[0,5,6,7,3,4],[1]]) (.forbid 0 4 1 (.system [[0,5,4,3,2,1]]) (.forbid 0 4 3 (.system [[0,5,6,7,4],[1]]) (certificate_2_part_1))))))))

theorem certificate_2_checked : certificate_2.Valid 5 3 5 certificate_2_q certificate_2_E 2 1 certificate_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_2_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_2_valid : certificate_2.Valid 5 3 (patternOrder [[],[2]]) (patternClique [[],[2]]) (patternEdges [[],[2]]) (patternAmount [[],[2]]) (patternEdgeCount [[],[2]]) [] := certificate_2_checked

noncomputable def certificate_3_q : Finset ℕ := ([0,2,4] : List ℕ).toFinset

noncomputable def certificate_3_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(0,2),(0,4),(2,4)]

noncomputable def certificate_3_E : List (ℕ × ℕ) := certificate_3_edges

noncomputable def certificate_3_M : ForbiddenMatrix := []

noncomputable def certificate_3_part_1_E : List (ℕ × ℕ) := certificate_3_E

noncomputable def certificate_3_part_1_M : ForbiddenMatrix := ((0,4,1) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_3_M))))))))))))))))

noncomputable def certificate_3_part_1 : FiniteCertificate := .forbid 0 4 2 (.system [[0,5,6,4],[2]]) (.forbid 0 4 3 (.system [[0,5,6,7,4],[2]]) (.forbid 0 4 4 (.system [[0,5,6,7,8,4],[2]]) (.forbid 1 3 1 (.system [[0,1,5,3,2],[4]]) (.forbid 1 4 1 (.system [[0,1,5,4],[2]]) (.forbid 1 4 2 (.system [[0,1,5,6,4],[2]]) (.forbid 3 4 1 (.system [[0],[2,3,5,4]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4} 4 2) {1} 7 3), .singleton 3, .ball 1 (.zero ∅ 1 1), .ball 4 (.zero ∅ 1 1)})))))))

theorem certificate_3_part_1_checked : certificate_3_part_1.Valid 5 3 5 certificate_3_q certificate_3_part_1_E 2 2 certificate_3_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_3 : FiniteCertificate := .forbid 0 1 1 (.system [[0,5,1,2],[4]]) (.forbid 0 1 2 (.system [[0,5,6,1,2],[4]]) (.forbid 0 1 3 (.system [[0,5,6,7,1,2],[4]]) (.forbid 0 1 4 (.cycle [0,1,8,7,6,5]) (.forbid 0 3 1 (.system [[0,5,3,2],[4]]) (.forbid 0 3 2 (.system [[0,5,6,3,2],[4]]) (.forbid 0 3 3 (.system [[0,5,6,7,3,2],[4]]) (.forbid 0 4 1 (.cycle [0,1,2,3,4,5]) (certificate_3_part_1))))))))

theorem certificate_3_checked : certificate_3.Valid 5 3 5 certificate_3_q certificate_3_E 2 2 certificate_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_3_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_3_valid : certificate_3.Valid 5 3 (patternOrder [[1,1]]) (patternClique [[1,1]]) (patternEdges [[1,1]]) (patternAmount [[1,1]]) (patternEdgeCount [[1,1]]) [] := certificate_3_checked

noncomputable def certificate_4_q : Finset ℕ := ([0,1,2,3] : List ℕ).toFinset
noncomputable def certificate_4_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

noncomputable def certificate_4 : FiniteCertificate := .forbid 0 1 1 (.system [[0,4,1],[2],[3]]) (.forbid 0 1 2 (.system [[0,4,5,1],[2],[3]]) (.forbid 0 1 3 (.system [[0,4,5,6,1],[2],[3]]) (.forbid 0 2 1 (.system [[0,4,2],[1],[3]]) (.forbid 0 2 2 (.system [[0,4,5,2],[1],[3]]) (.forbid 0 2 3 (.system [[0,4,5,6,2],[1],[3]]) (.forbid 0 2 4 (.system [[0,4,5,6,7,2],[1],[3]]) (.forbid 0 3 1 (.system [[0,4,3],[1],[2]]) (.forbid 0 3 2 (.system [[0,4,5,3],[1],[2]]) (.forbid 0 3 3 (.system [[0,4,5,6,3],[1],[2]]) (.forbid 0 3 4 (.system [[0,4,5,6,7,3],[1],[2]]) (.forbid 1 2 1 (.system [[0],[1,4,2],[3]]) (.forbid 1 3 1 (.system [[0],[1,4,3],[2]]) (.forbid 2 3 1 (.system [[0],[1],[2,4,3]]) (.forbid 2 3 2 (.system [[0],[1],[2,4,5,3]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,2,3} 5 2) {1,2} 9 3), .singleton 1, .ball 2 (.zero ∅ 2 1), .ball 3 (.zero ∅ 2 1)})))))))))))))))

theorem certificate_4_checked : certificate_4.Valid 5 4 4 certificate_4_q certificate_4_edges 0 0 [] := by decide +kernel
theorem certificate_4_valid : certificate_4.Valid 5 4 (patternOrder [[],[],[],[]]) (patternClique [[],[],[],[]]) (patternEdges [[],[],[],[]]) (patternAmount [[],[],[],[]]) (patternEdgeCount [[],[],[],[]]) [] := certificate_4_checked

noncomputable def certificate_5_q : Finset ℕ := ([0,1,2,4] : List ℕ).toFinset
noncomputable def certificate_5_edges : List (ℕ × ℕ) := [(2,3),(3,4),(0,1),(0,2),(0,4),(1,2),(1,4),(2,4)]

noncomputable def certificate_5 : FiniteCertificate := .forbid 0 1 1 (.system [[0,5,1],[2,3,4]]) (.forbid 0 1 2 (.system [[0,5,6,1],[2],[4]]) (.forbid 0 1 3 (.system [[0,5,6,7,1],[2],[4]]) (.forbid 0 1 4 (.system [[0,5,6,7,8,1],[2],[4]]) (.forbid 0 2 1 (.system [[0,5,2,3,4],[1]]) (.forbid 0 2 2 (.system [[0,5,6,2],[1],[4]]) (.forbid 0 2 3 (.system [[0,5,6,7,2],[1],[4]]) (.forbid 0 2 4 (.system [[0,5,6,7,8,2],[1],[4]]) (.forbid 0 3 1 (.system [[0,5,3,2],[1],[4]]) (.forbid 0 3 2 (.system [[0,5,6,3,2],[1],[4]]) (.forbid 0 3 3 (.system [[0,5,6,7,3,2],[1],[4]]) (.forbid 0 4 1 (.system [[0,5,4,3,2],[1]]) (.forbid 1 2 1 (.system [[0],[1,5,2,3,4]]) (.forbid 1 2 2 (.system [[0],[1,5,6,2],[4]]) (.forbid 1 3 1 (.system [[0],[1,5,3,2],[4]]) (.forbid 2 3 1 (.system [[0],[1],[2,5,3,4]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,4} 5 2) {1,2,3} 9 3), .singleton 3, .ball 1 (.zero ∅ 1 1), .ball 2 (.zero ∅ 1 1)}))))))))))))))))

theorem certificate_5_checked : certificate_5.Valid 5 4 5 certificate_5_q certificate_5_edges 1 1 [] := by decide +kernel
theorem certificate_5_valid : certificate_5.Valid 5 4 (patternOrder [[],[],[1]]) (patternClique [[],[],[1]]) (patternEdges [[],[],[1]]) (patternAmount [[],[],[1]]) (patternEdgeCount [[],[],[1]]) [] := certificate_5_checked

noncomputable def certificate_6_q : Finset ℕ := ([0,1,2,3,4] : List ℕ).toFinset
noncomputable def certificate_6_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

noncomputable def certificate_6_part_0 : FiniteCertificate := .forbid 2 4 1 (.system [[0],[1],[2,5,4],[3]]) (.forbid 2 4 2 (.system [[0],[1],[2,5,6,4],[3]]) (.forbid 3 4 1 (.system [[0],[1],[2],[3,5,4]]) (.forbid 3 4 2 (.system [[0],[1],[2],[3,5,6,4]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,4} 5 1) {1,2,3,4} 5 2), .singleton 1, .ball 2 (.zero ∅ 1 1), .ball 3 (.zero ∅ 1 1), .ball 4 (.zero ∅ 1 1)}))))

noncomputable def certificate_6 : FiniteCertificate := .forbid 0 1 1 (.system [[0,5,1],[2],[3],[4]]) (.forbid 0 1 2 (.system [[0,5,6,1],[2],[3],[4]]) (.forbid 0 1 3 (.system [[0,5,6,7,1],[2],[3],[4]]) (.forbid 0 2 1 (.system [[0,5,2],[1],[3],[4]]) (.forbid 0 2 2 (.system [[0,5,6,2],[1],[3],[4]]) (.forbid 0 2 3 (.system [[0,5,6,7,2],[1],[3],[4]]) (.forbid 0 2 4 (.system [[0,5,6,7,8,2],[1],[3],[4]]) (.forbid 0 3 1 (.system [[0,5,3],[1],[2],[4]]) (.forbid 0 3 2 (.system [[0,5,6,3],[1],[2],[4]]) (.forbid 0 3 3 (.system [[0,5,6,7,3],[1],[2],[4]]) (.forbid 0 3 4 (.system [[0,5,6,7,8,3],[1],[2],[4]]) (.forbid 0 4 1 (.system [[0,5,4],[1],[2],[3]]) (.forbid 0 4 2 (.system [[0,5,6,4],[1],[2],[3]]) (.forbid 0 4 3 (.system [[0,5,6,7,4],[1],[2],[3]]) (.forbid 0 4 4 (.system [[0,5,6,7,8,4],[1],[2],[3]]) (.forbid 1 2 1 (.system [[0],[1,5,2],[3],[4]]) (.forbid 1 3 1 (.system [[0],[1,5,3],[2],[4]]) (.forbid 1 4 1 (.system [[0],[1,5,4],[2],[3]]) (.forbid 2 3 1 (.system [[0],[1],[2,5,3],[4]]) (.forbid 2 3 2 (.system [[0],[1],[2,5,6,3],[4]]) (certificate_6_part_0))))))))))))))))))))

theorem certificate_6_checked : certificate_6.Valid 5 5 5 certificate_6_q certificate_6_edges 0 0 [] := by decide +kernel
theorem certificate_6_valid : certificate_6.Valid 5 5 (patternOrder [[],[],[],[],[]]) (patternClique [[],[],[],[],[]]) (patternEdges [[],[],[],[],[]]) (patternAmount [[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[]]) [] := certificate_6_checked

noncomputable def certificate_7_q : Finset ℕ := ([0,1,2] : List ℕ).toFinset
noncomputable def certificate_7_edges : List (ℕ × ℕ) := [(0,1),(0,2),(1,2)]

noncomputable def certificate_7 : FiniteCertificate := .forbid 0 1 1 (.system [[0,3,1],[2]]) (.forbid 0 1 2 (.system [[0,3,4,1],[2]]) (.forbid 0 1 3 (.system [[0,3,4,5,1],[2]]) (.forbid 0 1 4 (.system [[0,3,4,5,6,1],[2]]) (.forbid 0 2 1 (.system [[0,3,2],[1]]) (.forbid 0 2 2 (.system [[0,3,4,2],[1]]) (.forbid 0 2 3 (.system [[0,3,4,5,2],[1]]) (.forbid 0 2 4 (.system [[0,3,4,5,6,2],[1]]) (.forbid 1 2 1 (.system [[0],[1,3,2]]) (.forbid 1 2 2 (.system [[0],[1,3,4,2]]) (.forbid 1 2 3 (.system [[0],[1,3,4,5,2]]) (.forbid 1 2 4 (.system [[0],[1,3,4,5,6,2]]) (.packing {.ball 0 (.succ (.zero ∅ 4 2) ∅ 10 3), .ball 1 (.succ (.zero ∅ 4 2) ∅ 10 3), .ball 2 (.succ (.zero ∅ 4 2) ∅ 10 3)}))))))))))))

theorem certificate_7_checked : certificate_7.Valid 6 3 3 certificate_7_q certificate_7_edges 0 0 [] := by decide +kernel
theorem certificate_7_valid : certificate_7.Valid 6 3 (patternOrder [[],[],[]]) (patternClique [[],[],[]]) (patternEdges [[],[],[]]) (patternAmount [[],[],[]]) (patternEdgeCount [[],[],[]]) [] := certificate_7_checked

noncomputable def certificate_8_q : Finset ℕ := ([0,1,3] : List ℕ).toFinset
noncomputable def certificate_8_edges : List (ℕ × ℕ) := [(1,2),(2,3),(0,1),(0,3),(1,3)]

noncomputable def certificate_8 : FiniteCertificate := .forbid 0 1 1 (.system [[0,4,1,2,3]]) (.forbid 0 1 2 (.system [[0,4,5,1],[3]]) (.forbid 0 1 3 (.system [[0,4,5,6,1],[3]]) (.forbid 0 1 4 (.system [[0,4,5,6,7,1],[3]]) (.forbid 0 2 1 (.system [[0,4,2,1],[3]]) (.forbid 0 2 2 (.system [[0,4,5,2,1],[3]]) (.forbid 0 2 3 (.system [[0,4,5,6,2,1],[3]]) (.forbid 0 2 4 (.system [[0,4,5,6,7,2,1],[3]]) (.forbid 1 2 1 (.system [[0],[1,4,2,3]]) (.forbid 1 2 2 (.system [[0],[1,4,5,2,3]]) (.forbid 1 2 3 (.system [[0],[1,4,5,6,2,3]]) (.forbid 1 2 4 (.system [[0],[1,4,5,6,7,2,3]]) (.packing {.ball 0 (.succ (.zero ∅ 3 2) ∅ 9 3), .ball 2 (.succ (.zero ∅ 3 2) ∅ 9 3), .ball 1 (.succ (.zero ∅ 3 2) ∅ 9 3)}))))))))))))

theorem certificate_8_checked : certificate_8.Valid 6 3 4 certificate_8_q certificate_8_edges 1 1 [] := by decide +kernel
theorem certificate_8_valid : certificate_8.Valid 6 3 (patternOrder [[],[1]]) (patternClique [[],[1]]) (patternEdges [[],[1]]) (patternAmount [[],[1]]) (patternEdgeCount [[],[1]]) [] := certificate_8_checked

noncomputable def certificate_9_q : Finset ℕ := ([0,1,4] : List ℕ).toFinset

noncomputable def certificate_9_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(0,1),(0,4),(1,4)]

noncomputable def certificate_9_E : List (ℕ × ℕ) := certificate_9_edges

noncomputable def certificate_9_M : ForbiddenMatrix := []

noncomputable def certificate_9_part_1_E : List (ℕ × ℕ) := certificate_9_E

noncomputable def certificate_9_part_1_M : ForbiddenMatrix := ((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,5) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_9_M))))))))))))))))

noncomputable def certificate_9_part_2_E : List (ℕ × ℕ) := certificate_9_part_1_E

noncomputable def certificate_9_part_2_M : ForbiddenMatrix := ((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((0,2,0) :: (((1,2,3) :: (((1,2,2) :: (((1,2,1) :: (((0,2,4) :: (certificate_9_part_1_M))))))))))))))))

noncomputable def certificate_9_part_3_E : List (ℕ × ℕ) := certificate_9_part_2_E

noncomputable def certificate_9_part_3_M : ForbiddenMatrix := ((1,3,2) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((2,4,0) :: (((1,2,5) :: (((0,4,4) :: (certificate_9_part_2_M))))))))))))))))

noncomputable def certificate_9_part_3 : FiniteCertificate := .forbid 1 3 3 (.system [[0],[1,5,6,7,3,4]]) (.forbid 2 3 1 (.system [[0],[1,2,5,3,4]]) (.forbid 2 4 1 (.forbid 1 3 1 (.cycle [1,0,4,5,2,3,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3} 4 2) ∅ 7 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,3} 4 2), .singleton 2, .ball 3 (.zero ∅ 1 1)})) (.forbid 2 4 2 (.system [[0],[1,2,5,6,4]]) (.forbid 2 4 3 (.system [[0],[1,2,5,6,7,4]]) (.forbid 2 4 4 (.system [[0],[1,2,5,6,7,8,4]]) (.packing {.ball 0 (.succ (.zero {2} 3 2) ∅ 8 3), .ball 2 (.succ (.zero {0} 3 2) ∅ 8 3), .ball 4 (.succ (.zero {2} 3 2) ∅ 8 3)}))))))

theorem certificate_9_part_3_checked : certificate_9_part_3.Valid 6 3 5 certificate_9_q certificate_9_part_3_E 2 1 certificate_9_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

noncomputable def certificate_9_part_2 : FiniteCertificate := .forbid 0 4 4 (.system [[0,5,6,7,8,4],[1]]) (.forbid 1 2 5 (.cycle [1,2,9,8,7,6,5]) (.forbid 2 4 0 (.forbid 1 2 4 (.cycle [1,4,2,8,7,6,5]) (.packing {.ball 0 (.succ (.zero ∅ 2 1) {1,2} 4 2), .ball 1 (.succ (.succ (.zero ∅ 2 1) {0,2} 4 2) ∅ 8 3), .ball 2 (.succ (.zero ∅ 2 1) {0,1} 4 2)})) (.forbid 0 3 1 (.system [[0,5,3,2,1],[4]]) (.forbid 0 3 2 (.system [[0,5,6,3,2,1],[4]]) (.forbid 0 3 3 (.system [[0,5,6,7,3,2,1],[4]]) (.forbid 0 3 4 (.system [[0,5,6,7,8,3,4],[1]]) (.forbid 1 3 2 (.system [[0],[1,5,6,3,4]]) (certificate_9_part_3))))))))

theorem certificate_9_part_2_checked : certificate_9_part_2.Valid 6 3 5 certificate_9_q certificate_9_part_2_E 2 1 certificate_9_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_9_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_9_part_1 : FiniteCertificate := .forbid 0 2 4 (.system [[0,5,6,7,8,2,1],[4]]) (.forbid 1 2 1 (.system [[0],[1,5,2,3,4]]) (.forbid 1 2 2 (.system [[0],[1,5,6,2,3,4]]) (.forbid 1 2 3 (.system [[0],[1,5,6,7,2,3,4]]) (.forbid 0 2 0 (.forbid 0 2 5 (.cycle [0,2,9,8,7,6,5]) (.forbid 1 2 4 (.cycle [1,0,2,8,7,6,5]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,2} 4 2) ∅ 8 3), .ball 1 (.succ (.zero ∅ 2 1) {0,2} 4 2), .ball 2 (.succ (.zero ∅ 2 1) {0,1} 4 2)}))) (.forbid 0 4 1 (.system [[0,5,4,3,2,1]]) (.forbid 0 4 2 (.system [[0,5,6,4,3,2,1]]) (.forbid 0 4 3 (.system [[0,5,6,7,4],[1]]) (certificate_9_part_2))))))))

theorem certificate_9_part_1_checked : certificate_9_part_1.Valid 6 3 5 certificate_9_q certificate_9_part_1_E 2 1 certificate_9_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_9_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_9 : FiniteCertificate := .forbid 0 1 1 (.system [[0,5,1,2,3,4]]) (.forbid 0 1 2 (.system [[0,5,6,1,2,3,4]]) (.forbid 0 1 3 (.system [[0,5,6,7,1],[4]]) (.forbid 0 1 4 (.system [[0,5,6,7,8,1],[4]]) (.forbid 0 1 5 (.system [[0,5,6,7,8,9,1],[4]]) (.forbid 0 2 1 (.system [[0,5,2,3,4],[1]]) (.forbid 0 2 2 (.system [[0,5,6,2,1],[4]]) (.forbid 0 2 3 (.system [[0,5,6,7,2,1],[4]]) (certificate_9_part_1))))))))

theorem certificate_9_checked : certificate_9.Valid 6 3 5 certificate_9_q certificate_9_E 2 1 certificate_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_9_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_9_valid : certificate_9.Valid 6 3 (patternOrder [[],[2]]) (patternClique [[],[2]]) (patternEdges [[],[2]]) (patternAmount [[],[2]]) (patternEdgeCount [[],[2]]) [] := certificate_9_checked

noncomputable def certificate_10_q : Finset ℕ := ([0,1,5] : List ℕ).toFinset

noncomputable def certificate_10_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(0,1),(0,5),(1,5)]

noncomputable def certificate_10_E : List (ℕ × ℕ) := certificate_10_edges

noncomputable def certificate_10_M : ForbiddenMatrix := []

noncomputable def certificate_10_part_1_E : List (ℕ × ℕ) := certificate_10_E

noncomputable def certificate_10_part_1_M : ForbiddenMatrix := ((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((0,2,4) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,1) :: (certificate_10_M))))))))))))))))

noncomputable def certificate_10_part_2_E : List (ℕ × ℕ) := (augmentedEdges 6 (certificate_10_part_1_E) 0 3 1)

noncomputable def certificate_10_part_2_M : ForbiddenMatrix := ((2,4,0) :: (((1,4,0) :: (((0,4,0) :: (((0,2,0) :: (((2,4,2) :: (((0,5,1) :: (((0,4,4) :: (certificate_10_part_1_M))))))))))))))

noncomputable def certificate_10_part_2 : FiniteCertificate := .forbid 2 4 1 (.cycle [2,1,0,6,3,4,7]) (.forbid 2 5 0 (.cycle [2,1,0,6,3,4,5]) (.packing {.ball 0 (.succ (.succ (.zero {2} 1 1) {1,2,4,5} 4 2) {2} 7 3), .ball 2 (.zero {0,4,5} 3 2), .ball 4 (.zero {0,1,2} 3 2)}))

theorem certificate_10_part_2_checked : certificate_10_part_2.Valid 6 3 7 certificate_10_q certificate_10_part_2_E 3 1 certificate_10_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

noncomputable def certificate_10_part_3_E : List (ℕ × ℕ) := certificate_10_part_1_E

noncomputable def certificate_10_part_3_M : ForbiddenMatrix := ((0,5,5) :: (((0,5,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((2,4,2) :: (((0,5,1) :: (((0,4,4) :: (certificate_10_part_1_M))))))))))))))))

noncomputable def certificate_10_part_4_E : List (ℕ × ℕ) := (augmentedEdges 6 (certificate_10_part_3_E) 3 5 1)

noncomputable def certificate_10_part_4_M : ForbiddenMatrix := ((2,4,1) :: (((2,4,0) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((0,4,0) :: (((3,4,1) :: (certificate_10_part_3_M))))))))))))))

noncomputable def certificate_10_part_4 : FiniteCertificate := .forbid 2 6 0 (.cycle [2,1,0,5,4,3,6]) (.forbid 4 6 0 (.cycle [4,3,2,1,0,5,6]) (.forbid 4 6 1 (.cycle [4,3,2,1,5,6,7]) (.packing {.ball 0 (.succ (.succ (.zero {4} 1 1) {1,2,4,6} 4 2) {2} 7 3), .ball 4 (.zero {0,2,6} 3 2), .singleton 6, .singleton 2})))

theorem certificate_10_part_4_checked : certificate_10_part_4.Valid 6 3 7 certificate_10_q certificate_10_part_4_E 3 1 certificate_10_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

noncomputable def certificate_10_part_5_E : List (ℕ × ℕ) := (augmentedEdges 6 (certificate_10_part_3_E) 0 2 0)

noncomputable def certificate_10_part_5_M : ForbiddenMatrix := ((0,3,4) :: (((4,5,2) :: (((4,5,1) :: (((3,5,3) :: (((3,5,2) :: (((3,5,1) :: (((3,4,1) :: (certificate_10_part_3_M))))))))))))))

noncomputable def certificate_10_part_5 : FiniteCertificate := .forbid 0 5 2 (.cycle [0,2,3,4,5,7,6]) (.forbid 0 5 3 (.cycle [0,2,1,5,8,7,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {3,4,5} 4 2) ∅ 7 3), .ball 5 (.succ (.zero ∅ 1 1) {0,3,4} 4 2), .singleton 4, .ball 3 (.zero ∅ 1 1)}))

theorem certificate_10_part_5_checked : certificate_10_part_5.Valid 6 3 6 certificate_10_q certificate_10_part_5_E 3 1 certificate_10_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

noncomputable def certificate_10_part_6_E : List (ℕ × ℕ) := certificate_10_part_3_E

noncomputable def certificate_10_part_6_M : ForbiddenMatrix := ((0,1,4) :: (((0,2,0) :: (((4,5,2) :: (((4,5,1) :: (((3,5,3) :: (((3,5,2) :: (((3,5,1) :: (((3,4,1) :: (certificate_10_part_3_M))))))))))))))))

noncomputable def certificate_10_part_7_E : List (ℕ × ℕ) := (augmentedEdges 6 (certificate_10_part_6_E) 0 3 0)

noncomputable def certificate_10_part_7_M : ForbiddenMatrix := ((1,4,1) :: (((0,1,3) :: (((0,1,2) :: (((1,4,3) :: (((1,2,2) :: (((1,2,1) :: (((0,1,5) :: (certificate_10_part_6_M))))))))))))))

noncomputable def certificate_10_part_7 : FiniteCertificate := .forbid 1 4 2 (.cycle [1,5,0,3,4,7,6]) (.forbid 2 4 1 (.cycle [2,1,5,0,3,4,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,4} 4 2) ∅ 7 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,4} 4 2), .singleton 2, .ball 4 (.zero ∅ 1 1)}))

theorem certificate_10_part_7_checked : certificate_10_part_7.Valid 6 3 6 certificate_10_q certificate_10_part_7_E 3 1 certificate_10_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

noncomputable def certificate_10_part_8_E : List (ℕ × ℕ) := (augmentedEdges 6 (certificate_10_part_6_E) 1 3 1)

noncomputable def certificate_10_part_8_M : ForbiddenMatrix := ((0,6,2) :: (((0,6,1) :: (((0,3,0) :: (((1,4,3) :: (((1,2,2) :: (((1,2,1) :: (((0,1,5) :: (certificate_10_part_6_M))))))))))))))

noncomputable def certificate_10_part_8 : FiniteCertificate := .forbid 0 6 3 (.cycle [0,5,1,6,9,8,7]) (.forbid 2 4 0 (.cycle [2,3,6,1,0,5,4]) (.forbid 2 4 1 (.cycle [2,3,6,1,5,4,7]) (.forbid 2 6 0 (.cycle [2,1,0,5,4,3,6]) (.forbid 2 6 1 (.cycle [2,1,5,4,3,6,7]) (.forbid 4 6 0 (.cycle [4,5,0,1,2,3,6]) (.packing {.ball 0 (.succ (.succ (.zero {2} 1 1) {1,2,4,6} 4 2) {2} 7 3), .ball 2 (.zero {0,4,6} 3 2), .singleton 6, .singleton 4}))))))

theorem certificate_10_part_8_checked : certificate_10_part_8.Valid 6 3 7 certificate_10_q certificate_10_part_8_E 3 1 certificate_10_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

noncomputable def certificate_10_part_9_E : List (ℕ × ℕ) := certificate_10_part_6_E

noncomputable def certificate_10_part_9_M : ForbiddenMatrix := ((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((0,3,0) :: (((1,4,3) :: (((1,2,2) :: (((1,2,1) :: (((0,1,5) :: (certificate_10_part_6_M))))))))))))))))

noncomputable def certificate_10_part_10_E : List (ℕ × ℕ) := (augmentedEdges 6 (certificate_10_part_9_E) 2 4 0)

noncomputable def certificate_10_part_10_M : ForbiddenMatrix := ((1,3,0) :: (((3,4,2) :: (((2,4,4) :: (((2,4,3) :: (((2,3,2) :: (((0,4,0) :: (((2,3,1) :: (certificate_10_part_9_M))))))))))))))

noncomputable def certificate_10_part_10 : FiniteCertificate := .forbid 0 1 2 (.cycle [0,5,4,2,1,7,6]) (.packing {.ball 0 (.succ (.zero {2,3} 3 2) ∅ 7 3), .ball 3 (.zero {0,1} 3 2), .singleton 1, .ball 2 (.zero ∅ 1 1)})

theorem certificate_10_part_10_checked : certificate_10_part_10.Valid 6 3 6 certificate_10_q certificate_10_part_10_E 3 1 certificate_10_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

noncomputable def certificate_10_part_11_E : List (ℕ × ℕ) := certificate_10_part_9_E

noncomputable def certificate_10_part_11_M : ForbiddenMatrix := ((2,4,0) :: (((1,3,0) :: (((3,4,2) :: (((2,4,4) :: (((2,4,3) :: (((2,3,2) :: (((0,4,0) :: (((2,3,1) :: (certificate_10_part_9_M))))))))))))))))

noncomputable def certificate_10_part_12_E : List (ℕ × ℕ) := (augmentedEdges 6 (certificate_10_part_11_E) 2 5 1)

noncomputable def certificate_10_part_12_M : ForbiddenMatrix := ((1,6,0) :: (((1,4,0) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((0,6,0) :: (certificate_10_part_11_M))))))))))))))

noncomputable def certificate_10_part_12 : FiniteCertificate := .forbid 4 6 0 (.cycle [4,3,2,1,0,5,6]) (.forbid 4 6 1 (.cycle [4,3,2,1,5,6,7]) (.forbid 4 6 2 (.cycle [4,5,1,2,6,8,7]) (.forbid 4 6 3 (.cycle [4,3,2,6,9,8,7]) (.forbid 4 6 4 (.cycle [4,5,6,10,9,8,7]) (.packing {.ball 0 (.succ (.zero {3,4,6} 3 2) {4} 7 3), .ball 4 (.succ (.zero {0,1,6} 3 2) {0} 7 3), .ball 6 (.succ (.zero {0,1,4} 3 2) {0} 7 3)})))))

theorem certificate_10_part_12_checked : certificate_10_part_12.Valid 6 3 7 certificate_10_q certificate_10_part_12_E 3 1 certificate_10_part_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

noncomputable def certificate_10_part_13_E : List (ℕ × ℕ) := (augmentedEdges 6 (certificate_10_part_11_E) 1 4 1)

noncomputable def certificate_10_part_13_M : ForbiddenMatrix := ((2,5,0) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((0,6,0) :: (((2,5,1) :: (certificate_10_part_11_M))))))))))))))

noncomputable def certificate_10_part_13 : FiniteCertificate := .forbid 2 6 0 (.cycle [2,3,4,5,0,1,6]) (.forbid 2 6 1 (.cycle [2,1,0,5,4,6,7]) (.forbid 2 6 2 (.cycle [2,1,5,4,6,8,7]) (.forbid 2 6 3 (.cycle [2,3,4,6,9,8,7]) (.forbid 2 6 4 (.cycle [2,1,6,10,9,8,7]) (.forbid 3 6 0 (.cycle [3,2,1,0,5,4,6]) (.packing {.ball 0 (.succ (.zero {2,3,6} 3 2) {2} 7 3), .ball 2 (.succ (.zero {0,5,6} 3 2) {0} 7 3), .ball 6 (.succ (.zero {0,2,3} 3 2) {0} 7 3)}))))))

theorem certificate_10_part_13_checked : certificate_10_part_13.Valid 6 3 7 certificate_10_q certificate_10_part_13_E 3 1 certificate_10_part_13_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

noncomputable def certificate_10_part_11 : FiniteCertificate := .forbid 2 5 1 (.forbid 0 6 0 (.cycle [0,1,2,3,4,5,6]) (.forbid 0 6 1 (.cycle [0,5,4,3,2,6,7]) (.forbid 0 6 2 (.cycle [0,5,1,2,6,8,7]) (.forbid 0 6 3 (.cycle [0,1,2,6,9,8,7]) (.forbid 0 6 4 (.cycle [0,5,6,10,9,8,7]) (.forbid 1 4 0 (.cycle [1,0,5,6,2,3,4]) (.forbid 1 6 0 (.cycle [1,0,5,4,3,2,6]) (certificate_10_part_12)))))))) (.forbid 1 4 1 (.forbid 0 6 0 (.cycle [0,5,1,2,3,4,6]) (.forbid 0 6 1 (.cycle [0,1,2,3,4,6,7]) (.forbid 0 6 2 (.cycle [0,1,5,4,6,8,7]) (.forbid 0 6 3 (.cycle [0,5,1,6,9,8,7]) (.forbid 0 6 4 (.cycle [0,1,6,10,9,8,7]) (.forbid 2 5 0 (.cycle [2,3,4,6,1,0,5]) (certificate_10_part_13))))))) (.forbid 3 5 0 (.forbid 0 1 2 (.cycle [0,5,3,2,1,7,6]) (.forbid 1 4 2 (.cycle [1,0,5,3,4,7,6]) (.forbid 2 4 1 (.cycle [2,1,0,5,3,4,6]) (.packing {.ball 0 (.succ (.zero ∅ 1 1) {1,2,4} 4 2), .ball 2 (.succ (.zero ∅ 1 1) {0,1,4} 4 2), .ball 4 (.succ (.zero ∅ 1 1) {0,1,2} 4 2), .singleton 1})))) (.forbid 2 4 1 (.forbid 2 3 3 (.cycle [2,6,4,3,9,8,7]) (.packing {.ball 0 (.succ (.zero {2,3,4} 3 2) {2} 7 3), .ball 3 (.zero {0,1,5} 3 2), .ball 2 (.succ (.zero {0} 1 1) {0,1,3,5} 4 2)})) (.packing {.ball 0 (.succ (.zero {2,3} 3 2) ∅ 7 3), .ball 2 (.succ (.zero {0,4} 3 2) ∅ 7 3), .ball 4 (.succ (.zero {0,2} 3 2) ∅ 7 3)}))))

theorem certificate_10_part_11_checked : certificate_10_part_11.Valid 6 3 6 certificate_10_q certificate_10_part_11_E 3 1 certificate_10_part_11_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_12_checked⟩⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_13_checked⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩⟩⟩⟩

noncomputable def certificate_10_part_9 : FiniteCertificate := .forbid 2 3 1 (.system [[0],[1,2,6,3,4,5]]) (.forbid 0 4 0 (.forbid 0 1 2 (.cycle [0,4,3,2,1,7,6]) (.forbid 0 1 3 (.cycle [0,4,5,1,8,7,6]) (.forbid 0 3 4 (.cycle [0,4,3,9,8,7,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3} 4 2) ∅ 7 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,3} 4 2), .singleton 2, .ball 3 (.zero ∅ 1 1)})))) (.forbid 2 3 2 (.system [[0],[1,2,6,7,3,4,5]]) (.forbid 2 4 3 (.system [[0],[1,2,6,7,8,4,5]]) (.forbid 2 4 4 (.cycle [2,3,4,9,8,7,6]) (.forbid 3 4 2 (.system [[0],[1,2,3,6,7,4,5]]) (.forbid 1 3 0 (.forbid 2 4 1 (.cycle [2,3,1,0,5,4,6]) (.packing {.ball 0 (.succ (.zero ∅ 1 1) {2,3,4} 4 2), .ball 2 (.succ (.zero ∅ 1 1) {0,3,4} 4 2), .ball 4 (.succ (.zero ∅ 1 1) {0,2,3} 4 2), .singleton 3})) (.forbid 2 4 0 (certificate_10_part_10) (certificate_10_part_11))))))))

theorem certificate_10_part_9_checked : certificate_10_part_9.Valid 6 3 6 certificate_10_q certificate_10_part_9_E 3 1 certificate_10_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, certificate_10_part_10_checked, certificate_10_part_11_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_10_part_6 : FiniteCertificate := .forbid 0 1 5 (.system [[0,6,7,8,9,10,1],[5]]) (.forbid 1 2 1 (.system [[0],[1,6,2,3,4,5]]) (.forbid 1 2 2 (.system [[0],[1,6,7,2,3,4,5]]) (.forbid 1 4 3 (.system [[0],[1,6,7,8,4,5]]) (.forbid 0 3 0 (.forbid 0 1 2 (.cycle [0,3,4,5,1,7,6]) (.forbid 0 1 3 (.cycle [0,3,2,1,8,7,6]) (.forbid 1 4 1 (.cycle [1,2,3,0,5,4,6]) (certificate_10_part_7)))) (.forbid 1 3 1 (.forbid 0 6 1 (.cycle [0,1,5,4,3,6,7]) (.forbid 0 6 2 (.cycle [0,1,2,3,6,8,7]) (certificate_10_part_8))) (.forbid 1 3 2 (.system [[0],[1,6,7,3,4,5]]) (.forbid 1 3 3 (.system [[0],[1,6,7,8,3,4,5]]) (certificate_10_part_9))))))))

theorem certificate_10_part_6_checked : certificate_10_part_6.Valid 6 3 6 certificate_10_q certificate_10_part_6_E 3 1 certificate_10_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_7_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_8_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_9_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_10_part_3 : FiniteCertificate := .forbid 3 4 1 (.system [[0],[1,2,3,6,4,5]]) (.forbid 3 5 1 (.forbid 0 4 0 (.cycle [0,1,2,3,6,5,4]) (.forbid 0 6 1 (.cycle [0,1,5,4,3,6,7]) (.forbid 0 6 2 (.cycle [0,1,2,3,6,8,7]) (.forbid 0 6 3 (.cycle [0,1,5,6,9,8,7]) (.forbid 2 4 0 (.cycle [2,1,0,5,6,3,4]) (.forbid 2 4 1 (.cycle [2,1,5,6,3,4,7]) (certificate_10_part_4))))))) (.forbid 3 5 2 (.system [[0],[1,2,3,6,7,5]]) (.forbid 3 5 3 (.system [[0],[1,2,3,6,7,8,5]]) (.forbid 4 5 1 (.system [[0],[1,2,3,4,6,5]]) (.forbid 4 5 2 (.system [[0],[1,2,3,4,6,7,5]]) (.forbid 0 2 0 (.forbid 0 3 4 (.cycle [0,2,3,9,8,7,6]) (certificate_10_part_5)) (.forbid 0 1 4 (.system [[0,6,7,8,9,1],[5]]) (certificate_10_part_6))))))))

theorem certificate_10_part_3_checked : certificate_10_part_3.Valid 6 3 6 certificate_10_q certificate_10_part_3_E 3 1 certificate_10_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_4_checked⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_5_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_10_part_1 : FiniteCertificate := .forbid 0 4 4 (.system [[0,6,7,8,9,4,5],[1]]) (.forbid 0 5 1 (.system [[0,6,5,4,3,2,1]]) (.forbid 2 4 2 (.system [[0],[1,2,6,7,4,5]]) (.forbid 0 3 1 (.forbid 0 2 0 (.cycle [0,6,3,4,5,1,2]) (.forbid 0 4 0 (.cycle [0,6,3,2,1,5,4]) (.forbid 1 4 0 (.cycle [1,2,3,6,0,5,4]) (.forbid 2 4 0 (.cycle [2,1,5,0,6,3,4]) (certificate_10_part_2))))) (.forbid 0 3 2 (.system [[0,6,7,3,2,1],[5]]) (.forbid 0 3 3 (.system [[0,6,7,8,3,2,1],[5]]) (.forbid 0 5 4 (.system [[0,6,7,8,9,5],[1]]) (.forbid 0 5 5 (.system [[0,6,7,8,9,10,5],[1]]) (certificate_10_part_3))))))))

theorem certificate_10_part_1_checked : certificate_10_part_1.Valid 6 3 6 certificate_10_q certificate_10_part_1_E 3 1 certificate_10_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_2_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_10 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1,2,3,4,5]]) (.forbid 0 2 1 (.system [[0,6,2,3,4,5],[1]]) (.forbid 0 2 2 (.system [[0,6,7,2,3,4,5],[1]]) (.forbid 0 2 3 (.system [[0,6,7,8,2,1],[5]]) (.forbid 0 2 4 (.system [[0,6,7,8,9,2,1],[5]]) (.forbid 0 4 1 (.system [[0,6,4,3,2,1],[5]]) (.forbid 0 4 2 (.system [[0,6,7,4,3,2,1],[5]]) (.forbid 0 4 3 (.system [[0,6,7,8,4,5],[1]]) (certificate_10_part_1))))))))

theorem certificate_10_checked : certificate_10.Valid 6 3 6 certificate_10_q certificate_10_E 3 1 certificate_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_10_valid : certificate_10.Valid 6 3 (patternOrder [[],[3]]) (patternClique [[],[3]]) (patternEdges [[],[3]]) (patternAmount [[],[3]]) (patternEdgeCount [[],[3]]) [] := certificate_10_checked

noncomputable def certificate_11_q : Finset ℕ := ([0,2,4] : List ℕ).toFinset

noncomputable def certificate_11_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(0,2),(0,4),(2,4)]

noncomputable def certificate_11_E : List (ℕ × ℕ) := certificate_11_edges

noncomputable def certificate_11_M : ForbiddenMatrix := []

noncomputable def certificate_11_part_1_E : List (ℕ × ℕ) := certificate_11_E

noncomputable def certificate_11_part_1_M : ForbiddenMatrix := ((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,5) :: (((1,2,4) :: (((1,2,3) :: (((1,2,2) :: (((1,2,1) :: (certificate_11_M))))))))))))))))

noncomputable def certificate_11_part_1 : FiniteCertificate := .forbid 1 3 4 (.cycle [1,2,3,8,7,6,5]) (.forbid 2 3 1 (.system [[0],[2,5,3,4]]) (.forbid 2 3 2 (.system [[0],[2,5,6,3,4]]) (.forbid 2 3 3 (.system [[0],[2,5,6,7,3,4]]) (.forbid 2 3 4 (.system [[0],[2,5,6,7,8,3,4]]) (.forbid 2 3 5 (.cycle [2,3,9,8,7,6,5]) (.packing {.ball 1 (.succ (.zero ∅ 2 1) {2,3} 4 2), .ball 2 (.succ (.succ (.zero ∅ 2 1) {1,3} 4 2) ∅ 8 3), .ball 3 (.succ (.zero ∅ 2 1) {1,2} 4 2)}))))))

theorem certificate_11_part_1_checked : certificate_11_part_1.Valid 6 3 5 certificate_11_q certificate_11_part_1_E 2 2 certificate_11_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

noncomputable def certificate_11 : FiniteCertificate := .forbid 1 2 1 (.system [[0,1,5,2],[4]]) (.forbid 1 2 2 (.system [[0,1,5,6,2],[4]]) (.forbid 1 2 3 (.system [[0,1,5,6,7,2],[4]]) (.forbid 1 2 4 (.system [[0,1,5,6,7,8,2],[4]]) (.forbid 1 2 5 (.cycle [1,2,9,8,7,6,5]) (.forbid 1 3 1 (.system [[0,1,5,3,2],[4]]) (.forbid 1 3 2 (.system [[0,1,5,6,3,2],[4]]) (.forbid 1 3 3 (.system [[0,1,5,6,7,3,2],[4]]) (certificate_11_part_1))))))))

theorem certificate_11_checked : certificate_11.Valid 6 3 5 certificate_11_q certificate_11_E 2 2 certificate_11_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_11_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_11_valid : certificate_11.Valid 6 3 (patternOrder [[1,1]]) (patternClique [[1,1]]) (patternEdges [[1,1]]) (patternAmount [[1,1]]) (patternEdgeCount [[1,1]]) [] := certificate_11_checked

noncomputable def certificate_12_q : Finset ℕ := ([0,2,5] : List ℕ).toFinset

noncomputable def certificate_12_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(0,2),(0,5),(2,5)]

noncomputable def certificate_12_E : List (ℕ × ℕ) := certificate_12_edges

noncomputable def certificate_12_M : ForbiddenMatrix := []

noncomputable def certificate_12_part_1_E : List (ℕ × ℕ) := certificate_12_E

noncomputable def certificate_12_part_1_M : ForbiddenMatrix := ((0,5,2) :: (((0,5,1) :: (((0,3,1) :: (((0,1,5) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_12_M))))))))))))))))

noncomputable def certificate_12_part_2_E : List (ℕ × ℕ) := certificate_12_part_1_E

noncomputable def certificate_12_part_2_M : ForbiddenMatrix := ((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,5,1) :: (((1,2,1) :: (((0,5,5) :: (((0,5,4) :: (((0,5,3) :: (certificate_12_part_1_M))))))))))))))))

noncomputable def certificate_12_part_2 : FiniteCertificate := .forbid 4 5 1 (.system [[0],[2,3,4,6,5]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,5} 4 2) ∅ 7 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,5} 4 2), .ball 5 (.succ (.zero ∅ 1 1) {0,1,4} 4 2)})

theorem certificate_12_part_2_checked : certificate_12_part_2.Valid 6 3 6 certificate_12_q certificate_12_part_2_E 3 2 certificate_12_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

noncomputable def certificate_12_part_1 : FiniteCertificate := .forbid 0 5 3 (.system [[0,6,7,8,5],[2]]) (.forbid 0 5 4 (.system [[0,6,7,8,9,5],[2]]) (.forbid 0 5 5 (.system [[0,6,7,8,9,10,5],[2]]) (.forbid 1 2 1 (.system [[0,1,6,2,3,4,5]]) (.forbid 1 5 1 (.system [[0,1,6,5,4,3,2]]) (.forbid 1 5 2 (.system [[0,1,6,7,5],[2]]) (.forbid 1 5 3 (.system [[0,1,6,7,8,5],[2]]) (.forbid 1 5 4 (.system [[0,1,6,7,8,9,5],[2]]) (certificate_12_part_2))))))))

theorem certificate_12_part_1_checked : certificate_12_part_1.Valid 6 3 6 certificate_12_q certificate_12_part_1_E 3 2 certificate_12_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_12_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_12 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1,2,3,4,5]]) (.forbid 0 1 2 (.system [[0,6,7,1,2],[5]]) (.forbid 0 1 3 (.system [[0,6,7,8,1,2],[5]]) (.forbid 0 1 4 (.system [[0,6,7,8,9,1,2],[5]]) (.forbid 0 1 5 (.cycle [0,1,10,9,8,7,6]) (.forbid 0 3 1 (.system [[0,6,3,4,5],[2]]) (.forbid 0 5 1 (.cycle [0,1,2,3,4,5,6]) (.forbid 0 5 2 (.system [[0,6,7,5,4,3,2]]) (certificate_12_part_1))))))))

theorem certificate_12_checked : certificate_12.Valid 6 3 6 certificate_12_q certificate_12_E 3 2 certificate_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_12_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_12_valid : certificate_12.Valid 6 3 (patternOrder [[1,2]]) (patternClique [[1,2]]) (patternEdges [[1,2]]) (patternAmount [[1,2]]) (patternEdgeCount [[1,2]]) [] := certificate_12_checked

noncomputable def certificate_13_q : Finset ℕ := ([0,1,2,3] : List ℕ).toFinset
noncomputable def certificate_13_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

noncomputable def certificate_13 : FiniteCertificate := .forbid 0 1 1 (.system [[0,4,1],[2],[3]]) (.forbid 0 1 2 (.system [[0,4,5,1],[2],[3]]) (.forbid 0 1 3 (.system [[0,4,5,6,1],[2],[3]]) (.forbid 0 1 4 (.system [[0,4,5,6,7,1],[2],[3]]) (.forbid 0 1 5 (.system [[0,4,5,6,7,8,1],[2],[3]]) (.forbid 0 2 1 (.system [[0,4,2],[1],[3]]) (.forbid 0 2 2 (.system [[0,4,5,2],[1],[3]]) (.forbid 0 2 3 (.system [[0,4,5,6,2],[1],[3]]) (.forbid 0 2 4 (.system [[0,4,5,6,7,2],[1],[3]]) (.forbid 0 2 5 (.system [[0,4,5,6,7,8,2],[1],[3]]) (.forbid 1 2 1 (.system [[0],[1,4,2],[3]]) (.forbid 1 2 2 (.system [[0],[1,4,5,2],[3]]) (.forbid 1 2 3 (.system [[0],[1,4,5,6,2],[3]]) (.forbid 1 2 4 (.system [[0],[1,4,5,6,7,2],[3]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 3 1) {1,2} 5 2) ∅ 9 3), .ball 1 (.succ (.zero ∅ 3 1) {0,2} 5 2), .ball 2 (.succ (.zero ∅ 3 1) {0,1} 5 2)}))))))))))))))

theorem certificate_13_checked : certificate_13.Valid 6 4 4 certificate_13_q certificate_13_edges 0 0 [] := by decide +kernel
theorem certificate_13_valid : certificate_13.Valid 6 4 (patternOrder [[],[],[],[]]) (patternClique [[],[],[],[]]) (patternEdges [[],[],[],[]]) (patternAmount [[],[],[],[]]) (patternEdgeCount [[],[],[],[]]) [] := certificate_13_checked

noncomputable def certificate_14_q : Finset ℕ := ([0,1,2,4] : List ℕ).toFinset
noncomputable def certificate_14_edges : List (ℕ × ℕ) := [(2,3),(3,4),(0,1),(0,2),(0,4),(1,2),(1,4),(2,4)]

noncomputable def certificate_14 : FiniteCertificate := .forbid 0 1 1 (.system [[0,5,1],[2,3,4]]) (.forbid 0 1 2 (.system [[0,5,6,1],[2],[4]]) (.forbid 0 1 3 (.system [[0,5,6,7,1],[2],[4]]) (.forbid 0 1 4 (.system [[0,5,6,7,8,1],[2],[4]]) (.forbid 0 1 5 (.system [[0,5,6,7,8,9,1],[2],[4]]) (.forbid 0 2 1 (.system [[0,5,2,3,4],[1]]) (.forbid 0 2 2 (.system [[0,5,6,2],[1],[4]]) (.forbid 0 2 3 (.system [[0,5,6,7,2],[1],[4]]) (.forbid 0 2 4 (.system [[0,5,6,7,8,2],[1],[4]]) (.forbid 0 2 5 (.system [[0,5,6,7,8,9,2],[1],[4]]) (.forbid 0 3 1 (.system [[0,5,3,2],[1],[4]]) (.forbid 1 2 1 (.system [[0],[1,5,2,3,4]]) (.forbid 1 2 2 (.system [[0],[1,5,6,2],[4]]) (.forbid 1 2 3 (.system [[0],[1,5,6,7,2],[4]]) (.forbid 1 2 4 (.system [[0],[1,5,6,7,8,2],[4]]) (.forbid 1 3 1 (.system [[0],[1,5,3,2],[4]]) (.forbid 2 3 1 (.system [[0],[1],[2,5,3,4]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,2,3} 5 2) {1} 9 3), .ball 1 (.succ (.zero ∅ 2 1) {0,2,3} 5 2), .ball 2 (.succ (.zero ∅ 2 1) {0,1,3} 5 2)})))))))))))))))))

theorem certificate_14_checked : certificate_14.Valid 6 4 5 certificate_14_q certificate_14_edges 1 1 [] := by decide +kernel
theorem certificate_14_valid : certificate_14.Valid 6 4 (patternOrder [[],[],[1]]) (patternClique [[],[],[1]]) (patternEdges [[],[],[1]]) (patternAmount [[],[],[1]]) (patternEdgeCount [[],[],[1]]) [] := certificate_14_checked

noncomputable def certificate_15_q : Finset ℕ := ([0,1,2,5] : List ℕ).toFinset

noncomputable def certificate_15_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(0,1),(0,2),(0,5),(1,2),(1,5),(2,5)]

noncomputable def certificate_15_E : List (ℕ × ℕ) := certificate_15_edges

noncomputable def certificate_15_M : ForbiddenMatrix := []

noncomputable def certificate_15_part_1_E : List (ℕ × ℕ) := certificate_15_E

noncomputable def certificate_15_part_1_M : ForbiddenMatrix := ((0,2,4) :: (((0,2,3) :: (((0,2,2) :: (((0,1,5) :: (((0,1,4) :: (((0,1,3) :: (((0,2,1) :: (((0,1,1) :: (certificate_15_M))))))))))))))))

noncomputable def certificate_15_part_2_E : List (ℕ × ℕ) := certificate_15_part_1_E

noncomputable def certificate_15_part_2_M : ForbiddenMatrix := ((1,3,1) :: (((1,2,4) :: (((1,2,3) :: (((1,2,2) :: (((1,2,1) :: (((0,4,1) :: (((0,3,1) :: (((0,2,5) :: (certificate_15_part_1_M))))))))))))))))

noncomputable def certificate_15_part_3_E : List (ℕ × ℕ) := (augmentedEdges 6 (certificate_15_part_2_E) 0 4 0)

noncomputable def certificate_15_part_3_M : ForbiddenMatrix := ((0,1,2) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,0) :: (((2,3,1) :: (((1,4,1) :: (certificate_15_part_2_M))))))))))))))

noncomputable def certificate_15_part_3 : FiniteCertificate := .forbid 2 5 1 (.cycle [2,3,4,0,1,5,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,4} 5 2) {1,2} 9 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,3,4} 5 2), .ball 2 (.succ (.zero ∅ 1 1) {0,1,3,5} 5 2)})

theorem certificate_15_part_3_checked : certificate_15_part_3.Valid 6 4 6 certificate_15_q certificate_15_part_3_E 2 1 certificate_15_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

noncomputable def certificate_15_part_4_E : List (ℕ × ℕ) := certificate_15_part_2_E

noncomputable def certificate_15_part_4_M : ForbiddenMatrix := ((0,4,2) :: (((0,4,0) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,0) :: (((2,3,1) :: (((1,4,1) :: (certificate_15_part_2_M))))))))))))))))

noncomputable def certificate_15_part_5_E : List (ℕ × ℕ) := certificate_15_part_4_E

noncomputable def certificate_15_part_5_M : ForbiddenMatrix := ((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((1,4,0) :: (((1,3,0) :: (((0,4,4) :: (((0,4,3) :: (certificate_15_part_4_M))))))))))))))))

noncomputable def certificate_15_part_6_E : List (ℕ × ℕ) := (augmentedEdges 6 (certificate_15_part_5_E) 2 4 0)

noncomputable def certificate_15_part_6_M : ForbiddenMatrix := ((0,1,2) :: (((4,5,1) :: (((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,5,1) :: (((0,5,5) :: (certificate_15_part_5_M))))))))))))))

noncomputable def certificate_15_part_6 : FiniteCertificate := .forbid 3 5 1 (.cycle [3,4,2,0,1,5,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,5} 5 2) {1,5} 9 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,3,5} 5 2), .ball 5 (.succ (.zero ∅ 1 1) {0,1,3,4} 5 2)})

theorem certificate_15_part_6_checked : certificate_15_part_6.Valid 6 4 6 certificate_15_q certificate_15_part_6_E 2 1 certificate_15_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

noncomputable def certificate_15_part_7_E : List (ℕ × ℕ) := certificate_15_part_5_E

noncomputable def certificate_15_part_7_M : ForbiddenMatrix := ((3,4,1) :: (((2,4,0) :: (((4,5,1) :: (((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,5,1) :: (((0,5,5) :: (certificate_15_part_5_M))))))))))))))))

noncomputable def certificate_15_part_7 : FiniteCertificate := .forbid 3 4 2 (.system [[0],[1],[2,3,6,7,4,5]]) (.forbid 3 5 0 (.forbid 0 1 2 (.cycle [0,2,3,5,1,7,6]) (.forbid 2 4 1 (.cycle [2,0,1,5,3,4,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,4} 5 2) {1,2} 9 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,3,4} 5 2), .ball 2 (.succ (.zero ∅ 1 1) {0,1,3,4} 5 2)}))) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,4} 5 2) {3,4} 9 3), .ball 3 (.zero {0,1,5} 4 2), .ball 4 (.zero {0,1,2} 4 2)}))

theorem certificate_15_part_7_checked : certificate_15_part_7.Valid 6 4 6 certificate_15_q certificate_15_part_7_E 2 1 certificate_15_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, by decide +kernel⟩⟩

noncomputable def certificate_15_part_5 : FiniteCertificate := .forbid 0 5 5 (.system [[0,6,7,8,9,10,5],[1],[2]]) (.forbid 1 5 1 (.system [[0],[1,6,5,4,3,2]]) (.forbid 1 5 2 (.system [[0],[1,6,7,5,4,3,2]]) (.forbid 1 5 3 (.system [[0],[1,6,7,8,5],[2]]) (.forbid 1 5 4 (.system [[0],[1,6,7,8,9,5],[2]]) (.forbid 4 5 1 (.system [[0],[1],[2,3,4,6,5]]) (.forbid 2 4 0 (.forbid 0 1 2 (.cycle [0,2,4,5,1,7,6]) (certificate_15_part_6)) (.forbid 3 4 1 (.system [[0],[1],[2,3,6,4,5]]) (certificate_15_part_7))))))))

theorem certificate_15_part_5_checked : certificate_15_part_5.Valid 6 4 6 certificate_15_q certificate_15_part_5_E 2 1 certificate_15_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_6_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_15_part_4 : FiniteCertificate := .forbid 0 4 3 (.system [[0,6,7,8,4,3,2],[1],[5]]) (.forbid 0 4 4 (.system [[0,6,7,8,9,4,5],[1],[2]]) (.forbid 1 3 0 (.forbid 0 1 2 (.cycle [0,5,2,3,1,7,6]) (.forbid 2 4 1 (.cycle [2,0,5,1,3,4,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,4} 5 2) {1,2} 9 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,3,4} 5 2), .ball 2 (.succ (.zero ∅ 1 1) {0,1,3,4} 5 2)}))) (.forbid 1 4 0 (.forbid 0 1 2 (.cycle [0,2,3,4,1,7,6]) (.forbid 2 5 1 (.cycle [2,3,4,1,0,5,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,4} 5 2) {1,2} 9 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,3,4} 5 2), .ball 2 (.succ (.zero ∅ 1 1) {0,1,3,5} 5 2)}))) (.forbid 0 5 1 (.system [[0,6,5,4,3,2],[1]]) (.forbid 0 5 2 (.system [[0,6,7,5,4,3,2],[1]]) (.forbid 0 5 3 (.system [[0,6,7,8,5],[1],[2]]) (.forbid 0 5 4 (.system [[0,6,7,8,9,5],[1],[2]]) (certificate_15_part_5))))))))

theorem certificate_15_part_4_checked : certificate_15_part_4.Valid 6 4 6 certificate_15_q certificate_15_part_4_E 2 1 certificate_15_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_15_part_2 : FiniteCertificate := .forbid 1 4 1 (.system [[0],[1,6,4,3,2],[5]]) (.forbid 2 3 1 (.system [[0],[1],[2,6,3,4,5]]) (.forbid 0 3 0 (.forbid 0 1 2 (.cycle [0,3,2,5,1,7,6]) (.forbid 2 4 1 (.cycle [2,1,5,0,3,4,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,4} 5 2) {1,2} 9 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,3,4} 5 2), .ball 2 (.succ (.zero ∅ 1 1) {0,1,3,4} 5 2)}))) (.forbid 0 3 2 (.system [[0,6,7,3,2],[1],[5]]) (.forbid 0 3 3 (.system [[0,6,7,8,3,2],[1],[5]]) (.forbid 0 3 4 (.system [[0,6,7,8,9,3,2],[1],[5]]) (.forbid 0 4 0 (.forbid 0 1 2 (.cycle [0,4,3,2,1,7,6]) (certificate_15_part_3)) (.forbid 0 4 2 (.system [[0,6,7,4,3,2],[1],[5]]) (certificate_15_part_4))))))))

theorem certificate_15_part_2_checked : certificate_15_part_2.Valid 6 4 6 certificate_15_q certificate_15_part_2_E 2 1 certificate_15_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_3_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_15_part_1 : FiniteCertificate := .forbid 0 2 5 (.system [[0,6,7,8,9,10,2],[1],[5]]) (.forbid 0 3 1 (.system [[0,6,3,4,5],[1],[2]]) (.forbid 0 4 1 (.system [[0,6,4,3,2],[1],[5]]) (.forbid 1 2 1 (.system [[0],[1,6,2,3,4,5]]) (.forbid 1 2 2 (.system [[0],[1,6,7,2,3,4,5]]) (.forbid 1 2 3 (.system [[0],[1,6,7,8,2],[5]]) (.forbid 1 2 4 (.system [[0],[1,6,7,8,9,2],[5]]) (.forbid 1 3 1 (.system [[0],[1,6,3,4,5],[2]]) (certificate_15_part_2))))))))

theorem certificate_15_part_1_checked : certificate_15_part_1.Valid 6 4 6 certificate_15_q certificate_15_part_1_E 2 1 certificate_15_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_15 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1],[2,3,4,5]]) (.forbid 0 2 1 (.system [[0,6,2,3,4,5],[1]]) (.forbid 0 1 3 (.system [[0,6,7,8,1],[2],[5]]) (.forbid 0 1 4 (.system [[0,6,7,8,9,1],[2],[5]]) (.forbid 0 1 5 (.system [[0,6,7,8,9,10,1],[2],[5]]) (.forbid 0 2 2 (.system [[0,6,7,2,3,4,5],[1]]) (.forbid 0 2 3 (.system [[0,6,7,8,2],[1],[5]]) (.forbid 0 2 4 (.system [[0,6,7,8,9,2],[1],[5]]) (certificate_15_part_1))))))))

theorem certificate_15_checked : certificate_15.Valid 6 4 6 certificate_15_q certificate_15_E 2 1 certificate_15_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_15_valid : certificate_15.Valid 6 4 (patternOrder [[],[],[2]]) (patternClique [[],[],[2]]) (patternEdges [[],[],[2]]) (patternAmount [[],[],[2]]) (patternEdgeCount [[],[],[2]]) [] := certificate_15_checked

noncomputable def certificate_16_q : Finset ℕ := ([0,1,3,5] : List ℕ).toFinset

noncomputable def certificate_16_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(0,1),(0,3),(0,5),(1,3),(1,5),(3,5)]

noncomputable def certificate_16_E : List (ℕ × ℕ) := certificate_16_edges

noncomputable def certificate_16_M : ForbiddenMatrix := []

noncomputable def certificate_16_part_1_E : List (ℕ × ℕ) := certificate_16_E

noncomputable def certificate_16_part_1_M : ForbiddenMatrix := ((0,4,2) :: (((0,4,1) :: (((0,2,4) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,2) :: (((0,1,1) :: (certificate_16_M))))))))))))))))

noncomputable def certificate_16_part_2_E : List (ℕ × ℕ) := certificate_16_part_1_E

noncomputable def certificate_16_part_2_M : ForbiddenMatrix := ((2,3,1) :: (((1,4,2) :: (((1,4,1) :: (((1,2,2) :: (((1,2,1) :: (((0,5,1) :: (((0,4,4) :: (((0,4,3) :: (certificate_16_part_1_M))))))))))))))))

noncomputable def certificate_16_part_2 : FiniteCertificate := .forbid 2 4 1 (.system [[0],[1,2,6,4,3],[5]]) (.forbid 2 4 2 (.system [[0],[1,2,6,7,4,3],[5]]) (.forbid 2 4 3 (.system [[0],[1,2,6,7,8,4,3],[5]]) (.forbid 2 4 4 (.cycle [2,3,4,9,8,7,6]) (.forbid 3 4 1 (.system [[0],[1],[3,6,4,5]]) (.packing {.ball 0 (.succ (.zero ∅ 1 1) {1,2,4,5} 5 2), .ball 2 (.succ (.zero ∅ 1 1) {0,1,3,4} 5 2), .ball 4 (.succ (.zero ∅ 1 1) {0,1,2,3} 5 2), .singleton 1})))))

theorem certificate_16_part_2_checked : certificate_16_part_2.Valid 6 4 6 certificate_16_q certificate_16_part_2_E 2 2 certificate_16_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

noncomputable def certificate_16_part_1 : FiniteCertificate := .forbid 0 4 3 (.system [[0,6,7,8,4,3],[1],[5]]) (.forbid 0 4 4 (.system [[0,6,7,8,9,4,3],[1],[5]]) (.forbid 0 5 1 (.system [[0,6,5,4,3,2,1]]) (.forbid 1 2 1 (.system [[0],[1,6,2,3],[5]]) (.forbid 1 2 2 (.system [[0],[1,6,7,2,3],[5]]) (.forbid 1 4 1 (.system [[0],[1,6,4,3],[5]]) (.forbid 1 4 2 (.system [[0],[1,6,7,4,3],[5]]) (.forbid 2 3 1 (.system [[0],[1,2,6,3],[5]]) (certificate_16_part_2))))))))

theorem certificate_16_part_1_checked : certificate_16_part_1.Valid 6 4 6 certificate_16_q certificate_16_part_1_E 2 2 certificate_16_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_16_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_16 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1,2,3,4,5]]) (.forbid 0 1 2 (.system [[0,6,7,1],[3],[5]]) (.forbid 0 2 1 (.system [[0,6,2,1],[3],[5]]) (.forbid 0 2 2 (.system [[0,6,7,2,1],[3],[5]]) (.forbid 0 2 3 (.system [[0,6,7,8,2,1],[3],[5]]) (.forbid 0 2 4 (.system [[0,6,7,8,9,2,1],[3],[5]]) (.forbid 0 4 1 (.system [[0,6,4,3],[1],[5]]) (.forbid 0 4 2 (.system [[0,6,7,4,3],[1],[5]]) (certificate_16_part_1))))))))

theorem certificate_16_checked : certificate_16.Valid 6 4 6 certificate_16_q certificate_16_E 2 2 certificate_16_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_16_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_16_valid : certificate_16.Valid 6 4 (patternOrder [[],[1,1]]) (patternClique [[],[1,1]]) (patternEdges [[],[1,1]]) (patternAmount [[],[1,1]]) (patternEdgeCount [[],[1,1]]) [] := certificate_16_checked

noncomputable def certificate_17_q : Finset ℕ := ([0,2,3,5] : List ℕ).toFinset
noncomputable def certificate_17_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(0,2),(0,3),(0,5),(2,3),(2,5),(3,5)]

noncomputable def certificate_17 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1,2],[3],[5]]) (.forbid 0 1 2 (.system [[0,6,7,1,2],[3],[5]]) (.forbid 0 1 3 (.system [[0,6,7,8,1,2],[3],[5]]) (.forbid 0 3 1 (.system [[2,1,0,6,3,4,5]]) (.forbid 0 3 2 (.system [[0,6,7,3],[2],[5]]) (.forbid 0 3 3 (.system [[0,6,7,8,3],[2],[5]]) (.forbid 0 3 4 (.system [[0,6,7,8,9,3],[2],[5]]) (.forbid 0 3 5 (.system [[0,6,7,8,9,10,3],[2],[5]]) (.forbid 0 4 1 (.system [[0,6,4,3],[2],[5]]) (.forbid 0 4 2 (.system [[0,6,7,4,3],[2],[5]]) (.forbid 0 4 3 (.system [[0,6,7,8,4,3],[2],[5]]) (.forbid 0 4 4 (.system [[0,6,7,8,9,4,3],[2],[5]]) (.forbid 0 5 1 (.system [[2,1,0,6,5,4,3]]) (.forbid 1 3 1 (.system [[0,1,6,3],[2],[5]]) (.forbid 1 3 2 (.system [[0,1,6,7,3],[2],[5]]) (.forbid 1 4 1 (.system [[0,1,6,4,3],[2],[5]]) (.forbid 2 3 1 (.system [[0,1,2,6,3,4,5]]) (.forbid 3 4 1 (.system [[0],[2],[3,6,4,5]]) (.forbid 3 4 2 (.system [[0],[2],[3,6,7,4,5]]) (.forbid 3 4 3 (.system [[0],[2],[3,6,7,8,4,5]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4,5} 5 2) {1,3} 9 3), .ball 3 (.succ (.zero ∅ 1 1) {0,1,2,4} 5 2), .singleton 1, .ball 4 (.zero ∅ 1 1)}))))))))))))))))))))

theorem certificate_17_checked : certificate_17.Valid 6 4 6 certificate_17_q certificate_17_edges 2 2 [] := by decide +kernel
theorem certificate_17_valid : certificate_17.Valid 6 4 (patternOrder [[1],[1]]) (patternClique [[1],[1]]) (patternEdges [[1],[1]]) (patternAmount [[1],[1]]) (patternEdgeCount [[1],[1]]) [] := certificate_17_checked

noncomputable def certificate_18_q : Finset ℕ := ([0,1,2,3,4] : List ℕ).toFinset
noncomputable def certificate_18_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

noncomputable def certificate_18_part_0 : FiniteCertificate := .forbid 2 4 1 (.system [[0],[1],[2,5,4],[3]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,2,3,4} 6 2) {1,2,3} 11 3), .ball 1 (.succ (.zero ∅ 2 1) {0,2,3,4} 6 2), .ball 2 (.succ (.zero ∅ 2 1) {0,1,3,4} 6 2)})

noncomputable def certificate_18 : FiniteCertificate := .forbid 0 1 1 (.system [[0,5,1],[2],[3],[4]]) (.forbid 0 1 2 (.system [[0,5,6,1],[2],[3],[4]]) (.forbid 0 1 3 (.system [[0,5,6,7,1],[2],[3],[4]]) (.forbid 0 1 4 (.system [[0,5,6,7,8,1],[2],[3],[4]]) (.forbid 0 1 5 (.system [[0,5,6,7,8,9,1],[2],[3],[4]]) (.forbid 0 2 1 (.system [[0,5,2],[1],[3],[4]]) (.forbid 0 2 2 (.system [[0,5,6,2],[1],[3],[4]]) (.forbid 0 2 3 (.system [[0,5,6,7,2],[1],[3],[4]]) (.forbid 0 2 4 (.system [[0,5,6,7,8,2],[1],[3],[4]]) (.forbid 0 2 5 (.system [[0,5,6,7,8,9,2],[1],[3],[4]]) (.forbid 0 3 1 (.system [[0,5,3],[1],[2],[4]]) (.forbid 0 3 2 (.system [[0,5,6,3],[1],[2],[4]]) (.forbid 0 4 1 (.system [[0,5,4],[1],[2],[3]]) (.forbid 1 2 1 (.system [[0],[1,5,2],[3],[4]]) (.forbid 1 2 2 (.system [[0],[1,5,6,2],[3],[4]]) (.forbid 1 2 3 (.system [[0],[1,5,6,7,2],[3],[4]]) (.forbid 1 2 4 (.system [[0],[1,5,6,7,8,2],[3],[4]]) (.forbid 1 3 1 (.system [[0],[1,5,3],[2],[4]]) (.forbid 1 4 1 (.system [[0],[1,5,4],[2],[3]]) (.forbid 2 3 1 (.system [[0],[1],[2,5,3],[4]]) (certificate_18_part_0))))))))))))))))))))

theorem certificate_18_checked : certificate_18.Valid 6 5 5 certificate_18_q certificate_18_edges 0 0 [] := by decide +kernel
theorem certificate_18_valid : certificate_18.Valid 6 5 (patternOrder [[],[],[],[],[]]) (patternClique [[],[],[],[],[]]) (patternEdges [[],[],[],[],[]]) (patternAmount [[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[]]) [] := certificate_18_checked

noncomputable def certificate_19_q : Finset ℕ := ([0,1,2,3,5] : List ℕ).toFinset
noncomputable def certificate_19_edges : List (ℕ × ℕ) := [(3,4),(4,5),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,5),(2,3),(2,5),(3,5)]

noncomputable def certificate_19_part_0 : FiniteCertificate := .forbid 1 4 1 (.system [[0],[1,6,4,3],[2],[5]]) (.forbid 1 5 1 (.system [[0],[1,6,5,4,3],[2]]) (.forbid 2 3 1 (.system [[0],[1],[2,6,3,4,5]]) (.forbid 2 4 1 (.system [[0],[1],[2,6,4,3],[5]]) (.forbid 2 5 1 (.system [[0],[1],[2,6,5,4,3]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,4,5} 6 2) {1,2,3,4} 11 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,3,4,5} 6 2), .ball 2 (.succ (.zero ∅ 1 1) {0,1,3,4,5} 6 2)})))))

noncomputable def certificate_19 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1],[2],[3,4,5]]) (.forbid 0 1 2 (.system [[0,6,7,1],[2],[3],[5]]) (.forbid 0 1 3 (.system [[0,6,7,8,1],[2],[3],[5]]) (.forbid 0 1 4 (.system [[0,6,7,8,9,1],[2],[3],[5]]) (.forbid 0 1 5 (.system [[0,6,7,8,9,10,1],[2],[3],[5]]) (.forbid 0 2 1 (.system [[0,6,2],[1],[3,4,5]]) (.forbid 0 2 2 (.system [[0,6,7,2],[1],[3],[5]]) (.forbid 0 2 3 (.system [[0,6,7,8,2],[1],[3],[5]]) (.forbid 0 2 4 (.system [[0,6,7,8,9,2],[1],[3],[5]]) (.forbid 0 2 5 (.system [[0,6,7,8,9,10,2],[1],[3],[5]]) (.forbid 0 3 1 (.system [[0,6,3,4,5],[1],[2]]) (.forbid 0 3 2 (.system [[0,6,7,3],[1],[2],[5]]) (.forbid 0 4 1 (.system [[0,6,4,3],[1],[2],[5]]) (.forbid 0 4 2 (.system [[0,6,7,4,3],[1],[2],[5]]) (.forbid 0 5 1 (.system [[0,6,5,4,3],[1],[2]]) (.forbid 1 2 1 (.system [[0],[1,6,2],[3,4,5]]) (.forbid 1 2 2 (.system [[0],[1,6,7,2],[3],[5]]) (.forbid 1 2 3 (.system [[0],[1,6,7,8,2],[3],[5]]) (.forbid 1 2 4 (.system [[0],[1,6,7,8,9,2],[3],[5]]) (.forbid 1 3 1 (.system [[0],[1,6,3,4,5],[2]]) (certificate_19_part_0))))))))))))))))))))

theorem certificate_19_checked : certificate_19.Valid 6 5 6 certificate_19_q certificate_19_edges 1 1 [] := by decide +kernel
theorem certificate_19_valid : certificate_19.Valid 6 5 (patternOrder [[],[],[],[1]]) (patternClique [[],[],[],[1]]) (patternEdges [[],[],[],[1]]) (patternAmount [[],[],[],[1]]) (patternEdgeCount [[],[],[],[1]]) [] := certificate_19_checked

noncomputable def certificate_20_q : Finset ℕ := ([0,1,2,3,4,5] : List ℕ).toFinset
noncomputable def certificate_20_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

noncomputable def certificate_20_part_0 : FiniteCertificate := .forbid 1 3 1 (.system [[0],[1,6,3],[2],[4],[5]]) (.forbid 1 4 1 (.system [[0],[1,6,4],[2],[3],[5]]) (.forbid 1 5 1 (.system [[0],[1,6,5],[2],[3],[4]]) (.forbid 2 3 1 (.system [[0],[1],[2,6,3],[4],[5]]) (.forbid 2 3 2 (.system [[0],[1],[2,6,7,3],[4],[5]]) (.forbid 2 4 1 (.system [[0],[1],[2,6,4],[3],[5]]) (.forbid 2 4 2 (.system [[0],[1],[2,6,7,4],[3],[5]]) (.forbid 2 5 1 (.system [[0],[1],[2,6,5],[3],[4]]) (.forbid 2 5 2 (.system [[0],[1],[2,6,7,5],[3],[4]]) (.forbid 3 4 1 (.system [[0],[1],[2],[3,6,4],[5]]) (.forbid 3 4 2 (.system [[0],[1],[2],[3,6,7,4],[5]]) (.forbid 3 5 1 (.system [[0],[1],[2],[3,6,5],[4]]) (.forbid 3 5 2 (.system [[0],[1],[2],[3,6,7,5],[4]]) (.forbid 4 5 1 (.system [[0],[1],[2],[3],[4,6,5]]) (.forbid 4 5 2 (.system [[0],[1],[2],[3],[4,6,7,5]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,4,5} 6 1) {1,2,3,4,5} 6 2), .singleton 1, .ball 2 (.zero ∅ 1 1), .ball 3 (.zero ∅ 1 1), .ball 4 (.zero ∅ 1 1), .ball 5 (.zero ∅ 1 1)})))))))))))))))

noncomputable def certificate_20 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1],[2],[3],[4],[5]]) (.forbid 0 1 2 (.system [[0,6,7,1],[2],[3],[4],[5]]) (.forbid 0 1 3 (.system [[0,6,7,8,1],[2],[3],[4],[5]]) (.forbid 0 2 1 (.system [[0,6,2],[1],[3],[4],[5]]) (.forbid 0 2 2 (.system [[0,6,7,2],[1],[3],[4],[5]]) (.forbid 0 2 3 (.system [[0,6,7,8,2],[1],[3],[4],[5]]) (.forbid 0 2 4 (.system [[0,6,7,8,9,2],[1],[3],[4],[5]]) (.forbid 0 3 1 (.system [[0,6,3],[1],[2],[4],[5]]) (.forbid 0 3 2 (.system [[0,6,7,3],[1],[2],[4],[5]]) (.forbid 0 3 3 (.system [[0,6,7,8,3],[1],[2],[4],[5]]) (.forbid 0 3 4 (.system [[0,6,7,8,9,3],[1],[2],[4],[5]]) (.forbid 0 4 1 (.system [[0,6,4],[1],[2],[3],[5]]) (.forbid 0 4 2 (.system [[0,6,7,4],[1],[2],[3],[5]]) (.forbid 0 4 3 (.system [[0,6,7,8,4],[1],[2],[3],[5]]) (.forbid 0 4 4 (.system [[0,6,7,8,9,4],[1],[2],[3],[5]]) (.forbid 0 5 1 (.system [[0,6,5],[1],[2],[3],[4]]) (.forbid 0 5 2 (.system [[0,6,7,5],[1],[2],[3],[4]]) (.forbid 0 5 3 (.system [[0,6,7,8,5],[1],[2],[3],[4]]) (.forbid 0 5 4 (.system [[0,6,7,8,9,5],[1],[2],[3],[4]]) (.forbid 1 2 1 (.system [[0],[1,6,2],[3],[4],[5]]) (certificate_20_part_0))))))))))))))))))))

theorem certificate_20_checked : certificate_20.Valid 6 6 6 certificate_20_q certificate_20_edges 0 0 [] := by decide +kernel
theorem certificate_20_valid : certificate_20.Valid 6 6 (patternOrder [[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[]]) [] := certificate_20_checked

noncomputable def certificate_21_q : Finset ℕ := ([0,1,2] : List ℕ).toFinset
noncomputable def certificate_21_edges : List (ℕ × ℕ) := [(0,1),(0,2),(1,2)]

noncomputable def certificate_21 : FiniteCertificate := .forbid 0 1 1 (.system [[0,3,1],[2]]) (.forbid 0 1 2 (.system [[0,3,4,1],[2]]) (.forbid 0 1 3 (.system [[0,3,4,5,1],[2]]) (.forbid 0 1 4 (.system [[0,3,4,5,6,1],[2]]) (.forbid 0 2 1 (.system [[0,3,2],[1]]) (.forbid 0 2 2 (.system [[0,3,4,2],[1]]) (.forbid 0 2 3 (.system [[0,3,4,5,2],[1]]) (.forbid 0 2 4 (.system [[0,3,4,5,6,2],[1]]) (.forbid 1 2 1 (.system [[0],[1,3,2]]) (.forbid 1 2 2 (.system [[0],[1,3,4,2]]) (.forbid 1 2 3 (.system [[0],[1,3,4,5,2]]) (.forbid 1 2 4 (.system [[0],[1,3,4,5,6,2]]) (.packing {.ball 0 (.succ (.zero ∅ 5 2) ∅ 12 3), .ball 1 (.succ (.zero ∅ 5 2) ∅ 12 3), .ball 2 (.succ (.zero ∅ 5 2) ∅ 12 3)}))))))))))))

theorem certificate_21_checked : certificate_21.Valid 7 3 3 certificate_21_q certificate_21_edges 0 0 [] := by decide +kernel
theorem certificate_21_valid : certificate_21.Valid 7 3 (patternOrder [[],[],[]]) (patternClique [[],[],[]]) (patternEdges [[],[],[]]) (patternAmount [[],[],[]]) (patternEdgeCount [[],[],[]]) [] := certificate_21_checked

noncomputable def certificate_22_q : Finset ℕ := ([0,1,3] : List ℕ).toFinset
noncomputable def certificate_22_edges : List (ℕ × ℕ) := [(1,2),(2,3),(0,1),(0,3),(1,3)]

noncomputable def certificate_22 : FiniteCertificate := .forbid 0 1 1 (.system [[0,4,1,2,3]]) (.forbid 0 1 2 (.system [[0,4,5,1],[3]]) (.forbid 0 1 3 (.system [[0,4,5,6,1],[3]]) (.forbid 0 1 4 (.system [[0,4,5,6,7,1],[3]]) (.forbid 0 2 1 (.system [[0,4,2,1],[3]]) (.forbid 0 2 2 (.system [[0,4,5,2,1],[3]]) (.forbid 0 2 3 (.system [[0,4,5,6,2,1],[3]]) (.forbid 0 2 4 (.system [[0,4,5,6,7,2,1],[3]]) (.forbid 1 2 1 (.system [[0],[1,4,2,3]]) (.forbid 1 2 2 (.system [[0],[1,4,5,2,3]]) (.forbid 1 2 3 (.system [[0],[1,4,5,6,2,3]]) (.forbid 1 2 4 (.system [[0],[1,4,5,6,7,2,3]]) (.packing {.ball 0 (.succ (.zero ∅ 4 2) ∅ 11 3), .ball 1 (.succ (.zero ∅ 4 2) ∅ 11 3), .ball 2 (.succ (.zero ∅ 4 2) ∅ 11 3)}))))))))))))

theorem certificate_22_checked : certificate_22.Valid 7 3 4 certificate_22_q certificate_22_edges 1 1 [] := by decide +kernel
theorem certificate_22_valid : certificate_22.Valid 7 3 (patternOrder [[],[1]]) (patternClique [[],[1]]) (patternEdges [[],[1]]) (patternAmount [[],[1]]) (patternEdgeCount [[],[1]]) [] := certificate_22_checked

noncomputable def certificate_23_q : Finset ℕ := ([0,1,4] : List ℕ).toFinset
noncomputable def certificate_23_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(0,1),(0,4),(1,4)]

noncomputable def certificate_23 : FiniteCertificate := .forbid 0 1 1 (.system [[0,5,1,2,3,4]]) (.forbid 0 1 2 (.system [[0,5,6,1,2,3,4]]) (.forbid 0 1 3 (.system [[0,5,6,7,1],[4]]) (.forbid 0 1 4 (.system [[0,5,6,7,8,1],[4]]) (.forbid 0 2 1 (.system [[0,5,2,3,4],[1]]) (.forbid 0 2 2 (.system [[0,5,6,2,1],[4]]) (.forbid 0 2 3 (.system [[0,5,6,7,2,1],[4]]) (.forbid 0 2 4 (.system [[0,5,6,7,8,2,1],[4]]) (.forbid 1 2 1 (.system [[0],[1,5,2,3,4]]) (.forbid 1 2 2 (.system [[0],[1,5,6,2,3,4]]) (.forbid 1 2 3 (.system [[0],[1,5,6,7,2,3,4]]) (.forbid 1 2 4 (.system [[0],[1,5,6,7,8,2,3,4]]) (.packing {.ball 0 (.succ (.zero ∅ 3 2) ∅ 10 3), .ball 1 (.succ (.zero ∅ 3 2) ∅ 10 3), .ball 2 (.succ (.zero ∅ 3 2) ∅ 10 3)}))))))))))))

theorem certificate_23_checked : certificate_23.Valid 7 3 5 certificate_23_q certificate_23_edges 2 1 [] := by decide +kernel
theorem certificate_23_valid : certificate_23.Valid 7 3 (patternOrder [[],[2]]) (patternClique [[],[2]]) (patternEdges [[],[2]]) (patternAmount [[],[2]]) (patternEdgeCount [[],[2]]) [] := certificate_23_checked

noncomputable def certificate_24_q : Finset ℕ := ([0,1,5] : List ℕ).toFinset

noncomputable def certificate_24_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(0,1),(0,5),(1,5)]

noncomputable def certificate_24_E : List (ℕ × ℕ) := certificate_24_edges

noncomputable def certificate_24_M : ForbiddenMatrix := []

noncomputable def certificate_24_part_1_E : List (ℕ × ℕ) := certificate_24_E

noncomputable def certificate_24_part_1_M : ForbiddenMatrix := ((0,4,2) :: (((0,4,1) :: (((0,2,1) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((0,1,2) :: (((0,1,1) :: (certificate_24_M))))))))))))))))

noncomputable def certificate_24_part_2_E : List (ℕ × ℕ) := (augmentedEdges 6 (certificate_24_part_1_E) 0 3 1)

noncomputable def certificate_24_part_2_M : ForbiddenMatrix := ((1,4,5) :: (((1,4,4) :: (((1,4,3) :: (((1,2,1) :: (((0,4,5) :: (((0,4,4) :: (((0,4,3) :: (certificate_24_part_1_M))))))))))))))

noncomputable def certificate_24_part_2 : FiniteCertificate := .forbid 0 1 3 (.cycle [0,6,3,2,1,9,8,7]) (.forbid 1 4 1 (.cycle [1,2,3,6,0,5,4,7]) (.forbid 1 4 2 (.cycle [1,5,0,6,3,4,8,7]) (.forbid 2 4 1 (.cycle [2,1,5,0,6,3,4,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,4} 4 2) ∅ 8 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,4} 4 2) ∅ 8 3), .ball 4 (.succ (.zero ∅ 1 1) {0,1,2} 4 2)}))))

theorem certificate_24_part_2_checked : certificate_24_part_2.Valid 7 3 7 certificate_24_q certificate_24_part_2_E 3 1 certificate_24_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

noncomputable def certificate_24_part_3_E : List (ℕ × ℕ) := certificate_24_part_1_E

noncomputable def certificate_24_part_3_M : ForbiddenMatrix := ((0,3,1) :: (((1,4,5) :: (((1,4,4) :: (((1,4,3) :: (((1,2,1) :: (((0,4,5) :: (((0,4,4) :: (((0,4,3) :: (certificate_24_part_1_M))))))))))))))))

noncomputable def certificate_24_part_4_E : List (ℕ × ℕ) := certificate_24_part_3_E

noncomputable def certificate_24_part_4_M : ForbiddenMatrix := ((0,5,6) :: (((0,5,5) :: (((0,5,4) :: (((0,5,2) :: (((0,5,1) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (certificate_24_part_3_M))))))))))))))))

noncomputable def certificate_24_part_5_E : List (ℕ × ℕ) := (augmentedEdges 6 (certificate_24_part_4_E) 3 5 1)

noncomputable def certificate_24_part_5_M : ForbiddenMatrix := ((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((0,2,5) :: (((0,2,4) :: (((0,2,3) :: (((0,2,2) :: (certificate_24_part_4_M))))))))))))))

noncomputable def certificate_24_part_5 : FiniteCertificate := .forbid 0 6 1 (.cycle [0,1,2,3,4,5,6,7]) (.forbid 0 6 2 (.cycle [0,1,5,4,3,6,8,7]) (.forbid 0 6 3 (.cycle [0,1,2,3,6,9,8,7]) (.forbid 2 4 1 (.cycle [2,1,0,5,6,3,4,7]) (.forbid 2 6 1 (.cycle [2,1,0,5,4,3,6,7]) (.forbid 2 6 2 (.cycle [2,1,5,4,3,6,8,7]) (.forbid 4 6 1 (.cycle [4,3,2,1,0,5,6,7]) (.forbid 4 6 2 (.cycle [4,3,2,1,5,6,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {2,4,6} 4 2) ∅ 8 3), .ball 2 (.succ (.zero ∅ 1 1) {0,4,6} 4 2), .ball 4 (.succ (.zero ∅ 1 1) {0,2,6} 4 2), .singleton 6}))))))))

theorem certificate_24_part_5_checked : certificate_24_part_5.Valid 7 3 7 certificate_24_q certificate_24_part_5_E 3 1 certificate_24_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_24_part_6_E : List (ℕ × ℕ) := certificate_24_part_4_E

noncomputable def certificate_24_part_6_M : ForbiddenMatrix := ((3,5,1) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((0,2,5) :: (((0,2,4) :: (((0,2,3) :: (((0,2,2) :: (certificate_24_part_4_M))))))))))))))))

noncomputable def certificate_24_part_7_E : List (ℕ × ℕ) := certificate_24_part_6_E

noncomputable def certificate_24_part_7_M : ForbiddenMatrix := ((2,5,5) :: (((2,5,4) :: (((2,5,3) :: (((0,2,0) :: (((3,5,5) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (certificate_24_part_6_M))))))))))))))))

noncomputable def certificate_24_part_7 : FiniteCertificate := .forbid 4 5 1 (.system [[0],[1,2,3,4,6,5]]) (.forbid 1 4 1 (.forbid 0 5 3 (.cycle [0,1,6,4,5,9,8,7]) (.forbid 2 5 1 (.cycle [2,3,4,6,1,0,5,7]) (.forbid 2 5 2 (.cycle [2,3,4,6,1,5,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,5} 4 2) ∅ 8 3), .ball 5 (.succ (.succ (.zero ∅ 1 1) {0,2,4} 4 2) ∅ 8 3), .ball 2 (.succ (.zero ∅ 1 1) {0,1,5} 4 2)})))) (.forbid 0 3 0 (.forbid 0 1 3 (.cycle [0,3,4,5,1,8,7,6]) (.forbid 1 4 2 (.cycle [1,2,3,0,5,4,7,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,4} 4 2) ∅ 9 3), .ball 1 (.succ (.succ (.zero ∅ 2 1) {0,4} 4 2) ∅ 9 3), .ball 4 (.succ (.zero ∅ 2 1) {0,1} 4 2)}))) (.forbid 2 3 1 (.system [[0],[1,2,6,3,4,5]]) (.forbid 2 3 2 (.system [[0],[1,2,6,7,3,4,5]]) (.forbid 2 3 3 (.system [[0],[1,2,6,7,8,3,4,5]]) (.packing {.ball 0 (.succ (.zero {2} 3 2) ∅ 9 3), .ball 3 (.succ (.zero {0} 3 2) ∅ 9 3), .ball 2 (.zero {0} 3 2)}))))))

theorem certificate_24_part_7_checked : certificate_24_part_7.Valid 7 3 6 certificate_24_q certificate_24_part_7_E 3 1 certificate_24_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

noncomputable def certificate_24_part_6 : FiniteCertificate := .forbid 3 5 2 (.system [[0],[1,2,3,6,7,5]]) (.forbid 3 5 3 (.system [[0],[1,2,3,6,7,8,5]]) (.forbid 3 5 4 (.system [[0],[1,2,3,6,7,8,9,5]]) (.forbid 3 5 5 (.cycle [3,4,5,10,9,8,7,6]) (.forbid 0 2 0 (.forbid 0 3 5 (.cycle [0,2,3,10,9,8,7,6]) (.forbid 0 5 3 (.cycle [0,2,3,4,5,8,7,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {3,5} 4 2) ∅ 9 3), .ball 5 (.succ (.succ (.zero ∅ 2 1) {0,3} 4 2) ∅ 9 3), .ball 3 (.succ (.zero ∅ 2 1) {0,5} 4 2)}))) (.forbid 2 5 3 (.system [[0],[1,2,6,7,8,5]]) (.forbid 2 5 4 (.system [[0],[1,2,6,7,8,9,5]]) (.forbid 2 5 5 (.system [[0],[1,2,6,7,8,9,10,5]]) (certificate_24_part_7))))))))

theorem certificate_24_part_6_checked : certificate_24_part_6.Valid 7 3 6 certificate_24_q certificate_24_part_6_E 3 1 certificate_24_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_24_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_24_part_4 : FiniteCertificate := .forbid 0 2 2 (.system [[0,6,7,2,3,4,5],[1]]) (.forbid 0 2 3 (.system [[0,6,7,8,2,1],[5]]) (.forbid 0 2 4 (.system [[0,6,7,8,9,2,1],[5]]) (.forbid 0 2 5 (.system [[0,6,7,8,9,10,2,1],[5]]) (.forbid 2 4 2 (.system [[0],[1,2,6,7,4,5]]) (.forbid 2 4 3 (.system [[0],[1,2,6,7,8,4,5]]) (.forbid 2 4 4 (.system [[0],[1,2,6,7,8,9,4,5]]) (.forbid 3 5 1 (certificate_24_part_5) (certificate_24_part_6))))))))

theorem certificate_24_part_4_checked : certificate_24_part_4.Valid 7 3 6 certificate_24_q certificate_24_part_4_E 3 1 certificate_24_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_24_part_5_checked, certificate_24_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_24_part_3 : FiniteCertificate := .forbid 0 3 2 (.system [[0,6,7,3,2,1],[5]]) (.forbid 0 3 3 (.system [[0,6,7,8,3,2,1],[5]]) (.forbid 0 3 4 (.system [[0,6,7,8,9,3,2,1],[5]]) (.forbid 0 5 1 (.system [[0,6,5,4,3,2,1]]) (.forbid 0 5 2 (.system [[0,6,7,5,4,3,2,1]]) (.forbid 0 5 4 (.system [[0,6,7,8,9,5],[1]]) (.forbid 0 5 5 (.system [[0,6,7,8,9,10,5],[1]]) (.forbid 0 5 6 (.system [[0,6,7,8,9,10,11,5],[1]]) (certificate_24_part_4))))))))

theorem certificate_24_part_3_checked : certificate_24_part_3.Valid 7 3 6 certificate_24_q certificate_24_part_3_E 3 1 certificate_24_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_24_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_24_part_1 : FiniteCertificate := .forbid 0 4 3 (.system [[0,6,7,8,4,3,2,1],[5]]) (.forbid 0 4 4 (.system [[0,6,7,8,9,4,5],[1]]) (.forbid 0 4 5 (.system [[0,6,7,8,9,10,4,5],[1]]) (.forbid 1 2 1 (.system [[0],[1,6,2,3,4,5]]) (.forbid 1 4 3 (.system [[0],[1,6,7,8,4,5]]) (.forbid 1 4 4 (.system [[0],[1,6,7,8,9,4,5]]) (.forbid 1 4 5 (.system [[0],[1,6,7,8,9,10,4,5]]) (.forbid 0 3 1 (certificate_24_part_2) (certificate_24_part_3))))))))

theorem certificate_24_part_1_checked : certificate_24_part_1.Valid 7 3 6 certificate_24_q certificate_24_part_1_E 3 1 certificate_24_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_24_part_2_checked, certificate_24_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_24 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1,2,3,4,5]]) (.forbid 0 1 2 (.system [[0,6,7,1,2,3,4,5]]) (.forbid 0 1 4 (.system [[0,6,7,8,9,1],[5]]) (.forbid 0 1 5 (.system [[0,6,7,8,9,10,1],[5]]) (.forbid 0 1 6 (.system [[0,6,7,8,9,10,11,1],[5]]) (.forbid 0 2 1 (.system [[0,6,2,3,4,5],[1]]) (.forbid 0 4 1 (.system [[0,6,4,3,2,1],[5]]) (.forbid 0 4 2 (.system [[0,6,7,4,3,2,1],[5]]) (certificate_24_part_1))))))))

theorem certificate_24_checked : certificate_24.Valid 7 3 6 certificate_24_q certificate_24_E 3 1 certificate_24_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_24_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_24_valid : certificate_24.Valid 7 3 (patternOrder [[],[3]]) (patternClique [[],[3]]) (patternEdges [[],[3]]) (patternAmount [[],[3]]) (patternEdgeCount [[],[3]]) [] := certificate_24_checked

noncomputable def certificate_25_q : Finset ℕ := ([0,1,6] : List ℕ).toFinset

noncomputable def certificate_25_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(0,1),(0,6),(1,6)]

noncomputable def certificate_25_E : List (ℕ × ℕ) := certificate_25_edges

noncomputable def certificate_25_M : ForbiddenMatrix := []

noncomputable def certificate_25_part_1_E : List (ℕ × ℕ) := certificate_25_E

noncomputable def certificate_25_part_1_M : ForbiddenMatrix := ((2,5,3) :: (((0,5,5) :: (((0,5,4) :: (((0,5,2) :: (((0,5,1) :: (((0,1,1) :: (((0,2,2) :: (((0,2,1) :: (certificate_25_M))))))))))))))))

noncomputable def certificate_25_part_2_E : List (ℕ × ℕ) := (augmentedEdges 7 (certificate_25_part_1_E) 0 3 1)

noncomputable def certificate_25_part_2_M : ForbiddenMatrix := ((1,7,0) :: (((1,5,1) :: (((0,7,3) :: (((0,7,2) :: (((0,7,1) :: (((0,5,3) :: (((0,2,0) :: (certificate_25_part_1_M))))))))))))))

noncomputable def certificate_25_part_3_E : List (ℕ × ℕ) := certificate_25_part_2_E

noncomputable def certificate_25_part_3_M : ForbiddenMatrix := ((5,7,2) :: (((5,7,1) :: (((4,7,0) :: (((2,7,1) :: (((2,7,0) :: (((2,5,2) :: (((2,5,1) :: (((2,5,0) :: (certificate_25_part_2_M))))))))))))))))

noncomputable def certificate_25_part_3 : FiniteCertificate := .forbid 5 7 3 (.cycle [5,6,1,0,7,10,9,8]) (.forbid 5 7 4 (.cycle [5,4,3,7,11,10,9,8]) (.packing {.ball 0 (.succ (.zero {2} 1 1) {1,2,5,7} 4 2), .ball 5 (.succ (.succ (.zero {2} 1 1) {0,1,2,7} 4 2) {0} 8 3), .ball 7 (.zero {1,2,4} 3 2), .singleton 2}))

theorem certificate_25_part_3_checked : certificate_25_part_3.Valid 7 3 8 certificate_25_q certificate_25_part_3_E 4 1 certificate_25_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

noncomputable def certificate_25_part_2 : FiniteCertificate := .forbid 2 5 0 (.cycle [2,1,6,0,7,3,4,5]) (.forbid 2 5 1 (.cycle [2,1,0,7,3,4,5,8]) (.forbid 2 5 2 (.cycle [2,3,7,0,6,5,9,8]) (.forbid 2 7 0 (.cycle [2,1,0,6,5,4,3,7]) (.forbid 2 7 1 (.cycle [2,1,6,5,4,3,7,8]) (.forbid 4 7 0 (.cycle [4,5,6,0,1,2,3,7]) (.forbid 5 7 1 (.cycle [5,4,3,2,1,0,7,8]) (.forbid 5 7 2 (.cycle [5,6,1,2,3,7,9,8]) (certificate_25_part_3))))))))

theorem certificate_25_part_2_checked : certificate_25_part_2.Valid 7 3 8 certificate_25_q certificate_25_part_2_E 4 1 certificate_25_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_25_part_4_E : List (ℕ × ℕ) := (augmentedEdges 7 (certificate_25_part_1_E) 0 4 1)

noncomputable def certificate_25_part_4_M : ForbiddenMatrix := ((1,2,1) :: (((0,2,5) :: (((0,2,4) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (certificate_25_part_1_M))))))))))))))

noncomputable def certificate_25_part_5_E : List (ℕ × ℕ) := certificate_25_part_4_E

noncomputable def certificate_25_part_5_M : ForbiddenMatrix := ((2,5,1) :: (((2,5,0) :: (((1,7,0) :: (((0,7,3) :: (((0,7,2) :: (((0,7,1) :: (((0,3,0) :: (((0,2,3) :: (certificate_25_part_4_M))))))))))))))))

noncomputable def certificate_25_part_5 : FiniteCertificate := .forbid 2 5 2 (.cycle [2,1,0,7,4,5,9,8]) (.forbid 2 7 0 (.cycle [2,3,4,5,6,1,0,7]) (.forbid 2 7 1 (.cycle [2,1,0,6,5,4,7,8]) (.forbid 2 7 2 (.cycle [2,1,6,5,4,7,9,8]) (.forbid 2 7 3 (.cycle [2,1,6,0,7,10,9,8]) (.forbid 2 7 4 (.cycle [2,1,0,7,11,10,9,8]) (.forbid 3 7 0 (.cycle [3,2,1,0,6,5,4,7]) (.forbid 5 7 1 (.cycle [5,4,3,2,1,0,7,8]) (.packing {.ball 0 (.succ (.zero {3} 1 1) {1,2,5,7} 4 2), .ball 2 (.succ (.succ (.zero {5} 1 1) {0,1,5,7} 4 2) {0} 8 3), .ball 7 (.zero {1,2,3} 3 2), .singleton 5}))))))))

theorem certificate_25_part_5_checked : certificate_25_part_5.Valid 7 3 8 certificate_25_q certificate_25_part_5_E 4 1 certificate_25_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_25_part_4 : FiniteCertificate := .forbid 0 2 3 (.cycle [0,7,4,3,2,10,9,8]) (.forbid 0 3 0 (.cycle [0,7,4,5,6,1,2,3]) (.forbid 0 7 1 (.cycle [0,6,1,2,3,4,7,8]) (.forbid 0 7 2 (.cycle [0,1,2,3,4,7,9,8]) (.forbid 0 7 3 (.cycle [0,6,5,4,7,10,9,8]) (.forbid 1 7 0 (.cycle [1,2,3,4,5,6,0,7]) (.forbid 2 5 0 (.cycle [2,3,4,7,0,1,6,5]) (.forbid 2 5 1 (.cycle [2,1,6,0,7,4,5,8]) (certificate_25_part_5))))))))

theorem certificate_25_part_4_checked : certificate_25_part_4.Valid 7 3 8 certificate_25_q certificate_25_part_4_E 4 1 certificate_25_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_25_part_6_E : List (ℕ × ℕ) := certificate_25_part_1_E

noncomputable def certificate_25_part_6_M : ForbiddenMatrix := ((0,4,1) :: (((1,2,1) :: (((0,2,5) :: (((0,2,4) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (certificate_25_part_1_M))))))))))))))))

noncomputable def certificate_25_part_7_E : List (ℕ × ℕ) := (augmentedEdges 7 (certificate_25_part_6_E) 2 5 1)

noncomputable def certificate_25_part_7_M : ForbiddenMatrix := ((0,3,0) :: (((3,4,2) :: (((3,4,1) :: (((2,4,2) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (certificate_25_part_6_M))))))))))))))

noncomputable def certificate_25_part_7 : FiniteCertificate := .forbid 0 4 0 (.cycle [0,1,6,5,7,2,3,4]) (.forbid 0 7 0 (.cycle [0,1,6,5,4,3,2,7]) (.forbid 1 4 0 (.cycle [1,0,6,5,7,2,3,4]) (.forbid 3 4 3 (.cycle [3,2,7,5,4,10,9,8]) (.forbid 3 6 0 (.cycle [3,4,5,7,2,1,0,6]) (.forbid 3 7 0 (.cycle [3,4,5,6,0,1,2,7]) (.forbid 4 7 0 (.cycle [4,3,2,1,0,6,5,7]) (.packing {.ball 0 (.succ (.zero {3,4,7} 3 2) {3} 8 3), .ball 3 (.succ (.zero {0,6,7} 3 2) {0} 8 3), .ball 4 (.zero {0,1,7} 3 2)})))))))

theorem certificate_25_part_7_checked : certificate_25_part_7.Valid 7 3 8 certificate_25_q certificate_25_part_7_E 4 1 certificate_25_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_25_part_8_E : List (ℕ × ℕ) := certificate_25_part_6_E

noncomputable def certificate_25_part_8_M : ForbiddenMatrix := ((2,5,4) :: (((2,5,1) :: (((3,4,2) :: (((3,4,1) :: (((2,4,2) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (certificate_25_part_6_M))))))))))))))))

noncomputable def certificate_25_part_9_E : List (ℕ × ℕ) := (augmentedEdges 7 (certificate_25_part_8_E) 2 4 0)

noncomputable def certificate_25_part_9_M : ForbiddenMatrix := ((0,5,3) :: (((3,5,5) :: (((3,5,3) :: (((3,5,2) :: (((1,3,0) :: (((4,5,2) :: (((4,5,1) :: (certificate_25_part_8_M))))))))))))))

noncomputable def certificate_25_part_9 : FiniteCertificate := .forbid 3 5 1 (.cycle [3,4,2,1,0,6,5,7]) (.forbid 3 5 4 (.cycle [3,2,4,5,10,9,8,7]) (.forbid 4 5 3 (.cycle [4,2,1,6,5,9,8,7]) (.packing {.ball 0 (.succ (.zero ∅ 1 1) {3,4,5} 4 2), .ball 5 (.succ (.succ (.zero ∅ 1 1) {0,3,4} 4 2) ∅ 8 3), .ball 3 (.succ (.zero ∅ 1 1) {0,4,5} 4 2), .singleton 4})))

theorem certificate_25_part_9_checked : certificate_25_part_9.Valid 7 3 7 certificate_25_q certificate_25_part_9_E 4 1 certificate_25_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

noncomputable def certificate_25_part_10_E : List (ℕ × ℕ) := certificate_25_part_8_E

noncomputable def certificate_25_part_10_M : ForbiddenMatrix := ((1,2,2) :: (((2,4,0) :: (((3,5,5) :: (((3,5,3) :: (((3,5,2) :: (((1,3,0) :: (((4,5,2) :: (((4,5,1) :: (certificate_25_part_8_M))))))))))))))))

noncomputable def certificate_25_part_11_E : List (ℕ × ℕ) := (augmentedEdges 7 (certificate_25_part_10_E) 1 4 1)

noncomputable def certificate_25_part_11_M : ForbiddenMatrix := ((0,7,4) :: (((0,7,3) :: (((0,7,2) :: (((0,7,1) :: (((0,7,0) :: (((0,5,3) :: (((0,3,0) :: (certificate_25_part_10_M))))))))))))))

noncomputable def certificate_25_part_12_E : List (ℕ × ℕ) := certificate_25_part_11_E

noncomputable def certificate_25_part_12_M : ForbiddenMatrix := ((5,7,3) :: (((5,7,2) :: (((5,7,1) :: (((3,7,0) :: (((3,5,1) :: (((2,7,0) :: (((2,5,0) :: (((0,7,5) :: (certificate_25_part_11_M))))))))))))))))

noncomputable def certificate_25_part_12 : FiniteCertificate := .forbid 5 7 4 (.cycle [5,6,1,7,11,10,9,8]) (.packing {.ball 0 (.succ (.succ (.zero {3} 1 1) {1,2,5,7} 4 2) {5} 8 3), .ball 7 (.succ (.zero {0,2,3} 3 2) {0} 8 3), .ball 5 (.succ (.zero {2} 1 1) {0,2,3,7} 4 2)})

theorem certificate_25_part_12_checked : certificate_25_part_12.Valid 7 3 8 certificate_25_q certificate_25_part_12_E 4 1 certificate_25_part_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

noncomputable def certificate_25_part_11 : FiniteCertificate := .forbid 0 7 5 (.cycle [0,1,7,12,11,10,9,8]) (.forbid 2 5 0 (.cycle [2,3,4,7,1,0,6,5]) (.forbid 2 7 0 (.cycle [2,3,4,5,6,0,1,7]) (.forbid 3 5 1 (.cycle [3,4,7,1,0,6,5,8]) (.forbid 3 7 0 (.cycle [3,2,1,0,6,5,4,7]) (.forbid 5 7 1 (.cycle [5,6,1,2,3,4,7,8]) (.forbid 5 7 2 (.cycle [5,4,3,2,1,7,9,8]) (.forbid 5 7 3 (.cycle [5,6,0,1,7,10,9,8]) (certificate_25_part_12))))))))

theorem certificate_25_part_11_checked : certificate_25_part_11.Valid 7 3 8 certificate_25_q certificate_25_part_11_E 4 1 certificate_25_part_11_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_12_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_25_part_13_E : List (ℕ × ℕ) := (augmentedEdges 7 (certificate_25_part_10_E) 3 5 0)

noncomputable def certificate_25_part_13_M : ForbiddenMatrix := ((1,4,2) :: (((1,2,3) :: (((0,2,3) :: (((0,1,2) :: (((2,4,5) :: (((2,4,3) :: (((1,4,1) :: (certificate_25_part_10_M))))))))))))))

noncomputable def certificate_25_part_13 : FiniteCertificate := .forbid 2 4 1 (.cycle [2,1,0,6,5,3,4,7]) (.forbid 2 4 4 (.cycle [2,3,5,4,10,9,8,7]) (.packing {.ball 0 (.succ (.zero ∅ 1 1) {1,2,4} 4 2), .ball 2 (.succ (.succ (.zero ∅ 1 1) {0,1,4} 4 2) ∅ 8 3), .ball 4 (.succ (.zero ∅ 1 1) {0,1,2} 4 2), .singleton 1}))

theorem certificate_25_part_13_checked : certificate_25_part_13.Valid 7 3 7 certificate_25_q certificate_25_part_13_E 4 1 certificate_25_part_13_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

noncomputable def certificate_25_part_14_E : List (ℕ × ℕ) := (augmentedEdges 7 (certificate_25_part_10_E) 4 6 0)

noncomputable def certificate_25_part_14_M : ForbiddenMatrix := ((0,2,3) :: (((2,3,2) :: (((2,3,1) :: (((3,5,0) :: (((2,4,5) :: (((2,4,3) :: (((1,4,1) :: (certificate_25_part_10_M))))))))))))))

noncomputable def certificate_25_part_14 : FiniteCertificate := .forbid 0 5 3 (.cycle [0,1,6,4,5,9,8,7]) (.forbid 2 5 2 (.cycle [2,1,0,6,4,5,8,7]) (.forbid 3 5 1 (.cycle [3,2,1,0,6,4,5,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {2,3,5} 4 2) ∅ 8 3), .ball 2 (.succ (.zero ∅ 1 1) {0,3,5} 4 2), .ball 5 (.succ (.zero ∅ 1 1) {0,2,3} 4 2), .singleton 3})))

theorem certificate_25_part_14_checked : certificate_25_part_14.Valid 7 3 7 certificate_25_q certificate_25_part_14_E 4 1 certificate_25_part_14_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

noncomputable def certificate_25_part_15_E : List (ℕ × ℕ) := (augmentedEdges 7 (certificate_25_part_10_E) 0 3 0)

noncomputable def certificate_25_part_15_M : ForbiddenMatrix := ((4,6,0) :: (((2,3,2) :: (((2,3,1) :: (((3,5,0) :: (((2,4,5) :: (((2,4,3) :: (((1,4,1) :: (certificate_25_part_10_M))))))))))))))

noncomputable def certificate_25_part_15 : FiniteCertificate := .forbid 0 4 5 (.cycle [0,3,4,11,10,9,8,7]) (.forbid 3 4 3 (.cycle [3,0,6,5,4,9,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4} 4 2) ∅ 8 3), .ball 4 (.succ (.zero {2,6} 3 2) ∅ 8 3), .ball 3 (.zero {1,5} 3 2)}))

theorem certificate_25_part_15_checked : certificate_25_part_15.Valid 7 3 7 certificate_25_q certificate_25_part_15_E 4 1 certificate_25_part_15_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

noncomputable def certificate_25_part_16_E : List (ℕ × ℕ) := certificate_25_part_10_E

noncomputable def certificate_25_part_16_M : ForbiddenMatrix := ((0,3,0) :: (((4,6,0) :: (((2,3,2) :: (((2,3,1) :: (((3,5,0) :: (((2,4,5) :: (((2,4,3) :: (((1,4,1) :: (certificate_25_part_10_M))))))))))))))))

noncomputable def certificate_25_part_16 : FiniteCertificate := .forbid 0 4 0 (.forbid 0 3 5 (.cycle [0,4,3,11,10,9,8,7]) (.forbid 3 4 3 (.cycle [3,2,1,0,4,9,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4} 4 2) ∅ 8 3), .ball 3 (.succ (.zero {1,5} 3 2) ∅ 8 3), .ball 4 (.zero {2,6} 3 2)}))) (.packing {.ball 0 (.succ (.zero {3,4} 3 2) ∅ 8 3), .ball 3 (.succ (.zero {0,1} 3 2) ∅ 8 3), .singleton 2, .singleton 4})

theorem certificate_25_part_16_checked : certificate_25_part_16.Valid 7 3 7 certificate_25_q certificate_25_part_16_E 4 1 certificate_25_part_16_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, by decide +kernel⟩

noncomputable def certificate_25_part_10 : FiniteCertificate := .forbid 1 4 1 (.forbid 0 3 0 (.cycle [0,6,5,4,7,1,2,3]) (.forbid 0 5 3 (.cycle [0,1,7,4,5,10,9,8]) (.forbid 0 7 0 (.cycle [0,6,5,4,3,2,1,7]) (.forbid 0 7 1 (.cycle [0,6,1,2,3,4,7,8]) (.forbid 0 7 2 (.cycle [0,1,2,3,4,7,9,8]) (.forbid 0 7 3 (.cycle [0,6,5,4,7,10,9,8]) (.forbid 0 7 4 (.cycle [0,6,1,7,11,10,9,8]) (certificate_25_part_11)))))))) (.forbid 2 4 3 (.system [[0],[1,2,7,8,9,4,5,6]]) (.forbid 2 4 5 (.cycle [2,3,4,11,10,9,8,7]) (.forbid 3 5 0 (.forbid 0 1 2 (.cycle [0,6,5,3,2,1,8,7]) (.forbid 0 2 3 (.cycle [0,6,5,3,2,9,8,7]) (.forbid 1 2 3 (.cycle [1,6,5,3,2,9,8,7]) (.forbid 1 4 2 (.cycle [1,0,6,5,3,4,8,7]) (certificate_25_part_13))))) (.forbid 2 3 1 (.system [[0],[1,2,7,3,4,5,6]]) (.forbid 2 3 2 (.system [[0],[1,2,7,8,3,4,5,6]]) (.forbid 4 6 0 (.forbid 0 2 3 (.cycle [0,6,4,3,2,9,8,7]) (certificate_25_part_14)) (.forbid 0 3 0 (certificate_25_part_15) (certificate_25_part_16))))))))

theorem certificate_25_part_10_checked : certificate_25_part_10.Valid 7 3 7 certificate_25_q certificate_25_part_10_E 4 1 certificate_25_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_11_checked⟩⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_13_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_14_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_25_part_15_checked, certificate_25_part_16_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_25_part_8 : FiniteCertificate := .forbid 4 5 1 (.system [[0],[1,2,3,4,7,5,6]]) (.forbid 4 5 2 (.system [[0],[1,2,3,4,7,8,5,6]]) (.forbid 1 3 0 (.forbid 0 2 3 (.cycle [0,6,1,3,2,9,8,7]) (.forbid 0 5 3 (.cycle [0,1,3,4,5,9,8,7]) (.forbid 2 4 1 (.cycle [2,3,1,0,6,5,4,7]) (.forbid 2 5 2 (.cycle [2,3,1,0,6,5,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {2,4,5} 4 2) ∅ 8 3), .ball 2 (.succ (.zero ∅ 1 1) {0,4,5} 4 2), .ball 5 (.succ (.zero ∅ 1 1) {0,2,4} 4 2), .singleton 4}))))) (.forbid 3 5 2 (.system [[0],[1,2,3,7,8,5,6]]) (.forbid 3 5 3 (.system [[0],[1,2,3,7,8,9,5,6]]) (.forbid 3 5 5 (.cycle [3,4,5,11,10,9,8,7]) (.forbid 2 4 0 (.forbid 0 5 3 (.cycle [0,1,2,4,5,9,8,7]) (certificate_25_part_9)) (.forbid 1 2 2 (.system [[0],[1,7,8,2,3,4,5,6]]) (certificate_25_part_10))))))))

theorem certificate_25_part_8_checked : certificate_25_part_8.Valid 7 3 7 certificate_25_q certificate_25_part_8_E 4 1 certificate_25_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_9_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_10_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_25_part_6 : FiniteCertificate := .forbid 0 4 2 (.system [[0,7,8,4,3,2,1],[6]]) (.forbid 0 4 3 (.system [[0,7,8,9,4,3,2,1],[6]]) (.forbid 0 4 4 (.system [[0,7,8,9,10,4,5,6],[1]]) (.forbid 2 4 2 (.system [[0],[1,2,7,8,4,5,6]]) (.forbid 3 4 1 (.system [[0],[1,2,3,7,4,5,6]]) (.forbid 3 4 2 (.system [[0],[1,2,3,7,8,4,5,6]]) (.forbid 2 5 1 (.forbid 0 3 0 (.cycle [0,6,1,2,7,5,4,3]) (certificate_25_part_7)) (.forbid 2 5 4 (.system [[0],[1,2,7,8,9,10,5,6]]) (certificate_25_part_8))))))))

theorem certificate_25_part_6_checked : certificate_25_part_6.Valid 7 3 7 certificate_25_q certificate_25_part_6_E 4 1 certificate_25_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_7_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_8_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_25_part_1 : FiniteCertificate := .forbid 0 3 1 (.forbid 0 2 0 (.cycle [0,7,3,4,5,6,1,2]) (.forbid 0 5 3 (.cycle [0,7,3,4,5,10,9,8]) (.forbid 0 7 1 (.cycle [0,1,6,5,4,3,7,8]) (.forbid 0 7 2 (.cycle [0,6,1,2,3,7,9,8]) (.forbid 0 7 3 (.cycle [0,1,2,3,7,10,9,8]) (.forbid 1 5 1 (.cycle [1,2,3,7,0,6,5,8]) (.forbid 1 7 0 (.cycle [1,2,3,4,5,6,0,7]) (certificate_25_part_2)))))))) (.forbid 0 3 2 (.system [[0,7,8,3,4,5,6],[1]]) (.forbid 0 3 3 (.system [[0,7,8,9,3,2,1],[6]]) (.forbid 0 3 4 (.system [[0,7,8,9,10,3,2,1],[6]]) (.forbid 0 2 4 (.system [[0,7,8,9,10,2,1],[6]]) (.forbid 0 2 5 (.system [[0,7,8,9,10,11,2,1],[6]]) (.forbid 1 2 1 (.system [[0],[1,7,2,3,4,5,6]]) (.forbid 0 4 1 (certificate_25_part_4) (certificate_25_part_6))))))))

theorem certificate_25_part_1_checked : certificate_25_part_1.Valid 7 3 7 certificate_25_q certificate_25_part_1_E 4 1 certificate_25_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_2_checked⟩⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_25_part_4_checked, certificate_25_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_25 : FiniteCertificate := .forbid 0 2 1 (.system [[0,7,2,3,4,5,6],[1]]) (.forbid 0 2 2 (.system [[0,7,8,2,3,4,5,6],[1]]) (.forbid 0 1 1 (.system [[0,7,1,2,3,4,5,6]]) (.forbid 0 5 1 (.system [[0,7,5,4,3,2,1],[6]]) (.forbid 0 5 2 (.system [[0,7,8,5,4,3,2,1],[6]]) (.forbid 0 5 4 (.system [[0,7,8,9,10,5,6],[1]]) (.forbid 0 5 5 (.system [[0,7,8,9,10,11,5,6],[1]]) (.forbid 2 5 3 (.system [[0],[1,2,7,8,9,5,6]]) (certificate_25_part_1))))))))

theorem certificate_25_checked : certificate_25.Valid 7 3 7 certificate_25_q certificate_25_E 4 1 certificate_25_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_25_valid : certificate_25.Valid 7 3 (patternOrder [[],[4]]) (patternClique [[],[4]]) (patternEdges [[],[4]]) (patternAmount [[],[4]]) (patternEdgeCount [[],[4]]) [] := certificate_25_checked

noncomputable def certificate_26_q : Finset ℕ := ([0,2,4] : List ℕ).toFinset
noncomputable def certificate_26_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(0,2),(0,4),(2,4)]

noncomputable def certificate_26 : FiniteCertificate := .forbid 0 1 1 (.system [[0,5,1,2],[4]]) (.forbid 0 1 2 (.system [[0,5,6,1,2],[4]]) (.forbid 0 1 3 (.system [[0,5,6,7,1,2],[4]]) (.forbid 0 1 4 (.system [[0,5,6,7,8,1,2],[4]]) (.forbid 0 3 1 (.system [[0,5,3,2],[4]]) (.forbid 0 3 2 (.system [[0,5,6,3,2],[4]]) (.forbid 0 3 3 (.system [[0,5,6,7,3,2],[4]]) (.forbid 0 3 4 (.system [[0,5,6,7,8,3,2],[4]]) (.forbid 1 3 1 (.system [[0,1,5,3,2],[4]]) (.forbid 1 3 2 (.system [[0,1,5,6,3,2],[4]]) (.forbid 1 3 3 (.system [[0,1,5,6,7,3,2],[4]]) (.forbid 1 3 4 (.system [[0,1,5,6,7,8,3,2],[4]]) (.packing {.ball 0 (.succ (.zero ∅ 3 2) ∅ 10 3), .ball 1 (.succ (.zero ∅ 3 2) ∅ 10 3), .ball 3 (.succ (.zero ∅ 3 2) ∅ 10 3)}))))))))))))

theorem certificate_26_checked : certificate_26.Valid 7 3 5 certificate_26_q certificate_26_edges 2 2 [] := by decide +kernel
theorem certificate_26_valid : certificate_26.Valid 7 3 (patternOrder [[1,1]]) (patternClique [[1,1]]) (patternEdges [[1,1]]) (patternAmount [[1,1]]) (patternEdgeCount [[1,1]]) [] := certificate_26_checked

noncomputable def certificate_27_q : Finset ℕ := ([0,2,5] : List ℕ).toFinset
noncomputable def certificate_27_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(0,2),(0,5),(2,5)]

noncomputable def certificate_27_part_0 : FiniteCertificate := .forbid 1 4 2 (.system [[0,1,6,7,4,3,2],[5]]) (.forbid 1 4 3 (.system [[0,1,6,7,8,4,3,2],[5]]) (.forbid 1 4 4 (.system [[0,1,6,7,8,9,4,5],[2]]) (.forbid 3 4 1 (.system [[0],[2,3,6,4,5]]) (.forbid 3 4 2 (.system [[0],[2,3,6,7,4,5]]) (.forbid 3 4 3 (.system [[0],[2,3,6,7,8,4,5]]) (.forbid 3 4 4 (.system [[0],[2,3,6,7,8,9,4,5]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,3} 4 2) ∅ 9 3), .ball 1 (.succ (.zero ∅ 2 1) {0,3} 4 2), .ball 3 (.succ (.zero ∅ 2 1) {0,1} 4 2), .ball 4 (.succ (.zero ∅ 2 1) {0,1} 4 2)})))))))

noncomputable def certificate_27 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1,2,3,4,5]]) (.forbid 0 1 2 (.system [[0,6,7,1,2],[5]]) (.forbid 0 1 3 (.system [[0,6,7,8,1,2],[5]]) (.forbid 0 1 4 (.system [[0,6,7,8,9,1,2],[5]]) (.forbid 0 1 5 (.system [[0,6,7,8,9,10,1,2],[5]]) (.forbid 0 3 1 (.system [[0,6,3,4,5],[2]]) (.forbid 0 3 2 (.system [[0,6,7,3,2],[5]]) (.forbid 0 3 3 (.system [[0,6,7,8,3,2],[5]]) (.forbid 0 3 4 (.system [[0,6,7,8,9,3,2],[5]]) (.forbid 0 3 5 (.system [[0,6,7,8,9,10,3,2],[5]]) (.forbid 0 4 1 (.system [[0,6,4,3,2],[5]]) (.forbid 0 4 2 (.system [[0,6,7,4,3,2],[5]]) (.forbid 0 4 3 (.system [[0,6,7,8,4,3,2],[5]]) (.forbid 0 4 4 (.system [[0,6,7,8,9,4,3,2],[5]]) (.forbid 0 4 5 (.system [[0,6,7,8,9,10,4,5],[2]]) (.forbid 1 3 1 (.system [[0,1,6,3,2],[5]]) (.forbid 1 3 2 (.system [[0,1,6,7,3,2],[5]]) (.forbid 1 3 3 (.system [[0,1,6,7,8,3,2],[5]]) (.forbid 1 3 4 (.system [[0,1,6,7,8,9,3,2],[5]]) (.forbid 1 4 1 (.system [[0,1,6,4,3,2],[5]]) (certificate_27_part_0))))))))))))))))))))

theorem certificate_27_checked : certificate_27.Valid 7 3 6 certificate_27_q certificate_27_edges 3 2 [] := by decide +kernel
theorem certificate_27_valid : certificate_27.Valid 7 3 (patternOrder [[1,2]]) (patternClique [[1,2]]) (patternEdges [[1,2]]) (patternAmount [[1,2]]) (patternEdgeCount [[1,2]]) [] := certificate_27_checked

noncomputable def certificate_28_q : Finset ℕ := ([0,2,6] : List ℕ).toFinset

noncomputable def certificate_28_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(0,2),(0,6),(2,6)]

noncomputable def certificate_28_E : List (ℕ × ℕ) := certificate_28_edges

noncomputable def certificate_28_M : ForbiddenMatrix := []

noncomputable def certificate_28_part_1_E : List (ℕ × ℕ) := certificate_28_E

noncomputable def certificate_28_part_1_M : ForbiddenMatrix := ((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((0,1,3) :: (((0,1,1) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (certificate_28_M))))))))))))))))

noncomputable def certificate_28_part_2_E : List (ℕ × ℕ) := certificate_28_part_1_E

noncomputable def certificate_28_part_2_M : ForbiddenMatrix := ((1,3,4) :: (((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,1) :: (((0,5,1) :: (((0,3,5) :: (((0,3,4) :: (certificate_28_part_1_M))))))))))))))))

noncomputable def certificate_28_part_3_E : List (ℕ × ℕ) := certificate_28_part_2_E

noncomputable def certificate_28_part_3_M : ForbiddenMatrix := ((3,5,2) :: (((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,5,1) :: (((0,4,0) :: (((2,3,1) :: (((1,3,5) :: (certificate_28_part_2_M))))))))))))))))

noncomputable def certificate_28_part_4_E : List (ℕ × ℕ) := (augmentedEdges 7 (certificate_28_part_3_E) 0 4 1)

noncomputable def certificate_28_part_4_M : ForbiddenMatrix := ((3,5,1) :: (((3,5,0) :: (((1,7,0) :: (((1,5,0) :: (((1,3,0) :: (((3,5,4) :: (((3,5,3) :: (certificate_28_part_3_M))))))))))))))

noncomputable def certificate_28_part_4 : FiniteCertificate := .forbid 3 6 0 (.cycle [3,2,1,0,7,4,5,6]) (.forbid 5 7 0 (.cycle [5,6,0,1,2,3,4,7]) (.packing {.ball 1 (.succ (.zero {3,5,7} 3 2) {3} 8 3), .ball 5 (.succ (.zero {1,3,7} 3 2) {1} 8 3), .ball 3 (.succ (.zero {1,5,6} 3 2) {1} 8 3)}))

theorem certificate_28_part_4_checked : certificate_28_part_4.Valid 7 3 8 certificate_28_q certificate_28_part_4_E 4 2 certificate_28_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

noncomputable def certificate_28_part_5_E : List (ℕ × ℕ) := (augmentedEdges 7 (certificate_28_part_3_E) 1 3 0)

noncomputable def certificate_28_part_5_M : ForbiddenMatrix := ((0,5,0) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((3,5,4) :: (((3,5,3) :: (certificate_28_part_3_M))))))))))))))

noncomputable def certificate_28_part_5 : FiniteCertificate := .forbid 0 1 2 (.cycle [0,6,5,4,3,1,8,7]) (.forbid 0 2 1 (.cycle [0,1,3,4,5,6,2,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3} 4 2) ∅ 8 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3} 4 2) ∅ 8 3), .ball 3 (.succ (.zero ∅ 1 1) {0,1,2} 4 2)}))

theorem certificate_28_part_5_checked : certificate_28_part_5.Valid 7 3 7 certificate_28_q certificate_28_part_5_E 4 2 certificate_28_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

noncomputable def certificate_28_part_6_E : List (ℕ × ℕ) := certificate_28_part_3_E

noncomputable def certificate_28_part_6_M : ForbiddenMatrix := ((1,3,0) :: (((0,5,0) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((3,5,4) :: (((3,5,3) :: (certificate_28_part_3_M))))))))))))))))

noncomputable def certificate_28_part_6 : FiniteCertificate := .forbid 1 4 0 (.forbid 0 1 2 (.cycle [0,2,6,5,4,1,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,5} 4 2) ∅ 8 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3} 4 2) ∅ 8 3), .ball 3 (.succ (.zero ∅ 1 1) {0,1,2} 4 2)})) (.forbid 3 4 1 (.system [[0],[2,3,7,4,5,6]]) (.forbid 3 4 2 (.system [[0],[2,3,7,8,4,5,6]]) (.forbid 3 4 3 (.system [[0],[2,3,7,8,9,4,5,6]]) (.forbid 3 5 0 (.forbid 0 1 2 (.cycle [0,6,5,3,2,1,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4} 4 2) ∅ 8 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3} 4 2) ∅ 8 3), .ball 3 (.succ (.zero ∅ 1 1) {0,1,2} 4 2)})) (.packing {.ball 0 (.succ (.zero {4,5} 3 2) ∅ 8 3), .ball 4 (.succ (.zero {0,1} 3 2) ∅ 8 3), .ball 3 (.zero {1,5} 3 2)})))))

theorem certificate_28_part_6_checked : certificate_28_part_6.Valid 7 3 7 certificate_28_q certificate_28_part_6_E 4 2 certificate_28_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩⟩⟩⟩⟩

noncomputable def certificate_28_part_3 : FiniteCertificate := .forbid 3 5 3 (.system [[0],[2,3,7,8,9,5,6]]) (.forbid 3 5 4 (.system [[0],[2,3,7,8,9,10,5,6]]) (.forbid 0 4 1 (.forbid 1 3 0 (.cycle [1,0,7,4,5,6,2,3]) (.forbid 1 5 0 (.cycle [1,0,7,4,3,2,6,5]) (.forbid 1 7 0 (.cycle [1,2,3,4,5,6,0,7]) (.forbid 3 5 0 (.cycle [3,4,7,0,1,2,6,5]) (.forbid 3 5 1 (.cycle [3,2,1,0,7,4,5,8]) (certificate_28_part_4)))))) (.forbid 0 4 2 (.system [[0,7,8,4,3,2],[6]]) (.forbid 0 4 3 (.system [[0,7,8,9,4,3,2],[6]]) (.forbid 0 4 4 (.system [[0,7,8,9,10,4,3,2],[6]]) (.forbid 0 5 0 (.forbid 0 1 2 (.cycle [0,5,4,3,2,1,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,5} 4 2) ∅ 8 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3} 4 2) ∅ 8 3), .ball 3 (.succ (.zero ∅ 1 1) {0,1,2} 4 2)})) (.forbid 1 3 0 (certificate_28_part_5) (certificate_28_part_6))))))))

theorem certificate_28_part_3_checked : certificate_28_part_3.Valid 7 3 7 certificate_28_q certificate_28_part_3_E 4 2 certificate_28_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_28_part_4_checked⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, certificate_28_part_5_checked, certificate_28_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_28_part_2 : FiniteCertificate := .forbid 1 3 5 (.cycle [1,2,3,11,10,9,8,7]) (.forbid 2 3 1 (.system [[0],[2,7,3,4,5,6]]) (.forbid 0 4 0 (.forbid 0 1 2 (.cycle [0,4,5,6,2,1,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,5} 4 2) ∅ 8 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3} 4 2) ∅ 8 3), .ball 3 (.succ (.zero ∅ 1 1) {0,1,2} 4 2)})) (.forbid 1 5 1 (.system [[0,1,7,5,4,3,2],[6]]) (.forbid 1 5 2 (.system [[0,1,7,8,5,4,3,2],[6]]) (.forbid 1 5 3 (.system [[0,1,7,8,9,5,6],[2]]) (.forbid 1 5 4 (.system [[0,1,7,8,9,10,5,6],[2]]) (.forbid 3 5 2 (.system [[0],[2,3,7,8,5,6]]) (certificate_28_part_3))))))))

theorem certificate_28_part_2_checked : certificate_28_part_2.Valid 7 3 7 certificate_28_q certificate_28_part_2_E 4 2 certificate_28_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_28_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_28_part_1 : FiniteCertificate := .forbid 0 3 4 (.system [[0,7,8,9,10,3,2],[6]]) (.forbid 0 3 5 (.system [[0,7,8,9,10,11,3,2],[6]]) (.forbid 0 5 1 (.system [[0,7,5,4,3,2],[6]]) (.forbid 1 2 1 (.system [[0,1,7,2,3,4,5,6]]) (.forbid 1 3 1 (.system [[0,1,7,3,4,5,6],[2]]) (.forbid 1 3 2 (.system [[0,1,7,8,3,2],[6]]) (.forbid 1 3 3 (.system [[0,1,7,8,9,3,2],[6]]) (.forbid 1 3 4 (.system [[0,1,7,8,9,10,3,2],[6]]) (certificate_28_part_2))))))))

theorem certificate_28_part_1_checked : certificate_28_part_1.Valid 7 3 7 certificate_28_q certificate_28_part_1_E 4 2 certificate_28_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_28_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_28 : FiniteCertificate := .forbid 0 3 1 (.system [[0,7,3,4,5,6],[2]]) (.forbid 0 3 2 (.system [[0,7,8,3,4,5,6],[2]]) (.forbid 0 3 3 (.system [[0,7,8,9,3,2],[6]]) (.forbid 0 1 1 (.system [[0,7,1,2,3,4,5,6]]) (.forbid 0 1 3 (.system [[0,7,8,9,1,2],[6]]) (.forbid 0 1 4 (.system [[0,7,8,9,10,1,2],[6]]) (.forbid 0 1 5 (.system [[0,7,8,9,10,11,1,2],[6]]) (.forbid 0 1 6 (.cycle [0,1,12,11,10,9,8,7]) (certificate_28_part_1))))))))

theorem certificate_28_checked : certificate_28.Valid 7 3 7 certificate_28_q certificate_28_E 4 2 certificate_28_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_28_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_28_valid : certificate_28.Valid 7 3 (patternOrder [[1,3]]) (patternClique [[1,3]]) (patternEdges [[1,3]]) (patternAmount [[1,3]]) (patternEdgeCount [[1,3]]) [] := certificate_28_checked

noncomputable def certificate_29_q : Finset ℕ := ([0,3,6] : List ℕ).toFinset

noncomputable def certificate_29_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(0,3),(0,6),(3,6)]

noncomputable def certificate_29_E : List (ℕ × ℕ) := certificate_29_edges

noncomputable def certificate_29_M : ForbiddenMatrix := []

noncomputable def certificate_29_part_1_E : List (ℕ × ℕ) := certificate_29_E

noncomputable def certificate_29_part_1_M : ForbiddenMatrix := ((0,6,3) :: (((0,6,1) :: (((0,4,1) :: (((0,1,6) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_29_M))))))))))))))))

noncomputable def certificate_29_part_2_E : List (ℕ × ℕ) := certificate_29_part_1_E

noncomputable def certificate_29_part_2_M : ForbiddenMatrix := ((2,6,1) :: (((1,6,5) :: (((1,6,4) :: (((1,6,3) :: (((1,6,2) :: (((1,2,1) :: (((0,6,5) :: (((0,6,4) :: (certificate_29_part_1_M))))))))))))))))

noncomputable def certificate_29_part_3_E : List (ℕ × ℕ) := certificate_29_part_2_E

noncomputable def certificate_29_part_3_M : ForbiddenMatrix := ((1,5,2) :: (((1,5,1) :: (((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (((1,4,1) :: (((1,2,2) :: (((0,2,0) :: (certificate_29_part_2_M))))))))))))))))

noncomputable def certificate_29_part_4_E : List (ℕ × ℕ) := certificate_29_part_3_E

noncomputable def certificate_29_part_4_M : ForbiddenMatrix := ((4,5,2) :: (((4,5,1) :: (((2,5,2) :: (((2,5,1) :: (((2,4,2) :: (((2,4,1) :: (((1,5,4) :: (((1,5,3) :: (certificate_29_part_3_M))))))))))))))))

noncomputable def certificate_29_part_5_E : List (ℕ × ℕ) := certificate_29_part_4_E

noncomputable def certificate_29_part_5_M : ForbiddenMatrix := ((1,2,3) :: (((0,2,4) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((5,6,1) :: (((4,5,4) :: (((4,5,3) :: (certificate_29_part_4_M))))))))))))))))

noncomputable def certificate_29_part_6_E : List (ℕ × ℕ) := (augmentedEdges 7 (certificate_29_part_5_E) 1 3 0)

noncomputable def certificate_29_part_6_M : ForbiddenMatrix := ((0,1,5) :: (((2,3,1) :: (((0,2,5) :: (((0,4,0) :: (((2,4,5) :: (((2,4,3) :: (((1,2,4) :: (certificate_29_part_5_M))))))))))))))

noncomputable def certificate_29_part_6 : FiniteCertificate := .forbid 1 2 5 (.cycle [1,3,2,11,10,9,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,4} 4 2) ∅ 8 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,4} 4 2) ∅ 8 3), .ball 2 (.succ (.zero ∅ 1 1) {0,1,3} 4 2)})

theorem certificate_29_part_6_checked : certificate_29_part_6.Valid 7 3 7 certificate_29_q certificate_29_part_6_E 4 2 certificate_29_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

noncomputable def certificate_29_part_7_E : List (ℕ × ℕ) := certificate_29_part_5_E

noncomputable def certificate_29_part_7_M : ForbiddenMatrix := ((0,3,3) :: (((1,3,0) :: (((2,3,1) :: (((0,2,5) :: (((0,4,0) :: (((2,4,5) :: (((2,4,3) :: (((1,2,4) :: (certificate_29_part_5_M))))))))))))))))

noncomputable def certificate_29_part_8_E : List (ℕ × ℕ) := certificate_29_part_7_E

noncomputable def certificate_29_part_8_M : ForbiddenMatrix := ((2,3,3) :: (((2,3,2) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (certificate_29_part_7_M))))))))))))))))

noncomputable def certificate_29_part_9_E : List (ℕ × ℕ) := certificate_29_part_8_E

noncomputable def certificate_29_part_9_M : ForbiddenMatrix := ((3,6,4) :: (((3,6,3) :: (((0,6,6) :: (((1,4,0) :: (((3,4,4) :: (((3,4,3) :: (((3,4,2) :: (((3,4,1) :: (certificate_29_part_8_M))))))))))))))))

noncomputable def certificate_29_part_10_E : List (ℕ × ℕ) := (augmentedEdges 7 (certificate_29_part_9_E) 2 4 0)

noncomputable def certificate_29_part_10_M : ForbiddenMatrix := ((1,6,1) :: (((1,3,1) :: (((0,6,2) :: (((0,3,2) :: (((0,3,1) :: (((3,6,6) :: (((3,6,5) :: (certificate_29_part_9_M))))))))))))))

noncomputable def certificate_29_part_10 : FiniteCertificate := .forbid 3 6 1 (.cycle [3,0,1,2,4,5,6,7]) (.forbid 3 6 2 (.cycle [3,4,2,1,0,6,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,6} 4 2) ∅ 8 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,6} 4 2) ∅ 8 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,3} 4 2) ∅ 8 3)}))

theorem certificate_29_part_10_checked : certificate_29_part_10.Valid 7 3 7 certificate_29_q certificate_29_part_10_E 4 2 certificate_29_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

noncomputable def certificate_29_part_9 : FiniteCertificate := .forbid 3 6 5 (.system [[0],[3,7,8,9,10,11,6]]) (.forbid 3 6 6 (.system [[0],[3,7,8,9,10,11,12,6]]) (.forbid 2 4 0 (.forbid 0 3 1 (.cycle [0,1,2,4,5,6,3,7]) (.forbid 0 3 2 (.cycle [0,6,5,4,2,3,8,7]) (.forbid 0 6 2 (.cycle [0,1,2,4,3,6,8,7]) (.forbid 1 3 1 (.cycle [1,0,6,5,4,2,3,7]) (.forbid 1 6 1 (.cycle [1,0,3,2,4,5,6,7]) (certificate_29_part_10)))))) (.packing {.ball 0 (.succ (.zero {2,4} 3 2) ∅ 8 3), .ball 1 (.succ (.zero {3,4} 3 2) ∅ 8 3), .ball 2 (.succ (.zero {0,4} 3 2) ∅ 8 3)})))

theorem certificate_29_part_9_checked : certificate_29_part_9.Valid 7 3 7 certificate_29_q certificate_29_part_9_E 4 2 certificate_29_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_10_checked⟩⟩⟩⟩⟩, by decide +kernel⟩⟩⟩

noncomputable def certificate_29_part_8 : FiniteCertificate := .forbid 3 4 1 (.system [[0,1,2,3,7,4,5,6]]) (.forbid 3 4 2 (.system [[0],[3,7,8,4,5,6]]) (.forbid 3 4 3 (.system [[0],[3,7,8,9,4,5,6]]) (.forbid 3 4 4 (.system [[0],[3,7,8,9,10,4,5,6]]) (.forbid 1 4 0 (.forbid 0 3 1 (.cycle [0,6,5,4,1,2,3,7]) (.forbid 0 3 2 (.cycle [0,1,4,5,6,3,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {2,3,4} 4 2) ∅ 8 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,2,4} 4 2) ∅ 8 3), .singleton 2, .ball 4 (.zero ∅ 1 1)}))) (.forbid 0 6 6 (.system [[0,7,8,9,10,11,12,6],[3]]) (.forbid 3 6 3 (.system [[0,1,2,3,7,8,9,6]]) (.forbid 3 6 4 (.system [[0],[3,7,8,9,10,6]]) (certificate_29_part_9))))))))

theorem certificate_29_part_8_checked : certificate_29_part_8.Valid 7 3 7 certificate_29_q certificate_29_part_8_E 4 2 certificate_29_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_9_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_29_part_7 : FiniteCertificate := .forbid 0 3 4 (.system [[0,7,8,9,10,3],[6]]) (.forbid 0 3 5 (.system [[0,7,8,9,10,11,3],[6]]) (.forbid 0 3 6 (.system [[0,7,8,9,10,11,12,3],[6]]) (.forbid 0 4 2 (.system [[0,7,8,4,5,6],[3]]) (.forbid 0 4 3 (.system [[0,7,8,9,4,3],[6]]) (.forbid 0 4 4 (.system [[0,7,8,9,10,4,3],[6]]) (.forbid 2 3 2 (.system [[0,1,2,7,8,3],[6]]) (.forbid 2 3 3 (.system [[0,1,2,7,8,9,3],[6]]) (certificate_29_part_8))))))))

theorem certificate_29_part_7_checked : certificate_29_part_7.Valid 7 3 7 certificate_29_q certificate_29_part_7_E 4 2 certificate_29_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_8_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_29_part_5 : FiniteCertificate := .forbid 1 2 4 (.system [[0,1,7,8,9,10,2,3],[6]]) (.forbid 2 4 3 (.system [[0,1,2,7,8,9,4,3],[6]]) (.forbid 2 4 5 (.cycle [2,3,4,11,10,9,8,7]) (.forbid 0 4 0 (.forbid 1 4 5 (.cycle [1,0,4,11,10,9,8,7]) (.forbid 2 4 4 (.cycle [2,1,0,4,10,9,8,7]) (.packing {.ball 1 (.succ (.zero ∅ 1 1) {2,4,5} 4 2), .ball 4 (.succ (.succ (.zero ∅ 1 1) {1,2,5} 4 2) ∅ 8 3), .ball 2 (.succ (.zero ∅ 1 1) {1,4,5} 4 2), .singleton 5}))) (.forbid 0 2 5 (.system [[0,7,8,9,10,11,2,3],[6]]) (.forbid 2 3 1 (.system [[0,1,2,7,3,4,5,6]]) (.forbid 1 3 0 (.forbid 0 1 5 (.cycle [0,3,1,11,10,9,8,7]) (certificate_29_part_6)) (.forbid 0 3 3 (.system [[0,7,8,9,3,4,5,6]]) (certificate_29_part_7))))))))

theorem certificate_29_part_5_checked : certificate_29_part_5.Valid 7 3 7 certificate_29_q certificate_29_part_5_E 4 2 certificate_29_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_6_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_29_part_4 : FiniteCertificate := .forbid 4 5 3 (.system [[0],[3,4,7,8,9,5,6]]) (.forbid 4 5 4 (.system [[0],[3,4,7,8,9,10,5,6]]) (.forbid 5 6 1 (.system [[0,1,2,3,4,5,7,6]]) (.forbid 0 2 1 (.forbid 1 3 0 (.cycle [1,2,7,0,6,5,4,3]) (.forbid 1 4 0 (.cycle [1,0,7,2,3,6,5,4]) (.forbid 1 5 0 (.cycle [1,2,7,0,6,3,4,5]) (.packing {.ball 1 (.succ (.zero {3,4,5} 3 2) {2} 8 3), .ball 4 (.succ (.zero {1} 1 1) {0,1,2,5} 4 2), .ball 5 (.succ (.zero {1} 1 1) {1,2,4,6} 4 2), .singleton 2})))) (.forbid 0 2 2 (.system [[0,7,8,2,3,4,5,6]]) (.forbid 0 2 3 (.system [[0,7,8,9,2,3],[6]]) (.forbid 0 2 4 (.system [[0,7,8,9,10,2,3],[6]]) (.forbid 1 2 3 (.system [[0,1,7,8,9,2,3],[6]]) (certificate_29_part_5))))))))

theorem certificate_29_part_4_checked : certificate_29_part_4.Valid 7 3 7 certificate_29_q certificate_29_part_4_E 4 2 certificate_29_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_29_part_3 : FiniteCertificate := .forbid 1 5 3 (.system [[0,1,7,8,9,5,4,3],[6]]) (.forbid 1 5 4 (.system [[0,1,7,8,9,10,5,6],[3]]) (.forbid 2 4 1 (.system [[0,1,2,7,4,3],[6]]) (.forbid 2 4 2 (.system [[0,1,2,7,8,4,3],[6]]) (.forbid 2 5 1 (.system [[0,1,2,7,5,4,3],[6]]) (.forbid 2 5 2 (.system [[0,1,2,7,8,5,4,3],[6]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,7,5,6]]) (.forbid 4 5 2 (.system [[0],[3,4,7,8,5,6]]) (certificate_29_part_4))))))))

theorem certificate_29_part_3_checked : certificate_29_part_3.Valid 7 3 7 certificate_29_q certificate_29_part_3_E 4 2 certificate_29_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_29_part_2 : FiniteCertificate := .forbid 0 2 0 (.forbid 0 1 5 (.cycle [0,2,1,11,10,9,8,7]) (.forbid 0 6 2 (.cycle [0,2,3,4,5,6,8,7]) (.forbid 1 6 1 (.cycle [1,0,2,3,4,5,6,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,4,6} 4 2) ∅ 8 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,6} 4 2) ∅ 8 3), .ball 6 (.succ (.zero ∅ 1 1) {0,1,2} 4 2)})))) (.forbid 1 2 2 (.system [[0,1,7,8,2,3],[6]]) (.forbid 1 4 1 (.system [[0,1,7,4,5,6],[3]]) (.forbid 1 4 2 (.system [[0,1,7,8,4,3],[6]]) (.forbid 1 4 3 (.system [[0,1,7,8,9,4,3],[6]]) (.forbid 1 4 4 (.system [[0,1,7,8,9,10,4,3],[6]]) (.forbid 1 5 1 (.system [[0,1,7,5,4,3],[6]]) (.forbid 1 5 2 (.system [[0,1,7,8,5,4,3],[6]]) (certificate_29_part_3))))))))

theorem certificate_29_part_2_checked : certificate_29_part_2.Valid 7 3 7 certificate_29_q certificate_29_part_2_E 4 2 certificate_29_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_29_part_1 : FiniteCertificate := .forbid 0 6 4 (.system [[0,7,8,9,10,6],[3]]) (.forbid 0 6 5 (.system [[0,7,8,9,10,11,6],[3]]) (.forbid 1 2 1 (.system [[0,1,7,2,3,4,5,6]]) (.forbid 1 6 2 (.system [[0,1,7,8,6,5,4,3]]) (.forbid 1 6 3 (.system [[0,1,7,8,9,6],[3]]) (.forbid 1 6 4 (.system [[0,1,7,8,9,10,6],[3]]) (.forbid 1 6 5 (.system [[0,1,7,8,9,10,11,6],[3]]) (.forbid 2 6 1 (.system [[0,1,2,7,6,5,4,3]]) (certificate_29_part_2))))))))

theorem certificate_29_part_1_checked : certificate_29_part_1.Valid 7 3 7 certificate_29_q certificate_29_part_1_E 4 2 certificate_29_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def certificate_29 : FiniteCertificate := .forbid 0 1 1 (.system [[0,7,1,2,3,4,5,6]]) (.forbid 0 1 2 (.system [[0,7,8,1,2,3],[6]]) (.forbid 0 1 3 (.system [[0,7,8,9,1,2,3],[6]]) (.forbid 0 1 4 (.system [[0,7,8,9,10,1,2,3],[6]]) (.forbid 0 1 6 (.cycle [0,1,12,11,10,9,8,7]) (.forbid 0 4 1 (.system [[3,2,1,0,7,4,5,6]]) (.forbid 0 6 1 (.cycle [0,1,2,3,4,5,6,7]) (.forbid 0 6 3 (.system [[3,2,1,0,7,8,9,6]]) (certificate_29_part_1))))))))

theorem certificate_29_checked : certificate_29.Valid 7 3 7 certificate_29_q certificate_29_E 4 2 certificate_29_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_29_valid : certificate_29.Valid 7 3 (patternOrder [[2,2]]) (patternClique [[2,2]]) (patternEdges [[2,2]]) (patternAmount [[2,2]]) (patternEdgeCount [[2,2]]) [] := certificate_29_checked

noncomputable def certificate_30_q : Finset ℕ := ([0,1,2,3] : List ℕ).toFinset
noncomputable def certificate_30_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

noncomputable def certificate_30 : FiniteCertificate := .forbid 0 1 1 (.system [[0,4,1],[2],[3]]) (.forbid 0 1 2 (.system [[0,4,5,1],[2],[3]]) (.forbid 0 1 3 (.system [[0,4,5,6,1],[2],[3]]) (.forbid 0 1 4 (.system [[0,4,5,6,7,1],[2],[3]]) (.forbid 0 2 1 (.system [[0,4,2],[1],[3]]) (.forbid 0 2 2 (.system [[0,4,5,2],[1],[3]]) (.forbid 0 2 3 (.system [[0,4,5,6,2],[1],[3]]) (.forbid 0 2 4 (.system [[0,4,5,6,7,2],[1],[3]]) (.forbid 1 2 1 (.system [[0],[1,4,2],[3]]) (.forbid 1 2 2 (.system [[0],[1,4,5,2],[3]]) (.forbid 1 2 3 (.system [[0],[1,4,5,6,2],[3]]) (.forbid 1 2 4 (.system [[0],[1,4,5,6,7,2],[3]]) (.packing {.ball 0 (.succ (.zero ∅ 4 2) ∅ 11 3), .ball 1 (.succ (.zero ∅ 4 2) ∅ 11 3), .ball 2 (.succ (.zero ∅ 4 2) ∅ 11 3)}))))))))))))

theorem certificate_30_checked : certificate_30.Valid 7 4 4 certificate_30_q certificate_30_edges 0 0 [] := by decide +kernel
theorem certificate_30_valid : certificate_30.Valid 7 4 (patternOrder [[],[],[],[]]) (patternClique [[],[],[],[]]) (patternEdges [[],[],[],[]]) (patternAmount [[],[],[],[]]) (patternEdgeCount [[],[],[],[]]) [] := certificate_30_checked

noncomputable def certificate_31_q : Finset ℕ := ([0,1,2,4] : List ℕ).toFinset
noncomputable def certificate_31_edges : List (ℕ × ℕ) := [(2,3),(3,4),(0,1),(0,2),(0,4),(1,2),(1,4),(2,4)]

noncomputable def certificate_31 : FiniteCertificate := .forbid 0 1 1 (.system [[0,5,1],[2,3,4]]) (.forbid 0 1 2 (.system [[0,5,6,1],[2],[4]]) (.forbid 0 1 3 (.system [[0,5,6,7,1],[2],[4]]) (.forbid 0 1 4 (.system [[0,5,6,7,8,1],[2],[4]]) (.forbid 0 1 5 (.system [[0,5,6,7,8,9,1],[2],[4]]) (.forbid 0 1 6 (.system [[0,5,6,7,8,9,10,1],[2],[4]]) (.forbid 0 2 1 (.system [[0,5,2,3,4],[1]]) (.forbid 0 2 2 (.system [[0,5,6,2],[1],[4]]) (.forbid 0 2 3 (.system [[0,5,6,7,2],[1],[4]]) (.forbid 0 2 4 (.system [[0,5,6,7,8,2],[1],[4]]) (.forbid 0 2 5 (.system [[0,5,6,7,8,9,2],[1],[4]]) (.forbid 0 2 6 (.system [[0,5,6,7,8,9,10,2],[1],[4]]) (.forbid 1 2 1 (.system [[0],[1,5,2,3,4]]) (.forbid 1 2 2 (.system [[0],[1,5,6,2],[4]]) (.forbid 1 2 3 (.system [[0],[1,5,6,7,2],[4]]) (.forbid 1 2 4 (.system [[0],[1,5,6,7,8,2],[4]]) (.forbid 1 2 5 (.system [[0],[1,5,6,7,8,9,2],[4]]) (.forbid 1 2 6 (.system [[0],[1,5,6,7,8,9,10,2],[4]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 3 1) {1,2} 5 2) ∅ 10 3), .ball 1 (.succ (.succ (.zero ∅ 3 1) {0,2} 5 2) ∅ 10 3), .ball 2 (.succ (.succ (.zero ∅ 3 1) {0,1} 5 2) ∅ 10 3)}))))))))))))))))))

theorem certificate_31_checked : certificate_31.Valid 7 4 5 certificate_31_q certificate_31_edges 1 1 [] := by decide +kernel
theorem certificate_31_valid : certificate_31.Valid 7 4 (patternOrder [[],[],[1]]) (patternClique [[],[],[1]]) (patternEdges [[],[],[1]]) (patternAmount [[],[],[1]]) (patternEdgeCount [[],[],[1]]) [] := certificate_31_checked

end CycleClique

end OAI
