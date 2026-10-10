import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates007
import OAI.Combinatorics.Ramsey.CycleClique.Certificates008
import OAI.Combinatorics.Ramsey.CycleClique.Certificates009
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

noncomputable def patterns_11_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]],[[],[],[],[1]],[[],[],[],[2]],[[],[],[],[3]],[[],[],[],[4]],[[],[],[],[5]],[[],[],[],[6]],[[],[],[1,1]],[[],[],[1,2]],[[],[],[1,3]],[[],[],[1,4]],[[],[],[1,5]],[[],[],[2,2]],[[],[],[2,3]],[[],[],[2,4]],[[],[],[3,3]]]

theorem patterns_11_5_0_verified : ∀ D ∈ patterns_11_5_0, PatternVerified 11 5 D := by

  simp only [patterns_11_5_0, List.forall_mem_cons]

  exact ⟨⟨certificate_219, certificate_219_valid⟩, ⟨⟨certificate_220, certificate_220_valid⟩, ⟨⟨certificate_221, certificate_221_valid⟩, ⟨⟨certificate_222, certificate_222_valid⟩, ⟨⟨certificate_223, certificate_223_valid⟩, ⟨⟨certificate_224, certificate_224_valid⟩, ⟨⟨certificate_225, certificate_225_valid⟩, ⟨⟨certificate_226, certificate_226_valid⟩, ⟨⟨certificate_227, certificate_227_valid⟩, ⟨⟨certificate_228, certificate_228_valid⟩, ⟨⟨certificate_229, certificate_229_valid⟩, ⟨⟨certificate_230, certificate_230_valid⟩, ⟨⟨certificate_231, certificate_231_valid⟩, ⟨⟨certificate_232, certificate_232_valid⟩, ⟨⟨certificate_233, certificate_233_valid⟩, ⟨⟨certificate_234, certificate_234_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_11_5_1 : List (List (List ℕ)) := [[[],[1],[1]],[[],[1],[2]],[[],[1],[3]],[[],[1],[4]],[[],[1],[5]],[[],[1,1,1]],[[],[1,1,2]],[[],[1,1,3]],[[],[1,1,4]],[[],[1,2,1]],[[],[1,2,2]],[[],[1,2,3]],[[],[1,3,1]],[[],[1,3,2]],[[],[1,4,1]],[[],[2],[2]]]

theorem patterns_11_5_1_verified : ∀ D ∈ patterns_11_5_1, PatternVerified 11 5 D := by

  simp only [patterns_11_5_1, List.forall_mem_cons]

  exact ⟨⟨certificate_235, certificate_235_valid⟩, ⟨⟨certificate_236, certificate_236_valid⟩, ⟨⟨certificate_237, certificate_237_valid⟩, ⟨⟨certificate_238, certificate_238_valid⟩, ⟨⟨certificate_239, certificate_239_valid⟩, ⟨⟨certificate_240, certificate_240_valid⟩, ⟨⟨certificate_241, certificate_241_valid⟩, ⟨⟨certificate_242, certificate_242_valid⟩, ⟨⟨certificate_243, certificate_243_valid⟩, ⟨⟨certificate_244, certificate_244_valid⟩, ⟨⟨certificate_245, certificate_245_valid⟩, ⟨⟨certificate_246, certificate_246_valid⟩, ⟨⟨certificate_247, certificate_247_valid⟩, ⟨⟨certificate_248, certificate_248_valid⟩, ⟨⟨certificate_249, certificate_249_valid⟩, ⟨⟨certificate_250, certificate_250_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_11_5_2 : List (List (List ℕ)) := [[[],[2],[3]],[[],[2],[4]],[[],[2,1,2]],[[],[2,1,3]],[[],[2,2,2]],[[],[3],[3]],[[1],[1,1]],[[1],[1,2]],[[1],[1,3]],[[1],[1,4]],[[1],[2,2]],[[1],[2,3]],[[1,1],[2]],[[1,1],[3]],[[1,1],[4]],[[1,1,1,1]]]

theorem patterns_11_5_2_verified : ∀ D ∈ patterns_11_5_2, PatternVerified 11 5 D := by

  simp only [patterns_11_5_2, List.forall_mem_cons]

  exact ⟨⟨certificate_251, certificate_251_valid⟩, ⟨⟨certificate_252, certificate_252_valid⟩, ⟨⟨certificate_253, certificate_253_valid⟩, ⟨⟨certificate_254, certificate_254_valid⟩, ⟨⟨certificate_255, certificate_255_valid⟩, ⟨⟨certificate_256, certificate_256_valid⟩, ⟨⟨certificate_257, certificate_257_valid⟩, ⟨⟨certificate_258, certificate_258_valid⟩, ⟨⟨certificate_259, certificate_259_valid⟩, ⟨⟨certificate_260, certificate_260_valid⟩, ⟨⟨certificate_261, certificate_261_valid⟩, ⟨⟨certificate_262, certificate_262_valid⟩, ⟨⟨certificate_263, certificate_263_valid⟩, ⟨⟨certificate_264, certificate_264_valid⟩, ⟨⟨certificate_265, certificate_265_valid⟩, ⟨⟨certificate_266, certificate_266_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_11_5_3 : List (List (List ℕ)) := [[[1,1,1,2]],[[1,1,1,3]],[[1,1,2,1]],[[1,1,2,2]],[[1,1,3,1]],[[1,2],[2]],[[1,2],[3]],[[1,2,1,2]],[[1,2,2,1]],[[1,3],[2]],[[2],[2,2]],[[2,1,1,2]]]

theorem patterns_11_5_3_verified : ∀ D ∈ patterns_11_5_3, PatternVerified 11 5 D := by

  simp only [patterns_11_5_3, List.forall_mem_cons]

  exact ⟨⟨certificate_267, certificate_267_valid⟩, ⟨⟨certificate_268, certificate_268_valid⟩, ⟨⟨certificate_269, certificate_269_valid⟩, ⟨⟨certificate_270, certificate_270_valid⟩, ⟨⟨certificate_271, certificate_271_valid⟩, ⟨⟨certificate_272, certificate_272_valid⟩, ⟨⟨certificate_273, certificate_273_valid⟩, ⟨⟨certificate_274, certificate_274_valid⟩, ⟨⟨certificate_275, certificate_275_valid⟩, ⟨⟨certificate_276, certificate_276_valid⟩, ⟨⟨certificate_277, certificate_277_valid⟩, ⟨⟨certificate_278, certificate_278_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_11_5 : List (List (List ℕ)) := patterns_11_5_0 ++ (patterns_11_5_1 ++ (patterns_11_5_2 ++ (patterns_11_5_3 ++ ([]))))

theorem patterns_11_5_verified : ∀ D ∈ patterns_11_5, PatternVerified 11 5 D := by

  simp only [patterns_11_5, List.forall_mem_append]

  exact ⟨patterns_11_5_0_verified, ⟨patterns_11_5_1_verified, ⟨patterns_11_5_2_verified, ⟨patterns_11_5_3_verified, by simp⟩⟩⟩⟩

theorem patterns_11_5_coverage : patternChoices 5 6 [] = patterns_11_5 := by decide +kernel

theorem finite_patterns_11_5 : ∀ D ∈ patternChoices 5 (11-5) [], PatternVerified 11 5 D := by

  rw [patterns_11_5_coverage]

  exact patterns_11_5_verified

end CycleClique

end OAI
