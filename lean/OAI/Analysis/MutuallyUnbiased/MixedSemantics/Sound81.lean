import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons81

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5184 node5184Labels = Sparse.eval nodeValue5184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5184) = mixedMoment B node5184 node5184Labels := rfl
  simpa [nodeValue5184, Sparse.eval] using hc.symm

theorem sound5185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5185 node5185Labels = Sparse.eval nodeValue5185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5185) = mixedMoment B node5185 node5185Labels := rfl
  simpa [nodeValue5185, Sparse.eval] using hc.symm

theorem sound5186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5186 node5186Labels = Sparse.eval nodeValue5186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5186) = mixedMoment B node5186 node5186Labels := rfl
  simpa [nodeValue5186, Sparse.eval] using hc.symm

theorem sound5187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5187 node5187Labels = Sparse.eval nodeValue5187 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5187) = mixedMoment B node5187 node5187Labels := rfl
  simpa [nodeValue5187, Sparse.eval] using hc.symm

theorem sound5188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5188 node5188Labels = Sparse.eval nodeValue5188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5188) = mixedMoment B node5188 node5188Labels := rfl
  simpa [nodeValue5188, Sparse.eval] using hc.symm

theorem sound5189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5189 node5189Labels = Sparse.eval nodeValue5189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5189) = mixedMoment B node5189 node5189Labels := rfl
  simpa [nodeValue5189, Sparse.eval] using hc.symm

theorem sound5190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5190 node5190Labels = Sparse.eval nodeValue5190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5190) = mixedMoment B node5190 node5190Labels := rfl
  simpa [nodeValue5190, Sparse.eval] using hc.symm

theorem sound5191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5191 node5191Labels = Sparse.eval nodeValue5191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5191) = mixedMoment B node5191 node5191Labels := rfl
  simpa [nodeValue5191, Sparse.eval] using hc.symm

theorem sound5192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5192 node5192Labels = Sparse.eval nodeValue5192 (mixedVector B) := by
  have h := singleton5192 B _hB
  rw [sound2853 B _hB _hF, sound3620 B _hB _hF] at h
  norm_num [nodeValue5192, nodeValue2853, nodeValue3620, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5193 node5193Labels = Sparse.eval nodeValue5193 (mixedVector B) := by
  have h := singleton5193 B _hB
  rw [sound2856 B _hB _hF, sound3630 B _hB _hF] at h
  norm_num [nodeValue5193, nodeValue2856, nodeValue3630, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5194 node5194Labels = Sparse.eval nodeValue5194 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5194) = mixedMoment B node5194 node5194Labels := rfl
  simpa [nodeValue5194, Sparse.eval] using hc.symm

theorem sound5195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5195 node5195Labels = Sparse.eval nodeValue5195 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5195) = mixedMoment B node5195 node5195Labels := rfl
  simpa [nodeValue5195, Sparse.eval] using hc.symm

theorem sound5196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5196 node5196Labels = Sparse.eval nodeValue5196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5196) = mixedMoment B node5196 node5196Labels := rfl
  simpa [nodeValue5196, Sparse.eval] using hc.symm

theorem sound5197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5197 node5197Labels = Sparse.eval nodeValue5197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5197) = mixedMoment B node5197 node5197Labels := rfl
  simpa [nodeValue5197, Sparse.eval] using hc.symm

theorem sound5198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5198 node5198Labels = Sparse.eval nodeValue5198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5198) = mixedMoment B node5198 node5198Labels := rfl
  simpa [nodeValue5198, Sparse.eval] using hc.symm

theorem sound5199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5199 node5199Labels = Sparse.eval nodeValue5199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5199) = mixedMoment B node5199 node5199Labels := rfl
  simpa [nodeValue5199, Sparse.eval] using hc.symm

theorem sound5200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5200 node5200Labels = Sparse.eval nodeValue5200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5200) = mixedMoment B node5200 node5200Labels := rfl
  simpa [nodeValue5200, Sparse.eval] using hc.symm

theorem sound5201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5201 node5201Labels = Sparse.eval nodeValue5201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5201) = mixedMoment B node5201 node5201Labels := rfl
  simpa [nodeValue5201, Sparse.eval] using hc.symm

theorem sound5202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5202 node5202Labels = Sparse.eval nodeValue5202 (mixedVector B) := by
  have h := singleton5202 B _hB
  rw [sound2880 B _hB _hF, sound3617 B _hB _hF] at h
  norm_num [nodeValue5202, nodeValue2880, nodeValue3617, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5203 node5203Labels = Sparse.eval nodeValue5203 (mixedVector B) := by
  have h := singleton5203 B _hB
  rw [sound2884 B _hB _hF, sound3621 B _hB _hF] at h
  norm_num [nodeValue5203, nodeValue2884, nodeValue3621, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5204 node5204Labels = Sparse.eval nodeValue5204 (mixedVector B) := by
  have h := singleton5204 B _hB
  rw [sound2881 B _hB _hF, sound3624 B _hB _hF] at h
  norm_num [nodeValue5204, nodeValue2881, nodeValue3624, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5205 node5205Labels = Sparse.eval nodeValue5205 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5205) = mixedMoment B node5205 node5205Labels := rfl
  simpa [nodeValue5205, Sparse.eval] using hc.symm

theorem sound5206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5206 node5206Labels = Sparse.eval nodeValue5206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5206) = mixedMoment B node5206 node5206Labels := rfl
  simpa [nodeValue5206, Sparse.eval] using hc.symm

theorem sound5207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5207 node5207Labels = Sparse.eval nodeValue5207 (mixedVector B) := by
  have h := singleton5207 B _hB
  rw [sound2889 B _hB _hF, sound3631 B _hB _hF] at h
  norm_num [nodeValue5207, nodeValue2889, nodeValue3631, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5208 node5208Labels = Sparse.eval nodeValue5208 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5208) = mixedMoment B node5208 node5208Labels := rfl
  simpa [nodeValue5208, Sparse.eval] using hc.symm

theorem sound5209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5209 node5209Labels = Sparse.eval nodeValue5209 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5209) = mixedMoment B node5209 node5209Labels := rfl
  simpa [nodeValue5209, Sparse.eval] using hc.symm

theorem sound5210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5210 node5210Labels = Sparse.eval nodeValue5210 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5210) = mixedMoment B node5210 node5210Labels := rfl
  simpa [nodeValue5210, Sparse.eval] using hc.symm

theorem sound5211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5211 node5211Labels = Sparse.eval nodeValue5211 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5211) = mixedMoment B node5211 node5211Labels := rfl
  simpa [nodeValue5211, Sparse.eval] using hc.symm

theorem sound5212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5212 node5212Labels = Sparse.eval nodeValue5212 (mixedVector B) := by
  have h := singleton5212 B _hB
  rw [sound2839 B _hB _hF] at h
  norm_num [nodeValue5212, nodeValue2839, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5213 node5213Labels = Sparse.eval nodeValue5213 (mixedVector B) := by
  have h := singleton5213 B _hB
  rw [sound2840 B _hB _hF] at h
  norm_num [nodeValue5213, nodeValue2840, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5214 node5214Labels = Sparse.eval nodeValue5214 (mixedVector B) := by
  have h := singleton5214 B _hB
  rw [sound2843 B _hB _hF] at h
  norm_num [nodeValue5214, nodeValue2843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5215 node5215Labels = Sparse.eval nodeValue5215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5215) = mixedMoment B node5215 node5215Labels := rfl
  simpa [nodeValue5215, Sparse.eval] using hc.symm

theorem sound5216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5216 node5216Labels = Sparse.eval nodeValue5216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5216) = mixedMoment B node5216 node5216Labels := rfl
  simpa [nodeValue5216, Sparse.eval] using hc.symm

theorem sound5217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5217 node5217Labels = Sparse.eval nodeValue5217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5217) = mixedMoment B node5217 node5217Labels := rfl
  simpa [nodeValue5217, Sparse.eval] using hc.symm

theorem sound5218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5218 node5218Labels = Sparse.eval nodeValue5218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5218) = mixedMoment B node5218 node5218Labels := rfl
  simpa [nodeValue5218, Sparse.eval] using hc.symm

theorem sound5219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5219 node5219Labels = Sparse.eval nodeValue5219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5219) = mixedMoment B node5219 node5219Labels := rfl
  simpa [nodeValue5219, Sparse.eval] using hc.symm

theorem sound5220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5220 node5220Labels = Sparse.eval nodeValue5220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5220) = mixedMoment B node5220 node5220Labels := rfl
  simpa [nodeValue5220, Sparse.eval] using hc.symm

theorem sound5221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5221 node5221Labels = Sparse.eval nodeValue5221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5221) = mixedMoment B node5221 node5221Labels := rfl
  simpa [nodeValue5221, Sparse.eval] using hc.symm

theorem sound5222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5222 node5222Labels = Sparse.eval nodeValue5222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5222) = mixedMoment B node5222 node5222Labels := rfl
  simpa [nodeValue5222, Sparse.eval] using hc.symm

theorem sound5223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5223 node5223Labels = Sparse.eval nodeValue5223 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5223) = mixedMoment B node5223 node5223Labels := rfl
  simpa [nodeValue5223, Sparse.eval] using hc.symm

theorem sound5224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5224 node5224Labels = Sparse.eval nodeValue5224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5224) = mixedMoment B node5224 node5224Labels := rfl
  simpa [nodeValue5224, Sparse.eval] using hc.symm

theorem sound5225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5225 node5225Labels = Sparse.eval nodeValue5225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5225) = mixedMoment B node5225 node5225Labels := rfl
  simpa [nodeValue5225, Sparse.eval] using hc.symm

theorem sound5226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5226 node5226Labels = Sparse.eval nodeValue5226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5226) = mixedMoment B node5226 node5226Labels := rfl
  simpa [nodeValue5226, Sparse.eval] using hc.symm

theorem sound5227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5227 node5227Labels = Sparse.eval nodeValue5227 (mixedVector B) := by
  have h := singleton5227 B _hB
  rw [sound2671 B _hB _hF, sound3390 B _hB _hF] at h
  norm_num [nodeValue5227, nodeValue2671, nodeValue3390, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5228 node5228Labels = Sparse.eval nodeValue5228 (mixedVector B) := by
  have h := singleton5228 B _hB
  rw [sound2672 B _hB _hF, sound3391 B _hB _hF] at h
  norm_num [nodeValue5228, nodeValue2672, nodeValue3391, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5229 node5229Labels = Sparse.eval nodeValue5229 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5229) = mixedMoment B node5229 node5229Labels := rfl
  simpa [nodeValue5229, Sparse.eval] using hc.symm

theorem sound5230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5230 node5230Labels = Sparse.eval nodeValue5230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5230) = mixedMoment B node5230 node5230Labels := rfl
  simpa [nodeValue5230, Sparse.eval] using hc.symm

theorem sound5231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5231 node5231Labels = Sparse.eval nodeValue5231 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5231) = mixedMoment B node5231 node5231Labels := rfl
  simpa [nodeValue5231, Sparse.eval] using hc.symm

theorem sound5232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5232 node5232Labels = Sparse.eval nodeValue5232 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5232) = mixedMoment B node5232 node5232Labels := rfl
  simpa [nodeValue5232, Sparse.eval] using hc.symm

theorem sound5233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5233 node5233Labels = Sparse.eval nodeValue5233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5233) = mixedMoment B node5233 node5233Labels := rfl
  simpa [nodeValue5233, Sparse.eval] using hc.symm

theorem sound5234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5234 node5234Labels = Sparse.eval nodeValue5234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5234) = mixedMoment B node5234 node5234Labels := rfl
  simpa [nodeValue5234, Sparse.eval] using hc.symm

theorem sound5235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5235 node5235Labels = Sparse.eval nodeValue5235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5235) = mixedMoment B node5235 node5235Labels := rfl
  simpa [nodeValue5235, Sparse.eval] using hc.symm

theorem sound5236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5236 node5236Labels = Sparse.eval nodeValue5236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5236) = mixedMoment B node5236 node5236Labels := rfl
  simpa [nodeValue5236, Sparse.eval] using hc.symm

theorem sound5237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5237 node5237Labels = Sparse.eval nodeValue5237 (mixedVector B) := by
  have h := singleton5237 B _hB
  rw [sound2684 B _hB _hF, sound3394 B _hB _hF] at h
  norm_num [nodeValue5237, nodeValue2684, nodeValue3394, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5238 node5238Labels = Sparse.eval nodeValue5238 (mixedVector B) := by
  have h := singleton5238 B _hB
  rw [sound2686 B _hB _hF, sound3397 B _hB _hF] at h
  norm_num [nodeValue5238, nodeValue2686, nodeValue3397, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5239 node5239Labels = Sparse.eval nodeValue5239 (mixedVector B) := by
  simpa only [nodeValue5239, Sparse.eval_nil] using zero5239 B _hB _hF

theorem sound5240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5240 node5240Labels = Sparse.eval nodeValue5240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5240) = mixedMoment B node5240 node5240Labels := rfl
  simpa [nodeValue5240, Sparse.eval] using hc.symm

theorem sound5241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5241 node5241Labels = Sparse.eval nodeValue5241 (mixedVector B) := by
  have h := singleton5241 B _hB
  rw [sound2694 B _hB _hF, sound3493 B _hB _hF] at h
  norm_num [nodeValue5241, nodeValue2694, nodeValue3493, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5242 node5242Labels = Sparse.eval nodeValue5242 (mixedVector B) := by
  simpa only [nodeValue5242, Sparse.eval_nil] using zero5242 B _hB _hF

theorem sound5243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5243 node5243Labels = Sparse.eval nodeValue5243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5243) = mixedMoment B node5243 node5243Labels := rfl
  simpa [nodeValue5243, Sparse.eval] using hc.symm

theorem sound5244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5244 node5244Labels = Sparse.eval nodeValue5244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5244) = mixedMoment B node5244 node5244Labels := rfl
  simpa [nodeValue5244, Sparse.eval] using hc.symm

theorem sound5245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5245 node5245Labels = Sparse.eval nodeValue5245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5245) = mixedMoment B node5245 node5245Labels := rfl
  simpa [nodeValue5245, Sparse.eval] using hc.symm

theorem sound5246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5246 node5246Labels = Sparse.eval nodeValue5246 (mixedVector B) := by
  simpa only [nodeValue5246, Sparse.eval_nil] using zero5246 B _hB _hF

theorem sound5247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5247 node5247Labels = Sparse.eval nodeValue5247 (mixedVector B) := by
  have h := singleton5247 B _hB
  rw [sound2703 B _hB _hF, sound3496 B _hB _hF] at h
  norm_num [nodeValue5247, nodeValue2703, nodeValue3496, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
