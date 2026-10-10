import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropSurgeryConnected
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropSurgeryEstimates
import OAI.Analysis.JiangSu.CStarAlgebras.EndpointTestCutoffs

namespace OAI


noncomputable section
namespace JiangSuConstruction
open MatrixTensor FourEdgeSurgery
open scoped CStarAlgebra ComplexOrder TensorProduct

variable {p q : ℕ}

lemma squareTensorMap_left_eval (f : DimensionDrop p q) (s t : Interval) :
    (squareTensorMap p q p q (f ⊗ₜ[ℂ] 1)).val (s,t)=MatrixTensor.left (f.val s) := by
  change MatrixTensor.left (f.val s)*MatrixTensor.right (1:TensorMat p q)=_
  rw [map_one,mul_one]
lemma squareTensorMap_right_eval (f : DimensionDrop p q) (s t : Interval) :
    (squareTensorMap p q p q (1 ⊗ₜ[ℂ] f)).val (s,t)=MatrixTensor.right (f.val t) := by
  change MatrixTensor.left (1:TensorMat p q)*MatrixTensor.right (f.val t)=_
  rw [map_one,one_mul]

theorem square_connected_half_flip_of_matching
    (F : Finset (DimensionDrop p q)) {ε : ℝ} (hε : 0<ε)
    (W : C(Interval×Interval,unitary (TensorMat p q)))
    (hWd : ∀ s,W (s,s)=1)
    (hW : ∀ f∈F,∀ s t,‖unitaryConjugation (W (s,t)) (f.val s)-f.val t‖<ε/42) :
    ∃ u : unitary (Square p q p q),Joined 1 u ∧ ∀ f∈F,
      ‖(u:Square p q p q)*squareTensorMap p q p q (f ⊗ₜ[ℂ] 1)*star (u:Square p q p q)-
        squareTensorMap p q p q (1 ⊗ₜ[ℂ] f)‖<ε := by
  classical
  have hδ : 0<ε/42 := by positivity
  have h01 : leftEndpoint≠rightEndpoint := by
    intro he
    have := congrArg Subtype.val he
    norm_num [leftEndpoint,rightEndpoint] at this
  obtain ⟨a,b,ha0,ha1,hb0,hb1,ha,hb⟩ := EndpointPartition.exists_endpoint_cutoffs
    leftEndpoint rightEndpoint h01 (fun f : F => f.val.val) hδ
  let u := surgeryUnitary W a b ha0 ha1 hb0 hb1 (hWd _) (hWd _)
  refine ⟨u,surgeryUnitary_joined a b ha0 ha1 hb0 hb1 W hWd,?_⟩
  intro f hf
  have he : ‖(u:Square p q p q)*squareTensorMap p q p q (f ⊗ₜ[ℂ] 1)*star (u:Square p q p q)-
      squareTensorMap p q p q (1 ⊗ₜ[ℂ] f)‖≤16*(ε/42)+5*(ε/42) := by
    change ‖((u:Square p q p q)*squareTensorMap p q p q (f ⊗ₜ[ℂ] 1)*star (u:Square p q p q)-
      squareTensorMap p q p q (1 ⊗ₜ[ℂ] f)).val‖≤_
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    rintro ⟨s,t⟩
    change ‖(surgerySection W a b (s,t):MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))*
      (squareTensorMap p q p q (f ⊗ₜ[ℂ] 1)).val (s,t)*
      star (surgerySection W a b (s,t):MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))-
      (squareTensorMap p q p q (1 ⊗ₜ[ℂ] f)).val (s,t)‖≤_
    rw [squareTensorMap_left_eval,squareTensorMap_right_eval]
    exact surgerySection_control W a b f hδ.le hδ.le
      (fun s hs => (ha s hs ⟨f,hf⟩).le) (fun s hs => (hb s hs ⟨f,hf⟩).le)
      (fun s t => (hW f hf s t).le) s t
  exact he.trans_lt (by linarith)

end JiangSuConstruction

end

end OAI
