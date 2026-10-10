import OAI.InformationTheory.SecretKey.ChoiTransfer

namespace OAI

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace ZeroKey.ChoiTransfer

lemma cp_of_channelCP {a b : ℕ}
    {F : ChannelCompletion.Map (Fin a) (Fin b)} (hF : ChannelCompletion.CP F) :
    CompletelyPositive F := by
  intro k X hX
  exact hF (Fin k) X hX

lemma ppt_of_channelPPT {a b : ℕ}
    {F : ChannelCompletion.Map (Fin a) (Fin b)} (hF : ChannelCompletion.PPT F) :
    PPTType F :=
  ⟨cp_of_channelCP hF.1,
    cp_of_channelCP (TensorCriterion.ppt_input_transpose hF).1⟩

theorem publishedPPT {a b c : ℕ}
    {F : ChannelCompletion.Map (Fin a) (Fin b)}
    {G : ChannelCompletion.Map (Fin b) (Fin c)}
    (hF : ChannelCompletion.PPT F) (hG : ChannelCompletion.PPT G) :
    PublishedPPT F G := by
  refine ⟨ppt_of_channelPPT ?_, ppt_of_channelPPT hG⟩
  exact TensorCriterion.ppt_output_transpose
    (TensorCriterion.ppt_input_transpose (TensorCriterion.ppt_hsAdjoint hF))

lemma matrixUnit_single {a : ℕ} (i j : Fin a) :
    matrixUnit i j = Matrix.single i j (1 : ℂ) := by
  ext x y
  simp [matrixUnit, Matrix.single_apply, ite_and, eq_comm]

lemma sharp_matrixUnit {a b : ℕ}
    {F : ChannelCompletion.Map (Fin a) (Fin b)} (hF : ChannelCompletion.CP F)
    (x y : Fin b) (i j : Fin a) :
    sharp F (matrixUnit x y) i j = F (Matrix.single i j 1) x y := by
  change TensorCriterion.hsAdjoint F (matrixUnit x y)ᵀ j i = _
  rw [matrixUnit_single, Matrix.transpose_single, TensorCriterion.hsAdjoint_single]
  exact (ChannelCompletion.cp_choi hF).isHermitian.apply (i, x) (j, y)

theorem publishedTransfer {a b c : ℕ}
    (F : ChannelCompletion.Map (Fin a) (Fin b))
    (G : ChannelCompletion.Map (Fin b) (Fin c))
    (hF : ChannelCompletion.CP F) : PublishedTransfer F G := by
  ext ⟨i, k⟩ ⟨j, l⟩
  change G (F (Matrix.single i j 1)) k l = _
  rw [linearMap_matrix_units_apply]
  simp [tensorMap, outer, omega, ite_mul, mul_ite, sharp_matrixUnit hF]

end ZeroKey.ChoiTransfer

end

end OAI
