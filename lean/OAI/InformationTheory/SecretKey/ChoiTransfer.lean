import OAI.InformationTheory.SecretKey.MatrixBasics
import OAI.Analysis.Quantum.PPTSquare.TensorPositivity

namespace OAI

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace ZeroKey.ChoiTransfer

def sharp {a b : ℕ} (F : ChannelCompletion.Map (Fin a) (Fin b)) :
    Mat b →ₗ[ℂ] Mat a :=
  ChannelCompletion.transposeMap.comp
    ((TensorCriterion.hsAdjoint F).comp ChannelCompletion.transposeMap)

def omega (b : ℕ) : Fin b × Fin b → ℂ :=
  fun i => if i.1 = i.2 then 1 else 0

def PublishedTransfer {a b c : ℕ}
    (F : ChannelCompletion.Map (Fin a) (Fin b))
    (G : ChannelCompletion.Map (Fin b) (Fin c)) : Prop :=
  ChannelCompletion.choi (G.comp F) =
    tensorMap (sharp F) G (outer (omega b) (omega b))

def PublishedPPT {a b c : ℕ}
    (F : ChannelCompletion.Map (Fin a) (Fin b))
    (G : ChannelCompletion.Map (Fin b) (Fin c)) : Prop :=
  PPTType (sharp F) ∧ PPTType G

lemma cp_smul {a b : ℕ} {F : Mat a →ₗ[ℂ] Mat b}
    (hF : CompletelyPositive F) {s : ℂ} (hs : 0 ≤ s) :
    CompletelyPositive (s • F) := by
  intro k X hX
  exact (hF k X hX).smul hs

lemma ppt_smul {a b : ℕ} {F : Mat a →ₗ[ℂ] Mat b}
    (hF : PPTType F) {s : ℂ} (hs : 0 ≤ s) : PPTType (s • F) := by
  refine ⟨cp_smul hF.1 hs, ?_⟩
  have he : (s • F).comp (transposeLinear a) =
      s • (F.comp (transposeLinear a)) := rfl
  rw [he]
  exact cp_smul hF.2 hs

lemma tensorMap_smul_left {a b c d : ℕ} (F : Mat a →ₗ[ℂ] Mat b)
    (G : Mat c →ₗ[ℂ] Mat d) (s : ℂ)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap (s • F) G X = s • tensorMap F G X := by
  ext i j
  simp only [tensorMap, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  ring

def normalize {a b : ℕ} (Z : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :=
  (trace Z)⁻¹ • Z

lemma normalize_density {a b : ℕ}
    {Z : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ}
    (hZ : Z.PosSemidef) (hne : Z ≠ 0) : Density (normalize Z) := by
  have ht : trace Z ≠ 0 := fun h => hne (hZ.trace_eq_zero_iff.mp h)
  refine ⟨hZ.smul (inv_nonneg.mpr hZ.trace_nonneg), ?_⟩
  simp only [normalize, Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ ht]

theorem normalized_inClass_conditional {a b c : ℕ}
    (F : ChannelCompletion.Map (Fin a) (Fin b))
    (G : ChannelCompletion.Map (Fin b) (Fin c))
    (hPPT : PublishedPPT F G) (htransfer : PublishedTransfer F G)
    (hZ : (ChannelCompletion.choi (G.comp F)).PosSemidef)
    (hne : ChannelCompletion.choi (G.comp F) ≠ 0) :
    InClass (normalize (ChannelCompletion.choi (G.comp F))) := by
  let Z := ChannelCompletion.choi (G.comp F)
  refine ⟨normalize_density hZ hne, b, b, (trace Z)⁻¹ • sharp F, G,
    omega b, ppt_smul hPPT.1 (inv_nonneg.mpr hZ.trace_nonneg), hPPT.2, ?_⟩
  rw [tensorMap_smul_left, ← htransfer]
  rfl

end ZeroKey.ChoiTransfer

end

end OAI
