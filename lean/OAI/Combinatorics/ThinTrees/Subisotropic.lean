import OAI.Combinatorics.ThinTrees.Padding

namespace OAI

universe uI uD

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} [Fintype I] [Fintype D] [DecidableEq D]

theorem subisotropic_binary (v : I → Bool → D → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hiso : (∑i, ∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (v i b) (v i b)) ≤ 1)
    (hsize : ∀i, (∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (v i b) (v i b)).trace ≤ ε) :
    ∃f : I → Bool, (∑i, Matrix.vecMulVec (v i (f i)) (v i (f i))) ≤
      (∑i, ∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (v i b) (v i b)) +
      (2*Real.sqrt ε+ε) • (1 : Matrix D D ℝ) := by
  classical
  let M := ∑i, ∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (v i b) (v i b)
  have hR : (1-M).PosSemidef := (sub_nonneg.mpr hiso).posSemidef
  obtain ⟨N,u,hu,hutr⟩ := deterministic_padding (1-M) hR hε
  let V : I ⊕ (Fin N × D) → Bool → D → ℝ := Sum.elim v (fun p _ => u p)
  have hprob : ∀i : I ⊕ (Fin N × D), ∑_b : Bool, (1/2 : ℝ)=1 := by
    intro i
    norm_num [Fintype.sum_bool]
  have hdet (p : Fin N × D) :
      (∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (V (.inr p) b) (V (.inr p) b))=
        Matrix.vecMulVec (u p) (u p) := by
    simp only [V,Sum.elim_inr,Fintype.sum_bool,←add_smul]
    norm_num
  have hiso' : (∑i, ∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (V i b) (V i b))=1 := by
    rw [Fintype.sum_sum_type]
    simp only [hdet,V,Sum.elim_inl]
    change M+(∑p, Matrix.vecMulVec (u p) (u p))=1
    rw [hu]
    abel
  have hsize' : ∀i, (∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (V i b) (V i b)).trace ≤ ε := by
    intro i
    cases i with
    | inl i => exact hsize i
    | inr p => rw [hdet]; exact hutr p
  obtain ⟨f,hf⟩ := small_vectors (fun _ _ => (1/2 : ℝ)) V (by intros; norm_num) hprob hiso' hε hsize'
  rw [Fintype.sum_sum_type] at hf
  simp only [V,Sum.elim_inl,Sum.elim_inr] at hf
  rw [hu] at hf
  refine ⟨fun i => f (.inl i),?_⟩
  change (∑i, Matrix.vecMulVec (v i (f (.inl i))) (v i (f (.inl i)))) ≤
    M+(2*Real.sqrt ε+ε) • (1 : Matrix D D ℝ)
  have hβ : (1+Real.sqrt ε)^2=1+(2*Real.sqrt ε+ε) := by
    nlinarith [Real.sq_sqrt hε.le]
  have he : (1+Real.sqrt ε)^2 • (1 : Matrix D D ℝ) =
      (M+(2*Real.sqrt ε+ε) • (1 : Matrix D D ℝ))+(1-M) := by
    rw [hβ,add_smul,one_smul]
    abel
  rw [he] at hf
  exact (add_le_add_iff_right (1-M)).mp hf

end StrongThinTree.MSS

end
end

end OAI
