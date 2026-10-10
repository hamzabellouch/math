import OAI.Combinatorics.ThinTrees.Blocks

namespace OAI

universe uI uD

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]

omit [DecidableEq I] in

theorem two_sided_split (w : I → D → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hiso : (∑i, Matrix.vecMulVec (w i) (w i)) ≤ (2 : ℝ) • (1 : Matrix D D ℝ))
    (hsize : ∀i, (Matrix.vecMulVec (w i) (w i)).trace ≤ ε) :
    ∃A : Finset I,
      (1/2 : ℝ) • (∑i, Matrix.vecMulVec (w i) (w i)) -
        (2*Real.sqrt ε+ε) • (1 : Matrix D D ℝ) ≤ ∑i ∈ A, Matrix.vecMulVec (w i) (w i) ∧
      (∑i ∈ A, Matrix.vecMulVec (w i) (w i)) ≤
        (1/2 : ℝ) • (∑i, Matrix.vecMulVec (w i) (w i)) +
        (2*Real.sqrt ε+ε) • (1 : Matrix D D ℝ) := by
  let Smat := ∑i, Matrix.vecMulVec (w i) (w i)
  let τ := 2*Real.sqrt ε+ε
  have hhalf : (1/2 : ℝ) • Smat ≤ (1 : Matrix D D ℝ) := by
    have hh := smul_le_smul_of_nonneg_left hiso (by norm_num : (0:ℝ) ≤ 1/2)
    simpa only [smul_smul,show (1/2:ℝ)*2=1 by norm_num,one_smul] using hh
  have hmean : (∑i, ∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (blockEmbed (w i) b) (blockEmbed (w i) b))=
      Matrix.blockDiagonal (fun _ : Bool => (1/2 : ℝ) • Smat) := by
    simp_rw [blockEmbed_mean]
    rw [←blockDiagonal_sum]
    simp only [Smat,Finset.smul_sum]
  have hmiso : (∑i, ∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (blockEmbed (w i) b) (blockEmbed (w i) b)) ≤ 1 := by
    rw [hmean]
    simpa only [Matrix.blockDiagonal_one] using blockDiagonal_mono
      (fun _ : Bool => (1/2 : ℝ) • Smat) (1 : Bool → Matrix D D ℝ) (fun _ => hhalf)
  have hmsize : ∀i, (∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (blockEmbed (w i) b) (blockEmbed (w i) b)).trace ≤ ε := by
    intro i
    rw [Fintype.sum_bool, Matrix.trace_add]
    simp only [Matrix.trace_smul,smul_eq_mul,blockEmbed_trace]
    linarith [hsize i]
  obtain ⟨f,hf⟩ := subisotropic_binary (fun i b => blockEmbed (w i) b) hε hmiso hmsize
  rw [hmean] at hf
  have hb (b : Bool) : (∑i, if f i=b then Matrix.vecMulVec (w i) (w i) else 0) ≤
      (1/2 : ℝ) • Smat+τ • (1 : Matrix D D ℝ) := by
    have hh := blockDiag_mono hf b
    simpa only [blockDiag_sum,blockEmbed_blockDiag,Matrix.blockDiag_add,Pi.add_apply,
      Matrix.blockDiag_blockDiagonal,Matrix.blockDiag_smul,Pi.smul_apply,Matrix.blockDiag_one,Pi.one_apply] using hh
  let A : Finset I := Finset.univ.filter (fun i => f i=true)
  have hA : (∑i ∈ A, Matrix.vecMulVec (w i) (w i))=
      ∑i, if f i=true then Matrix.vecMulVec (w i) (w i) else 0 := by
    simp only [A,Finset.sum_filter]
  have hcomp : (∑i, if f i=true then Matrix.vecMulVec (w i) (w i) else 0)+
      (∑i, if f i=false then Matrix.vecMulVec (w i) (w i) else 0)=Smat := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases f i <;> simp
  refine ⟨A,?_,?_⟩
  · rw [hA]
    have hh := hb false
    rw [add_comm ((1/2 : ℝ) • Smat), ←sub_le_iff_le_add] at hh
    have he : (∑i, if f i=false then Matrix.vecMulVec (w i) (w i) else 0) -
        (1/2 : ℝ) • Smat = (1/2 : ℝ) • Smat - (∑i, if f i=true then Matrix.vecMulVec (w i) (w i) else 0) := by
      have hc : (∑i, if f i=false then Matrix.vecMulVec (w i) (w i) else 0)=
          Smat-(∑i, if f i=true then Matrix.vecMulVec (w i) (w i) else 0) := by
        rw [←hcomp]; abel
      rw [hc]
      module
    rw [he] at hh
    exact (sub_le_comm.mp hh)
  · rw [hA]
    exact hb true

end StrongThinTree.MSS

end
end

end OAI
