import Mathlib
import OAI.Analysis.MatrixSigning.Potential.PairHilbert
import OAI.Analysis.MatrixSigning.Matrices.JordanCLM
import OAI.Analysis.MatrixSigning.Potential.SymmetricNormQuadratic
import OAI.Analysis.MatrixSigning.Matrices.SquareScalarBound

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

private local instance : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace

def hessian (X Y P Q : H d) : PairHilbert d →L[ℝ] PairHilbert d :=
  onPairHilbert ((jordanCLM (invH X) (sandwich (invH X) P)).prodMap
    (jordanCLM (invH Y) (sandwich (invH Y) Q)))

lemma hessian_symmetric (X Y P Q : H d) :
    LinearMap.IsSymmetric (𝕜 := ℝ) (E := PairHilbert d) (hessian X Y P Q).toLinearMap := by
  intro u v
  change inner ℝ (jordanCLM (invH X) (sandwich (invH X) P) (WithLp.ofLp u).1) (WithLp.ofLp v).1 +
    inner ℝ (jordanCLM (invH Y) (sandwich (invH Y) Q) (WithLp.ofLp u).2) (WithLp.ofLp v).2 =
    inner ℝ (WithLp.ofLp u).1 (jordanCLM (invH X) (sandwich (invH X) P) (WithLp.ofLp v).1) +
    inner ℝ (WithLp.ofLp u).2 (jordanCLM (invH Y) (sandwich (invH Y) Q) (WithLp.ofLp v).2)
  congr 1
  · exact jordanCLM_symmetric _ _ _ _
  · exact jordanCLM_symmetric _ _ _ _

lemma hessian_block_bounds (X P : H d) (hX : X ∈ pd d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hXlo : (2*K)⁻¹ • (Hermitian.one : H d) ≤ X)
    (hXhi : X ≤ (K/ε) • (Hermitian.one : H d))
    (hPhi : P ≤ (Hermitian.one : H d))
    (hStat : ε • (Hermitian.one : H d) ≤ sandwich (invH X) P) (U : H d) :
    (2*ε^2/K) * ‖U‖^2 ≤ inner ℝ U (jordanCLM (invH X) (sandwich (invH X) P) U) ∧
    inner ℝ U (jordanCLM (invH X) (sandwich (invH X) P) U) ≤ (16*K^3) * ‖U‖^2 := by
  have hiXlo : (ε/K) • (Hermitian.one : H d) ≤ invH X := by
    simpa only [inv_div] using inverse_lower_of_upper X hX (div_pos hK hε) hXhi
  have hiXhi : invH X ≤ (2*K) • (Hermitian.one : H d) := by
    simpa only [inv_inv] using inverse_upper_of_lower X hX (inv_pos.mpr (by positivity)) hXlo
  have hiPhi : sandwich (invH X) P ≤ (2*K)^2 • (Hermitian.one : H d) :=
    (sandwich_mono (invH X) hPhi).trans
      (square_scalar_bound (invH X) (by positivity) hX.inv.posSemidef hiXhi)
  constructor
  · have hl := jordanCLM_lower (invH X) (sandwich (invH X) P)
      (div_pos hε hK).le hε.le hiXlo hStat U
    convert hl using 1; ring
  · have hu := jordanCLM_upper (invH X) (sandwich (invH X) P)
      (sq_nonneg (2*K)) hX.inv.posSemidef hiXhi hiPhi U
    convert hu using 1; ring

lemma hessian_bounds (X Y P Q : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hXlo : (2*K)⁻¹ • (Hermitian.one : H d) ≤ X)
    (hYlo : (2*K)⁻¹ • (Hermitian.one : H d) ≤ Y)
    (hXhi : X ≤ (K/ε) • (Hermitian.one : H d))
    (hYhi : Y ≤ (K/ε) • (Hermitian.one : H d))
    (hPhi : P ≤ (Hermitian.one : H d)) (hQhi : Q ≤ (Hermitian.one : H d))
    (hStatX : ε • (Hermitian.one : H d) ≤ sandwich (invH X) P)
    (hStatY : ε • (Hermitian.one : H d) ≤ sandwich (invH Y) Q) :
    (∀ u : PairHilbert d, (2*ε^2/K) * ‖u‖^2 ≤ inner ℝ u (hessian X Y P Q u)) ∧
    ‖hessian X Y P Q‖ ≤ 16*K^3 := by
  have hbounds (u : PairHilbert d) :
      (2*ε^2/K) * ‖u‖^2 ≤ inner ℝ u (hessian X Y P Q u) ∧
      inner ℝ u (hessian X Y P Q u) ≤ (16*K^3) * ‖u‖^2 := by
    obtain ⟨h₁,h₂⟩ := hessian_block_bounds X P hX hε hK hXlo hXhi hPhi hStatX (WithLp.ofLp u).1
    obtain ⟨h₃,h₄⟩ := hessian_block_bounds Y Q hY hε hK hYlo hYhi hQhi hStatY (WithLp.ofLp u).2
    have he : inner ℝ u (hessian X Y P Q u) =
        inner ℝ (WithLp.ofLp u).1 (jordanCLM (invH X) (sandwich (invH X) P) (WithLp.ofLp u).1) +
        inner ℝ (WithLp.ofLp u).2 (jordanCLM (invH Y) (sandwich (invH Y) Q) (WithLp.ofLp u).2) := rfl
    rw [he, WithLp.prod_norm_sq_eq_of_L2]
    dsimp only [WithLp.fst, WithLp.snd]
    constructor <;> nlinarith
  refine ⟨fun u => (hbounds u).1, ?_⟩
  apply CurrentKS.Hilbert.symmetric_norm_le_of_quadratic (hessian X Y P Q)
    (hessian_symmetric X Y P Q) (by positivity)
  intro u
  rw [real_inner_comm]
  have hn : 0 ≤ inner ℝ u (hessian X Y P Q u) :=
    (by positivity : 0 ≤ (2*ε^2/K) * ‖u‖^2).trans (hbounds u).1
  rw [abs_of_nonneg hn]
  exact (hbounds u).2

end
end CurrentKS.Variational

end OAI
