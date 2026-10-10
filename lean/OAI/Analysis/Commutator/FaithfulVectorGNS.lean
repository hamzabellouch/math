import Mathlib
import OAI.Analysis.Commutator.FaithfulNormalStateProducer
import OAI.Analysis.Commutator.GNSVectorEmbedding
import OAI.Analysis.Commutator.InfiniteAmplification

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology ENNReal

namespace Kadison.FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (x : ℕ → H)

def weighted (n : ℕ) : H := (Real.sqrt (weight x n) : ℂ) • x n

omit [CompleteSpace H] in
lemma weighted_norm_sq (n : ℕ) : ‖weighted x n‖^2=weight x n*‖x n‖^2 := by
  rw [weighted,norm_smul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (weight_pos x n).le]

omit [CompleteSpace H] in
lemma weighted_mem : Memℓp (weighted x) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
  have hs : Summable (fun n => ‖weighted x n‖^2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => by
      rw [weighted_norm_sq]; exact weight_norm_bound x n)
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1))
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hs

def vector : InfiniteAmplification.Space ℕ H := ⟨weighted x,weighted_mem x⟩

lemma vector_inner (T : H →L[ℂ] H) :
    inner ℂ (vector x) ((InfiniteAmplification.diagonal (H:=H) (ι:=ℕ)) T (vector x))=functional x T := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change inner ℂ ((Real.sqrt (weight x n):ℂ) • x n)
    (T ((Real.sqrt (weight x n):ℂ) • x n))=term x n T
  rw [map_smul,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal,term]
  rw [←mul_assoc,←Complex.ofReal_mul,←pow_two,Real.sq_sqrt (weight_pos x n).le]

variable (M : VonNeumannAlgebra H)

def gnsEmbedding : (restricted x M).GNS →ₗᵢ[ℂ] InfiniteAmplification.Space ℕ H :=
  VectorGNS.embedding (restricted x M)
    ((InfiniteAmplification.diagonal (H:=H) (ι:=ℕ)).comp M.subtype) (vector x) (fun a => (vector_inner x a.val).symm)

lemma gnsEmbedding_intertwines (a : M) (v : (restricted x M).GNS) (n : ℕ) :
    gnsEmbedding x M ((restricted x M).gnsStarAlgHom a v) n=a.val (gnsEmbedding x M v n) := by
  exact congrArg (fun T : (restricted x M).GNS →L[ℂ] InfiniteAmplification.Space ℕ H => T v n)
    (VectorGNS.intertwines (restricted x M)
      ((InfiniteAmplification.diagonal (H:=H) (ι:=ℕ)).comp M.subtype) (vector x)
      (fun a => (vector_inner x a.val).symm) a)

end Kadison.FaithfulNormalFunctional

end

end
end

end OAI
