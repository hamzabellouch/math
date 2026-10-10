import OAI.Analysis.LpDimension.RampLaws

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u uE uJ uV uΩ

namespace SubpolynomialLp

lemma controlled_retraction_integrals {Ω : Type uΩ} {E : Type uE} {V : Type uV} {J : Type uJ} [MeasurableSpace Ω]
    [Fintype E] [Fintype V] [Fintype J] [DecidableEq E] [DecidableEq V] [Nonempty E]
    (μ : Measure Ω) (src dst : E → V) (δ lam : E → ℝ) (hδ : ∀ e, 0 < δ e)
    (hlam : ∀ e, 0 < lam e) (hls : ∑ e, lam e = 1)
    (hcard : 2 ≤ Fintype.card V)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (f : J → E → Ω → ℝ) (hf : ∀ j e, MemLp (f j e) 2 μ)
    (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hbound : ∀ j e, (∫ x, (f j e x)^2 ∂μ) ≤ B j) :
    ∃ P ∈ retractions (normalizedGradient src dst δ),
      (∀ e, matrixRowNorm P e ≤ 4*Real.log (Fintype.card V : ℝ)) ∧
      (∀ j, (∑ e, lam e * (∫ x, (P.mulVec (fun a => f j a x) e)^2 ∂μ)) ≤ 4*B j) := by
  have hnorm (j : J) (e : E) : ‖(hf j e).toLp (f j e)‖^2 ≤ B j := by
    rw [L2_norm_sq]; exact hbound j e
  obtain ⟨P,hP,hr,hE⟩ := controlled_retraction_bounds src dst δ lam hδ hlam hls hcard hinc hconn
    (fun j e => (hf j e).toLp (f j e)) B hB hnorm
  refine ⟨P,hP,hr,fun j => ?_⟩
  simpa only [L2_hilbertMul_energy,Matrix.mulVec,dotProduct] using hE j

lemma retraction_fixes {E : Type uE} {V : Type uV} [Fintype E] [Fintype V]
    (A : Matrix E V ℝ) (P : Matrix E E ℝ) (hP : P ∈ retractions A)
    (v : E → ℝ) (hv : ∃ x, A.mulVec x = v) : P.mulVec v = v := by
  obtain ⟨x,rfl⟩ := hv
  rw [Matrix.mulVec_mulVec,hP.1]

lemma retraction_range {E : Type uE} {V : Type uV} [Fintype E] [Fintype V]
    (A : Matrix E V ℝ) (P : Matrix E E ℝ) (hP : P ∈ retractions A)
    (v : E → ℝ) : ∃ x, A.mulVec x = P.mulVec v := by
  obtain ⟨B,hB⟩ := hP.2
  exact ⟨B.mulVec v,by rw [Matrix.mulVec_mulVec,← hB]⟩

lemma matrix_mulVec_bound {E : Type uE} [Fintype E]
    (P : Matrix E E ℝ) (v : E → ℝ) (K : ℝ) (hK : ∀ e, |v e| ≤ K) (e : E) :
    |P.mulVec v e| ≤ matrixRowNorm P e * K := by
  calc
    _ ≤ ∑ f, |P e f*v f| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f, |P e f| *K := Finset.sum_le_sum (fun f _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK f) (abs_nonneg _))
    _ = _ := (Finset.sum_mul ..).symm

lemma matrix_memLp {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) (P : Matrix E E ℝ) (f : E → Ω → ℝ)
    (hf : ∀ e, MemLp (f e) 2 μ) (e : E) : MemLp (fun x => P.mulVec (fun a => f a x) e) 2 μ := by
  convert memLp_finsetSum' Finset.univ (fun a _ => (hf a).const_mul (P e a)) using 1
  ext x
  simp only [Matrix.mulVec,dotProduct,Finset.sum_apply]

lemma matrix_integral_sq_bound {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) (P : Matrix E E ℝ) (f : E → Ω → ℝ)
    (hf : ∀ e, MemLp (f e) 2 μ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ e, (∫ x, (f e x)^2 ∂μ) ≤ B) (e : E) :
    (∫ x, (P.mulVec (fun a => f a x) e)^2 ∂μ) ≤ (matrixRowNorm P e)^2*B := by
  have hnorm (a : E) : ‖(hf a).toLp (f a)‖ ≤ Real.sqrt B := by
    apply (Real.le_sqrt (norm_nonneg _) hB).mpr
    rw [L2_norm_sq]; exact hbound a
  have hsum : ‖hilbertMul P (fun a => (hf a).toLp (f a)) e‖ ≤ matrixRowNorm P e*Real.sqrt B := by
    calc
      _ ≤ ∑ a, ‖P e a • (hf a).toLp (f a)‖ := norm_sum_le _ _
      _ ≤ ∑ a, |P e a| *Real.sqrt B := Finset.sum_le_sum (fun a _ => by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hnorm a) (abs_nonneg _))
      _ = _ := (Finset.sum_mul ..).symm
  have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (matrixRowNorm_nonneg P e) (Real.sqrt_nonneg B))).mpr hsum
  rw [L2_hilbertMul_energy,mul_pow,Real.sq_sqrt hB] at hh
  exact hh

lemma ramp_error_le_cut_errors {E : Type uE} [Fintype E]
    (P : Matrix E E ℝ) (v : E → ℝ) (ℓ : ℕ) (e : E) :
    |P.mulVec (fun a => dyadicRamp ℓ (v a)) e - dyadicRamp ℓ (v e)| ≤
      ∑ k ∈ Finset.range (2*ℓ),
        |P.mulVec (fun a => cutPart ((2:ℝ)^k) (v a)) e-cutPart ((2:ℝ)^k) (v e)| := by
  let d : ℕ → ℝ := fun k => P.mulVec (fun a => cutPart ((2:ℝ)^k) (v a)) e-cutPart ((2:ℝ)^k) (v e)
  have he : P.mulVec (fun a => dyadicRamp ℓ (v a)) e-dyadicRamp ℓ (v e) =
      ∑ k ∈ Finset.range ℓ, (d (k+ℓ)-d k) := by
    simp only [dyadicRamp,bandPart_eq_cutPart _ _ _ (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right _ _)),
      Matrix.mulVec,dotProduct,d]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range ℓ, |d (k+ℓ)-d k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range ℓ, (|d (k+ℓ)|+|d k|) := Finset.sum_le_sum (fun k _ => abs_sub _ _)
    _ = ∑ k ∈ Finset.range (2*ℓ), |d k| := by
      rw [Finset.sum_add_distrib,show 2*ℓ=ℓ+ℓ by omega,Finset.sum_range_add]
      simp only [Nat.add_comm]
      ring

lemma cut_error_eq_neg_tail_error {E : Type uE} [Fintype E]
    (P : Matrix E E ℝ) (v : E → ℝ) (hv : P.mulVec v=v) (a : ℝ) (e : E) :
    P.mulVec (fun f => cutPart a (v f)) e-cutPart a (v e) =
      -(P.mulVec (fun f => tailPart a (v f)) e-tailPart a (v e)) := by
  have ht : (fun f => tailPart a (v f))+(fun f => cutPart a (v f))=v := by
    ext f; exact tailPart_add_cutPart a (v f)
  have hh := congrFun (congrArg (P.mulVec) ht) e
  rw [Matrix.mulVec_add,hv] at hh
  have he := tailPart_add_cutPart a (v e)
  change P.mulVec (fun f => tailPart a (v f)) e+P.mulVec (fun f => cutPart a (v f)) e=v e at hh
  linarith

end SubpolynomialLp

end

end OAI
