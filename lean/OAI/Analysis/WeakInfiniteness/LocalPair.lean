import Mathlib
import OAI.Analysis.WeakInfiniteness.ComplexScalar
import OAI.Analysis.WeakInfiniteness.FixedColumns
import OAI.Analysis.WeakInfiniteness.InnerSubalgebras

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma map_ramp_cut_mul_of_no_orthogonal (π : A →⋆ₙₐ[ℂ] B)
    {h : A} (hh : 0 ≤ h) (hhn : π h ≠ 0)
    (hno : ∀ a ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      ∀ b ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      0 ≤ a → 0 ≤ b → a*b=0 → π a=0 ∨ π b=0) :
    π (cfcₙ (spectralRamp (‖π h‖/8)) (positiveCut (‖π h‖/2) h))*π h=π h := by
  let l := ‖π h‖
  have hl : 0 < l := norm_pos_iff.mpr hhn
  have hhπ : IsSelfAdjoint (π h) := (map_nonneg π hh).isSelfAdjoint
  have hf : Continuous (fun x : ℝ => max (x-l/2) 0) := by fun_prop
  have hf0 : max (0-l/2) 0=0 := max_eq_right (by linarith)
  have hg0 : spectralRamp (l/8) 0=0 := spectralRamp_eq_zero (by positivity) (by positivity)
  rw [π.map_cfcₙ _ _ (continuous_spectralRamp _).continuousOn hg0 (by fun_prop)
    (positiveCut_nonneg _ _).isSelfAdjoint (map_nonneg π (positiveCut_nonneg _ _)).isSelfAdjoint]
  change cfcₙ (spectralRamp (l/8)) (π (cfcₙ (fun x : ℝ => max (x-l/2) 0) h))*π h=π h
  rw [π.map_cfcₙ _ _ hf.continuousOn hf0 (by fun_prop) hh.isSelfAdjoint hhπ]
  rw [← cfcₙ_comp (spectralRamp (l/8)) (fun x : ℝ => max (x-l/2) 0) (π h)
    (continuous_spectralRamp _).continuousOn hg0 hf.continuousOn hf0 hhπ]
  conv_rhs => rw [← cfcₙ_id' ℝ (π h) hhπ]
  conv_lhs => rhs; rw [← cfcₙ_id' ℝ (π h) hhπ]
  rw [← cfcₙ_mul ((spectralRamp (l/8)) ∘ (fun x : ℝ => max (x-l/2) 0))
    (fun x : ℝ => x) (π h) ((continuous_spectralRamp _).comp hf).continuousOn
    (by simpa only [Function.comp_apply,hf0] using hg0) continuous_id.continuousOn rfl]
  apply cfcₙ_congr
  intro x hx
  rcases mem_quasispectrum_iff.mp hx with rfl | hx
  · simp
  rcases spectrum_dichotomy_of_no_orthogonal _ π hno (self_mem_hereditary h hh) hh hx with rfl | rfl
  · simp
  · change spectralRamp (l/8) (max (l-l/2) 0)*l=l
    rw [max_eq_left (by linarith),spectralRamp_eq_one (by positivity) (by linarith),one_mul]

lemma exists_orthogonal_detected_pair {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (π : A →⋆ₙₐ[ℂ] B) {h : A} (hh : 0 ≤ h) (hhn : π h ≠ 0) :
    ∃ a ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      ∃ b ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      0 ≤ a ∧ 0 ≤ b ∧ a*b=0 ∧ π a ≠ 0 ∧ π b ≠ 0 := by
  classical
  by_contra! hno
  have hno' : ∀ a ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      ∀ b ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      0 ≤ a → 0 ≤ b → a*b=0 → π a=0 ∨ π b=0 := by
    intro a ha b hb ha0 hb0 hab
    by_cases han : π a=0
    · exact Or.inl han
    · exact Or.inr (hno a ha b hb ha0 hb0 hab han)
  let l := ‖π h‖
  have hl : 0 < l := norm_pos_iff.mpr hhn
  let e := cfcₙ (spectralRamp (l/4)) h
  let d := cfcₙ (spectralRamp (l/8)) (positiveCut (l/2) h)
  obtain ⟨L,hL,-,-,heL⟩ := exists_finite_model_columns hn hpi h hl (n+1)
  have he : e ∈ hereditarySubalgebra h hh.isSelfAdjoint :=
    cfcₙ_mem _ (self_mem_hereditary h hh)
  have heL' (i : Fin n) (j : Fin (n+1)) : e*L i j=L i j := by
    have hv := congrArg (fun X => X i j) heL
    change ((Matrix.diagonal fun _ : Fin n => e)*(CStarMatrix.ofMatrix.symm L)) i j=L i j at hv
    simpa only [Matrix.diagonal_mul,CStarMatrix.ofMatrix_symm_apply] using hv
  have hm (i : Fin n) (j : Fin (n+1)) : L i j*h ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
    rw [← heL' i j]
    exact (hereditarySubalgebra_inner h hh.isSelfAdjoint).2 e he h
      (self_mem_hereditary h hh) (L i j)
  choose z hz using fun i j => hereditary_image_scalar_of_no_orthogonal π hh hhn hno' (hm i j)
  let Z : Matrix (Fin n) (Fin (n+1)) ℂ := z
  have hsq : π h*π h=l • π h := square_eq_norm_smul_of_no_orthogonal _ π hno'
    (self_mem_hereditary h hh) hh
  have hsqn : π h*π h ≠ 0 := by rw [hsq]; exact smul_ne_zero (ne_of_gt hl) hhn
  have hdh : π d*π h=π h := map_ramp_cut_mul_of_no_orthogonal π hh hhn hno'
  have hgram (i j : Fin (n+1)) :
      (Z.conjTranspose*Z) i j • (π h*π h) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) i j • (π h*π h) := by
    calc
      (Z.conjTranspose*Z) i j • (π h*π h) =
          ∑ k : Fin n,star (π (L k i*h))*π (L k j*h) := by
        change (∑ k : Fin n,star (z k i)*z k j) • (π h*π h)=_
        simp only [Finset.sum_smul,hz,star_smul,(map_nonneg π hh).star_eq,
          smul_mul_assoc,mul_smul_comm,smul_smul]
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_comm]
      _ = π (h*(L.conjTranspose*L) i j*h) := by
        simp only [CStarMatrix.mul_apply,CStarMatrix.conjTranspose_apply,map_mul,map_star,map_sum,
          Finset.mul_sum,Finset.sum_mul,star_mul,(map_nonneg π hh).star_eq]
        apply Finset.sum_congr rfl
        intro k _
        noncomm_ring
      _ = π (h*(diagonalCopies (n+1) d) i j*h) := by rw [hL]
      _ = _ := by
        by_cases hij : i=j
        · subst j
          simp only [diagonalCopies,CStarMatrix.ofMatrix_apply,Matrix.diagonal_apply_eq,Matrix.one_apply_eq,one_smul,map_mul]
          rw [mul_assoc,hdh]
        · simp [diagonalCopies,Matrix.diagonal_apply_ne _ hij,Matrix.one_apply_ne hij]
  have hZZ : Z.conjTranspose*Z=1 := by
    ext i j
    exact (smul_left_injective ℂ hsqn) (hgram i j)
  have hr := (Matrix.rank_mul_le_left Z.conjTranspose Z).trans (Matrix.rank_le_width Z.conjTranspose)
  rw [hZZ,Matrix.rank_one] at hr
  simp only [Fintype.card_fin] at hr
  omega

end

end WeakPureInfiniteness
end

end OAI
