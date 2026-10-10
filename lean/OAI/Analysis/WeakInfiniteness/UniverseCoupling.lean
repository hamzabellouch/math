import Mathlib
import OAI.Analysis.WeakInfiniteness.FiniteCoupling
import OAI.Analysis.WeakInfiniteness.UniverseSelfadjoint

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

open scoped CStarAlgebra Topology InnerProductSpace ComplexOrder

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_finite_coupling_of_gap_any
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    {ι : Type*} (F : ι → OrthogonalPerturbationData A n) :
    ∀ s : Finset ι, (∀ i ∈ s, (F i).p ∈ D ∧ (F i).q ∈ D) →
    ∃ U : A, U ∈ D ∧ IsSelfAdjoint U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ i ∈ s, ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        (F i).α ≤ ‖π (F i).c‖ → ε ≤ ‖π ((F i).p*U*(F i).q)‖ := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨0,D.zero_mem,IsSelfAdjoint.zero A,1,zero_lt_one,?_⟩
      simp
  | @insert i s hi ih =>
      intro hmem
      obtain ⟨U,hUD,hUsa,ε,hε,hU⟩ := ih (fun j hj => hmem j (Finset.mem_insert_of_mem hj))
      let δ := ε/4
      have hδ : 0 < δ := by dsimp [δ]; positivity
      have hph : star (F i).p*(F i).p*(F i).h=(F i).h := by
        rw [(F i).nonneg_p.star_eq,mul_assoc,(F i).support_h,(F i).support_h]
      have hqk : (F i).q*star (F i).q*(F i).k=(F i).k := by
        rw [(F i).nonneg_q.star_eq,mul_assoc,(F i).support_k,(F i).support_k]
      obtain ⟨y,hyn,hysa,⟨z,hz⟩,hnew⟩ := selfadjoint_uniform_perturbation_of_gap_any
        hσ.le hσγ hgap hA hn hpi (F i).p (F i).q (F i).h (F i).k (F i).c
        (F i).norm_p (F i).norm_q (F i).nonneg_p (F i).nonneg_q (F i).orthogonal
        (F i).nonneg_h (F i).nonneg_k (F i).nonneg_c hph hqk
        (F i).compare_h (F i).compare_k ((F i).p*U*(F i).q) hδ (F i).pos_α
      have hyD : y ∈ D := by
        rw [hz]
        exact hD.symmetrized_corner_mem (hmem i (Finset.mem_insert_self ..)).1
          (hmem i (Finset.mem_insert_self ..)).2 z
      let U' := U+(δ : ℂ) • y
      have hU'D : U' ∈ D := D.add_mem hUD (D.smul_mem _ hyD)
      have hU'sa : IsSelfAdjoint U' := by
        show star (U+(δ : ℂ) • y)=U+(δ : ℂ) • y
        simp only [star_add,star_smul,hUsa.star_eq,hysa.star_eq,Complex.star_def,Complex.conj_ofReal]
      refine ⟨U',hU'D,hU'sa,min (ε/2) (σ*δ),lt_min (by positivity) (mul_pos hσ hδ),?_⟩
      intro j hj H π hπc
      rcases Finset.mem_insert.mp hj with rfl | hj
      · apply (min_le_right _ _).trans
        dsimp only [U']
        rw [corner_add_smul]
        exact hnew H π hπc
      · have hold := hU j hj H π hπc
        have herr : ‖π ((δ : ℂ) • ((F j).p*y*(F j).q))‖ ≤ δ := by
          calc
            _ ≤ ‖(δ : ℂ) • ((F j).p*y*(F j).q)‖ := NonUnitalStarAlgHom.norm_apply_le π _
            _ = δ*‖(F j).p*y*(F j).q‖ := by
              rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
            _ ≤ δ*1 := mul_le_mul_of_nonneg_left
              (norm_corner_le_one _ _ _ (F j).norm_p (F j).norm_q hyn) hδ.le
            _ = δ := mul_one _
        have hdiff : π ((F j).p*U*(F j).q)-π ((F j).p*U'*(F j).q)=
            -π ((δ : ℂ) • ((F j).p*y*(F j).q)) := by
          dsimp only [U']
          rw [corner_add_smul,map_add]
          abel
        have ht := norm_le_norm_add_norm_sub' (π ((F j).p*U*(F j).q))
          (π ((F j).p*U'*(F j).q))
        rw [hdiff,norm_neg] at ht
        apply (min_le_left _ _).trans
        dsimp only [δ] at herr
        linarith

end

end WeakPureInfiniteness
end

end OAI
