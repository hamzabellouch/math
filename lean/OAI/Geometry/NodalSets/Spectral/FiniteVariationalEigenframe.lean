import Mathlib.Data.Fin.Tuple.Basic
import OAI.Geometry.NodalSets.Elliptic.FiniteFamilyNonzeroComplement

namespace OAI

namespace Yau.Analysis
open Set
noncomputable section

theorem real_orthogonal_span_range {E I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e : I → E) (x : E)
    (h : ∀ i, inner ℝ (e i) x = 0) :
    x ∈ (Submodule.span ℝ (range e))ᗮ := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨i,rfl⟩ := hy; exact h i
  | zero => exact inner_zero_left _
  | add y z hy hz ihy ihz => rw [inner_add_left,ihy,ihz,add_zero]
  | smul a y hy ih => rw [inner_smul_left_eq_smul,smul_eq_mul,ih,mul_zero]

theorem real_orthonormal_snoc {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {N : ℕ} (e : Fin N → E) (v : E)
    (he : Orthonormal ℝ e) (hv : ‖v‖ = 1)
    (ho : ∀ i, inner ℝ (e i) v = 0) : Orthonormal ℝ (Fin.snoc e v) := by
  rw [orthonormal_iff_ite]
  intro i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  · simp [hv]
  · rename_i j
    rw [Fin.snoc_last,Fin.snoc_castSucc,real_inner_comm,ho j]
    simp [ne_of_gt (Fin.castSucc_lt_last j)]
  · simp [ho]
  · simpa using (orthonormal_iff_ite.mp he _ _)

theorem compact_positive_finite_variational_eigenframe {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hE : ¬FiniteDimensional ℝ E)
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (T x) x) (N : ℕ) :
    ∃ (e : Fin N → E) (mu : Fin N → ℝ),
      Orthonormal ℝ e ∧ (∀ i, 0 < mu i ∧ T (e i) = mu i • e i) ∧
      Antitone mu ∧ ∀ i x,
        (∀ j, j < i → inner ℝ (e j) x = 0) →
        inner ℝ (T x) x ≤ mu i * ‖x‖^2 := by
  classical
  induction N with
  | zero =>
    refine ⟨Fin.elim0,Fin.elim0,?_,?_,?_,?_⟩
    · exact ⟨fun i ↦ Fin.elim0 i,fun i ↦ Fin.elim0 i⟩
    · exact fun i ↦ Fin.elim0 i
    · exact fun i ↦ Fin.elim0 i
    · exact fun i ↦ Fin.elim0 i
  | succ N ih =>
    obtain ⟨e,mu,he,heig,hanti,hmax⟩ := ih
    obtain ⟨lam,hlam,v,hvn,hve,horth,hvmax⟩ :=
      compact_positive_finite_family_extension hE T hc hs hp e mu (fun i ↦ (heig i).2)
    have hlam_le (i : Fin N) : lam ≤ mu i := by
      have h := hmax i v (fun j _ ↦ horth j)
      rw [hve,inner_smul_left_eq_smul,smul_eq_mul,real_inner_self_eq_norm_sq,hvn] at h
      simpa using h
    refine ⟨Fin.snoc e v,Fin.snoc mu lam,real_orthonormal_snoc e v he hvn horth,?_,?_,?_⟩
    · intro i
      induction i using Fin.lastCases
      · simpa using And.intro hlam hve
      · simpa using heig _
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact le_rfl
      · simp at hij
      · simpa using hlam_le _
      · simpa using hanti (by simpa using hij)
    · intro i x hx
      induction i using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last]
        apply hvmax x
        apply real_orthogonal_span_range e x
        intro j
        simpa using hx j.castSucc (Fin.castSucc_lt_last j)
      | cast i =>
        rw [Fin.snoc_castSucc]
        apply hmax i x
        intro j hji
        simpa using hx j.castSucc (by simpa using hji)

end
end Yau.Analysis

end OAI
