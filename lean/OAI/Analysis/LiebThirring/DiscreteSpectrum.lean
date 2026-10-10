import OAI.Analysis.LiebThirring.NegativeResolvent

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set
open scoped Topology ENNReal

/-- Negative eigenvalues at or below a threshold form a finite set whenever
one positive spectral moment is finite.  No enumeration is presupposed. -/
lemma finite_eigenvalues_below {γ : ℝ} (hγ : 0 < γ) {A : L2C →ₗ.[ℂ] L2C}
    (hA : IsSelfAdjoint A) (hfin : eigenvalueSum γ A hA ≠ ∞)
    {a : ℝ} (ha : 0 < a) :
    {e : ℝ | e ≤ -a ∧ ∃ f : L2C, f ≠ 0 ∧ IsOperatorEigenfunction A e f}.Finite := by
  classical
  let c := (ENNReal.ofReal a)^γ
  have hc : c ≠ 0 := ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr ha) ENNReal.ofReal_ne_top)
  let w := fun i : EigenIndex A hA ↦ (ENNReal.ofReal |i.1.1|)^γ
  have hs : {i : EigenIndex A hA | c ≤ w i}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top hfin hc
  apply (hs.image (fun i ↦ i.1.1)).subset
  rintro e ⟨he,f,hf,haf⟩
  have he₀ : e < 0 := lt_of_le_of_lt he (neg_neg_of_pos ha)
  obtain ⟨i⟩ := eigenBasis_nonempty hA hf haf
  refine ⟨⟨⟨e,he₀⟩,i⟩,?_,rfl⟩
  change (ENNReal.ofReal a)^γ ≤ (ENNReal.ofReal |e|)^γ
  apply ENNReal.rpow_le_rpow _ hγ.le
  apply ENNReal.ofReal_le_ofReal
  rw [abs_of_neg he₀]
  linarith

/-- Every negative eigenvalue is isolated from all other negative eigenvalues. -/
lemma negative_eigenvalue_isolated {γ : ℝ} (hγ : 0 < γ) {A : L2C →ₗ.[ℂ] L2C}
    (hA : IsSelfAdjoint A) (hfin : eigenvalueSum γ A hA ≠ ∞) {e : ℝ} (he : e < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t-e| < ε →
      (∃ f : L2C, f ≠ 0 ∧ IsOperatorEigenfunction A t f) → t = e := by
  let S := {t : ℝ | t ≤ e/2 ∧ ∃ f : L2C, f ≠ 0 ∧ IsOperatorEigenfunction A t f}
  have hs : S.Finite := by
    have hh := finite_eigenvalues_below hγ hA hfin (show 0 < -e/2 by linarith)
    simpa only [neg_div,neg_neg] using hh
  have hc : IsClosed (S \ {e}) := hs.sdiff.isClosed
  have hmem : e ∈ (S \ {e})ᶜ := by simp
  obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp hc.isOpen_compl e hmem
  refine ⟨min δ (-e/2),lt_min hδ (by linarith),fun t ht hex ↦ ?_⟩
  have htδ : dist t e < δ := (Real.dist_eq t e).symm ▸ (lt_of_lt_of_le ht (min_le_left _ _))
  have hte : t ≤ e/2 := by
    have hab : t-e ≤ |t-e| := le_abs_self _
    have hε := lt_of_lt_of_le ht (min_le_right δ (-e/2))
    linarith
  have hn : t ∉ S \ {e} := hsub (show t ∈ Metric.ball e δ from htδ)
  by_contra hne
  exact hn ⟨⟨hte,hex⟩,show t ∉ ({e} : Set ℝ) from hne⟩

/-- The negative part of the operator has only isolated
finite-multiplicity eigenvalues, with zero as its only possible finite
accumulation point. The first clause excludes continuous/residual spectrum. -/
theorem schrodinger_negative_spectrum {γ : ℝ} (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2)
    {W : ℝ → ℝ} (hW : Admissible γ W) :
    (∀ e : ℝ, e < 0 →
      (¬ HasBoundedResolventAt (schrodingerOperator hγ₀ hW) e ↔
        ∃ f : L2C, f ≠ 0 ∧ IsOperatorEigenfunction (schrodingerOperator hγ₀ hW) e f)) ∧
    (∀ e : NegativeEnergy, FiniteDimensional ℂ (eigenSpace (schrodingerOperator hγ₀ hW) e.1)) ∧
    (∀ a : ℝ, 0 < a →
      {e : ℝ | e ≤ -a ∧ ∃ f : L2C, f ≠ 0 ∧
        IsOperatorEigenfunction (schrodingerOperator hγ₀ hW) e f}.Finite) ∧
    (∀ e : ℝ, e < 0 → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t-e| < ε →
      (∃ f : L2C, f ≠ 0 ∧ IsOperatorEigenfunction (schrodingerOperator hγ₀ hW) t f) → t = e) := by
  let A := schrodingerOperator hγ₀ hW
  have hA : IsSelfAdjoint A := schrodingerOperator_selfAdjoint hγ₀ hW
  have hb := sharp_bound_for_associated_operator hγ₀ hγ₁ hW hA
    (schrodingerOperator_associated hγ₀ hW)
  have hfin : eigenvalueSum γ A hA ≠ ∞ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hW.mass_ne_top hγ₀)) hb.1
  have hγ : 0 < γ := by linarith
  refine ⟨fun e he ↦ ?_,hb.2,fun a ha ↦ finite_eigenvalues_below hγ hA hfin ha,
    fun e he ↦ negative_eigenvalue_isolated hγ hA hfin he⟩
  constructor
  · intro hr
    rcases negative_resolvent_or_eigenvalue hγ₀ hW (potentialData hγ₀ hW) he with hi | hn
    · exact (hr hi).elim
    · exact hn
  · intro hn hr
    exact hasBoundedResolventAt_not_eigenvalue hr hn

end SharpLiebThirring.OperatorProof

end

end OAI
