import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open Filter Topology

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma exists_orthonormal_small {I : Type*} [Fintype I] (v : I → E)
    (hv : Orthonormal ℂ v) (b : ℕ → E) (n : ℕ) (ε : ℝ) (hε : 0<ε)
    (hlarge : (∑ j ∈ Finset.range n, ‖b j‖^2)<Fintype.card I*ε^2) :
    ∃ i, ∀ j < n, ‖inner ℂ (v i) (b j)‖<ε := by
  classical
  by_contra! h
  have hlow (i : I) : ε^2≤∑ j ∈ Finset.range n, ‖inner ℂ (v i) (b j)‖^2 := by
    obtain ⟨j,hj,hij⟩ := h i
    calc
      ε^2 ≤ ‖inner ℂ (v i) (b j)‖^2 := by nlinarith [norm_nonneg (inner ℂ (v i) (b j))]
      _ ≤ _ := Finset.single_le_sum (fun k _ => sq_nonneg ‖inner ℂ (v i) (b k)‖)
        (Finset.mem_range.mpr hj)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlow i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hupp : (∑ i, ∑ j ∈ Finset.range n, ‖inner ℂ (v i) (b j)‖^2)≤
      ∑ j ∈ Finset.range n, ‖b j‖^2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun j _ => hv.sum_inner_products_le (b j)
  linarith

theorem exists_weak_zero_sequence (P : Set E) (b : ℕ → E) (hb : DenseRange b)
    (hlarge : ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ v : Fin m → E,
      Orthonormal ℂ v ∧ ∀ i, v i∈P) :
    ∃ v : ℕ → E, (∀ n, v n∈P) ∧ (∀ n, ‖v n‖=1) ∧
      ∀ y : E, Tendsto (fun n => inner ℂ (v n) y) atTop (𝓝 0) := by
  classical
  have hchoose (n : ℕ) : ∃ x : E, x∈P ∧ ‖x‖=1 ∧
      ∀ j < n, ‖inner ℂ x (b j)‖<(1:ℝ)/(n+1) := by
    have hε : 0<(1:ℝ)/(n+1) := by positivity
    obtain ⟨N,hN⟩ := exists_nat_gt ((∑ j ∈ Finset.range n, ‖b j‖^2)/((1:ℝ)/(n+1))^2)
    obtain ⟨m,hm,v,hv,hP⟩ := hlarge N
    have hbound : (∑ j ∈ Finset.range n, ‖b j‖^2)<Fintype.card (Fin m)*((1:ℝ)/(n+1))^2 := by
      rw [Fintype.card_fin]
      apply (div_lt_iff₀ (sq_pos_of_pos hε)).mp
      exact hN.trans_le (by exact_mod_cast hm)
    obtain ⟨i,hi⟩ := exists_orthonormal_small v hv b n _ hε hbound
    exact ⟨v i,hP i,hv.norm_eq_one i,hi⟩
  choose v hvP hvnorm hvsmall using hchoose
  have htest (j : ℕ) : Tendsto (fun n => inner ℂ (v n) (b j)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
      (eventually_atTop.mpr ⟨j+1,fun n hn => (hvsmall n j (by omega)).le⟩)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hclosed : IsClosed {y : E | Tendsto (fun n => inner ℂ (v n) y) atTop (𝓝 0)} := by
    have hF : Equicontinuous (fun n y => inner ℂ (v n) y) :=
      (LipschitzWith.uniformEquicontinuous (fun n y => inner ℂ (v n) y) 1
        (fun n => (innerSL ℂ (v n)).lipschitzWith.weaken (by
          exact_mod_cast (show ‖innerSL ℂ (v n)‖ ≤ (1:ℝ) by rw [innerSL_apply_norm,hvnorm])))).equicontinuous
    exact hF.isClosed_setOfPred_tendsto continuous_const
  refine ⟨v,hvP,hvnorm,fun y => ?_⟩
  have hsub : Set.range b ⊆ {y : E | Tendsto (fun n => inner ℂ (v n) y) atTop (𝓝 0)} := by
    rintro _ ⟨j,rfl⟩
    exact htest j
  exact closure_minimal hsub hclosed (hb y)

end Kadison

end

end
end

end OAI
