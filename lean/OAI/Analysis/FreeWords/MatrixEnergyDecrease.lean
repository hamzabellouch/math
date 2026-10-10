import Mathlib
import OAI.Analysis.FreeWords.ChosenUnitaryMatrix
import OAI.Analysis.FreeWords.MatrixAverageCycle
import OAI.Analysis.FreeWords.MatrixAverageTrace
import OAI.Analysis.FreeWords.SimultaneousDispersion

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKTraceTransfer KKUltraTrace KKFactorSupport KKProjectionSupport KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

theorem unitary_norm_le_one (u : unitary (ConcreteAlgebra M)) : ‖u.val‖ ≤ 1 := by
  cases subsingleton_or_nontrivial (ConcreteAlgebra M) with
  | inl h =>
    have := h
    rw [Subsingleton.elim u.val 0,norm_zero]
    norm_num
  | inr h =>
    have := h
    exact (CStarRing.norm_coe_unitary u).le

theorem algebraConj_traceNorm_sub_le (u v : unitary (ConcreteAlgebra M))
    (x : ConcreteAlgebra M) :
    traceNorm τ (algebraConj u x-algebraConj v x) ≤
      (2*‖x‖)*traceNorm τ (u.val-v.val) := by
  have he : algebraConj u x-algebraConj v x=
      (u.val-v.val)*x*star u.val+v.val*x*star (u.val-v.val) := by
    simp only [algebraConj,star_sub]
    noncomm_ring
  rw [he]
  have h1 := traceNorm_mul_right_le τ ((u.val-v.val)*x) (star u.val)
  have h2 := traceNorm_mul_right_le τ (u.val-v.val) x
  have h3 := traceNorm_mul_le τ (v.val*x) (star (u.val-v.val))
  have h4 := norm_mul_le v.val x
  rw [norm_star] at h1
  rw [traceNorm_star] at h3
  have hu := unitary_norm_le_one u
  have hv := unitary_norm_le_one v
  have ha : traceNorm τ ((u.val-v.val)*x*star u.val) ≤
      traceNorm τ (u.val-v.val)*‖x‖ :=
    h1.trans ((mul_le_mul h2 hu (norm_nonneg _) (mul_nonneg (traceNorm_nonneg _ _) (norm_nonneg _))).trans (by simp))
  have hb : traceNorm τ (v.val*x*star (u.val-v.val)) ≤
      ‖x‖*traceNorm τ (u.val-v.val) := by
    apply h3.trans
    apply mul_le_mul_of_nonneg_right _ (traceNorm_nonneg _ _)
    exact h4.trans (by nlinarith [norm_nonneg x])
  have hh := (traceNorm_add_le τ _ _).trans (add_le_add ha hb)
  nlinarith [hh]

theorem finite_polynomial_slack {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (s : ℝ) (hs : 0 < s)
    (ha : ∑ i, (a i)^2 ≤ 3*s) :
    ∃ ε : ℝ, 0 < ε ∧ ∑ i, (a i+b i*ε)^2 < 7/2*s := by
  have hc : Continuous (fun t : ℝ => ∑ i, (a i+b i*t)^2) := by fun_prop
  have h0 : (∑ i, (a i+b i*0)^2) < 7/2*s := by simp only [mul_zero,add_zero]; linarith
  have hn := hc.continuousAt.eventually_lt_const h0
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ/2,half_pos hδ,hd ?_⟩
  rw [Metric.mem_ball,Real.dist_eq]
  simpa [abs_of_pos (half_pos hδ)] using (half_lt_self hδ)

theorem exists_matrix_energy_decrease {ι : Type*} [Fintype ι]
    (hF : IsFactor M) (hD : IsDiffuse M) (x : ι → ConcreteAlgebra M)
    (hx : ∀ i, τ.map (x i)=0) (hs : 0 < ∑ i, (traceNorm τ (x i))^2) :
    ∃ (n : ℕ) (_hn : 0 < n)
      (ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M),
      Function.Injective ρ ∧
      ∑ i, (traceNorm τ (matrixAverage ρ (x i)))^2 <
        7/8*∑ i, (traceNorm τ (x i))^2 := by
  classical
  obtain ⟨u,hu⟩ := exists_simultaneous_dispersion τ hF x hx
  obtain ⟨ε,hε,hεb⟩ := finite_polynomial_slack
    (fun i => traceNorm τ (x i+algebraConj u (x i))) (fun i => 2*‖x i‖) _ hs hu
  obtain ⟨n,hn,ρ,v,hρ,hv⟩ := chosen_unitary_matrix_approximation M τ hF hD u ε hε
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let V : unitary (ConcreteAlgebra M) := ⟨ρ v.val,Unitary.map_mem ρ v.property⟩
  have hpoint (i : ι) : 2*traceNorm τ (matrixAverage ρ (x i)) ≤
      traceNorm τ (x i+algebraConj u (x i))+2*‖x i‖*ε := by
    have he : matrixAverage ρ (x i+algebraConj V (x i))=
        (2:ℂ) • matrixAverage ρ (x i) := by
      rw [matrixAverage_add]
      change matrixAverage ρ (x i)+matrixAverage ρ (ρ v.val*x i*star (ρ v.val))=_
      rw [← map_star,matrixAverage_conjugate]
      module
    have hh := matrixAverage_traceNorm_le ρ τ (x i+algebraConj V (x i))
    rw [he,traceNorm_smul] at hh
    norm_num at hh
    change 2*traceNorm τ (matrixAverage ρ (x i)) ≤
      traceNorm τ (x i+algebraConj V (x i)) at hh
    have ht := traceNorm_add_le τ (x i+algebraConj u (x i))
      (algebraConj V (x i)-algebraConj u (x i))
    have he2 : x i+algebraConj u (x i)+(algebraConj V (x i)-algebraConj u (x i))=
        x i+algebraConj V (x i) := by abel
    rw [he2] at ht
    have hb := algebraConj_traceNorm_sub_le τ V u (x i)
    have hv' : traceNorm τ (V.val-u.val) < ε := by
      simpa only [traceNorm_eq_gns,map_sub,norm_sub_rev] using hv
    nlinarith [traceNorm_nonneg τ (matrixAverage ρ (x i)), norm_nonneg (x i)]
  refine ⟨n,hn,ρ,hρ,?_⟩
  have hh : 4*(∑ i, (traceNorm τ (matrixAverage ρ (x i)))^2) ≤
      ∑ i, (traceNorm τ (x i+algebraConj u (x i))+2*‖x i‖*ε)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hp := hpoint i
    have hn0 := traceNorm_nonneg τ (matrixAverage ρ (x i))
    nlinarith
  linarith

end

end KKMatrixQuantization
end

end OAI
