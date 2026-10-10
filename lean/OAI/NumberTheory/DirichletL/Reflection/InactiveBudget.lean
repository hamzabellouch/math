import OAI.NumberTheory.DirichletL.Reflection.SlotMass

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section

lemma subtype_product_le_full {σ : Type*} [Fintype σ] (p : σ→Prop) [DecidablePred p]
    (H : σ→ℝ) (hH : ∀ i,1≤H i) :
    (∏ i : {i // p i},H i.val)≤∏ i,H i := by
  rw [←Finset.prod_subtype (Finset.univ.filter p) (by simp) H]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ _)
    (fun i _ => (zero_le_one.trans (hH i))) (fun i _ _ => hH i)

theorem harmonic_product_small_power (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤rmax → (∀ i,1≤H i) →
      (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤C*(∏ i,H i)^ε := by
  let D := max 1 (256*(2+1/((ε/2)*Real.log 2)))
  have hD : 1≤D := le_max_left _ _
  refine ⟨D^(2*rmax),by positivity,?_⟩
  intro σ _ H hcard hH
  have hp : 0<∏ i,H i := Finset.prod_pos (fun i _ => lt_of_lt_of_le zero_lt_one (hH i))
  have he (i : σ) : 256*(columnDyadicLength (H i)+1:ℝ)≤D*(H i)^(ε/2) := by
    apply (mul_le_mul_of_nonneg_left (columnDyadicLength_small_power (ε/2) (by positivity) (H i) (hH i)) (by norm_num : (0:ℝ)≤256)).trans
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (zero_le_one.trans (hH i)) _)
  calc
    _ ≤ (∏ i,D*(H i)^(ε/2))^2 := by
      apply pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => by positivity))
      exact Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => he i)
    _ = D^(2*Fintype.card σ)*(∏ i,H i)^ε := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        Real.finsetProd_rpow Finset.univ H (fun i _ => zero_le_one.trans (hH i)),mul_pow,←pow_mul,
        ←Real.rpow_mul_natCast hp.le]
      congr 1
      · congr 1;omega
      · congr 1;norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (Nat.mul_le_mul_left 2 hcard)) (Real.rpow_nonneg hp.le _)

theorem inactive_product_small_power (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (T : Finset σ) (H : σ→ℝ),
      Fintype.card σ≤rmax → (∀ i,1≤H i) →
      (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2≤C*(∏ i,H i)^ε := by
  obtain ⟨C,hC,hb⟩ := harmonic_product_small_power rmax ε hε
  refine ⟨C,hC,?_⟩
  intro σ _ T H hcard hH
  apply (hb (fun i : {i // i∉T} => H i.val)
    ((Fintype.card_subtype_le _).trans hcard) (fun i => hH i.val)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i.val)))
    (subtype_product_le_full (fun i => i∉T) H hH) hε.le
end
end SevenEighths.InverseReflectedPhase

end OAI
