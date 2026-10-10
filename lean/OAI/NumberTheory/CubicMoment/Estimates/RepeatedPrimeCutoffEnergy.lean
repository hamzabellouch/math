import OAI.NumberTheory.CubicMoment.Estimates.RepeatedPrimeSupport

namespace OAI

/-! Repeated-prime energy on the actual global norm cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma convolutionError_mem_largeSquareSupport_of_norm
    (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ) (Y D : ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p)
    {b : Eisenstein} (hbY : norm b ≤ Y) (hb : squarefreeConvolutionError S w b ≠ 0) :
    b ∈ largeSquareSupport Y D := by
  have hns : ¬Squarefree b := by
    intro hs
    simp [squarefreeConvolutionError,squarefreeConvolution,hs] at hb
  have ho : orderedConvolution S w b ≠ 0 := by
    simpa only [squarefreeConvolutionError,squarefreeConvolution,ite_eq_right hns,sub_zero] using hb
  obtain ⟨f,hf,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero ho
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  have hprime : ∀ i, primaryPrime (f i) :=
    fun i => (hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)).1
  have hnot : ¬Function.Injective f := by
    intro hi
    exact hns (hfb ▸ (squarefree_prime_tuple_iff f hprime).mpr hi)
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hnot
  have hdvd : (f i)^2 ∣ ∏ k, f k := by
    have h := Finset.prod_dvd_prod_of_subset ({i,j}:Finset ι) Finset.univ f
      (Finset.subset_univ _)
    simpa [hne,hij,pow_two] using h
  have hprod0 : (∏ i, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => (hprime i).2.ne_zero)
  apply Finset.mem_filter.mpr
  refine ⟨mem_nonzeroNormBall.mpr ⟨?_,?_⟩,f i,?_,?_⟩
  · exact hbY
  · exact hfb ▸ hprod0
  · exact (hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)).2
  · exact hfb ▸ hdvd

private theorem convolutionError_cutoff_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (Y D E : ℝ),
      0 ≤ Y → 0 < D → 0 ≤ E →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ b ∈ B, ‖squarefreeConvolutionError S w b‖ ≤ E) →
      (∑ b ∈ B, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y*D^(-(1/2:ℝ))*E^2 := by
  obtain ⟨C,hC,hcount⟩ := largeSquareSupport_card_bound
  refine ⟨C,hC,?_⟩
  intro S w Y D E hY hD hE hS B hB hBY hbound
  let T := B.filter (fun b => squarefreeConvolutionError S w b ≠ 0)
  have hsub : T ⊆ largeSquareSupport Y D := by
    intro b hb
    exact convolutionError_mem_largeSquareSupport_of_norm S w Y D hS
      (hBY b (Finset.mem_filter.mp hb).1) (Finset.mem_filter.mp hb).2
  have hcard : (T.card:ℝ) ≤ C*Y*D^(-(1/2:ℝ)) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount Y D hY hD)
  have heq : (∑ b ∈ T, ‖squarefreeConvolutionError S w b‖^2) =
      ∑ b ∈ B, ‖squarefreeConvolutionError S w b‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hnot
    have hz : squarefreeConvolutionError S w b = 0 := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨hb,hn⟩)
    simp [hz]
  rw [← heq]
  calc
    _ ≤ ∑ _b ∈ T, E^2 := by
      apply Finset.sum_le_sum
      intro b hb
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) (hbound b (Finset.mem_filter.mp hb).1) 2
    _ = (T.card:ℝ)*E^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg E)

theorem primeConvolutionError_cutoff_power_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y c : ℝ),
      0 < Y → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ Y^c < norm p) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      (∑ b ∈ B, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y^(1-c/2)*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  obtain ⟨C,hC,hbound⟩ := convolutionError_cutoff_energy_bound (ι := ι)
  refine ⟨C,hC,?_⟩
  intro S w M Y c hY hM hS B hB hBY hw
  have hA : 0 ≤ ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))
  have hh := hbound S w Y (Y^c) _ hY.le (Real.rpow_pos_of_pos hY _) hA
    hS B hB hBY (fun b _ => convolutionError_norm_bound S w M
      (fun i p hp => (hS i p hp).1) hM hw b)
  have he : C*Y*(Y^c)^(-(1/2:ℝ)) = C*Y^(1-c/2) := by
    rw [← Real.rpow_mul hY.le]
    nth_rw 1 [← Real.rpow_one Y]
    rw [mul_assoc,← Real.rpow_add hY]
    congr 2
    ring
  simpa only [he] using hh

end CubicFirstMoment

end

end OAI
