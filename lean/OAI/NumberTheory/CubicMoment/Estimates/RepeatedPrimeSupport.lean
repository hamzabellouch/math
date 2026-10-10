import OAI.NumberTheory.CubicMoment.Estimates.PrimeConvolutionBounds
import OAI.NumberTheory.CubicMoment.Estimates.LargeSquareSupport

namespace OAI

/-! The squarefree prime-convolution discrepancy has sparse support.
This supplies the support saving before the character-moment estimates. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def squarefreeConvolutionError (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (b : Eisenstein) : ℂ :=
  orderedConvolution S w b-squarefreeConvolution S w b

/-- Every surviving discrepancy coefficient is divisible by the square
of one of the large supported primes. -/
theorem convolutionError_mem_largeSquareSupport
    (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ) (Y D : ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p)
    (hY : ∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y)
    {b : Eisenstein} (hb : squarefreeConvolutionError S w b ≠ 0) :
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
  · exact hfb ▸ hY f hfs
  · exact hfb ▸ hprod0
  · exact (hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)).2
  · exact hfb ▸ hdvd

/-- Uniform energy saving for the actual discrepancy coefficients.
A divisor-type coefficient bound may be inserted as `E`; the support
saving itself is unconditional and independent of that bound. -/
theorem convolutionError_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (Y D E : ℝ),
      0 ≤ Y → 0 < D → 0 ≤ E →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖ ≤ E) →
      (∑ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y*D^(-(1/2:ℝ))*E^2 := by
  obtain ⟨C,hC,hcount⟩ := largeSquareSupport_card_bound
  refine ⟨C,hC,?_⟩
  intro S w Y D E hY hD hE hS hprod hbound
  let T := (orderedConvolutionSupport S).filter (fun b => squarefreeConvolutionError S w b ≠ 0)
  have hsub : T ⊆ largeSquareSupport Y D := by
    intro b hb
    exact convolutionError_mem_largeSquareSupport S w Y D hS hprod (Finset.mem_filter.mp hb).2
  have hcard : (T.card:ℝ) ≤ C*Y*D^(-(1/2:ℝ)) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount Y D hY hD)
  have heq : (∑ b ∈ T, ‖squarefreeConvolutionError S w b‖^2) =
      ∑ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖^2 := by
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

/-- The coefficient-amplitude hypothesis is discharged for the actual prime
convolution by the uniform prime-tuple multiplicity bound. -/
theorem primeConvolutionError_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y D : ℝ),
      0 ≤ Y → 0 < D → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      (∑ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y*D^(-(1/2:ℝ))*
          (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  obtain ⟨C,hC,hbound⟩ := convolutionError_energy_bound (ι := ι)
  refine ⟨C,hC,?_⟩
  intro S w M Y D hY hD hM hS hprod hw
  apply hbound S w Y D _ hY hD (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => hM i)))
    hS hprod
  intro b hb
  exact convolutionError_norm_bound S w M (fun i p hp => (hS i p hp).1) hM hw b

/-- With every prime larger than `Y^c`, the repeated-prime error has a
fixed support saving `Y^(-c/2)`, before the harmless smooth-weight factors. -/
theorem primeConvolutionError_power_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y c : ℝ),
      0 < Y → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ Y^c < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      (∑ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y^(1-c/2)*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  obtain ⟨C,hC,hbound⟩ := primeConvolutionError_energy_bound (ι := ι)
  refine ⟨C,hC,?_⟩
  intro S w M Y c hY hM hS hprod hw
  have h := hbound S w M Y (Y^c) hY.le (Real.rpow_pos_of_pos hY _) hM hS hprod hw
  have he : C*Y*(Y^c)^(-(1/2:ℝ)) = C*Y^(1-c/2) := by
    rw [← Real.rpow_mul hY.le]
    nth_rw 1 [← Real.rpow_one Y]
    rw [mul_assoc,← Real.rpow_add hY]
    congr 2
    ring
  simpa only [he] using h

end CubicFirstMoment

end

end OAI
