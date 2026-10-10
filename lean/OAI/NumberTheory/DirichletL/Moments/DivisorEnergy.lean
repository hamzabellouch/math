import OAI.NumberTheory.DirichletL.Moments.DivisorExtraction

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorEnergy
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι α ρ : Type*} [DecidableEq ι]

def allocatedPolynomial (D : Ideal O) (s : Finset ι) (T : Finset α)
    (v : α → ι → Ideal O) (F : ρ → α → ℂ) (a : Allocation D s) (h : ρ) : ℂ :=
  ∑ j ∈ T, allocationTerm D s (v j) a*F h j

theorem finite_mask_regroup (D : Ideal O) (hD : Squarefree D) (s : Finset ι)
    (T : Finset α) (v : α → ι → Ideal O) (F : ρ → α → ℂ) (h : ρ) :
    (∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0) =
      ∑ a : Allocation D s, allocatedPolynomial D s T v F a h := by
  have ht (j : α) : (if D∣∏ i ∈ s,v j i then F h j else 0) =
      ∑ a : Allocation D s, allocationTerm D s (v j) a*F h j := by
    have he := congrArg (fun w : ℂ => w*F h j) (squarefree_mask_allocation D hD s (v j))
    simpa only [ite_mul,one_mul,zero_mul,Finset.sum_mul] using he
  simp_rw [ht]
  rw [Finset.sum_comm]
  rfl

theorem allocation_card_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), D ≠ 0 → ∀ s : Finset ι, s.card ≤ N →
      (Fintype.card (Allocation D s):ℝ) ≤ C*(Ideal.absNorm D:ℝ)^ε := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/N) (div_pos hε hNr)
  refine ⟨C^N,pow_pos hC _,?_⟩
  intro D hD s hs
  have hn : 0 ≤ (Ideal.absNorm D:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ((2:ℝ)^(primeSupport D).card)^s.card := by exact_mod_cast allocation_card_bound D s
    _ ≤ ((2:ℝ)^(primeSupport D).card)^N := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hs
    _ ≤ (C*(Ideal.absNorm D:ℝ)^(ε/N))^N := pow_le_pow_left₀ (by positivity) (hb D hD) N
    _ = C^N*(Ideal.absNorm D:ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hn]
      congr 2
      field_simp

theorem allocated_energy_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), Squarefree D → ∀ s : Finset ι, s.card ≤ N →
      ∀ (T : Finset α) (v : α → ι → Ideal O) (F : ρ → α → ℂ) (rows : Finset ρ),
      (∑ h ∈ rows, ‖∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a : Allocation D s, ∑ h ∈ rows, ‖allocatedPolynomial D s T v F a h‖^2 := by
  obtain ⟨C,hC,hcard⟩ := allocation_card_small_power (ι := ι) N hN ε hε
  refine ⟨C,hC,?_⟩
  intro D hD s hs T v F rows
  have hrow (h : ρ) : ‖∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0‖^2 ≤
      (Fintype.card (Allocation D s):ℝ)*∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖^2 := by
    rw [finite_mask_regroup D hD s T v F h]
    calc
      _ ≤ (∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _a : Allocation D s => (1:ℝ))
          (fun a => ‖allocatedPolynomial D s T v F a h‖))
  calc
    _ ≤ ∑ h ∈ rows, (Fintype.card (Allocation D s):ℝ)*
        ∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖^2 :=
      Finset.sum_le_sum (fun h _ => hrow h)
    _ = (Fintype.card (Allocation D s):ℝ)*
        ∑ a : Allocation D s, ∑ h ∈ rows, ‖allocatedPolynomial D s T v F a h‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD.ne_zero s hs)
      (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end SevenEighths.CenteredMomentDivisorEnergy

end

end OAI
