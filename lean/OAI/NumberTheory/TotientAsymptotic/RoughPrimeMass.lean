import OAI.NumberTheory.TotientAsymptotic.RoughCollisionMass

namespace OAI

/-! Sharp reciprocal-prime mass and square-error bounds above a large cutoff. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prime_interval_reciprocal_eq {U V : ℝ} (hU : 2 ≤ U) (hUV : U ≤ V) :
    (∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),(p:ℝ)⁻¹)=
      primeReciprocalLE V-primeReciprocalLE U := by
  have hU0 : 0 ≤ U := by linarith
  have hV0 := hU0.trans hUV
  have hsub : primesUpTo U ⊆ primesUpTo V := by
    intro p hp
    obtain ⟨hp,hpU⟩ := (primesUpTo_mem hU0).mp hp
    exact (primesUpTo_mem hV0).mpr ⟨hp,hpU.trans hUV⟩
  have hsets : (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ))=primesUpTo V \ primesUpTo U := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_sdiff,primesUpTo_mem hU0,primesUpTo_mem hV0]
    constructor
    · rintro ⟨⟨hp,hpV⟩,hUp⟩
      exact ⟨⟨hp,hpV⟩,fun h => (not_le_of_gt hUp) h.2⟩
    · rintro ⟨⟨hp,hpV⟩,hnot⟩
      exact ⟨⟨hp,hpV⟩,lt_of_not_ge (fun h => hnot ⟨hp,h⟩)⟩
  rw [hsets,Finset.sum_sdiff_eq_sub hsub]
  rfl

lemma prime_interval_reciprocal_sharp : ∃ U₀ : ℝ,2 ≤ U₀ ∧ ∀ U V : ℝ,
    U₀ ≤ U → U ≤ V →
    (∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),(p:ℝ)⁻¹) ≤ B V-B U+1 := by
  obtain ⟨C,hC,hM⟩ := primeReciprocalLE_mertens
  refine ⟨Real.exp (2*C+2),?_,?_⟩
  · have hh := Real.add_one_le_exp (2*C+2)
    linarith
  · intro U V hU hUV
    have hU0 : 0 < U := (Real.exp_pos _).trans_le hU
    have hlog : 2*C+2 ≤ Real.log U := (Real.le_log_iff_exp_le hU0).mpr hU
    have hLU : 0 < Real.log U := by linarith
    have hV0 := hU0.trans_le hUV
    have hlogUV := Real.log_le_log hU0 hUV
    have hU2 : 2 ≤ U := by
      have hh := Real.add_one_le_exp (2*C+2)
      linarith
    have hu := hM U hU2
    have hv := hM V (hU2.trans hUV)
    have hqU : C/Real.log U ≤ 1/2 := (div_le_iff₀ hLU).mpr (by linarith)
    have hqV : C/Real.log V ≤ 1/2 := (div_le_iff₀ (hLU.trans_le hlogUV)).mpr (by linarith)
    rw [prime_interval_reciprocal_eq hU2 hUV]
    dsimp [B]
    linarith [(abs_le.mp hu).1,(abs_le.mp hv).2]

lemma prime_interval_square_tail {U V : ℝ} (hU : 0 < U) :
    (∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),((p:ℝ)^2)⁻¹) ≤ 2/U := by
  have hsub : (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)) ⊆
      Finset.Ioo ⌊U⌋₊ (⌊V⌋₊+1) := by
    intro p hp
    obtain ⟨hp,hUp⟩ := Finset.mem_filter.mp hp
    have hpV := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hpU : ⌊U⌋₊ < p := by exact_mod_cast (Nat.floor_le hU.le).trans_lt hUp
    exact Finset.mem_Ioo.mpr ⟨hpU,by omega⟩
  calc
    _ ≤ ∑ p ∈ Finset.Ioo ⌊U⌋₊ (⌊V⌋₊+1),((p:ℝ)^2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ ≤ 2/((⌊U⌋₊:ℝ)+1) := sum_Ioo_inv_sq_le (α:=ℝ) _ _
    _ ≤ 2/U := div_le_div_of_nonneg_left (by norm_num) hU (Nat.lt_floor_add_one U).le

/-- The full allocation estimate, allowing all multiplicities in the common product. -/
theorem rough_interval_allocation_bound : ∃ U₀ : ℝ,2 ≤ U₀ ∧ ∀ (c U V I : ℝ),
    1 ≤ c → U₀ ≤ U → 4*c^2 ≤ U → U ≤ V →
    c*(B V-B U+1) ≤ I → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ (n.primeFactorsList.length:ℝ) ≤ I ∧
      ∀ p ∈ n.primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) →
    (∑ n ∈ Q,c^(2*n.primeFactorsList.length)/(n:ℝ)) ≤ Real.exp (I*(Real.log c+1)+1) := by
  obtain ⟨U₀,hU₀,hprime⟩ := prime_interval_reciprocal_sharp
  refine ⟨U₀,hU₀,?_⟩
  intro c U V I hc hU hquad hUV hI Q hQ
  have hU2 := hU₀.trans hU
  have hU0 : 0 < U := by linarith
  have hcU : 2*c ≤ U := by nlinarith
  apply rough_collision_mass hc hcU hU2 hUV Q hQ (hprime U V hU hUV) ?_ hI
  calc
    _ ≤ 2*c^2*(2/U) := mul_le_mul_of_nonneg_left (prime_interval_square_tail (V:=V) hU0) (by positivity)
    _ = 4*c^2/U := by ring
    _ ≤ 1 := (div_le_one hU0).mpr hquad

end TotientAsymptotic

end

end OAI
