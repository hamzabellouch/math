import OAI.NumberTheory.JointDickman.Amplification.AllLargeLowVanishing
import OAI.NumberTheory.JointDickman.Amplification.MultiplicityMargins

namespace OAI

/-! # One tolerance and vanishing errors for every grid cell -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

private theorem finite_positive_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ t : ℝ, 0 < t ∧ ∀ i ∈ s, t ≤ f i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨t,ht,hbound⟩ := ih (fun i hi => hf i (mem_insert_of_mem hi))
    refine ⟨min (f a) t,lt_min (hf a (mem_insert_self _ _)) ht,?_⟩
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound i hi)

/-- The actual sieve estimates at both endpoints hold for the same positive
tolerance, with a nonnegative vanishing majorant on every later grid cell. -/
theorem exists_grid_multiplicity_bounds
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 10000 ≤ L) {η cap : ℝ} (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      smallMultiplicityExponent L τ < 8/1000 ∧
      ∃ E : ℕ → ℕ → ℝ, (∀ k B, 0 ≤ E k B) ∧
        (∀ k ∈ Icc 4 L, Tendsto (E k) atTop (𝓝 0)) ∧
        ∀ᶠ B : ℕ in atTop, ∀ k ∈ Icc 4 L,
          ∀ (C : ℝ) (A D V : Finset ℕ) (j : ℕ),
            A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
            RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
            (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
            0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
            η*(B : ℝ)^(32/100 : ℝ) ≤ j →
            tiltedAllLargeLowPairCount B L k j τ C (1/(L : ℝ)) A D V ≤ E k B ∧
            tiltedAllLargeHighPairCount B L k j τ C (1/(L : ℝ)) A D V ≤ E k B := by
  let I := ↥(Icc 4 L)
  let : Fintype I := FinsetCoe.fintype _
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hg (k : I) : 0 < (k.val : ℝ)/L :=
    div_pos (by exact_mod_cast (show 0 < k.val from lt_of_lt_of_le (by norm_num) (mem_Icc.mp k.property).1)) hLpos
  have hg1 (k : I) : (k.val : ℝ)/L ≤ 1 :=
    (div_le_one hLpos).mpr (by exact_mod_cast (mem_Icc.mp k.property).2)
  have hgap (k : I) : 2*(1/(L : ℝ)) < (k.val : ℝ)/L := by
    rw [mul_one_div]
    exact (div_lt_div_iff_of_pos_right hLpos).mpr
      (by exact_mod_cast (show 2 < k.val from lt_of_lt_of_le (by norm_num) (mem_Icc.mp k.property).1))
  have hk (k : I) : k.val ∈ Icc 1 L := mem_Icc.mpr ⟨by have := (mem_Icc.mp k.property).1; omega,(mem_Icc.mp k.property).2⟩
  have hlo (k : I) := all_large_low_class_vanishing hFord hM (hk k) rfl (hg k) (hg1 k)
    (show 0 < 1/(L : ℝ) by positivity) (hgap k)
    (by norm_num : (0 : ℝ) < 1/200) (by norm_num) (by norm_num : (0 : ℝ) < 1/1000) hη
  have hhi (k : I) := all_large_high_class_vanishing hFord hM (hk k) rfl (hg k) (hg1 k)
    (show 0 < 1/(L : ℝ) by positivity) (hgap k)
    (by norm_num : (0 : ℝ) < 1/200) (by norm_num) (by norm_num : (0 : ℝ) < 1/1000) hη
  choose tlo htlo hlo using hlo
  choose thi hthi hhi using hhi
  obtain ⟨θ,hθ,hθle⟩ := finite_positive_bound (univ : Finset I)
    (fun k => min (tlo k) (thi k)) (fun k _ => lt_min (htlo k) (hthi k))
  obtain ⟨τ,hτ,hτbound,hτsampling,hsmall,hloss⟩ :=
    exists_common_multiplicity_tolerance hL (lt_min hcap hθ)
  have hτlo (k : I) : τ ≤ tlo k :=
    hτbound.trans ((min_le_right _ _).trans ((hθle k (mem_univ k)).trans (min_le_left _ _)))
  have hτhi (k : I) : τ ≤ thi k :=
    hτbound.trans ((min_le_right _ _).trans ((hθle k (mem_univ k)).trans (min_le_right _ _)))
  choose Elo hElolim hElobound using fun k => hlo k τ hτ (hτlo k) hloss
  choose Ehi hEhilim hEhibound using fun k => hhi k τ hτ (hτhi k) hloss
  let E := fun k B => if hk : k ∈ Icc 4 L then |Elo ⟨k,hk⟩ B|+|Ehi ⟨k,hk⟩ B| else 0
  refine ⟨τ,hτ,hτbound.trans (min_le_left _ _),hτsampling,hsmall,E,?_,?_,?_⟩
  · intro k B
    dsimp only [E]
    split_ifs <;> positivity
  · intro k hk
    have hh := (hElolim ⟨k,hk⟩).abs.add (hEhilim ⟨k,hk⟩).abs
    simpa only [E,dite_eq_left hk,abs_zero,add_zero] using hh
  · have hboth : ∀ᶠ B : ℕ in atTop, ∀ k : I,
        (∀ (C : ℝ) (A D V : Finset ℕ) (j : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ j →
          tiltedAllLargeLowPairCount B L k.val j τ C (1/(L : ℝ)) A D V ≤ Elo k B) ∧
        (∀ (C : ℝ) (A D V : Finset ℕ) (j : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ j →
          tiltedAllLargeHighPairCount B L k.val j τ C (1/(L : ℝ)) A D V ≤ Ehi k B) :=
      eventually_all.mpr (fun k => (hElobound k).and (hEhibound k))
    filter_upwards [hboth] with B hB
    intro k hk C A D V j hA hD hV hAr hDr hVr hsize hj hcut hjB hjlow
    have hlo := (hB ⟨k,hk⟩).1 C A D V j hA hD hV hAr hDr hVr hsize hj hcut hjB hjlow
    have hhi := (hB ⟨k,hk⟩).2 C A D V j hA hD hV hAr hDr hVr hsize hj hcut hjB hjlow
    dsimp only [E]
    rw [dite_eq_left hk]
    constructor
    · exact hlo.trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
    · exact hhi.trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))

end JointDickman

end OAI
