import OAI.NumberTheory.Jacobsthal.Harmonic.PrimeFourierSieve

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def deviationResidues (N : ℕ) (S : Finset ℤ) (T : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun e => T/(N : ℝ) < |(integerResidueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ)|)

noncomputable def exceptionalResidues (N : ℕ) (S : Finset ℤ) (T : ℝ) : Finset (ZMod N) :=
  (deviationResidues N S T).image (fun e : ℕ => (e : ZMod N))

theorem exceptionalResidues_card (N : ℕ) (S : Finset ℤ) (T : ℝ) :
    (exceptionalResidues N S T).card = (deviationResidues N S T).card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  have haN := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hbN := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have hh := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt haN,ZMod.val_natCast_of_lt hbN] using hh

theorem mem_exceptionalResidues (N : ℕ) [NeZero N] (S : Finset ℤ) (T : ℝ) (e : ZMod N) :
    e ∈ exceptionalResidues N S T ↔
      T/(N : ℝ) < |(residueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ)| := by
  constructor
  · intro he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨haN,hdev⟩ := Finset.mem_filter.mp ha
    rw [residueCount_at_val,ZMod.val_natCast_of_lt (Finset.mem_range.mp haN)]
    exact hdev
  · intro he
    apply Finset.mem_image.mpr
    refine ⟨e.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt e),?_⟩,ZMod.natCast_zmod_val e⟩
    rwa [residueCount_at_val] at he

theorem exceptional_fraction_le_variance (N : ℕ) (hN : 0 < N) (S : Finset ℤ) (T : ℝ) (hT : 0 < T) :
    ((exceptionalResidues N S T).card : ℝ)/(N : ℝ) ≤
      (N : ℝ)*integerResidueVariance N S/T^2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hthreshold : 0 ≤ T/(N : ℝ) := (div_pos hT hNR).le
  have hsum : ((deviationResidues N S T).card : ℝ)*(T/(N : ℝ))^2 ≤ integerResidueVariance N S := by
    calc
      _ = ∑ _e ∈ deviationResidues N S T,(T/(N : ℝ))^2 := by simp
      _ ≤ ∑ e ∈ deviationResidues N S T,((integerResidueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ))^2 := by
        apply Finset.sum_le_sum
        intro e he
        have hh := (Finset.mem_filter.mp he).2
        calc
          _ ≤ |(integerResidueCount N S e : ℝ)-(S.card : ℝ)/(N : ℝ)|^2 :=
            pow_le_pow_left₀ hthreshold hh.le 2
          _ = _ := sq_abs _
      _ ≤ integerResidueVariance N S :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  rw [exceptionalResidues_card]
  apply (div_le_div_iff₀ hNR (sq_pos_of_pos hT)).mpr
  calc
    _ = (((deviationResidues N S T).card : ℝ)*(T/(N : ℝ))^2)*(N : ℝ)^2 := by field_simp
    _ ≤ integerResidueVariance N S*(N : ℝ)^2 := mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
    _ = _ := by ring

end ErdosInverseSpectrum

end

end Erdos970

end OAI
