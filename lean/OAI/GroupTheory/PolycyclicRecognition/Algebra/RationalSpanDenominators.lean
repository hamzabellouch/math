import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalAbelianRank

namespace OAI

/-! # Clearing denominators in a rational span -/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem exists_nsmul_mem_integral_span {S : Set V} {v : V}
    (hv : v ∈ Submodule.span ℚ S) :
    ∃ n : ℕ, 0 < n ∧ n • v ∈ Submodule.span ℤ S := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨1, by omega, by simpa using Submodule.subset_span hv⟩
  | zero => exact ⟨1, by omega, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [nsmul_add]
    apply Submodule.add_mem
    · simpa only [← mul_nsmul, Submodule.mem_toAddSubmonoid] using
        (Submodule.span ℤ S).nsmul_mem hnx m
    · simpa only [← mul_nsmul, Nat.mul_comm, Submodule.mem_toAddSubmonoid] using
        (Submodule.span ℤ S).nsmul_mem hmy n
  | smul r v _ hv =>
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨n * r.den, Nat.mul_pos hn r.den_pos, ?_⟩
    have hcoeff : ((n * r.den : ℕ) : ℚ) * r = (r.num : ℚ) * (n : ℚ) := by
      have hden : (r.den : ℚ) * r = r.num := by
        calc
          (r.den : ℚ) * r = (r.den : ℚ) * ((r.num : ℚ) / (r.den : ℚ)) :=
            congrArg (fun z : ℚ => (r.den : ℚ) * z) r.num_div_den.symm
          _ = r.num := by field_simp
      push_cast
      calc
        (n : ℚ) * (r.den : ℚ) * r = (n : ℚ) * ((r.den : ℚ) * r) := mul_assoc _ _ _
        _ = (r.num : ℚ) * n := by rw [hden, mul_comm]
    have he : (n * r.den) • (r • v) = r.num • (n • v) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
        ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul, hcoeff]
    rw [he]
    exact (Submodule.span ℤ S).smul_mem r.num hnv

end PolycyclicRecognition

end

end OAI
