import OAI.NumberTheory.Ostmann.Arithmetic.PrimeBandHarmonicTransferGeometry

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.PrimeBandHarmonicTransfer

theorem finite_band_harmonic_bound (f : ℕ→ℝ) (hf : ∀p,0≤f p)
    (δ T₀ a b : ℝ) (hδ : 0≤δ) (ha : 0≤a) (hb : 0≤b)
    (hstart : T₀≤Real.exp (a-Real.log 2))
    (hband : ∀T:ℝ,T₀≤T → ∀Q:Finset ℕ,(∀p∈Q,p.Prime) →
      (∀p∈Q,T≤Real.log (p:ℝ) ∧ Real.log (p:ℝ)≤2*T) →
      (∑p∈Q,(Real.log (p:ℝ)/(p:ℝ))*f p)≤δ*T)
    (P : Finset ℕ) (hprime : ∀p∈P,p.Prime)
    (hP : ∀p∈P,a≤Real.log (Real.log (p:ℝ)) ∧ Real.log (Real.log (p:ℝ))≤b) :
    (∑p∈P,f p/(p:ℝ))≤δ*(b/Real.log 2+1) := by
  classical
  let J := Finset.range (⌊b/Real.log 2⌋₊+1)
  let Q : ℕ→Finset ℕ := fun j => P.filter (fun p : ℕ => logDyadicIndex (Real.log (p:ℝ))=j)
  have hmap : ∀p∈P,logDyadicIndex (Real.log (p:ℝ))∈J := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (logDyadicIndex_le (hP p hp).2))
  have he : (∑j∈J,∑p∈Q j,f p/(p:ℝ))=∑p∈P,f p/(p:ℝ) :=
    Finset.sum_fiberwise_of_maps_to hmap (fun p => f p/(p:ℝ))
  have hblock : ∀j∈J,(∑p∈Q j,f p/(p:ℝ))≤δ := by
    intro j hj
    by_cases hQ : (Q j).Nonempty
    · obtain ⟨p,hp⟩ := hQ
      have hpP := (Finset.mem_filter.mp hp).1
      have hjp := (Finset.mem_filter.mp hp).2
      have hT₀ : T₀≤logDyadicScale j := by
        rw [←hjp]
        exact hstart.trans (logDyadicScale_lower (hP p hpP).1)
      have hbounds : ∀p∈Q j,logDyadicScale j≤Real.log (p:ℝ) ∧
          Real.log (p:ℝ)≤2*logDyadicScale j := by
        intro p hp
        obtain ⟨hpP,hpj⟩ := Finset.mem_filter.mp hp
        have hpp := hprime p hpP
        have hp1 : (1:ℝ)<p := by exact_mod_cast hpp.one_lt
        have hh := logDyadicIndex_bounds (Real.log_pos hp1) (ha.trans (hP p hpP).1)
        rw [hpj] at hh
        exact ⟨hh.1,hh.2.le⟩
      have hsum := hband (logDyadicScale j) hT₀ (Q j)
        (fun p hp => hprime p (Finset.mem_filter.mp hp).1) hbounds
      have hh : logDyadicScale j*(∑p∈Q j,f p/(p:ℝ))≤
          ∑p∈Q j,(Real.log (p:ℝ)/(p:ℝ))*f p := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p hp
        calc
          _ ≤ Real.log (p:ℝ)*(f p/(p:ℝ)) :=
            mul_le_mul_of_nonneg_right (hbounds p hp).1 (div_nonneg (hf p) (Nat.cast_nonneg p))
          _ = _ := by ring
      apply (mul_le_mul_iff_right₀ (Real.exp_pos ((j:ℝ)*Real.log 2))).mp
      simpa only [logDyadicScale,mul_comm] using hh.trans hsum
    · have hz : Q j=∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
      simpa only [hz,Finset.sum_empty] using hδ
  calc
    _ = ∑j∈J,∑p∈Q j,f p/(p:ℝ) := he.symm
    _ ≤ ∑j∈J,δ := Finset.sum_le_sum hblock
    _ = δ*((⌊b/Real.log 2⌋₊:ℝ)+1) := by
      simp only [Finset.sum_const,nsmul_eq_mul,J,Finset.card_range,Nat.cast_add,Nat.cast_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by have hh := Nat.floor_le (div_nonneg hb log_two_pos.le); linarith) hδ

end Ostmann.Arithmetic.PrimeBandHarmonicTransfer

end

end OAI
