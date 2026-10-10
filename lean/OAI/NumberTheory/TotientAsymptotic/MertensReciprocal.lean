import OAI.NumberTheory.TotientAsymptotic.PrimeIntervalMass
import PrimeNumberTheoremAnd.IEANTN.Mertens

namespace OAI

/-! Reciprocal prime sums from the second Mertens theorem. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma primeReciprocalLE_mertens : ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, 2≤x →
    |primeReciprocalLE x-Real.log (Real.log x)-Mertens.M| ≤ C/Real.log x := by
  refine ⟨Real.log 4+6+Mertens.E₁,?_,?_⟩
  · have hh := Mertens.E₁.nonneg
    have hl : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · intro x hx
    have hset : (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime=
        (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨hp2,hpx⟩,hp⟩
        exact ⟨⟨by omega,hpx⟩,hp⟩
      · rintro ⟨⟨_,hpx⟩,hp⟩
        exact ⟨⟨hp.two_le,hpx⟩,hp⟩
    simpa only [primeReciprocalLE,primesUpTo,hset,one_div,Mertens.E₂p] using Mertens.E₂p.abs_le hx

lemma primeReciprocalLT_mertens : ∃ D : ℝ, 0<D ∧ ∀ x : ℝ, 2≤x →
    |primeReciprocalLT x-Real.log (Real.log x)-Mertens.M| ≤ D/Real.log x := by
  obtain ⟨C,hC,hbound⟩ := primeReciprocalLE_mertens
  refine ⟨C+1,by linarith,?_⟩
  intro x hx
  have hx0 : 0<x := by linarith
  have hl : 0<Real.log x := Real.log_pos (by linarith)
  have hxlog : Real.log x≤x := by linarith [Real.log_le_sub_one_of_pos hx0]
  have he := (primeReciprocal_endpoint_error hx0).trans
    (one_div_le_one_div_of_le hl hxlog)
  calc
    _ = |(primeReciprocalLT x-primeReciprocalLE x)+
        (primeReciprocalLE x-Real.log (Real.log x)-Mertens.M)| := by congr 1; ring
    _ ≤ |primeReciprocalLT x-primeReciprocalLE x|+
        |primeReciprocalLE x-Real.log (Real.log x)-Mertens.M| := abs_add_le _ _
    _ ≤ 1/Real.log x+C/Real.log x := add_le_add he (hbound x hx)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
