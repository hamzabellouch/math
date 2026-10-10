import OAI.NumberTheory.Jacobsthal.Estimates.RichLinearFactor

namespace OAI

namespace Erdos970

section

namespace ErdosRichLine
open ErdosCriticalGeometry

theorem exponent_sum_le_one_cases (m : Fin 2 →₀ ℕ) (hm : m.sum (fun _ n => n) ≤ 1) :
    m = 0 ∨ m = Finsupp.single 0 1 ∨ m = Finsupp.single 1 1 := by
  have hs : m 0+m 1 ≤ 1 := by
    have he : m.sum (fun _ n => n) = m 0+m 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact Fin.sum_univ_two _
    rwa [he] at hm
  by_cases h0 : m 0 = 0
  · by_cases h1 : m 1 = 0
    · left
      ext i
      fin_cases i <;> simp [h0,h1]
    · right;right
      have h1' : m 1 = 1 := by omega
      ext i
      fin_cases i <;> simp [h0,h1']
  · right;left
    have h0' : m 0 = 1 := by omega
    have h1 : m 1 = 0 := by omega
    ext i
    fin_cases i <;> simp [h0',h1]

theorem linear_polynomial_form (F : MV ℂ) (hdeg : F.totalDegree ≤ 1) :
    F = MvPolynomial.C (F.coeff 0)+
      MvPolynomial.C (F.coeff (Finsupp.single 0 1))*MvPolynomial.X 0+
      MvPolynomial.C (F.coeff (Finsupp.single 1 1))*MvPolynomial.X 1 := by
  classical
  have he0 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ 0 := by
    intro h
    have hh := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h
    simp at hh
  have he1 : (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ 0 := by
    intro h
    have hh := congrArg (fun m : Fin 2 →₀ ℕ => m 1) h
    simp at hh
  have he01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have hh := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h
    simp at hh
  ext m
  by_cases hm : m.sum (fun _ n => n) ≤ 1
  · rcases exponent_sum_le_one_cases m hm with rfl | rfl | rfl <;>
      simp [MvPolynomial.coeff_C_mul,MvPolynomial.coeff_C,
        MvPolynomial.coeff_X,he0,he1,he01,Ne.symm he0,Ne.symm he1,Ne.symm he01]
  · have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    have hm1 : m ≠ Finsupp.single 0 1 := by rintro rfl; simp at hm
    have hm2 : m ≠ Finsupp.single 1 1 := by rintro rfl; simp at hm
    have hc : F.coeff m = 0 := by
      by_contra hn
      exact hm ((MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hn)).trans hdeg)
    simp [MvPolynomial.coeff_C_mul,MvPolynomial.coeff_C,
      MvPolynomial.coeff_X,Ne.symm hm0,Ne.symm hm1,Ne.symm hm2,hc]

theorem linear_polynomial_eval (F : MV ℂ) (hdeg : F.totalDegree ≤ 1) (x y : ℂ) :
    MvPolynomial.eval ![x,y] F = F.coeff 0+F.coeff (Finsupp.single 0 1)*x+
      F.coeff (Finsupp.single 1 1)*y := by
  conv_lhs => rw [linear_polynomial_form F hdeg]
  simp

end ErdosRichLine

end

end Erdos970

end OAI
