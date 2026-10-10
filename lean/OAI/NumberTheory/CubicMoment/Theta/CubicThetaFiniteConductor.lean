import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveResidueConductorKernel

namespace OAI

/-! Additive conductors of the actual finite Fourier pairing. A function
that factors through a smaller residue ring has Fourier support in the
annihilator of the reduction kernel. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma finiteFourier_translation_support {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f : R → ℂ) (a m : R)
    (hf : ∀ x b : R, f (x+m*b)=f x)
    (hF : (∑ x : R, f x*ψ (a*x))≠0) : m*a=0 := by
  classical
  by_contra hma
  have hn : ψ.mulShift (m*a)≠1 := hψ hma
  obtain ⟨b,hb⟩ : ∃ b : R, ψ ((m*a)*b)≠1 := by
    by_contra he
    push Not at he
    apply hn
    ext b
    simpa only [AddChar.mulShift_apply,AddChar.one_apply] using he b
  let F : ℂ := ∑ x : R, f x*ψ (a*x)
  have he : F=ψ ((m*a)*b)*F := by
    calc
      F = ∑ x : R, f (x+m*b)*ψ (a*(x+m*b)) :=
        (Equiv.sum_comp (Equiv.addRight (m*b)) _).symm
      _ = ψ ((m*a)*b)*F := by
        simp_rw [hf,mul_add,ψ.map_add_eq_mul]
        dsimp only [F]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [show a*(m*b)=(m*a)*b by ring]
        ring
  exact hF (eq_zero_of_mul_eq_self_left hb he.symm)

theorem residueFourier_reduction_support {q d : Eisenstein} (hq : q≠0)
    [Fintype (Residues q)] (f : Residues q → ℂ) (h : Eisenstein)
    (hf : ∀ x b : Residues q,
      f (x+Ideal.Quotient.mk (modulus q) d*b)=f x)
    (hF : (∑ x : Residues q, f x * residueFourierChar q hq
      (Ideal.Quotient.mk (modulus q) h*x))≠0) : q ∣ d*h := by
  have he := finiteFourier_translation_support (residueFourierChar q hq)
    (residueFourierChar_isPrimitive q hq) f (Ideal.Quotient.mk (modulus q) h)
    (Ideal.Quotient.mk (modulus q) d) hf hF
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rwa [map_mul]

theorem residueFourier_inflation_support {q d : Eisenstein} (hq : q≠0)
    [Fintype (Residues q)] (hd : d ∣ q) (f : Residues d → ℂ) (h : Eisenstein)
    (hF : (∑ x : Residues q, f (residueReduction hd x) * residueFourierChar q hq
      (Ideal.Quotient.mk (modulus q) h*x))≠0) : q ∣ d*h := by
  apply residueFourier_reduction_support hq _ h _ hF
  intro x b
  congr 1
  rw [map_add,map_mul,residueReduction_mk]
  have hz : Ideal.Quotient.mk (modulus d) d=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl d))
  rw [hz,zero_mul,add_zero]

end CubicFirstMoment

end

end OAI
