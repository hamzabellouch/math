import OAI.NumberTheory.CubicMoment.Estimates.RamifiedCubicValues
import OAI.NumberTheory.CubicGram.CubeExtraction

namespace OAI

/-! Exact separation of a nonzero Eisenstein integer into a global unit,
a ramified-prime power, and a primary factor. -/
noncomputable section
namespace CubicFirstMoment

lemma unit_ramified_primary_decomposition {v : Eisenstein} (hv : v ≠ 0) :
    ∃ (u : Eisensteinˣ) (k : ℕ) (a : Eisenstein), primary a ∧
      v=(u:Eisenstein)*lambdaE^k*a := by
  have H : ∀ v : Eisenstein, v ≠ 0 →
      ∃ (u : Eisensteinˣ) (k : ℕ) (a : Eisenstein), primary a ∧
        v=(u:Eisenstein)*lambdaE^k*a := by
    intro v
    induction v using WfDvdMonoid.induction_on_irreducible with
    | zero => simp
    | unit b hb =>
      intro _
      obtain ⟨u,rfl⟩ := hb
      exact ⟨u,0,1,primary_one,by simp⟩
    | mul b p hb hp ih =>
      intro _
      obtain ⟨u,k,a,ha,he⟩ := ih hb
      by_cases hp3 : IsCoprime p 3
      · obtain ⟨w,hw,hpw⟩ := unit_lift_mod_three (residue_isUnit_of_isCoprime hp3.symm)
        obtain ⟨w,rfl⟩ := hw
        refine ⟨u*w⁻¹,k,(p*(w:Eisenstein))*a,primary_mul hpw ha,?_⟩
        rw [he,Units.val_mul]
        linear_combination -(p*(u:Eisenstein)*lambdaE^k*a)*w.mul_inv
      · have hpd : p ∣ (3:Eisenstein) := by
          by_contra h
          exact hp3 (isRelPrime_iff_isCoprime.mp (hp.isRelPrime_iff_not_dvd.mpr h))
        have hpl : p ∣ lambdaE := hp.prime.dvd_of_dvd_pow
          (by rw [lambdaE_sq]; exact dvd_neg.mpr hpd)
        obtain ⟨w,hw⟩ := hp.associated_of_dvd lambdaE_prime.irreducible hpl
        refine ⟨u*w⁻¹,k+1,a,ha,?_⟩
        rw [he,Units.val_mul,pow_succ,←hw]
        linear_combination -(p*(u:Eisenstein)*(p*(w:Eisenstein))^k*a)*w.mul_inv
  exact H v hv

end CubicFirstMoment

end

end OAI
