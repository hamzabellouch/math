import OAI.Combinatorics.ContingencyTables.Transport.IntegerLaw

namespace OAI

/-! # Integer realization of the exact residual correction law -/

namespace ContingencyTables.IntegerResidualCorrection
open ResidualMixture
open scoped BigOperators Classical
noncomputable section

variable {A : Type*} [Fintype A] [Nonempty A] {Q : ℕ}

def count (p : IntegerLaw A Q) (T : ℕ) (a : A) : ℕ :=
  (residualNumerator Q T (fun x => (p.count x : ℤ)) a).toNat

lemma cast_count (p : IntegerLaw A Q) (T : ℕ) (hQ : 0<Q) (hT : 0<T)
    (hdom : ∀ x,(1-1/(T:ℚ))*(p.toRational hQ).mass x≤uniformMass (α := A)) (a : A) :
    (count p T a : ℤ)=residualNumerator Q T (fun x => (p.count x : ℤ)) a := by
  apply Int.toNat_of_nonneg
  apply residualNumerator_nonnegative
  · exact_mod_cast hQ
  · exact_mod_cast hT
  · simpa only [IntegerLaw.toRational,Int.cast_natCast] using hdom

/-- The finite integer weights sum to `|A|*Q`; all truncations are exact
because the ordinary law is pointwise dominated by the uniform law. -/
def law (p : IntegerLaw A Q) (T : ℕ) (hQ : 0<Q) (hT : 0<T)
    (hdom : ∀ x,(1-1/(T:ℚ))*(p.toRational hQ).mass x≤uniformMass (α := A)) :
    IntegerLaw A (Fintype.card A*Q) where
  count := count p T
  total := by
    apply Int.ofNat_injective
    change ((∑ a,count p T a : ℕ) : ℤ)=((Fintype.card A*Q : ℕ) : ℤ)
    rw [Nat.cast_sum]
    simp_rw [cast_count p T hQ hT hdom]
    have ht : (∑ x,(p.count x:ℤ))=(Q:ℤ) := by
      rw [←Nat.cast_sum,p.total]
    simpa only [Nat.cast_mul] using residualNumerator_total (Q:ℤ) (T:ℤ)
      (fun x => (p.count x:ℤ)) ht

lemma denominator_pos (hQ : 0<Q) : 0<Fintype.card A*Q :=
  Nat.mul_pos Fintype.card_pos hQ

lemma law_mass (p : IntegerLaw A Q) (T : ℕ) (hQ : 0<Q) (hT : 0<T)
    (hdom : ∀ x,(1-1/(T:ℚ))*(p.toRational hQ).mass x≤uniformMass (α := A)) (a : A) :
    ((law p T hQ hT hdom).toRational (denominator_pos hQ)).mass a=
      residualMass (p.toRational hQ) (1/(T:ℚ)) a := by
  have hc := congrArg (fun z : ℤ => (z:ℚ)) (cast_count p T hQ hT hdom a)
  simp only [Int.cast_natCast] at hc
  change (count p T a:ℚ)/(Fintype.card A*Q:ℕ)=_
  rw [hc,Nat.cast_mul]
  exact residualNumerator_quotient (Q:ℤ) (T:ℤ) (fun x => (p.count x:ℤ))
    (by exact_mod_cast hQ.ne') (by exact_mod_cast hT.ne') a

/-- The ordinary branch and the explicit integer-weight branch have
exactly uniform combined mass, before physical execution is compiled. -/
theorem mixture_exact (p : IntegerLaw A Q) (T : ℕ) (hQ : 0<Q) (hT : 0<T)
    (hdom : ∀ x,(1-1/(T:ℚ))*(p.toRational hQ).mass x≤uniformMass (α := A)) (a : A) :
    (1-1/(T:ℚ))*(p.toRational hQ).mass a+
      (1/(T:ℚ))*((law p T hQ hT hdom).toRational (denominator_pos hQ)).mass a=
        uniformMass (α := A) := by
  rw [law_mass]
  exact ResidualMixture.mixture_exact _ (one_div_ne_zero (by exact_mod_cast hT.ne')) a

end
end ContingencyTables.IntegerResidualCorrection

end OAI
