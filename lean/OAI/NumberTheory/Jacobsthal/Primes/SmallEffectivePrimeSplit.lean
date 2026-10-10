import OAI.NumberTheory.Jacobsthal.Estimates.EffectiveAvoidance

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosPrimitiveIntercept

theorem full_cofactor_coprime_small (qf : ℕ) (hq : Squarefree qf) (w : ℝ)
    (hlarge : ∀ u ∈ qf.primeFactors,w < (u : ℝ)) (t : ℕ) (ht : t.Prime) (htw : (t : ℝ) ≤ w) :
    qf.Coprime t := by
  apply Nat.Coprime.symm
  apply ht.coprime_iff_not_dvd.mpr
  intro hdiv
  have hh := hlarge t (Nat.mem_primeFactors.mpr ⟨ht,hdiv,hq.ne_zero⟩)
  linarith

theorem small_dvd_effectiveModulus_iff (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) (w : ℝ)
    (hlarge : ∀ u ∈ qf.primeFactors,w < (u : ℝ)) (t : ℕ) (ht : t.Prime) (htw : (t : ℝ) ≤ w) :
    t ∣ effectiveModulus a r qf ↔ t ∣ r.den := by
  rw [effectiveModulus,ht.dvd_mul]
  have htq : ¬t ∣ qf := ht.coprime_iff_not_dvd.mp (full_cofactor_coprime_small qf hq w hlarge t ht htw).symm
  have hbad : ¬t ∣ badPrimeProduct (fun u => (a u : ℤ)) r qf := by
    intro hd
    apply htq
    rw [← alignedCofactor_mul_bad (fun u => (a u : ℤ)) r qf hq]
    exact dvd_mul_of_dvd_right hd _
  simp only [hbad,or_false]

theorem small_effective_avoidance (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) (w : ℝ)
    (hlarge : ∀ u ∈ qf.primeFactors,w < (u : ℝ))
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p)
    (t : ℕ) (ht : t.Prime) (htw : (t : ℝ) ≤ w) (j : ℤ) :
    (t ∣ effectiveModulus a r qf →
      ((effectiveInteger a r qf p hHp j : ZMod t) ≠ (a t : ZMod t) ↔
        (intervalK p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ZMod t)+
          (p : ZMod t)*(j : ZMod t) ≠
          ((a t : ZMod t)-(ErdosInverseCells.cofactorHit qf a : ZMod t))*
            (↑((ZMod.unitOfCoprime qf (full_cofactor_coprime_small qf hq w hlarge t ht htw))⁻¹) : ZMod t))) ∧
    (¬t ∣ effectiveModulus a r qf →
      ((effectiveInteger a r qf p hHp j : ZMod t) ≠ (a t : ZMod t) ↔
        (p : ZMod t)*(alignedCofactor (fun u => (a u : ℤ)) r qf : ZMod t)*
          ((intervalM0 p (effectiveModulus a r qf) hHp (effectiveIntercept a r qf) : ZMod t)+
            (effectiveModulus a r qf : ZMod t)*(j : ZMod t)) ≠
          (r.den : ZMod t)*(a t : ZMod t)-(r.num : ZMod t))) := by
  constructor
  · intro _htH
    exact effective_avoidance_unit a r qf p hHp t (full_cofactor_coprime_small qf hq w hlarge t ht htw) j
  · intro htH
    exact effective_avoidance_not_dvd a r qf hq p hHp t ht htH j

end ErdosVarianceEffective

end

end Erdos970

end OAI
