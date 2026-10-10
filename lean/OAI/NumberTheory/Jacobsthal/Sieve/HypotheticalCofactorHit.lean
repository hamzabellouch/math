import OAI.NumberTheory.Jacobsthal.Estimates.EffectiveProgression

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseCells ErdosInverseHits ErdosHypotheticalTag

theorem cofactorHit_eq_of_residues (a b : ℕ → ℕ) (qf : ℕ) (hq : Squarefree qf)
    (hres : ∀ t ∈ qf.primeFactors,a t%t = b t%t) : cofactorHit qf a = cofactorHit qf b := by
  have ha := cofactorHit_spec qf hq a
  have hb := cofactorHit_spec qf hq b
  have hm : Nat.ModEq qf (cofactorHit qf a) (cofactorHit qf b) := by
    rw [cofactorHit_eq qf hq b]
    apply ((primeHitRepresentative_spec qf hq b).2.2 _).mp
    intro t ht
    exact (ha.2.2 t ht).trans (hres t ht)
  have hs := Nat.ModEq.sub ha.1 hb.1 hm (Nat.ModEq.refl 1)
  change (cofactorHit qf a-1)%qf = (cofactorHit qf b-1)%qf at hs
  rw [Nat.mod_eq_of_lt (by omega : cofactorHit qf a-1 < qf),
    Nat.mod_eq_of_lt (by omega : cofactorHit qf b-1 < qf)] at hs
  omega

theorem cofactorHit_hypothetical (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ) [NeZero p]
    (hq : Squarefree qf) (hqp : qf.Coprime p) :
    cofactorHit qf (hypotheticalClass a r p) = cofactorHit qf a := by
  apply cofactorHit_eq_of_residues _ _ qf hq
  intro t ht
  have htp : t ≠ p := by
    intro he
    subst t
    exact (Nat.prime_of_mem_primeFactors ht).coprime_iff_not_dvd.mp hqp.symm
      (Nat.dvd_of_mem_primeFactors ht)
  rw [hypothetical_other a r p t htp]

end ErdosVarianceEffective

end

end Erdos970

end OAI
