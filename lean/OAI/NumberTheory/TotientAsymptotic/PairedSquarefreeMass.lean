import OAI.NumberTheory.TotientAsymptotic.CommonPrimeMass
import OAI.NumberTheory.TotientAsymptotic.SquarefreeCollisionMass

namespace OAI

/-! The application retains squarefreeness of the common band product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma paired_squarefree_allocation_bound (k : ℕ) (hk : 1 ≤ k)
    {U V I H : ℝ} (hU : 2 ≤ U) (hUV : U ≤ V)
    (hH : (∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),(p:ℝ)⁻¹) ≤ H)
    (hI : (k:ℝ)*H ≤ I) (Q : Finset (PairedFactors k))
    (hQ : ∀ f ∈ Q,0 < pairedProduct f ∧ pairedProduct f=∏ j,f.2 j)
    (hsq : ∀ f ∈ Q,Squarefree (pairedProduct f))
    (hΩ : ∀ f ∈ Q,((pairedProduct f).primeFactorsList.length:ℝ) ≤ I)
    (hpf : ∀ f ∈ Q,∀ p ∈ (pairedProduct f).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) :
    (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤ Real.exp (I*(Real.log k+1)) := by
  classical
  let N := Q.image pairedProduct
  let S := (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ))
  have hV0 : 0 ≤ V := by linarith
  have hN (n : ℕ) (hn : n ∈ N) : Squarefree n ∧ n.primeFactors ⊆ S ∧ (n.primeFactors.card:ℝ) ≤ I := by
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hn
    refine ⟨hsq f hf,?_,?_⟩
    · intro p hp
      have hp' : p ∈ (pairedProduct f).primeFactorsList := List.mem_toFinset.mp hp
      obtain ⟨hpU,hpV⟩ := hpf f hf p hp'
      exact Finset.mem_filter.mpr ⟨(primesUpTo_mem hV0).mpr
        ⟨Nat.prime_of_mem_primeFactorsList hp',hpV⟩,hpU⟩
    · rw [squarefree_primeFactors_card (hsq f hf)]
      exact hΩ f hf
  have hm := squarefree_collision_mass S N (by exact_mod_cast hk) hN hH hI
  have he : (∑ n ∈ N,(k:ℝ)^(2*n.primeFactorsList.length)/(n:ℝ))=
      ∑ n ∈ N,(k:ℝ)^(2*n.primeFactors.card)/(n:ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [squarefree_primeFactors_card (hN n hn).1]
  have hc := paired_factorization_mass_le k Q hQ
  have himage : Q.image (fun f : PairedFactors k => ∏ j,f.1 j)=N := by
    ext n
    simp only [N,Finset.mem_image,pairedProduct]
  rw [himage] at hc
  have hc' : (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤
      ∑ n ∈ N,(k:ℝ)^(2*n.primeFactorsList.length)/(n:ℝ) := by
    simpa only [pairedProduct,Nat.cast_prod] using hc
  exact hc'.trans (he.trans_le hm)

end TotientAsymptotic

end

end OAI
