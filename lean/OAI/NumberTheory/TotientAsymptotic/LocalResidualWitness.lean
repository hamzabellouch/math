import OAI.NumberTheory.TotientAsymptotic.PPTPrefixGrouping

namespace OAI

/-! Choose bad preimages on each distinct residual family before dyadic counting. -/
noncomputable section
namespace TotientAsymptotic

theorem local_bad_residual_witness {d q : ℕ} (hd : 0 < d)
    (hqpos : 0 < q) (hq : q.totient=d) (R : Finset ℕ)
    (hR : ∀ r ∈ R,PPTBadResidual d r) :
    ∃ F : ℕ → ℕ,Set.InjOn F (R : Set ℕ) ∧
      (∀ r ∈ R,0 < F r ∧ (F r).totient=d*r.totient ∧ ¬r ∣ F r ∧
        largestPrimeFactor (F r) ≠ largestPrimeFactor r) ∧
      ∀ r ∈ R,(∃ s ∈ R,s≠r ∧ s.totient=r.totient) →
        ∃ s ∈ R,F r=s*q := by
  obtain ⟨F,hinj,hF,hseed⟩ := ppt_injective_bad_preimages_seed_branch hd hqpos hq R
    (fun r hr => ⟨(hR r hr).1,(hR r hr).2.1⟩)
    (fun r hr => (hR r hr).2.2.1)
  refine ⟨F,hinj,?_,hseed⟩
  intro r hr
  have hh := hF r hr
  exact ⟨hh.1,hh.2.1,hh.2.2,(hR r hr).2.2.2 (F r) hh.1 hh.2.1 hh.2.2⟩

end TotientAsymptotic

end

end OAI
