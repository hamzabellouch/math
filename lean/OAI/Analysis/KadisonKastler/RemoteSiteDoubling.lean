import OAI.Analysis.KadisonKastler.TwoRatioSelfAbsorption
import OAI.Analysis.KadisonKastler.TwoRatioFiniteSites
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! # Interleaving two site families beyond a finite prefix -/

namespace KadisonKastler

/-- The left copy starts beyond the prefix, which belongs to the right copy. -/
def remoteNatDoubling (n : ℕ) : (ℕ ⊕ ℕ) ≃ ℕ :=
  (Equiv.sumComm ℕ ℕ).trans
    ((Equiv.sumCongr (finSumNatEquiv n).symm (Equiv.refl ℕ)).trans
      ((Equiv.sumAssoc (Fin n) ℕ ℕ).trans
        ((Equiv.sumCongr (Equiv.refl (Fin n)) Equiv.natSumNatEquivNat).trans
          (finSumNatEquiv n))))

theorem remoteNatDoubling_left (n i : ℕ) :
    remoteNatDoubling n (Sum.inl i)=n+(2*i+1) := rfl

theorem remoteNatDoubling_right_prefix {n i : ℕ} (hi : i < n) :
    remoteNatDoubling n (Sum.inr i)=i := by
  change (finSumNatEquiv n)
    (Sum.map (fun j : Fin n => j) Equiv.natSumNatEquivNat
      ((Equiv.sumAssoc (Fin n) ℕ ℕ) (Sum.inl ((finSumNatEquiv n).symm i))))=i
  rw [finSumNatEquiv_symm_apply_of_lt hi]
  rfl

def remoteTwoRatioDoubling (n : ℕ) : (TwoRatioSite ⊕ TwoRatioSite) ≃ TwoRatioSite :=
  (Equiv.sumSumSumComm ℕ ℕ ℕ ℕ).trans
    (Equiv.sumCongr (remoteNatDoubling n) (remoteNatDoubling n))

theorem remoteTwoRatioDoubling_parameter (n : ℕ) (i : TwoRatioSite ⊕ TwoRatioSite) :
    twoRatioSiteParameter (remoteTwoRatioDoubling n i)=
      Sum.elim twoRatioSiteParameter twoRatioSiteParameter i := by
  rcases i with ((i | i) | (i | i)) <;> rfl

theorem remoteTwoRatioDoubling_prefix {n : ℕ} {i : TwoRatioSite}
    (hi : i ∈ twoRatioFiniteSites n) :
    remoteTwoRatioDoubling n (Sum.inr i)=i := by
  rcases i with i | i
  · change Sum.inl (remoteNatDoubling n (Sum.inr i))=Sum.inl i
    rw [remoteNatDoubling_right_prefix ((inl_mem_twoRatioFiniteSites i n).mp hi)]
  · change Sum.inr (remoteNatDoubling n (Sum.inr i))=Sum.inr i
    rw [remoteNatDoubling_right_prefix ((inr_mem_twoRatioFiniteSites i n).mp hi)]

end KadisonKastler

end OAI
