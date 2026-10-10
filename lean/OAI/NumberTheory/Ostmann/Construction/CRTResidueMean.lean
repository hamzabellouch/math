import OAI.NumberTheory.Ostmann.Construction.CRTCancellation

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction

theorem crt_cutoff_residue_mean {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀i,NeZero (p i)] [NeZero (∏i,p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀i,ZMod (p i) → ℂ) {X : ℝ} (hX : 0<X)
    (hperiod : ((∏i,p i:ℕ):ℝ)/4<X) :
    (∑'n : ℤ,(∏i,F i (n:ZMod (p i)))*SchwartzCutoff.psi ((n:ℝ)/X))=
      (X:ℂ)*𝓕 SchwartzCutoff.psi 0*(∏i,(∑x,F i x)/(p i:ℂ)) := by
  classical
  let Q := ∏i,p i
  let G : ZMod Q → ℂ := fun z => ∏i,F i (ZMod.prodEquivPi p hcop z i)
  let H : Fin Q → ℂ := fun r => G (ZMod.finEquiv Q r)
  have hmean : (∑r,H r)=∏i,∑x,F i x := by
    change (∑r : Fin Q,G (ZMod.finEquiv Q r))=_
    calc
      _ = ∑z : ZMod Q,G z := (ZMod.finEquiv Q).toEquiv.sum_comp G
      _ = _ := crt_physical_sum p hcop F
  have hterm (n : ℤ) : periodicResidueTest Q H n=∏i,F i (n:ZMod (p i)) := by
    unfold periodicResidueTest H
    rw [finEquiv_residue]
    unfold G
    congr 1
    funext i
    exact congrArg (fun f => F i (f i)) (map_intCast (ZMod.prodEquivPi p hcop) n)
  have h := cutoff_periodic_poisson Q H hX hperiod
  simp only [hterm,hmean] at h
  rw [h,Finset.prod_div_distrib]
  have hcast : (Q:ℂ)=∏i,(p i:ℂ) := by simp only [Q,Nat.cast_prod]
  rw [Complex.ofReal_natCast,hcast]
  ring

end Ostmann.Construction

end

end OAI
