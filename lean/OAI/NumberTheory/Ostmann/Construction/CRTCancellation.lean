import OAI.NumberTheory.Ostmann.Construction.CutoffPoisson

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem finEquiv_residue (Q : ℕ) [NeZero Q] (n : ℤ) :
    ZMod.finEquiv Q ((Int.divModEquiv Q n).2) = (n : ZMod Q) := by
  have hfin (r : Fin Q) : ZMod.finEquiv Q r = ((r : ℕ) : ZMod Q) := by
    cases Q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ Q =>
      apply Fin.ext
      change r.val = r.val % (Q+1)
      exact (Nat.mod_eq_of_lt r.isLt).symm
  rw [hfin]
  have hrepr : (Int.divModEquiv Q n).1*(Q:ℤ)+((Int.divModEquiv Q n).2 : ℕ)=n :=
    (Int.divModEquiv Q).symm_apply_apply n
  have h := congrArg (fun z : ℤ => (z : ZMod Q)) hrepr
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    mul_zero, zero_add] using h

theorem crt_physical_sum {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) :
    (∑ z : ZMod (∏ i, p i), ∏ i, F i (ZMod.prodEquivPi p hcop z i)) =
      ∏ i, ∑ z : ZMod (p i), F i z := by
  classical
  calc
    _ = ∑ z : (∀ i, ZMod (p i)), ∏ i, F i (z i) :=
      (ZMod.prodEquivPi p hcop).toEquiv.sum_comp _
    _ = _ := (Fintype.prod_sum F).symm

theorem crt_singleton_cutoff_zero {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (j : ι) (hzero : ∑ z, F j z=0)
    {X : ℝ} (hX : 0<X) (hperiod : ((∏ i, p i : ℕ):ℝ)/4<X) :
    (∑' n : ℤ, (∏ i, F i (n : ZMod (p i))) *
      SchwartzCutoff.psi ((n:ℝ)/X))=0 := by
  classical
  let Q := ∏ i, p i
  let G : ZMod Q → ℂ := fun z => ∏ i, F i (ZMod.prodEquivPi p hcop z i)
  let H : Fin Q → ℂ := fun r => G (ZMod.finEquiv Q r)
  have hmean : ∑ r, H r=0 := by
    change (∑ r : Fin Q, G (ZMod.finEquiv Q r))=0
    calc
      _ = ∑ z : ZMod Q, G z := (ZMod.finEquiv Q).toEquiv.sum_comp G
      _ = 0 := by
        change (∑ z : ZMod (∏ i, p i), ∏ i, F i (ZMod.prodEquivPi p hcop z i))=0
        rw [crt_physical_sum p hcop F]
        exact Finset.prod_eq_zero (Finset.mem_univ j) hzero
  have hterm (n : ℤ) : periodicResidueTest Q H n=∏ i, F i (n : ZMod (p i)) := by
    unfold periodicResidueTest H
    rw [finEquiv_residue]
    unfold G
    congr 1
    funext i
    have hc := map_intCast (ZMod.prodEquivPi p hcop) n
    exact congrArg (fun f => F i (f i)) hc
  have h := cutoff_periodic_mean_zero Q H hX hperiod hmean
  simpa only [hterm] using h

end Ostmann.Construction

end

end OAI
