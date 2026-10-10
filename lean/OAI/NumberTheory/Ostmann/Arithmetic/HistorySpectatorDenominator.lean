import OAI.NumberTheory.Ostmann.Arithmetic.HistoryResidueRegular
import OAI.NumberTheory.Ostmann.Construction.Coefficient

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryResidueRegular
open Construction

theorem outside_cofactor_coprime {q l : ℕ} (hqprime : q.Prime)
    {V : ℕ → ℕ} {outside : List ℕ} {h : History l}
    (hs : h.Supported V outside) (hq : q ∈ outside) :
    Nat.Coprime (outsideProduct outside / q) q := by
  have hp := (List.pairwise_append.mp (History.supported_root_coprime hs)).2.1
  have he := List.perm_cons_erase hq
  have hp' : (q :: outside.erase q).Pairwise Nat.Coprime :=
    (he.pairwise_iff Nat.Coprime.symm).mp hp
  have hc : Nat.Coprime q (outside.erase q).prod :=
    Nat.coprime_list_prod_right_iff.mpr (List.pairwise_cons.mp hp').1
  have hd : outsideProduct outside = q*(outside.erase q).prod := he.prod_eq
  rw [hd,Nat.mul_div_cancel_left _ hqprime.pos]
  exact hc.symm

def denominatorUnit {q l : ℕ} [Fact q.Prime] {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) (hq : q ∈ outside) : (ZMod q)ˣ :=
  (ZMod.isUnit_iff_coprime (outsideProduct outside/q) q).mpr
    (outside_cofactor_coprime (Fact.out) hs hq) |>.unit

@[simp] theorem denominatorUnit_coe {q l : ℕ} [Fact q.Prime] {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) (hq : q ∈ outside) :
    (denominatorUnit hs hq : ZMod q) = (outsideProduct outside/q : ℕ) :=
  IsUnit.unit_spec _

end Ostmann.Arithmetic.HistoryResidueRegular

end

end OAI
