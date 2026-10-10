import Mathlib
import OAI.Computability.QuantumFactoring.FactorController
import OAI.Computability.QuantumFactoring.CRTLevels

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma component_modulus_two_lt {m : ℕ} (hm : m≠0) (hodd : Odd m) (p : Component m) :
    2 < p.val^m.factorization p.val := by
  have hp := Nat.mem_primeFactors.mp p.property
  have hp2 : p.val≠2 := by
    intro he
    have hdiv : 2∣m := he ▸ hp.2.1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)
  exact (lt_of_le_of_ne hp.1.two_le (Ne.symm hp2)).trans_le
    (Nat.le_pow (hp.1.factorization_pos_of_dvd hm hp.2.1))

lemma unitCRT_apply {m : ℕ} (hm : m≠0) (a : (ZMod m)ˣ) (p : Component m) :
    unitCRT m hm a p=Units.map (ZMod.castHom (Nat.ordProj_dvd m p.val)
      (ZMod (p.val^m.factorization p.val))).toMonoidHom a := by
  apply Units.ext
  change ZMod.equivPi m hm (a : ZMod m) p = _
  exact RingHom.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom (fun p : Component m => ZMod (p.val^m.factorization p.val)) p).comp
      (ZMod.equivPi m hm).toRingHom)
    (ZMod.castHom (Nat.ordProj_dvd m p.val) (ZMod (p.val^m.factorization p.val)))) (a : ZMod m)

/-- A favorable CRT event supplies a proper split from the actual true order. -/
theorem favorable_split {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (hodd : Odd m)
    (p₀ : Component m) (a : (ZMod m)ˣ) (hf : FavorableUnit (by omega : m≠0) hb p₀ a) :
    2 ∣ orderOf a ∧ FactorController.ProperDivisor m (splitGcd a) := by
  classical
  obtain ⟨p,hp⟩ := not_forall.mp hf
  have hneq : padicValNat 2 (orderOf (unitCRT m (by omega) a p)) ≠
      padicValNat 2 (orderOf (unitCRT m (by omega) a p₀)) := by
    exact fun he => hp (Fin.ext he)
  simp only [unitCRT_apply] at hneq
  have hproper := splitGcd_proper_of_unequal_components hm
    (component_modulus_two_lt (by omega) hodd p).le
    (component_modulus_two_lt (by omega) hodd p₀).le
    (Nat.ordProj_dvd m p.val) (Nat.ordProj_dvd m p₀.val) a hneq
  let f := Units.map (ZMod.castHom (Nat.ordProj_dvd m p.val)
    (ZMod (p.val^m.factorization p.val))).toMonoidHom
  let g := Units.map (ZMod.castHom (Nat.ordProj_dvd m p₀.val)
    (ZMod (p₀.val^m.factorization p₀.val))).toMonoidHom
  have hr : orderOf a≠0 := (orderOf_pos a).ne'
  have hp' := level_le_of_dvd hr (orderOf_map_dvd f a)
  have h₀ := level_le_of_dvd hr (orderOf_map_dvd g a)
  have heven : 2∣orderOf a := dvd_of_one_le_padicValNat (by
    change padicValNat 2 (orderOf (f a)) ≠ padicValNat 2 (orderOf (g a)) at hneq
    omega)
  exact ⟨heven,hproper⟩

/-- The distinguished CRT residue used in the list-completion branch. The
parameter p₀ is subsequently chosen as the least prime component. -/
noncomputable def canonicalUnit {m : ℕ} (hm : m≠0) (p₀ : Component m) : (ZMod m)ˣ :=
  (unitCRT m hm).symm (fun p => if p=p₀ then 1 else -1)

lemma canonicalUnit_component {m : ℕ} (hm : m≠0) (p₀ p : Component m) :
    unitCRT m hm (canonicalUnit hm p₀) p=if p=p₀ then 1 else -1 := by
  rw [canonicalUnit,MulEquiv.apply_symm_apply]

lemma component_neg_one_order {m : ℕ} (hm : m≠0) (hodd : Odd m) (p : Component m) :
    orderOf (-1 : ComponentUnits m p)=2 := by
  have hd := component_modulus_two_lt hm hodd p
  let : Fact (1 < p.val^m.factorization p.val) := ⟨by omega⟩
  rw [← orderOf_units]
  change orderOf (-1 : ZMod (p.val^m.factorization p.val))=2
  rw [orderOf_neg_one,ringChar.eq _ (p.val^m.factorization p.val),ite_eq_right (by omega)]

lemma canonicalUnit_favorable {m n : ℕ} (hm : m≠0) (hb : m < 2^n) (hodd : Odd m)
    (p₀ p₁ : Component m) (hne : p₁≠p₀) :
    FavorableUnit hm hb p₀ (canonicalUnit hm p₀) := by
  intro h
  have he := congrArg Fin.val (h p₁)
  simp only [componentLevel,canonicalUnit_component,ite_eq_right hne,
    component_neg_one_order hm hodd p₁] at he
  norm_num at he

end ExactQuantumFactoring


end

end OAI
