import Mathlib
import OAI.Computability.QuantumFactoring.UniversalSplit
import OAI.Computability.QuantumFactoring.RetrospectiveStatistics

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open AuxiliaryTree

/-- The distinguished component is selected from the supplied record, not by
factoring the requested integer a second time. -/
def recordFirst (f : FactorRecord) : ℕ :=
  if h : f.support.Nonempty then f.support.min' h else 0

lemma recordFirst_factorization {m : ℕ} (hm : 2 ≤ m) :
    recordFirst m.factorization=m.minFac := by
  have hp : m.minFac∈m.factorization.support :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd m,by omega⟩
  rw [recordFirst,dite_eq_left ⟨_,hp⟩]
  apply (Finset.min'_eq_iff _ _ _).mpr
  refine ⟨hp,?_⟩
  intro p h
  obtain ⟨hprime,hd,_⟩ := Nat.mem_primeFactors.mp h
  exact Nat.minFac_le_of_dvd hprime.two_le hd

lemma component_two_le {m : ℕ} (p : Component m) : 2 ≤ p.val^m.factorization p.val := by
  have hp := Nat.mem_primeFactors.mp p.property
  exact hp.1.two_le.trans (Nat.le_pow (hp.1.factorization_pos_of_dvd hp.2.2 hp.2.1))

lemma equivPi_natCast {m : ℕ} (hm : m≠0) (p : Component m) (a : ℕ) :
    ZMod.equivPi m hm (a : ZMod m) p=(a : ZMod (p.val^m.factorization p.val)) := by
  exact map_natCast ((Pi.evalRingHom _ p).comp (ZMod.equivPi m hm).toRingHom) a

lemma unitCRT_natCast {m : ℕ} (hm : m≠0) (p : Component m) (u : (ZMod m)ˣ) (a : ℕ)
    (ha : (a : ZMod m)=u) :
    ((unitCRT m hm u p : ComponentUnits m p) : ZMod (p.val^m.factorization p.val))=a := by
  change ZMod.equivPi m hm (u : ZMod m) p=_
  rw [←ha,equivPi_natCast]

noncomputable def dataResidueGood (data : FactorData) (a m : ℕ) : Prop :=
  a < m ∧ Nat.Coprime a m ∧
    ¬∀ p∈(dataRecord data m).support,
      padicValNat 2 (dataOrder data a (p^(dataRecord data m) p))=
      padicValNat 2 (dataOrder data a
        ((recordFirst (dataRecord data m))^((dataRecord data m) (recordFirst (dataRecord data m)))))

lemma data_component_order {M m a : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hd : m∣M)
    (u : (ZMod m)ˣ) (ha : (a : ZMod m)=u) (p : Component m) :
    dataOrder (trueData M) a (p.val^m.factorization p.val)=
      orderOf (unitCRT m (by omega) u p) := by
  exact dataOrder_correct hM (component_two_le p) ((Nat.ordProj_dvd m p.val).trans hd)
    (unitCRT m (by omega) u p) (unitCRT_natCast (by omega) p u a ha).symm

/-- The retrospective favorable test is a scan of supplied prime-power factors
and prime-stripping computations. It agrees with the CRT event on every actual
requested cofactor, including those below a node of the auxiliary tree. -/
lemma dataResidueGood_correct {M m n a : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hb : m < 2^n)
    (hd : m∣M) (u : (ZMod m)ˣ) (ha : a=(u : ZMod m).val) :
    dataResidueGood (trueData M) a m ↔
      FavorableUnit (by omega) hb (UniversalSplit.firstComponent hm) u := by
  let : NeZero m := ⟨by omega⟩
  have haz : (a : ZMod m)=u := by rw [ha,ZMod.natCast_zmod_val]
  have hac : a.Coprime m := (ZMod.isUnit_iff_coprime a m).mp (haz ▸ u.isUnit)
  have hal : a < m := ha ▸ (u : ZMod m).val_lt
  rw [dataResidueGood,and_iff_right hal,and_iff_right hac,dataRecord_correct hM hd,
    recordFirst_factorization hm]
  apply not_congr
  constructor
  · intro h p
    apply Fin.ext
    change padicValNat 2 (orderOf (unitCRT m _ u p))=_
    have he := h p.val p.property
    change padicValNat 2 (dataOrder (trueData M) a (p.val^m.factorization p.val))=
      padicValNat 2 (dataOrder (trueData M) a
        ((UniversalSplit.firstComponent hm).val^m.factorization (UniversalSplit.firstComponent hm).val)) at he
    rw [data_component_order hM hm hd u haz p,
      data_component_order hM hm hd u haz (UniversalSplit.firstComponent hm)] at he
    exact he
  · intro h p hp
    let pp : Component m := ⟨p,hp⟩
    change padicValNat 2 (dataOrder (trueData M) a (pp.val^m.factorization pp.val))=
      padicValNat 2 (dataOrder (trueData M) a
        ((UniversalSplit.firstComponent hm).val^m.factorization (UniversalSplit.firstComponent hm).val))
    rw [data_component_order hM hm hd u haz pp,
      data_component_order hM hm hd u haz (UniversalSplit.firstComponent hm)]
    exact congrArg Fin.val (h pp)

/-- Checking the uniquely specified CRT residue needs only congruences against
the supplied prime powers; no CRT search is hidden in the guess validator. -/
noncomputable def dataCanonicalResidue (data : FactorData) (a m : ℕ) : Prop :=
  a < m ∧ ∀ p∈(dataRecord data m).support,
    a%(p^(dataRecord data m) p)=
      if p=recordFirst (dataRecord data m) then 1 else p^(dataRecord data m) p-1

lemma canonical_component_val {m : ℕ} (hm : m≠0) (p₀ p : Component m) :
    ((unitCRT m hm (canonicalUnit hm p₀) p : ComponentUnits m p) :
      ZMod (p.val^m.factorization p.val)).val=
      if p.val=p₀.val then 1 else p.val^m.factorization p.val-1 := by
  classical
  rw [canonicalUnit_component]
  by_cases h : p=p₀
  · subst p
    simp only [ite_true,Units.val_one]
    exact ZMod.val_one'' (n:=p₀.val^m.factorization p₀.val) (by have := component_two_le p₀; omega)
  · have hn : p.val≠p₀.val := fun hh=>h (Subtype.ext hh)
    simp only [ite_eq_right h,ite_eq_right hn,Units.val_neg,Units.val_one]
    have hq := component_two_le p
    generalize p.val^m.factorization p.val=q at *
    cases q with
    | zero => omega
    | succ q => simpa only [Nat.add_sub_cancel] using ZMod.val_neg_one q

lemma dataCanonicalResidue_correct {M m : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hd : m∣M) (a : ℕ) :
    dataCanonicalResidue (trueData M) a m ↔
      a=(canonicalUnit (by omega) (UniversalSplit.firstComponent hm) : ZMod m).val := by
  let : NeZero m := ⟨by omega⟩
  let u := canonicalUnit (by omega : m≠0) (UniversalSplit.firstComponent hm)
  rw [dataCanonicalResidue,dataRecord_correct hM hd,recordFirst_factorization hm]
  constructor
  · rintro ⟨hal,h⟩
    have hz : (a : ZMod m)=u := by
      apply (ZMod.equivPi m (by omega : m≠0)).injective
      funext p
      apply ZMod.val_injective
      rw [equivPi_natCast,ZMod.val_natCast]
      change _=((unitCRT m (by omega) u p : ComponentUnits m p) :
        ZMod (p.val^m.factorization p.val)).val
      rw [canonical_component_val]
      exact h p.val p.property
    have he := congrArg (fun z : ZMod m=>z.val) hz
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hal] using he
  · intro ha
    refine ⟨ha ▸ (u : ZMod m).val_lt,?_⟩
    intro p hp
    let pp : Component m := ⟨p,hp⟩
    have haz : (a : ZMod m)=u := by rw [ha,ZMod.natCast_zmod_val]
    have he := congrArg (fun z : ZMod (p^m.factorization p)=>z.val)
      (unitCRT_natCast (by omega) pp u a haz)
    rw [ZMod.val_natCast,canonical_component_val] at he
    exact he.symm

end ExactQuantumFactoring


end

end OAI
