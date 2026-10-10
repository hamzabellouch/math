import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTProjectionBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryCRTProjection
open ResidueHaar HistoryCRTIntegration

def unitPairMap {m M : ℕ} (hd : m∣M) : UnitPair M→*UnitPair m :=
  (ZMod.unitsMap hd).prodMap (ZMod.unitsMap hd)

def mixedPairMap {m M : ℕ} (hd : m∣M) (z : MixedPair M) : MixedPair m :=
  (ZMod.castHom hd (ZMod m) z.1,ZMod.unitsMap hd z.2)

theorem unitPairMap_surjective {m M : ℕ} [NeZero M] (hd : m∣M) :
    Function.Surjective (unitPairMap hd) := by
  rintro ⟨x,y⟩
  obtain ⟨a,ha⟩ := ZMod.unitsMap_surjective hd x
  obtain ⟨b,hb⟩ := ZMod.unitsMap_surjective hd y
  exact ⟨(a,b),Prod.ext ha hb⟩

theorem mixedPairMap_surjective {m M : ℕ} [NeZero M] (hd : m∣M) :
    Function.Surjective (mixedPairMap hd) := by
  rintro ⟨x,y⟩
  obtain ⟨a,ha⟩ := ZMod.castHom_surjective hd x
  obtain ⟨b,hb⟩ := ZMod.unitsMap_surjective hd y
  exact ⟨(a,b),Prod.ext ha hb⟩

theorem unitPair_fiber_card {m M : ℕ} [NeZero M] (hd : m∣M) (z : UnitPair m) :
    Nat.card {x : UnitPair M // unitPairMap hd x=z}=Nat.card (unitPairMap hd).ker :=
  card_fiber_eq_kernel _ (unitPairMap_surjective hd) z

theorem unit_pair_average {m M : ℕ} [NeZero m] [NeZero M] (hd : m∣M)
    (F : UnitPair m→ℂ) : average (fun z : UnitPair M=>F (unitPairMap hd z))=average F :=
  average_surjective_hom (unitPairMap hd) (unitPairMap_surjective hd) F

def mixedPairHom {m M : ℕ} (hd : m∣M) :
    Multiplicative (ZMod M)×(ZMod M)ˣ→*Multiplicative (ZMod m)×(ZMod m)ˣ :=
  (ZMod.castHom hd (ZMod m)).toAddMonoidHom.toMultiplicative.prodMap (ZMod.unitsMap hd)

theorem mixedPair_fiber_card {m M : ℕ} [NeZero M] (hd : m∣M) (z : MixedPair m) :
    Nat.card {x : MixedPair M // mixedPairMap hd x=z}=Nat.card (mixedPairHom hd).ker := by
  exact card_fiber_eq_kernel (mixedPairHom hd) (mixedPairMap_surjective hd) z

theorem mixed_pair_average {m M : ℕ} [NeZero m] [NeZero M] (hd : m∣M)
    (F : MixedPair m→ℂ) : average (fun z : MixedPair M=>F (mixedPairMap hd z))=average F := by
  let eM : MixedPair M ≃ Multiplicative (ZMod M)×(ZMod M)ˣ := Equiv.refl _
  let em : MixedPair m ≃ Multiplicative (ZMod m)×(ZMod m)ˣ := Equiv.refl _
  have hsource := average_equiv eM (fun z => F (mixedPairHom hd z))
  have htarget := average_equiv em F
  exact hsource.trans ((average_surjective_hom (mixedPairHom hd)
    (mixedPairMap_surjective hd) F).trans htarget.symm)

end Ostmann.Arithmetic.HistoryCRTProjection

end

end OAI
