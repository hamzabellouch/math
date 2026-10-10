import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencySplit
import OAI.NumberTheory.Ostmann.Characters.TemplateResidueExposure

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts Characters
open Characters.Template (unitConvention unitConvention_coe)

abbrev KnownGiants (R : ℕ) := (j : ℕ) → ZMod (R^(j+2)) × ZMod (R^(j+2))

def GiantsMatch (R j : ℕ) (g : KnownGiants R) (a : State) : Prop :=
  (g j).1=(a.giantPlus:ZMod (R^(j+2))) ∧
  (g j).2=(a.giantMinus:ZMod (R^(j+2)))

def initialGiants (R : ℕ) (a : State) : KnownGiants R :=
  fun _ => (a.giantPlus,a.giantMinus)

@[simp] theorem initialGiants_matches (R j : ℕ) (a : State) :
    GiantsMatch R j (initialGiants R a) a := ⟨rfl,rfl⟩

def knownCoefficient (R j : ℕ) (s : ℤ) (hs : s.natAbs∣R)
    (fixed : ℕ) (x : ZMod (R^(j+2))) : (ZMod s.natAbs)ˣ :=
  unitConvention (ZMod.castHom (Template.frequency_dvd_precision R j hs)
    (ZMod s.natAbs) x * (fixed:ZMod s.natAbs))

theorem knownCoefficient_natCast (R j : ℕ) (s : ℤ) (hs : s.natAbs∣R)
    (fixed X : ℕ) : knownCoefficient R j s hs fixed (X:ZMod (R^(j+2))) =
      unitConvention ((X*fixed:ℕ):ZMod s.natAbs) := by
  simp only [knownCoefficient,map_natCast,Nat.cast_mul]

def childGiants (R j : ℕ) (s v w : ℤ) (fixedPlus fixedMinus comp : ℕ)
    (g : KnownGiants R) (XL XR : ZMod (R^(j+3))) (right : Bool) : KnownGiants R :=
  let red := ZMod.castHom (pow_dvd_pow R (by omega : j+2≤j+3)) (ZMod (R^(j+2)))
  let pivot := nodePivot (R^(j+3)) (R^(j+2)) s v w
    (g (j+1)).1 (g (j+1)).2 ((fixedPlus:ZMod (R^(j+3)))*XL)
    ((fixedMinus:ZMod (R^(j+3)))*XR) (unitConvention (comp:ZMod (R^(j+2))))
  Function.update g j (pivot,red (if right then (g (j+1)).2 else (g (j+1)).1))

theorem childGiants_matches {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {comp hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p comp hp hm left right).Supported V outside)
    (R j : ℕ) (hf : a.frequency.natAbs∣R)
    (hu : Nat.Coprime (comp.map SmallSlot.value).prod R)
    (g : KnownGiants R) (hg : GiantsMatch R (j+1) g a)
    (XL XR : ZMod (R^(j+3)))
    (hXL : XL=(bulkProduct hp:ZMod (R^(j+3))))
    (hXR : XR=(bulkProduct hm:ZMod (R^(j+3)))) (b : Bool) :
    GiantsMatch R j
      (childGiants R j a.frequency left.root.frequency right.root.frequency
        (fixedProduct hp) (fixedProduct hm) (comp.map SmallSlot.value).prod g XL XR b)
      (if b then right.root else left.root) := by
  have hU : IsUnit ((comp.map SmallSlot.value).prod:ZMod (R^(j+2))) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (hu.pow_right _)
  have hunit : ((comp.map SmallSlot.value).prod:ZMod (R^(j+2)))=
      unitConvention ((comp.map SmallSlot.value).prod:ZMod (R^(j+2))) :=
    (unitConvention_coe _ hU).symm
  have hP := supported_nodePivot hs R (j+2) hf
    (unitConvention ((comp.map SmallSlot.value).prod:ZMod (R^(j+2)))) hunit
  have hc := History.supported_child_giants hs
  have hx (xs : List SmallSlot) :
      (fixedProduct xs:ZMod (R^(j+3)))*(bulkProduct xs:ZMod (R^(j+3)))=
        ((xs.map SmallSlot.value).prod:ZMod (R^(j+3))) := by
    rw [product_split,Nat.cast_mul]
  cases b <;> constructor <;>
    simp only [childGiants,Function.update_self,Bool.false_eq_true,
      ite_false,ite_true,hg.1,hg.2,hXL,hXR,hx,map_natCast,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]
  · exact hP
  · exact hP

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
