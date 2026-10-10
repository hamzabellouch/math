import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyContext

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts Characters
open Characters.Template (unitConvention unitConvention_coe)

theorem unitConvention_natCast_map (N Q : ℕ) (hNQ : N∣Q) (n : ℕ)
    (x : (ZMod Q)ˣ) (hx : (n:ZMod Q)=x) :
    unitConvention (n:ZMod N)=ZMod.unitsMap hNQ x := by
  have he : (n:ZMod N)=(ZMod.unitsMap hNQ x:ZMod N) := by
    rw [ZMod.unitsMap_def,Units.coe_map,← hx]
    exact (map_natCast (ZMod.castHom hNQ (ZMod N)) n).symm
  apply Units.ext
  rw [unitConvention_coe _ (he.symm ▸ Units.isUnit (ZMod.unitsMap hNQ x))]
  exact he

theorem supported_known_rawSplit {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {comp hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p comp hp hm left right).Supported V outside)
    (hsize : ∀ q∈a.small,V (l+1)<q.value)
    (R K j : ℕ) (hf : a.frequency.natAbs∣R)
    (g : KnownGiants R) (hg : GiantsMatch R j g a)
    (x y : (ZMod (R^(K+2)))ˣ)
    (hx : (bulkProduct hp:ZMod (R^(K+2)))=x)
    (hy : (bulkProduct hm:ZMod (R^(K+2)))=y) :
    rawSplitConstraint a.frequency.natAbs left.root.frequency right.root.frequency
      (knownCoefficient R j a.frequency hf (fixedProduct hp) (g j).1)
      (knownCoefficient R j a.frequency hf (fixedProduct hm) (g j).2)
      (ZMod.unitsMap (Template.frequency_dvd_precision R K hf) (x*y))
      (ZMod.unitsMap (Template.frequency_dvd_precision R K hf) x) := by
  rw [hg.1,hg.2,knownCoefficient_natCast,knownCoefficient_natCast,map_mul]
  have hL := unitConvention_natCast_map a.frequency.natAbs (R^(K+2))
    (Template.frequency_dvd_precision R K hf) (bulkProduct hp) x hx
  have hR := unitConvention_natCast_map a.frequency.natAbs (R^(K+2))
    (Template.frequency_dvd_precision R K hf) (bulkProduct hm) y hy
  have hh := supported_rawSplit hs hsize
  simpa only [coefficientUnit,bulkUnit,hL,hR] using hh

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
