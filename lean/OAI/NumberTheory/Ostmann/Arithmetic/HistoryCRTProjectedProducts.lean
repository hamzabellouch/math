import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTProjectionActual

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCRTIntegration
open ResidueHaar HistoryCRTProjection
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def projectedRingPair {M n : ℕ} (hd : n∣M) (z : ZMod M×ZMod M) : ZMod n×ZMod n :=
  (ZMod.castHom hd (ZMod n) z.1,ZMod.castHom hd (ZMod n) z.2)

theorem unitPairMap_fst_coe {M n : ℕ} (hd : n∣M) (z : UnitPair M) :
    ((unitPairMap hd z).1 : ZMod n) = ZMod.castHom hd (ZMod n) (z.1 : ZMod M) := rfl

theorem unitPairMap_snd_coe {M n : ℕ} (hd : n∣M) (z : UnitPair M) :
    ((unitPairMap hd z).2 : ZMod n) = ZMod.castHom hd (ZMod n) (z.2 : ZMod M) := rfl

theorem mixedPairMap_fst {M n : ℕ} (hd : n∣M) (z : MixedPair M) :
    (mixedPairMap hd z).1 = ZMod.castHom hd (ZMod n) z.1 := rfl

theorem mixedPairMap_snd_coe {M n : ℕ} (hd : n∣M) (z : MixedPair M) :
    ((mixedPairMap hd z).2 : ZMod n) = ZMod.castHom hd (ZMod n) (z.2 : ZMod M) := rfl

theorem unit_projected_product_average (p : ι → ℕ) [∀ i,NeZero (p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    {M : ℕ} [NeZero M] (hd : (∏ i,p i)∣M)
    (f : ∀ i,(ZMod (p i)×ZMod (p i))→ℂ) :
    average (fun z : UnitPair M => ∏ i,f i
      (projectedRingPair ((Finset.dvd_prod_of_mem p (Finset.mem_univ i)).trans hd)
        ((z.1:ZMod M),(z.2:ZMod M)))) =
      ∏ i,average (fun z : UnitPair (p i) => f i ((z.1:ZMod (p i)),(z.2:ZMod (p i)))) := by
  have he := (unit_pair_average hd (fun z : UnitPair (∏ i,p i) =>
    ∏ i,f i (((unitPairEquiv p hc z i).1:ZMod (p i)),
      ((unitPairEquiv p hc z i).2:ZMod (p i))))).trans
      (unit_product_average p hc (fun i z => f i ((z.1:ZMod (p i)),(z.2:ZMod (p i)))))
  convert he using 1
  congr 1
  funext z
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  apply Prod.ext <;> simp only [projectedRingPair,unitPairEquiv_fst_coe,
    unitPairEquiv_snd_coe,unitPairMap_fst_coe,unitPairMap_snd_coe,
    ←RingHom.comp_apply,ZMod.castHom_comp]

theorem mixed_projected_product_average (p : ι → ℕ) [∀ i,NeZero (p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    {M : ℕ} [NeZero M] (hd : (∏ i,p i)∣M)
    (f : ∀ i,(ZMod (p i)×ZMod (p i))→ℂ) :
    average (fun z : MixedPair M => ∏ i,f i
      (projectedRingPair ((Finset.dvd_prod_of_mem p (Finset.mem_univ i)).trans hd)
        (z.1,(z.2:ZMod M)))) =
      ∏ i,average (fun z : MixedPair (p i) => f i (z.1,(z.2:ZMod (p i)))) := by
  have he := (mixed_pair_average hd (fun z : MixedPair (∏ i,p i) =>
    ∏ i,f i ((mixedPairEquiv p hc z i).1,((mixedPairEquiv p hc z i).2:ZMod (p i))))).trans
      (mixed_product_average p hc (fun i z => f i (z.1,(z.2:ZMod (p i)))))
  convert he using 1
  congr 1
  funext z
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  apply Prod.ext <;> simp only [projectedRingPair,mixedPairEquiv,
    DiagonalSmallResidueNorm.crtPairEquiv_fst,DiagonalSmallResidueNorm.crtPairEquiv_snd_coe,
    mixedPairMap_fst,mixedPairMap_snd_coe,←RingHom.comp_apply,ZMod.castHom_comp]

end Ostmann.Arithmetic.HistoryCRTIntegration

end

end OAI
