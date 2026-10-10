import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNormCRT
import OAI.NumberTheory.Ostmann.Arithmetic.ResidueHaar

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCRTIntegration
open ResidueHaar
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev UnitPair (M : ℕ) := (ZMod M)ˣ × (ZMod M)ˣ
abbrev MixedPair (M : ℕ) := ZMod M × (ZMod M)ˣ

instance product_neZero (p : ι → ℕ) [∀ i, NeZero (p i)] : NeZero (∏ i,p i) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (p i))⟩

def unitPairEquiv (p : ι → ℕ) (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    UnitPair (∏ i,p i) ≃ (∀ i,UnitPair (p i)) :=
  ((Supply.crtUnitsEquiv p hc).toEquiv.prodCongr
    (Supply.crtUnitsEquiv p hc).toEquiv).trans
      (DiagonalSmallResidueNorm.pairPiEquiv _ _)

abbrev mixedPairEquiv (p : ι → ℕ) (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    MixedPair (∏ i,p i) ≃ (∀ i,MixedPair (p i)) :=
  DiagonalSmallResidueNorm.crtPairEquiv p hc

omit [DecidableEq ι] in
@[simp] theorem unitPairEquiv_fst_coe (p : ι → ℕ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (z : UnitPair (∏ i,p i)) (i : ι) :
    ((unitPairEquiv p hc z i).1 : ZMod (p i)) =
      ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i))
        (z.1 : ZMod (∏ i,p i)) := Supply.crtUnitsEquiv_apply p hc z.1 i

omit [DecidableEq ι] in
@[simp] theorem unitPairEquiv_snd_coe (p : ι → ℕ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (z : UnitPair (∏ i,p i)) (i : ι) :
    ((unitPairEquiv p hc z i).2 : ZMod (p i)) =
      ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i))
        (z.2 : ZMod (∏ i,p i)) := Supply.crtUnitsEquiv_apply p hc z.2 i

theorem average_pi_product {β : ι → Type*} [∀ i,Fintype (β i)] (f : ∀ i,β i → ℂ) :
    average (fun z : ∀ i,β i => ∏ i,f i (z i)) = ∏ i,average (f i) := by
  simp only [average,mul_comm ((Fintype.card (∀ i,β i):ℂ)⁻¹),← div_eq_mul_inv]
  rw [← Fintype.prod_sum,Fintype.card_pi,Nat.cast_prod,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [div_eq_mul_inv,mul_comm]

theorem unit_joint_average (p : ι → ℕ) [∀ i,NeZero (p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : (∀ i,UnitPair (p i)) → ℂ) :
    average (fun z : UnitPair (∏ i,p i) => F (unitPairEquiv p hc z)) = average F :=
  average_equiv (unitPairEquiv p hc) F

theorem mixed_joint_average (p : ι → ℕ) [∀ i,NeZero (p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : (∀ i,MixedPair (p i)) → ℂ) :
    average (fun z : MixedPair (∏ i,p i) => F (mixedPairEquiv p hc z)) = average F :=
  average_equiv (mixedPairEquiv p hc) F

theorem unit_product_average (p : ι → ℕ) [∀ i,NeZero (p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (f : ∀ i,UnitPair (p i) → ℂ) :
    average (fun z : UnitPair (∏ i,p i) => ∏ i,f i (unitPairEquiv p hc z i)) =
      ∏ i,average (f i) :=
  (unit_joint_average p hc _).trans (average_pi_product f)

theorem mixed_product_average (p : ι → ℕ) [∀ i,NeZero (p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (f : ∀ i,MixedPair (p i) → ℂ) :
    average (fun z : MixedPair (∏ i,p i) => ∏ i,f i (mixedPairEquiv p hc z i)) =
      ∏ i,average (f i) :=
  (mixed_joint_average p hc _).trans (average_pi_product f)

theorem unitPair_card (M : ℕ) [NeZero M] :
    Fintype.card (UnitPair M)=M.totient^2 := by
  simp only [UnitPair,Fintype.card_prod,ZMod.card_units_eq_totient,pow_two]

theorem mixedPair_card (M : ℕ) [NeZero M] :
    Fintype.card (MixedPair M)=M*M.totient := by
  simp only [MixedPair,Fintype.card_prod,ZMod.card,ZMod.card_units_eq_totient]

end Ostmann.Arithmetic.HistoryCRTIntegration

end

end OAI
