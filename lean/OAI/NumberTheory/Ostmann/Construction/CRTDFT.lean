import OAI.NumberTheory.Ostmann.Construction.CRTCharacters

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def crtFrequency (p : ι → ℕ) (s : ℤ) (i : ι) : ZMod (p i) :=
  (s:ZMod (p i))*(otherProduct p i:ZMod (p i))⁻¹

theorem stdAddChar_crt_frequency (p : ι → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i,p i)] (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (s : ℤ) (z : ZMod (∏ i,p i)) :
    ZMod.stdAddChar (-(z*(s:ZMod (∏ i,p i)))) =
      ∏ i, ZMod.stdAddChar (-((ZMod.prodEquivPi p hcop z) i*crtFrequency p s i)) := by
  rw [stdAddChar_crt ι p hcop]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  simp only [interpolationCoordinate,crtFrequency,map_neg,map_mul,map_intCast,
    Pi.neg_apply,Pi.mul_apply,Pi.intCast_apply]
  ring

theorem dft_crt_product (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i,p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (s : ℤ) :
    ZMod.dft (fun z : ZMod (∏ i,p i) => ∏ i,F i (ZMod.prodEquivPi p hcop z i))
      (s:ZMod (∏ i,p i)) = ∏ i, ZMod.dft (F i) (crtFrequency p s i) := by
  simp only [ZMod.dft_apply, smul_eq_mul]
  simp_rw [stdAddChar_crt_frequency p hcop s]
  simp_rw [← Finset.prod_mul_distrib]
  calc
    _ = ∑ x : ∀ i,ZMod (p i), ∏ i,
        ZMod.stdAddChar (-(x i*crtFrequency p s i))*F i (x i) :=
      (ZMod.prodEquivPi p hcop).toEquiv.sum_comp _
    _ = _ := (Fintype.prod_sum (κ := fun i => ZMod (p i))
      (fun i x => ZMod.stdAddChar (-(x*crtFrequency p s i))*F i x)).symm

end Ostmann.Construction

end

end OAI
