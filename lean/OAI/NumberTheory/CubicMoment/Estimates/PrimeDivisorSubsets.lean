import OAI.NumberTheory.CubicMoment.Estimates.GramStructuredRows

namespace OAI

/-! A product of n primary primes has at most 2^n subsets of prescribed
primary primes dividing it, independently of the ambient prime set. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primeProduct_divisor_subsets_card (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport S) :
    (U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ b)).card ≤ 2^(Fintype.card ι) := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  have hprime (i : ι) : primaryPrime (f i) := hS i (f i) (Fintype.mem_piFinset.mp hf i)
  have hsub : U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ ∏ i, f i) ⊆
      (Finset.univ.image f).powerset := by
    intro s hs
    obtain ⟨hsU,hsd⟩ := Finset.mem_filter.mp hs
    apply Finset.mem_powerset.mpr
    intro p hp
    have hpU := hU p (Finset.mem_powerset.mp hsU hp)
    have hpd : p ∣ ∏ i, f i := (Finset.dvd_prod_of_mem (fun q : Eisenstein => q) hp).trans hsd
    obtain ⟨i,_,hi⟩ := (hpU.2.dvd_finsetProd_iff f).mp hpd
    have he : p = f i := primary_associated_eq hpU.1 (hprime i).1
      ((hpU.2.dvd_prime_iff_associated (hprime i).2).mp hi)
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩
  calc
    _ ≤ ((Finset.univ.image f).powerset).card := Finset.card_le_card hsub
    _ = 2^(Finset.univ.image f).card := Finset.card_powerset _
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      simpa using Finset.card_image_le (s := (Finset.univ:Finset ι)) (f := f))

theorem fullPrime_divisor_subsets_card (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (U : Finset Eisenstein) (hU : ∀ p ∈ U, primaryPrime p)
    {b : Eisenstein} (hb : b ∈ fullSquarefreePrimeSupport R W X e) :
    (U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ b)).card ≤ 2^(Fintype.card ι) :=
  primeProduct_divisor_subsets_card (fullPrimeSupport R W X)
    (fullPrimeSupport_prime R W X) U hU (Finset.mem_filter.mp hb).1

end CubicFirstMoment

end

end OAI
