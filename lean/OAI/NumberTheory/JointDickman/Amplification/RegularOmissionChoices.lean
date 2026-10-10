import OAI.NumberTheory.JointDickman.Counting.PrefixOmissionWindow
import OAI.NumberTheory.JointDickman.Counting.SubsetWindowEntropy
import OAI.NumberTheory.JointDickman.Amplification.SmallAdditionCount

namespace OAI

/-! # Entropy count of retained coefficient factors -/

namespace JointDickman
open Finset Classical

noncomputable def regularOmissionChoices (B L k : ℕ) (τ C : ℝ)
    (A U : Finset ℕ) (d : ℕ) : Finset (Finset ℕ) :=
  ((regularSmallAlternatives B L k τ C A U).filter (fun X => (X \ A).card = d)).image
    (fun X => A \ X)

/-- Encoding the omitted primes by their portions below and above the
prefix keeps the exact addition cardinality in the entropy window. -/
theorem regularOmissionChoices_count {B L k : ℕ} {τ C : ℝ}
    (A U : Finset ℕ) (d : ℕ) (hL : 1 ≤ L) (hk : k ∈ Icc 1 L)
    (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : RegularPrimeSet B L τ C A) (hU : RegularPrimeSet B L τ C U) :
    (regularOmissionChoices B L k τ C A U d).card ≤
      (subsetCardWindow (A ∩ primePrefix B ((k : ℝ)/L) (A ∪ U))
        (auxiliaryLogLength B) ((k : ℝ)/L)
        (min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2)) τ).card *
      (((A \ primePrefix B ((k : ℝ)/L) (A ∪ U)).powerset).filter
        (fun R => (R.card : ℝ) ≤ 4*τ*auxiliaryLogLength B)).card := by
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ U)
  let r : ℝ := min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2)
  let target := (subsetCardWindow (A ∩ Q) (auxiliaryLogLength B) ((k : ℝ)/L) r τ).product
    (((A \ Q).powerset).filter (fun R => (R.card : ℝ) ≤ 4*τ*auxiliaryLogLength B))
  let enc := fun O : Finset ℕ => (O ∩ Q,O \ Q)
  have hmap (O : Finset ℕ) (hO : O ∈ regularOmissionChoices B L k τ C A U d) : enc O ∈ target := by
    obtain ⟨X,hX,rfl⟩ := mem_image.mp hO
    have hx := mem_filter.mp hX
    apply mem_product.mpr
    constructor
    · apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (inter_subset_inter sdiff_subset subset_rfl),?_⟩
      have hh := regular_omission_clipped_window hk hτ hℓ hA hU hx.1
      simpa only [clippedAdditionDensity,hx.2] using hh
    · apply mem_filter.mpr
      exact ⟨mem_powerset.mpr (sdiff_subset_sdiff sdiff_subset subset_rfl),
        regularSmallAlternatives_omissions hL hk hA hx.1⟩
  have hinj : Set.InjOn enc (regularOmissionChoices B L k τ C A U d) := by
    intro O _ R _ he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    change O ∩ Q = R ∩ Q at h₁
    change O \ Q = R \ Q at h₂
    ext p
    have he₁ := Finset.ext_iff.mp h₁ p
    have he₂ := Finset.ext_iff.mp h₂ p
    simp only [Finset.mem_inter,Finset.mem_sdiff] at he₁ he₂
    tauto
  have hc := card_le_card_of_injOn enc hmap hinj
  simpa only [target,Finset.product_eq_sprod,card_product,Q,r] using hc

end JointDickman

end OAI
