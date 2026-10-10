import OAI.NumberTheory.JointDickman.Amplification.OmissionEntropy

namespace OAI

/-! # Encoding regular alternatives with small additions -/

namespace JointDickman
open Finset Classical

noncomputable def regularSmallAlternatives (B L k : ℕ) (τ C : ℝ)
    (A R : Finset ℕ) : Finset (Finset ℕ) :=
  (A ∪ R).powerset.filter (fun X => RegularPrimeSet B L τ C X ∧
    X \ A ⊆ primePrefix B ((k : ℝ)/L) (X \ A))

theorem regularSmallAlternatives_omissions {B L k : ℕ} {τ C : ℝ}
    {A R X : Finset ℕ} (hL : 1 ≤ L) (hk : k ∈ Icc 1 L)
    (hA : RegularPrimeSet B L τ C A)
    (hX : X ∈ regularSmallAlternatives B L k τ C A R) :
    (((A \ X) \ primePrefix B ((k : ℝ)/L) (A ∪ R)).card : ℝ) ≤
      4*τ*auxiliaryLogLength B := by
  obtain ⟨hsub,hreg,hadd⟩ := mem_filter.mp hX
  have hsub' := mem_powerset.mp hsub
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ R)
  have hAQ : A ∩ Q = primePrefix B ((k : ℝ)/L) A := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr subset_union_left]
  have hXQ : X ∩ Q = primePrefix B ((k : ℝ)/L) X := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr hsub']
  have hcut : X \ A ⊆ Q := hadd.trans (primePrefix_mono B _ (sdiff_subset.trans hsub'))
  have he := omitted_above_count A X Q hcut
  rw [hAQ,hXQ] at he
  have ha := hA.total_upper hL
  have hx := hreg.total_lower hL
  have hap := (hA.1 k hk).1
  have hxp := (hreg.1 k hk).2
  nlinarith

/-- Prefix membership and omitted higher primes determine an alternative
uniquely. This preserves multiplicities without assuming disjoint first
coefficient and remainder sets. -/
theorem regularSmallAlternatives_count {B L k : ℕ} {τ C : ℝ}
    (A R : Finset ℕ) (hL : 1 ≤ L) (hk : k ∈ Icc 1 L)
    (hA : RegularPrimeSet B L τ C A) :
    (regularSmallAlternatives B L k τ C A R).card ≤
      2^(primePrefix B ((k : ℝ)/L) (A ∪ R)).card *
        (((A \ primePrefix B ((k : ℝ)/L) (A ∪ R)).powerset).filter
          (fun U => (U.card : ℝ) ≤ 4*τ*auxiliaryLogLength B)).card := by
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ R)
  let enc (X : Finset ℕ) := (X ∩ Q,(A \ X) \ Q)
  let target := Q.powerset.product
    ((A \ Q).powerset.filter (fun U => (U.card : ℝ) ≤ 4*τ*auxiliaryLogLength B))
  have htarget (X : Finset ℕ) (hX : X ∈ regularSmallAlternatives B L k τ C A R) :
      enc X ∈ target := by
    apply mem_product.mpr
    refine ⟨mem_powerset.mpr inter_subset_right,mem_filter.mpr ⟨?_,?_⟩⟩
    · exact mem_powerset.mpr (sdiff_subset_sdiff sdiff_subset subset_rfl)
    · exact regularSmallAlternatives_omissions hL hk hA hX
  have hcut (X : Finset ℕ) (hX : X ∈ regularSmallAlternatives B L k τ C A R) :
      X \ A ⊆ Q := by
    have h := mem_filter.mp hX
    exact h.2.2.trans (primePrefix_mono B _ (sdiff_subset.trans (mem_powerset.mp h.1)))
  have hinj : Set.InjOn enc (regularSmallAlternatives B L k τ C A R) := by
    intro X hX Y hY he
    have he₁ := congrArg Prod.fst he
    have he₂ := congrArg Prod.snd he
    change X ∩ Q = Y ∩ Q at he₁
    change (A \ X) \ Q = (A \ Y) \ Q at he₂
    ext p
    have h₁ := Finset.ext_iff.mp he₁ p
    have h₂ := Finset.ext_iff.mp he₂ p
    have hx : p ∈ X → p ∉ A → p ∈ Q := fun hp ha => hcut X hX (mem_sdiff.mpr ⟨hp,ha⟩)
    have hy : p ∈ Y → p ∉ A → p ∈ Q := fun hp ha => hcut Y hY (mem_sdiff.mpr ⟨hp,ha⟩)
    simp only [Finset.mem_inter,Finset.mem_sdiff] at h₁ h₂
    tauto
  have hc := card_le_card_of_injOn enc htarget hinj
  simpa only [target,Finset.product_eq_sprod,card_product,card_powerset,Q] using hc

end JointDickman

end OAI
