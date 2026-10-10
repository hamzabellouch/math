import OAI.NumberTheory.JointDickman.Amplification.RegularAlternatives
import OAI.NumberTheory.JointDickman.Amplification.TiltedAdditionRate

namespace OAI

/-! # The prefix omission count lies in the addition's entropy window -/

namespace JointDickman
open Finset Classical

theorem omitted_prefix_count (A X Q : Finset ℕ) (hadd : X \ A ⊆ Q) :
    (((A \ X) ∩ Q).card : ℝ)-(X \ A).card = (A ∩ Q).card-(X ∩ Q).card := by
  have he₁ : (A ∩ Q) \ (X ∩ Q) = (A \ X) ∩ Q := by
    ext p
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  have he₂ : (X ∩ Q) \ (A ∩ Q) = X \ A := by
    ext p
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    constructor
    · tauto
    · intro h
      exact ⟨⟨h.1,hadd (mem_sdiff.mpr h)⟩,by tauto⟩
  have h₁ := card_sdiff_add_card_inter (A ∩ Q) (X ∩ Q)
  have h₂ := card_sdiff_add_card_inter (X ∩ Q) (A ∩ Q)
  rw [he₁] at h₁
  rw [he₂,inter_comm (X ∩ Q)] at h₂
  have hc₁ : (((A \ X) ∩ Q).card : ℝ)+((A ∩ Q) ∩ (X ∩ Q)).card = (A ∩ Q).card := by exact_mod_cast h₁
  have hc₂ : ((X \ A).card : ℝ)+((A ∩ Q) ∩ (X ∩ Q)).card = (X ∩ Q).card := by exact_mod_cast h₂
  linarith

theorem regular_omission_prefix_window {B L k : ℕ} {τ C : ℝ} {A U X : Finset ℕ}
    (hk : k ∈ Icc 1 L) (hA : RegularPrimeSet B L τ C A)
    (hX : X ∈ regularSmallAlternatives B L k τ C A U) :
    |(((A \ X) ∩ primePrefix B ((k : ℝ)/L) (A ∪ U)).card : ℝ)-
      (X \ A).card| ≤ 2*τ*auxiliaryLogLength B := by
  obtain ⟨hsub,hreg,hadd⟩ := mem_filter.mp hX
  have hsub' := mem_powerset.mp hsub
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ U)
  have hAQ : A ∩ Q = primePrefix B ((k : ℝ)/L) A := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr subset_union_left]
  have hXQ : X ∩ Q = primePrefix B ((k : ℝ)/L) X := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr hsub']
  have hcut : X \ A ⊆ Q := hadd.trans (primePrefix_mono B _ (sdiff_subset.trans hsub'))
  have he := omitted_prefix_count A X Q hcut
  rw [hAQ,hXQ] at he
  have ha := hA.1 k hk
  have hx := hreg.1 k hk
  apply abs_le.mpr
  constructor <;> linarith [ha.1,ha.2,hx.1,hx.2]

theorem regular_omission_clipped_window {B L k : ℕ} {τ C : ℝ} {A U X : Finset ℕ}
    (hk : k ∈ Icc 1 L) (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : RegularPrimeSet B L τ C A) (hU : RegularPrimeSet B L τ C U)
    (hX : X ∈ regularSmallAlternatives B L k τ C A U) :
    |(((A \ X) ∩ primePrefix B ((k : ℝ)/L) (A ∪ U)).card : ℝ)/auxiliaryLogLength B-
      ((k : ℝ)/L)*clippedAdditionDensity B ((k : ℝ)/L) (X \ A)| ≤ 3*τ := by
  let g : ℝ := (k : ℝ)/L
  let Z := X \ A
  let q : ℝ := (((A \ X) ∩ primePrefix B g (A ∪ U)).card : ℝ)
  have hkpos : 0 < k := by have := (mem_Icc.mp hk).1; omega
  have hLpos : 0 < L := by have := (mem_Icc.mp hk).2; omega
  have hg : 0 < g := div_pos (by exact_mod_cast hkpos) (by exact_mod_cast hLpos)
  have hpre := regular_omission_prefix_window hk hA hX
  have h₁ : |q/auxiliaryLogLength B-(Z.card : ℝ)/auxiliaryLogLength B| ≤ 2*τ := by
    rw [← sub_div,abs_div,abs_of_pos hℓ]
    exact (div_le_iff₀ hℓ).mpr (by simpa [q,Z,g] using hpre)
  have hZU : Z ⊆ U := by
    intro p hp
    have hx := (mem_powerset.mp (mem_filter.mp hX).1) (mem_sdiff.mp hp).1
    exact (mem_union.mp hx).resolve_left (mem_sdiff.mp hp).2
  have hZpre := (mem_filter.mp hX).2.2
  have hZprefix : Z ⊆ primePrefix B g U := hZpre.trans (primePrefix_mono B g hZU)
  have hcount : (Z.card : ℝ) ≤ (g/2+τ)*auxiliaryLogLength B := by
    exact (show (Z.card : ℝ) ≤ (primePrefix B g U).card by exact_mod_cast card_le_card hZprefix).trans
      (hU.1 k hk).2
  have hcount' : (Z.card : ℝ)/auxiliaryLogLength B ≤ g/2+τ := (div_le_iff₀ hℓ).mpr hcount
  have h₂ : |(Z.card : ℝ)/auxiliaryLogLength B-g*clippedAdditionDensity B g Z| ≤ τ := by
    unfold clippedAdditionDensity
    by_cases hs : (Z.card : ℝ)/(g*auxiliaryLogLength B) ≤ 1/2
    · rw [min_eq_left hs]
      have he : g*((Z.card : ℝ)/(g*auxiliaryLogLength B)) = (Z.card : ℝ)/auxiliaryLogLength B := by
        field_simp
      rw [he,sub_self,abs_zero]
      exact hτ
    · rw [min_eq_right (le_of_not_ge hs)]
      have hlo : g/2 ≤ (Z.card : ℝ)/auxiliaryLogLength B := by
        have hh := (le_div_iff₀ (mul_pos hg hℓ)).mp (le_of_not_ge hs)
        exact (le_div_iff₀ hℓ).mpr (by nlinarith)
      apply abs_le.mpr
      constructor <;> linarith
  have htri := abs_sub_le (q/auxiliaryLogLength B) ((Z.card : ℝ)/auxiliaryLogLength B)
    (g*clippedAdditionDensity B g Z)
  exact htri.trans (by linarith)

end JointDickman

end OAI
