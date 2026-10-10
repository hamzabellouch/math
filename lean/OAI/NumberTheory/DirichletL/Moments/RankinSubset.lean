import OAI.NumberTheory.DirichletL.Moments.RankinCount

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinSubset
open IdealMobiusDivisorSum CenteredMomentRankinCount
local notation "O" => ActualEisensteinCubic.O

theorem supported_power_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (Q : Ideal O),Q ≠ 0 → ∀ S : Finset (Ideal O),
      (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I ⊆ primeSupport Q) →
      ∀ X : ℝ,0 < X → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ X) →
      (S.card:ℝ) ≤ C*X^a*(Ideal.absNorm Q:ℝ)^ε := by
  obtain ⟨C,hC,hcount⟩ := fixed_support_count a ha
  obtain ⟨D,hD,hsub⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Q hQ S hS hs X hX hN
  have hf : ∀ I ∈ S,primeSupport I ∈ (primeSupport Q).powerset :=
    fun I hI => Finset.mem_powerset.mpr (hs I hI)
  have he := Finset.card_eq_sum_card_fiberwise hf
  have hfiber (R : Finset (Ideal O)) (hR : R ∈ (primeSupport Q).powerset) :
      ((S.filter (fun I => primeSupport I=R)).card:ℝ) ≤ C*X^a := by
    apply hcount R _ (fun P hP => support_prime ((Finset.mem_powerset.mp hR) hP))
      (fun I hI => hS I (Finset.mem_filter.mp hI).1)
      (fun I hI => (Finset.mem_filter.mp hI).2) X hX
      (fun I hI => hN I (Finset.mem_filter.mp hI).1)
  calc
    _ = ∑ R ∈ (primeSupport Q).powerset,((S.filter (fun I => primeSupport I=R)).card:ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _R ∈ (primeSupport Q).powerset,C*X^a := Finset.sum_le_sum hfiber
    _ = (2:ℝ)^(primeSupport Q).card*(C*X^a) := by simp
    _ ≤ (D*(Ideal.absNorm Q:ℝ)^ε)*(C*X^a) :=
      mul_le_mul_of_nonneg_right (hsub Q hQ) (mul_nonneg hC.le (Real.rpow_nonneg hX.le _))
    _ = _ := by ring

theorem supported_power_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (Q : Ideal O),Q ≠ 0 → ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S,v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1 ⊆ primeSupport Q ∧ primeSupport v.2 ⊆ primeSupport Q) →
      ∀ X Y : ℝ,0 < X → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1:ℝ) ≤ X ∧ (Ideal.absNorm v.2:ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X^a*Y^a*(Ideal.absNorm Q:ℝ)^ε := by
  obtain ⟨C,hC,hcount⟩ := supported_power_count a (ε/2) ha (by positivity)
  refine ⟨C^2,pow_pos hC _,?_⟩
  intro Q hQ S hS hs X Y hX hY hN
  have hfst : ((S.image Prod.fst).card:ℝ) ≤ C*X^a*(Ideal.absNorm Q:ℝ)^(ε/2) := by
    refine hcount Q hQ _ ?_ ?_ X hX ?_
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hS v hv).1
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hs v hv).1
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hN v hv).1
  have hsnd : ((S.image Prod.snd).card:ℝ) ≤ C*Y^a*(Ideal.absNorm Q:ℝ)^(ε/2) := by
    refine hcount Q hQ _ ?_ ?_ Y hY ?_
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hS v hv).2
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hs v hv).2
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hN v hv).2
  have hin : S ⊆ (S.image Prod.fst) ×ˢ (S.image Prod.snd) := by
    intro v hv
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hv,Finset.mem_image_of_mem _ hv⟩
  have hn : (0:ℝ) < Ideal.absNorm Q := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  calc
    _ ≤ ((S.image Prod.fst).card:ℝ)*((S.image Prod.snd).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hin).trans_eq (Finset.card_product _ _)
    _ ≤ (C*X^a*(Ideal.absNorm Q:ℝ)^(ε/2))*(C*Y^a*(Ideal.absNorm Q:ℝ)^(ε/2)) :=
      mul_le_mul hfst hsnd (Nat.cast_nonneg _) (by positivity)
    _ = C^2*X^a*Y^a*((Ideal.absNorm Q:ℝ)^(ε/2)*(Ideal.absNorm Q:ℝ)^(ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

end SevenEighths.CenteredMomentRankinSubset

end

end OAI
