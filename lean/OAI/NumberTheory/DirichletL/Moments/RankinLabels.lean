import OAI.NumberTheory.DirichletL.Moments.RankinRadical
import OAI.NumberTheory.DirichletL.Moments.RankinSubset

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinLabels
open IdealMobiusDivisorSum CenteredMomentRankinRadical CenteredMomentRankinSubset
local notation "O" => ActualEisensteinCubic.O

theorem common_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Ideal O),Squarefree s → s ≠ 0 →
      ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S,v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1=primeSupport v.2) →
      (∀ v ∈ S,s ∣ v.1 ∧ s ∣ v.2) →
      ∀ X₁ X₂ Y : ℝ,0 < X₁ → 0 < X₂ → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1:ℝ) ≤ X₁ ∧ (Ideal.absNorm v.2:ℝ) ≤ X₂) →
      (∀ v ∈ S,(Ideal.absNorm (commonRadical v.1 v.2):ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X₁^a*X₂^a*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := supported_power_pair_count a ε ha hε
  refine ⟨128*C,by positivity,?_⟩
  intro s hs hs0 S hS heq hdiv X₁ X₂ Y hX₁ hX₂ hY hN hR
  let rad : Ideal O × Ideal O → Ideal O := fun v => commonRadical v.1 v.2
  have hfiber (R : Ideal O) (hRmem : R ∈ S.image rad) :
      ((S.filter (fun v => rad v=R)).card:ℝ) ≤ C*X₁^a*X₂^a*Y^ε := by
    obtain ⟨v,hv,hvR⟩ := Finset.mem_image.mp hRmem
    have hR0 : R ≠ 0 := hvR ▸ commonRadical_ne_zero v.1 v.2
    have hRN : (Ideal.absNorm R:ℝ) ≤ Y := hvR ▸ hR v hv
    have hb := hcount R hR0 (S.filter (fun v => rad v=R))
      (fun v hv => hS v (Finset.mem_filter.mp hv).1)
      (by
        intro w hw
        obtain ⟨hw,hwr⟩ := Finset.mem_filter.mp hw
        have he : primeSupport R=primeSupport w.1 := by
          rw [← hwr,commonRadical_support,← heq w hw,Finset.inter_self]
        rw [he,heq w hw]
        exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩)
      X₁ X₂ hX₁ hX₂ (fun w hw => hN w (Finset.mem_filter.mp hw).1)
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hRN hε.le) (by positivity))
  have hrad := old_mask_radical_count S Prod.fst Prod.snd s hs hs0
    (fun v hv => (hS v hv).1) (fun v hv => (hS v hv).2)
    (fun v hv => (hdiv v hv).1) (fun v hv => (hdiv v hv).2) Y hY.le hR
  have he := Finset.card_eq_sum_card_fiberwise
    (fun v (hv : v ∈ S) => Finset.mem_image_of_mem rad hv)
  calc
    _ = ∑ R ∈ S.image rad,((S.filter (fun v => rad v=R)).card:ℝ) := by exact_mod_cast he
    _ ≤ ∑ _R ∈ S.image rad,C*X₁^a*X₂^a*Y^ε := Finset.sum_le_sum hfiber
    _ = ((S.image rad).card:ℝ)*(C*X₁^a*X₂^a*Y^ε) := by simp
    _ ≤ (128*Y/(Ideal.absNorm s:ℝ))*(C*X₁^a*X₂^a*Y^ε) :=
      mul_le_mul_of_nonneg_right hrad (by positivity)
    _ = _ := by rw [Real.rpow_add hY,Real.rpow_one]; ring

theorem partitioned_common_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Ideal O),Squarefree s → s ≠ 0 →
      ∀ S : Finset ((Ideal O × Ideal O) × Finset (Ideal O)),
      (∀ v ∈ S,v.1.1 ≠ 0 ∧ v.1.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1.1=primeSupport v.1.2) →
      (∀ v ∈ S,s ∣ v.1.1 ∧ s ∣ v.1.2) →
      (∀ v ∈ S,v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)) →
      ∀ X₁ X₂ Y : ℝ,0 < X₁ → 0 < X₂ → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1.1:ℝ) ≤ X₁ ∧ (Ideal.absNorm v.1.2:ℝ) ≤ X₂) →
      (∀ v ∈ S,(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X₁^a*X₂^a*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := common_pair_count a (ε/2) ha (by positivity)
  obtain ⟨D,hD,hpow⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro s hs hs0 S hS heq hdiv hpart X₁ X₂ Y hX₁ hX₂ hY hN hR
  have hpairs := hcount s hs hs0 (S.image Prod.fst)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hS w hw)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact heq w hw)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hdiv w hw)
    X₁ X₂ Y hX₁ hX₂ hY
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hN w hw)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hR w hw)
  have hfiber (v : Ideal O × Ideal O) (hv : v ∈ S.image Prod.fst) :
      ((S.filter (fun w => w.1=v)).card:ℝ) ≤ D*Y^(ε/2) := by
    have hin : (S.filter (fun w => w.1=v)).image Prod.snd ⊆
        (primeSupport (commonRadical v.1 v.2)).powerset := by
      intro A hA
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨hw,hwe⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_powerset.mpr (hwe ▸ hpart w hw)
    have hinj : Set.InjOn (fun w : (Ideal O × Ideal O) × Finset (Ideal O) => w.2)
        (↑(S.filter (fun w => w.1=v)) : Set ((Ideal O × Ideal O) × Finset (Ideal O))) := by
      intro w hw z hz he
      exact Prod.ext ((Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hz).2.symm) he
    have hc : ((S.filter (fun w => w.1=v)).card:ℝ) ≤
        (2:ℝ)^(primeSupport (commonRadical v.1 v.2)).card := by
      have hb := Finset.card_le_card hin
      rw [Finset.card_image_of_injOn hinj,Finset.card_powerset] at hb
      exact_mod_cast hb
    obtain ⟨w,hw,hwe⟩ := Finset.mem_image.mp hv
    have hb := hpow (commonRadical v.1 v.2) (commonRadical_ne_zero _ _)
    have hn : (Ideal.absNorm (commonRadical v.1 v.2):ℝ) ≤ Y := hwe ▸ hR w hw
    exact hc.trans (hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hn (by positivity)) hD.le))
  have he := Finset.card_eq_sum_card_fiberwise
    (fun v (hv : v ∈ S) => Finset.mem_image_of_mem Prod.fst hv)
  calc
    _ = ∑ v ∈ S.image Prod.fst,((S.filter (fun w => w.1=v)).card:ℝ) := by exact_mod_cast he
    _ ≤ ∑ _v ∈ S.image Prod.fst,D*Y^(ε/2) := Finset.sum_le_sum hfiber
    _ = ((S.image Prod.fst).card:ℝ)*(D*Y^(ε/2)) := by simp
    _ ≤ (C*X₁^a*X₂^a*Y^(1+ε/2)/(Ideal.absNorm s:ℝ))*(D*Y^(ε/2)) :=
      mul_le_mul_of_nonneg_right hpairs (by positivity)
    _ = (C*D)*X₁^a*X₂^a*(Y^(1+ε/2)*Y^(ε/2))/(Ideal.absNorm s:ℝ) := by ring
    _ = _ := by rw [← Real.rpow_add hY]; congr 3; ring

end SevenEighths.CenteredMomentRankinLabels

end

end OAI
