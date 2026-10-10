import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCodePartition
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticHarmonic

namespace OAI

/-! Separated finite sums over the actual supported prefixes. A finite
subset of prefixes costs at most the product of its coordinate sums. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_prefix_product_bound {r : Eisenstein}
    (P : Finset (MetaplecticDyadPrefix r))
    (fd : PrimaryArgument → ℝ) (fk : ℕ → ℝ) (fhp : PrimaryArgument → ℝ)
    (hd : ∀ d, 0 ≤ fd d) (hk : ∀ k, 0 ≤ fk k) (hhp : ∀ p, 0 ≤ fhp p) :
    (∑ p ∈ P, fd p.1*fk p.2.1*fhp p.2.2.2.2) ≤
      (∑ d ∈ P.image Prod.fst, fd d)*(∑ k ∈ P.image (fun p => p.2.1), fk k)*
        (Nat.card (Eisensteinˣ):ℝ)*((metaplecticPrimaryDivisors r).card:ℝ)*
          (∑ h ∈ P.image (fun p => p.2.2.2.2), fhp h) := by
  let : Finite (Eisensteinˣ) := metaplectic_units_finite
  let : Fintype (Eisensteinˣ) := Fintype.ofFinite _
  let D := P.image Prod.fst
  let K := P.image (fun p => p.2.1)
  let H := P.image (fun p => p.2.2.2.2)
  have hsub : P ⊆ D ×ˢ (K ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ H))) := by
    intro p hp
    apply Finset.mem_product.mpr
    refine ⟨?_,Finset.mem_product.mpr ⟨?_,Finset.mem_product.mpr
      ⟨Finset.mem_univ _,Finset.mem_product.mpr ⟨Finset.mem_univ _,?_⟩⟩⟩⟩
    · exact Finset.mem_image_of_mem _ hp
    · exact Finset.mem_image_of_mem _ hp
    · exact Finset.mem_image_of_mem _ hp
  calc
    _ ≤ ∑ p ∈ D ×ˢ (K ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ H))),
        fd p.1*fk p.2.1*fhp p.2.2.2.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
        mul_nonneg (mul_nonneg (hd _) (hk _)) (hhp _))
    _ = _ := by
      simp only [Finset.sum_product]
      simp_rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      simp_rw [←Finset.mul_sum,←Finset.sum_mul]
      simp only [Fintype.card_coe,Nat.card_eq_fintype_card]
      simp_rw [←Finset.mul_sum,←Finset.sum_mul]
      dsimp only [D,K,H]
      ring

lemma primary_argument_harmonic {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset PrimaryArgument) (J : ℝ), 0 < J →
      (∀ d ∈ S, norm d ≤ J) → (∑ d ∈ S, norm d^(-1:ℝ)) ≤ C*J^ε := by
  obtain ⟨C,hC,hb⟩ := primary_finite_harmonic_power hε
  refine ⟨C,hC,?_⟩
  intro S J hJ hS
  have hs := hb (S.image Subtype.val) J hJ
    (by rintro d hd; obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hd; exact x.property)
    (by rintro d hd; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hd; exact hS x hx)
  rw [Finset.sum_image] at hs
  · exact hs
  · intro x _ y _ hxy
    exact Subtype.ext hxy

lemma primary_argument_supported_sum {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      ∀ (S : Finset PrimaryArgument) (J : ℝ),
      (∀ h ∈ S, ∃ k : ℕ, h.val ∣ r^k) → (∀ h ∈ S, norm h ≤ J) →
      (∑ h ∈ S, norm h^(-δ)) ≤ C*norm r^ε := by
  obtain ⟨C,hC,hb⟩ := primary_supported_norm_sum hε hδ
  refine ⟨C,hC,?_⟩
  intro r hr S J hs hJ
  have h := hb r hr (S.image Subtype.val) J
    (by rintro d hd; obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hd; exact x.property)
    (by rintro d hd; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hd; exact hs x hx)
    (by rintro d hd; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hd; exact hJ x hx)
  rw [Finset.sum_image] at h
  · exact h
  · intro x _ y _ hxy
    exact Subtype.ext hxy

end CubicFirstMoment

end

end OAI
