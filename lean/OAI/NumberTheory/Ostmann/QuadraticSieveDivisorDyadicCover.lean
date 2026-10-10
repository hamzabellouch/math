import OAI.NumberTheory.Ostmann.QuadraticSieveDivisorDyadicBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Finset

def divisorAnnulusPairs (D : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc D (2*D)).biUnion Nat.divisorsAntidiagonal

@[simp] theorem mem_divisorAnnulusPairs {D : ℕ} {e : ℕ × ℕ} :
    e∈divisorAnnulusPairs D ↔ D<e.1*e.2 ∧ e.1*e.2≤2*D := by
  simp only [divisorAnnulusPairs,mem_biUnion,mem_Ioc,Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨d,hd,he,hne⟩
    simpa only [he] using hd
  · intro he
    exact ⟨e.1*e.2,he,rfl,by omega⟩

theorem divisorAnnulusPairs_positive {D : ℕ} {e : ℕ × ℕ}
    (he : e∈divisorAnnulusPairs D) : 0<e.1 ∧ 0<e.2 := by
  have h := (mem_divisorAnnulusPairs.mp he).1
  have hn : e.1*e.2≠0 := by omega
  exact ⟨Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hn).1,
    Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hn).2⟩

theorem sum_divisorAnnulusPairs (D : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ e∈divisorAnnulusPairs D,f e)=
      ∑ d∈Ioc D (2*D),∑ e∈d.divisorsAntidiagonal,f e := by
  apply sum_biUnion
  intro d hd t ht hdt
  apply disjoint_left.mpr
  intro e hed het
  exact hdt ((Nat.mem_divisorsAntidiagonal.mp hed).1.symm.trans
    (Nat.mem_divisorsAntidiagonal.mp het).1)

theorem divisor_annulus_sum_le_dyadic (D : ℕ) (f : ℕ × ℕ → ℝ)
    (hf : ∀ e,0≤f e) :
    (∑ e∈divisorAnnulusPairs D,f e) ≤
      ∑ k∈divisorDyadicIndices D,∑ e∈dyadicDivisors k.1 ×ˢ dyadicDivisors k.2,f e := by
  have hmaps (e) (he : e∈divisorAnnulusPairs D) :
      (Nat.log 2 e.1,Nat.log 2 e.2)∈divisorDyadicIndices D := by
    obtain ⟨h1,h2⟩ := divisorAnnulusPairs_positive he
    obtain ⟨hl,hu⟩ := mem_divisorAnnulusPairs.mp he
    exact dyadic_pair_mem h1 h2 hl hu
  rw [←sum_fiberwise_of_maps_to hmaps f]
  apply sum_le_sum
  intro k hk
  apply sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨he,hk'⟩ := mem_filter.mp he
    rw [←hk']
    obtain ⟨h1,h2⟩ := divisorAnnulusPairs_positive he
    exact mem_product.mpr ⟨mem_dyadicDivisors_log h1,mem_dyadicDivisors_log h2⟩
  · intro e he hn
    exact hf e

theorem product_divisor_annulus_le_dyadic (D : ℕ) (V S T : Finset ℕ)
    (a b : ℕ → ℂ) :
    (∑ d∈Ioc D (2*D),∑ v∈V,‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖) ≤
      ∑ k∈divisorDyadicIndices D,∑ e∈dyadicDivisors k.1 ×ˢ dyadicDivisors k.2,
        ∑ v∈V,‖coprimeDivisorJacobiRow S T a b e.1 e.2 (v : ℤ)‖ := by
  let f : ℕ × ℕ → ℝ := fun e => ∑ v∈V,‖coprimeDivisorJacobiRow S T a b e.1 e.2 (v : ℤ)‖
  have hf (e) : 0≤f e := sum_nonneg (fun v hv => norm_nonneg _)
  apply le_trans _ (divisor_annulus_sum_le_dyadic D f hf)
  rw [sum_divisorAnnulusPairs]
  apply sum_le_sum
  intro d hd
  have hd0 : d≠0 := by have := (mem_Ioc.mp hd).1; omega
  simp_rw [coprimeProductDivisorJacobiRow_eq S T a b d hd0]
  rw [show (∑ e∈d.divisorsAntidiagonal,f e)=
      ∑ v∈V,∑ e∈d.divisorsAntidiagonal,‖coprimeDivisorJacobiRow S T a b e.1 e.2 (v : ℤ)‖ by
    exact sum_comm]
  exact sum_le_sum (fun v hv => norm_sum_le _ _)

theorem exists_divisor_dyadic_rectangle {D : ℕ} (hD : 0<D) (V S T : Finset ℕ)
    (a b : ℕ → ℂ) :
    ∃ k∈divisorDyadicIndices D,
      (∑ d∈Ioc D (2*D),∑ v∈V,‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖) ≤
        ((divisorDyadicDepth D : ℕ) : ℝ)^2 *
          ∑ e∈dyadicDivisors k.1 ×ˢ dyadicDivisors k.2,
            ∑ v∈V,‖coprimeDivisorJacobiRow S T a b e.1 e.2 (v : ℤ)‖ := by
  let B : ℕ × ℕ → ℝ := fun k => ∑ e∈dyadicDivisors k.1 ×ˢ dyadicDivisors k.2,
    ∑ v∈V,‖coprimeDivisorJacobiRow S T a b e.1 e.2 (v : ℤ)‖
  have hB (k) : 0≤B k := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => norm_nonneg _))
  obtain ⟨k,hk,hmax⟩ := exists_max_image (divisorDyadicIndices D) B
    (divisorDyadicIndices_nonempty hD)
  refine ⟨k,hk,(product_divisor_annulus_le_dyadic D V S T a b).trans ?_⟩
  calc
    (∑ j∈divisorDyadicIndices D,B j) ≤ (divisorDyadicIndices D).card * B k := by
      simpa only [nsmul_eq_mul] using sum_le_card_nsmul (divisorDyadicIndices D) B (B k) hmax
    _ ≤ ((divisorDyadicDepth D : ℕ) : ℝ)^2 * B k := by
      apply mul_le_mul_of_nonneg_right _ (hB k)
      exact_mod_cast divisorDyadicIndices_card_le D

end Ostmann.QuadraticSieve

end

end OAI
