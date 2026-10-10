import Mathlib
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SourceProductSmall
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MeanC

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryCorrelations.SourceRoughCountIntegration
open Classical Finset
open SourceBoxSieve SourcePrimeBoxSieve SourceRoughSieveLocal SourceBonferroni SourceRoughFourier

noncomputable def goodBox (K a N : ℕ) : Finset (Box N) :=
  univ.filter (fun ω => ∀ p : Primes K, avoids p.val
    ((a+ω.1.val:ℕ):ZMod p.val) ((a+ω.2.1.val:ℕ):ZMod p.val) ((a+ω.2.2.val:ℕ):ZMod p.val))

lemma density_eq_card (K a N : ℕ) :
    density (fun p : Primes K => p.val) a N = (N:ℝ)⁻¹^3*(goodBox K a N).card := by
  unfold density survivalMass weight
  rw [← Finset.mul_sum]
  congr 1
  have he (ω : Box N) : survives univ (event (fun p : Primes K => p.val) a N) ω =
      if ∀ p : Primes K, avoids p.val ((a+ω.1.val:ℕ):ZMod p.val)
        ((a+ω.2.1.val:ℕ):ZMod p.val) ((a+ω.2.2.val:ℕ):ZMod p.val) then (1:ℝ) else 0 := by
    simp only [survives,event,Finset.mem_univ,forall_const,not_not]
  simp only [he]
  rw [← Finset.sum_filter]
  simp [goodBox]

lemma rough_cast {y : ℝ} {n : ℕ} (hy : 0 ≤ y) (hn : IsRough y n) (p : Primes ⌊y⌋₊) :
    (n : ZMod p.val) ≠ 0 := by
  intro hz
  apply hn p.val (Nat.prime_of_mem_primesBelow p.property)
    ((by exact_mod_cast primes_le ⌊y⌋₊ p : (p.val:ℝ) ≤ ⌊y⌋₊).trans (Nat.floor_le hy))
  exact (ZMod.natCast_eq_zero_iff n p.val).mp hz

lemma triple_data {D : ℕ} {y : ℝ} (t : ↥(roughTriples D y)) :
    (D ≤ t.val.1.1 ∧ t.val.1.1 < 2*D ∧ IsRough y t.val.1.1) ∧
    (D ≤ t.val.1.2 ∧ t.val.1.2 < 2*D ∧ IsRough y t.val.1.2) ∧
    (D ≤ t.val.2 ∧ t.val.2 < 2*D ∧ IsRough y t.val.2) ∧
    IsRough y (t.val.1.1+t.val.1.2-t.val.2) := by
  obtain ⟨ht,he⟩ := Finset.mem_filter.mp t.property
  obtain ⟨hxy,hz⟩ := Finset.mem_product.mp ht
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
  exact ⟨⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).1,
    (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).2,(Finset.mem_filter.mp hx).2⟩,
    ⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1).1,
    (Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1).2,(Finset.mem_filter.mp hy).2⟩,
    ⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp hz).1).1,
    (Finset.mem_Ico.mp (Finset.mem_filter.mp hz).1).2,(Finset.mem_filter.mp hz).2⟩,he⟩

lemma roughTriples_le_goodBox (D : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    (roughTriples D y).card ≤ (goodBox ⌊y⌋₊ D D).card := by
  let f : ↥(roughTriples D y) → ↥(goodBox ⌊y⌋₊ D D) := fun t =>
    ⟨(⟨t.val.1.1-D,by have := triple_data t; omega⟩,
      ⟨t.val.1.2-D,by have := triple_data t; omega⟩,
      ⟨t.val.2-D,by have := triple_data t; omega⟩),by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro p
      obtain ⟨hx,hy',hz,hw⟩ := triple_data t
      have hxe : D+(t.val.1.1-D) = t.val.1.1 := by omega
      have hye : D+(t.val.1.2-D) = t.val.1.2 := by omega
      have hze : D+(t.val.2-D) = t.val.2 := by omega
      dsimp only
      rw [hxe,hye,hze]
      refine ⟨rough_cast hy hx.2.2 p,rough_cast hy hy'.2.2 p,rough_cast hy hz.2.2 p,?_⟩
      have hs : t.val.2 ≤ t.val.1.1+t.val.1.2 := by omega
      have h := rough_cast hy hw p
      rwa [Nat.cast_sub hs,Nat.cast_add] at h⟩
  have hi : Function.Injective f := by
    intro t u he
    have hv := congrArg (fun b : ↥(goodBox ⌊y⌋₊ D D) =>
      (b.val.1.val,b.val.2.1.val,b.val.2.2.val)) he
    have ht := triple_data t
    have hu := triple_data u
    dsimp only [f] at hv
    have hx := congrArg Prod.fst hv
    have hy := congrArg (fun b : ℕ × ℕ × ℕ => b.2.1) hv
    have hz := congrArg (fun b : ℕ × ℕ × ℕ => b.2.2) hv
    change t.val.1.1-D = u.val.1.1-D at hx
    change t.val.1.2-D = u.val.1.2-D at hy
    change t.val.2-D = u.val.2-D at hz
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext <;> omega
    · omega
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

lemma roughTriples_le_density (D : ℕ) (hD : 0 < D) (y : ℝ) (hy : 0 ≤ y) :
    ((roughTriples D y).card:ℝ) ≤ (D:ℝ)^3 * density (fun p : Primes ⌊y⌋₊ => p.val) D D := by
  have hDz : (D:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  rw [density_eq_card]
  have he : (D:ℝ)^3 * ((D:ℝ)⁻¹^3*(goodBox ⌊y⌋₊ D D).card) = (goodBox ⌊y⌋₊ D D).card := by
    field_simp
  rw [he]
  exact_mod_cast roughTriples_le_goodBox D y hy

theorem eventual_roughTriples : ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ D : ℕ, (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) ≤ D →
      ((roughTriples D (Real.exp (L^(99/100:ℝ)))).card:ℝ) ≤
        C*(D:ℝ)^3*L^(-99/25:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventual_rough_box
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with L hL
  intro D hD
  have hDp : 0 < D := by
    have hp : 0 < (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) := by positivity
    exact_mod_cast hp.trans_le hD
  calc
    _ ≤ (D:ℝ)^3 * density (fun p : Primes ⌊Real.exp (L^(99/100:ℝ))⌋₊ => p.val) D D :=
      roughTriples_le_density D hDp _ (Real.exp_pos _).le
    _ ≤ (D:ℝ)^3 * (C*L^(-99/25:ℝ)) := mul_le_mul_of_nonneg_left (hL D D hD) (by positivity)
    _ = _ := by ring

end OrdinaryCorrelations.SourceRoughCountIntegration

end

end OAI
