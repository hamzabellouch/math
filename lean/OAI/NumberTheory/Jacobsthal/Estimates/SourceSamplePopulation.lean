import OAI.NumberTheory.Jacobsthal.Estimates.SmallModelSourceScales
import OAI.NumberTheory.Jacobsthal.Probability.FallingFactorialProbability

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseSampling
attribute [local instance] Classical.decEq

noncomputable def sampleAverage {α : Type*} (U : Finset α) (h : ℕ) (f : Sample U h → ℝ) : ℝ :=
  (∑ e : Sample U h,f e)/(Fintype.card (Sample U h) : ℝ)

theorem sample_product_sum_le {α : Type*} (U : Finset α) (h : ℕ) (t : U → ℝ)
    (ht : ∀ u,0 ≤ t u) :
    (∑ e : Sample U h,∏ i : Fin h,t (e i)) ≤ (∑ u : U,t u)^h := by
  classical
  let E : Finset (Fin h → U) := Finset.univ.image (fun e : Sample U h => (e : Fin h → U))
  have he : (∑ e : Sample U h,∏ i : Fin h,t (e i)) = ∑ f ∈ E,∏ i : Fin h,t (f i) := by
    dsimp only [E]
    rw [Finset.sum_image (fun _ _ _ _ he => Function.Embedding.coe_injective he)]
  have hall : (∑ f : Fin h → U,∏ i : Fin h,t (f i)) = (∑ u : U,t u)^h := by
    have hh := (Fintype.prod_sum (fun _i : Fin h => fun u : U => t u)).symm
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
  calc
    _ = ∑ f ∈ E,∏ i : Fin h,t (f i) := he
    _ ≤ ∑ f : Fin h → U,∏ i : Fin h,t (f i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        (fun f _ _ => Finset.prod_nonneg (fun i _ => ht (f i)))
    _ = _ := hall

theorem sample_product_average_le {α : Type*} (U : Finset α) (h : ℕ) (t : U → ℝ)
    (ht : ∀ u,0 ≤ t u) (hU : 0 < U.card) (hh : h ≤ U.card) :
    sampleAverage U h (fun e => ∏ i : Fin h,t (e i)) ≤
      ((U.card : ℝ)^h/(U.card.descFactorial h : ℝ))*((∑ u : U,t u)/(U.card : ℝ))^h := by
  have hn : (0 : ℝ) < U.card := by exact_mod_cast hU
  have hd : (0 : ℝ) < U.card.descFactorial h := by exact_mod_cast Nat.descFactorial_pos.mpr hh
  unfold sampleAverage
  rw [sample_card]
  calc
    _ ≤ (∑ u : U,t u)^h/(U.card.descFactorial h : ℝ) :=
      div_le_div_of_nonneg_right (sample_product_sum_le U h t ht) hd.le
    _ = _ := by rw [div_pow];field_simp

end ErdosInverseSampling

end

section

open _root_.Filter _root_.Erdos970.Filter
open scoped Topology
namespace ErdosInverseSampling

theorem normalized_falling_eq_product (n h : ℕ) (hh : h ≤ n) (hn : 0 < n) :
    (n.descFactorial h : ℝ)/(n : ℝ)^h = ∏ i ∈ Finset.range h,(1-(i : ℝ)/(n : ℝ)) := by
  rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]
  have hden : (n : ℝ)^h = ∏ _i ∈ Finset.range h,(n : ℝ) := by simp
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hden,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hin : i ≤ n := (Finset.mem_range.mp hi).le.trans hh
  rw [Nat.cast_sub hin]
  field_simp

theorem normalized_falling_tendsto (h : ℕ) :
    Tendsto (fun n : ℕ => (n.descFactorial h : ℝ)/(n : ℝ)^h) atTop (𝓝 1) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hprod : Tendsto (fun n : ℕ => ∏ i ∈ Finset.range h,(1-(i : ℝ)/(n : ℝ))) atTop (𝓝 1) := by
    have hh := tendsto_finsetProd (Finset.range h) (fun i _ =>
      (tendsto_const_nhds : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        (hcast.const_div_atTop (i : ℝ)))
    simpa only [sub_zero,Finset.prod_const_one] using hh
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop h,eventually_ge_atTop (1 : ℕ)] with n hhn hn
  exact (normalized_falling_eq_product n h hhn (by omega)).symm

theorem sampling_prefactor_tendsto (h : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^h/(n.descFactorial h : ℝ)) atTop (𝓝 1) := by
  have hh := (normalized_falling_tendsto h).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_div,inv_one] using hh

theorem sampling_prefactor_eventually_le_two (h : ℕ) :
    ∀ᶠ n : ℕ in atTop,(n : ℝ)^h/(n.descFactorial h : ℝ) ≤ 2 := by
  have hh := (tendsto_order.mp (sampling_prefactor_tendsto h)).2 2 (by norm_num)
  exact hh.mono (fun _ hn => hn.le)

end ErdosInverseSampling

end

section

namespace ErdosInverseSampleCost
open ErdosInverseSampling
attribute [local instance] Classical.decEq

theorem sampleAverage_mono {α : Type*} (U : Finset α) (h : ℕ)
    (f g : Sample U h → ℝ) (hfg : ∀ s,f s ≤ g s) : sampleAverage U h f ≤ sampleAverage U h g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun s _ => hfg s)) (Nat.cast_nonneg _)

theorem sampleAverage_nonneg {α : Type*} (U : Finset α) (h : ℕ)
    (f : Sample U h → ℝ) (hf : ∀ s,0 ≤ f s) : 0 ≤ sampleAverage U h f :=
  div_nonneg (Finset.sum_nonneg (fun s _ => hf s)) (Nat.cast_nonneg _)

theorem sampleAverage_add {α : Type*} (U : Finset α) (h : ℕ) (f g : Sample U h → ℝ) :
    sampleAverage U h (fun s => f s+g s) = sampleAverage U h f+sampleAverage U h g := by
  unfold sampleAverage
  rw [Finset.sum_add_distrib,add_div]

theorem sampleAverage_mul {α : Type*} (U : Finset α) (h : ℕ) (c : ℝ) (f : Sample U h → ℝ) :
    sampleAverage U h (fun s => c*f s) = c*sampleAverage U h f := by
  unfold sampleAverage
  rw [← Finset.mul_sum,mul_div_assoc]

theorem sampleAverage_div {α : Type*} (U : Finset α) (h : ℕ) (c : ℝ) (f : Sample U h → ℝ) :
    sampleAverage U h (fun s => f s/c) = sampleAverage U h f/c := by
  unfold sampleAverage
  rw [← Finset.sum_div,div_right_comm]

theorem sampleAverage_sum {α ι : Type*} (U : Finset α) (h : ℕ) (I : Finset ι)
    (f : ι → Sample U h → ℝ) :
    sampleAverage U h (fun s => ∑ i ∈ I,f i s) = ∑ i ∈ I,sampleAverage U h (f i) := by
  unfold sampleAverage
  rw [Finset.sum_comm,Finset.sum_div]

theorem sampleAverage_const {α : Type*} (U : Finset α) (h : ℕ) (hh : h ≤ U.card) (c : ℝ) :
    sampleAverage U h (fun _ => c) = c := by
  have hcard : (0 : ℝ) < Fintype.card (Sample U h) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (sample_nonempty_of_length U h hh)
  unfold sampleAverage
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

theorem sampleAverage_product_bound {α : Type*} (U : Finset α) (h : ℕ) (hh : h ≤ U.card)
    (t : U → ℝ) (T : ℝ) (ht : ∀ u,0 ≤ t u) (hT : ∀ u,t u ≤ T) :
    sampleAverage U h (fun s => ∏ i : Fin h,t (s i)) ≤ T^h := by
  have hprod : ∀ s : Sample U h,(∏ i : Fin h,t (s i)) ≤ T^h := by
    intro s
    have hh := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => ht (s i)) (fun i _ => hT (s i))
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
  exact (sampleAverage_mono U h _ _ hprod).trans_eq (sampleAverage_const U h hh (T^h))

end ErdosInverseSampleCost

end

section

open _root_.Filter _root_.Erdos970.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open ErdosInverseSampling ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

theorem source_sample_population (xi beta : ℝ) (h : ℕ) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,∀ U theta : ℝ,sourceW z ≤ U → xi/4 ≤ theta → theta ≤ xi →
      0 < (primeBin U theta).card ∧ h ≤ (primeBin U theta).card ∧
      4*(h : ℝ)/beta ≤ ((primeBin U theta).card : ℝ) ∧
      ((primeBin U theta).card : ℝ)^h/((primeBin U theta).card.descFactorial h : ℝ) ≤ 2 := by
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp (sampling_prefactor_eventually_le_two h)
  let M : ℕ := n0+h+⌈4*(h : ℝ)/beta⌉₊+1
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp (uniform_prime_bin_many (by positivity : 0 < xi/4) M)
  filter_upwards [sourceW_tendsto_atTop.eventually_ge_atTop U0] with z hz
  intro U theta hWU htlow hthigh
  have hmany := (hU0 U (hz.trans hWU)).2 theta htlow (hthigh.trans hxi1)
  have hM0 : n0 ≤ M := by dsimp [M];omega
  have hMh : h ≤ M := by dsimp [M];omega
  have hM1 : 1 ≤ M := by dsimp [M];omega
  have hMc : ⌈4*(h : ℝ)/beta⌉₊ ≤ M := by dsimp [M];omega
  refine ⟨by omega,hMh.trans hmany,?_,hn0 _ (hM0.trans hmany)⟩
  exact (Nat.le_ceil (4*(h : ℝ)/beta)).trans (by exact_mod_cast hMc.trans hmany)

end ErdosInverseSampleCost

end

end Erdos970

end OAI
