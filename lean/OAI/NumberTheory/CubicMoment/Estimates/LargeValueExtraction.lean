import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorGram
import Mathlib.Combinatorics.Pigeonhole

namespace OAI

/-! Finite logarithmic pigeonholing and compact extraction of large rows. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Unit-width logarithmic bins have an absolute multiplicative width. -/
lemma logarithmic_bucket {τ x : ℝ} (hτ : 0 < τ) (hx : τ ≤ x) :
    τ*Real.exp (⌊Real.log (x/τ)⌋₊:ℝ) ≤ x ∧
      x ≤ Real.exp 1*(τ*Real.exp (⌊Real.log (x/τ)⌋₊:ℝ)) := by
  have hxp : 0 < x := hτ.trans_le hx
  have hquot : 1 ≤ x/τ := (le_div_iff₀ hτ).mpr (by simpa using hx)
  have hlog : 0 ≤ Real.log (x/τ) := Real.log_nonneg hquot
  have hlo := Real.exp_le_exp.mpr (Nat.floor_le hlog)
  have hhi := Real.exp_le_exp.mpr (Nat.lt_floor_add_one (Real.log (x/τ))).le
  rw [Real.exp_log (div_pos hxp hτ)] at hlo hhi
  rw [Real.exp_add] at hhi
  constructor
  · exact (mul_le_mul_of_nonneg_left hlo hτ.le).trans_eq (mul_div_cancel₀ x hτ.ne')
  · have h := mul_le_mul_of_nonneg_left hhi hτ.le
    rw [mul_div_cancel₀ x hτ.ne'] at h
    nlinarith [Real.exp_pos (⌊Real.log (x/τ)⌋₊:ℝ)]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- An actual finite moment has a nonempty logarithmic box carrying at
least its average energy. The loss is the explicit number of boxes. -/
theorem finite_logarithmic_large_values (S : Finset κ) (f : ι → κ → ℝ)
    {τ U : ℝ} (hτ : 0 < τ)
    (hlo : ∀ x ∈ S, ∀ i, τ ≤ f i x) (hhi : ∀ x ∈ S, ∀ i, f i x ≤ U)
    (hm : 0 < ∑ x ∈ S, (∏ i, f i x)^2) :
    ∃ (P : Finset κ) (B : ι → ℝ), P.Nonempty ∧ P ⊆ S ∧
      (∀ i, τ ≤ B i ∧ B i ≤ U) ∧
      (∀ x ∈ P, ∀ i, B i ≤ f i x ∧ f i x ≤ Real.exp 1*B i) ∧
      (∑ x ∈ S, (∏ i, f i x)^2) ≤
        ((⌊Real.log (U/τ)⌋₊+1:ℕ)^Fintype.card ι:ℝ)*
          (Real.exp 1)^(2*Fintype.card ι)*(P.card:ℝ)*(∏ i, B i)^2 := by
  let K : ℕ := ⌊Real.log (U/τ)⌋₊+1
  let T : Finset (ι → ℕ) := Fintype.piFinset (fun _ => Finset.range K)
  let label : κ → ι → ℕ := fun x i => ⌊Real.log (f i x/τ)⌋₊
  have hTne : T.Nonempty := by
    refine ⟨fun _ => 0,Fintype.mem_piFinset.mpr (fun _ => ?_)⟩
    exact Finset.mem_range.mpr (Nat.zero_lt_succ _)
  have hlabel : ∀ x ∈ S, label x ∈ T := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    apply Real.log_le_log (div_pos (hτ.trans_le (hlo x hx i)) hτ)
    exact div_le_div_of_nonneg_right (hhi x hx i) hτ.le
  have hcard : 0 < (T.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hTne)
  obtain ⟨k,hk,hweight⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    hlabel hTne (show T.card • ((∑ x ∈ S, (∏ i, f i x)^2)/(T.card:ℝ)) ≤
      ∑ x ∈ S, (∏ i, f i x)^2 by
      rw [nsmul_eq_mul,mul_div_cancel₀ _ hcard.ne'])
  let P := S.filter (fun x => label x = k)
  let B : ι → ℝ := fun i => τ*Real.exp (k i:ℝ)
  have hPne : P.Nonempty := by
    by_contra hn
    have he : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change (∑ x ∈ S, (∏ i, f i x)^2)/(T.card:ℝ) ≤ ∑ x ∈ P, (∏ i, f i x)^2 at hweight
    rw [he,Finset.sum_empty] at hweight
    exact (not_lt_of_ge hweight) (div_pos hm hcard)
  have hPsub : P ⊆ S := Finset.filter_subset _ _
  have hrows : ∀ x ∈ P, ∀ i, B i ≤ f i x ∧ f i x ≤ Real.exp 1*B i := by
    intro x hx i
    obtain ⟨hxS,hxk⟩ := Finset.mem_filter.mp hx
    have he : label x i = k i := congrFun hxk i
    have h := logarithmic_bucket hτ (hlo x hxS i)
    simpa only [B,← he,label] using h
  have hB : ∀ i, τ ≤ B i ∧ B i ≤ U := by
    obtain ⟨x,hx⟩ := hPne
    intro i
    refine ⟨?_,(hrows x hx i).1.trans (hhi x (hPsub hx) i)⟩
    change τ ≤ τ*Real.exp (k i:ℝ)
    have he := Real.one_le_exp_iff.mpr (Nat.cast_nonneg (k i))
    nlinarith
  have hbound : ∑ x ∈ P, (∏ i, f i x)^2 ≤
      (P.card:ℝ)*(Real.exp 1)^(2*Fintype.card ι)*(∏ i, B i)^2 := by
    calc
      _ ≤ ∑ _x ∈ P, ((Real.exp 1)^(Fintype.card ι)*(∏ i, B i))^2 := by
        apply Finset.sum_le_sum
        intro x hx
        apply pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => (hτ.trans_le (hlo x (hPsub hx) i)).le))
        have h := Finset.prod_le_prod₀ (s := Finset.univ)
          (fun i _ => (hτ.trans_le (hlo x (hPsub hx) i)).le)
          (fun i _ => (hrows x hx i).2)
        simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] using h
      _ = _ := by
        rw [Finset.sum_const,nsmul_eq_mul,mul_pow,← pow_mul]
        ring
  have htotal : (∑ x ∈ S, (∏ i, f i x)^2) ≤
      (T.card:ℝ)*((P.card:ℝ)*(Real.exp 1)^(2*Fintype.card ι)*(∏ i, B i)^2) := by
    simpa only [mul_comm] using (div_le_iff₀ hcard).mp (hweight.trans hbound)
  refine ⟨P,B,hPne,hPsub,hB,hrows,?_⟩
  have hTc : T.card = K^(Fintype.card ι) := by
    simp [T,Fintype.card_piFinset]
  rw [hTc] at htotal
  dsimp [K] at htotal
  push_cast at htotal ⊢
  convert htotal using 1
  ring


private lemma product_le_small_factor (f : ι → ℝ) {τ U : ℝ}
    (hf : ∀ i, 0 ≤ f i) (hU : 1 ≤ U) (hbound : ∀ i, f i ≤ U)
    (i : ι) (hi : f i ≤ τ) : (∏ j, f j) ≤ τ*U^(Fintype.card ι) := by
  have hτ : 0 ≤ τ := (hf i).trans hi
  rw [← Finset.prod_erase_mul Finset.univ f (Finset.mem_univ i)]
  have hprod : (∏ j ∈ Finset.univ.erase i, f j) ≤ U^((Finset.univ.erase i).card) := by
    simpa only [Finset.prod_const] using Finset.prod_le_prod₀
      (fun j _ => hf j) (fun j _ => hbound j)
  calc
    _ ≤ U^((Finset.univ.erase i).card)*τ := mul_le_mul hprod hi (hf i)
      (pow_nonneg (zero_le_one.trans hU) _)
    _ ≤ U^(Fintype.card ι)*τ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hU (by simpa only [Finset.card_univ] using Finset.card_le_card (Finset.erase_subset i Finset.univ))) hτ
    _ = _ := mul_comm _ _

/-- Rows with an extremely small factor have uniformly negligible total
energy once all other factors have their elementary upper bound. -/
theorem discard_small_factor_moment (S : Finset κ) (f : ι → κ → ℝ)
    {τ U : ℝ} (hU : 1 ≤ U)
    (hf : ∀ x ∈ S, ∀ i, 0 ≤ f i x)
    (hbound : ∀ x ∈ S, ∀ i, f i x ≤ U) :
    (∑ x ∈ S, (∏ i, f i x)^2) ≤
      (∑ x ∈ S with ∀ i, τ ≤ f i x, (∏ i, f i x)^2)+
        (S.card:ℝ)*(τ*U^(Fintype.card ι))^2 := by
  have hbad : (∑ x ∈ S with ¬∀ i, τ ≤ f i x, (∏ i, f i x)^2) ≤
      (S.card:ℝ)*(τ*U^(Fintype.card ι))^2 := by
    calc
      _ ≤ ∑ _x ∈ S.filter (fun x => ¬∀ i, τ ≤ f i x),
          (τ*U^(Fintype.card ι))^2 := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hxS,hxsmall⟩ := Finset.mem_filter.mp hx
        push Not at hxsmall
        obtain ⟨i,hi⟩ := hxsmall
        exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => hf x hxS i))
          (product_le_small_factor (fun i => f i x) (hf x hxS) hU (hbound x hxS) i hi.le) 2
      _ ≤ _ := by
        rw [Finset.sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (sq_nonneg _)
  have he := Finset.sum_filter_add_sum_filter_not S (fun x => ∀ i, τ ≤ f i x)
    (fun x => (∏ i, f i x)^2)
  linarith

/-- Compactness supplies simultaneous limiting exponents of the actual
selected row counts and factor scales. -/
theorem bounded_logarithms_subsequence {δ : Type*} [Finite δ]
    (Y : ℕ → ℝ) (f : δ → ℕ → ℝ) (l u : δ → ℝ)
    (hbound : ∀ j i, l i ≤ Real.log (f i j)/Real.log (Y j) ∧
      Real.log (f i j)/Real.log (Y j) ≤ u i) :
    ∃ (a : δ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, l i ≤ a i ∧ a i ≤ u i) ∧
      ∀ i, HasPowerExponent (Y ∘ φ) (f i ∘ φ) (a i) := by
  let x : ℕ → δ → ℝ := fun j i => Real.log (f i j)/Real.log (Y j)
  have hc : IsCompact {x : δ → ℝ | ∀ i, x i ∈ Set.Icc (l i) (u i)} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨a,ha,φ,hφ,hlim⟩ := hc.tendsto_subseq (fun j i => hbound j i)
  refine ⟨a,φ,hφ,ha,?_⟩
  intro i
  exact (tendsto_pi_nhds.mp hlim) i

end CubicFirstMoment

end

end OAI
