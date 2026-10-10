import OAI.NumberTheory.DukePrimeDegree.Entropy.SmallReturnPartition
import OAI.NumberTheory.DukePrimeDegree.Entropy.RefinedReturnPartition

namespace OAI

/-! # A quantitative entropy budget for fine return cells -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma refined_return_information_le
    (K : ℕ → ℕ) (p : ∀ n, Fin (K n) → ℝ) (mass : ℕ → ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hm : ∀ n, ∑ i, p n i=mass n)
    (hm1 : ∀ n, mass n ≤ 1)
    (hmean : Summable (fun n : ℕ => (n+1:ℝ)*mass n))
    {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcard : ∀ n, Real.log (K n) ≤ a+b*(n+1))
    (hmass : (∑' n, mass n) ≤ m)
    (hmeanBound : (∑' n : ℕ, (n+1:ℝ)*mass n) ≤ 1) :
    (∑' z : Σ n : ℕ, Fin (K n), Real.negMulLog (p z.1 z.2)) ≤
      (∑' n, Real.negMulLog (mass n))+a*m+b := by
  have hm0 n : 0 ≤ mass n := by rw [←hm n]; exact Finset.sum_nonneg (fun i _ => hp n i)
  have hs : Summable mass := Summable.of_nonneg_of_le hm0
    (fun n => by nlinarith [hm0 n,Nat.cast_nonneg (α := ℝ) n]) hmean
  have hi := summable_information_of_first_moment mass hm0 hm1 hmean
  have hcap n : Real.log (K n) ≤ (a+b)*(n+1) := by
    have hn : 1 ≤ (n+1:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith [hcard n]
  have hfull := refined_return_information_summable K p mass hp hm hm1 hmean (a+b) hcap
  have hrows : Summable (fun n => finiteShannon (p n)) := by
    simpa only [tsum_fintype,finiteShannon] using hfull.sigma
  have hdom : Summable (fun n => Real.negMulLog (mass n)+a*mass n+
      b*((n+1:ℝ)*mass n)) := (hi.add (hs.mul_left a)).add (hmean.mul_left b)
  have H : (∑' n, finiteShannon (p n)) ≤
      ∑' n, (Real.negMulLog (mass n)+a*mass n+b*((n+1:ℝ)*mass n)) := by
    apply hrows.tsum_le_tsum _ hdom
    intro n
    have h := finiteShannon_le_mass_log_card (p n) (hp n)
    rw [hm n,Fintype.card_fin] at h
    nlinarith [mul_le_mul_of_nonneg_left (hcard n) (hm0 n)]
  rw [hfull.tsum_sigma]
  simp only [tsum_fintype]
  change (∑' n, finiteShannon (p n)) ≤ _
  rw [Summable.tsum_add (hi.add (hs.mul_left a)) (hmean.mul_left b),
    Summable.tsum_add hi (hs.mul_left a),tsum_mul_left,tsum_mul_left] at H
  have hma := mul_le_mul_of_nonneg_left hmass ha
  have hmb := mul_le_mul_of_nonneg_left hmeanBound hb
  linarith

lemma tsum_option_eq {α : Type*} (f : Option α → ℝ) (hs : Summable f) :
    (∑' z, f z)=f none+∑' z : α, f (some z) := by
  let e : Option α ≃ α ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit α
  have hh : Summable (fun z => f (e.symm z)) := hs.comp_injective e.symm.injective
  calc
    _ = ∑' z, f (e.symm z) := (e.symm.tsum_eq f).symm
    _ = _ := by
      rw [hh.comp_injective Sum.inl_injective |>.tsum_sum
        (hh.comp_injective Sum.inr_injective)]
      simp only [e,Equiv.optionEquivSumPUnit_symm_inl,
        Equiv.optionEquivSumPUnit_symm_inr,tsum_fintype,Finset.sum_const,
        Finset.card_univ,Fintype.card_punit,one_nsmul,add_comm]

/-- The refinement cost splits into section mass times a fixed grid cost,
plus the chosen exponential rate times the Kac return-time moment. -/
theorem returnRefinement_information_le
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S)
    (K : ℕ → ℕ) (B : ∀ n, Y → Fin (K n)) (hB : ∀ n, Measurable (B n))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcard : ∀ n, Real.log (K n) ≤ a+b*(n+1)) :
    (∑' z : Option (Σ n : ℕ, Fin (K n)),
      Real.negMulLog (μ.real {x | returnRefinement T S B x=z})) ≤
    (∑' n, Real.negMulLog (μ.real {x | firstReturnPartitionCode T S x=n}))+
      a*μ.real S+b := by
  let p := fun n (i : Fin (K n)) =>
    μ.real {x | x ∈ firstReturnLevel T S n ∧ B n x=i}
  have hm (n : ℕ) : ∑ i, p n i=μ.real (firstReturnLevel T S n) := by
    have hd : Pairwise (fun i j : Fin (K n) => Disjoint
        {x | x ∈ firstReturnLevel T S n ∧ B n x=i}
        {x | x ∈ firstReturnLevel T S n ∧ B n x=j}) := by
      intro i j hij
      exact disjoint_left.mpr (fun _ hi hj => hij (hi.2.symm.trans hj.2))
    have hme i : MeasurableSet {x | x ∈ firstReturnLevel T S n ∧ B n x=i} :=
      (measurableSet_firstReturnLevel hT.measurable hS n).inter
        (hB n (measurableSet_singleton i))
    change (∑ i, μ.real {x | x ∈ firstReturnLevel T S n ∧ B n x=i})=_
    rw [←measureReal_iUnion_fintype hd hme]
    congr 1
    ext x
    simp only [mem_iUnion,mem_ofPred_eq]
    exact ⟨fun ⟨_,hx,_⟩ => hx,fun hx => ⟨B n x,hx,rfl⟩⟩
  have H := refined_return_information_le K p
    (fun n => μ.real (firstReturnLevel T S n))
    (fun _ _ => measureReal_nonneg) hm (fun _ => measureReal_le_one)
    (summable_firstReturnLevel_mass μ hT hE hS) ha hb hcard
    (firstReturnLevel_real_mass_sum_le μ hT.measurable hS)
    (firstReturnLevel_real_mean_le_one μ hT hE hS)
  have hcap n : Real.log (K n) ≤ (a+b)*(n+1) := by
    nlinarith [hcard n, mul_nonneg ha (Nat.cast_nonneg (α := ℝ) n)]
  have hs := returnRefinement_information_summable μ hT hE hS K B hB (a+b) hcap
  rw [tsum_option_eq _ hs,firstReturnPartitionCode_entropy_eq μ hT hE hS]
  have hz : {x | returnRefinement T S B x=none}=
      {x | firstReturnPartitionCode T S x=0} := by
    rw [returnRefinement_fiber]
    ext x
    exact (firstReturnPartitionCode_eq_iff T S x 0).symm
  rw [hz,firstReturnPartitionCode_zero_mass μ hT hS]
  have he (z : Σ n : ℕ, Fin (K n)) :
      μ.real {x | returnRefinement T S B x=some z}=p z.1 z.2 := by
    rw [returnRefinement_fiber]
    rfl
  simp only [he]
  linarith

end DukePrimeDegree

end

end OAI
