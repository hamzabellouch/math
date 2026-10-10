import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SmoothCofactorSumEq
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CofactorEnergy
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CappedRectangle
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.IntervalWidthSum
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SmallSmoothCountFinite
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LogSmoothPart
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Grid

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

namespace OrdinarySmoothRough
open Finset OrdinaryNarrowGrid OrdinarySelbergWeights OrdinaryCorrelations Filter

lemma grid_min_lower (q r R : ℕ) {i : ℕ×ℕ} (hi : i∈grid q r R) :
    q*2^r ≤ lower i := by
  have hr := (mem_Ico.mp (mem_product.mp hi).1).1
  have hq := (mem_Ico.mp (mem_product.mp hi).2).1
  unfold lower
  exact Nat.mul_le_mul hq (Nat.pow_le_pow_right (by norm_num) hr)

lemma grid_boundary_bound (S : Finset ℕ) (hS : ∀ p∈S, Nat.Prime p)
    (N q r R z : ℕ) (hq : 0<q) (hz : 1≤z) (hprime : Squarefree (∏ p∈S,p)) :
    (∑ i∈grid q r R, ((upper i:ℝ)-(lower i:ℝ)) *
        ((3*(N:ℝ)*((upper i:ℝ)-(lower i:ℝ))/((lower i:ℝ)*(upper i:ℝ)) + 8) *
          (actualMass (∏ p∈S,p) z hprime)⁻¹ + 4*(z:ℝ)^4)) ≤
      3*(N:ℝ)*(actualMass (∏ p∈S,p) z hprime)⁻¹*R/q +
        (8*(actualMass (∏ p∈S,p) z hprime)⁻¹+4*(z:ℝ)^4)*(q*2^(r+R):ℕ) := by
  have hmass : 0 < actualMass (∏ p∈S,p) z hprime := by
    unfold actualMass mass
    apply Finset.sum_pos'
    · intro divisor hdivisor
      split_ifs
      · exact ((reciprocalSieve _ hprime).selbergTerms_pos
          (Nat.dvd_of_mem_divisors hdivisor)).le
      · exact le_rfl
    · refine ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, ?_⟩, ?_⟩
      · exact Finset.prod_ne_zero_iff.mpr (fun prime hmem => (hS prime hmem).ne_zero)
      · simpa only [ite_eq_left hz] using
          (reciprocalSieve _ hprime).selbergTerms_pos (one_dvd _)
  have h := boundary_sum_bound (grid q r R) lower upper N (q*2^(r+R)) z
    (actualMass (∏ p∈S,p) z hprime) (1/(q:ℝ)^2) hmass (by positivity)
    (fun i _ => lower_le_upper i) (fun i hi => upper_le_endpoint q r R hi)
    (grid_disjoint q r R hq) (fun i hi => relative_width q r R hq hi)
  rw [grid_card] at h
  have hq' : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  convert h using 1
  push_cast
  field_simp

lemma large_smooth_above (S : Finset ℕ) (e N U : ℕ)
    (hS : S ⊆ Nat.primesLE (2^e)) (hU : 1<U) :
    (((Finset.Icc 1 N).filter (fun n => U < smoothPart S n)).card:ℝ) ≤
      (N:ℝ)*(2*Real.log 4*e)/Real.log U := by
  have hU' : (1:ℝ)<U := by exact_mod_cast hU
  apply le_trans _ (large_smooth_count S e N hS (Real.log_pos hU'))
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnI,hpart⟩ := mem_filter.mp hn
  apply mem_filter.mpr ⟨hnI,?_⟩
  apply Real.log_le_log (by linarith : (0:ℝ)<U)
  exact_mod_cast hpart.le

theorem grid_remainder_density (S : Finset ℕ) (e N q r R z : ℕ)
    (hS : S ⊆ Nat.primesLE (2^e)) (hq : 0<q) (hz : 1≤z)
    (hU : 1<q*2^(r+R)) (hprime : Squarefree (∏ p∈S,p)) :
    (((Finset.Ioc N (2*N)) \ (grid q r R).biUnion (fun i => cappedRectangle S N (lower i) (upper i))).card:ℝ) ≤
      (2*N:ℕ)*(actualMass (∏ p∈S,p) z hprime)⁻¹*(1+Real.log (q*2^r:ℕ)) +
      (q*2^r:ℕ)*(z:ℝ)^4 +
      (2*N:ℕ)*(2*Real.log 4*e)/Real.log (q*2^(r+R):ℕ) +
      (3*(N:ℝ)*(actualMass (∏ p∈S,p) z hprime)⁻¹*R/q +
        (8*(actualMass (∏ p∈S,p) z hprime)⁻¹+4*(z:ℝ)^4)*(q*2^(r+R):ℕ)) := by
  have hS' : ∀ p∈S, Nat.Prime p := fun p hp => (Nat.mem_primesLE.mp (hS hp)).2
  have h := capped_family_remainder_sieve S hS' N (q*2^r) (q*2^(r+R)) z (grid q r R)
    lower upper (fun a hl hu => grid_cover q r R a hl hu)
    (fun i hi => grid_lower_pos q r R hq hi) (fun i _ => lower_le_upper i) hz hprime
  have hs := small_smooth_count S hS' (2*N) (q*2^r) z hprime hz
  have hl := large_smooth_above S e (2*N) (q*2^(r+R)) hS hU
  have hb := grid_boundary_bound S hS' N q r R z hq hz hprime
  linarith

private lemma reciprocal_loss_mono (c : ℝ) (hc : 0≤c) (K B : ℕ)
    (hK : 0<K) (hKB : K≤B) : c/(B:ℝ) ≤ c/(K:ℝ) := by
  apply div_le_div_of_nonneg_left hc (by exact_mod_cast hK)
  exact_mod_cast hKB

theorem uniform_sparse_grid_cofactor {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    (k : ℕ) (hk : 1≤k) {ε : ℝ} (hε : 0<ε) :
    ∃ M₀ : ℕ, ∀ (P S : Finset ℕ) (T : Finset ℝ) (e H q r R u K z : ℕ)
      (hprime : Squarefree (∏ p∈S,p)),
      S ⊆ Nat.primesLE (2^e) → P ⊆ S →
      0<H → 0<q → 1≤u → H≤u^8 → 0<K → 1≤z → z^2≤K →
      M₀≤q*2^r → 1<q*2^(r+R) →
      (∀ i∈grid q r R, K≤(2*H)/(2*lower i) ∧ (2*H)/(2*lower i)≤u^8) →
      (T : Set ℝ).Pairwise (fun x y => 1≤|x-y|) →
      (∀ t∈T, ∀ s∈T, |t-s|≤(u:ℝ)^10) →
      (∀ t∈T, |t|≤((q*2^r:ℕ):ℝ)^k/2) →
      cofactorEnergy f P (Ioc (2*H) (4*H)) T ≤
      2*((R*q:ℕ):ℝ)^2*ε^2 *
        ((264*(actualMass (∏ p∈S,p) z hprime)⁻¹ + 3200*(T.card:ℝ)*(z:ℝ)^4*(u:ℝ)^7/K) *
         (44*(actualMass (∏ p∈S,p) z hprime)⁻¹ + 3200*(z:ℝ)^4*(u:ℝ)^7/K)/4) +
      2*(264+3200*(T.card:ℝ)*(u:ℝ)^7/H) *
        ((4*H:ℕ)*(actualMass (∏ p∈S,p) z hprime)⁻¹*(1+Real.log (q*2^r:ℕ)) +
          (q*2^r:ℕ)*(z:ℝ)^4 +
          (4*H:ℕ)*(2*Real.log 4*e)/Real.log (q*2^(r+R):ℕ) +
          (6*(H:ℝ)*(actualMass (∏ p∈S,p) z hprime)⁻¹*R/q +
            (8*(actualMass (∏ p∈S,p) z hprime)⁻¹+4*(z:ℝ)^4)*(q*2^(r+R):ℕ))) / (4*(H:ℝ)) := by
  obtain ⟨M₀,hM⟩ := eventually_atTop.mp (uniform_actual_rectangle_energy hf hm hNP k hk hε)
  refine ⟨M₀,?_⟩
  intro P S T e H q r R u K z hprime hS hPS hH hq hu hHu hK hz hzK hM₀ hU hscale hsep hheight hTs
  let I := grid q r R
  let C := fun i => cappedRectangle S (2*H) (lower i) (upper i)
  let G := actualMass (∏ p∈S,p) z hprime
  let E := ((264*G⁻¹ + 3200*(T.card:ℝ)*(z:ℝ)^4*(u:ℝ)^7/K) *
         (44*G⁻¹ + 3200*(z:ℝ)^4*(u:ℝ)^7/K)/4)
  have hG : 0<G := mass_pos _ hz
  have hS' : ∀ p∈S, Nat.Prime p := fun p hp => (Nat.mem_primesLE.mp (hS hp)).2
  have hC : ∀ i∈I, C i ⊆ Ioc (2*H) (4*H) := by
    intro i hi
    exact (cappedRectangle_subset_slice S (2*H) (lower i) (upper i)
      (grid_lower_pos q r R hq hi)).trans (by
        intro n hn
        have hh := (mem_filter.mp hn).1
        simpa only [show 2*(2*H)=4*H by omega] using hh)
  have hd : (I : Set (ℕ×ℕ)).PairwiseDisjoint C := by
    intro i hi j hj hij
    exact cappedRectangle_disjoint S (2*H) (lower i) (upper i) (lower j) (upper j)
      (grid_lower_pos q r R hq hi) (grid_lower_pos q r R hq hj)
      (grid_disjoint q r R hq hi hj hij)
  have hblock : ∀ i∈I, cofactorEnergy f P (C i) T ≤ ε^2*E := by
    intro i hi
    let B := (2*H)/(2*lower i)
    have hA := grid_lower_pos q r R hq hi
    have hKB : K≤B := (hscale i hi).1
    have hB : 0<B := hK.trans_le hKB
    have hBz : z^2≤B := hzK.trans hKB
    have hh := hM (lower i) (hM₀.trans (grid_min_lower q r R hi)) (upper i)
      (lower_le_upper i) (upper_le_two_lower q r R hq hi) P S
      (roughBlock S ((2*H)/lower i) (capUpper (2*H) (lower i) (upper i))) T u B z hS' hprime hPS
      (fun b hb => ⟨lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp (mem_filter.mp hb).1).1,
        rough_of_coprime_product S (mem_filter.mp hb).2⟩)
      hu hB (hscale i hi).2 hz hBz (capped_rough_scale S (2*H) (lower i) (upper i) hA)
      hsep hheight (fun t ht => (hTs t ht).trans (by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact_mod_cast Nat.pow_le_pow_left (grid_min_lower q r R hi) k))
    change cofactorEnergy f P (C i) T ≤
      ε^2*((264*G⁻¹ + 3200*(T.card:ℝ)*(z:ℝ)^4*(u:ℝ)^7/B) *
         (44*G⁻¹ + 3200*(z:ℝ)^4*(u:ℝ)^7/B)/4) at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg ε)
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul
    · exact _root_.add_le_add le_rfl (reciprocal_loss_mono _ (by positivity) K B hK hKB)
    · exact _root_.add_le_add le_rfl (reciprocal_loss_mono _ (by positivity) K B hK hKB)
    · positivity
    · positivity
  have hsum : (∑ i∈I, cofactorEnergy f P (C i) T) ≤ (I.card:ℝ)*(ε^2*E) := by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum hblock
  have hsplit := sparse_cofactor_decomposition hf P (Ioc (2*H) (4*H)) I C T u H hu hH hHu
    (fun n hn => mem_Icc.mpr ⟨(mem_Ioc.mp hn).1.le,(mem_Ioc.mp hn).2⟩) hC hd hsep hheight
  have htail := grid_remainder_density S e (2*H) q r R z hS hq hz hU hprime
  simp only [show 2*(2*H)=4*H by omega] at htail
  have hfac : 0≤ 2*(264+3200*(T.card:ℝ)*(u:ℝ)^7/H)/(4*(H:ℝ)) := by positivity
  have hs1 := mul_le_mul_of_nonneg_left hsum (show 0≤2*(I.card:ℝ) by positivity)
  have hs2 := mul_le_mul_of_nonneg_left htail hfac
  have hcard : (I.card:ℝ) = (R*q:ℕ) := by change ((grid q r R).card:ℝ) = (R*q:ℕ); rw [grid_card]
  rw [hcard] at hs1 hsplit
  dsimp only [I,C,E,G] at hs1 hs2 hsplit
  push_cast at hs1 hs2 hsplit ⊢
  apply hsplit.trans
  convert _root_.add_le_add hs1 hs2 using 1 <;> ring

end OrdinarySmoothRough

end

end OAI
