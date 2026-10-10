import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBoundedMass
import OAI.NumberTheory.CubicMoment.Estimates.WeightedDivisorEnergy
import OAI.NumberTheory.CubicMoment.Estimates.PrimeSubsetNormTail

namespace OAI

/-! Pointwise bounds for all rows in the actual coprimality expansion.
The small-core estimate sums inverse-square quotient lengths, while the
hybrid core estimate sums the proved logarithmic divisor energy. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma bounded_filtered_character_row (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    {N M : ℝ} (hN : 0 ≤ N)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N)
    (hβ : ∀ a ∈ S, ‖β a‖ ≤ M) {d : Eisenstein} (hd : primary d) (v : Eisenstein) :
    ‖∑ a ∈ S.filter (fun a => d ∣ a), β a*cubicSymbol a v‖^2 ≤
      324*N^2*M^2*(norm d)^(-2:ℝ) := by
  have hdp := norm_pos_of_ne_zero (primary_ne_zero hd)
  have hr := residualRows_primary hd (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩)
  have hrows : ∀ a ∈ residualRows S d, primary a ∧ norm a ≤ N/norm d := by
    intro a ha
    have hh := hS (d*a) ((mem_residualRows (primary_ne_zero hd)).mp ha)
    refine ⟨(hr a ha).1,(le_div_iff₀ hdp).mpr ?_⟩
    simpa only [norm_mul_eq,mul_comm] using hh.2.2
  have heq : (∑ a ∈ S.filter (fun a => d ∣ a), β a*cubicSymbol a v) =
      cubicSymbol d v*∑ a ∈ residualRows S d, β (d*a)*cubicSymbol a v := by
    rw [←sum_residualRows (S := S) (primary_ne_zero hd),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [cubicSymbol_mul_lower (primary_ne_zero hd) (primary_ne_zero (hr a ha).1)]
    ring
  rw [heq,norm_mul,mul_pow]
  have hnorm : ‖cubicSymbol d v‖^2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hd v) 2
  have hb := bounded_primary_character_row (residualRows S d) (fun a => β (d*a))
    (div_nonneg hN hdp.le) hrows
    (fun a ha => hβ (d*a) ((mem_residualRows (primary_ne_zero hd)).mp ha)) v
  calc
    _ ≤ 1*(324*(N/norm d)^2*M^2) :=
      mul_le_mul hnorm hb (sq_nonneg _) (by norm_num)
    _ = _ := by
      rw [Real.rpow_neg hdp.le,Real.rpow_two,div_pow]
      ring

lemma bounded_divisor_character_row (S U : Finset Eisenstein)
    (β : Eisenstein → ℂ) {N M : ℝ} (hN : 0 ≤ N)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N)
    (hβ : ∀ a ∈ S, ‖β a‖ ≤ M) (hU : ∀ p ∈ U, primaryPrime p) (v : Eisenstein) :
    (∑ s ∈ U.powerset, ‖∑ a ∈ S.filter (fun a => (∏ p ∈ s,p) ∣ a),
      β a*cubicSymbol a v‖^2) ≤
      324*N^2*M^2*(∑' n : Eisenstein, norm n^(-2:ℝ)) := by
  calc
    _ ≤ ∑ s ∈ U.powerset, 324*N^2*M^2*norm (∏ p ∈ s,p)^(-2:ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      exact bounded_filtered_character_row S β hN hS hβ
        (primary_finset_prod s (fun p => p) (fun p hp => (hU p (Finset.mem_powerset.mp hs hp)).1)) v
    _ = (324*N^2*M^2)*(∑ s ∈ U.powerset, norm (∏ p ∈ s,p)^(-2:ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (primary_prime_subset_norm_sum U hU U.powerset (Finset.Subset.refl _) (by norm_num))
      (by positivity)

theorem bounded_divisor_all_frequency_mass (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S H U : Finset Eisenstein)
      (β : Eisenstein → ℂ) (N M B : ℝ), 65536 ≤ N → 0 ≤ M → 1 ≤ B →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ a ∈ S, ‖β a‖ ≤ M) → (∀ p ∈ U, primaryPrime p) →
      8*B ≤ N^(3/4:ℝ) → (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B) →
      (∑ s ∈ U.powerset, ∑ v ∈ H,
        ‖∑ a ∈ S.filter (fun a => (∏ p ∈ s,p) ∣ a), β a*cubicSymbol a v‖^2) ≤
        K*M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^d := by
  obtain ⟨C,d,hC,henergy⟩ := bounded_third_divisor_energy hpnt
  obtain ⟨K,hK,hcore⟩ := smallB_core_hybrid_sieve hHuxley
  obtain ⟨I,hI,hcount⟩ := core_dyadic_index_log_count
  let c : ℝ := ((1:ℝ)/5832)^(-(1/4:ℝ))
  let Z := ∑' n : Eisenstein, norm n^(-2:ℝ)
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hZ : 0 ≤ Z := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  refine ⟨110808*Z+K*(c+1)*C*I+1,d+2,by positivity,?_⟩
  intro S H U β N M B hN hM hB hS hβ hU hsize hH
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hNE : Real.exp 1 ≤ N := by
    have hh : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
    linarith
  have hL : 1 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN1]
  have hBN : B ≤ N := by
    have ht : N^(3/4:ℝ) ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (3/4:ℝ) ≤ 1)
    linarith
  let f := fun v => ∑ s ∈ U.powerset,
    ‖∑ a ∈ S.filter (fun a => (∏ p ∈ s,p) ∣ a), β a*cubicSymbol a v‖^2
  have hf : ∀ v, 0 ≤ f v := fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have htriv (v : Eisenstein) : f v ≤ 324*N^2*M^2*Z :=
    bounded_divisor_character_row S U β hNp.le hS hβ hU v
  have he : (∑ s ∈ U.powerset, ∑ a ∈ S.filter (fun a => (∏ p ∈ s,p) ∣ a), ‖β a‖^2) ≤
      C*M^2*N*(1+Real.log N)^d :=
    (ordinary_divisor_row_energy S U β hU (fun a ha => (hS a ha).1)).trans
      (henergy S β N M hNE hM hS hβ)
  let HN := H.filter (fun v => ¬∃ a : Eisenstein, a^3 = v)
  let HC := H.filter (fun v => ∃ a : Eisenstein, a^3 = v)
  let HS := HN.filter (fun v => v ∈ lowNoncubeSupport 1 (B^(1/3:ℝ)))
  have hcardS : (HS.card:ℝ) ≤ 324*B^(1/3:ℝ) := by
    simpa only [mul_one] using
      (Nat.cast_le.mpr (Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2))).trans
        (lowNoncubeSupport_card (by norm_num : (0:ℝ) ≤ 1) (Real.rpow_nonneg hB0 _))
  have hcardC : (HC.card:ℝ) ≤ 18*B^(1/3:ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card (by
      intro v hv
      exact mem_nonzeroCubeNormBall (hH v (Finset.mem_filter.mp hv).1).1
        (hH v (Finset.mem_filter.mp hv).1).2 (Finset.mem_filter.mp hv).2))).trans
          (nonzeroCubeNormBall_card hB0)
  have hsmall : (∑ v ∈ HS, f v)+(∑ v ∈ HC, f v) ≤ 110808*Z*M^2*N^2*B^(1/3:ℝ) := by
    have hs := Finset.sum_le_sum (fun v (_ : v ∈ HS) => htriv v)
    have hh := Finset.sum_le_sum (fun v (_ : v ∈ HC) => htriv v)
    simp only [Finset.sum_const,nsmul_eq_mul] at hs hh
    have hb := mul_le_mul_of_nonneg_right (add_le_add hcardS hcardC)
      (show 0 ≤ 324*N^2*M^2*Z by positivity)
    calc
      _ ≤ (HS.card:ℝ)*(324*N^2*M^2*Z)+(HC.card:ℝ)*(324*N^2*M^2*Z) :=
        add_le_add hs hh
      _ = ((HS.card:ℝ)+(HC.card:ℝ))*(324*N^2*M^2*Z) := by ring
      _ ≤ (324*B^(1/3:ℝ)+18*B^(1/3:ℝ))*(324*N^2*M^2*Z) := hb
      _ = _ := by ring
  have hrow (q : ℕ × ℕ) (hq : q ∈ largeCoreDyadicIndices 1 B) :
      (∑ v ∈ coreDyadicBlock B q.1 q.2, f v) ≤
        (K*(c+1)*C)*M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^d := by
    have hq' := (Finset.mem_filter.mp hq).2
    have hp : N^(1-1/20000:ℝ) ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
        (by norm_num : (1-1/20000:ℝ) ≤ 1)
    have hb : N*c+N^(1-1/20000:ℝ) ≤ N*(c+1) := by nlinarith
    have hr (s : Finset Eisenstein) (_hs : s ∈ U.powerset) :=
      hcore (S.filter (fun a => (∏ p ∈ s,p) ∣ a)) (coreDyadicBlock B q.1 q.2) β
        N B 1 q.1 q.2 hN hB0 (by norm_num)
        (fun a ha => hS a (Finset.mem_filter.mp ha).1) hq'.1.le
        ((mul_le_mul_of_nonneg_left hq'.2 (by norm_num : (0:ℝ) ≤ 8)).trans hsize)
        (Finset.Subset.refl _)
    change (∑ v ∈ coreDyadicBlock B q.1 q.2, ∑ s ∈ U.powerset, _) ≤ _
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ s ∈ U.powerset, K*B^(1/3:ℝ)*(N*c+N^(1-1/20000:ℝ))*
          ∑ a ∈ S.filter (fun a => (∏ p ∈ s,p) ∣ a), ‖β a‖^2 := Finset.sum_le_sum hr
      _ = (K*B^(1/3:ℝ)*(N*c+N^(1-1/20000:ℝ)))*
          (∑ s ∈ U.powerset, ∑ a ∈ S.filter (fun a => (∏ p ∈ s,p) ∣ a), ‖β a‖^2) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (K*B^(1/3:ℝ)*(N*(c+1)))*(C*M^2*N*(1+Real.log N)^d) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) he
          (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by positivity)
      _ = _ := by ring
  have hcount' : ((largeCoreDyadicIndices 1 B).card:ℝ) ≤ I*(1+Real.log N)^2 :=
    hcount 1 B N hB hN1 (hBN.trans (by nlinarith))
  have hlarge := Finset.sum_le_sum hrow
  simp only [Finset.sum_const,nsmul_eq_mul] at hlarge
  have hlarge' : (∑ q ∈ largeCoreDyadicIndices 1 B, ∑ v ∈ coreDyadicBlock B q.1 q.2, f v) ≤
      (K*(c+1)*C*I)*M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^(d+2) := by
    apply hlarge.trans
    calc
      _ ≤ (I*(1+Real.log N)^2)*((K*(c+1)*C)*M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^d) :=
        mul_le_mul_of_nonneg_right hcount' (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hsmall' : (∑ v ∈ HS, f v)+(∑ v ∈ HC, f v) ≤
      (110808*Z)*M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^(d+2) := by
    exact hsmall.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL))
  have hsplit := noncube_frequency_mass_split HN (V := 1) (B := B)
    (fun v hv => ⟨(hH v (Finset.mem_filter.mp hv).1).1,
      (hH v (Finset.mem_filter.mp hv).1).2,(Finset.mem_filter.mp hv).2⟩) f hf
  have heq : (∑ v ∈ H, f v) = (∑ v ∈ HN, f v)+(∑ v ∈ HC, f v) := by
    simpa only [HN,HC,not_not] using
      (Finset.sum_filter_add_sum_filter_not H (fun v => ¬∃ a : Eisenstein, a^3 = v) f).symm
  change (∑ s ∈ U.powerset, ∑ v ∈ H, _) ≤ _
  rw [Finset.sum_comm]
  change (∑ v ∈ H, f v) ≤ _
  rw [heq]
  change (∑ v ∈ HN, f v) ≤ (∑ v ∈ HS, f v)+
    ∑ q ∈ largeCoreDyadicIndices 1 B, ∑ v ∈ coreDyadicBlock B q.1 q.2, f v at hsplit
  calc
    _ ≤ ((∑ v ∈ HS, f v)+(∑ q ∈ largeCoreDyadicIndices 1 B,
        ∑ v ∈ coreDyadicBlock B q.1 q.2, f v))+(∑ v ∈ HC, f v) :=
      add_le_add hsplit le_rfl
    _ = ((∑ v ∈ HS, f v)+(∑ v ∈ HC, f v))+
        (∑ q ∈ largeCoreDyadicIndices 1 B, ∑ v ∈ coreDyadicBlock B q.1 q.2, f v) := by ring
    _ ≤ (110808*Z)*M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^(d+2)+
        (K*(c+1)*C*I)*M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^(d+2) :=
      add_le_add hsmall' hlarge'
    _ ≤ _ := by
      have hp : 0 ≤ M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^(d+2) := by positivity
      nlinarith

end CubicFirstMoment

end

end OAI
