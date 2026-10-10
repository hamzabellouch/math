import OAI.Combinatorics.HalvingLines.Decomposition

namespace OAI

open Filter Topology

namespace PlanarHalving.Sweep

lemma switchCount_le_sq {n : ℕ} (P : Fin n → Point) (k : ℕ) : switchCount P k≤n*n := by
  classical
  simpa only [switchCount,Finset.card_univ,Fintype.card_prod,Fintype.card_fin] using
    (Finset.card_le_card (Finset.filter_subset (fun ij : Fin n × Fin n =>
      ij.1 < ij.2 ∧ 0<k ∧ k<n ∧ belowCount P ij.1 ij.2=k-1) Finset.univ))

lemma packing_scale : ∃ q : ℕ, 4≤q ∧ ∀ {n k : ℕ} (P : Fin n → Point)
    (hP : Generic P) (hk : k≤n) (_hn : 4*q≤n),
    let b := n/q-1
    ∀ hb : 0<b, (((states P hP hk).activityGreedy 0 b hb).count:ℝ)+1≤(q:ℝ)^((4:ℝ)/3)/2 := by
  obtain ⟨Q,_,hpack⟩ := activity_saving_cubic (δ := (1:ℝ)/(524288*1024)) (by norm_num)
  obtain ⟨q,hq⟩ := exists_nat_gt (max (4:ℝ) Q)
  have hq4 : 4≤q := by exact_mod_cast (le_max_left (4:ℝ) Q).trans hq.le
  have hqQ : Q≤q := (le_max_right (4:ℝ) Q).trans hq.le
  refine ⟨q,hq4,?_⟩
  intro n k P hP hk hn b hb
  let S := states P hP hk
  let G := S.activityGreedy 0 b hb
  have hscale := division_scale hq4 hn
  change 0<b ∧ b+1=n/q ∧ (b+1:ℝ)≤(n:ℝ)/q ∧ n≤2*q*b ∧ b+1<n at hscale
  have hqb : q*b≤n := (Nat.mul_le_mul_left q (Nat.sub_le (n/q) 1)).trans (Nat.mul_div_le n q)
  have hratio : Q≤(n:ℝ)/b := hqQ.trans ((le_div_iff₀ (by exact_mod_cast hb)).mpr (by exact_mod_cast hqb))
  have hdata := G.intervals_data S
  have hh := hpack P hP hk hb hratio (G.intervals S) hdata.1
    (fun p hp => (hdata.2 p hp).1) (fun p hp => by
      rw [← S.activitySize_eq]
      exact (hdata.2 p hp).2)
  rw [G.intervals_card S] at hh
  apply greedy_count_bound hq4 hb hscale.2.2.2.1
  norm_num at hh
  nlinarith

lemma count_bound_induction {q : ℕ} (hq : 4≤q) {β : ℝ} (hβ : 0<β)
    (hpacking : ∀ {n k : ℕ} (P : Fin n → Point) (hP : Generic P) (hk : k≤n)
      (_hn : 4*q≤n), let b := n/q-1
      ∀ hb : 0<b, (((states P hP hk).activityGreedy 0 b hb).count:ℝ)+1≤(q:ℝ)^β) :
    ∀ n : ℕ, ∀ P : Fin n → Point, Generic P → ∀ k : ℕ, k≤n →
      (switchCount P k:ℝ)≤(4*(q:ℝ))^2*(n:ℝ)^β := by
  let C : ℝ := (4*(q:ℝ))^2
  have hC : 0≤C := sq_nonneg _
  have hq0 : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hP k hk
    by_cases hn : 4*q≤n
    · let b := n/q-1
      have hscale := division_scale hq hn
      change 0<b ∧ b+1=n/q ∧ (b+1:ℝ)≤(n:ℝ)/q ∧ n≤2*q*b ∧ b+1<n at hscale
      let hb := hscale.1
      let G := (states P hP hk).activityGreedy 0 b hb
      obtain ⟨A,r,hA,hr,hcount⟩ := activity_decomposition hP hk hb
      have hg : (G.count:ℝ)+1≤(q:ℝ)^β := hpacking P hP hk hn hb
      have hAreal (j : Fin (G.count+1)) : ((A j).card:ℝ)≤(n:ℝ)/q :=
        (by exact_mod_cast hA j : ((A j).card:ℝ)≤b+1).trans hscale.2.2.1
      have hind (j : Fin (G.count+1)) :
          (switchCount (subsetPoints P (A j)) (r j):ℝ)≤C*((A j).card:ℝ)^β :=
        ih (A j).card ((hA j).trans_lt hscale.2.2.2.2) (subsetPoints P (A j))
          (subsetPoints_generic hP (A j)) (r j) (hr j)
      change (switchCount P k:ℝ)≤C*(n:ℝ)^β
      calc
        (switchCount P k:ℝ) ≤ ∑ j : Fin (G.count+1), (switchCount (subsetPoints P (A j)) (r j):ℝ) := by exact_mod_cast hcount
        _ ≤ ∑ j : Fin (G.count+1), C*((A j).card:ℝ)^β := Finset.sum_le_sum (fun j _ => hind j)
        _ ≤ ∑ _j : Fin (G.count+1), C*((n:ℝ)/q)^β := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (hAreal j) hβ.le) hC)
        _ = C*((n:ℝ)/q)^β*((G.count:ℝ)+1) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one];ring
        _ ≤ C*((n:ℝ)/q)^β*(q:ℝ)^β := mul_le_mul_of_nonneg_left hg (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
        _ = C*(n:ℝ)^β := by rw [Real.div_rpow (by positivity) hq0.le];field_simp
    · have hs : (switchCount P k:ℝ)≤(n:ℝ)^2 := by exact_mod_cast (by simpa only [pow_two] using switchCount_le_sq P k : switchCount P k≤n^2)
      by_cases hz : n=0
      · subst n
        simpa only [Nat.cast_zero,zero_pow (by decide : (2:ℕ)≠0),Real.zero_rpow hβ.ne',mul_zero] using hs
      · have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
        have hnr : (n:ℝ)≤4*(q:ℝ) := by exact_mod_cast (le_of_lt (lt_of_not_ge hn))
        have hpow : 1≤(n:ℝ)^β := by
          simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1) hn1 hβ.le
        exact (hs.trans (pow_le_pow_left₀ (by positivity) hnr 2)).trans (le_mul_of_one_le_right hC hpow)

end PlanarHalving.Sweep

namespace PlanarHalving

theorem all_ranks_power :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ n : ℕ, 1 ≤ n → ∀ P : Fin n → Point, Generic P →
        ∀ k : ℕ, k ≤ n → (switchCount P k : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε) := by
  obtain ⟨q,hq,hpack⟩ := Sweep.packing_scale
  obtain ⟨ε,he,hβ,hpow⟩ := Sweep.recurrence_exponent hq
  refine ⟨ε,he,(4*(q:ℝ))^2,?_⟩
  intro n _ P hP k hk
  apply Sweep.count_bound_induction hq hβ _ n P hP k hk
  intro n k P hP hk hn b hb
  exact (hpack P hP hk hn hb).trans hpow
end PlanarHalving

end OAI
