import OAI.NumberTheory.JointDickman.Counting.PeriodicAverages
import OAI.NumberTheory.JointDickman.Counting.CountingShift

namespace OAI

/-! # A periodic average with a slowly varying counting parameter -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem sum_range_blocks_real (f : ℕ → ℝ) (q k : ℕ) :
    (∑ u ∈ range (k*q), f u) = ∑ b ∈ range k, ∑ r ∈ range q, f (b*q+r) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul,sum_range_add,ih,sum_range_succ]

theorem slow_periodic_sum_bound {q : ℕ} (hq : 0 < q) (f : ℕ → ℝ → ℝ)
    {A L δ : ℝ} (hL : 0 ≤ L) (_hδ : 0 ≤ δ)
    (hpos : ∀ u s, |s| ≤ 3 → 0 ≤ f u s)
    (hper : ∀ b r s, f (b*q+r) s = f r s)
    (hmean : ∀ s, |s| ≤ 3 → (∑ r ∈ range q, f r s) ≤ (q : ℝ)*A)
    (hlip : ∀ u s t, |s| ≤ 3 → |t| ≤ 3 → |f u s-f u t| ≤ L*|s-t|)
    (K : ℕ) (σ : ℕ → ℝ) (hσ : ∀ u, |σ u| ≤ 3)
    (hstep : ∀ b r, r < q → |σ (b*q+r)-σ (b*q)| ≤ δ) :
    (∑ u ∈ range K, f u (σ u)) ≤ ((K/q+1)*q : ℕ)*(A+L*δ) := by
  have hsub : range K ⊆ range ((K/q+1)*q) := by
    apply range_mono
    have hm := Nat.mod_lt K hq
    have he : K/q*q+K%q = K := by simpa only [Nat.mul_comm] using Nat.div_add_mod K q
    simp only [Nat.add_mul,one_mul]
    omega
  calc
    _ ≤ ∑ u ∈ range ((K/q+1)*q), f u (σ u) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hpos u (σ u) (hσ u))
    _ = ∑ b ∈ range (K/q+1), ∑ r ∈ range q, f (b*q+r) (σ (b*q+r)) :=
      sum_range_blocks_real _ _ _
    _ ≤ ∑ b ∈ range (K/q+1), (q : ℝ)*(A+L*δ) := by
      apply sum_le_sum
      intro b _
      calc
        _ ≤ ∑ r ∈ range q, (f r (σ (b*q))+L*δ) := by
          apply sum_le_sum
          intro r hr
          have hh := (le_abs_self (f (b*q+r) (σ (b*q+r))-f (b*q+r) (σ (b*q)))).trans
            ((hlip _ _ _ (hσ _) (hσ _)).trans
              (mul_le_mul_of_nonneg_left (hstep b r (mem_range.mp hr)) hL))
          simp only [hper] at hh ⊢
          linarith
        _ = (∑ r ∈ range q, f r (σ (b*q)))+(q : ℝ)*(L*δ) := by simp [sum_add_distrib]
        _ ≤ (q : ℝ)*A+(q : ℝ)*(L*δ) := add_le_add (hmean _ (hσ _)) le_rfl
        _ = _ := by ring
    _ = _ := by simp; ring

theorem slow_periodic_mean_bound {q T : ℕ} (hq : 0 < q) (hT : 0 < T)
    (f : ℕ → ℝ → ℝ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hpos : ∀ u s, |s| ≤ 3 → 0 ≤ f u s)
    (hper : ∀ b r s, f (b*q+r) s = f r s)
    (hmean : ∀ s, |s| ≤ 3 → (∑ r ∈ range q, f r s) ≤ (q : ℝ)*A)
    (hlip : ∀ u s t, |s| ≤ 3 → |t| ≤ 3 → |f u s-f u t| ≤ L*|s-t|)
    (J : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ σ : ℕ → ℝ, (∀ u, |σ u| ≤ 3) →
      (∀ b r, r < q → |σ (b*q+r)-σ (b*q)| ≤ (q : ℝ)/((T : ℝ)*(N+1))) →
      (∑ u ∈ range (J*N), f u (σ u))/(N : ℝ) < (J : ℝ)*A+ε := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hrec := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (q : ℝ)
  have hrec' : Tendsto (fun N : ℕ => (q : ℝ)/((T : ℝ)*(N+1))) atTop (𝓝 0) := by
    have hh := (tendsto_add_atTop_nat 1).comp tendsto_id
    have ht := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) ((q : ℝ)/T)).comp hh
    simpa only [Function.comp_def,id_eq,Nat.cast_add,Nat.cast_one,div_div] using ht
  have hlim : Tendsto (fun N : ℕ => ((J : ℝ)+(q : ℝ)/N)*
      (A+L*((q : ℝ)/((T : ℝ)*(N+1))))) atTop (𝓝 ((J : ℝ)*A)) := by
    simpa only [add_zero,mul_zero] using
      (tendsto_const_nhds.add hrec).mul (tendsto_const_nhds.add (hrec'.const_mul L))
  filter_upwards [hlim.eventually (eventually_lt_nhds (lt_add_of_pos_right ((J : ℝ)*A) hε)),
    eventually_gt_atTop 0] with N hN hNpos
  intro σ hσ hstep
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  apply (div_le_div_of_nonneg_right (slow_periodic_sum_bound hq f hL (by positivity)
    hpos hper hmean hlip (J*N) σ hσ hstep) hNr.le).trans_lt
  have hcard : (((J*N/q+1)*q : ℕ) : ℝ) ≤ (J : ℝ)*N+q := by
    exact_mod_cast (show (J*N/q+1)*q ≤ J*N+q by
      nlinarith [Nat.div_mul_le_self (J*N) q])
  calc
    _ ≤ (((J : ℝ)*N+q)*(A+L*((q : ℝ)/((T : ℝ)*(N+1)))))/(N : ℝ) := by
      gcongr
    _ = ((J : ℝ)+(q : ℝ)/N)*(A+L*((q : ℝ)/((T : ℝ)*(N+1)))) := by field_simp
    _ < _ := hN

end JointDickman

end OAI
