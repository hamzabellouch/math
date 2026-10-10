import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationModuli
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightScaleNumerics

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReplacementGeometry
open Construction Conclusion HistoryCRTIntegration

def frequencyLogCoefficient (Bs BD Bz : ℝ) (k : ℕ) : ℝ :=
  ((k+2:ℕ):ℝ)*(2*(2:ℝ)^(k+1))*(scaleLinearConstant Bs BD Bz k+1)

theorem frequencyLogCoefficient_pos (Bs BD Bz : ℝ) (k : ℕ) :
    0 < frequencyLogCoefficient Bs BD Bz k := by
  have hc := scaleLinearConstant_pos Bs BD Bz k
  unfold frequencyLogCoefficient
  positivity

theorem frequencyLogCoefficient_nonneg (Bs BD Bz : ℝ) (k : ℕ) :
    0 ≤ frequencyLogCoefficient Bs BD Bz k := (frequencyLogCoefficient_pos Bs BD Bz k).le

theorem supported_frequency_log_le_linear (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    {l : ℕ} (hl : l ≤ k) (hm : 1 ≤ bulkSize k L) {outside : List ℕ}
    (h : History l) (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
    (s : ℤ) (hmem : s ∈ h.frequencies) :
    0 < s.natAbs ∧ Real.log (s.natAbs:ℝ) ≤
      (scaleLinearConstant Bs BD Bz k+1)*(bulkSize k L:ℝ) := by
  obtain ⟨hs0,j,hjl,hj⟩ := History.supported_frequency_bounds hs s hmem
  have hp := Int.natAbs_pos.mpr hs0
  refine ⟨hp,?_⟩
  have hbound : (s.natAbs:ℝ) ≤ (frequencyBound Bs BD Bz k L j:ℝ)+1 := by
    have hn : (s.natAbs:ℝ) ≤ (frequencyBound Bs BD Bz k L j:ℝ) := by exact_mod_cast hj
    linarith
  exact (Real.log_le_log (by exact_mod_cast hp) hbound).trans
    (log_frequencyBound_add_one_le_linear Bs BD Bz k L hm (hjl.trans hl))

theorem log_nat_list_prod_le (S : List ℕ) (A : ℝ)
    (hS : ∀ q ∈ S, 0 < q ∧ Real.log (q:ℝ) ≤ A) :
    Real.log (S.prod:ℝ) ≤ (S.length:ℝ)*A := by
  induction S with
  | nil => simp
  | cons q S ih =>
    have hq := hS q List.mem_cons_self
    have ht := fun r hr => hS r (List.mem_cons_of_mem q hr)
    have hp : 0 < S.prod := List.prod_pos (fun r hr => (ht r hr).1)
    rw [List.prod_cons,Nat.cast_mul,Real.log_mul (by exact_mod_cast hq.1.ne')
      (by exact_mod_cast hp.ne')]
    calc
      _ ≤ A+(S.length:ℝ)*A := add_le_add hq.2 (ih ht)
      _ = ((q::S).length:ℝ)*A := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

theorem pair_frequency_count_le {l k : ℕ} (hl : l ≤ k) (h g : History l) :
    ((h.frequencies++g.frequencies).map Int.natAbs).length ≤ 2*2^(k+1) := by
  have hh := History.frequencies_length h
  have hg := History.frequencies_length g
  have hp : 2^(l+1) ≤ 2^(k+1) := Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hl 1)
  simp only [List.length_map,List.length_append]
  omega

theorem frequencyModulus_log_le (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    {l : ℕ} (hl : l ≤ k) (hm : 1 ≤ bulkSize k L) {outside : List ℕ}
    (h g : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
    (gs : g.Supported (frequencyBound Bs BD Bz k L) outside) :
    Real.log (frequencyModulus h g (k+2):ℝ) ≤
      frequencyLogCoefficient Bs BD Bz k*(bulkSize k L:ℝ) := by
  let A : ℝ := (scaleLinearConstant Bs BD Bz k+1)*(bulkSize k L:ℝ)
  have hA : 0 ≤ A := by
    have hc := scaleLinearConstant_pos Bs BD Bz k
    dsimp [A]
    positivity
  have hp : Real.log (FrequencyPrecision.product (h.frequencies++g.frequencies):ℝ) ≤
      (2*(2:ℝ)^(k+1))*A := by
    have hh := log_nat_list_prod_le ((h.frequencies++g.frequencies).map Int.natAbs) A
      (by
        intro q hq
        obtain ⟨s,hs',rfl⟩ := List.mem_map.mp hq
        rcases List.mem_append.mp hs' with hmem | hmem
        · exact supported_frequency_log_le_linear Bs BD Bz k L hl hm h hs s hmem
        · exact supported_frequency_log_le_linear Bs BD Bz k L hl hm g gs s hmem)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ hA
    exact_mod_cast pair_frequency_count_le hl h g
  rw [frequencyModulus,Nat.cast_pow,Real.log_pow]
  calc
    _ ≤ ((k+2:ℕ):ℝ)*((2*(2:ℝ)^(k+1))*A) :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = _ := by dsimp [frequencyLogCoefficient,A]; ring

end Ostmann.Arithmetic.HistoryBulkReplacementGeometry

end

end OAI
