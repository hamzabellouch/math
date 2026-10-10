import Mathlib
import OAI.Probability.SKValue.Evolution.FiniteStepEvolution

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def gridProfile (d : ℝ≥0) (f : ℕ → ℝ≥0) : ℕ → ℕ → HeatProfile
  | _,0 => []
  | j,n+1 => (d,f j)::gridProfile d f (j+1) n

lemma gridProfile_time (d : ℝ≥0) (f : ℕ → ℝ≥0) (j n : ℕ) :
    profileTime (gridProfile d f j n)=(n : ℝ)*d := by
  induction n generalizing j with
  | zero => simp only [gridProfile,profileTime,Nat.cast_zero,zero_mul]
  | succ n ih => simp only [gridProfile,profileTime,ih,Nat.cast_add,Nat.cast_one]; ring

lemma gridProfile_mem {d : ℝ≥0} {f : ℕ → ℝ≥0} {j n : ℕ} {p : ℝ≥0 × ℝ≥0}
    (hp : p∈gridProfile d f j n) : ∃ i, j ≤ i ∧ i<j+n ∧ p=(d,f i) := by
  induction n generalizing j with
  | zero => simp only [gridProfile,List.not_mem_nil] at hp
  | succ n ih =>
    simp only [gridProfile,List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨j,le_rfl,by omega,rfl⟩
    · obtain ⟨i,hi,hij,rfl⟩ := ih hp
      exact ⟨i,by omega,by omega,rfl⟩

lemma gridProfile_pairwise {d : ℝ≥0} {f : ℕ → ℝ≥0} {j n : ℕ}
    (hm : ∀ i k, j ≤ i → i<k → k<j+n → f i ≤ f k) :
    (gridProfile d f j n).Pairwise (fun p q ↦ p.2 ≤ q.2) := by
  induction n generalizing j with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [gridProfile,List.pairwise_cons]
    constructor
    · intro q hq
      obtain ⟨i,hi,hij,rfl⟩ := gridProfile_mem hq
      exact hm j i le_rfl (by omega) (by omega)
    · exact ih (fun i k hi hik hk ↦ hm i k (by omega) hik (by omega))

lemma gridProfile_sample {d : ℝ≥0} {f : ℕ → ℝ≥0} {j n : ℕ}
    (hn : 0<n) {t : ℝ} (ht : t∈Icc (0 : ℝ) ((n : ℝ)*d)) :
    ∃ i, j ≤ i ∧ i<j+n ∧
      profileCoeff (gridProfile d f j n) t=(f i : ℝ) ∧
      0 ≤ (j : ℝ)*d+t-(i : ℝ)*d ∧ (j : ℝ)*d+t-(i : ℝ)*d ≤ d := by
  induction n generalizing j t with
  | zero => omega
  | succ n ih =>
    by_cases htd : t ≤ (d : ℝ)
    · refine ⟨j,le_rfl,by omega,?_,?_,?_⟩
      · exact patchTime_left _ _ htd
      · linarith [ht.1]
      · linarith
    · have hd : (d : ℝ)<t := lt_of_not_ge htd
      have hn' : 0<n := by
        by_contra hh
        have hn0 : n=0 := by omega
        subst n
        simp only [Nat.cast_one,zero_add,one_mul] at ht
        exact htd ht.2
      have ht' : t-(d : ℝ)∈Icc (0 : ℝ) ((n : ℝ)*d) := by
        constructor
        · linarith
        · have hu := ht.2
          rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul] at hu
          linarith
      obtain ⟨i,hij,hin,hc,hlo,hhi⟩ := ih hn' ht' (j := j+1)
      refine ⟨i,by omega,by omega,?_,?_,?_⟩
      · change patchTime (d : ℝ) _ _ t=_
        rw [patchTime_right _ _ hd]
        exact hc
      · simp only [Nat.cast_add,Nat.cast_one] at hlo
        nlinarith
      · simp only [Nat.cast_add,Nat.cast_one] at hhi
        nlinarith

noncomputable def gridDelta (n : ℕ) : ℝ≥0 := ⟨1/(n+1 : ℝ),by positivity⟩

lemma gridDelta_coe (n : ℕ) : (gridDelta n : ℝ)=1/(n+1 : ℝ) := rfl

noncomputable def OrderParameter.grid (γ : OrderParameter) (n : ℕ) : HeatProfile :=
  gridProfile (gridDelta n)
    (fun i ↦ (γ.coeff ((i : ℝ)/(n+1 : ℝ))).toNNReal) 0 (n+1)

lemma OrderParameter.grid_time (γ : OrderParameter) (n : ℕ) : profileTime (γ.grid n)=1 := by
  rw [OrderParameter.grid,gridProfile_time]
  simp only [gridDelta_coe,Nat.cast_add,Nat.cast_one]
  field_simp

lemma OrderParameter.grid_mono (γ : OrderParameter) (n : ℕ) :
    (γ.grid n).Pairwise (fun p q ↦ p.2 ≤ q.2) := by
  apply gridProfile_pairwise
  intro i k hi hik hk
  apply Real.toNNReal_mono
  apply γ.monotone
  · exact ⟨by positivity,(div_lt_one (by positivity)).mpr (by exact_mod_cast (lt_trans hik (by simpa using hk)))⟩
  · exact ⟨by positivity,(div_lt_one (by positivity)).mpr (by exact_mod_cast (show k<n+1 by simpa using hk))⟩
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hik.le) (by positivity)

lemma OrderParameter.grid_sample (γ : OrderParameter) (n : ℕ) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) : ∃ r∈Ico (0 : ℝ) 1,
      profileCoeff (γ.grid n) t=γ.coeff r ∧ r ≤ t ∧ t-r ≤ 1/(n+1 : ℝ) := by
  have hnd : ((n+1 : ℕ) : ℝ)*(gridDelta n : ℝ≥0)=1 := by
    simp only [gridDelta_coe,Nat.cast_add,Nat.cast_one]; field_simp
  obtain ⟨i,hi,hin,hc,hlo,hhi⟩ := gridProfile_sample (d := gridDelta n)
    (f := fun i ↦ (γ.coeff ((i : ℝ)/(n+1 : ℝ))).toNNReal) (j := 0)
    (Nat.succ_pos n) (t := t) (by simpa only [hnd] using ht)
  have hr : (i : ℝ)/(n+1 : ℝ)∈Ico (0 : ℝ) 1 :=
    ⟨by positivity,(div_lt_one (by positivity)).mpr (by exact_mod_cast (show i<n+1 by simpa using hin))⟩
  refine ⟨(i : ℝ)/(n+1 : ℝ),hr,?_,?_,?_⟩
  · simpa only [OrderParameter.grid,Real.coe_toNNReal _ (γ.nonneg _ hr)] using hc
  · simp only [Nat.cast_zero,zero_mul,zero_add,gridDelta_coe] at hlo
    rw [mul_one_div] at hlo
    linarith
  · simpa only [Nat.cast_zero,zero_mul,zero_add,gridDelta_coe,mul_one_div,zero_div,zero_add] using hhi

lemma OrderParameter.grid_le (γ : OrderParameter) (n : ℕ) {t : ℝ}
    (ht : t∈Ico (0 : ℝ) 1) : profileCoeff (γ.grid n) t ≤ γ.coeff t := by
  obtain ⟨r,hr,hc,hrt,_⟩ := γ.grid_sample n ⟨ht.1,ht.2.le⟩
  rw [hc]
  exact γ.monotone hr ht hrt

end SKValue

end

end OAI
