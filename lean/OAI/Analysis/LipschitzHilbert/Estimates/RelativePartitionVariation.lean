import OAI.Analysis.LipschitzHilbert.Estimates.RelativeExitEnergy

namespace OAI

/-! Finite partitions are dominated by the summed quadratic relative-exit energies. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert
variable {Ω : Type*}

theorem relative_partition_cube_bound (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω)
    (p : Fin (N+1) → Fin (N+1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) x-F (p i.castSucc) x‖^3) ≤
      2048*runningOscillation F N x*weightedRelativeExitEnergy F (N+1) x := by
  classical
  let d := fun i : Fin N => ‖F (p i.succ) x-F (p i.castSucc) x‖
  let s : Finset (Fin N) := Finset.univ.filter (fun i => 0<d i)
  have he (i : Fin N) (hi : i∈s) : ∃ q : ℕ × Fin (N+1),
      (p i.castSucc).val<relativeExitTimes F (relativeExitScale q.1) (N+1) (q.2.val+1) x ∧
      relativeExitTimes F (relativeExitScale q.1) (N+1) (q.2.val+1) x ≤ (p i.succ).val ∧
      d i^3 ≤ 2048*runningOscillation F N x*(relativeExitScale q.1*
        ‖F (relativeExitTimes F (relativeExitScale q.1) (N+1) (q.2.val+1) x) x-
          F (relativeExitTimes F (relativeExitScale q.1) (N+1) q.2.val x) x‖^2) := by
    have hd : 0<d i := (Finset.mem_filter.mp hi).2
    obtain ⟨m,j,hj,hl,hb,hv⟩ := relative_interval_scale F (N+1) (p i.castSucc) (p i.succ)
      (p i.succ).isLt (hp (show i.castSucc  ≤  i.succ by change i.val ≤ i.val+1; omega)) x hd
    refine ⟨(m,⟨j,hj⟩),hl,hb,?_⟩
    have hrad := runningOscillation_mono F (Nat.le_of_lt_succ (p i.succ).isLt) x
    have hs := relativeExitScale_pos m
    have hn := sq_nonneg ‖F (relativeExitTimes F (relativeExitScale m) (N+1) (j+1) x) x-
      F (relativeExitTimes F (relativeExitScale m) (N+1) j x) x‖
    calc
      _  ≤  _ := hv
      _ = (2048*relativeExitScale m*
          ‖F (relativeExitTimes F (relativeExitScale m) (N+1) (j+1) x) x-
            F (relativeExitTimes F (relativeExitScale m) (N+1) j x) x‖^2)*
              runningOscillation F (p i.succ) x := by ring
      _  ≤  (2048*relativeExitScale m*
          ‖F (relativeExitTimes F (relativeExitScale m) (N+1) (j+1) x) x-
            F (relativeExitTimes F (relativeExitScale m) (N+1) j x) x‖^2)*
              runningOscillation F N x := mul_le_mul_of_nonneg_left hrad (by positivity)
      _ = _ := by ring
  let q : Fin N → ℕ × Fin (N+1) := fun i => if hi : i∈s then Classical.choose (he i hi) else (0,0)
  have hq (i : Fin N) (hi : i∈s) := Classical.choose_spec (he i hi)
  have hqp (i : Fin N) (hi : i∈s) :
      (p i.castSucc).val<relativeExitTimes F (relativeExitScale (q i).1) (N+1) ((q i).2.val+1) x ∧
      relativeExitTimes F (relativeExitScale (q i).1) (N+1) ((q i).2.val+1) x ≤ (p i.succ).val ∧
      d i^3 ≤ 2048*runningOscillation F N x*(relativeExitScale (q i).1*
        ‖F (relativeExitTimes F (relativeExitScale (q i).1) (N+1) ((q i).2.val+1) x) x-
          F (relativeExitTimes F (relativeExitScale (q i).1) (N+1) (q i).2.val x) x‖^2) := by
    simpa only [q,dite_eq_left hi] using hq i hi
  have horder (i k : Fin N) (hik : i<k) : (p i.succ).val ≤ (p k.castSucc).val :=
    hp (show i.succ ≤ k.castSucc by change i.val+1 ≤ k.val; exact hik)
  have hqinj : Set.InjOn q s := by
    intro i hi k hk heq
    rcases lt_trichotomy i k with hik | hik | hki
    · have h1 := (hqp i hi).2.1
      have h2 := (hqp k hk).1
      rw [←heq] at h2
      have h3 := horder i k hik
      omega
    · exact hik
    · have h1 := (hqp k hk).2.1
      have h2 := (hqp i hi).1
      rw [heq] at h2
      have h3 := horder k i hki
      omega
  let M := s.sup (fun i => (q i).1)+1
  let w := fun z : ℕ × Fin (N+1) => relativeExitScale z.1*
    ‖F (relativeExitTimes F (relativeExitScale z.1) (N+1) (z.2.val+1) x) x-
      F (relativeExitTimes F (relativeExitScale z.1) (N+1) z.2.val x) x‖^2
  have hsum : (∑ i∈s,d i^3) ≤
      ∑ z∈(Finset.range M).product Finset.univ, 2048*runningOscillation F N x*w z := by
    apply Finset.sum_le_sum_of_injOn q hqinj
    · intro z hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      rw [Finset.product_eq_sprod]
      simp only [Finset.mem_product,Finset.mem_range,Finset.mem_univ,and_true]
      exact Nat.lt_succ_of_le (Finset.le_sup (f:=fun i => (q i).1) hi)
    · exact fun i hi => (hqp i hi).2.2
    · intro z _ _
      exact mul_nonneg (mul_nonneg (by norm_num) (runningOscillation_nonneg F N x))
        (mul_nonneg (relativeExitScale_pos z.1).le (sq_nonneg _))
  have hsumeq : (∑ i∈s, d i^3)=∑ i : Fin N,d i^3 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hd : ¬0<d i := by simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    have hdn : 0 ≤ d i := norm_nonneg _
    have : d i=0 := le_antisymm (le_of_not_gt hd) hdn
    simp only [this,zero_pow (by decide : 3≠0)]
  rw [hsumeq] at hsum
  calc
    _  ≤  _ := hsum
    _ = 2048*runningOscillation F N x*
        (∑ m∈Finset.range M, relativeExitScale m*relativeExitEnergy F (relativeExitScale m) (N+1) x) := by
      rw [Finset.product_eq_sprod,Finset.sum_product]
      simp only [w,relativeExitEnergy,←Finset.mul_sum]
    _  ≤  _ := mul_le_mul_of_nonneg_left
      ((relativeExitEnergy_summable F (N+1) x).sum_le_tsum (Finset.range M)
        (fun m _ => mul_nonneg (relativeExitScale_pos m).le (relativeExitEnergy_nonneg F _ _ x)))
      (mul_nonneg (by norm_num) (runningOscillation_nonneg F N x))

end LipschitzHilbert

end

end OAI
