import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseCountRun
import OAI.Combinatorics.KMedian.Compression.RationalOperationHeight

namespace OAI


                                      
section
namespace MetricKMedian.SparseCounts
open Binary
variable {n m : ℕ}

theorem edge_height (G : Table n m) (H : ℕ) (hG : ∀ i h, G i h≤2^H)
    (h : Fin n) (i : Fin m) : HasHeight (edge G h i) H := by
  constructor
  · simpa only [edge,Rat.num_natCast,abs_of_nonneg (Nat.cast_nonneg _ : (0:ℤ)≤((G i h:ℕ):ℤ)),Nat.cast_pow,Nat.cast_ofNat]
      using (Nat.cast_le (α:=ℤ)).mpr (hG i h)
  · simp only [edge,Rat.den_natCast,Nat.cast_one]
    exact one_le_pow₀ (by norm_num)

theorem features_height (G : Table n m) (H : ℕ) (hG : ∀ i h, G i h≤2^H)
    (a : Fin (n*m+(n*m)*(n*m))) : HasHeight (features G a) (H+H) := by
  unfold features edgeCode
  generalize finSumFinEquiv.symm a=z
  cases z with
  | inl i => exact (edge_height _ _ hG _ _).mono (Nat.le_add_right _ _)
  | inr ij => exact (edge_height _ _ hG _ _).mul (edge_height _ _ hG _ _)

theorem next_bound (G : Table n m) (S : Fin n → ℕ) (i : Fin m) (U : ℕ)
    (hG : ∀ j h,G j h≤U) (hS : ∀ h,S h≤U) : ∀ j h,next G S i j h≤U := by
  intro j h
  by_cases hj : j=i
  · subst j; simpa only [next,Function.update_self] using hS h
  · simpa only [next,Function.update_of_ne hj] using hG j h

theorem run_bound (ν : Fin m → SparseIntegerLaw (Fin n → ℕ)) (U : ℕ)
    (hν : ∀ i, ∀ a : Fin (ν i).length, ∀ h, (ν i).states[a.val] h≤U) (t : ℕ) :
    ∀ a : Fin (run ν t).length, ∀ i h,(run ν t).states[a.val] i h≤U := by
  induction t with
  | zero =>
    intro a i h
    change (Vector.replicate 1 (fun _ : Fin m => fun _ : Fin n => (0:ℕ)))[a.val] i h≤U
    simp only [Vector.getElem_replicate]
    exact Nat.zero_le _
  | succ t ih =>
    let P := fun μ : SparseIntegerLaw (Table n m) => ∀ a : Fin μ.length, ∀ i h,μ.states[a.val] i h≤U
    change P (run ν (t+1))
    rw [run]
    split_ifs with ht
    · intro a i h
      obtain ⟨j,k,hjk⟩ := ((run ν t).prodCompress_spec (ν ⟨t,ht⟩)
        (fun G S => next G S ⟨t,ht⟩) features).2.1 a
      change (step (run ν t) (ν ⟨t,ht⟩) ⟨t,ht⟩).states[a.val]=_ at hjk
      rw [hjk]
      exact next_bound _ _ _ U (ih j) (hν _ k) i h
    · exact ih

def stepHeight (n m N L H : ℕ) :=
  let d := n*m+(n*m)*(n*m)
  L+((2*(d+1)*(d+1+(H+H)*((d+1)*N+1)))*((d+1)*N+1))*((d+1)*N)

theorem denominator_height (ν : Fin m → SparseIntegerLaw (Fin n → ℕ)) (N L H : ℕ)
    (hN : ∀ i, (ν i).length≤N) (hL : ∀ i, (ν i).law.denominator≤(2:ℤ)^L)
    (hν : ∀ i, ∀ a : Fin (ν i).length, ∀ h, (ν i).states[a.val] h≤2^H) (t : ℕ) :
    (run ν t).law.denominator≤(2:ℤ)^(stepHeight n m N L H*t) := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac]
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · rw [dite_eq_left ht]
      let μ := run ν t
      let ρ := μ.prod (ν ⟨t,ht⟩) (fun G S => next G S ⟨t,ht⟩)
      have hr : ∀ a : Fin ρ.length, ∀ i h,ρ.states[a.val] i h≤2^H := by
        apply SparseIntegerLaw.prod_property μ (ν ⟨t,ht⟩) (fun G S => next G S ⟨t,ht⟩) (fun G => ∀ i h,G i h≤2^H)
        intro a b
        exact next_bound _ _ _ _ (run_bound ν _ hν t a) (hν _ b)
      have hc := ρ.compressAuto_denominator features (H+H)
        (fun i a => (features_height ρ.states[i.val] H (hr i) a).1)
        (fun i a => (features_height ρ.states[i.val] H (hr i) a).2)
      have hrD : ρ.law.denominator=μ.law.denominator*(ν ⟨t,ht⟩).law.denominator := rfl
      have hrN : ρ.length ≤ (n*m+(n*m)*(n*m)+1)*N :=
        Nat.mul_le_mul (run_length ν t) (hN _)
      change (ρ.compressAuto features).law.denominator≤_
      apply hc.trans
      rw [hrD]
      calc
        _ ≤ ((2:ℤ)^(stepHeight n m N L H*t)*(2:ℤ)^L)*
            (2:ℤ)^((2*(n*m+(n*m)*(n*m)+1)*(n*m+(n*m)*(n*m)+1+
              (H+H)*((n*m+(n*m)*(n*m)+1)*N+1)))*
              ((n*m+(n*m)*(n*m)+1)*N+1)*((n*m+(n*m)*(n*m)+1)*N)) := by
          gcongr
          · exact (ν ⟨t,ht⟩).law.denominator_pos.le
          · exact hL _
          · norm_num
        _ = _ := by rw [← pow_add,← pow_add]; congr 1; simp only [stepHeight]; ring
    · rw [dite_eq_right ht]
      exact ih.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_succ t)))
end MetricKMedian.SparseCounts
end

end OAI
