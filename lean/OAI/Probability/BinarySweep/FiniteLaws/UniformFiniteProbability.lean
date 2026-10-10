import Mathlib
import OAI.Probability.BinarySweep.Trajectories.Trajectory
import OAI.Probability.BinarySweep.Trajectories.SharingProbability

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {Ω V W : Type*} [Fintype Ω] [Fintype V] [Fintype W]

 def uniformWeight (_u : Ω) : ℝ := 1 / Fintype.card Ω

lemma uniformWeight_nonneg (u : Ω) : 0 ≤ uniformWeight u := by
  unfold uniformWeight; positivity

lemma uniformWeight_sum [Nonempty Ω] : ∑ u : Ω, uniformWeight u = 1 := by
  simp [uniformWeight,ne_of_gt (Fintype.card_pos : 0 < Fintype.card Ω)]

def finiteProbability (p : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  ∑ u, p u * (if E u then 1 else 0)

lemma finiteProbability_union {T : Type*} [Fintype T]
    (p : Ω → ℝ) (hp : ∀ u, 0 ≤ p u) (E : T → Ω → Prop) :
    finiteProbability p (fun u => ∃ t, E t u) ≤ ∑ t, finiteProbability p (E t) := by
  unfold finiteProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro u _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hp u)
  by_cases h : ∃ t, E t u
  · obtain ⟨t,ht⟩ := h
    rw [ite_eq_left ⟨t,ht⟩]
    exact (show (1:ℝ) ≤ if E t u then 1 else 0 by simp [ht]).trans
      (Finset.single_le_sum (f:=fun t:T => if E t u then (1:ℝ) else 0)
        (fun t _ => by split_ifs <;> norm_num) (Finset.mem_univ t))
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun t _ => by split_ifs <;> norm_num)

lemma uniform_projection_probability [Nonempty W] (e : Ω ≃ V × W) (v : V) :
    finiteProbability uniformWeight (fun u => (e u).1 = v) = 1 / Fintype.card V := by
  classical
  unfold finiteProbability uniformWeight
  rw [← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type,Fintype.card_congr e,Fintype.card_prod]
  have hW : (Fintype.card W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  simp [Nat.cast_mul]

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
namespace Sparse
variable {b : ℕ} {bits : Fin b → ℕ}

def independentPosition (z : GridSlot bits × GridSlot bits) (t : Fin (b+1)) : GridSlot bits :=
  fun i => if i.val<t.val then z.2 i else z.1 i

lemma independentPosition_changes (z : GridSlot bits × GridSlot bits) (j i : Fin b) (h : i≠j) :
    independentPosition z j.succ i=independentPosition z j.castSucc i := by
  have hn : i.val≠j.val := fun he => h (Fin.ext he)
  simp only [independentPosition,Fin.val_succ,Fin.val_castSucc]
  have he : i.val<j.val+1 ↔ i.val<j.val := by omega
  simp only [he]

lemma independentPosition_of_path (x : Fin (b+1) → GridSlot bits)
    (h : ∀(j i : Fin b), i≠j → x j.succ i=x j.castSucc i) (t : Fin (b+1)) :
    independentPosition (x 0,x (Fin.last b)) t=x t := by
  funext i
  exact (trajectory_coordinates x h t i).symm

def endpointSwap (t : Fin (b+1)) :
    (GridSlot bits × GridSlot bits) ≃ GridSlot bits × GridSlot bits where
  toFun z := (independentPosition z t,independentPosition (z.2,z.1) t)
  invFun z := (independentPosition z t,independentPosition (z.2,z.1) t)
  left_inv z := by
    apply Prod.ext <;> funext i <;> dsimp [independentPosition] <;> split <;> rfl
  right_inv z := by
    apply Prod.ext <;> funext i <;> dsimp [independentPosition] <;> split <;> rfl

lemma independentPosition_uniform (t : Fin (b+1)) (v : GridSlot bits) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits =>
      independentPosition z t=v)=1/gridSize bits := by
  have hh := uniform_projection_probability (endpointSwap (bits:=bits) t) v
  convert hh using 1 <;> simp only [endpointSwap,Equiv.coe_fn_mk,card_gridSlot]

def shareVertex (z w : GridSlot bits × GridSlot bits) : Prop :=
  ∃t : Fin (b+1), independentPosition z t=independentPosition w t

lemma shareVertex_symmetric :
    ∀ ⦃first second⦄, shareVertex (bits:=bits) first second → shareVertex second first := by
  rintro z w ⟨t,ht⟩
  exact ⟨t,ht.symm⟩

lemma shareVertex_probability (w : GridSlot bits × GridSlot bits) :
    finiteProbability uniformWeight (fun z => shareVertex (bits:=bits) z w) ≤
      (b+1:ℝ)/gridSize bits := by
  have hh := finiteProbability_union uniformWeight uniformWeight_nonneg
    (fun (t : Fin (b+1)) (z : GridSlot bits × GridSlot bits) =>
      independentPosition z t=independentPosition w t)
  simp_rw [independentPosition_uniform] at hh
  simpa only [shareVertex,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one,mul_one_div] using hh

theorem independent_trajectory_sharing {k h : ℕ}
    (roots : Fin h → GridSlot bits × GridSlot bits) (w : ℕ)
    (hs : ((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits) ≤ 1) :
    productProbability uniformWeight (fun z : Fin k → GridSlot bits × GridSlot bits =>
      w ≤ (incidentSet shareVertex roots z).card) ≤
      (2:ℝ)^k * (((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits))^((w+1)/2) := by
  have hh := sharing_probability_le (I:=Fin k) uniformWeight uniformWeight_nonneg uniformWeight_sum
    shareVertex shareVertex_symmetric roots ((b+1:ℝ)/gridSize bits) (by positivity)
    (fun v => shareVertex_probability v) w (by simpa only [Fintype.card_fin] using hs)
  simpa only [Fintype.card_fin] using hh

def endpointLineEquiv (j : Fin b) :
    (GridSlot bits × GridSlot bits) ≃
      GridOutside bits j × (Slot (bits j) × GridSlot bits) :=
  (endpointSwap j.castSucc).trans
    (((Equiv.piSplitAt j (fun i : Fin b => Slot (bits i))).trans (Equiv.prodComm _ _)).prodCongr
      (Equiv.refl _)) |>.trans (Equiv.prodAssoc _ _ _)

lemma independent_line_uniform (j : Fin b) (y : GridOutside bits j) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits =>
      (fun i : {i : Fin b // i≠j} => independentPosition z j.castSucc i)=y)=
      1/Fintype.card (GridOutside bits j) := by
  exact uniform_projection_probability (endpointLineEquiv j) y

lemma finiteProbability_mem {Ω L : Type*} [Fintype Ω] [Fintype L] [DecidableEq L]
    (p : Ω → ℝ) (f : Ω → L) (S : Finset L) :
    finiteProbability p (fun u => f u∈S)=∑l∈S, finiteProbability p (fun u => f u=l) := by
  unfold finiteProbability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.mul_sum]
  congr 1
  simp only [eq_comm,Finset.sum_ite_eq']
  by_cases h : f u∈S <;> simp only [h,ite_true,ite_false]

lemma independent_line_set_uniform (j : Fin b) (S : Finset (GridOutside bits j)) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits =>
      (fun i : {i : Fin b // i≠j} => independentPosition z j.castSucc i)∈S)=
      S.card/Fintype.card (GridOutside bits j) := by
  rw [finiteProbability_mem]
  simp_rw [independent_line_uniform]
  simp [div_eq_mul_inv]

end Sparse
end BinaryCoordinateSweeps

end

end OAI
