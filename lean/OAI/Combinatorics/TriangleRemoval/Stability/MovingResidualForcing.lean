import Mathlib
import OAI.Combinatorics.TriangleRemoval.Stability.MovingPerturbationFiniteExpansion
import OAI.Combinatorics.TriangleRemoval.Asymptotics.ActiveL2Map

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave
open Classical

lemma moving_active_subset {E : Type*} (active : ℕ → Finset E) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ T) :
    active j ⊆ active i := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ k hik ih => exact (hnest k (by omega)).trans (ih (by omega))

lemma activeLinf_mono {E : Type*} [Fintype E] {s t : Finset E} (h : s ⊆ t) (x : E → ℝ) :
    activeLinf s x ≤ activeLinf t x :=
  activeLinf_bound s x (apply_nonneg _ _) (fun _ he => activeLinf_coordinate t x (h he))

noncomputable def movingResidualForcing {E : Type*} [Fintype E]
    (a : ℕ → ℝ) (R : ℕ → Module.End ℝ (E → ℝ)) : Module.End ℝ (ℕ → E → ℝ) where
  toFun x t := ∑ i ∈ Finset.range t, (-a i) • (R i (x i))
  map_add' x y := by
    funext t
    simp only [Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib]
  map_smul' c x := by
    funext t
    simp only [Pi.smul_apply,map_smul,smul_comm (-a _) c,Finset.smul_sum,RingHom.id_apply]

lemma movingResidualForcing_zero {E : Type*} [Fintype E]
    (a : ℕ → ℝ) (R : ℕ → Module.End ℝ (E → ℝ)) (x : ℕ → E → ℝ) :
    movingResidualForcing a R x 0 = 0 := by simp [movingResidualForcing]

lemma movingResidualForcing_succ {E : Type*} [Fintype E]
    (a : ℕ → ℝ) (R : ℕ → Module.End ℝ (E → ℝ)) (x : ℕ → E → ℝ) (t : ℕ) :
    movingResidualForcing a R x (t+1) = movingResidualForcing a R x t-a t • R t (x t) := by
  simp [movingResidualForcing,Finset.sum_range_succ,sub_eq_add_neg,add_comm]

lemma movingResidualForcing_bound {E : Type*} [Fintype E]
    (P : ℕ → Seminorm ℝ (E → ℝ)) (a : ℕ → ℝ) (R : ℕ → Module.End ℝ (E → ℝ))
    (T : ℕ) (ha : ∀ i < T, 0 ≤ a i)
    (hmono : ∀ i j, i ≤ j → j ≤ T → ∀ x, P j x ≤ P i x)
    {B : ℝ} (hB : 0 ≤ B) (hR : ∀ i < T, ∀ x, P i (R i x) ≤ B*P i x)
    (x : ℕ → E → ℝ) :
    trajectorySeminorm P T (movingResidualForcing a R x) ≤
      (∑ i ∈ Finset.range T, a i)*B*trajectorySeminorm P T x := by
  have hS : 0 ≤ ∑ i ∈ Finset.range T, a i :=
    Finset.sum_nonneg (fun i hi => ha i (Finset.mem_range.mp hi))
  have hx0 := apply_nonneg (trajectorySeminorm P T) x
  apply trajectorySeminorm_bound _ _ _ (by positivity)
  intro t ht
  change P t (∑ i ∈ Finset.range t, (-a i) • R i (x i)) ≤ _
  calc
    _ ≤ ∑ i ∈ Finset.range t, P t ((-a i) • R i (x i)) := seminorm_finset_sum_le _ _ _
    _ ≤ ∑ i ∈ Finset.range t, a i*(B*trajectorySeminorm P T x) := by
      apply Finset.sum_le_sum
      intro i hi
      have hit : i < t := Finset.mem_range.mp hi
      have hiT : i < T := by omega
      rw [map_smul_eq_mul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (ha i hiT)]
      apply mul_le_mul_of_nonneg_left _ (ha i hiT)
      exact (hmono i t hit.le ht _).trans ((hR i hiT _).trans
        (mul_le_mul_of_nonneg_left (trajectorySeminorm_at P T x (by omega)) hB))
    _ ≤ ∑ i ∈ Finset.range T, a i*(B*trajectorySeminorm P T x) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht)
        (fun i hi _ => mul_nonneg (ha i (Finset.mem_range.mp hi)) (mul_nonneg hB hx0))
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma movingStar_actual_response {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ)
    (R : ℕ → Module.End ℝ (E → ℝ)) (M x : ℕ → E → ℝ) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (hinit : ∀ e ∈ active 0, x 0 e = M 0 e)
    (hstep : ∀ k < T, ∀ e ∈ active (k+1), x (k+1) e = x k e -
      a k*(movingStarLift ends (movingStarMean ends (active k) (x k)) e+R k (x k) e) +
        (M (k+1) e-M k e)) :
    trajectorySeminorm (fun t => activeLinf (active t)) T
      (x-movingStarResponse ends active a M-
        movingStarResponse ends active a (movingResidualForcing a R x)) = 0 := by
  let F := M+movingResidualForcing a R x
  have hi : ∀ e ∈ active 0, x 0 e = F 0 e := by
    intro e he
    simp only [F,Pi.add_apply,movingResidualForcing_zero,Pi.zero_apply,add_zero]
    exact hinit e he
  have hs : ∀ k < T, ∀ e ∈ active (k+1), x (k+1) e = x k e -
      a k*movingStarLift ends (movingStarMean ends (active k) (x k)) e + (F (k+1) e-F k e) := by
    intro k hk e he
    rw [hstep k hk e he]
    simp only [F,Pi.add_apply,movingResidualForcing_succ,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  apply le_antisymm _ (apply_nonneg _ _)
  apply trajectorySeminorm_bound _ _ _ le_rfl
  intro t ht
  apply activeLinf_bound _ _ le_rfl
  intro e he
  have h₁ := movingStar_trajectory_representation ends active a F x t
    (fun k hk => hnest k (by omega)) hi (fun k hk => hs k (by omega)) e he
  have h₂ := movingStar_trajectory_representation ends active a F
    (movingStarSolve ends active a F) t (fun k hk => hnest k (by omega))
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) e he
  have h_eq : x t e = movingStarResponse ends active a F t e := h₁.trans h₂.symm
  change |x t e-movingStarResponse ends active a M t e-
    movingStarResponse ends active a (movingResidualForcing a R x) t e| ≤ 0
  have hadd := congrFun (congrFun (map_add (movingStarResponse ends active a)
    M (movingResidualForcing a R x)) t) e
  change movingStarResponse ends active a F t e = _ at hadd
  rw [h_eq,hadd]
  simp

theorem movingStar_mixed_stability {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : ℕ → Finset E) (a : ℕ → ℝ) (R : ℕ → Module.End ℝ (E → ℝ))
    (M x : ℕ → E → ℝ) (T K : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (ha : ∀ k < T, 0 ≤ a k ∧ a k ≤ 1)
    (hinit : ∀ e ∈ active 0, x 0 e = M 0 e)
    (hstep : ∀ k < T, ∀ e ∈ active (k+1), x (k+1) e = x k e -
      a k*(movingStarLift ends (movingStarMean ends (active k) (x k)) e+R k (x k) e) +
        (M (k+1) e-M k e))
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hRinf : ∀ k < T, ∀ z, activeLinf (active k) (R k z) ≤ B*activeLinf (active k) z)
    (hR₂ : ∀ k < T, ∀ z, activeL2 (active k) (R k z) ≤ δ*activeL2 (active k) z)
    (hK : ((1+2*∑ k ∈ Finset.range T, a k)*(∑ k ∈ Finset.range T, a k)*δ)^K*
      (Fintype.card E : ℝ) ≤ 1/2) :
    trajectorySeminorm (fun t => activeLinf (active t)) T x ≤
      2*(∑ j ∈ Finset.range K,
        ((1+2*∑ k ∈ Finset.range T, a k)*(∑ k ∈ Finset.range T, a k)*B)^j)*
        (1+2*∑ k ∈ Finset.range T, a k)*trajectorySeminorm (fun t => activeLinf (active t)) T M := by
  let p := trajectorySeminorm (fun t => activeLinf (active t)) T
  let q := trajectorySeminorm (fun t => activeL2 (active t)) T
  let V₁ := (movingStarResponse ends active a).comp (movingResidualForcing a R)
  let S := ∑ k ∈ Finset.range T, a k
  let L := 1+2*S
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k hk => (ha k (Finset.mem_range.mp hk)).1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hVp : ∀ z, p (V₁ z) ≤ L*S*B*p z := by
    intro z
    have hb := movingStarResponse_linf ends hends active a T hnest ha (movingResidualForcing a R z)
    have hf := movingResidualForcing_bound (fun t => activeLinf (active t)) a R T
      (fun k hk => (ha k hk).1)
      (fun i j hij hj z => activeLinf_mono (moving_active_subset active T hnest hij hj) z) hB hRinf z
    exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hf hL)
  have hVq : ∀ z, q (V₁ z) ≤ L*S*δ*q z := by
    intro z
    have hb := movingStarResponse_l2 ends hends active a T hnest ha (movingResidualForcing a R z)
    have hf := movingResidualForcing_bound (fun t => activeL2 (active t)) a R T
      (fun k hk => (ha k hk).1)
      (fun i j hij hj z => activeL2_mono (moving_active_subset active T hnest hij hj) z) hδ hR₂ z
    exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hf hL)
  have hb := moving_perturbation_mixed_norm_absorb_modulo p q V₁ x
    (movingStarResponse ends active a M) (by positivity : 0 ≤ L*S*B) (by positivity : 0 ≤ L*S*δ)
    hVp hVq (fun z => (trajectory_mixed_seminorms active T z).1)
    (fun z => (trajectory_mixed_seminorms active T z).2)
    (movingStar_actual_response ends active a R M x T hnest hinit hstep) K hK
  have hy := movingStarResponse_linf ends hends active a T hnest ha M
  apply hb.trans
  calc
    _ ≤ 2*(∑ j ∈ Finset.range K, (L*S*B)^j)*(L*p M) :=
      mul_le_mul_of_nonneg_left hy (by positivity)
    _ = _ := by dsimp only [p,L,S]; ring

end SharpTerminalLeave
end
end

end OAI
