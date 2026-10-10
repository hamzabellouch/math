import Mathlib

namespace OAI

section
open scoped BigOperators

namespace SharpTerminalLeave

open Classical

private lemma moving_abs_sub_bound (x y : ℝ) : |x-y| ≤ |x|+|y| := by
  simpa using (abs_sub_le x 0 y)

noncomputable def movingStarDegree {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (u : V) : ℝ := by
  classical
  exact ((active.filter (fun e => u ∈ ends e)).card : ℝ)

noncomputable def movingStarMean {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (x : E → ℝ) (u : V) : ℝ := by
  classical
  exact (∑ e ∈ active.filter (fun e => u ∈ ends e), x e) / movingStarDegree ends active u

noncomputable def movingStarLift {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (b : V → ℝ) (e : E) : ℝ := ∑ u ∈ ends e, b u

noncomputable def movingStarOtherMean {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (b : V → ℝ) (u : V) : ℝ := by
  classical
  exact (∑ e ∈ active.filter (fun e => u ∈ ends e), ∑ v ∈ (ends e).erase u, b v) /
    movingStarDegree ends active u

lemma movingStarDegree_nonneg {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (u : V) :
    0 ≤ movingStarDegree ends active u := Nat.cast_nonneg _

lemma movingStarMean_congr {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) {x y : E → ℝ}
    (h : ∀ e ∈ active, x e = y e) : movingStarMean ends active x = movingStarMean ends active y := by
  classical
  funext u
  unfold movingStarMean
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  exact h e (Finset.mem_filter.mp he).1

lemma movingStarMean_sub {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (x y : E → ℝ) (u : V) :
    movingStarMean ends active (fun e => x e-y e) u =
      movingStarMean ends active x u-movingStarMean ends active y u := by
  classical
  simp only [movingStarMean,Finset.sum_sub_distrib,sub_div]

lemma movingStarMean_zero_degree {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (x : E → ℝ) (u : V)
    (hd : movingStarDegree ends active u = 0) : movingStarMean ends active x u = 0 := by
  simp [movingStarMean,hd]

lemma movingStarMean_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (x : E → ℝ) (u : V)
    {M : ℝ} (hM : 0 ≤ M) (hx : ∀ e ∈ active, |x e| ≤ M) :
    |movingStarMean ends active x u| ≤ M := by
  classical
  by_cases hd : movingStarDegree ends active u = 0
  · simpa [movingStarMean_zero_degree ends active x u hd] using hM
  · have hp : 0 < movingStarDegree ends active u :=
      lt_of_le_of_ne (movingStarDegree_nonneg ends active u) (Ne.symm hd)
    unfold movingStarMean
    rw [abs_div,abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    calc
      _ ≤ ∑ e ∈ active.filter (fun e => u ∈ ends e), |x e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ active.filter (fun e => u ∈ ends e), M := by
        apply Finset.sum_le_sum
        intro e he
        exact hx e (Finset.mem_filter.mp he).1
      _ = _ := by simp [movingStarDegree,mul_comm]

lemma movingStarLift_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2) (b : V → ℝ)
    {B : ℝ} (hb : ∀ v, |b v| ≤ B) (e : E) : |movingStarLift ends b e| ≤ 2*B := by
  classical
  unfold movingStarLift
  calc
    _ ≤ ∑ v ∈ ends e, |b v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ ends e, B := Finset.sum_le_sum (fun v _ => hb v)
    _ = _ := by simp [hends]

lemma movingStarOtherMean_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2) (active : Finset E)
    (b : V → ℝ) (u : V) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ v, |b v| ≤ B) :
    |movingStarOtherMean ends active b u| ≤ B := by
  classical
  by_cases hd : movingStarDegree ends active u = 0
  · simpa [movingStarOtherMean,hd] using hB
  · have hp : 0 < movingStarDegree ends active u :=
      lt_of_le_of_ne (movingStarDegree_nonneg ends active u) (Ne.symm hd)
    unfold movingStarOtherMean
    rw [abs_div,abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    calc
      _ ≤ ∑ e ∈ active.filter (fun e => u ∈ ends e), |∑ v ∈ (ends e).erase u, b v| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ active.filter (fun e => u ∈ ends e), B := by
        apply Finset.sum_le_sum
        intro e he
        have hu := (Finset.mem_filter.mp he).2
        have hc : ((ends e).erase u).card = 1 := by
          rw [Finset.card_erase_of_mem hu,hends]
        calc
          _ ≤ ∑ v ∈ (ends e).erase u, |b v| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _v ∈ (ends e).erase u, B := Finset.sum_le_sum (fun v _ => hb v)
          _ = B := by simp [hc]
      _ = _ := by simp [movingStarDegree,mul_comm]

lemma movingStarMean_lift {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (b : V → ℝ) (u : V)
    (hd : movingStarDegree ends active u ≠ 0) :
    movingStarMean ends active (movingStarLift ends b) u =
      b u + movingStarOtherMean ends active b u := by
  classical
  have he : (∑ e ∈ active.filter (fun e => u ∈ ends e), movingStarLift ends b e) =
      movingStarDegree ends active u*b u +
      ∑ e ∈ active.filter (fun e => u ∈ ends e), ∑ v ∈ (ends e).erase u, b v := by
    calc
      _ = ∑ e ∈ active.filter (fun e => u ∈ ends e), (b u+∑ v ∈ (ends e).erase u, b v) := by
        apply Finset.sum_congr rfl
        intro e he
        exact (Finset.add_sum_erase _ b (Finset.mem_filter.mp he).2).symm
      _ = _ := by simp [Finset.sum_add_distrib,movingStarDegree]
  unfold movingStarMean movingStarOtherMean
  rw [he,add_div,mul_div_cancel_left₀ _ hd]

theorem movingStar_vertex_step_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2) (active : Finset E)
    (b : V → ℝ) (M : E → ℝ) {B R a : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : ∀ u, |b u| ≤ B)
    (hM : ∀ e ∈ active, |M e| ≤ R) (u : V) :
    |b u + a*movingStarMean ends active (fun e => M e-movingStarLift ends b e) u| ≤ B+a*R := by
  classical
  rw [movingStarMean_sub]
  by_cases hd : movingStarDegree ends active u = 0
  · rw [movingStarMean_zero_degree ends active M u hd,
      movingStarMean_zero_degree ends active (movingStarLift ends b) u hd]
    simp only [sub_self,mul_zero,add_zero]
    exact (hb u).trans (le_add_of_nonneg_right (mul_nonneg ha hR))
  · rw [movingStarMean_lift ends active b u hd]
    have hid : b u+a*(movingStarMean ends active M u-(b u+movingStarOtherMean ends active b u)) =
        (1-a)*b u-a*movingStarOtherMean ends active b u+a*movingStarMean ends active M u := by ring
    rw [hid]
    calc
      _ ≤ |(1-a)*b u-a*movingStarOtherMean ends active b u|+
          |a*movingStarMean ends active M u| := abs_add_le _ _
      _ ≤ (|(1-a)*b u|+|a*movingStarOtherMean ends active b u|)+
          |a*movingStarMean ends active M u| := by
        exact add_le_add (moving_abs_sub_bound _ _) le_rfl
      _ = ((1-a)*|b u|+a*|movingStarOtherMean ends active b u|)+
          a*|movingStarMean ends active M u| := by
        rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ha1),abs_of_nonneg ha]
      _ ≤ ((1-a)*B+a*B)+a*R := by
        gcongr
        · exact hb u
        · exact movingStarOtherMean_bound ends hends active b u hB hb
        · exact movingStarMean_bound ends active M u hR hM
      _ = _ := by ring

noncomputable def movingStarVertices {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ)
    (M : ℕ → E → ℝ) : ℕ → V → ℝ
  | 0 => fun _ => 0
  | k+1 => fun u => movingStarVertices ends active a M k u + a k *
      movingStarMean ends (active k)
        (fun e => M k e-movingStarLift ends (movingStarVertices ends active a M k) e) u

theorem movingStarVertices_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : ℕ → Finset E) (a : ℕ → ℝ) (M : ℕ → E → ℝ) (T : ℕ)
    {R : ℝ} (hR : 0 ≤ R) (ha : ∀ k < T, 0 ≤ a k ∧ a k ≤ 1)
    (hM : ∀ k < T, ∀ e ∈ active k, |M k e| ≤ R) :
    ∀ u, |movingStarVertices ends active a M T u| ≤ R*∑ k ∈ Finset.range T, a k := by
  induction T with
  | zero => intro u; simp [movingStarVertices]
  | succ T ih =>
    have haT := ha T (by omega)
    have hb := ih (fun k hk => ha k (by omega)) (fun k hk => hM k (by omega))
    have hB : 0 ≤ R*∑ k ∈ Finset.range T, a k := by
      exact mul_nonneg hR (Finset.sum_nonneg (fun k hk => (ha k (by have := Finset.mem_range.mp hk; omega)).1))
    intro u
    have hh := movingStar_vertex_step_bound ends hends (active T)
      (movingStarVertices ends active a M T) (M T) hB hR haT.1 haT.2 hb (hM T (by omega)) u
    simpa only [movingStarVertices,Finset.sum_range_succ,mul_add,mul_comm] using hh

theorem movingStar_trajectory_representation {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ)
    (M x : ℕ → E → ℝ) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (hinit : ∀ e ∈ active 0, x 0 e = M 0 e)
    (hstep : ∀ k < T, ∀ e ∈ active (k+1), x (k+1) e = x k e -
      a k*movingStarLift ends (movingStarMean ends (active k) (x k)) e + (M (k+1) e-M k e)) :
    ∀ e ∈ active T, x T e = M T e-movingStarLift ends (movingStarVertices ends active a M T) e := by
  induction T with
  | zero => intro e he; simpa [movingStarVertices,movingStarLift] using hinit e he
  | succ T ih =>
    have hx := ih (fun k hk => hnest k (by omega)) (fun k hk => hstep k (by omega))
    have hm := movingStarMean_congr ends (active T) hx
    intro e he
    rw [hstep T (by omega) e he,hx e (hnest T (by omega) he),hm]
    simp only [movingStarVertices,movingStarLift,Finset.sum_add_distrib,Finset.mul_sum]
    ring

theorem movingStar_trajectory_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : ℕ → Finset E) (a : ℕ → ℝ) (M x : ℕ → E → ℝ) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (hinit : ∀ e ∈ active 0, x 0 e = M 0 e)
    (hstep : ∀ k < T, ∀ e ∈ active (k+1), x (k+1) e = x k e -
      a k*movingStarLift ends (movingStarMean ends (active k) (x k)) e + (M (k+1) e-M k e))
    {R : ℝ} (hR : 0 ≤ R) (ha : ∀ k < T, 0 ≤ a k ∧ a k ≤ 1)
    (hM : ∀ k ≤ T, ∀ e ∈ active k, |M k e| ≤ R) :
    ∀ e ∈ active T, |x T e| ≤ R*(1+2*∑ k ∈ Finset.range T, a k) := by
  have hb := movingStarVertices_bound ends hends active a M T hR ha (fun k hk => hM k (by omega))
  intro e he
  rw [movingStar_trajectory_representation ends active a M x T hnest hinit hstep e he]
  calc
    _ ≤ |M T e|+|movingStarLift ends (movingStarVertices ends active a M T) e| := moving_abs_sub_bound _ _
    _ ≤ R+2*(R*∑ k ∈ Finset.range T, a k) := add_le_add (hM T le_rfl e he)
      (movingStarLift_bound ends hends _ hb e)
    _ = _ := by ring

lemma movingStar_incidence_swap {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (f : E → V → ℝ) :
    (∑ e ∈ active, ∑ u ∈ ends e, f e u) =
      ∑ u, ∑ e ∈ active.filter (fun e => u ∈ ends e), f e u := by
  classical
  have he (e : E) : (∑ u ∈ ends e, f e u) = ∑ u, if u ∈ ends e then f e u else 0 := by simp
  simp_rw [he]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]

lemma movingStarMean_mass {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (x : E → ℝ) (u : V) :
    movingStarDegree ends active u*movingStarMean ends active x u =
      ∑ e ∈ active.filter (fun e => u ∈ ends e), x e := by
  classical
  by_cases hd : movingStarDegree ends active u = 0
  · have hc : (active.filter (fun e => u ∈ ends e)).card = 0 := by
      exact_mod_cast (show ((active.filter (fun e => u ∈ ends e)).card : ℝ) = 0 from hd)
    have he := Finset.card_eq_zero.mp hc
    simp [movingStarMean,hd,he]
  · unfold movingStarMean
    exact mul_div_cancel₀ _ hd

theorem movingStar_energy_identity {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (x : E → ℝ) :
    (∑ e ∈ active, x e*movingStarLift ends (movingStarMean ends active x) e) =
      ∑ u, movingStarDegree ends active u*(movingStarMean ends active x u)^2 := by
  classical
  simp only [movingStarLift,Finset.mul_sum]
  rw [movingStar_incidence_swap]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul,← movingStarMean_mass ends active x u]
  ring

lemma movingStar_lift_sq_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : Finset E) (b : V → ℝ) :
    (∑ e ∈ active, (movingStarLift ends b e)^2) ≤
      2*∑ u, movingStarDegree ends active u*(b u)^2 := by
  classical
  calc
    _ ≤ ∑ e ∈ active, 2*∑ u ∈ ends e, (b u)^2 := by
      apply Finset.sum_le_sum
      intro e _
      simpa only [movingStarLift,hends,Nat.cast_ofNat] using
        (sq_sum_le_card_mul_sum_sq (s := ends e) (f := b))
    _ = _ := by
      rw [← Finset.mul_sum,movingStar_incidence_swap]
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      simp [movingStarDegree]

theorem movingStar_euler_energy_le {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : Finset E) (x : E → ℝ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑ e ∈ active, (x e-a*movingStarLift ends (movingStarMean ends active x) e)^2) ≤
      ∑ e ∈ active, (x e)^2 := by
  classical
  let P := movingStarLift ends (movingStarMean ends active x)
  let V := ∑ u, movingStarDegree ends active u*(movingStarMean ends active x u)^2
  have hV : 0 ≤ V := Finset.sum_nonneg (fun u _ =>
    mul_nonneg (movingStarDegree_nonneg ends active u) (sq_nonneg _))
  have hlin : (∑ e ∈ active, x e*P e) = V := movingStar_energy_identity ends active x
  have hsq : (∑ e ∈ active, (P e)^2) ≤ 2*V :=
    movingStar_lift_sq_bound ends hends active (movingStarMean ends active x)
  have hexpand : (∑ e ∈ active, (x e-a*P e)^2) =
      (∑ e ∈ active, (x e)^2)-2*a*(∑ e ∈ active, x e*P e)+
      a^2*(∑ e ∈ active, (P e)^2) := by
    calc
      _ = ∑ e ∈ active, ((x e)^2-2*a*(x e*P e)+a^2*(P e)^2) := by
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
  change (∑ e ∈ active, (x e-a*P e)^2) ≤ _
  rw [hexpand,hlin]
  have hsq' := mul_le_mul_of_nonneg_left hsq (sq_nonneg a)
  have hab : a^2 ≤ a := by nlinarith
  have hb := mul_le_mul_of_nonneg_right hab hV
  nlinarith only [hsq',hb]

theorem movingStar_euler_energy_subset_le {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active remaining : Finset E) (hsub : remaining ⊆ active) (x : E → ℝ)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑ e ∈ remaining, (x e-a*movingStarLift ends (movingStarMean ends active x) e)^2) ≤
      ∑ e ∈ active, (x e)^2 := by
  apply le_trans _ (movingStar_euler_energy_le ends hends active x ha ha1)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)

end SharpTerminalLeave
end

end OAI
