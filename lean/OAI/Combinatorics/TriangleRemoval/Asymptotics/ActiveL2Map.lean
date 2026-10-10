import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.MovingStarDegree

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave
open Classical

noncomputable def activeL2Map {E : Type*} [Fintype E] (s : Finset E) :
    (E → ℝ) →ₗ[ℝ] EuclideanSpace ℝ E where
  toFun x := WithLp.toLp 2 (fun e => if e ∈ s then x e else 0)
  map_add' x y := by ext e; by_cases he : e ∈ s <;> simp [he]
  map_smul' c x := by ext e; by_cases he : e ∈ s <;> simp [he]

noncomputable def activeL2 {E : Type*} [Fintype E] (s : Finset E) : Seminorm ℝ (E → ℝ) :=
  (normSeminorm ℝ (EuclideanSpace ℝ E)).comp (activeL2Map s)

lemma activeL2_sq {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ) :
    (activeL2 s x)^2 = ∑ e ∈ s, (x e)^2 := by
  change ‖activeL2Map s x‖^2 = _
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [activeL2Map]

lemma activeL2_congr {E : Type*} [Fintype E] (s : Finset E) {x y : E → ℝ}
    (h : ∀ e ∈ s, x e = y e) : activeL2 s x = activeL2 s y := by
  have hm : activeL2Map s x = activeL2Map s y := by
    ext e
    by_cases he : e ∈ s
    · simp [activeL2Map,he,h e he]
    · simp [activeL2Map,he]
  change ‖activeL2Map s x‖ = ‖activeL2Map s y‖
  rw [hm]

lemma activeL2_mono {E : Type*} [Fintype E] {s t : Finset E} (h : s ⊆ t) (x : E → ℝ) :
    activeL2 s x ≤ activeL2 t x := by
  have hs : (activeL2 s x)^2 ≤ (activeL2 t x)^2 := by
    rw [activeL2_sq,activeL2_sq]
    exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _)
  nlinarith [apply_nonneg (activeL2 s) x,apply_nonneg (activeL2 t) x]

lemma activeL2_coordinate {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ)
    {e : E} (he : e ∈ s) : |x e| ≤ activeL2 s x := by
  have hs : (x e)^2 ≤ (activeL2 s x)^2 := by
    rw [activeL2_sq]
    exact Finset.single_le_sum (fun _ _ => sq_nonneg _) he
  nlinarith [sq_abs (x e), abs_nonneg (x e),apply_nonneg (activeL2 s) x]

lemma activeL2_of_bound {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hx : ∀ e ∈ s, |x e| ≤ R) :
    activeL2 s x ≤ (Fintype.card E : ℝ)*R := by
  have hs : (activeL2 s x)^2 ≤ (s.card : ℝ)*R^2 := by
    rw [activeL2_sq]
    calc
      _ ≤ ∑ _e ∈ s, R^2 := Finset.sum_le_sum (fun e he => by
        have := hx e he
        nlinarith [sq_abs (x e),abs_nonneg (x e)])
      _ = _ := by simp
  have hn : (s.card : ℝ) ≤ Fintype.card E := by exact_mod_cast Finset.card_le_univ s
  have hn2 : (Fintype.card E : ℝ) ≤ (Fintype.card E : ℝ)^2 := by
    have := Nat.le_mul_self (Fintype.card E)
    exact_mod_cast (by simpa only [pow_two] using this)
  have hp := mul_le_mul_of_nonneg_right (hn.trans hn2) (sq_nonneg R)
  have h0 : 0 ≤ (Fintype.card E : ℝ)*R := mul_nonneg (Nat.cast_nonneg _) hR
  nlinarith [apply_nonneg (activeL2 s) x]

lemma movingStar_euler_activeL2 {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (s : Finset E) (x : E → ℝ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    activeL2 s (fun e => x e-a*movingStarLift ends (movingStarMean ends s x) e) ≤ activeL2 s x := by
  have hs := movingStar_euler_energy_le ends hends s x ha ha1
  rw [← activeL2_sq,← activeL2_sq] at hs
  nlinarith [apply_nonneg (activeL2 s) x,
    apply_nonneg (activeL2 s) (fun e => x e-a*movingStarLift ends (movingStarMean ends s x) e)]

lemma movingStar_activeL2_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (s : Finset E) (x : E → ℝ) :
    activeL2 s (movingStarLift ends (movingStarMean ends s x)) ≤ 2*activeL2 s x := by
  let P := movingStarLift ends (movingStarMean ends s x)
  have hi : P = x-(x-P) := by funext e; simp
  have he := movingStar_euler_activeL2 ends hends s x (a := 1) (by norm_num) le_rfl
  simp only [one_mul] at he
  calc
    activeL2 s P = activeL2 s (x-(x-P)) := congrArg _ hi
    _ ≤ activeL2 s x+activeL2 s (x-P) := map_sub_le_add _ _ _
    _ ≤ activeL2 s x+activeL2 s x := add_le_add le_rfl he
    _ = _ := by ring

lemma movingStarMean_add {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (s : Finset E) (x y : E → ℝ) (u : V) :
    movingStarMean ends s (x+y) u = movingStarMean ends s x u+movingStarMean ends s y u := by
  simp [movingStarMean,Pi.add_apply,Finset.sum_add_distrib,add_div]

lemma movingStarLift_add {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (b c : V → ℝ) :
    movingStarLift ends (b+c) = movingStarLift ends b+movingStarLift ends c := by
  funext e
  simp [movingStarLift,Pi.add_apply,Finset.sum_add_distrib]

theorem movingStar_trajectory_l2_bound {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : ℕ → Finset E) (a : ℕ → ℝ) (M x : ℕ → E → ℝ) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (hinit : ∀ e ∈ active 0, x 0 e = M 0 e)
    (hstep : ∀ k < T, ∀ e ∈ active (k+1), x (k+1) e = x k e -
      a k*movingStarLift ends (movingStarMean ends (active k) (x k)) e + (M (k+1) e-M k e))
    {R : ℝ} (_hR : 0 ≤ R) (ha : ∀ k < T, 0 ≤ a k ∧ a k ≤ 1)
    (hM : ∀ k ≤ T, activeL2 (active k) (M k) ≤ R) :
    activeL2 (active T) (x T) ≤ R*(1+2*∑ k ∈ Finset.range T, a k) := by
  let z : ℕ → E → ℝ := fun k => x k-M k
  have hz : ∀ t ≤ T, activeL2 (active t) (z t) ≤ 2*R*∑ k ∈ Finset.range t, a k := by
    intro t ht
    induction t with
    | zero =>
      have he : activeL2 (active 0) (z 0) = 0 := by
        trans activeL2 (active 0) 0
        · apply activeL2_congr
          intro e he
          simp [z,hinit e he]
        · exact map_zero _
      simpa only [he, Finset.range_zero, Finset.sum_empty, mul_zero] using (le_refl (0 : ℝ))
    | succ t ih =>
      have htT : t < T := by omega
      have hi := ih (by omega)
      have hzstep : ∀ e ∈ active (t+1), z (t+1) e =
          (z t e-a t*movingStarLift ends (movingStarMean ends (active t) (z t)) e)-
            a t*movingStarLift ends (movingStarMean ends (active t) (M t)) e := by
        intro e he
        have hx : x t = z t+M t := by funext e; simp [z]
        have hp := hstep t htT e he
        rw [hx] at hp
        have hm : movingStarMean ends (active t) (z t+M t) =
            movingStarMean ends (active t) (z t)+movingStarMean ends (active t) (M t) := by
          funext u
          exact movingStarMean_add ends (active t) (z t) (M t) u
        rw [hm,movingStarLift_add] at hp
        change x (t+1) e-M (t+1) e = _
        simp only [Pi.add_apply] at hp
        linarith only [hp]
      calc
        activeL2 (active (t+1)) (z (t+1)) = activeL2 (active (t+1))
          ((fun e => z t e-a t*movingStarLift ends (movingStarMean ends (active t) (z t)) e)-
            a t • movingStarLift ends (movingStarMean ends (active t) (M t))) :=
              activeL2_congr _ hzstep
        _ ≤ activeL2 (active t)
          ((fun e => z t e-a t*movingStarLift ends (movingStarMean ends (active t) (z t)) e)-
            a t • movingStarLift ends (movingStarMean ends (active t) (M t))) :=
              activeL2_mono (hnest t htT) _
        _ ≤ activeL2 (active t)
          (fun e => z t e-a t*movingStarLift ends (movingStarMean ends (active t) (z t)) e)+
            activeL2 (active t) (a t • movingStarLift ends (movingStarMean ends (active t) (M t))) :=
              map_sub_le_add _ _ _
        _ ≤ activeL2 (active t) (z t)+a t*(2*activeL2 (active t) (M t)) := by
          rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg (ha t htT).1]
          exact add_le_add (movingStar_euler_activeL2 ends hends _ _ (ha t htT).1 (ha t htT).2)
            (mul_le_mul_of_nonneg_left (movingStar_activeL2_bound ends hends _ _) (ha t htT).1)
        _ ≤ 2*R*∑ k ∈ Finset.range t, a k+a t*(2*R) := by
          exact add_le_add hi (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hM t (by omega)) (by norm_num)) (ha t htT).1)
        _ = _ := by rw [Finset.sum_range_succ]; ring
  have hx : x T = M T+z T := by funext e; simp [z]
  calc
    activeL2 (active T) (x T) = activeL2 (active T) (M T+z T) := congrArg _ hx
    _ ≤ activeL2 (active T) (M T)+activeL2 (active T) (z T) := map_add_le_add _ _ _
    _ ≤ R+2*R*∑ k ∈ Finset.range T, a k := add_le_add (hM T le_rfl) (hz T le_rfl)
    _ = _ := by ring

noncomputable def activeLinf {E : Type*} [Fintype E] (s : Finset E) : Seminorm ℝ (E → ℝ) :=
  s.sup (fun e => (normSeminorm ℝ ℝ).comp (LinearMap.proj e))

lemma activeLinf_coordinate {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ)
    {e : E} (he : e ∈ s) : |x e| ≤ activeLinf s x := by
  exact Seminorm.le_finset_sup_apply (p := fun e =>
    (normSeminorm ℝ ℝ).comp (LinearMap.proj e)) (x := x) he

lemma activeLinf_bound {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hx : ∀ e ∈ s, |x e| ≤ R) : activeLinf s x ≤ R := by
  exact Seminorm.finset_sup_apply_le hR hx

lemma activeLinf_le_l2 {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ) :
    activeLinf s x ≤ activeL2 s x :=
  activeLinf_bound s x (apply_nonneg _ _) (fun _ he => activeL2_coordinate s x he)

lemma activeL2_le_card_linf {E : Type*} [Fintype E] (s : Finset E) (x : E → ℝ) :
    activeL2 s x ≤ (Fintype.card E : ℝ)*activeLinf s x :=
  activeL2_of_bound s x (apply_nonneg _ _) (fun _ he => activeLinf_coordinate s x he)

noncomputable def trajectorySeminorm {E : Type*} [Fintype E]
    (P : ℕ → Seminorm ℝ (E → ℝ)) (T : ℕ) : Seminorm ℝ (ℕ → E → ℝ) :=
  (Finset.range (T+1)).sup (fun t => (P t).comp (LinearMap.proj t))

lemma trajectorySeminorm_at {E : Type*} [Fintype E]
    (P : ℕ → Seminorm ℝ (E → ℝ)) (T : ℕ) (x : ℕ → E → ℝ) {t : ℕ} (ht : t ≤ T) :
    P t (x t) ≤ trajectorySeminorm P T x :=
  Seminorm.le_finset_sup_apply (p := fun t => (P t).comp (LinearMap.proj t))
    (x := x) (Finset.mem_range.mpr (by omega))

lemma trajectorySeminorm_bound {E : Type*} [Fintype E]
    (P : ℕ → Seminorm ℝ (E → ℝ)) (T : ℕ) (x : ℕ → E → ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hx : ∀ t ≤ T, P t (x t) ≤ R) : trajectorySeminorm P T x ≤ R := by
  apply Seminorm.finset_sup_apply_le hR
  intro t ht
  exact hx t (by have := Finset.mem_range.mp ht; omega)

lemma trajectory_mixed_seminorms {E : Type*} [Fintype E]
    (active : ℕ → Finset E) (T : ℕ) (x : ℕ → E → ℝ) :
    trajectorySeminorm (fun t => activeLinf (active t)) T x ≤
      trajectorySeminorm (fun t => activeL2 (active t)) T x ∧
    trajectorySeminorm (fun t => activeL2 (active t)) T x ≤
      (Fintype.card E : ℝ)*trajectorySeminorm (fun t => activeLinf (active t)) T x := by
  constructor
  · apply trajectorySeminorm_bound _ _ _ (apply_nonneg _ _)
    intro t ht
    exact (activeLinf_le_l2 _ _).trans (trajectorySeminorm_at (fun t => activeL2 (active t)) T x ht)
  · apply trajectorySeminorm_bound _ _ _ (by positivity)
    intro t ht
    exact (activeL2_le_card_linf _ _).trans
      (mul_le_mul_of_nonneg_left (trajectorySeminorm_at (fun t => activeLinf (active t)) T x ht) (Nat.cast_nonneg _))

noncomputable def movingStarSolve {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ)
    (M : ℕ → E → ℝ) : ℕ → E → ℝ
  | 0 => M 0
  | t+1 => fun e => movingStarSolve ends active a M t e-
      a t*movingStarLift ends (movingStarMean ends (active t) (movingStarSolve ends active a M t)) e+
        (M (t+1) e-M t e)

lemma movingStarMean_smul {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (s : Finset E) (c : ℝ) (x : E → ℝ) :
    movingStarMean ends s (c • x) = c • movingStarMean ends s x := by
  funext u
  simp only [movingStarMean,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]
  ring

lemma movingStarLift_smul {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (c : ℝ) (b : V → ℝ) :
    movingStarLift ends (c • b) = c • movingStarLift ends b := by
  funext e
  simp [movingStarLift,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]

lemma movingStarSolve_add {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ)
    (M N : ℕ → E → ℝ) :
    movingStarSolve ends active a (M+N) = movingStarSolve ends active a M+movingStarSolve ends active a N := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm : movingStarMean ends (active t)
        (movingStarSolve ends active a M t+movingStarSolve ends active a N t) =
        movingStarMean ends (active t) (movingStarSolve ends active a M t)+
        movingStarMean ends (active t) (movingStarSolve ends active a N t) := by
      funext u
      exact movingStarMean_add _ _ _ _ _
    simp only [movingStarSolve,ih,Pi.add_apply] at hm ⊢
    rw [hm,movingStarLift_add]
    funext e
    simp only [Pi.add_apply]
    ring

lemma movingStarSolve_smul {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ)
    (c : ℝ) (M : ℕ → E → ℝ) :
    movingStarSolve ends active a (c • M) = c • movingStarSolve ends active a M := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    change (fun e => movingStarSolve ends active a (c • M) t e-
      a t*movingStarLift ends (movingStarMean ends (active t) (movingStarSolve ends active a (c • M) t)) e+
        ((c • M) (t+1) e-(c • M) t e)) = c • movingStarSolve ends active a M (t+1)
    rw [show movingStarSolve ends active a (c • M) t = c • movingStarSolve ends active a M t from ih,
      movingStarMean_smul,movingStarLift_smul]
    simp only [movingStarSolve]
    funext e
    simp only [Pi.smul_apply,smul_eq_mul]
    ring

noncomputable def movingStarResponse {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ) :
    Module.End ℝ (ℕ → E → ℝ) where
  toFun := movingStarSolve ends active a
  map_add' := movingStarSolve_add ends active a
  map_smul' := movingStarSolve_smul ends active a

lemma movingStarResponse_linf {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : ℕ → Finset E) (a : ℕ → ℝ) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (ha : ∀ k < T, 0 ≤ a k ∧ a k ≤ 1) (M : ℕ → E → ℝ) :
    trajectorySeminorm (fun t => activeLinf (active t)) T (movingStarResponse ends active a M) ≤
      (1+2*∑ k ∈ Finset.range T, a k)*trajectorySeminorm (fun t => activeLinf (active t)) T M := by
  let R := trajectorySeminorm (fun t => activeLinf (active t)) T M
  have hR : 0 ≤ R := apply_nonneg _ _
  have hsum : ∀ t ≤ T, (∑ k ∈ Finset.range t, a k) ≤ ∑ k ∈ Finset.range T, a k := by
    intro t ht
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht)
      (fun k hk _ => (ha k (Finset.mem_range.mp hk)).1)
  have hS : 0 ≤ ∑ k ∈ Finset.range T, a k :=
    Finset.sum_nonneg (fun k hk => (ha k (Finset.mem_range.mp hk)).1)
  apply trajectorySeminorm_bound _ _ _ (by positivity)
  intro t ht
  apply activeLinf_bound _ _ (by positivity)
  intro e he
  have hb := movingStar_trajectory_bound ends hends active a M
    (movingStarSolve ends active a M) t (fun k hk => hnest k (by omega))
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) hR (fun k hk => ha k (by omega))
    (fun k hk f hf => (activeLinf_coordinate _ _ hf).trans (trajectorySeminorm_at (fun t => activeLinf (active t)) T M (by omega))) e he
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left (hsum t ht) hR])

lemma movingStarResponse_l2 {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (hends : ∀ e, (ends e).card = 2)
    (active : ℕ → Finset E) (a : ℕ → ℝ) (T : ℕ)
    (hnest : ∀ k < T, active (k+1) ⊆ active k)
    (ha : ∀ k < T, 0 ≤ a k ∧ a k ≤ 1) (M : ℕ → E → ℝ) :
    trajectorySeminorm (fun t => activeL2 (active t)) T (movingStarResponse ends active a M) ≤
      (1+2*∑ k ∈ Finset.range T, a k)*trajectorySeminorm (fun t => activeL2 (active t)) T M := by
  let R := trajectorySeminorm (fun t => activeL2 (active t)) T M
  have hR : 0 ≤ R := apply_nonneg _ _
  have hsum : ∀ t ≤ T, (∑ k ∈ Finset.range t, a k) ≤ ∑ k ∈ Finset.range T, a k := by
    intro t ht
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht)
      (fun k hk _ => (ha k (Finset.mem_range.mp hk)).1)
  have hS : 0 ≤ ∑ k ∈ Finset.range T, a k :=
    Finset.sum_nonneg (fun k hk => (ha k (Finset.mem_range.mp hk)).1)
  apply trajectorySeminorm_bound _ _ _ (by positivity)
  intro t ht
  have hb := movingStar_trajectory_l2_bound ends hends active a M
    (movingStarSolve ends active a M) t (fun k hk => hnest k (by omega))
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) hR (fun k hk => ha k (by omega))
    (fun k hk => trajectorySeminorm_at (fun t => activeL2 (active t)) T M (by omega))
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left (hsum t ht) hR])

end SharpTerminalLeave
end
end

end OAI
