import Mathlib
import OAI.Combinatorics.Chromatic.Walls.StationaryIntegerSequences

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open ElementaryPositivity.QuantumTorus
variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
variable (Ω : Lattice n B →+ Lattice n B →+ ℤ)

omit [Fintype B] in
lemma period_of_bridge_eq (level : B → Fin n) (cycle : List B) (L : ℕ) (m : Lattice n B)
    (h : ∀ b, period Ω level cycle L m (Sum.inr b) = m (Sum.inr b)) :
    period Ω level cycle L m = m ∧ ∀ b ∈ cycle, 0 ≤ Ω (eventRoot level L b) m := by
  induction cycle generalizing m with
  | nil => exact ⟨rfl,by simp⟩
  | cons b bs ih =>
    have hle := period_bridge_mono Ω level bs L (rotate Ω level L m b) b
    change rotate Ω level L m b (Sum.inr b) ≤ period Ω level (b::bs) L m (Sum.inr b) at hle
    rw [h b] at hle
    have ht : max 0 (-Ω (eventRoot level L b) m) = 0 := by
      simp only [rotate,mutationIncomingLabel,Pi.add_apply,Pi.smul_apply,eventRoot_bridge,
        ite_true,smul_eq_mul,mul_one] at hle
      omega
    have hfix : rotate Ω level L m b = m := by
      simp only [rotate,mutationIncomingLabel,ht,zero_zsmul,add_zero]
    have hp : period Ω level (b::bs) L m = period Ω level bs L m := by
      change period Ω level bs L (rotate Ω level L m b) = _
      rw [hfix]
    have H := ih m (by intro c; simpa only [hp] using h c)
    refine ⟨hp.trans H.1,fun c hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · omega
    · exact H.2 c hc

lemma history_late_fixed (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (N : ℕ) (hs : ∀ L i, 0 ≤ cutDeficit level i N L (history Ω level cycle m L)) :
    ∃ T, (∀ L, T ≤ L → history Ω level cycle m L = history Ω level cycle m T) ∧
      ∀ L, T ≤ L → ∀ b ∈ cycle, 0 ≤ Ω (eventRoot level L b) (history Ω level cycle m T) := by
  obtain ⟨T,hT⟩ := history_bridge_stabilizes Ω level cycle m N hs
  have he : ∀ L, T ≤ L → period Ω level cycle L (history Ω level cycle m L) =
      history Ω level cycle m L ∧
      ∀ b ∈ cycle, 0 ≤ Ω (eventRoot level L b) (history Ω level cycle m L) := by
    intro L hL
    apply period_of_bridge_eq
    intro b
    change history Ω level cycle m (L+1) (Sum.inr b) = history Ω level cycle m L (Sum.inr b)
    rw [hT (L+1) (by omega) b,hT L hL b]
  have hconst : ∀ k, history Ω level cycle m (T+k) = history Ω level cycle m T := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.add_succ,history]
      exact ((he (T+k) (by omega)).1).trans ih
  refine ⟨T,?_,?_⟩
  · intro L hL
    simpa only [Nat.add_sub_of_le hL] using hconst (L-T)
  · intro L hL b hb
    have HH := (he L hL).2 b hb
    have H := hconst (L-T)
    rw [Nat.add_sub_of_le hL] at H
    simpa only [H] using HH

omit [Fintype B] in
lemma eventRoot_pairing (level : B → Fin n) (L : ℕ) (b : B) (m : Lattice n B) :
    Ω (eventRoot level L b) m = Ω (eventRoot level 0 b) m + (L:ℤ)*Ω (delta level b) m := by
  simp only [eventRoot,Nat.cast_zero,zero_zsmul,add_zero,map_add,map_zsmul,
    AddMonoidHom.add_apply,AddMonoidHom.zsmul_apply,smul_eq_mul]

omit [Fintype B] in
lemma period_fixed (level : B → Fin n) (cycle : List B) (L : ℕ) (m : Lattice n B)
    (hp : ∀ b ∈ cycle, 0 ≤ Ω (eventRoot level L b) m) : period Ω level cycle L m = m := by
  induction cycle with
  | nil => rfl
  | cons b bs ih =>
    change period Ω level bs L (mutationIncomingLabel Ω (eventRoot level L b) m) = m
    rw [mutationIncomingLabel_nonnegative Ω _ m (hp b (by simp))]
    exact ih (by intro c hc; exact hp c (by simp [hc]))

omit [Fintype B] in
lemma period_injective (hΩ : ∀ m, Ω m m = 0) (level : B → Fin n) (cycle : List B) (L : ℕ) :
    Function.Injective (period Ω level cycle L) := by
  induction cycle with
  | nil => exact Function.injective_id
  | cons b bs ih =>
    intro m m' h
    apply (mutationIncomingLabelEquiv Ω (eventRoot level L b) (hΩ _)).injective
    apply ih
    exact h

omit [Fintype B] in
lemma history_injective (hΩ : ∀ m, Ω m m = 0) (level : B → Fin n) (cycle : List B) (L : ℕ) :
    Function.Injective (fun m => history Ω level cycle m L) := by
  induction L with
  | zero => exact Function.injective_id
  | succ L ih =>
    intro m m' h
    apply ih
    exact period_injective Ω hΩ level cycle L h

omit [Fintype B] in
lemma history_fixed (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (hp : ∀ L b, b ∈ cycle → 0 ≤ Ω (eventRoot level L b) m) (L : ℕ) :
    history Ω level cycle m L = m := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [history,ih]
    exact period_fixed Ω level cycle L m (hp L)
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open ElementaryPositivity.QuantumTorus
variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

def extendedTotal (level : B → Fin n) (m : Lattice n B) (k : ℕ) : ℤ :=
  if h : 0 < k ∧ k ≤ n then levelTotal level ⟨k-1,by omega⟩ m else 0

omit [DecidableEq B] in
@[simp] lemma extendedTotal_zero (level : B → Fin n) (m : Lattice n B) :
    extendedTotal level m 0 = 0 := by simp [extendedTotal]
omit [DecidableEq B] in
@[simp] lemma extendedTotal_last (level : B → Fin n) (m : Lattice n B) :
    extendedTotal level m (n+1) = 0 := by simp [extendedTotal]
omit [DecidableEq B] in
@[simp] lemma extendedTotal_succ (level : B → Fin n) (m : Lattice n B) (i : Fin n) :
    extendedTotal level m (i.val+1) = levelTotal level i m := by
  unfold extendedTotal
  rw [dite_eq_left (by constructor <;> omega)]
  congr 2

omit [DecidableEq B] in
lemma extendedTotal_nonpos (level : B → Fin n) (m : Lattice n B)
    (h : ∀ i, levelTotal level i m ≤ 0) (k : ℕ) : extendedTotal level m k ≤ 0 := by
  unfold extendedTotal
  split_ifs with hk
  · exact h _
  · rfl

omit [DecidableEq B] in
lemma extendedTotal_all_zero (level : B → Fin n) (m : Lattice n B)
    (h : ∀ k, k ≤ n+1 → extendedTotal level m k = 0) (k : ℕ) :
    extendedTotal level m k = 0 := by
  by_cases hk : k ≤ n+1
  · exact h k hk
  · simp [extendedTotal,show ¬(0<k ∧ k≤n) by omega]

variable (Ω : Lattice n B →+ Lattice n B →+ ℤ)

lemma tropical_history_stationary (hΩ : ∀ m, Ω m m = 0)
    (level : B → Fin n) (hl : Function.Surjective level)
    (cycle : List B) (hcycle : ∀ b, b ∈ cycle)
    (hdelta : ∀ b m, Ω (delta level b) m =
      2*extendedTotal level m ((level b).val+1) - extendedTotal level m (level b).val -
        extendedTotal level m ((level b).val+2))
    (m : Lattice n B) (N : ℕ)
    (hs : ∀ L i, 0 ≤ cutDeficit level i N L (history Ω level cycle m L)) :
    (∀ i, levelTotal level i m = 0) ∧
      (∀ b, 0 ≤ Ω (eventRoot level 0 b) m) ∧
      (∀ L, history Ω level cycle m L = m) := by
  obtain ⟨T,hT,hp⟩ := history_late_fixed Ω level cycle m N hs
  let star := history Ω level cycle m T
  have hslope : ∀ b, 0 ≤ Ω (delta level b) star := by
    intro b
    apply nonnegative_affine_slope (Ω (eventRoot level 0 b) star)
    refine ⟨T,fun L hL => ?_⟩
    rw [←eventRoot_pairing]
    exact hp L hL b (hcycle b)
  have ht : ∀ k, k ≤ n+1 → extendedTotal level star k = 0 := by
    apply concave_nonpositive_zero (n+1) (extendedTotal level star)
      (extendedTotal_zero _ _) (extendedTotal_last _ _)
    · intro k _
      exact extendedTotal_nonpos level star (fun i => history_total_nonpos Ω level cycle m N hs T i) k
    · intro k hk hkn
      let i : Fin n := ⟨k-1,by omega⟩
      obtain ⟨b,hb⟩ := hl i
      have HH := hslope b
      rw [hdelta,hb] at HH
      have hi : i.val+1=k := by dsimp [i]; omega
      have hi' : i.val+2=k+1 := by omega
      rw [hi,hi'] at HH
      exact HH
  have hall := extendedTotal_all_zero level star ht
  have hd0 : ∀ b, Ω (delta level b) star = 0 := by
    intro b
    rw [hdelta,hall,hall,hall]
    ring
  have hp0 : ∀ b, 0 ≤ Ω (eventRoot level 0 b) star := by
    intro b
    have HH := hp T le_rfl b (hcycle b)
    change 0 ≤ Ω (eventRoot level T b) star at HH
    rw [eventRoot_pairing,hd0,mul_zero,add_zero] at HH
    exact HH
  have hpl : ∀ L b, b ∈ cycle → 0 ≤ Ω (eventRoot level L b) star := by
    intro L b _
    rw [eventRoot_pairing,hd0,mul_zero,add_zero]
    exact hp0 b
  have hm : m = star := by
    apply history_injective Ω hΩ level cycle T
    change history Ω level cycle m T = history Ω level cycle star T
    rw [history_fixed Ω level cycle star hpl T]
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [hm,←extendedTotal_succ]
    exact hall _
  · simpa only [hm] using hp0
  · intro L
    rw [hm]
    exact history_fixed Ω level cycle star hpl L
end ElementaryPositivity.TriangularDynamics

end

end OAI
