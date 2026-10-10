import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.MarkovLaw

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

abbrev History (α : Type*) (T : ℕ) := Fin (T + 1) → α

def historyIndex (T k : ℕ) : Fin (T + 1) := ⟨min k T,by omega⟩

@[simp] theorem historyIndex_val (T k : ℕ) : (historyIndex T k).val = min k T := rfl

noncomputable def historyInitial {α : Type*} (initial : PMF α) (T : ℕ) : PMF (History α T) :=
  initial.map (fun a => fun _ => a)

noncomputable def historyKernel {α : Type*} (K : ℕ → α → PMF α) (T k : ℕ)
    (ω : History α T) : PMF (History α T) :=
  if k < T then (K k (ω (historyIndex T k))).map
    (fun b => Function.update ω (historyIndex T (k + 1)) b) else PMF.pure ω

noncomputable def historyLaw {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α)
    (T k : ℕ) : PMF (History α T) :=
  markovLaw (historyInitial initial T) (historyKernel K T) k

theorem historyIndex_ne_succ {T j k : ℕ} (hjk : j ≤ k) (hk : k < T) :
    historyIndex T j ≠ historyIndex T (k + 1) := by
  intro h
  have he := congrArg Fin.val h
  simp only [historyIndex_val] at he
  omega

theorem historyLaw_marginal {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α)
    (T k : ℕ) (hk : k ≤ T) :
    (historyLaw initial K T k).map (fun ω => ω (historyIndex T k)) =
      markovLaw initial K k := by
  induction k with
  | zero =>
    simp only [historyLaw,markovLaw,historyInitial,PMF.map_comp]
    change initial.map id = initial
    exact PMF.map_id initial
  | succ k ih =>
    have hkt : k < T := by omega
    have hkm : k ≤ T := by omega
    simp only [historyLaw,markovLaw,PMF.map_bind]
    have ih' := ih hkm
    change (historyLaw initial K T k).bind _ = (markovLaw initial K k).bind (K k)
    rw [← ih',PMF.bind_map]
    congr 1
    funext ω
    simp only [historyKernel,ite_eq_left hkt,PMF.map_comp,Function.comp_def,
      Function.update_self]
    exact PMF.map_id _

theorem historyLaw_invariant {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α)
    (P : α → Prop) (hinit : ∀ a ∈ initial.support, P a)
    (hstep : ∀ k a, P a → ∀ b ∈ (K k a).support, P b)
    (T k : ℕ) (ω : History α T) (hω : ω ∈ (historyLaw initial K T k).support) :
    ∀ j, P (ω j) := by
  induction k generalizing ω with
  | zero =>
    obtain ⟨a,ha,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
    exact fun _ => hinit a ha
  | succ k ih =>
    obtain ⟨π,hπ,hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
    have hp := ih π hπ
    by_cases hk : k < T
    · rw [historyKernel,ite_eq_left hk] at hω
      obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
      intro j
      by_cases hj : j = historyIndex T (k + 1)
      · subst j
        rw [Function.update_self]
        exact hstep k _ (hp _) b hb
      · rw [Function.update_of_ne hj]
        exact hp j
    · rw [historyKernel,ite_eq_right hk,PMF.mem_support_pure_iff] at hω
      subst ω
      exact hp

noncomputable def historyIncrement {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T j : ℕ) (ω : History α T) : ℝ :=
  f (j + 1) (ω (historyIndex T (j + 1))) -
    pmfMean (K j (ω (historyIndex T j))) (f (j + 1))

noncomputable def historyNoise {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T k : ℕ) (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), historyIncrement K f T j ω

noncomputable def historyCounter {α : Type*} (v : ℕ → α → ℝ)
    (T k : ℕ) (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), v j (ω (historyIndex T j))

noncomputable def historyCounterRate {α : Type*} (v : ℕ → α → ℝ)
    (T k : ℕ) (ω : History α T) : ℝ :=
  if k < T then v k (ω (historyIndex T k)) else 0

theorem historyNoise_update {α : Type*} [Fintype α] (K : ℕ → α → PMF α)
    (f : ℕ → α → ℝ) (T k : ℕ) (hk : k < T) (ω : History α T) (b : α) :
    historyNoise K f T (k + 1) (Function.update ω (historyIndex T (k + 1)) b) =
      historyNoise K f T k ω + f (k + 1) b -
        pmfMean (K k (ω (historyIndex T k))) (f (k + 1)) := by
  unfold historyNoise
  rw [Nat.min_eq_left (by omega : k + 1 ≤ T),Nat.min_eq_left hk.le,Finset.sum_range_succ]
  have hp : (∑ j ∈ Finset.range k,
      historyIncrement K f T j (Function.update ω (historyIndex T (k + 1)) b)) =
      ∑ j ∈ Finset.range k, historyIncrement K f T j ω := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjk := Finset.mem_range.mp hj
    simp only [historyIncrement,Function.update_of_ne (historyIndex_ne_succ (by omega : j + 1 ≤ k) hk),
      Function.update_of_ne (historyIndex_ne_succ hjk.le hk)]
  rw [hp]
  simp only [historyIncrement,Function.update_self,
    Function.update_of_ne (historyIndex_ne_succ le_rfl hk)]
  ring

theorem historyCounter_update {α : Type*} (v : ℕ → α → ℝ)
    (T k : ℕ) (hk : k < T) (ω : History α T) (b : α) :
    historyCounter v T (k + 1) (Function.update ω (historyIndex T (k + 1)) b) =
      historyCounter v T k ω + v k (ω (historyIndex T k)) := by
  unfold historyCounter
  rw [Nat.min_eq_left (by omega : k + 1 ≤ T),Nat.min_eq_left hk.le,Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (historyIndex_ne_succ (Finset.mem_range.mp hj).le hk)]
  · rw [Function.update_of_ne (historyIndex_ne_succ le_rfl hk)]

@[simp] theorem historyNoise_zero {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T : ℕ) (ω : History α T) :
    historyNoise K f T 0 ω = 0 := by simp [historyNoise]

@[simp] theorem historyCounter_zero {α : Type*} (v : ℕ → α → ℝ)
    (T : ℕ) (ω : History α T) : historyCounter v T 0 ω = 0 := by simp [historyCounter]

theorem historyLaw_current_support {α : Type*} (initial : PMF α)
    (K : ℕ → α → PMF α) (T k : ℕ) (hk : k ≤ T)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T k).support) :
    ω (historyIndex T k) ∈ (markovLaw initial K k).support := by
  rw [← historyLaw_marginal initial K T k hk]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨ω,hω,rfl⟩

theorem historyNoise_frozen {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T k : ℕ) (hk : T ≤ k)
    (ω : History α T) : historyNoise K f T (k + 1) ω = historyNoise K f T k ω := by
  simp only [historyNoise,Nat.min_eq_right hk,Nat.min_eq_right (by omega : T ≤ k + 1)]

theorem historyCounter_frozen {α : Type*} (v : ℕ → α → ℝ) (T k : ℕ) (hk : T ≤ k)
    (ω : History α T) : historyCounter v T (k + 1) ω = historyCounter v T k ω := by
  simp only [historyCounter,Nat.min_eq_right hk,Nat.min_eq_right (by omega : T ≤ k + 1)]

theorem history_noise_freedman {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (f v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support,
        |f (k + 1) b - pmfMean (K k a) (f (k + 1))| ≤ c)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b =>
        (f (k + 1) b - pmfMean (K k a) (f (k + 1))) ^ 2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyNoise K f T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0) ≤ Real.exp (-r ^ 2 / (4 * (V + c * r))) := by
  classical
  apply finite_freedman (historyInitial initial T) (historyKernel K T)
    (historyNoise K f T) (historyCounter v T) (historyCounterRate v T) c hc
  · intro ω _
    simp only [historyNoise_zero,historyCounter_zero,le_refl,and_self]
  · intro j ω hω π hπ
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hπ
      obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hπ
      rw [historyNoise_update K f T j hj]
      have hb' := hbounded j hj _ (historyLaw_current_support initial K T j hj.le ω hω) b hb
      convert hb' using 1; congr 1; ring
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hπ
      subst π
      rw [historyNoise_frozen K f T j (Nat.le_of_not_gt hj),sub_self,abs_zero]
      exact hc.le
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map]
      have he (b : α) : historyNoise K f T (j + 1)
          (Function.update ω (historyIndex T (j + 1)) b) - historyNoise K f T j ω =
          f (j + 1) b - pmfMean (K j (ω (historyIndex T j))) (f (j + 1)) := by
        rw [historyNoise_update K f T j hj]
        ring
      simp_rw [he]
      rw [pmfMean_sub,pmfMean_const,sub_self]
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyNoise_frozen K f T j (Nat.le_of_not_gt hj),sub_self]
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map,historyCounterRate,ite_eq_left hj]
      have he (b : α) : historyNoise K f T (j + 1)
          (Function.update ω (historyIndex T (j + 1)) b) - historyNoise K f T j ω =
          f (j + 1) b - pmfMean (K j (ω (historyIndex T j))) (f (j + 1)) := by
        rw [historyNoise_update K f T j hj]
        ring
      simp_rw [he]
      exact hvar j hj _ (historyLaw_current_support initial K T j hj.le ω hω)
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyNoise_frozen K f T j (Nat.le_of_not_gt hj),sub_self,
        historyCounterRate,ite_eq_right hj,zero_pow (by decide : 2 ≠ 0)]
  · intro j ω _ π hπ
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hπ
      obtain ⟨b,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hπ
      rw [historyCounter_update v T j hj,historyCounterRate,ite_eq_left hj]
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hπ
      subst π
      rw [historyCounter_frozen v T j (Nat.le_of_not_gt hj),
        historyCounterRate,ite_eq_right hj,add_zero]
  · exact hr
  · exact hV

end SharpTerminalLeave

end

end OAI
