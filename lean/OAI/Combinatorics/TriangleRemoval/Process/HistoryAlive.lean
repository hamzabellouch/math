import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.TriangleDrift
import OAI.Combinatorics.TriangleRemoval.Process.History

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

def historyAlive {α : Type*} (safe : ℕ → α → Prop) (T j : ℕ)
    (ω : History α T) : Prop := ∀ i < j, safe i (ω (historyIndex T i))

lemma historyAlive_update {α : Type*} (safe : ℕ → α → Prop) (T j : ℕ)
    (hj : j < T) (ω : History α T) (b : α) :
    historyAlive safe T (j+1) (Function.update ω (historyIndex T (j+1)) b) ↔
      historyAlive safe T j ω ∧ safe j (ω (historyIndex T j)) := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hh := h i (by omega)
      rwa [Function.update_of_ne (historyIndex_ne_succ hi.le hj)] at hh
    · have hh := h j (by omega)
      rwa [Function.update_of_ne (historyIndex_ne_succ le_rfl hj)] at hh
  · rintro ⟨h,hj'⟩ i hi
    rw [Function.update_of_ne (historyIndex_ne_succ (by omega) hj)]
    rcases lt_or_eq_of_le (show i ≤ j by omega) with hi' | rfl
    · exact h i hi'
    · exact hj'

theorem history_alive_mean_le {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (safe : ℕ → α → Prop)
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (T : ℕ)
    (hstep : ∀ i < T, ∀ a, safe i a → pmfMean (K i a) f ≤ r i * f a)
    (j : ℕ) (hj : j ≤ T) :
    pmfMean (historyLaw initial K T j)
      (fun ω => if historyAlive safe T j ω then f (ω (historyIndex T j)) else 0) ≤
      (∏ i ∈ Finset.range j, r i) * pmfMean initial f := by
  classical
  induction j with
  | zero =>
    simp [historyLaw,markovLaw,historyInitial,pmfMean_map,historyAlive]
  | succ j ih =>
    have hjT : j < T := by omega
    have ih' := ih hjT.le
    change pmfMean ((historyLaw initial K T j).bind (historyKernel K T j)) _ ≤ _
    rw [pmfMean_bind,Finset.prod_range_succ]
    calc
      _ ≤ pmfMean (historyLaw initial K T j)
          (fun ω => r j * (if historyAlive safe T j ω then f (ω (historyIndex T j)) else 0)) := by
        apply pmfMean_mono
        intro ω _
        simp only [historyKernel,ite_eq_left hjT,pmfMean_map,historyAlive_update safe T j hjT,
          Function.update_self]
        by_cases ha : historyAlive safe T j ω
        · by_cases hs : safe j (ω (historyIndex T j))
          · simp only [ha,hs,and_self,ite_true]
            exact hstep j hjT _ hs
          · simp only [ha,hs,and_false,ite_false,ite_true,pmfMean_const]
            exact mul_nonneg (hr j) (hf _)
        · simp only [ha,false_and,ite_false,pmfMean_const,mul_zero,le_refl]
      _ = r j * pmfMean (historyLaw initial K T j)
          (fun ω => if historyAlive safe T j ω then f (ω (historyIndex T j)) else 0) :=
        pmfMean_const_mul _ _ _
      _ ≤ r j * ((∏ i ∈ Finset.range j, r i) * pmfMean initial f) :=
        mul_le_mul_of_nonneg_left ih' (hr j)
      _ = _ := by ring

lemma intact_nonnegative {n : ℕ} (F G : Graph n) : 0 ≤ intact F G := by
  classical
  unfold intact
  split_ifs <;> norm_num

theorem triangle_intact_exponential_bound {n : ℕ} (G F : Graph n) (D δ : ℝ)
    (hQ : (triangles G).Nonempty)
    (hdeg : ∀ e ∈ G, |(triangleDegree G e : ℝ)-D| ≤ δ) :
    pmfMean (step G) (intact F) ≤
      Real.exp (-((F.card : ℝ)*D-((F.card : ℝ)*δ+(F.card : ℝ)^2))/(triangles G).card) *
        intact F G := by
  classical
  by_cases hF : F ⊆ G
  · have he := hittingTriangles_degree_error G F D δ (fun e he => hdeg e (hF he))
    have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast hQ.card_pos
    rw [step_mean_intact hF hQ]
    simp only [intact,hF,ite_true,mul_one]
    have hl : (F.card : ℝ)*D-((F.card : ℝ)*δ+(F.card : ℝ)^2) ≤
        (hittingTriangles G F).card := by linarith [(abs_le.mp he).1]
    calc
      _ ≤ 1-((F.card : ℝ)*D-((F.card : ℝ)*δ+(F.card : ℝ)^2))/(triangles G).card :=
        sub_le_sub_left (div_le_div_of_nonneg_right hl hq.le) 1
      _ ≤ _ := by
        have hh := Real.add_one_le_exp
          (-(((F.card : ℝ)*D-((F.card : ℝ)*δ+(F.card : ℝ)^2))/(triangles G).card))
        convert hh using 1 <;> congr 1 <;> ring
  · rw [step_mean_intact_of_not_subset hF]
    simp [intact,hF]

theorem triangle_killed_survival {n : ℕ} (initial : PMF (Graph n))
    (safe : ℕ → Graph n → Prop) (F : Graph n) (rate : ℕ → ℝ) (T j : ℕ) (hj : j ≤ T)
    (hstep : ∀ i < T, ∀ G, safe i G →
      pmfMean (step G) (intact F) ≤ Real.exp (rate i) * intact F G) :
    pmfMean (historyLaw initial (fun _ => step) T j)
      (fun ω => if historyAlive safe T j ω then intact F (ω (historyIndex T j)) else 0) ≤
      Real.exp (∑ i ∈ Finset.range j, rate i) * pmfMean initial (intact F) := by
  classical
  have h := history_alive_mean_le initial (fun _ => step) safe (intact F)
    (intact_nonnegative F) (fun i => Real.exp (rate i)) (fun i => (Real.exp_pos _).le)
    T hstep j hj
  simpa only [← Real.exp_sum] using h

end SharpTerminalLeave
end
end

end OAI
