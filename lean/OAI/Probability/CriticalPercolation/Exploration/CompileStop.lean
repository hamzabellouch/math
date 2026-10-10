import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.PrefixState
import OAI.Probability.CriticalPercolation.Exploration.ScoreMeanStep

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] in
lemma compile_stop (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (hh : ∃ v ∈ st.reached, v ∈ B) :
    compile G order B fuel st stack = .done st := by
  cases fuel with
  | zero => rfl
  | succ n => rw [compile.eq_def]; exact ite_eq_left hh

theorem compile_score_second (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (a t : V) (fuel : ℕ) (st : State V E)
    (stack : List (Dart V E)) (hrank : rank order st stack ≤ fuel)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (fresh : Fresh w p st.read) (hs : PrefixState G a st w) :
    expect w (fun ω => ((compile G order {t} fuel st stack).score p (G.connects a t) w ω)^2) ≤
      3*expect w ((compile G order {t} fuel st stack).score p (G.connects a t) w) := by
  induction fuel generalizing st stack w with
  | zero =>
    change expect w (fun _ : E → Prop => (0:ℝ)^2) ≤ 3*expect w (fun _ : E → Prop => (0:ℝ))
    simp only [zero_pow (by omega : 2 ≠ 0),expect_const w hw 0,mul_zero,le_refl]
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · change expect w (fun _ : E → Prop => (0:ℝ)^2) ≤ 3*expect w (fun _ : E → Prop => (0:ℝ))
      simp only [zero_pow (by omega : 2 ≠ 0),expect_const w hw 0,mul_zero,le_refl]
    · cases stack with
      | nil =>
        change expect w (fun _ : E → Prop => (0:ℝ)^2) ≤ 3*expect w (fun _ : E → Prop => (0:ℝ))
        simp only [zero_pow (by omega : 2 ≠ 0),expect_const w hw 0,mul_zero,le_refl]
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · apply ih st rest (by have := rank_pop order st d rest; omega) w hw hn fresh hs
        · have hz : d.2.2 ∉ st.reached := fun hz => hd (Or.inl hz)
          have hf : d.2.1 ∉ st.read := fun hf => hd (Or.inr (Or.inl hf))
          have hv : d.1 ∈ st.reached := by tauto
          have he : G.ends d.2.1 = s(d.1,d.2.2) := by tauto
          have ht : t ∉ st.reached := fun ht => hh ⟨t,ht,Set.mem_singleton t⟩
          have hb := fresh d.2.1 hf
          have h0 : w d.2.1 False ≠ 0 := by rw [hb.1]; exact (sub_pos.mpr hp.2).ne'
          have h1 : w d.2.1 True ≠ 0 := by rw [hb.2]; exact hp.1.ne'
          have hrc : rank order (st.closed d.2.1) rest ≤ n := by
            have := rank_closed order st d rest
            omega
          have hro : rank order (st.opened d.2.1 d.2.2) (push G order d.2.2++rest) ≤ n := by
            have := rank_opened G order st d rest hz
            omega
          have hrp : rank order (st.opened d.2.1 d.2.2) (push G order d.2.2) ≤ n := by
            unfold rank at hro ⊢
            simp only [List.length_append] at hro
            omega
          have hpair : expect (pin w d.2.1 True) (fun ω =>
              if openPivot (G.connects a t) d.2.1 ω then
                (compile G order {t} n (st.opened d.2.1 d.2.2) (push G order d.2.2++rest)).score p
                  (G.connects a t) (pin w d.2.1 True) ω else 0) ≤ delta w (G.connects a t) d.2.1 := by
            by_cases hzt : d.2.2 = t
            · have hstop := compile_stop G order {t} n (st.opened d.2.1 d.2.2)
                (push G order d.2.2++rest) ⟨t,by simp [State.opened,hzt],Set.mem_singleton t⟩
              simp only [hstop,score,ite_self,expect_const _ (pin_normalized w hw d.2.1 True) 0]
              exact (delta_unit w hw hn d.2.1 h0 h1 _ (G.connects_mono a t)).1
            · exact future_pair_bound G order ho a t d.1 d.2.2 d.2.1 st rest n
                hv hz ht hzt hf he hrp hp w hw hn fresh hs
          have hstep := score_second_step d.2.1
            (compile G order {t} n (st.closed d.2.1) rest)
            (compile G order {t} n (st.opened d.2.1 d.2.2) (push G order d.2.2++rest))
            hp w hw hn hb.1 hb.2 (G.connects a t) (G.connects_mono a t) hpair
          have hc := ih (st.closed d.2.1) rest hrc (pin w d.2.1 False)
            (pin_normalized w hw d.2.1 False) (pin_nonneg w hn d.2.1 False)
            (fresh_pin w p st.read fresh d.2.1 False) (prefixState_closed G a st w hs d.2.1 h0)
          have ho' := ih (st.opened d.2.1 d.2.2) (push G order d.2.2++rest) hro (pin w d.2.1 True)
            (pin_normalized w hw d.2.1 True) (pin_nonneg w hn d.2.1 True)
            (fresh_pin w p st.read fresh d.2.1 True) (prefixState_opened G a st w hs d.2.1 d.1 d.2.2 hv he h1)
          rw [score_mean_step _ _ _ hp w hw hb.1 hb.2 _ (G.connects_mono a t)]
          have hc' := mul_le_mul_of_nonneg_left hc (sub_pos.mpr hp.2).le
          have ho'' := mul_le_mul_of_nonneg_left ho' hp.1.le
          linarith

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem search_pivotal_moments (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (a t : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    expect w ((search G order a {t}).score p (G.connects a t) w) ≤ 1 ∧
      expect w (fun ω => ((search G order a {t}).score p (G.connects a t) w ω)^2) ≤ 3 := by
  have hw : ∀ e, ∑ b, w e b = 1 := by
    intro e
    simp [Fintype.univ_Prop,h0,h1]
  have hn : ∀ e b, 0 ≤ w e b := by
    intro e b
    by_cases hb : b
    · have : b = True := propext (iff_true_intro hb)
      rw [this,h1]; exact hp.1.le
    · have : b = False := propext (iff_false_intro hb)
      rw [this,h0]; exact (sub_pos.mpr hp.2).le
  have hf : Fresh w p (initial (E := E) a).read := fun e _ => ⟨h0 e,h1 e⟩
  have hm := score_mean_le_variance (search G order a {t}) (initial a).read
    (compile_valid G order {t} _ _ _) hp w hw hn hf _ (G.connects_mono a t)
  have hmean := hm.trans (variance_le_one w hw hn _)
  refine ⟨hmean,?_⟩
  have hs := compile_score_second G order ho a t _ (initial a) (push G order a)
    le_rfl hp w hw hn hf (prefixState_initial G a w)
  change _ ≤ 3*expect w ((search G order a {t}).score p (G.connects a t) w) at hs
  exact hs.trans (by linarith)

end CriticalPercolation.LazyDFS

end
end

end OAI
