import Mathlib
import OAI.Probability.SKGap.Terminal.FinitePairTail
import OAI.Probability.SKGap.Localization.SmoothSelection

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

def cutoffWeight (C : ℕ→ℝ) (k : ℕ) : ℝ := C k*∏i∈Finset.range k,(1-C i)
def cutoffDeficit (C : ℕ→ℝ) (d : ℕ) : ℝ := 1-∑k∈Finset.range d,cutoffWeight C k

lemma cutoffDeficit_prod (C : ℕ→ℝ) (d : ℕ) :
    cutoffDeficit C d=∏k∈Finset.range d,(1-C k) := by
  induction d with
  | zero=>simp [cutoffDeficit]
  | succ d ih=>
    simp only [cutoffDeficit,Finset.sum_range_succ] at ih ⊢
    rw [Finset.prod_range_succ,cutoffWeight,←ih]
    ring

lemma cutoffDeficit_bounds (C : ℕ→ℝ) (d : ℕ) (hC : ∀k,0≤C k ∧ C k≤1) :
    0≤cutoffDeficit C d ∧ cutoffDeficit C d≤1 := by
  rw [cutoffDeficit_prod]
  refine ⟨Finset.prod_nonneg (fun k _=>sub_nonneg.mpr (hC k).2),?_⟩
  exact Finset.prod_le_one₀ (fun k _=>sub_nonneg.mpr (hC k).2) (fun k _=>by linarith [(hC k).1])

lemma cutoffWeight_bounds (C : ℕ→ℝ) (k : ℕ) (hC : ∀k,0≤C k ∧ C k≤1) :
    0≤cutoffWeight C k ∧ cutoffWeight C k≤C k := by
  have H:=cutoffDeficit_bounds C k hC
  rw [cutoffDeficit_prod] at H
  exact ⟨mul_nonneg (hC k).1 H.1,mul_le_of_le_one_right (hC k).1 H.2⟩

lemma cutoffDeficit_zero_of_one {C : ℕ→ℝ} {d k : ℕ} (hk : k<d) (hC : C k=1) : cutoffDeficit C d=0 := by
  rw [cutoffDeficit_prod]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hk) (by simp [hC])

lemma residualCutoff_deficit_inclusion (hn : 0<n) {j ρ ε : ℝ} (hρ : 0<ρ)
    (J : Interaction n) (h : Fin n→ℝ) (m : ℕ) (x : Spin n)
    (hm : 2<(m:ℝ)*ρ^2/4) (he : 2*(2*m:ℕ)*ε≤1)
    (hD : 0<cutoffDeficit (fun k=>residualCutoff ρ j J h k x) (2*m-1)) :
    ∃k:Fin (2*m),ε < |primaryPair j J h k x|/Real.sqrt (n:ℝ) := by
  by_contra hh
  have hs : ∀k<2*m,|primaryPair j J h k x|/Real.sqrt (n:ℝ)≤ε := by
    intro k hk
    exact le_of_not_gt (fun H=>hh ⟨⟨k,hk⟩,H⟩)
  obtain ⟨k,hk,h0,h1⟩:=small_residual_pair hn j J h m x hρ hm he hs
  have hC:=residualCutoff_one hn hρ J h (2*k) x h0 h1
  have hz:=cutoffDeficit_zero_of_one (C:=fun k=>residualCutoff ρ j J h k x) (by omega : 2*k<2*m-1) hC
  linarith

lemma weighted_indicator_mono (w : Spin n→ℝ) (hw : ∀x,0≤w x) (P Q : Spin n→Prop)
    [DecidablePred P] [DecidablePred Q] (hh : ∀x,P x→Q x) :
    (∑x,if P x then w x else 0)≤∑x,if Q x then w x else 0 := by
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hp hq
  · exact le_rfl
  · exact False.elim (hq (hh x hp))
  · exact hw x
  · exact le_rfl

universe u
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C ρ ε : ℝ}
variable {J : ∀a,Interaction (N a)} {h : ∀a,Fin (N a)→ℝ}

theorem gibbs_residual_selection_tail (m : ℕ) (hρ : 0<ρ) (hε : 0<ε)
    (hm : 2<(m:ℝ)*ρ^2/4) (he : 2*(2*m:ℕ)*ε≤1)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J a)) :
    ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀a,
      (∑x,if 0<cutoffDeficit (fun k=>residualCutoff ρ j (J a) (h a) k x) (2*m-1)
        then fieldGibbs (J a) (h a) x else 0)≤C₁/(N a:ℝ) ∧
      ∀f : Observables (N a),
      (∑x,if 0<cutoffDeficit (fun k=>residualCutoff ρ j (J a) (h a) k x) (2*m-1)
        then fieldGibbs (J a) (h a) x*(f x)^2 else 0)≤
        C₂/Real.sqrt (N a:ℝ)*starSquared (fieldGibbs (J a) (h a)) f := by
  classical
  obtain ⟨C₁,C₂,hC₁,hC₂,ht⟩:=gibbs_pairing_tail (h:=h) (2*m) hε hR hB hW hC hn hJ hdiag hevent
  refine ⟨C₁,C₂,hC₁,hC₂,fun a=>⟨?_,fun f=>?_⟩⟩
  · exact (weighted_indicator_mono _ (fun x=>(fieldGibbs_pos _ _ _).le) _ _
      (fun x=>residualCutoff_deficit_inclusion (hn a) hρ (J a) (h a) m x hm he)).trans (ht a).1
  · exact (weighted_indicator_mono _ (fun x=>mul_nonneg (fieldGibbs_pos _ _ _).le (sq_nonneg _)) _ _
      (fun x=>residualCutoff_deficit_inclusion (hn a) hρ (J a) (h a) m x hm he)).trans ((ht a).2 f)

end SKGapCutoff.Recipe

end
end

end OAI
