import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.RationalUpdate
import OAI.Combinatorics.MatchingCount.Algorithm.FiniteTrialLaw

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Initializer
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _
structure Layer (p : Trial.Parameters G) (j : ℕ) where
  Ω : Type
  finite : Fintype Ω
  law : @Law Ω finite
  state : Ω → ScaleState G j
  ratios : Ω → Fin j → ℚ
  ratios_nonneg : ∀ x i,0 ≤ ratios x i

attribute [instance] Layer.finite

noncomputable def Layer.good (p : Trial.Parameters G) {j : ℕ} (L : Layer p j) (x : L.Ω) : Prop :=
  (L.state x).Balanced p.hn ∧ ∀ i : Fin j,
    |(L.ratios x i:ℝ)/(partition (Trial.raw G (i.val+1)) ∅/partition (Trial.raw G i.val) ∅)-1| ≤ (p.epsilon:ℝ)/(100*p.K)

noncomputable def firstLayer (p : Trial.Parameters G) : Layer p 0 where
  Ω := PUnit
  finite := inferInstance
  law := ⟨fun _=>1,fun _=>by norm_num,by simp⟩
  state _ := initialScaleState G p.hn
  ratios _ := Fin.elim0
  ratios_nonneg _ i := Fin.elim0 i

noncomputable def Layer.append (p : Trial.Parameters G) {j : ℕ} (hj : j ≤ p.K) (L : Layer p j) : Layer p (j+1) where
  Ω := Σ x : L.Ω, Fin p.S → SourceMarked (fun a b=>((L.state x).activity a b:ℝ)) p.K
  finite := inferInstance
  law := L.law.sigma (fun x=>(L.state x).sampleLaw p hj)
  state x := (L.state x.1).update p.hn (RationalSource.sourceMarkedEquiv (L.state x.1).activity p.K ∘ x.2)
  ratios x := Fin.snoc (L.ratios x.1) ((L.state x.1).ratioEstimate (RationalSource.sourceMarkedEquiv (L.state x.1).activity p.K ∘ x.2))
  ratios_nonneg x i := by
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simpa using (L.state x.1).ratioEstimate_nonneg x.2
    · simpa using L.ratios_nonneg x.1 i

theorem Layer.append_good (p : Trial.Parameters G) {j : ℕ} (hj : j ≤ p.K) (L : Layer p j) (x : L.Ω)
    (hx : L.good p x) (y : Fin p.S → SourceMarked (fun a b=>((L.state x).activity a b:ℝ)) p.K)
    (hy : StageGood (fun a b=>((L.state x).activity a b:ℝ)) (fun a b=>((L.state x).nextActivity a b:ℝ)) p.K p.sigma y) :
    (L.append p hj).good p ⟨x,y⟩ := by
  have h := successful_update p hj (L.state x) hx.1 y hy
  refine ⟨h.1,?_⟩
  intro i
  refine Fin.lastCases ?_ (fun i=>?_) i
  · simpa [Layer.append] using h.2
  · simpa [Layer.append] using hx.2 i

theorem Layer.append_failure (p : Trial.Parameters G) {j : ℕ} (hj : j ≤ p.K) (L : Layer p j) :
    (L.append p hj).law.event (fun x=>¬(L.append p hj).good p x) ≤
      L.law.event (fun x=>¬L.good p x)+13/(1000*p.K) := by
  apply first_failure_sigma L.law (fun x=>(L.state x).sampleLaw p hj) (L.good p)
    ((L.append p hj).good p) _ (by positivity)
  intro x hx
  apply le_trans ((L.state x).sampleLaw p hj |>.event_mono ?_)
    ((L.state x).sampleLaw_budget p hj).le
  intro y hy hgood
  exact hy (L.append_good p hj x hx y hgood)

noncomputable def layers (p : Trial.Parameters G) : (j : ℕ) → j ≤ p.K → Layer p j
  | 0, _ => firstLayer p
  | j+1, h => (layers p j (by omega)).append p (by omega)

theorem layers_failure (p : Trial.Parameters G) (j : ℕ) (hj : j ≤ p.K) :
    (layers p j hj).law.event (fun x=>¬(layers p j hj).good p x) ≤ j*(13/(1000*p.K)) := by
  induction j with
  | zero =>
    have hg : ∀ x,(firstLayer p).good p x := by
      intro x
      constructor
      · exact initial_balanced p.hn p.even
      · intro i; exact Fin.elim0 i
    simp [layers,Law.event,hg]
  | succ j ih =>
    refine le_trans ((layers p j (by omega)).append_failure p (by omega)) ?_
    calc
      _ ≤ (j:ℝ)*(13/(1000*p.K))+13/(1000*p.K) := by linarith only [ih (by omega)]
      _ = _ := by push_cast; ring

noncomputable def output (p : Trial.Parameters G) (x : (layers p p.K le_rfl).Ω) : ℚ :=
  (Z (completeGraph G.n):ℚ)*∏ i,(layers p p.K le_rfl).ratios x i

lemma output_nonneg (p : Trial.Parameters G) (x : (layers p p.K le_rfl).Ω) : 0 ≤ output p x := by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact prod_nonneg fun i _=>(layers p p.K le_rfl).ratios_nonneg x i

def Accurate (p : Trial.Parameters G) (y : ℚ) : Prop :=
  (1-p.epsilon)*(Z G:ℚ)≤y ∧ y≤(1+p.epsilon)*(Z G:ℚ)

theorem good_output (p : Trial.Parameters G) (hZ : 0<Z G) (x : (layers p p.K le_rfl).Ω)
    (hx : (layers p p.K le_rfl).good p x) : Accurate p (output p x) := by
  have h:=Trial.final_trial_interval G p.even p.epsilon p.epsilon_pos p.epsilon_lt_one p.K p.schedule hZ
    (fun i=>((layers p p.K le_rfl).ratios x i:ℝ)) hx.2
  unfold Accurate output
  dsimp only at h
  exact_mod_cast h

theorem actual_finite_trial_failure (p : Trial.Parameters G) (hZ : 0<Z G) :
    (layers p p.K le_rfl).law.event (fun x=>¬Accurate p (output p x)) ≤ 13/1000 := by
  have hh := layers_failure p p.K le_rfl
  have he : (p.K:ℝ)*(13/(1000*p.K))=13/1000 := by
    have hk : (p.K:ℝ)≠0 := by exact_mod_cast p.K_pos.ne'
    rw [←mul_div_assoc,mul_comm (1000:ℝ),mul_div_mul_left _ _ hk]
  rw [he] at hh
  apply le_trans ((layers p p.K le_rfl).law.event_mono ?_) hh
  intro x hx hg
  exact hx (good_output p hZ x hg)

end MatchingFPRAS.FiniteTrial

end OAI
