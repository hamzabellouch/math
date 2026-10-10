import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.OutputDef
import OAI.Computability.DirectedFeedback.RankGraph.LastBias

namespace OAI

noncomputable section
open scoped BigOperators
open scoped Classical BigOperators
open scoped Classical
open scoped Classical
open scoped Classical BigOperators
open scoped BigOperators
open scoped BigOperators
open DirectedFeedback.SourceProbability
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal Ranks
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

theorem parameterized_soundness {D : ℕ} (P : Parameters D) (R : RankParameters P X)
    (G : Game U V E X Y) (hYX : Fintype.card Y ≤ Fintype.card X)
    (fiber : E → X ≃ Y × Bool) (hproj : ∀ e x, (fiber e x).1 = G.project e x)
    (hsound : G.Sound P.theta)
    (F : Finset (OutputVertex (M := P.M) G R.law))
    (hF : FeedbackR (OutputArc G R.law hYX fiber) F) :
    (D:ℝ) < totalDeletionCost G R.law D (8*((D:ℝ)+1)) P.K (fun v => decide (v ∈ F)) := by
  apply weighted_soundness (J := P.J) G R.law hYX fiber hproj D (8*((D:ℝ)+1)) P.K
    R.eta R.rho (lastBias P.M/1000) P.theta (Nat.cast_nonneg _) (by positivity)
    (by exact_mod_cast P.K_pos) R.eta_pos.le P.gamma_pos
  · exact_mod_cast P.M_eq
  · exact R.accuracy
  · exact R.spreads
  · exact R.rho_alphabet
  · exact R.rho_nonneg
  · exact P.full_error R.rho R.rho_small
  · exact P.J_pos
  · exact P.junta
  · exact P.product_error R.rho R.rho_small
  · exact hsound
  · exact hF

theorem parameterized_completeness {D : ℕ} (P : Parameters D) (R : RankParameters P X)
    (G : Game U V E X Y) (hYX : Fintype.card Y ≤ Fintype.card X)
    (fiber : E → X ≃ Y × Bool) (hproj : ∀ e x, (fiber e x).1 = G.project e x)
    (ellU : U → X) (ellV : V → Y) (hscore : 1-(P.theta:ℝ) ≤ G.score ellU ellV) :
    ∃ F : Finset (OutputVertex (M := P.M) G R.law),
      FeedbackR (OutputArc G R.law hYX fiber) F ∧
      totalDeletionCost G R.law D (8*((D:ℝ)+1)) P.K (fun v => decide (v ∈ F)) ≤ 4 := by
  refine ⟨labelFeedback (M := P.M) G R.law hYX fiber ellU ellV,
    labelFeedback_spec G R.law hYX fiber ellU ellV, ?_⟩
  rw [labelFeedback_indicator]
  have hh := weighted_completeness (M := P.M) G R.law hYX fiber ellU ellV hproj
      D (8*((D:ℝ)+1)) P.K (by positivity) (by exact_mod_cast P.K_pos.le)
  have hloss : (P.K:ℝ)*(1-G.score ellU ellV) ≤ (P.K:ℝ)*P.theta :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  linarith [P.fullChernoff,P.Ktheta]

end DirectedFeedback.Construction

open scoped Classical BigOperators
namespace DirectedFeedback

def Rational (x : ℝ) : Prop := ∃ q : ℚ, x = q
namespace Rational

theorem rat (q : ℚ) : Rational (q:ℝ) := ⟨q,rfl⟩
theorem nat (n : ℕ) : Rational (n:ℝ) := ⟨n,by simp⟩
theorem zero : Rational 0 := ⟨0,by simp⟩
theorem one : Rational 1 := ⟨1,by simp⟩
theorem add {x y : ℝ} (hx : Rational x) (hy : Rational y) : Rational (x+y) := by
  obtain ⟨a,rfl⟩ := hx; obtain ⟨b,rfl⟩ := hy
  exact ⟨a+b,by simp⟩
theorem sub {x y : ℝ} (hx : Rational x) (hy : Rational y) : Rational (x-y) := by
  obtain ⟨a,rfl⟩ := hx; obtain ⟨b,rfl⟩ := hy
  exact ⟨a-b,by simp⟩
theorem mul {x y : ℝ} (hx : Rational x) (hy : Rational y) : Rational (x*y) := by
  obtain ⟨a,rfl⟩ := hx; obtain ⟨b,rfl⟩ := hy
  exact ⟨a*b,by simp⟩
theorem inv {x : ℝ} (hx : Rational x) : Rational x⁻¹ := by
  obtain ⟨a,rfl⟩ := hx
  exact ⟨a⁻¹,by simp⟩
theorem div {x y : ℝ} (hx : Rational x) (hy : Rational y) : Rational (x/y) := by
  simpa only [div_eq_mul_inv] using hx.mul hy.inv
theorem pow {x : ℝ} (hx : Rational x) (n : ℕ) : Rational (x^n) := by
  obtain ⟨a,rfl⟩ := hx
  exact ⟨a^n,by simp⟩
theorem sum {I : Type*} (s : Finset I) (f : I → ℝ) (h : ∀ i ∈ s, Rational (f i)) :
    Rational (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih (fun i hi => h i (by simp [hi])))
theorem prod {I : Type*} (s : Finset I) (f : I → ℝ) (h : ∀ i ∈ s, Rational (f i)) :
    Rational (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using one
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (by simp)).mul (ih (fun i hi => h i (by simp [hi])))
end Rational
end DirectedFeedback

namespace DirectedFeedback.SourceProbability.FiniteDistribution
open DirectedFeedback
variable {I J : Type*} [Fintype I] [Fintype J]
def RationalMass (μ : FiniteDistribution I) : Prop := ∀ i, Rational (μ.weight i)

theorem RationalMass.uniform [Nonempty I] : RationalMass (uniform I) :=
  fun _ => Rational.one.div (Rational.nat _)

theorem RationalMass.product {μ : FiniteDistribution I} {ν : FiniteDistribution J}
    (hμ : μ.RationalMass) (hν : ν.RationalMass) : (μ.product ν).RationalMass :=
  fun x => (hμ x.1).mul (hν x.2)

theorem RationalMass.sigma {F : I → Type*} [∀ i, Fintype (F i)]
    {μ : FiniteDistribution I} {ν : ∀ i, FiniteDistribution (F i)}
    (hμ : μ.RationalMass) (hν : ∀ i, (ν i).RationalMass) : (μ.sigma ν).RationalMass :=
  fun x => (hμ x.1).mul (hν x.1 x.2)

theorem RationalMass.iid {μ : FiniteDistribution I} (hμ : μ.RationalMass) (n : ℕ) :
    (μ.iid n).RationalMass := by
  intro x
  change Rational (∏ i : Fin n, μ.weight (x i))
  exact Rational.prod _ _ (fun i _ => hμ (x i))

theorem RationalMass.table {μ : I → FiniteDistribution J}
    (hμ : ∀ i, (μ i).RationalMass) : (table μ).RationalMass :=
  fun x => Rational.prod _ _ (fun i _ => hμ i (x i))

theorem RationalMass.pushforward {μ : FiniteDistribution I} (hμ : μ.RationalMass)
    (f : I → J) : (μ.pushforward f).RationalMass := by
  intro j
  apply Rational.sum
  intro i _
  split_ifs
  · exact hμ i
  · exact Rational.zero

end DirectedFeedback.SourceProbability.FiniteDistribution

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

omit [NeZero M] [NeZero T] [Nonempty X] in
theorem subsetLaw_rational (i : Fin M) : (subsetLaw (X:=X) i).RationalMass := by
  apply RationalMass.table
  intro _ b
  change Rational (if b then bias i else 1-bias i)
  have hp : Rational (bias i) := (Rational.nat 2).inv.pow _
  split_ifs
  · exact hp
  · exact Rational.one.sub hp

variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
    (hG : G.edgeLaw.RationalMass) (hψ : ψLaw.RationalMass)
include hG hψ

omit [Fintype V] [Fintype Y] [Nonempty X] [Nonempty Y] in
theorem common_rational : (common (M:=M) G ψLaw).RationalMass := by
  apply hψ.product
  apply RationalMass.uniform.sigma
  intro t
  apply RationalMass.iid
  exact (hG.pushforward G.left).product (RationalMass.uniform.sigma (fun i => subsetLaw_rational i))

omit [Fintype V] [Fintype Y] [Nonempty X] [Nonempty Y] [NeZero T] in
theorem fullLaw_rational : (fullLaw (M:=M) G ψLaw).RationalMass := by
  apply hψ.product
  apply RationalMass.iid
  exact (hG.pushforward G.left).product (RationalMass.uniform.sigma (fun i => subsetLaw_rational i))

omit [Fintype V] [Fintype Y] [Nonempty Y] in
theorem bigLaw_rational : (bigLaw (M:=M) G ψLaw).RationalMass := by
  apply (common_rational G ψLaw hG hψ).product
  exact (hG.pushforward G.left).product (RationalMass.uniform.sigma (fun _ => RationalMass.uniform))

omit [Nonempty X] in
theorem smallLaw_rational : (smallLaw (M:=M) G ψLaw).RationalMass := by
  apply (common_rational G ψLaw hG hψ).product
  exact (hG.pushforward G.right).product (RationalMass.uniform.sigma (fun _ => RationalMass.uniform))

omit [Fintype V] [Nonempty X] [Nonempty Y] in
theorem comparisonLaw_rational : (comparisonLaw (M:=M) G ψLaw).RationalMass := by
  apply (common_rational G ψLaw hG hψ).sigma
  intro d
  apply hG.product
  apply RationalMass.uniform.sigma
  intro i
  apply RationalMass.uniform.product
  apply RationalMass.table
  intro _ b
  obtain ⟨⟨b₁,b₂⟩,b₃⟩ := b
  have hp : Rational (bias i) := (Rational.nat 2).inv.pow _
  have h1 := Rational.one.sub hp
  cases b₁ <;> cases b₂ <;> cases b₃ <;>
    first | exact Rational.one.sub ((Rational.nat 2).mul hp)
          | exact hp.pow 2 | exact hp.mul h1 | exact Rational.zero

theorem vertexCost_rational (D H K : ℕ)
    (v : OutputVertex (M:=M) G ψLaw) : Rational (vertexCost G ψLaw D H K v) := by
  rcases v with r | (d | d)
  · exact (Rational.nat D).add Rational.one
  · rcases d with d | (d | d)
    · exact (Rational.nat H).mul (fullLaw_rational G ψLaw hG hψ d.val)
    · exact (Rational.nat _).mul (bigLaw_rational G ψLaw hG hψ d.val)
    · exact (Rational.nat _).mul (smallLaw_rational G ψLaw hG hψ d.val)
  · exact (Rational.nat K).mul (comparisonLaw_rational G ψLaw hG hψ d.val)

end DirectedFeedback.Construction

open scoped Classical BigOperators
namespace DirectedFeedback

namespace Digraph

theorem dfvs_le_iff (G : Digraph) (k : ℕ) :
    G.dfvs ≤ k ↔ ∃ F : Finset (Fin G.n), G.Feedback F ∧ F.card ≤ k := by
  constructor
  · intro hk
    obtain ⟨F,hF,hcard⟩ := Nat.find_spec
      (show ∃ k : ℕ, ∃ F : Finset (Fin G.n), G.Feedback F ∧ F.card = k from
        ⟨G.n,Finset.univ,by intro r c _; exact ⟨0,Finset.mem_univ _⟩,by simp⟩)
    exact ⟨F,hF,hcard.trans_le hk⟩
  · rintro ⟨F,hF,hcard⟩
    exact (Nat.find_min' _ ⟨F,hF,rfl⟩).trans hcard

theorem dfvs_attained (G : Digraph) :
    ∃ F : Finset (Fin G.n), G.Feedback F ∧ F.card = G.dfvs := by
  exact Nat.find_spec
    (show ∃ k : ℕ, ∃ F : Finset (Fin G.n), G.Feedback F ∧ F.card = k from
      ⟨G.n,Finset.univ,by intro r c _; exact ⟨0,Finset.mem_univ _⟩,by simp⟩)

end Digraph

def graphOfRelation {V : Type} [Fintype V] (R : V → V → Prop)
    (hR : ∀ v, ¬R v v) : Digraph where
  n := Fintype.card V
  arcs := ((Finset.univ : Finset (Fin (Fintype.card V) × Fin (Fintype.card V))).filter
    (fun e => R ((Fintype.equivFin V).symm e.1) ((Fintype.equivFin V).symm e.2))).toList
  loopless := by
    intro e he heq
    simp only [Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and] at he
    rw [heq] at he
    exact hR _ he
  nodup := Finset.nodup_toList _

@[simp] theorem graphOfRelation_mem {V : Type} [Fintype V] (R : V → V → Prop)
    (hR : ∀ v, ¬R v v) (a b : Fin (Fintype.card V)) :
    (a,b) ∈ (graphOfRelation R hR).arcs ↔
      R ((Fintype.equivFin V).symm a) ((Fintype.equivFin V).symm b) := by
  change (a,b) ∈ ((Finset.univ : Finset (Fin (Fintype.card V) × Fin (Fintype.card V))).filter
    (fun e => R ((Fintype.equivFin V).symm e.1) ((Fintype.equivFin V).symm e.2))).toList ↔ _
  rw [Finset.mem_toList,Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]

theorem graphOfRelation_feedback {V : Type} [Fintype V] (R : V → V → Prop)
    (hR : ∀ v, ¬R v v) (F : Finset V) (hF : FeedbackR R F) :
    (graphOfRelation R hR).Feedback (F.map (Fintype.equivFin V).toEmbedding) := by
  intro n c hc
  obtain ⟨i,hi⟩ := hF n ((Fintype.equivFin V).symm ∘ c)
    ((Fintype.equivFin V).symm.injective.comp hc.1)
    (fun i => (graphOfRelation_mem R hR _ _).mp (hc.2 i))
  refine ⟨i,Finset.mem_map.mpr ⟨_,hi,?_⟩⟩
  exact (Fintype.equivFin V).apply_symm_apply _

theorem relation_feedback_of_graph {V : Type} [Fintype V] (R : V → V → Prop)
    (hR : ∀ v, ¬R v v) (F : Finset (Fin (Fintype.card V)))
    (hF : (graphOfRelation R hR).Feedback F) :
    FeedbackR R (F.map (Fintype.equivFin V).symm.toEmbedding) := by
  intro n c hcinj hc
  obtain ⟨i,hi⟩ := hF n ((Fintype.equivFin V) ∘ c) ⟨
    ((Fintype.equivFin V).injective.comp hcinj),fun i => by
      apply (graphOfRelation_mem R hR _ _).mpr
      change R ((Fintype.equivFin V).symm ((Fintype.equivFin V) (c i)))
        ((Fintype.equivFin V).symm ((Fintype.equivFin V) (c (i+1))))
      simpa only [Equiv.symm_apply_apply] using hc i⟩
  refine ⟨i,Finset.mem_map.mpr ⟨_,hi,?_⟩⟩
  exact (Fintype.equivFin V).symm_apply_apply _

theorem graphOfRelation_dfvs_le_iff {V : Type} [Fintype V] (R : V → V → Prop)
    (hR : ∀ v, ¬R v v) (k : ℕ) :
    (graphOfRelation R hR).dfvs ≤ k ↔ ∃ F : Finset V, FeedbackR R F ∧ F.card ≤ k := by
  rw [Digraph.dfvs_le_iff]
  change (∃ F : Finset (Fin (Fintype.card V)), (graphOfRelation R hR).Feedback F ∧ F.card ≤ k) ↔ _
  constructor
  · rintro ⟨F,hF,hcard⟩
    exact ⟨F.map (Fintype.equivFin V).symm.toEmbedding,
      relation_feedback_of_graph R hR F hF,by simpa using hcard⟩
  · rintro ⟨F,hF,hcard⟩
    exact ⟨F.map (Fintype.equivFin V).toEmbedding,
      graphOfRelation_feedback R hR F hF,by simpa using hcard⟩

theorem cloneRel_irrefl {V : Type} (R : V → V → Prop) (hR : ∀ v, ¬R v v) (c : V → ℕ) :
    ∀ v, ¬cloneRel R c v v := fun v => hR v.1

def roundedGraph {V : Type} [Fintype V] (R : V → V → Prop) (hR : ∀ v, ¬R v v)
    (w : V → ℚ) : Digraph :=
  graphOfRelation (cloneRel R (roundCopies (Fintype.card V) w)) (cloneRel_irrefl R hR _)

theorem roundedGraph_yes {V : Type} [Fintype V] (R : V → V → Prop)
    (hR : ∀ v, ¬R v v) (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (hyes : ∃ F : Finset V, FeedbackR R F ∧ (∑ v ∈ F, w v) ≤ 4) :
    (roundedGraph R hR w).dfvs ≤ 5*Fintype.card V := by
  obtain ⟨F,hF,hcost⟩ := hyes
  obtain ⟨Q,hQ,hcard⟩ := rounded_clone_completeness R w hw F hF 4 hcost
  rw [roundedGraph,graphOfRelation_dfvs_le_iff]
  refine ⟨Q,hQ,?_⟩
  have hh : (Q.card:ℚ) ≤ 5*Fintype.card V := by linarith
  exact_mod_cast hh

theorem roundedGraph_no {V : Type} [Fintype V] [Nonempty V] (R : V → V → Prop)
    (hR : ∀ v, ¬R v v) (w : V → ℚ) (b : ℚ)
    (hno : ∀ F : Finset V, FeedbackR R F → b < ∑ v ∈ F, w v) :
    (Fintype.card V : ℚ)*b < (roundedGraph R hR w).dfvs := by
  obtain ⟨Q,hQ,hcard⟩ := (graphOfRelation_dfvs_le_iff
    (cloneRel R (roundCopies (Fintype.card V) w)) (cloneRel_irrefl R hR _)
    (roundedGraph R hR w).dfvs).mp le_rfl
  have hb := rounded_clone_soundness R w (Fintype.card V) Fintype.card_pos b hno Q hQ
  exact hb.trans_le (by exact_mod_cast hcard)

end DirectedFeedback

open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal Ranks
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {D : ℕ} (P : Parameters D) (R : RankParameters P X)
  (G : Game U V E X Y) (hG : G.edgeLaw.RationalMass)

def rationalCost (v : OutputVertex (M := P.M) G R.law) : ℚ :=
  (vertexCost_rational G R.law hG R.rational D (8*(D+1)) P.K v).choose

theorem rationalCost_cast (v : OutputVertex (M := P.M) G R.law) :
    (rationalCost P R G hG v : ℝ) = vertexCost G R.law D (8*((D:ℝ)+1)) P.K v := by
  have h := (vertexCost_rational G R.law hG R.rational D (8*(D+1)) P.K v).choose_spec
  exact h.symm.trans (by congr 1; push_cast; rfl)

theorem rationalCost_pos (v : OutputVertex (M := P.M) G R.law) :
    0 < rationalCost P R G hG v := by
  have hp := vertexCost_pos G R.law (D:ℝ) (8*((D:ℝ)+1)) P.K
    (Nat.cast_nonneg _) (by positivity) (by exact_mod_cast P.K_pos) v
  rw [← rationalCost_cast P R G hG v] at hp
  exact_mod_cast hp

theorem cost_sum (F : Finset (OutputVertex (M := P.M) G R.law)) :
    ((∑ v ∈ F, rationalCost P R G hG v : ℚ) : ℝ) =
      totalDeletionCost G R.law D (8*((D:ℝ)+1)) P.K (fun v => decide (v ∈ F)) := by
  simp [totalDeletionCost, ← rationalCost_cast P R G hG]

instance parameterized_output_nonempty : Nonempty (OutputVertex (M := P.M) G R.law) := by
  obtain ⟨w⟩ := (fullLaw (M := P.M) G R.law).support_nonempty
  exact ⟨.inr (.inl (.inl w))⟩

variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)

def unweightedInstance : GapInstance where
  graph := roundedGraph (OutputArc G R.law hYX fiber) (output_loopless G R.law hYX fiber)
    (rationalCost P R G hG)
  k := 5 * Fintype.card (OutputVertex (M := P.M) G R.law)
  k_pos := Nat.mul_pos (by decide) Fintype.card_pos

theorem unweighted_yes (hproj : ∀ e x, (fiber e x).1 = G.project e x)
    (ellU : U → X) (ellV : V → Y) (hscore : 1-(P.theta:ℝ) ≤ G.score ellU ellV) :
    (unweightedInstance P R G hG hYX fiber).graph.dfvs ≤
      (unweightedInstance P R G hG hYX fiber).k := by
  apply roundedGraph_yes _ (output_loopless G R.law hYX fiber) _
  · intro v; exact (rationalCost_pos P R G hG v).le
  obtain ⟨F,hF,hcost⟩ := parameterized_completeness P R G hYX fiber hproj ellU ellV hscore
  refine ⟨F,hF,?_⟩
  rw [← cost_sum P R G hG F] at hcost
  exact_mod_cast hcost

theorem unweighted_no (hproj : ∀ e x, (fiber e x).1 = G.project e x)
    (hsound : G.Sound P.theta) (A : ℝ) (hA : 5*A ≤ D) :
    A * ((unweightedInstance P R G hG hYX fiber).k : ℝ) <
      ((unweightedInstance P R G hG hYX fiber).graph.dfvs : ℝ) := by
  have hn := roundedGraph_no (OutputArc G R.law hYX fiber)
    (output_loopless G R.law hYX fiber) (rationalCost P R G hG) (D:ℚ) (by
      intro F hF
      have hc := parameterized_soundness P R G hYX fiber hproj hsound F hF
      rw [← cost_sum P R G hG F] at hc
      exact_mod_cast hc)
  have hh : (Fintype.card (OutputVertex (M := P.M) G R.law):ℝ)*D <
      ((unweightedInstance P R G hG hYX fiber).graph.dfvs : ℝ) := by
    exact_mod_cast hn
  apply lt_of_le_of_lt _ hh
  change A * ((5*Fintype.card (OutputVertex (M := P.M) G R.law):ℕ):ℝ) ≤ _
  push_cast
  nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (OutputVertex (M := P.M) G R.law)),
    mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg (α:=ℝ)
      (Fintype.card (OutputVertex (M := P.M) G R.law)))]

end DirectedFeedback.Construction

end

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback
open SourceProbability SourceProbability.FiniteDistribution
open Games Construction
open DFVSGames.Explicit DFVSGames.Explicit.MachineOutputContract

namespace UGBridge
variable {U V E Q : Type} [Fintype U] [Fintype V] [Fintype E] [Fintype Q]
  [Nonempty E] [Nonempty Q]

def game (G : BipartiteGame U V E Q) : Game U V E (Q × Bool) Q where
  edgeLaw := uniform E
  left := G.left
  right := G.right
  project := fun e a => G.permutation e a.1

def fiber (G : BipartiteGame U V E Q) (e : E) : (Q × Bool) ≃ Q × Bool :=
  Equiv.prodCongr (G.permutation e) (Equiv.refl Bool)

omit [Fintype U] [Fintype V] [Fintype Q] [Nonempty Q] in
theorem fiber_project (G : BipartiteGame U V E Q) (e : E) (a : Q × Bool) :
    (fiber G e a).1 = (game G).project e a := rfl

omit [Nonempty Q] in
theorem alphabet_card : Fintype.card Q ≤ Fintype.card (Q × Bool) := by simp; omega

omit [Fintype U] [Fintype V] [Fintype Q] [Nonempty Q] in
theorem rational (G : BipartiteGame U V E Q) : (game G).edgeLaw.RationalMass :=
  RationalMass.uniform

omit [Fintype U] [Fintype V] [Fintype Q] [Nonempty Q] in
theorem score_eq [DecidableEq Q] (G : BipartiteGame U V E Q) (a : U → Q × Bool) (b : V → Q) :
    (game G).score a b = (G.satisfiedCount (fun u => (a u).1) b : ℝ)/Fintype.card E := by
  unfold Game.score game
  rw [probability_uniform]
  congr 1
  rw [Finset.card_filter]
  simp only [BipartiteGame.satisfiedCount, decide_eq_true_eq]

end UGBridge

namespace SourceInstance
variable {ε δ : ℝ} (R : BinaryGapReduction ε δ) (input : List Bool)

abbrev UG := (R.simpleBipartite input).toBipartiteGame
abbrev Left := {v : Fin (R.construct input).vertices // (R.simpleBipartite input).side v = false}
abbrev Right := {v : Fin (R.construct input).vertices // (R.simpleBipartite input).side v = true}
abbrev Edge := Fin (R.construct input).constraints.length

instance edge_nonempty : Nonempty (Edge R input) :=
  ⟨⟨0,R.occurrence_count_positive input⟩⟩
instance label_nonempty : Nonempty (Fin R.alphabet) :=
  ⟨⟨0,lt_of_lt_of_le (by decide : 0 < 2) R.alphabetAtLeastTwo⟩⟩

def game := UGBridge.game (UG R input)
def fiber := UGBridge.fiber (UG R input)

theorem correct (yes : DFVSGames.BinaryLanguage.language input) :
    ∃ a b, 1-ε ≤ (game R input).score a b := by
  obtain ⟨l,hl⟩ := R.completeness input yes
  refine ⟨fun u => (l u.val,false),fun v => l v.val,?_⟩
  rw [game,UGBridge.score_eq]
  have hc := (R.simpleBipartite input).toBipartiteGame_count l
  have hc' : (UG R input).satisfiedCount (fun u => l u.val) (fun v => l v.val) =
      DFVSGames.Foundations.Target.countSatisfied l (R.construct input).constraints := by
    simpa only [UG,BipartiteGame.satisfiedCount] using hc
  rw [hc']
  simpa only [Fintype.card_fin] using hl

theorem sound (no : ¬DFVSGames.BinaryLanguage.language input) :
    (game R input).Sound δ := by
  intro a b
  rw [game,UGBridge.score_eq]
  have hc := (R.simpleBipartite input).toBipartiteGame_count_merge (fun u => (a u).1) b
  have hc' : (UG R input).satisfiedCount (fun u => (a u).1) b =
      DFVSGames.Foundations.Target.countSatisfied
        ((R.simpleBipartite input).mergeLabelings (fun u => (a u).1) b)
        (R.construct input).constraints := by
    simpa only [UG,BipartiteGame.satisfiedCount] using hc
  rw [hc']
  simpa only [Fintype.card_fin] using
    R.soundness input no ((R.simpleBipartite input).mergeLabelings (fun u => (a u).1) b)

end SourceInstance

namespace FromUG
variable {D : ℕ} (P : Parameters D)
  (S : BinaryGapReduction P.theta P.theta)
  (R : RankParameters P (Fin S.alphabet × Bool))

def instanceOf (input : List Bool) : GapInstance :=
  unweightedInstance P R (SourceInstance.game S input) (UGBridge.rational _)
    UGBridge.alphabet_card (SourceInstance.fiber S input)

theorem yes (input : List Bool) (h : DFVSGames.BinaryLanguage.language input) :
    (instanceOf P S R input).graph.dfvs ≤ (instanceOf P S R input).k := by
  obtain ⟨a,b,hscore⟩ := SourceInstance.correct S input h
  exact unweighted_yes P R _ _ _ _ (UGBridge.fiber_project _) a b hscore

theorem no (A : ℝ) (hA : 5*A ≤ D) (input : List Bool)
    (h : ¬DFVSGames.BinaryLanguage.language input) :
    A*((instanceOf P S R input).k:ℝ) < ((instanceOf P S R input).graph.dfvs:ℝ) :=
  unweighted_no P R _ _ _ _ (UGBridge.fiber_project _) (SourceInstance.sound S input h) A hA

theorem exists_correct_map (A : ℝ) :
    ∃ f : List Bool → GapInstance,
      (∀ input, DFVSGames.BinaryLanguage.language input → (f input).graph.dfvs ≤ (f input).k) ∧
      (∀ input, ¬DFVSGames.BinaryLanguage.language input → A*((f input).k:ℝ) < ((f input).graph.dfvs:ℝ)) := by
  obtain ⟨D,hD⟩ := exists_nat_ge (5*A)
  obtain ⟨P⟩ := exists_parameters D
  obtain ⟨S⟩ := DFVSGames.theorem11 P.theta P.theta
    (by exact_mod_cast P.theta_pos) P.theta_half (by exact_mod_cast P.theta_pos) P.theta_half
  obtain ⟨R⟩ := exists_rankParameters P (Fin S.alphabet × Bool)
  exact ⟨instanceOf P S R,yes P S R,no P S R A hD⟩

end FromUG
end DirectedFeedback

end

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.FullGame
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Explicit.MachineOutputContract
open SourceProbability SourceProbability.FiniteDistribution Games

variable {q : Nat}

abbrev Edge (I : Instance q) := Fin I.constraints.length
instance edge_nonempty (I : Instance q) : Nonempty (Edge I) := ⟨⟨0,I.constraintCount_positive⟩⟩
instance vertex_nonempty (I : Instance q) : Nonempty (Fin I.vertices) :=
  ⟨(I.constraints[0]'I.constraintCount_positive).source⟩

def game (I : Instance q) : Game (Fin I.vertices) (Fin I.vertices) (Edge I) (Fin q × Bool) (Fin q) where
  edgeLaw := uniform (Edge I)
  left e := I.constraints[e].source
  right e := I.constraints[e].target
  project e a := (permutationEquiv I.constraints[e].permutation) a.1

def fiber (I : Instance q) (e : Edge I) : (Fin q × Bool) ≃ (Fin q × Bool) :=
  Equiv.prodCongr (permutationEquiv I.constraints[e].permutation) (Equiv.refl Bool)

theorem fiber_project (I : Instance q) (e : Edge I) (a : Fin q × Bool) :
    (fiber I e a).1=(game I).project e a := rfl

variable {ε δ : ℝ} (R : BinaryGapReduction ε δ) (input : List Bool)

theorem score_restrict (a : Fin (R.construct input).vertices → Fin R.alphabet × Bool)
    (b : Fin (R.construct input).vertices → Fin R.alphabet) :
    (game (R.construct input)).score a b = (SourceInstance.game R input).score
      (fun u => a u.val) (fun v => b v.val) := rfl

theorem completeness (h : DFVSGames.BinaryLanguage.language input) :
    ∃ a b, 1-ε ≤ (game (R.construct input)).score a b := by
  obtain ⟨l,hl⟩ := R.completeness input h
  refine ⟨fun u => (l u,false),l,?_⟩
  rw [score_restrict,SourceInstance.game,UGBridge.score_eq]
  have hc := (R.simpleBipartite input).toBipartiteGame_count l
  have hc' : (SourceInstance.UG R input).satisfiedCount (fun u => l u.val) (fun v => l v.val) =
      countSatisfied l (R.construct input).constraints := by
    simpa only [SourceInstance.UG,DFVSGames.Explicit.BipartiteGame.satisfiedCount] using hc
  rw [hc']
  simpa only [Fintype.card_fin] using hl

theorem soundness (h : ¬DFVSGames.BinaryLanguage.language input) :
    (game (R.construct input)).Sound δ := by
  intro a b
  rw [score_restrict]
  exact SourceInstance.sound R input h _ _

end DirectedFeedback.FullGame

end

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.GameRead
open BoundedExpr BoundedExpr.UnaryRead
open DFVSGames.Foundations DFVSGames.Foundations.Target DFVSGames.Foundations.Complexity
open DFVSGames.Explicit.MachineOutputContract

variable (q : Nat) [NeZero q]
def n (x : List Bool) : Nat := max 1 (word x 0)
def m (x : List Bool) : Nat := max 1 (word x 2)
def field (x : List Bool) (e j : Nat) : Nat := word x (3+e*(q+2)+j)
def left (x : List Bool) (e : Nat) : Nat := field q x e 0 % n x
def right (x : List Bool) (e : Nat) : Nat := field q x e 1 % n x
def table (x : List Bool) (e : Nat) : Fin q → Fin q := fun i =>
  ⟨field q x e (2+i.val)%q,Nat.mod_lt _ (NeZero.pos q)⟩
def asPerm (f : Fin q → Fin q) : Equiv.Perm (Fin q) :=
  if h : Function.Bijective f then Equiv.ofBijective f h else Equiv.refl _
def perm (x : List Bool) (e : Nat) : Equiv.Perm (Fin q) := asPerm q (table q x e)
def fiber (x : List Bool) (e : Nat) : (Fin q × Bool) ≃ (Fin q × Bool) :=
  Equiv.prodCongr (perm q x e) (Equiv.refl Bool)

theorem n_pos (x : List Bool) : 0<n x := by unfold n; omega
theorem m_pos (x : List Bool) : 0 < m x := by unfold m; omega

theorem n_def (r : Nat) : Def (r:=r) (fun x _ => n x) := (Def.lit 1).max (word_def (Def.lit 0))
theorem m_def (r : Nat) : Def (r:=r) (fun x _ => m x) := (Def.lit 1).max (word_def (Def.lit 2))
omit [NeZero q] in
theorem field_def {r : Nat} {e j : List Bool → (Fin r → Nat) → Nat} (he : Def e) (hj : Def j) :
    Def (fun x a => field q x (e x a) (j x a)) :=
  word_def (((Def.lit 3).add (he.mul (Def.lit (q+2)))).add hj)
omit [NeZero q] in
theorem left_def {r : Nat} {e : List Bool → (Fin r → Nat) → Nat} (he : Def e) :
    Def (fun x a => left q x (e x a)) := (field_def q he (Def.lit 0)).mod (n_def r)
omit [NeZero q] in
theorem right_def {r : Nat} {e : List Bool → (Fin r → Nat) → Nat} (he : Def e) :
    Def (fun x a => right q x (e x a)) := (field_def q he (Def.lit 1)).mod (n_def r)
theorem table_def {r : Nat} {e : List Bool → (Fin r → Nat) → Nat} (he : Def e) :
    FDef (fun x a => table q x (e x a)) := by
  apply FDef.pi
  intro i
  have h := FDef.ofNat ((field_def q he (Def.lit (2+i.val))).mod (Def.lit q)) q id (⟨0,NeZero.pos q⟩ : Fin q)
  apply h.congr
  intro x a
  simp [table,Nat.mod_lt _ (NeZero.pos q)]
theorem perm_def {r : Nat} {e : List Bool → (Fin r → Nat) → Nat} (he : Def e) :
    FDef (fun x a => perm q x (e x a)) := (table_def q he).map (asPerm q)
theorem fiber_def {r : Nat} {e : List Bool → (Fin r → Nat) → Nat} (he : Def e) :
    FDef (fun x a => fiber q x (e x a)) := (perm_def q he).map (fun p => Equiv.prodCongr p (Equiv.refl Bool))

omit [NeZero q] in
lemma word_game (I : Instance q) (j : Nat) :
    word (gameBits I) j=(gameWords I)[j]?.getD 0 := word_encoded _ _

omit [NeZero q] in
theorem n_encoded (I : Instance q) : n (gameBits I)=I.vertices := by
  rw [n,word_game]
  have hp : 0<I.vertices := Fintype.card_pos_iff.mpr (FullGame.vertex_nonempty I) |> (by simpa using ·)
  simp only [gameWords,List.getElem?_append,List.length_cons,List.length_nil,List.getElem?_cons_zero]
  simp
  omega

omit [NeZero q] in
theorem m_encoded (I : Instance q) : m (gameBits I)=I.constraints.length := by
  rw [m,word_game]
  simp only [gameWords,List.getElem?_append,List.length_cons,List.length_nil,List.getElem?_cons_succ,
    List.getElem?_cons_zero]
  simp
  exact Nat.succ_le_of_lt I.constraintCount_positive

lemma get_flatMap {A : Type} (f : A → List Nat) (L : Nat) (hL : ∀ a,(f a).length=L)
    (as : List A) (e : Fin as.length) (j : Nat) (hj : j<L) :
    (as.flatMap f)[e.val*L+j]?.getD 0=(f as[e])[j]?.getD 0 := by
  induction as with
  | nil => exact e.elim0
  | cons a as ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · simp only [Fin.val_zero,zero_mul,zero_add,List.flatMap_cons]
      rw [List.getElem?_append_left (by simpa [hL] using hj)]
      rfl
    · simp only [Fin.val_succ,List.flatMap_cons]
      rw [List.getElem?_append_right (by rw [hL]; nlinarith)]
      rw [hL]
      have he : (e.val+1)*L+j-L=e.val*L+j := by rw [add_mul,one_mul]; omega
      rw [he]
      exact ih e

omit [NeZero q] in
theorem field_encoded (I : Instance q) (e : FullGame.Edge I) (j : Nat) (hj : j<q+2) :
    field q (gameBits I) e.val j=(constraintWords I.constraints[e])[j]?.getD 0 := by
  rw [field,word_game]
  simp only [gameWords]
  rw [List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega)]
  simp only [List.length_cons,List.length_nil]
  have he : 3+e.val*(q+2)+j-(0+1+1+1)=e.val*(q+2)+j := by omega
  rw [he]
  apply get_flatMap constraintWords (q+2) _ I.constraints e j hj
  intro a
  simp [constraintWords,tableWords]

omit [NeZero q] in
theorem left_encoded (I : Instance q) (e : FullGame.Edge I) :
    left q (gameBits I) e.val=I.constraints[e].source.val := by
  rw [left,field_encoded q I e 0 (by omega),n_encoded]
  simp only [constraintWords,List.getElem?_append,List.length_cons,List.length_nil,
    List.getElem?_cons_zero,Option.getD_some,show (0:Nat)<0+1+1 by omega,ite_true]
  exact Nat.mod_eq_of_lt I.constraints[e].source.isLt

omit [NeZero q] in
theorem right_encoded (I : Instance q) (e : FullGame.Edge I) :
    right q (gameBits I) e.val=I.constraints[e].target.val := by
  rw [right,field_encoded q I e 1 (by omega),n_encoded]
  simp only [constraintWords,List.getElem?_append,List.length_cons,List.length_nil,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,show (1:Nat)<0+1+1 by omega,ite_true]
  exact Nat.mod_eq_of_lt I.constraints[e].target.isLt

theorem table_encoded (I : Instance q) (e : FullGame.Edge I) :
    table q (gameBits I) e.val=permutationEquiv I.constraints[e].permutation := by
  funext i
  apply Fin.ext
  change field q (gameBits I) e.val (2+i.val)%q= _
  rw [field_encoded q I e (2+i.val) (by have := i.isLt; omega)]
  unfold constraintWords
  rw [List.getElem?_append_right (by simp)]
  have he : 2+i.val-[I.constraints[e].source.val,I.constraints[e].target.val].length=i.val := by simp
  rw [he]
  have hi : i.val<(tableWords I.constraints[e].permutation).length := by simp
  rw [List.getElem?_eq_getElem hi]
  simp only [Option.getD_some,tableWords,List.getElem_map,Vector.getElem_toList]
  exact Nat.mod_eq_of_lt (I.constraints[e].permutation.images[i]).isLt

theorem perm_encoded (I : Instance q) (e : FullGame.Edge I) :
    perm q (gameBits I) e.val=permutationEquiv I.constraints[e].permutation := by
  rw [perm,table_encoded]
  apply Equiv.ext
  intro i
  simp [asPerm]

theorem fiber_encoded (I : Instance q) (e : FullGame.Edge I) :
    fiber q (gameBits I) e.val=FullGame.fiber I e := by
  rw [fiber,perm_encoded]
  rfl

end DirectedFeedback.GameRead

end

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PotentialCover

variable {L B I : Type} [Fintype L] [Fintype B]

def fullFibers (p : L → B) (F : Finset L) : Finset B :=
  Finset.univ.filter (fun b => ∀ a, p a=b → a ∈ F)

@[simp] theorem mem_fullFibers (p : L → B) (F : Finset L) (b : B) :
    b ∈ fullFibers p F ↔ ∀ a, p a=b → a ∈ F := by simp [fullFibers]

theorem feedback_project (p : L → B) (R : B → B → Prop) (S : L → L → Prop)
    (hcover : ∀ a b, R (p a) (p b) → S a b) (F : Finset L)
    (hF : FeedbackR S F) : FeedbackR R (fullFibers p F) := by
  intro n f hinj harc
  by_contra hn
  have hex (i) : ∃ a, p a=f i ∧ a ∉ F := by
    have hi : f i ∉ fullFibers p F := fun h => hn ⟨i,h⟩
    obtain ⟨a,ha⟩ := not_forall.mp ((mem_fullFibers p F (f i)).not.mp hi)
    exact ⟨a,Classical.not_imp.mp ha⟩
  choose g hg using hex
  have hginj : Function.Injective g := by
    intro i j hij
    apply hinj
    rw [← (hg i).1,← (hg j).1,hij]
  obtain ⟨i,hi⟩ := hF n g hginj (fun i => hcover _ _ (by
    rw [(hg i).1,(hg (i+1)).1]
    exact harc i))
  exact (hg i).2 hi

def fiberCount (p : L → B) (b : B) : Nat := (Finset.univ.filter (fun a => p a=b)).card

theorem fullFibers_cost_le (p : L → B) (F : Finset L) :
    ∑ b ∈ fullFibers p F, fiberCount p b ≤ F.card := by
  have he : ∑ b ∈ fullFibers p F, fiberCount p b =
      (Finset.univ.filter (fun a => p a ∈ fullFibers p F)).card := by
    simp only [fiberCount,Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp
  rw [he]
  exact Finset.card_le_card (by
    intro a ha
    exact (mem_fullFibers p F (p a)).mp ((Finset.mem_filter.mp ha).2) a rfl)

theorem weight_le_card (p : L → B) (w : B → ℝ) (C : Nat)
    (hw : ∀ b, C*w b ≤ fiberCount p b) (F : Finset L) :
    C * (∑ b ∈ fullFibers p F, w b) ≤ F.card := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ b ∈ fullFibers p F, (fiberCount p b : ℝ) :=
      Finset.sum_le_sum (fun b _ => hw b)
    _ = ((∑ b ∈ fullFibers p F, fiberCount p b : Nat) : ℝ) := by simp
    _ ≤ F.card := by exact_mod_cast fullFibers_cost_le p F

def Arc (deleted : I → L → Prop) (potential : I → L → ℚ) (a b : L) : Prop :=
  a ≠ b ∧ ∀ i, ¬deleted i a → ¬deleted i b → potential i a < potential i b

omit [Fintype L] in
theorem irrefl (d : I → L → Prop) (q : I → L → ℚ) (a : L) : ¬Arc d q a a :=
  fun h => h.1 rfl

theorem deleted_feedback (d : I → L → Prop) (q : I → L → ℚ) (i : I) :
    FeedbackR (Arc d q) (Finset.univ.filter (d i)) := by
  intro n f _ ha
  by_contra hn
  have hs (j) : ¬d i (f j) := by intro h; exact hn ⟨j,by simp [h]⟩
  have hi (j) : q i (f j) < q i (f (j+1)) := (ha j).2 i (hs _) (hs _)
  have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hi j)
  have he : (∑ j : Fin (n+1), q i (f (j+1))) = ∑ j : Fin (n+1), q i (f j) := by
    exact Fintype.sum_equiv (Equiv.addRight (1 : Fin (n+1))) _ _ (fun _ => rfl)
  rw [he] at hsum
  exact (lt_irrefl _ hsum)

omit [Fintype L] [Fintype B] in
theorem covers (p : L → B) (R : B → B → Prop) (d : I → B → Prop) (q : I → B → ℚ)
    (hirr : ∀ b, ¬R b b)
    (hinc : ∀ i a b, R a b → ¬d i a → ¬d i b → q i a < q i b)
    {a b : L} (h : R (p a) (p b)) :
    Arc (fun i a => d i (p a)) (fun i a => q i (p a)) a b := by
  refine ⟨?_,fun i => hinc i _ _ h⟩
  intro he
  subst b
  exact hirr _ h

end DirectedFeedback.PotentialCover

end

end OAI
