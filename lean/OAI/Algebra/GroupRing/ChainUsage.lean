import Mathlib
import OAI.Algebra.GroupRing.PatternTotalCoding

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainUsage
open scoped Classical BigOperators
open PortSubdivision DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity
variable {V D P : Type} [Fintype D] [Fintype P] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2
local notation "w" => word Γ mark h2
variable (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "col" => color Γ mark h2 paths
local notation "m" => ChunkComparisons.multiplicity col

def Used : Prop := ∀ d,∃ p,d∈(paths p).flatMap w ∨ Γ.reverse d∈(paths p).flatMap w

omit [Fintype P] in
lemma representative_used (hu : Used Γ mark h2 paths) (c : R) :
    ∃ p b,b∈paths p ∧ representative Γ mark h2 b=c := by
  obtain ⟨p,hp⟩ := hu c.val.val
  rcases hp with hp|hp
  · obtain ⟨b,hb,he⟩ := List.mem_flatMap.mp hp
    have heq := same_word Γ mark h2 he (start_mem_word Γ mark h2 c.val)
    exact ⟨p,b,hb,heq ▸ representative_val Γ mark h2 c⟩
  · obtain ⟨b,hb,he⟩ := List.mem_flatMap.mp hp
    have heq := same_word Γ mark h2 he
      (reverse_mem_word Γ mark h2 c.val c.val.val (start_mem_word Γ mark h2 c.val))
    exact ⟨p,b,hb,by rw [heq,representative_reverse,representative_val]⟩

lemma multiplicity_pos (hu : Used Γ mark h2 paths) (c : R) : 1 ≤ m c := by
  simp only [ChunkComparisons.multiplicity,Fintype.card_eq_nat_card]
  obtain ⟨p,b,hb,he⟩ := representative_used Γ mark h2 paths hu c
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hb
  have hn : Nonempty {t // col t=c} := by
    refine ⟨⟨⟨p,i⟩,?_⟩⟩
    change representative Γ mark h2 ((paths p).get i)=c
    rw [hi,he]
  exact Nat.card_pos

lemma traversal_card : Fintype.card (RepeatedBlocks.Traversal m)=∑p,(paths p).length := by
  rw [Fintype.card_congr (ChunkComparisons.enumeration col)]
  simp only [FiniteChunking.Traversal,chunks]
  exact (Fintype.card_sigma (α:=fun p : P => Fin (paths p).length)).trans (Finset.sum_congr rfl (fun p _ => Fintype.card_fin _))

lemma multiplicity_le (c : R) : m c≤∑p,(paths p).length := by
  simp only [ChunkComparisons.multiplicity,Fintype.card_eq_nat_card]
  have h := Nat.card_le_card_of_injective (Subtype.val : {t // col t=c} → _)
    Subtype.val_injective
  simpa only [FiniteChunking.Traversal,chunks,Nat.card_sigma,Nat.card_fin] using h

omit [Fintype D] [Fintype P] in
lemma flatMap_length_le {A Z : Type*} (f : A → List Z) (l : List A) {a : A} (ha : a∈l) :
    (f a).length≤(l.flatMap f).length := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl|ha
    · simp only [List.flatMap_cons,List.length_append]
      omega
    · have h := ih ha
      simp only [List.flatMap_cons,List.length_append]
      omega

lemma length_le_total_of_mem (p : P) (b : B) (hb : b∈paths p) :
    chainLength Γ mark h2 b≤∑p,((paths p).flatMap w).length := by
  rw [←word_length]
  exact (flatMap_length_le w _ hb).trans
    (Finset.single_le_sum (f:=fun p => ((paths p).flatMap w).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ p))

lemma chain_length_le (hu : Used Γ mark h2 paths) (b : B) :
    chainLength Γ mark h2 b≤∑p,((paths p).flatMap w).length := by
  obtain ⟨p,a,ha,he⟩ := representative_used Γ mark h2 paths hu (representative Γ mark h2 b)
  have h := length_le_total_of_mem Γ mark h2 paths p a ha
  rw [oriented_length Γ mark h2 a,he,←oriented_length Γ mark h2 b] at h
  exact h

lemma rep_card_le : Fintype.card R≤Fintype.card B := Fintype.card_subtype_le _

end TorsionFreeZeroDivisors.ChainUsage

namespace TorsionFreeZeroDivisors.SourcePattern
open scoped Classical BigOperators
open PortSubdivision MarkedChainBound DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open ActualComplexity CoreStripping ImageComplexity GirthAsymptotics TypedGraphs

/-- The uniformly bounded number of marked darts is derived, not required of an
original pattern. Extra marks are just the prescribed path endpoints. -/
theorem marked_bound (B K : ℕ) : ∃ R : ℕ,0<R ∧
    ∀ {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
      (Γ : PortGraph V D) (M : Finset V) (_hM : M.card≤2*K)
      (paths : P → List D) (_hp : ∀ p,paths p≠[])
      (_ : Fintype.card P≤K) (_ : Function.Surjective Γ.origin)
      (_ : ∀ p,(paths p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
      (_ : ∀ d,∃ p,d∈paths p ∨ Γ.reverse d∈paths p)
      (L : ℝ) (_ : 0<L) (_ : (∑ p,(paths p).length:ℕ)≤(B:ℝ)*L)
      (_ : ∀ a (c : Γ.subdivision.Walk a a),c.IsCycle →
        L≤WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : D => (1:ℝ))) c),
      Fintype.card {d : D // turn Γ.origin (marks Γ M) (marks_degree_two Γ M) d=d}≤R ∧
        Fintype.card (Mark (marks Γ M))≤R := by
  obtain ⟨R,hR⟩ := bounded_image_branches (B:ℝ) (Nat.cast_nonneg _) (2*K)
  refine ⟨R+6*K+1,by omega,?_⟩
  intro V D P _ _ _ Γ M hM paths hp hP hv hc hi L hL hH hg
  have hleaf := leaf_bound Γ paths hp hc hi
  have hdc := dart_count Γ paths hi
  have hdc' : (Fintype.card D:ℝ)≤2*(B:ℝ)*L := by
    have hdc' : (Fintype.card D:ℝ)≤2*(∑ p,(paths p).length:ℕ) := by exact_mod_cast hdc
    nlinarith
  have hleaf' : (Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card≤2*K :=
    hleaf.trans (Nat.mul_le_mul_left _ hP)
  have hb := hR Γ L hL hdc' hg hleaf'
  have hd := marked_dart_bound Γ M
  have hseed : Fintype.card {d : D //
      turn Γ.origin (marks Γ M) (marks_degree_two Γ M) d=d}≤R+6*K+1 := by
    rw [chain_dart_card]
    omega
  exact ⟨hseed,(marked_vertices_le Γ _ _ hv).trans hseed⟩

abbrev Seeds {V D : Type} [Fintype D] (Γ : PortGraph V D) (M : Finset V) :=
  {d : D // turn Γ.origin (marks Γ M) (marks_degree_two Γ M) d=d}

def R (B K : ℕ) : ℕ := (marked_bound B K).choose
lemma R_pos (B K : ℕ) : 0<R B K := (marked_bound B K).choose_spec.1
def T (B K : ℕ) : ℕ := R B K*(B+K)

/-- The actual suppressed form of source paths. No bound on the resulting
skeleton, chain lengths, multiplicities or number of traversals is assumed. -/
structure Data (B K I rep : ℕ) where
  V : Type
  D : Type
  P : Type
  E : Type
  [fV : Fintype V]
  [fD : Fintype D]
  [fP : Fintype P]
  [fE : Fintype E]
  graph : PortGraph V D
  vertices : Finset V
  vertices_bound : vertices.card≤2*K
  no_isolated : Function.Surjective graph.origin
  side : V → Bool
  side_edge : ∀ d,side (graph.origin (graph.reverse d))=side (graph.origin d)
  paths : P → List (Seeds graph vertices)
  nonempty : ∀ p,paths p≠[]
  root : Option P
  path_bound : Fintype.card P≤K
  comparison_bound : Fintype.card E≤I
  image : ChainUsage.Used graph (marks graph vertices) (marks_degree_two graph vertices) paths
  path_chain : ∀ p,((paths p).flatMap (word graph (marks graph vertices) (marks_degree_two graph vertices))).IsChain
    (WeightedMoore.PortWalk.step graph.origin graph.reverse)
  cyclic_chain : ∀ p,StageRoot.cyclic root p=true →
    ∀ᵉ (x∈((paths p).flatMap (word graph (marks graph vertices) (marks_degree_two graph vertices))).getLast?)
        (y∈((paths p).flatMap (word graph (marks graph vertices) (marks_degree_two graph vertices))).head?),
      WeightedMoore.PortWalk.step graph.origin graph.reverse x y
  girth : ∀ a (c : graph.subdivision.Walk a a),c.IsCycle →
    (L (size rep):ℝ)≤WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : D => (1:ℝ))) c
  length_le : (∑p,((paths p).flatMap (word graph (marks graph vertices) (marks_degree_two graph vertices))).length:ℕ)≤B*L (size rep)
  length_ge : L (size rep)≤(∑p,((paths p).flatMap (word graph (marks graph vertices) (marks_degree_two graph vertices))).length:ℕ)
  comparisons : Comparisons (E:=E) (pathLength (chunks graph (marks graph vertices) (marks_degree_two graph vertices) paths)
    (chunkLength graph (marks graph vertices) (marks_degree_two graph vertices) paths))
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e,comparisons.lo e=lower e
  upper_eq : ∀ e,comparisons.hi e=upper e
  lower_le : ∀ e,lower e≤upper e
  upper_le : ∀ e,upper e≤pathLength (chunks graph (marks graph vertices) (marks_degree_two graph vertices) paths)
    (chunkLength graph (marks graph vertices) (marks_degree_two graph vertices) paths) (comparisons.source e)
  reduced : ∀ x e,comparisons.side x=some e →
    originalDart graph (marks graph vertices) (marks_degree_two graph vertices) paths x≠
      originalDart graph (marks graph vertices) (marks_degree_two graph vertices) paths (comparisons.pairing.partner x) ∧
    originalDart graph (marks graph vertices) (marks_degree_two graph vertices) paths x≠graph.reverse
      (originalDart graph (marks graph vertices) (marks_degree_two graph vertices) paths (comparisons.pairing.partner x))
  unpaired_le : ((Finset.univ.filter (fun x => comparisons.pairing.partner x=x)).card:ℝ)≤
    StageFusion.epsilon (1/600) 256*
      (∑p,((paths p).flatMap (word graph (marks graph vertices) (marks_degree_two graph vertices))).length:ℕ)

attribute [instance] Data.fV Data.fD Data.fP Data.fE

namespace Data
variable {B K I rep : ℕ} (a : Data B K I rep)
abbrev mark := marks a.graph a.vertices
abbrev degree_two := marks_degree_two a.graph a.vertices
abbrev words (p : a.P) := (a.paths p).flatMap (word a.graph a.mark a.degree_two)
abbrev totalLength : ℕ := ∑p,(a.words p).length
abbrev lengths : a.P → ℕ := pathLength (chunks a.graph a.mark a.degree_two a.paths)
  (chunkLength a.graph a.mark a.degree_two a.paths)

lemma words_nonempty (p : a.P) : a.words p≠[] := by
  intro he
  obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil (a.paths p) (a.nonempty p)
  have hm : b.val∈a.words p := by
    apply List.mem_flatMap.mpr
    exact ⟨b,hb,start_mem_word a.graph a.mark a.degree_two b⟩
  simp [he] at hm

lemma lengths_le (p : a.P) : a.lengths p≤B*L (size rep) := by
  rw [lengths,pathLength_eq]
  apply le_trans (b:=a.totalLength) _ a.length_le
  exact Finset.single_le_sum (f:=fun p => (a.words p).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)

lemma upper_bound (e : a.E) : a.upper e≤B*L (size rep) :=
  (a.upper_le e).trans (a.lengths_le _)

lemma lower_bound (e : a.E) : a.lower e≤B*L (size rep) :=
  (a.lower_le e).trans (a.upper_bound e)

lemma covered : ∀ d,ChainCoverage.Covered a.graph.reverse (turn a.graph.origin a.mark a.degree_two)
    a.graph.reverse_reverse (turn_involutive a.graph.origin a.mark a.degree_two) d := by
  apply ActualMarkedChains.actual_image_covered a.graph a.mark a.degree_two a.words a.path_chain _ a.image
  intro p d hd
  rw [words,ChainPathTransport.flatMap_head] at hd
  obtain ⟨b,_hb,hbd⟩ := Option.mem_map.mp hd
  subst d
  exact (turn_fixed_iff a.graph.origin a.mark a.degree_two b.val).mp b.property

lemma mark_bounds (hL : 0<L (size rep)) :
    Fintype.card (Seeds a.graph a.vertices)≤R B K ∧ Fintype.card (Mark a.mark)≤R B K := by
  apply (marked_bound B K).choose_spec.2 a.graph a.vertices a.vertices_bound a.words
    a.words_nonempty a.path_bound a.no_isolated a.path_chain a.image (L (size rep))
    (by exact_mod_cast hL) _ a.girth
  exact_mod_cast a.length_le

lemma total_traversals_le (hL : 0<L (size rep)) : ∑p,(a.paths p).length≤T B K := by
  have h := ChainPaths.bounded_chain_traversals a.graph a.mark a.degree_two
    (B:ℝ) (Nat.cast_nonneg _) K (R B K) a.path_bound (a.mark_bounds hL).1
    (L (size rep)) (by exact_mod_cast hL) a.girth a.paths a.path_chain
    (by exact_mod_cast a.length_le)
  have he : (R B K:ℝ)*((B:ℝ)+K)=(T B K:ℝ) := by simp only [T,Nat.cast_mul,Nat.cast_add]
  rw [he,Nat.ceil_natCast] at h
  exact h

lemma traversal_le (hL : 0<L (size rep)) (p : a.P) : (a.paths p).length≤T B K :=
  (Finset.single_le_sum (f:=fun p => (a.paths p).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)).trans (a.total_traversals_le hL)

lemma offset_bounds (e : a.E) :
    -(2*(B*L (size rep):ℕ):ℤ)≤a.comparisons.offset e ∧
      a.comparisons.offset e≤(2*(B*L (size rep):ℕ):ℤ) := by
  have hlo : (0:ℝ)≤a.comparisons.lo e := by rw [a.lower_eq]; positivity
  have hhi : (0:ℝ)≤a.comparisons.hi e := by rw [a.upper_eq]; positivity
  have hlb : a.comparisons.lo e≤(B*L (size rep):ℕ) := by
    rw [a.lower_eq]; exact_mod_cast a.lower_bound e
  have hub : a.comparisons.hi e≤(B*L (size rep):ℕ) := by
    rw [a.upper_eq]; exact_mod_cast a.upper_bound e
  have hlen : (a.lengths (a.comparisons.source (a.comparisons.flip e)):ℝ)≤(B*L (size rep):ℕ) :=
    by exact_mod_cast a.lengths_le _
  have hr := a.comparisons.target_range e
  have he : -2*((B*L (size rep):ℕ):ℝ)≤(a.comparisons.offset e:ℝ) ∧
      (a.comparisons.offset e:ℝ)≤2*((B*L (size rep):ℕ):ℝ) := by
    cases hh : a.comparisons.reverse e <;> simp only [hh,Bool.false_eq_true,↓reduceIte] at hr
    · constructor <;> linarith
    · constructor <;> linarith
  exact_mod_cast he

def bounded (hL : 0<L (size rep)) : BoundedPattern.Data (R B K) K (T B K) I (B*L (size rep)) where
  V := a.V
  D := a.D
  P := a.P
  E := a.E
  graph := a.graph
  mark := a.mark
  degree_two := a.degree_two
  covered := a.covered
  side := a.side
  side_edge := a.side_edge
  paths := a.paths
  nonempty := a.nonempty
  root := a.root
  comparisons := a.comparisons
  lower e := ⟨a.lower e,by have := a.lower_bound e; omega⟩
  upper e := ⟨a.upper e,by have := a.upper_bound e; omega⟩
  offset e := ⟨(a.comparisons.offset e+2*(B*L (size rep):ℕ)).toNat,by
    obtain ⟨hl,hu⟩ := a.offset_bounds e
    omega⟩
  lower_eq := a.lower_eq
  upper_eq := a.upper_eq
  offset_eq e := by
    obtain ⟨hl,hu⟩ := a.offset_bounds e
    dsimp
    omega
  dart_bound := (a.mark_bounds hL).1
  vertex_bound := (a.mark_bounds hL).2
  path_bound := a.path_bound
  comparison_bound := a.comparison_bound
  chain_length_bound d := (ChainUsage.chain_length_le a.graph a.mark a.degree_two a.paths a.image d).trans a.length_le
  traversal_bound := a.traversal_le hL

lemma bounded_good (hL : 0<L (size rep)) :
    (a.bounded hL).Good B (R B K) (T B K) (I*(T B K)^2) rep where
  multiplicity_le c := (ChainUsage.multiplicity_le a.graph a.mark a.degree_two a.paths c).trans
    (a.total_traversals_le hL)
  multiplicity_pos := ChainUsage.multiplicity_pos a.graph a.mark a.degree_two a.paths a.image
  path_chain p := ChainPathTransport.isChain a.graph a.mark a.degree_two (a.paths p) (a.path_chain p)
  cyclic_chain p hp := ChainPathTransport.closing a.graph a.mark a.degree_two (a.paths p) (a.cyclic_chain p hp)
  reduced := a.reduced
  chains_le := (ChainUsage.rep_card_le a.graph a.mark a.degree_two).trans (a.mark_bounds hL).1
  cut_comparisons_le := by
    change Fintype.card a.E*(Fintype.card (RepeatedBlocks.Traversal
      (ChunkComparisons.multiplicity (color a.graph a.mark a.degree_two a.paths))))^2≤_
    rw [ChainUsage.traversal_card]
    exact Nat.mul_le_mul a.comparison_bound (Nat.pow_le_pow_left (a.total_traversals_le hL) 2)
  length_le := by
    change (∑p,(a.words p).length:ℝ)≤_
    exact_mod_cast a.length_le
  length_ge := by
    change _≤(∑p,(a.words p).length:ℝ)
    exact_mod_cast a.length_ge
  unpaired_le := by
    change _≤StageFusion.epsilon (1/600) 256*(∑p,(a.words p).length:ℝ)
    exact_mod_cast a.unpaired_le

end Data
end TorsionFreeZeroDivisors.SourcePattern

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical Topology
open Filter GirthAsymptotics TypedGraphs ActualPatternEvent

lemma polynomial_exp_tendsto (c B d M : ℕ) (hM : 0<M) :
    Tendsto (fun rep => (c:ℝ)*(B*L (size rep)+1:ℕ)^d*
      Real.exp (-(L (size rep):ℝ)/(4800*M))) atTop (𝓝 0) := by
  have hL : Tendsto (fun rep => (L (size rep):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (L_tendsto.comp size_tendsto)
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d:ℝ)
    (1/(4800*M)) (by positivity)).comp hL
  simp only [Function.comp_def,Real.rpow_natCast] at ht
  have ht' := ht.const_mul ((c:ℝ)*(B+1:ℝ)^d)
  simp only [mul_zero] at ht'
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ ht'
  filter_upwards [hL.eventually (eventually_ge_atTop (1:ℝ))] with rep hr
  have hp : ((B*L (size rep)+1:ℕ):ℝ)^d≤((B+1:ℝ)*(L (size rep):ℝ))^d := by
    gcongr
    push_cast
    nlinarith
  calc
    _ ≤ (c:ℝ)*((B+1:ℝ)*(L (size rep):ℝ))^d*
        Real.exp (-(L (size rep):ℝ)/(4800*M)) := by gcongr
    _ = (c:ℝ)*(B+1:ℝ)^d*((L (size rep):ℝ)^d*
        Real.exp (-(1/(4800*M:ℝ))*(L (size rep):ℝ))) := by
      have he : -(L (size rep):ℝ)/(4800*M)=-(1/(4800*M:ℝ))*(L (size rep):ℝ) := by ring
      rw [he,mul_pow]
      ring

lemma mem_samples (rep : ℕ) (r : Match rep) : r∈samples rep ↔
    (r.1.Contains ∅ ∧ ((3*L (size rep):ℕ):ℕ∞)≤(r.1.graph (PatternEmbeddings.origin (@Types.outgoingA rep))).subdivision.egirth) ∧
    (r.2.Contains ∅ ∧ ((3*L (size rep):ℕ):ℕ∞)≤(r.2.graph (PatternEmbeddings.origin (@Types.outgoingB rep))).subdivision.egirth) := by
  simp only [samples,ConditionedMatchings.Matching.conditioned,Finset.mem_product,
    Finset.mem_filter,Finset.mem_univ,true_and]

lemma samples_eventually_nonempty : ∀ᶠ rep in atTop,(samples rep).Nonempty := by
  filter_upwards [TypedGraphs.eventual_nonempty] with rep hr
  obtain ⟨a,ha⟩ := hr.1
  obtain ⟨b,hb⟩ := hr.2
  simp only [ConditionedMatchings.Matching.conditioned, Finset.mem_filter,
    Finset.mem_univ, true_and] at ha hb
  refine ⟨(a,b),(mem_samples rep (a,b)).mpr ?_⟩
  exact ⟨ha,hb⟩

/-- With the bounds fixed beforehand, for every sufficiently large admissible
size there is an actual pair of conditioned matchings avoiding every bounded
pattern. The roots are universally quantified after the size threshold. -/
theorem eventually_avoids (R K T I B Q M J : ℕ)
    (hR : 0<R) (hK : 0<K) (hI : 0<I) (hM : 0<M) :
    ∀ᶠ rep in atTop,∀ (x : Types.VertexA rep) (y : Types.VertexB rep),
      ∃ r∈samples rep,∀ a : Data R K T I (B*L (size rep)),
        a.Good B Q M J rep → ¬a.event rep x y r := by
  have hsmall := (polynomial_exp_tendsto (PatternTotalCoding.coefficient R K T I)
    B (R+3*I) M hM).eventually_lt_const (by norm_num : (0:ℝ)<1)
  filter_upwards [hsmall, samples_eventually_nonempty,PatternUniform.eventually_ready B M Q J hM]
    with rep hb hs hr
  intro x y
  have hprob := (probability_union R K T I (B*L (size rep)) B Q M J rep hR hK hI hM hs hr x y).trans_lt hb
  by_contra hn
  have hall : ∀ r∈samples rep,∃ a : Data R K T I (B*L (size rep)),
      a.Good B Q M J rep ∧ a.event rep x y r := by
    push Not at hn
    exact hn
  have he : (samples rep).filter (fun r => ∃ a : Data R K T I (B*L (size rep)),
      a.Good B Q M J rep ∧ a.event rep x y r)=samples rep := by
    apply Finset.filter_eq_self.mpr
    exact hall
  rw [he,div_self (by exact_mod_cast (Finset.card_pos.mpr hs).ne')] at hprob
  exact (lt_irrefl (1:ℝ)) hprob

end TorsionFreeZeroDivisors.BoundedPattern

end

end OAI
