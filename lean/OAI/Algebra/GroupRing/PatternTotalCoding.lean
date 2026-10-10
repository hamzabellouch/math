import Mathlib
import OAI.Algebra.GroupRing.ComparisonCoding

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternTotalCoding
open scoped Classical
open PatternCoding

abbrev Code (R K T I H : ℕ) := SizedCode R K T 0 H ×
  (Fin R → Bool) × Fin (I+1) × ComparisonCoding.Code K I H

def coefficient (R K T I : ℕ) :=
  (R+1)^2*(K+1)*PatternCoding.coefficient R K T 0*2^R*(I+1)*ComparisonCoding.coefficient K I

lemma card_code_bound (R K T I H : ℕ) : Fintype.card (Code R K T I H) ≤
    coefficient R K T I*(H+1)^(R+3*I) := by
  have h1 := card_sizedCode R K T 0 H
  have h2 := ComparisonCoding.card_code_bound K I H
  simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.mul_one] at h1
  have h := Nat.mul_le_mul (Nat.mul_le_mul_right (2^R*(I+1)) h1) h2
  have he : Fintype.card (Code R K T I H)=Fintype.card (SizedCode R K T 0 H)*(2^R*((I+1)*Fintype.card (ComparisonCoding.Code K I H))) := by
    simp only [Code,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  rw [he]
  simp only [coefficient,pow_add]
  convert h using 1 <;> ring

variable {D V P E D' V' P' E' : Type*}
    [Fintype D] [Fintype V] [Fintype P] [Fintype E]
    [Fintype D'] [Fintype V'] [Fintype P'] [Fintype E']
    (R K T I H : ℕ) (hR : 0<R) (hK : 0<K) (hI : 0<I)
    (hD : Fintype.card D≤R) (hV : Fintype.card V≤R)
    (hP : Fintype.card P≤K) (hE : Fintype.card E≤I)

def encode (a : Data D V P (Fin 0) T H) (side : V → Bool)
    (c : ComparisonCoding.Data P E H) : Code R K T I H :=
  (encodeData R K T 0 H hR hD hV hP (by simp) a,
   pad R hV false side,⟨Fintype.card E,by omega⟩,ComparisonCoding.encode K I H hK hI hP hE c)

variable (hD' : Fintype.card D'≤R) (hV' : Fintype.card V'≤R)
    (hP' : Fintype.card P'≤K) (hE' : Fintype.card E'≤I)

/-- Complete simultaneous code equivalence for graph, every marked vertex side,
path words, root and the full affine interval geometry. Padding loses no data. -/
theorem complete (a : Data D V P (Fin 0) T H) (side : V → Bool)
    (c : ComparisonCoding.Data P E H)
    (a' : Data D' V' P' (Fin 0) T H) (side' : V' → Bool)
    (c' : ComparisonCoding.Data P' E' H)
    (he : encode R K T I H hR hK hI hD hV hP hE a side c=
      encode R K T I H hR hK hI hD' hV' hP' hE' a' side' c') :
    ∃ f : PatternCoding.Isomorphism a a', ∃ g : ComparisonCoding.Isomorphism H c c',
      f.path=g.path ∧ (∀ d,(Fintype.equivFin D' (f.dart d)).val=(Fintype.equivFin D d).val) ∧
      ∀ v,side v=side' (f.vertex v) := by
  simp only [encode,encodeData,Prod.mk.injEq] at he
  obtain ⟨⟨cd,cv,cp,_,ha⟩,hs,ce,hc⟩ := he
  have cD : Fintype.card D=Fintype.card D' := congrArg Fin.val cd
  have cV : Fintype.card V=Fintype.card V' := congrArg Fin.val cv
  have cP : Fintype.card P=Fintype.card P' := congrArg Fin.val cp
  have cE : Fintype.card E=Fintype.card E' := congrArg Fin.val ce
  obtain ⟨f,fd,fp,fv⟩ := same_code_canonical_isomorphism R K T 0 H hR hD hV hP (by simp)
    hD' hV' hP' (by simp) a a' cD cV cP rfl ha
  obtain ⟨g,gp,_⟩ := ComparisonCoding.encode_complete K I H hK hI hP hE hP' hE' c c' cP cE hc
  refine ⟨f,g,fp.trans gp.symm,?_,?_⟩
  · intro d
    rw [fd]
    exact rename_rank cD d
  · intro v
    rw [fv]
    exact same_pad R hV hV' cV false side side' hs v

end TorsionFreeZeroDivisors.PatternTotalCoding

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks RankedSuppressionIso

/-- The literal finite pattern data. These are only combinatorial encoding
bounds; none of the probability or realizability conclusions is a field. -/
structure Data (R K T I H : ℕ) where
  V : Type
  D : Type
  P : Type
  E : Type
  [fV : Fintype V]
  [fD : Fintype D]
  [fP : Fintype P]
  [fE : Fintype E]
  graph : PortGraph V D
  mark : V → Prop
  degree_two : ∀ v,¬mark v → (out graph.origin v).card=2
  covered : ∀ d,ChainCoverage.Covered graph.reverse (turn graph.origin mark degree_two)
    graph.reverse_reverse (turn_involutive graph.origin mark degree_two) d
  side : V → Bool
  side_edge : ∀ d,side (graph.origin (graph.reverse d))=side (graph.origin d)
  paths : P → List {d : D // turn graph.origin mark degree_two d=d}
  nonempty : ∀ p,paths p≠[]
  root : Option P
  comparisons : Comparisons (E:=E) (pathLength (chunks graph mark degree_two paths)
    (chunkLength graph mark degree_two paths))
  lower : E → Fin (H+1)
  upper : E → Fin (H+1)
  offset : E → Fin (4*H+1)
  lower_eq : ∀ e,comparisons.lo e=(lower e).val
  upper_eq : ∀ e,comparisons.hi e=(upper e).val
  offset_eq : ∀ e,comparisons.offset e=((offset e).val:ℤ)-2*H
  dart_bound : Fintype.card {d : D // turn graph.origin mark degree_two d=d}≤R
  vertex_bound : Fintype.card (Mark mark)≤R
  path_bound : Fintype.card P≤K
  comparison_bound : Fintype.card E≤I
  chain_length_bound : ∀ d,chainLength graph mark degree_two d≤H
  traversal_bound : ∀ p,(paths p).length≤T

attribute [instance] Data.fV Data.fD Data.fP Data.fE

namespace Data
variable {R K T I H : ℕ} (a : Data R K T I H)

abbrev Seeds := {d : a.D // turn a.graph.origin a.mark a.degree_two d=d}
abbrev Marks := Mark a.mark
abbrev lengths : a.P → ℕ := pathLength (chunks a.graph a.mark a.degree_two a.paths)
  (chunkLength a.graph a.mark a.degree_two a.paths)

def graphData : PatternCoding.Data a.Seeds a.Marks a.P (Fin 0) T H where
  reverse := (skeleton a.graph a.mark a.degree_two).reverse
  origin := (skeleton a.graph a.mark a.degree_two).origin
  side d := a.side (a.graph.origin d.val)
  length d := ⟨chainLength a.graph a.mark a.degree_two d,by have := a.chain_length_bound d; omega⟩
  paths := a.paths
  path_bound := a.traversal_bound
  root := a.root.map (fun p => (p,true))
  comparisons := Fin.elim0

def geometryData : ComparisonCoding.Data a.P a.E H where
  flip := a.comparisons.flip
  source := a.comparisons.source
  lower := a.lower
  upper := a.upper
  reverse := a.comparisons.reverse
  offset := a.offset

def encode (hR : 0<R) (hK : 0<K) (hI : 0<I) : PatternTotalCoding.Code R K T I H :=
  PatternTotalCoding.encode R K T I H hR hK hI a.dart_bound a.vertex_bound
    a.path_bound a.comparison_bound a.graphData (fun v => a.side v.val) a.geometryData

end Data
end TorsionFreeZeroDivisors.BoundedPattern

namespace TorsionFreeZeroDivisors.PatternFiniteUnion
open scoped Classical

/-- Quotient-free finite union over a possibly large class of finite graphs.
Representatives are chosen only for used codes, and encode equality must preserve
the literal sample event. -/
theorem bound {P : Type*} {C Ω : Type*} [Fintype C]
    (sample : Finset Ω) (hs : sample.Nonempty) (code : P → C) (good : P → Prop)
    (event : P → Ω → Prop) (B : ℝ) (hB : 0≤B)
    (hinv : ∀ p q, code p=code q → ∀ ω,event p ω → event q ω)
    (hp : ∀ p,good p → ((sample.filter (event p)).card:ℝ)/sample.card≤B) :
    ((sample.filter (fun ω => ∃ p,good p ∧ event p ω)).card:ℝ)/sample.card≤
      (Fintype.card C:ℝ)*B := by
  let Used := {c : C // ∃ p,good p ∧ code p=c}
  let representative (c : Used) : P := Classical.choose c.property
  have hr (c : Used) : good (representative c) ∧ code (representative c)=c.val :=
    Classical.choose_spec c.property
  have hc : sample.filter (fun ω => ∃ p,good p ∧ event p ω)⊆
      sample.filter (fun ω => ∃ c : Used,event (representative c) ω) := by
    intro ω hω
    obtain ⟨hω,p,hp,he⟩ := Finset.mem_filter.mp hω
    refine Finset.mem_filter.mpr ⟨hω,?_,?_⟩
    · exact ⟨code p,p,hp,rfl⟩
    · exact hinv p (representative ⟨code p,p,hp,rfl⟩) (hr (⟨code p,p,hp,rfl⟩ : Used)).2.symm ω he
  calc
    _ ≤ ((sample.filter (fun ω => ∃ c : Used,event (representative c) ω)).card:ℝ)/sample.card :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hc)) (Nat.cast_nonneg _)
    _ ≤ (Fintype.card Used:ℝ)*B :=
      StageFusion.pattern_union sample hs _ B (fun c => hp _ (hr c).1)
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Fintype.card_subtype_le _)) hB

end TorsionFreeZeroDivisors.PatternFiniteUnion

namespace TorsionFreeZeroDivisors.BoundedPattern.Data

section
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks RankedSuppressionIso
variable {R K T I H : ℕ} (a b : Data R K T I H)

def event (rep : ℕ) (x : Types.VertexA rep) (y : Types.VertexB rep) (r : ActualPatternEvent.Match rep) : Prop :=
  OriginalPattern.Realized a.graph a.mark a.degree_two a.side a.side_edge a.paths a.nonempty
    a.root rep x y a.comparisons r

/-- Equal finite codes transport every fixed matching event, including both
pinned source sides. The code does not contain any graph labels. -/
theorem event_of_encode_eq (hR : 0<R) (hK : 0<K) (hI : 0<I)
    (he : a.encode hR hK hI=b.encode hR hK hI)
    (rep : ℕ) (x : Types.VertexA rep) (y : Types.VertexB rep) (r : ActualPatternEvent.Match rep)
    (hb : b.event rep x y r) : a.event rep x y r := by
  obtain ⟨f,g,hpg,hrank,hside⟩ := PatternTotalCoding.complete R K T I H hR hK hI
    a.dart_bound a.vertex_bound a.path_bound a.comparison_bound
    b.dart_bound b.vertex_bound b.path_bound b.comparison_bound
    a.graphData (fun v => a.side v.val) a.geometryData
    b.graphData (fun v => b.side v.val) b.geometryData he
  let f₀ : PortSubdivision.Iso (skeleton a.graph a.mark a.degree_two)
      (skeleton b.graph b.mark b.degree_two) :=
    ⟨f.vertex,f.dart,f.origin_eq,f.reverse_eq⟩
  have hlen (d : a.Seeds) : chainLength a.graph a.mark a.degree_two d=
      chainLength b.graph b.mark b.degree_two (f₀.dart d) := congrArg Fin.val (f.length_eq d)
  let F := full a.graph a.mark a.degree_two b.graph b.mark b.degree_two a.covered b.covered f₀ hrank hlen
  have words (p : a.P) : ((a.paths p).flatMap (word a.graph a.mark a.degree_two)).map F.dart=
      (b.paths (f.path p)).flatMap (word b.graph b.mark b.degree_two) :=
    full_words a.graph a.mark a.degree_two b.graph b.mark b.degree_two a.covered b.covered
      f₀ hrank hlen a.paths b.paths f.path f.paths_eq p
  have hroot : a.root.map f.path=b.root := by
    have hh := congrArg (Option.map Prod.fst) f.root_eq
    simpa [graphData,Option.map_map,Function.comp_def] using hh
  have sides (v : a.V) : a.side v=b.side (F.vertex v) :=
    full_side a.graph a.mark a.degree_two b.graph b.mark b.degree_two a.covered b.covered f₀ hrank hlen
      a.side b.side a.side_edge b.side_edge hside v
  have roots : (StageRoot.source a.graph a.mark a.degree_two a.paths a.nonempty a.root).map F.vertex=
      StageRoot.source b.graph b.mark b.degree_two b.paths b.nonempty b.root :=
    full_source a.graph a.mark a.degree_two b.graph b.mark b.degree_two a.covered b.covered f₀ hrank hlen
      a.paths b.paths f.path f.paths_eq a.nonempty b.nonempty a.root b.root hroot
  let geometry : ComparisonGeometry.Iso a.comparisons b.comparisons := {
    path := f.path
    comparison := g.comparison
    length_eq := OriginalPatternIso.length_eq a.graph a.mark a.degree_two b.graph b.mark b.degree_two
      a.paths b.paths F f.path words
    flip_eq := g.flip_eq
    source_eq := by intro e; rw [hpg]; exact g.source_eq e
    lo_eq := by
      intro e
      rw [a.lower_eq,b.lower_eq]
      exact_mod_cast congrArg Fin.val (g.lower_eq e)
    hi_eq := by
      intro e
      rw [a.upper_eq,b.upper_eq]
      exact_mod_cast congrArg Fin.val (g.upper_eq e)
    reverse_eq := g.reverse_eq
    offset_eq := by
      intro e
      rw [a.offset_eq,b.offset_eq]
      have ho := congrArg Fin.val (g.offset_eq e)
      exact congrArg (fun n : ℕ => (n:ℤ)-2*H) ho }
  exact OriginalPatternIso.realized a.graph a.mark a.degree_two b.graph b.mark b.degree_two
    a.paths a.nonempty b.paths b.nonempty F f.path words a.side b.side a.side_edge b.side_edge
    sides a.root b.root roots a.comparisons b.comparisons geometry rfl rep x y r hb

end

open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks ActualPatternEvent
open GridAsymptotics GirthAsymptotics TypedGraphs
variable {R K T I H : ℕ} (a : Data R K T I H)

abbrev multiplicity := ChunkComparisons.multiplicity (color a.graph a.mark a.degree_two a.paths)
abbrev totalLength : ℝ := ∑ p, (((a.paths p).flatMap (word a.graph a.mark a.degree_two)).length:ℝ)

/-- The manuscript's deterministic hypotheses for the bounded first moment.
Every condition concerns only the unlabeled graph, paths or comparisons. -/
structure Good (B Q M J rep : ℕ) : Prop where
  multiplicity_le : ∀ c,a.multiplicity c≤M
  multiplicity_pos : ∀ c,1≤a.multiplicity c
  path_chain : ∀ p,List.IsChain (WeightedMoore.PortWalk.step
    (suppressed a.graph a.mark a.degree_two).origin (suppressed a.graph a.mark a.degree_two).reverse) (a.paths p)
  cyclic_chain : ∀ p,StageRoot.cyclic a.root p=true →
    ∀ᵉ (x∈(a.paths p).getLast?) (y∈(a.paths p).head?),
      WeightedMoore.PortWalk.step (suppressed a.graph a.mark a.degree_two).origin
        (suppressed a.graph a.mark a.degree_two).reverse x y
  reduced : ∀ x e,a.comparisons.side x=some e →
    originalDart a.graph a.mark a.degree_two a.paths x≠
      originalDart a.graph a.mark a.degree_two a.paths (a.comparisons.pairing.partner x) ∧
    originalDart a.graph a.mark a.degree_two a.paths x≠a.graph.reverse
      (originalDart a.graph a.mark a.degree_two a.paths (a.comparisons.pairing.partner x))
  chains_le : Fintype.card (Rep a.graph a.mark a.degree_two)≤Q
  cut_comparisons_le : Fintype.card a.E*(Fintype.card (RepeatedBlocks.Traversal a.multiplicity))^2≤J
  length_le : a.totalLength≤B*(L (size rep):ℝ)
  length_ge : (L (size rep):ℝ)≤a.totalLength
  unpaired_le : ((Finset.univ.filter (fun x => a.comparisons.pairing.partner x=x)).card:ℝ)≤
    StageFusion.epsilon (1/600) 256*a.totalLength

lemma probability_bound (B Q M J rep : ℕ) (hM : 0<M) (hready : PatternUniform.Ready B M Q J rep)
    (hg : a.Good B Q M J rep) (x : Types.VertexA rep) (y : Types.VertexB rep) :
    (((samples rep).filter (a.event rep x y)).card:ℝ)/(samples rep).card≤
      Real.exp (-(L (size rep):ℝ)/(4800*M)) := by
  exact OriginalPattern.probability_bound a.graph a.mark a.degree_two a.side a.side_edge a.paths a.nonempty
    a.root rep x y a.comparisons (fun e => (a.lower e).val) (fun e => (a.upper e).val)
    (by simpa only [Int.cast_natCast] using a.lower_eq)
    (by simpa only [Int.cast_natCast] using a.upper_eq)
    B Q M J hM hready hg.multiplicity_le hg.multiplicity_pos hg.path_chain hg.cyclic_chain
    hg.reduced hg.chains_le hg.cut_comparisons_le hg.length_le hg.length_ge hg.unpaired_le

end TorsionFreeZeroDivisors.BoundedPattern.Data

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical
open ActualPatternEvent GirthAsymptotics TypedGraphs

/-- Uniform first-moment union over every actual-carrier pattern, not over a
postulated finite list of realizations. -/
theorem probability_union (R K T I H B Q M J rep : ℕ)
    (hR : 0<R) (hK : 0<K) (hI : 0<I) (hM : 0<M)
    (hs : (samples rep).Nonempty) (hready : PatternUniform.Ready B M Q J rep)
    (x : Types.VertexA rep) (y : Types.VertexB rep) :
    (((samples rep).filter (fun r => ∃ a : Data R K T I H,a.Good B Q M J rep ∧ a.event rep x y r)).card:ℝ)/
      (samples rep).card≤
      (PatternTotalCoding.coefficient R K T I:ℝ)*(H+1:ℕ)^(R+3*I)*
        Real.exp (-(L (size rep):ℝ)/(4800*M)) := by
  have he := PatternFiniteUnion.bound (samples rep) hs (fun a : Data R K T I H => a.encode hR hK hI)
    (fun a => a.Good B Q M J rep) (fun a => a.event rep x y) _ (Real.exp_pos _).le
    (fun a b hab r ha => b.event_of_encode_eq a hR hK hI hab.symm rep x y r ha)
    (fun a ha => a.probability_bound B Q M J rep hM hready ha x y)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact_mod_cast PatternTotalCoding.card_code_bound R K T I H

end TorsionFreeZeroDivisors.BoundedPattern

namespace TorsionFreeZeroDivisors.ActualComplexity
open scoped Classical BigOperators
open PortSubdivision DegreeTwoSuppression CoreStripping ImageComplexity
open ChainSuppression SuppressedMoore ChainPaths ChainIsomorphism ChainChunkTransport
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P] (Γ : PortGraph V D)

omit [Fintype V] in
lemma leaf_unique {v : V} (hv : degree Γ Finset.univ v=1) {a b : D}
    (ha : Γ.origin a=v) (hb : Γ.origin b=v) : a=b := by
  obtain ⟨d,hd⟩ := Finset.card_eq_one.mp hv
  have hma : a∈Finset.univ.filter (fun d => Γ.origin d=v) := by simp [ha]
  have hmb : b∈Finset.univ.filter (fun d => Γ.origin d=v) := by simp [hb]
  change Finset.univ.filter (fun d => Γ.origin d=v)={d} at hd
  rw [hd] at hma hmb
  exact (Finset.mem_singleton.mp hma).trans (Finset.mem_singleton.mp hmb).symm

omit [Fintype V] in
lemma step_not_leaf {a b : D} (h : WeightedMoore.PortWalk.step Γ.origin Γ.reverse a b) :
    degree Γ Finset.univ (Γ.origin b)≠1 ∧ degree Γ Finset.univ (Γ.origin (Γ.reverse a))≠1 := by
  constructor <;> intro he
  · exact h.2 (leaf_unique Γ he rfl h.1)
  · exact h.2 (leaf_unique Γ he h.1.symm rfl)

omit [Fintype V] in
lemma origin_leaf_head (p : List D)
    (hp : p.IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    {d : D} (hd : d∈p) (hv : degree Γ Finset.univ (Γ.origin d)=1) : d∈p.head? := by
  induction p with
  | nil => simp at hd
  | cons a p ih =>
    rcases List.mem_cons.mp hd with rfl|hd
    · simp
    · have hh := ih hp.tail hd
      cases p with
      | nil => simp at hd
      | cons b p =>
        have he : b=d := by simpa using hh
        subst d
        exact ((step_not_leaf Γ (List.isChain_cons_cons.mp hp).1).1 hv).elim

omit [Fintype V] in
lemma target_leaf_last (p : List D)
    (hp : p.IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    {d : D} (hd : d∈p) (hv : degree Γ Finset.univ (Γ.origin (Γ.reverse d))=1) :
    d∈p.getLast? := by
  induction p with
  | nil => simp at hd
  | cons a p ih =>
    cases p with
    | nil => simpa only [List.getLast?_singleton,Option.mem_some_iff] using (List.mem_singleton.mp hd).symm
    | cons b p =>
      rcases List.mem_cons.mp hd with rfl|hd
      · exact ((step_not_leaf Γ (List.isChain_cons_cons.mp hp).1).2 hv).elim
      · simpa only [List.getLast?_cons_cons] using ih hp.tail hd

variable (paths : P → List D) (hp : ∀ p,paths p≠[])
def start (p : P) : D := (paths p).head (hp p)
def finish (p : P) : D := (paths p).getLast (hp p)
def endpoints : Finset V :=
  (Finset.univ.image fun p => Γ.origin (start paths hp p)) ∪
    (Finset.univ.image fun p => Γ.origin (Γ.reverse (finish paths hp p)))

omit [Fintype V] [Fintype D] in
lemma endpoints_card : (endpoints Γ paths hp).card≤2*Fintype.card P := by
  exact (Finset.card_union_le _ _).trans (by
    have ha := Finset.card_image_le (s:=Finset.univ) (f:=fun p => Γ.origin (start paths hp p))
    have hb := Finset.card_image_le (s:=Finset.univ) (f:=fun p => Γ.origin (Γ.reverse (finish paths hp p)))
    rw [Finset.card_univ] at ha hb
    omega)

omit [Fintype V] [Fintype D] in
lemma start_mem (p : P) {d : D} (hd : d∈(paths p).head?) : Γ.origin d∈endpoints Γ paths hp := by
  have he : start paths hp p=d := by
    simpa only [start,List.head?_eq_some_head (hp p),Option.mem_some_iff] using hd
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,congrArg Γ.origin he⟩

omit [Fintype V] [Fintype D] in
lemma finish_mem (p : P) {d : D} (hd : d∈(paths p).getLast?) :
    Γ.origin (Γ.reverse d)∈endpoints Γ paths hp := by
  have he : finish paths hp p=d := by
    simpa only [finish,List.getLast?_eq_some_getLast (hp p),Option.mem_some_iff] using hd
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,congrArg (fun d => Γ.origin (Γ.reverse d)) he⟩

include hp in
lemma leaf_bound
    (hc : ∀ p,(paths p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    (hi : ∀ d,∃ p,d∈paths p ∨ Γ.reverse d∈paths p) :
    (Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card≤2*Fintype.card P := by
  apply (Finset.card_le_card ?_).trans (endpoints_card Γ paths hp)
  intro v hv
  have hv := (Finset.mem_filter.mp hv).2
  obtain ⟨d,hd⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun d => Γ.origin d=v)).card by
    change 0<degree Γ Finset.univ v
    omega)
  have ho := (Finset.mem_filter.mp hd).2
  obtain ⟨p,hp'⟩ := hi d
  rcases hp' with hm|hm
  · exact ho ▸ start_mem Γ paths hp p (origin_leaf_head Γ _ (hc p) hm (ho ▸ hv))
  · have he : degree Γ Finset.univ (Γ.origin (Γ.reverse (Γ.reverse d)))=1 := by simpa [ho] using hv
    have ht := finish_mem Γ paths hp p (target_leaf_last Γ _ (hc p) hm he)
    rw [Γ.reverse_reverse d,ho] at ht
    exact ht

omit [Fintype V] in
lemma dart_count (hi : ∀ d,∃ p,d∈paths p ∨ Γ.reverse d∈paths p) :
    Fintype.card D≤2*∑ p,(paths p).length := by
  let f : ((p : P) × Fin (paths p).length) × Bool → D := fun o =>
    if o.2 then Γ.reverse ((paths o.1.1).get o.1.2) else (paths o.1.1).get o.1.2
  have hs : Function.Surjective f := by
    intro d
    obtain ⟨p,hp⟩ := hi d
    rcases hp with hp|hp
    · obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
      exact ⟨(⟨p,i⟩,false),hi⟩
    · obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
      refine ⟨(⟨p,i⟩,true),?_⟩
      change Γ.reverse ((paths p).get i)=d
      rw [hi,Γ.reverse_reverse]
  have hh := Fintype.card_le_of_surjective f hs
  simpa only [Fintype.card_prod,Fintype.card_bool,Fintype.card_sigma,Fintype.card_fin,Nat.mul_comm] using hh

lemma marked_vertices_le (mark : V → Prop)
    (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (hv : Function.Surjective Γ.origin) :
    Fintype.card (Mark mark)≤Fintype.card {d : D // turn Γ.origin mark h2 d=d} := by
  let f : {d : D // turn Γ.origin mark h2 d=d} → Mark mark := fun d =>
    ⟨Γ.origin d.val,(turn_fixed_iff Γ.origin mark h2 d.val).mp d.property⟩
  apply Fintype.card_le_of_surjective f
  intro v
  obtain ⟨d,hd⟩ := hv v.val
  refine ⟨⟨d,turn_of_mark Γ.origin mark h2 d (hd ▸ v.property)⟩,?_⟩
  exact Subtype.ext hd

/-- Complexity is uniform before choosing any finite actual image. The coarser
2K leaf bound suffices and does not assume any of the image complexity estimates. -/
theorem bounded_suppression (B K : ℕ) : ∃ R : ℕ,0<R ∧
    ∀ {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
      (Γ : PortGraph V D) (paths : P → List D) (hp : ∀ p,paths p≠[])
      (_ : Fintype.card P≤K) (_ : Function.Surjective Γ.origin)
      (_ : ∀ p,(paths p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
      (_ : ∀ d,∃ p,d∈paths p ∨ Γ.reverse d∈paths p)
      (L : ℝ) (_ : 0<L) (_ : (∑ p,(paths p).length:ℕ)≤(B:ℝ)*L)
      (_ : ∀ a (c : Γ.subdivision.Walk a a),c.IsCycle →
        L≤WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : D => (1:ℝ))) c),
      let M := endpoints Γ paths hp
      let mark := MarkedChainBound.marks Γ M
      let h2 := MarkedChainBound.marks_degree_two Γ M
      Fintype.card {d : D // turn Γ.origin mark h2 d=d}≤R ∧
        Fintype.card (Mark mark)≤R := by
  obtain ⟨R,hR⟩ := bounded_image_branches (B:ℝ) (Nat.cast_nonneg _) (2*K)
  refine ⟨R+6*K+1,by omega,?_⟩
  intro V D P _ _ _ Γ paths hp hP hv hc hi L hL hH hg
  dsimp only
  have hleaf := leaf_bound Γ paths hp hc hi
  have hdc := dart_count Γ paths hi
  have hdc' : (Fintype.card D:ℝ)≤2*(B:ℝ)*L := by
    have hdc' : (Fintype.card D:ℝ)≤2*(∑ p,(paths p).length:ℕ) := by exact_mod_cast hdc
    nlinarith
  have hleaf' : (Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card≤2*K :=
    hleaf.trans (Nat.mul_le_mul_left _ hP)
  have hb := hR Γ L hL hdc' hg hleaf'
  have hm := endpoints_card Γ paths hp
  have hd := MarkedChainBound.marked_dart_bound Γ (endpoints Γ paths hp)
  have hseed : Fintype.card {d : D //
      turn Γ.origin (MarkedChainBound.marks Γ (endpoints Γ paths hp))
        (MarkedChainBound.marks_degree_two Γ (endpoints Γ paths hp)) d=d}≤R+6*K+1 := by
    rw [MarkedChainBound.chain_dart_card]
    omega
  exact ⟨hseed,(marked_vertices_le Γ _ _ hv).trans hseed⟩

end TorsionFreeZeroDivisors.ActualComplexity

end

end OAI
