import Mathlib
import OAI.Algebra.GroupRing.FiniteClusters

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ClusterLocalization

section
open scoped Classical BigOperators
open ComparedBlocks
variable {T E : Type} [Fintype T] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop)
local instance clusterFintype : Fintype (Cluster C keep) := Fintype.ofFinite _

def pathEquiv (c : Cluster C keep) : {t // belongs C keep c t} ≃
    {v : {t // keep t} // (graph C keep).connectedComponentMk v=c} where
  toFun t := by
    have hk : keep t.val := (cluster_exists C keep).mp ⟨c,t.property⟩
    refine ⟨⟨t.val,hk⟩,?_⟩
    have he := PairingClusters.cluster_some (fun x : Position len => x.1)
      C.pairing.partner C.pairing.involutive keep hk
    exact Option.some.inj (he.symm.trans t.property)
  invFun v := ⟨v.val.val,by
    change PairingClusters.cluster _ _ _ _ v.val.val=some c
    rw [PairingClusters.cluster_some _ _ _ _ v.val.property]
    exact congrArg some v.property⟩
  left_inv t := Subtype.ext rfl
  right_inv v := Subtype.ext (Subtype.ext rfl)

lemma paths_card (c : Cluster C keep) : (paths C keep c).card=(FiniteClusters.block (graph C keep) c).card := by
  simpa only [Fintype.card_subtype,paths,FiniteClusters.block] using Fintype.card_congr (pathEquiv C keep c)
lemma member_exists (c : Cluster C keep) : ∃ t,belongs C keep c t := by
  obtain ⟨v,hv⟩ := FiniteClusters.block_nonempty (graph C keep) c
  let t := (pathEquiv C keep c).symm ⟨v,(FiniteClusters.mem_block _).mp hv⟩
  exact ⟨t.val,t.property⟩

/-- A closed retained subset supplied by recursive separation bounds the
actual connected component, even when the pairing has loops or parallel arcs. -/
lemma paths_card_le {K : ℕ}
    (hs : ∀ t,keep t → ∃ B : Finset T,t∈B ∧ B.card≤K ∧
      ∀ x∈B,∀ y,keep y → PairingClusters.Rel (fun x : Position len=>x.1) C.pairing.partner x y → y∈B)
    (c : Cluster C keep) : (paths C keep c).card≤K := by
  rw [paths_card]
  apply FiniteClusters.block_card
  intro t
  obtain ⟨B,hB,hBK,hcl⟩ := hs t.val t.property
  refine ⟨B.subtype keep,?_,?_,?_⟩
  · simpa only [Finset.mem_subtype] using hB
  · exact (by rw [Finset.card_subtype]; exact Finset.card_filter_le _ _ : (B.subtype keep).card≤B.card).trans hBK
  · intro x hx y hxy
    have hx' : x.val∈B := by simpa only [Finset.mem_subtype] using hx
    have hy := hcl x.val hx' y.val y.property hxy.2
    simpa only [Finset.mem_subtype] using hy

lemma mass_upper {K cap : ℕ} (hK : ∀ c : Cluster C keep,(paths C keep c).card≤K)
    (hcap : ∀ t,len t≤cap) (c : Cluster C keep) : mass C keep c≤K*cap := by
  calc
    _ ≤ ∑ _t∈paths C keep c,cap := Finset.sum_le_sum fun t _=>hcap t
    _ = (paths C keep c).card*cap := by simp
    _ ≤ K*cap := Nat.mul_le_mul_right _ (hK c)

lemma mass_lower {L : ℕ} (hL : ∀ t,L≤len t) (c : Cluster C keep) : L ≤ mass C keep c := by
  obtain ⟨t,ht⟩ := member_exists C keep c
  apply (hL t).trans
  exact Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)

lemma short_mass_refined {L : ℕ} (root : Option T)
    (ho : ∀ t,root≠some t → L≤len t) :
    (∑ c∈Finset.univ.filter (fun c=>mass C keep c<L),mass C keep c)≤
      ∑ t∈Finset.univ.filter (fun t=>root=some t ∧ len t<L),len t := by
  cases root with
  | none => simpa using short_mass C keep none ho
  | some r =>
    by_cases h : len r<L
    · have he : Finset.univ.filter (fun t=>some r=some t ∧ len t<L)=
          Finset.univ.filter (fun t=>some r=some t) := by
        ext t
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,Option.some.injEq]
        constructor
        · exact And.left
        · intro ht; exact ⟨ht,ht ▸ h⟩
      rw [he]
      exact short_mass C keep (some r) ho
    · have hall : ∀ t,L≤len t := by
        intro t
        by_cases ht : r=t
        · subst t; omega
        · exact ho t (fun he=>ht (Option.some.inj he))
      have hn : ∀ c : Cluster C keep,¬mass C keep c<L :=
        fun c=>not_lt_of_ge (mass_lower C keep hall c)
      simp only [Finset.filter_false_of_mem (fun c _=>hn c),Finset.sum_empty,Nat.zero_le]

lemma short_mass_half {L : ℕ} (root : Option T) (H₀ : ℝ) (hH₀ : 0≤H₀)
    (ho : ∀ t,root≠some t → L≤len t)
    (hr : ∀ t,root=some t → len t<L → (len t:ℝ)≤H₀/2) :
    ((∑ c∈Finset.univ.filter (fun c=>mass C keep c<L),mass C keep c):ℝ)≤H₀/2 := by
  have hh : ((∑ c∈Finset.univ.filter (fun c=>mass C keep c<L),mass C keep c):ℝ)≤
      ((∑ t∈Finset.univ.filter (fun t=>root=some t ∧ len t<L),len t):ℝ) := by
    exact_mod_cast short_mass_refined C keep root ho
  apply hh.trans
  cases root with
  | none => simp only [reduceCtorEq,false_and]; simp; positivity
  | some r =>
    by_cases h : len r<L
    · have he : (Finset.univ.filter (fun t=>some r=some t ∧ len t<L))={r} := by ext t; simp; aesop
      rw [he,Finset.sum_singleton]
      exact hr r rfl h
    · have he : (Finset.univ.filter (fun t=>some r=some t ∧ len t<L))=∅ := by ext t; simp; aesop
      rw [he,Finset.sum_empty]
      positivity
end

open scoped Classical BigOperators
open ComparedBlocks
variable {T E : Type} [Fintype T] [Fintype E] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop)
local instance selectedClusterFintype : Fintype (Cluster C keep) := Fintype.ofFinite _

omit [Fintype E] in
/-- Retained closures are nonnegative; only deleted original positions are
charged in the lower bound for retained mass. -/
lemma retained_original (old : T → ℕ) (ho : ∀ t,old t≤len t) :
    (∑t,old t)≤(∑c,mass C keep c)+∑t∈Finset.univ.filter (fun t=>¬keep t),old t := by
  rw [mass_sum]
  calc
    _ = (∑t∈Finset.univ.filter keep,old t)+∑t∈Finset.univ.filter (fun t=>¬keep t),old t :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ _ := Nat.add_le_add_right (Finset.sum_le_sum fun t _=>ho t) _

/-- An averaging argument on the actual connected components of the
retained pairing graph. E counts oriented interval sides, hence its factor 2. -/
theorem exists_selected (old : T → ℕ) (ho : ∀ t,old t≤len t)
    (root : Option T) (L K cap : ℕ) (H₀ ε C₂ : ℝ)
    (hH₀ : 0<H₀) (hL : 0<L) (hε : 0<ε) (hC₂ : 0<C₂)
    (hsize : ∀ c : Cluster C keep,(paths C keep c).card≤K)
    (hcap : ∀ t,len t≤cap*L)
    (hbase : H₀≤∑t,(old t:ℝ))
    (hdelete : (∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ))≤H₀/16)
    (hbad : ((Finset.univ.filter (fun x : Position len=>C.pairing.partner x=x)).card:ℝ)+
      ((Finset.univ.filter (fun x : Position len=>¬keep x.1 ∧ C.pairing.partner x≠x)).card:ℝ)≤ε/16*H₀)
    (hcompare : (Fintype.card E:ℝ)/2≤C₂/(16*L)*H₀)
    (hlong : ∀ t,root≠some t → L≤len t)
    (hroot : ∀ t,root=some t → len t<L → (len t:ℝ)≤H₀/2) :
    ∃ c : Cluster C keep,L ≤ mass C keep c ∧ mass C keep c≤K*cap*L ∧
      (bad C keep c:ℝ)≤ε*mass C keep c ∧
      (comparisons C keep c:ℝ)/2≤C₂*mass C keep c/L := by
  have hret : 15/16*H₀≤∑c,(mass C keep c:ℝ) := by
    have hh : (∑t,(old t:ℝ))≤(∑c,(mass C keep c:ℝ))+
        ∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ) := by
      exact_mod_cast retained_original C keep old ho
    linarith
  have hb : (∑c,(bad C keep c:ℝ))≤ε/16*H₀ := by
    have hh : (∑c,(bad C keep c:ℝ))≤
        ((Finset.univ.filter (fun x : Position len=>C.pairing.partner x=x)).card:ℝ)+
        ((Finset.univ.filter (fun x : Position len=>¬keep x.1 ∧ C.pairing.partner x≠x)).card:ℝ) := by
      exact_mod_cast bad_sum C keep
    exact hh.trans hbad
  have hi : (∑c,(comparisons C keep c:ℝ)/2)≤C₂/(16*L)*H₀ := by
    rw [←Finset.sum_div]
    apply le_trans _ hcompare
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact_mod_cast comparisons_sum C keep
  have hu : ∀ c : Cluster C keep,(mass C keep c:ℝ)≤(K*cap:ℝ)*L := by
    intro c
    have h := mass_upper C keep hsize hcap c
    rw [←Nat.mul_assoc] at h
    exact_mod_cast h
  have hs : (∑c∈Finset.univ.filter (fun c=>(mass C keep c:ℝ)<L),(mass C keep c:ℝ))≤H₀/2 := by
    have h := short_mass_half C keep root H₀ hH₀.le hlong hroot
    simpa only [Nat.cast_sum,Nat.cast_lt] using h
  obtain ⟨c,hcl,hcu,hcb,hci⟩ := PlanarLocalization.exists_good_cluster
    (fun c=>(mass C keep c:ℝ)) (fun c=>(bad C keep c:ℝ))
    (fun c=>(comparisons C keep c:ℝ)/2) H₀ L ε (K*cap) C₂ hH₀
    (by exact_mod_cast hL) hε hC₂ (fun _=>Nat.cast_nonneg _) (fun _=>Nat.cast_nonneg _)
    (fun _=>by positivity) hu hret hb hi hs
  refine ⟨c,?_,?_,hcb,hci⟩
  · exact_mod_cast hcl
  · exact_mod_cast hcu
end TorsionFreeZeroDivisors.ClusterLocalization
namespace TorsionFreeZeroDivisors.RestrictComparisons
open scoped Classical
variable {T : Type} (root : Option T) (keep : T → Prop)
def rootPath : Option {t // keep t} := root.bind fun t=>if h : keep t then some ⟨t,h⟩ else none
lemma rootPath_some (t : {t // keep t}) : rootPath root keep=some t ↔ root=some t.val := by
  cases root with
  | none => simp [rootPath]
  | some r =>
    by_cases hr : keep r
    · simp only [rootPath,Option.bind_some,dite_eq_left hr,Option.some.injEq,Subtype.ext_iff]
    · simp only [rootPath,Option.bind_some,dite_eq_right hr,reduceCtorEq,false_iff,Option.some.injEq]
      intro h; subst r; exact hr t.property
lemma rootPath_cyclic (t : {t // keep t}) : StageRoot.cyclic (rootPath root keep) t=StageRoot.cyclic root t.val := by
  simp only [StageRoot.cyclic,ne_eq,rootPath_some]
lemma rootPath_map {Z : Type} (f : T → Z) {z : Z}
    (h : (rootPath root keep).map (f ∘ Subtype.val)=some z) : root.map f=some z := by
  cases root with
  | none => simp [rootPath] at h
  | some r =>
    by_cases hr : keep r
    · simpa only [rootPath,Option.bind_some,dite_eq_left hr,Option.map_some,Function.comp_apply] using h
    · simp only [rootPath,Option.bind_some,dite_eq_right hr,Option.map_none,reduceCtorEq] at h
end TorsionFreeZeroDivisors.RestrictComparisons

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent
/-- Literal path/comparison data before the separator and averaging step.
Unlike BoundedSystem it makes no quantitative smallness or pairing assumption. -/
structure PathSystem (rep : ℕ) (r : Match rep) (x : VA rep) (y : VB rep) where
  P : Type
  E : Type
  [fP : Fintype P]
  [fE : Fintype E]
  paths : P → List (DA rep⊕DB rep)
  nonempty : ∀ p,paths p≠[]
  root : Option P
  path_chain : ∀ p,(paths p).IsChain (WeightedMoore.PortWalk.step (graph rep r).origin (graph rep r).reverse)
  cyclic_chain : ∀ p,StageRoot.cyclic root p=true →
    ∀ᵉ (x∈(paths p).getLast?) (y∈(paths p).head?),
      WeightedMoore.PortWalk.step (graph rep r).origin (graph rep r).reverse x y
  comparisons : Comparisons (E:=E) (fun p => (paths p).length)
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e,comparisons.lo e=lower e
  upper_eq : ∀ e,comparisons.hi e=upper e
  lower_le : ∀ e,lower e≤upper e
  upper_le : ∀ e,upper e≤(paths (comparisons.source e)).length
  reduced : ∀ x e,comparisons.side x=some e →
    RawDecomposition.dart paths x≠RawDecomposition.dart paths (comparisons.pairing.partner x) ∧
    RawDecomposition.dart paths x≠(graph rep r).reverse (RawDecomposition.dart paths (comparisons.pairing.partner x))
  rootA : ∀ z,root.map (fun p => (graph rep r).origin ((paths p).head (nonempty p)))=some (.inl z) → z=x
  rootB : ∀ z,root.map (fun p => (graph rep r).origin ((paths p).head (nonempty p)))=some (.inr z) → z=y
  compatible : ∀ p e,comparisons.side p=some e → label rep (RawDecomposition.dart paths p)=
    if comparisons.reverse e then Types.inverse (label rep (RawDecomposition.dart paths (comparisons.pairing.partner p)))
    else label rep (RawDecomposition.dart paths (comparisons.pairing.partner p))
attribute [instance] PathSystem.fP PathSystem.fE
namespace PathSystem
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (keep : s.P → Prop)
lemma dart_embed (p : Position (fun t : {t // keep t}=>(s.paths t.val).length)) :
    RawDecomposition.dart (fun t : {t // keep t}=>s.paths t.val) p=
      RawDecomposition.dart s.paths (RestrictComparisons.embed keep p) := rfl

abbrev restrict : PathSystem rep r x y where
  P := {p // keep p}
  E := {e // RestrictComparisons.Active s.comparisons keep e}
  fP := inferInstance
  fE := inferInstance
  paths := fun p=>s.paths p.val
  nonempty := fun p=>s.nonempty p.val
  root := RestrictComparisons.rootPath s.root keep
  path_chain := fun p=>s.path_chain p.val
  cyclic_chain := by
    intro p hp
    exact s.cyclic_chain p.val ((RestrictComparisons.rootPath_cyclic s.root keep p) ▸ hp)
  comparisons := RestrictComparisons.comparisons s.comparisons keep
  lower := fun e=>s.lower e.val
  upper := fun e=>s.upper e.val
  lower_eq := fun e=>s.lower_eq e.val
  upper_eq := fun e=>s.upper_eq e.val
  lower_le := fun e=>s.lower_le e.val
  upper_le := fun e=>s.upper_le e.val
  reduced := by
    intro p e he
    have hh := s.reduced (RestrictComparisons.embed keep p) e.val
      ((RestrictComparisons.side_some s.comparisons keep p e).mp he)
    rw [←RestrictComparisons.partner_image_of_side s.comparisons keep he] at hh
    exact hh
  rootA := fun z hz=>s.rootA z (RestrictComparisons.rootPath_map s.root keep
    (fun p=>(graph rep r).origin ((s.paths p).head (s.nonempty p))) hz)
  rootB := fun z hz=>s.rootB z (RestrictComparisons.rootPath_map s.root keep
    (fun p=>(graph rep r).origin ((s.paths p).head (s.nonempty p))) hz)
  compatible := by
    intro p e he
    have hh := s.compatible (RestrictComparisons.embed keep p) e.val
      ((RestrictComparisons.side_some s.comparisons keep p e).mp he)
    rw [←RestrictComparisons.partner_image_of_side s.comparisons keep he] at hh
    exact hh

/-- Bounding a literal system adds no realizability or word constraints. -/
def bounded {Bnd K I : ℕ}
    (hP : Fintype.card s.P≤K) (hE : Fintype.card s.E≤I)
    (hlo : L (size rep)≤∑p,(s.paths p).length)
    (hhi : (∑p,(s.paths p).length)≤Bnd*L (size rep))
    (hbad : ((Finset.univ.filter (fun p=>s.comparisons.pairing.partner p=p)).card:ℝ)≤
      StageFusion.epsilon (1/600) 256*(∑p,(s.paths p).length:ℕ)) : BoundedSystem Bnd K I rep r x y where
  P := s.P
  E := s.E
  paths := s.paths
  nonempty := s.nonempty
  root := s.root
  path_bound := hP
  comparison_bound := hE
  path_chain := s.path_chain
  cyclic_chain := s.cyclic_chain
  length_le := hhi
  length_ge := hlo
  comparisons := s.comparisons
  lower := s.lower
  upper := s.upper
  lower_eq := s.lower_eq
  upper_eq := s.upper_eq
  lower_le := s.lower_le
  upper_le := s.upper_le
  reduced := s.reduced
  unpaired_le := hbad
  rootA := s.rootA
  rootB := s.rootB
  compatible := s.compatible
end PathSystem
end TorsionFreeZeroDivisors.SampleGraph
namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open ComparedBlocks ClusterLocalization GirthAsymptotics TypedGraphs ActualPatternEvent
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (keep : s.P → Prop)
local instance : Fintype (Cluster s.comparisons keep) := Fintype.ofFinite _

/-- Realizes the selected component by exactly its literal retained paths and
interval sides, with the same signs, noncoincident lifts, and prescribed root. -/
def selected_bounded {Bnd K I : ℕ} (c : Cluster s.comparisons keep)
    (hP : (ClusterLocalization.paths s.comparisons keep c).card≤K)
    (hE : ClusterLocalization.comparisons s.comparisons keep c≤I)
    (hlo : L (size rep) ≤ mass s.comparisons keep c)
    (hhi : mass s.comparisons keep c≤Bnd*L (size rep))
    (hbad : (bad s.comparisons keep c:ℝ)≤
      StageFusion.epsilon (1/600) 256*mass s.comparisons keep c) :
    BoundedSystem Bnd K I rep r x y := by
  let sc := s.restrict (belongs s.comparisons keep c)
  refine {
    P := {p // belongs s.comparisons keep c p}
    E := {e // RestrictComparisons.Active s.comparisons (belongs s.comparisons keep c) e}
    fP := inferInstance
    fE := inferInstance
    paths := fun p=>s.paths p.val
    nonempty := fun p=>s.nonempty p.val
    root := sc.root
    path_bound := ?_
    comparison_bound := hE
    path_chain := sc.path_chain
    cyclic_chain := sc.cyclic_chain
    length_le := ?_
    length_ge := ?_
    comparisons := localC s.comparisons keep c
    lower := sc.lower
    upper := sc.upper
    lower_eq := sc.lower_eq
    upper_eq := sc.upper_eq
    lower_le := sc.lower_le
    upper_le := sc.upper_le
    reduced := sc.reduced
    unpaired_le := ?_
    rootA := sc.rootA
    rootB := sc.rootB
    compatible := sc.compatible }
  · simpa only [Fintype.card_subtype,ClusterLocalization.paths] using hP
  · rw [local_mass]; exact hhi
  · rw [local_mass]; exact hlo
  · rw [←fixed_card s.comparisons keep c,←local_mass s.comparisons keep c] at hbad
    convert hbad using 2
    congr 1
    ext p
    simp

/-- The analytic union bound excludes the localized system using the sharp
mass and interval estimates. -/
theorem excluded_of_local_totals (K cap : ℕ) (C₂ H₀ : ℝ) (old : s.P → ℕ)
    (ho : ∀ t,old t≤(s.paths t).length)
    (hH₀ : 0<H₀) (hL : 0<L (size rep)) (hC₂ : 0<C₂)
    (hsize : ∀ c : Cluster s.comparisons keep,(ClusterLocalization.paths s.comparisons keep c).card≤K)
    (hcap : ∀ t,(s.paths t).length≤cap*L (size rep))
    (hbase : H₀≤∑t,(old t:ℝ))
    (hdelete : (∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ))≤H₀/16)
    (hbad : ((Finset.univ.filter (fun p=>s.comparisons.pairing.partner p=p)).card:ℝ)+
      ((Finset.univ.filter (fun p=>¬keep p.1 ∧ s.comparisons.pairing.partner p≠p)).card:ℝ)≤
        StageFusion.epsilon (1/600) 256/16*H₀)
    (hcompare : (Fintype.card s.E:ℝ)/2≤C₂/(16*L (size rep))*H₀)
    (hlong : ∀ t,s.root≠some t → L (size rep)≤(s.paths t).length)
    (hroot : ∀ t,s.root=some t → (s.paths t).length<L (size rep) → ((s.paths t).length:ℝ)≤H₀/2)
    (havoid : IsEmpty (BoundedSystem (K*cap) K ⌈2*C₂*(K*cap:ℝ)⌉₊ rep r x y)) : False := by
  have hε : 0<StageFusion.epsilon (1/600) 256 := StageFusion.epsilon_pos (by norm_num) (by norm_num)
  obtain ⟨c,hlo,hhi,hb,hi⟩ := exists_selected s.comparisons keep old ho s.root
    (L (size rep)) K cap H₀ (StageFusion.epsilon (1/600) 256) C₂ hH₀ hL hε hC₂
    hsize hcap hbase hdelete hbad hcompare hlong hroot
  have he : ClusterLocalization.comparisons s.comparisons keep c≤⌈2*C₂*(K*cap:ℝ)⌉₊ := by
    suffices (ClusterLocalization.comparisons s.comparisons keep c:ℝ)≤(⌈2*C₂*(K*cap:ℝ)⌉₊:ℝ) by exact_mod_cast this
    apply le_trans _ (Nat.le_ceil _)
    have hLr : (0:ℝ)<L (size rep) := by exact_mod_cast hL
    have hi' := (le_div_iff₀ hLr).mp hi
    have hh : (mass s.comparisons keep c:ℝ)≤(K*cap:ℝ)*L (size rep) := by exact_mod_cast hhi
    have hm := mul_le_mul_of_nonneg_left hh hC₂.le
    nlinarith
  exact havoid.false (s.selected_bounded keep c (hsize c) he hlo hhi hb)
end TorsionFreeZeroDivisors.SampleGraph.PathSystem

end

end OAI
