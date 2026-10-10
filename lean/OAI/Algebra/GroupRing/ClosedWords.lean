import Mathlib
import OAI.Algebra.GroupRing.BalancedPieces

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
def root : Option (Piece s cap) := s.root.bind fun t=>
  if (s.paths t).length≤cap then some ⟨t,⟨0,BalancedPieces.number_pos hc⟩⟩ else none
lemma piece_eq (p q : Piece s cap) (h : p.1=q.1) (hp : (s.paths p.1).length≤cap) : p=q := by
  rcases p with ⟨t,i⟩
  rcases q with ⟨u,j⟩
  dsimp only at h hp
  subst u
  have hij : i=j := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    simp only [BalancedPieces.number,ite_eq_left hp] at hi hj
    omega
  cases hij
  rfl
lemma root_eq_some (p : Piece s cap) : root s cap hc=some p ↔ s.root=some p.1 ∧ (s.paths p.1).length≤cap := by
  cases hr : s.root with
  | none => simp [root,hr]
  | some t =>
    by_cases ht : (s.paths t).length≤cap
    · simp only [root,hr,Option.bind_some,ite_eq_left ht,Option.some.injEq]
      constructor
      · intro h
        rw [←h]
        exact ⟨rfl,ht⟩
      · intro h
        exact piece_eq s cap _ p h.1 ht
    · simp only [root,hr,Option.bind_some,ite_eq_right ht,Option.some.injEq]
      constructor
      · intro h; cases h
      · intro h; exact False.elim (ht (h.1 ▸ h.2))
lemma cyclic_iff {T : Type} (root : Option T) (t : T) :
    StageRoot.cyclic root t=true ↔ root≠some t := by
  simp only [StageRoot.cyclic,decide_eq_true_eq]
lemma cyclic (p : Piece s cap) (hp : StageRoot.cyclic (root s cap hc) p=true) :
    ∀ᵉ (a∈(word s cap hc hL hd p).getLast?) (b∈(word s cap hc hL hd p).head?),
      PortWalk.step (graph rep r).origin (graph rep r).reverse a b := by
  have hp' := (cyclic_iff (root s cap hc) p).mp hp
  by_cases hs : (s.paths p.1).length≤cap
  · rw [word_short s cap hc hL hd p hs]
    apply s.cyclic_chain
    apply (cyclic_iff _ _).mpr
    intro he
    exact hp' ((root_eq_some s cap hc p).mpr ⟨he,hs⟩)
  · exact cyclic_of_long s cap hc hL hd p (by omega)
lemma root_start (p : Piece s cap) (hp : root s cap hc=some p) :
    (word s cap hc hL hd p).head (nonempty s cap hc hL hd p)=(s.paths p.1).head (s.nonempty p.1) := by
  have hs := ((root_eq_some s cap hc p).mp hp).2
  simp only [word_short s cap hc hL hd p hs]
lemma rootA (z : VA rep) (hz : (root s cap hc).map (fun p=>(graph rep r).origin
      ((word s cap hc hL hd p).head (nonempty s cap hc hL hd p)))=some (.inl z)) : z=x := by
  obtain ⟨p,hp,he⟩ := Option.map_eq_some_iff.mp hz
  apply s.rootA z
  have hh := (root_eq_some s cap hc p).mp hp
  rw [hh.1,Option.map_some]
  rw [root_start s cap hc hL hd p hp] at he
  exact congrArg some he
lemma rootB (z : VB rep) (hz : (root s cap hc).map (fun p=>(graph rep r).origin
      ((word s cap hc hL hd p).head (nonempty s cap hc hL hd p)))=some (.inr z)) : z=y := by
  obtain ⟨p,hp,he⟩ := Option.map_eq_some_iff.mp hz
  apply s.rootB z
  have hh := (root_eq_some s cap hc p).mp hp
  rw [hh.1,Option.map_some]
  rw [root_start s cap hc hL hd p hp] at he
  exact congrArg some he
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords
namespace TorsionFreeZeroDivisors.SingleException
open scoped Classical BigOperators
variable {T : Type} [Fintype T] (root : Option T) (f : T → ℕ) (L : ℕ)
lemma cardinal_charge (h : ∀t,root≠some t → L≤f t) : Fintype.card T*L≤(∑t,f t)+L := by
  classical
  have hsum : (∑_t : T,L)≤∑t,(f t+if root=some t then L else 0) := by
    apply Finset.sum_le_sum
    intro t _
    by_cases ht : root=some t
    · simp only [ite_eq_left ht]; omega
    · simpa only [ite_eq_right ht,Nat.add_zero] using h t ht
  rw [Finset.sum_add_distrib] at hsum
  have he : (∑t : T,if root=some t then L else 0)≤L := by
    cases root with
    | none => simp
    | some t => simp
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hsum
  omega
lemma two_mass (a b : T) (hab : a≠b) : f a+f b≤∑t,f t := by
  classical
  have h := Finset.sum_le_sum_of_subset (s:={a,b}) (t:=Finset.univ) (f:=f) (by simp)
  simpa only [Finset.sum_pair hab] using h
lemma divide_cast {U L D A H : ℕ} (hU : 0<U) (hL : 0<L)
    (h : U*L*A≤3*(D*L)*H) : (A:ℝ)≤3*(D:ℝ)/U*(H:ℝ) := by
  have hh : (U:ℝ)*L*A≤3*((D:ℝ)*L)*H := by exact_mod_cast h
  have hu : (0:ℝ)<U := by exact_mod_cast hU
  have hl : (0:ℝ)<L := by exact_mod_cast hL
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hu).mpr
  nlinarith
end TorsionFreeZeroDivisors.SingleException
namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (U : ℕ) (hU : 3≤U)
    (hL : 1≤L (size rep)) (hcap : 6≤U*L (size rep))
    (hd : GraphSample.Diameters rep r) (hr : r∈samples rep)
    (hordinary : ∃t,s.root≠some t)
abbrev cap_pos : 0<U*L (size rep) := lt_of_lt_of_le (by norm_num : 0<6) hcap
abbrev H₀ : ℕ := ∑t,(s.paths t).length
include hr hordinary in
lemma H₀_ge : L (size rep)≤H₀ s := by
  obtain ⟨t,ht⟩ := hordinary
  exact (original_girth s hr t ht).trans (Finset.single_le_sum (f:=fun t=>(s.paths t).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ t))
include hU hr in
lemma old_lower (p : Piece s (U*L (size rep)))
    (hp : root s _ (cap_pos U hcap)≠some p) :
    L (size rep)≤BalancedWords.old s.paths (U*L (size rep)) p := by
  have hc := cap_pos U hcap
  by_cases hs : (s.paths p.1).length≤U*L (size rep)
  · have ht : s.root≠some p.1 := fun he=>hp ((root_eq_some s _ hc p).mpr ⟨he,hs⟩)
    simp only [BalancedWords.old,BalancedPieces.sizes,ite_eq_left hs]
    exact original_girth s hr p.1 ht
  · have hh := BalancedPieces.sizes_lower_long hcap (by omega : U*L (size rep)<(s.paths p.1).length) p.2
    change L (size rep)≤BalancedPieces.sizes (s.paths p.1).length (U*L (size rep)) p.2
    nlinarith
include hU hcap hr hordinary in
lemma piece_charge : Fintype.card (Piece s (U*L (size rep)))*L (size rep)≤2*H₀ s := by
  have hh := SingleException.cardinal_charge (root s _ (cap_pos U hcap)) (BalancedWords.old s.paths _) (L (size rep))
    (old_lower s U hU hcap hr)
  rw [BalancedWords.old_sum s.paths _ (cap_pos U hcap)] at hh
  have hH := H₀_ge s hr hordinary
  change L (size rep)≤∑t,(s.paths t).length at hH
  change _≤2*(∑t,(s.paths t).length)
  omega
include hU hr in
lemma lower_word (p : Piece s (U*L (size rep)))
    (hp : root s _ (cap_pos U hcap)≠some p) :
    L (size rep)≤(word s _ (cap_pos U hcap) hL hd p).length :=
  (old_lower s U hU hcap hr p hp).trans (old_le_word s _ (cap_pos U hcap) hL hd p)
include hr hordinary in
lemma root_mass (p : Piece s (U*L (size rep)))
    (hp : root s _ (cap_pos U hcap)=some p)
    (hshort : (word s _ (cap_pos U hcap) hL hd p).length<L (size rep)) :
    2*(word s _ (cap_pos U hcap) hL hd p).length≤H₀ s := by
  obtain ⟨t,ht⟩ := hordinary
  have hs := (root_eq_some s _ (cap_pos U hcap) p).mp hp
  have hne : p.1≠t := by intro h; exact ht (h ▸ hs.1)
  have hg := original_girth s hr t ht
  have hsum := SingleException.two_mass (fun t=> (s.paths t).length) p.1 t hne
  rw [word_short s _ (cap_pos U hcap) hL hd p hs.2] at hshort ⊢
  change _≤∑t,(s.paths t).length
  omega
include hU in
lemma added_real : (∑p : Piece s (U*L (size rep)),((tail s _ (cap_pos U hcap) hL hd p).length:ℝ))≤
    3*(D:ℝ)/U*(H₀ s:ℝ) := by
  have h := total_added s _ (cap_pos U hcap) hL hd hcap
  have hh := SingleException.divide_cast (U:=U) (L:=L (size rep)) (D:=D)
    (A:=∑p : Piece s (U*L (size rep)),(tail s _ (cap_pos U hcap) hL hd p).length)
    (H:=H₀ s) (by omega) (by omega) h
  rw [Nat.cast_sum] at hh
  exact hh
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

/-! Finite rotation systems. The Euler inequality here
is explicitly an input from a planar realization; no PL realization or planar
separator theorem is asserted by this file. The face cycles and bad-gap count,
however, are computed from the actual boundary and pairing permutations. -/
namespace TorsionFreeZeroDivisors.PermutationCycles
open scoped Classical BigOperators
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
abbrev Cycle := Quotient (Equiv.Perm.SameCycle.setoid f)
instance : Fintype (Cycle f) := Fintype.ofFinite _
def cycle (x : O) : Cycle f := Quotient.mk _ x
def members (c : Cycle f) : Finset O := Finset.univ.filter (fun x => cycle f x=c)
@[simp] lemma mem_members {c : Cycle f} {x : O} : x∈members f c ↔ cycle f x=c := by simp [members]
omit [Fintype O] in
lemma cycle_eq {x y : O} : cycle f x=cycle f y ↔ f.SameCycle x y := Quotient.eq
omit [Fintype O] in
@[simp] lemma cycle_apply (x : O) : cycle f (f x)=cycle f x := by
  apply (cycle_eq f).mpr
  simpa only [Equiv.Perm.sameCycle_apply_left] using Equiv.Perm.SameCycle.refl f x
omit [Fintype O] in
lemma cycle_surjective : Function.Surjective (cycle f) := Quotient.mk_surjective
lemma members_nonempty (c : Cycle f) : (members f c).Nonempty := by
  obtain ⟨x,rfl⟩ := cycle_surjective f c
  exact ⟨x,(mem_members f).mpr rfl⟩
lemma mem_of_mem {c : Cycle f} {x : O} (hx : x∈members f c) : f x∈members f c := by
  simpa only [mem_members,cycle_apply] using hx
lemma card_one_fixed {x : O} (h : (members f (cycle f x)).card=1) : f x=x := by
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h
  have hx : x∈members f (cycle f x) := (mem_members f).mpr rfl
  have hf := mem_of_mem f hx
  rw [ha,Finset.mem_singleton] at hx hf
  exact hf.trans hx.symm
lemma card_le_two_square {x : O} (h : (members f (cycle f x)).card≤2) : f (f x)=x := by
  by_contra hn
  have hfx : f x≠x := fun he => hn (by rw [he,he])
  have hff : f (f x)≠f x := fun he => hfx (f.injective he)
  have hx : x∈members f (cycle f x) := (mem_members f).mpr rfl
  have hs : {x,f x,f (f x)}⊆members f (cycle f x) := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl
    · exact hx
    · exact mem_of_mem f hx
    · exact mem_of_mem f (mem_of_mem f hx)
  have hc := (Finset.card_le_card hs).trans h
  have he : ({x,f x,f (f x)} : Finset O).card=3 := by
    simp [Ne.symm hfx,Ne.symm hn,Ne.symm hff]
  omega

def fixed : Finset O := Finset.univ.filter (fun x => f x=x)
lemma fixed_le_cycles : (fixed f).card≤Fintype.card (Cycle f) := by
  have hi : Function.Injective (fun x : {x // x∈fixed f} => cycle f x.val) := by
    intro x y he
    apply Subtype.ext
    exact ((cycle_eq f).mp he).eq_of_left ((Finset.mem_filter.mp x.property).2)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hi
lemma singleton_cycles_le_fixed :
    (Finset.univ.filter (fun c : Cycle f => (members f c).card=1)).card≤(fixed f).card := by
  let pick : {c : Cycle f // (members f c).card=1} → {x // x∈fixed f} := fun c =>
    ⟨Quotient.out c.val,by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      apply card_one_fixed f
      have he : cycle f (Quotient.out c.val)=c.val := Quotient.out_eq c.val
      simpa only [he] using c.property⟩
  have hi : Function.Injective pick := by
    intro c d he
    apply Subtype.ext
    have h := congrArg (fun x : {x // x∈fixed f} => cycle f x.val) he
    simpa only [pick,cycle,Quotient.out_eq] using h
  simpa only [Fintype.card_subtype,Finset.filter_mem_eq_inter,Finset.univ_inter] using Fintype.card_le_of_injective pick hi
lemma sum_card : (∑ c : Cycle f,(members f c).card)=Fintype.card O := by
  have h := Finset.card_eq_sum_card_fiberwise (f:=cycle f)
    (s:=Finset.univ) (t:=Finset.univ) (fun _ _ => Finset.mem_univ _)
  exact h.symm
lemma large_count :
    (∑ c∈Finset.univ.filter (fun c : Cycle f => 3≤(members f c).card),(members f c).card)=
     (Finset.univ.filter (fun x : O => 3≤(members f (cycle f x)).card)).card := by
  calc
    _ = (Finset.univ.filter (fun x : O => cycle f x∈Finset.univ.filter
      (fun c : Cycle f => 3≤(members f c).card))).card :=
      Finset.sum_card_fiberwise_eq_card_filter _ _ (cycle f)
    _ = _ := by congr 1; ext x; simp

end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.PlanarRotation
open scoped Classical BigOperators
open PermutationCycles
lemma excess_identity {C : Type} [Fintype C] (len : C→ℕ) (hp : ∀ c,0<len c) :
    (∑ c,(len c-2))+2*Fintype.card C=(∑ c,len c)+
      (Finset.univ.filter (fun c => len c=1)).card := by
  calc
    _ = ∑ c,(len c-2+2) := by simp [Finset.sum_add_distrib,Nat.mul_comm]
    _ = ∑ c,(len c+if len c=1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro c _
      have h := hp c
      split_ifs <;> omega
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_boole,Nat.cast_id]
lemma large_sum_le {C : Type} [Fintype C] (len : C→ℕ) :
    (∑ c∈Finset.univ.filter (fun c => 3≤len c),len c)≤3*∑ c,(len c-2) := by
  rw [Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  split_ifs <;> omega

variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
def opposite : Equiv.Perm O := α*σ
/-- An actual distinct-arc digon gap, read solely from the two permutations. -/
def Good (x : O) : Prop :=
  opposite σ α (opposite σ α x)=x ∧ opposite σ α x≠x ∧ σ x≠x
def bad : Finset O := Finset.univ.filter (fun x => ¬Good σ α x)
lemma bad_card_bound :
    (bad σ α).card≤(fixed (opposite σ α)).card+(fixed σ).card+
      (Finset.univ.filter (fun x => 3≤(members (opposite σ α) (cycle (opposite σ α) x)).card)).card := by
  let f := opposite σ α
  let large := Finset.univ.filter (fun x => 3≤(members f (cycle f x)).card)
  have hs : bad σ α⊆(fixed f∪fixed σ)∪large := by
    intro x hx
    have hx := (Finset.mem_filter.mp hx).2
    by_cases h1 : f x=x
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h1⟩))
    by_cases h2 : σ x=x
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h2⟩))
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    by_contra hn
    exact hx ⟨card_le_two_square f (by omega),h1,h2⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))

/-- The exact `8N` estimate. The planar input is only its explicit Euler
inequality; no comparison-count estimate is assumed. -/
theorem bad_gaps_le
    (heuler : Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle (opposite σ α)))
    (hmono : (fixed (opposite σ α)).card≤1) :
    (bad σ α).card≤8*Fintype.card (Cycle σ) := by
  let f := opposite σ α
  let P := ∑ c : Cycle f,((members f c).card-2)
  let M := (Finset.univ.filter (fun c : Cycle f => (members f c).card=1)).card
  have hM : M≤1 := (singleton_cycles_le_fixed f).trans hmono
  change (fixed f).card≤1 at hmono
  have hP : P+2*Fintype.card (Cycle f)=Fintype.card O+M := by
    have h := excess_identity (fun c : Cycle f => (members f c).card)
      (fun c => Finset.card_pos.mpr (members_nonempty f c))
    rw [sum_card] at h
    exact h
  have hl := large_sum_le (fun c : Cycle f => (members f c).card)
  rw [large_count] at hl
  have hb := bad_card_bound σ α
  have hs := fixed_le_cycles σ
  change (bad σ α).card≤(fixed f).card+(fixed σ).card+
    (Finset.univ.filter (fun x => 3≤(members f (cycle f x)).card)).card at hb
  change (Finset.univ.filter (fun x => 3≤(members f (cycle f x)).card)).card≤3*P at hl
  change Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle f) at heuler
  omega

omit [Fintype O] in
lemma good_opposite (hr : Function.Involutive α) {x : O} (hx : Good σ α x) :
    Good σ α (opposite σ α x) := by
  have he : σ (opposite σ α x)=α x := by
    have h := congrArg α hx.1
    change α (α (σ (α (σ x))))=α x at h
    rw [hr] at h
    exact h
  refine ⟨congrArg (opposite σ α) hx.1,?_,?_⟩
  · intro h
    exact hx.2.1 (h.symm.trans hx.1)
  · intro h
    rw [he] at h
    exact hx.2.2 (α.injective h).symm

/-- Cut every bad gap and every prescribed marking together with its opposite. -/
def cuts (marks : Finset O) : Finset O := bad σ α∪marks∪marks.image (opposite σ α)
lemma cardinal_cuts (marks : Finset O) : (cuts σ α marks).card≤(bad σ α).card+2*marks.card := by
  have h := (Finset.card_union_le (bad σ α∪marks) (marks.image (opposite σ α))).trans
    (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_image_le))
  unfold cuts
  omega
lemma cut_stable (hr : Function.Involutive α) (marks : Finset O) {x : O} (hx : Good σ α x) :
    x∈cuts σ α marks ↔ opposite σ α x∈cuts σ α marks := by
  have hy := good_opposite σ α hr hx
  have image_iff {z : O} (hz : Good σ α z) :
      z∈marks.image (opposite σ α) ↔ opposite σ α z∈marks := by
    constructor
    · intro hm
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hm
      have hwz : w=opposite σ α z := (opposite σ α).injective (he.trans hz.1.symm)
      simpa only [hwz] using hw
    · intro h
      exact Finset.mem_image.mpr ⟨opposite σ α z,h,hz.1⟩
  simp only [cuts,Finset.mem_union,bad,Finset.mem_filter,Finset.mem_univ,true_and,
    not_true_eq_false, hx,hy,false_or,image_iff hx,image_iff hy,hx.1]
  exact or_comm

/-- The source's `J ≤ 12N'`, retaining the exact boundary and splitting count. -/
theorem cuts_le_twelve (marks : Finset O) (pieces : ℕ)
    (heuler : Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle (opposite σ α)))
    (hmono : (fixed (opposite σ α)).card≤1)
    (hpieces : Fintype.card (Cycle σ)≤pieces)
    (hmarks : marks.card≤Fintype.card (Cycle σ)+pieces) :
    (cuts σ α marks).card≤12*pieces := by
  have hb := bad_gaps_le σ α heuler hmono
  have hc := cardinal_cuts σ α marks
  omega
end TorsionFreeZeroDivisors.PlanarRotation
namespace TorsionFreeZeroDivisors.PlanarRuns
open scoped Classical BigOperators
open PlanarRotation
variable {O : Type}

/-- A finite circular boundary cut at least once in each boundary component. -/
structure CutSystem (σ : Equiv.Perm O) where
  cut : Finset O
  hits : ∀ x, ∃ n : ℕ, (σ^n) x∈cut

namespace CutSystem
variable {σ : Equiv.Perm O} (S : CutSystem σ)
def distance (x : O) : ℕ := Nat.find (S.hits x)
def finish (x : O) : O := (σ^(S.distance x)) x
lemma finish_mem (x : O) : S.finish x∈S.cut := Nat.find_spec (S.hits x)
lemma before {x : O} {i : ℕ} (hi : i<S.distance x) : (σ^i) x∉S.cut :=
  Nat.find_min (S.hits x) hi
lemma distance_zero {x : O} (hx : x∈S.cut) : S.distance x=0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.find_min' (S.hits x) (by simpa using hx)
lemma finish_cut {x : O} (hx : x∈S.cut) : S.finish x=x := by
  simp only [finish,S.distance_zero hx,pow_zero,Equiv.Perm.one_apply]
lemma zero_iff (x : O) : S.distance x=0 ↔ x∈S.cut := by
  constructor
  · intro h
    simpa only [finish,h,pow_zero,Equiv.Perm.one_apply] using S.finish_mem x
  · exact S.distance_zero
lemma distance_next {x : O} (hx : x∉S.cut) : S.distance x=S.distance (σ x)+1 := by
  have hp : 0<S.distance x := Nat.pos_of_ne_zero (fun h => hx ((S.zero_iff x).mp h))
  apply Nat.le_antisymm
  · apply Nat.find_min'
    simpa only [finish,pow_succ,Equiv.Perm.mul_apply] using S.finish_mem (σ x)
  · have hm := Nat.find_min' (S.hits (σ x)) (show (σ^(S.distance x-1)) (σ x)∈S.cut from by
      rw [← Equiv.Perm.mul_apply,← pow_succ,Nat.sub_add_cancel hp]
      exact S.finish_mem x)
    change S.distance (σ x)≤S.distance x-1 at hm
    omega
lemma finish_next {x : O} (hx : x∉S.cut) : S.finish (σ x)=S.finish x := by
  simp only [finish,S.distance_next hx,pow_succ,Equiv.Perm.mul_apply]
lemma finish_surjective : Function.Surjective (fun x => (⟨S.finish x,S.finish_mem x⟩ : {x // x∈S.cut})) := by
  intro x
  exact ⟨x.val,Subtype.ext (S.finish_cut x.property)⟩

lemma distance_iterate (x : O) : ∀ i, i≤S.distance x →
    S.distance ((σ^i) x)=S.distance x-i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro hi
    have hp := S.before (x:=x) (i:=i) (by omega)
    have hn := S.distance_next hp
    have hh := ih (by omega)
    rw [pow_succ',Equiv.Perm.mul_apply]
    omega
lemma finish_iterate (x : O) : ∀ i, i≤S.distance x → S.finish ((σ^i) x)=S.finish x := by
  intro i hi
  unfold finish
  rw [S.distance_iterate x i hi,← Equiv.Perm.mul_apply,← pow_add,Nat.sub_add_cancel hi]

/-- Every uncut adjacency is a distinct-arc digon, and cuts are stable under
its opposite gap. These are precisely the hypotheses obtained by cutting bad
and marked gaps in `PlanarRotation`. -/
structure Paired (α : Equiv.Perm O) : Prop where
  involutive : Function.Involutive α
  fixed_free : ∀ x, α x≠x
  good : ∀ x, x∉S.cut → Good σ α x
  stable : ∀ x, Good σ α x → (x∈S.cut ↔ opposite σ α x∈S.cut)

namespace Paired
variable {S}
variable {α : Equiv.Perm O} (P : S.Paired α)
include P
lemma opposite_next {x : O} (hx : x∉S.cut) : σ (α (σ x))=α x := by
  have h := congrArg α (P.good x hx).1
  change α (α (σ (α (σ x))))=α x at h
  rw [P.involutive] at h
  exact h
lemma opposite_uncut {x : O} (hx : x∉S.cut) : α (σ x)∉S.cut := by
  exact fun h => hx ((P.stable x (P.good x hx)).mpr h)
lemma finish_opposite {x : O} (hx : x∉S.cut) : S.finish (α (σ x))=S.finish (α x) := by
  have h := S.finish_next (P.opposite_uncut hx)
  rw [P.opposite_next hx] at h
  exact h.symm
lemma finish_pair (x : O) : S.finish (α (S.finish x))=S.finish (α x) := by
  generalize hn : S.distance x=n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hx : x∈S.cut
    · rw [S.finish_cut hx]
    · have hd := S.distance_next hx
      have he := ih (S.distance (σ x)) (by omega) (σ x) rfl
      rw [S.finish_next hx] at he
      exact he.trans (P.finish_opposite hx)

def pair (_P : S.Paired α) (c : {x // x∈S.cut}) : {x // x∈S.cut} := ⟨S.finish (α c.val),S.finish_mem _⟩
lemma pair_involutive : Function.Involutive (P.pair) := by
  intro c
  apply Subtype.ext
  change S.finish (α (S.finish (α c.val)))=c.val
  rw [P.finish_pair,P.involutive,S.finish_cut c.property]

lemma reverse_steps (c : {x // x∈S.cut}) (hs : P.pair c=c) :
    ∀ i, i≤S.distance (α c.val) →
      α ((σ^i) (α c.val))=(σ^(S.distance (α c.val)-i)) (α c.val) := by
  intro i
  induction i with
  | zero =>
    intro _
    have h := congrArg Subtype.val hs
    change S.finish (α c.val)=c.val at h
    simp only [pow_zero,Equiv.Perm.one_apply,Nat.sub_zero]
    rw [P.involutive]
    exact h.symm
  | succ i ih =>
    intro hi
    have hj : i<S.distance (α c.val) := by omega
    have hcut := S.before hj
    have he := P.opposite_next hcut
    have hh := ih (by omega)
    apply σ.injective
    rw [pow_succ',Equiv.Perm.mul_apply,he,hh]
    have hd : S.distance (α c.val)-i=(S.distance (α c.val)-(i+1))+1 := by omega
    rw [hd,pow_succ',Equiv.Perm.mul_apply]
lemma pair_fixed_free (c : {x // x∈S.cut}) : P.pair c≠c := by
  intro hs
  let d := S.distance (α c.val)
  let k := d/2
  have hk : k≤d := Nat.div_le_self _ _
  have he := P.reverse_steps c hs k hk
  by_cases hp : d=2*k
  · have hdk : S.distance (α c.val)-k=k := by change d-k=k; omega
    rw [hdk] at he
    exact P.fixed_free _ he
  · have hd : d=2*k+1 := by dsimp [k]; omega
    have hdk : S.distance (α c.val)-k=k+1 := by change d-k=k+1; omega
    rw [hdk,pow_succ',Equiv.Perm.mul_apply] at he
    have hc : (σ^k) (α c.val)∉S.cut := S.before (by change k<d; omega)
    have hg := P.good _ hc
    apply hg.2.1
    change α (σ ((σ^k) (α c.val)))=(σ^k) (α c.val)
    rw [← he,P.involutive]

lemma predecessor_cut (c : {x // x∈S.cut}) : σ.symm (α c.val)∈S.cut := by
  by_contra hn
  have h := P.opposite_uncut hn
  rw [Equiv.apply_symm_apply,P.involutive] at h
  exact h c.property

/-- Each cut is the last occurrence of its run; the first occurrence is the
partner of the final occurrence of the opposite run. -/
def first (c : {x // x∈S.cut}) : O := α (P.pair c).val
lemma finish_first (c : {x // x∈S.cut}) : S.finish (P.first c)=c.val := by
  exact congrArg Subtype.val (P.pair_involutive c)
lemma before_first_cut (c : {x // x∈S.cut}) : σ.symm (P.first c)∈S.cut :=
  P.predecessor_cut (P.pair c)

lemma distance_le_first {c : {x // x∈S.cut}} {x : O} (hx : S.finish x=c.val) :
    S.distance x≤S.distance (P.first c) := by
  by_contra hn
  have hd : S.distance (P.first c)+1≤S.distance x := by omega
  have he : (σ^(S.distance x-S.distance (P.first c))) x=P.first c := by
    apply (σ^(S.distance (P.first c))).injective
    rw [← Equiv.Perm.mul_apply,← pow_add,Nat.add_sub_of_le (by omega)]
    exact hx.trans (P.finish_first c).symm
  have hg : (σ^(S.distance x-S.distance (P.first c)-1)) x=σ.symm (P.first c) := by
    apply σ.injective
    rw [Equiv.apply_symm_apply,← Equiv.Perm.mul_apply,← pow_succ']
    have heq : S.distance x-S.distance (P.first c)-1+1=S.distance x-S.distance (P.first c) := by omega
    rw [heq]
    exact he
  have hcut := P.before_first_cut c
  rw [← hg] at hcut
  exact S.before (by omega) hcut

lemma run_coordinates {c : {x // x∈S.cut}} {x : O} (hx : S.finish x=c.val) :
    (σ^(S.distance (P.first c)-S.distance x)) (P.first c)=x := by
  have hd := P.distance_le_first hx
  apply (σ^(S.distance x)).injective
  rw [← Equiv.Perm.mul_apply,← pow_add,Nat.add_sub_of_le hd]
  exact (P.finish_first c).trans hx.symm

def run (c : {x // x∈S.cut}) : List O :=
  (List.range (S.distance (P.first c)+1)).map (fun i => (σ^i) (P.first c))
lemma mem_run {c : {x // x∈S.cut}} {x : O} : x∈P.run c ↔ S.finish x=c.val := by
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    have hi' : i≤S.distance (P.first c) := by simpa only [List.mem_range,Nat.lt_succ_iff] using hi
    exact (S.finish_iterate _ _ hi').trans (P.finish_first c)
  · intro hx
    apply List.mem_map.mpr
    exact ⟨S.distance (P.first c)-S.distance x,
      List.mem_range.mpr (by omega),P.run_coordinates hx⟩
lemma run_nonempty (c : {x // x∈S.cut}) : P.run c≠[] := by
  simp [run]
lemma run_nodup (c : {x // x∈S.cut}) : (P.run c).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro i hi j hj he
  have hi' : i≤S.distance (P.first c) := by simpa only [List.mem_range,Nat.lt_succ_iff] using hi
  have hj' : j≤S.distance (P.first c) := by simpa only [List.mem_range,Nat.lt_succ_iff] using hj
  have h := congrArg S.distance he
  rw [S.distance_iterate _ _ hi',S.distance_iterate _ _ hj'] at h
  omega
lemma belongs_opposite {c : {x // x∈S.cut}} {x : O} (hx : x∈P.run c) :
    α x∈P.run (P.pair c) := by
  apply P.mem_run.mpr
  have he := P.mem_run.mp hx
  have h := P.finish_pair x
  rw [he] at h
  exact h.symm
lemma distinct_runs (c : {x // x∈S.cut}) : P.run c≠P.run (P.pair c) := by
  intro h
  have hc : c.val∈P.run c := P.mem_run.mpr (S.finish_cut c.property)
  rw [h] at hc
  have he := P.mem_run.mp hc
  rw [S.finish_cut c.property] at he
  exact P.pair_fixed_free c (Subtype.ext he.symm)

lemma first_pair (c : {x // x∈S.cut}) : P.first (P.pair c)=α c.val := by
  unfold first
  rw [P.pair_involutive]
lemma distance_reverse (c : {x // x∈S.cut}) : ∀ i,i≤S.distance (P.first c) →
    S.distance (α ((σ^i) (P.first c)))=i := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [pow_zero,Equiv.Perm.one_apply,first]
    rw [P.involutive]
    exact S.distance_zero (P.pair c).property
  | succ i ih =>
    intro hi
    have hc := S.before (x:=P.first c) (i:=i) (by omega)
    have hd := S.distance_next (P.opposite_uncut hc)
    rw [P.opposite_next hc,ih (by omega)] at hd
    simpa only [pow_succ',Equiv.Perm.mul_apply] using hd
lemma distance_first_pair (c : {x // x∈S.cut}) :
    S.distance (P.first (P.pair c))=S.distance (P.first c) := by
  have h := P.distance_reverse c (S.distance (P.first c)) le_rfl
  change S.distance (α (S.finish (P.first c)))=S.distance (P.first c) at h
  rw [P.finish_first] at h
  rw [P.first_pair]
  exact h
lemma reverse_coordinate (c : {x // x∈S.cut}) (i : ℕ) (hi : i≤S.distance (P.first c)) :
    α ((σ^i) (P.first c))=(σ^(S.distance (P.first c)-i)) (P.first (P.pair c)) := by
  have hmem : (σ^i) (P.first c)∈P.run c :=
    P.mem_run.mpr ((S.finish_iterate _ _ hi).trans (P.finish_first c))
  have he := P.run_coordinates (P.mem_run.mp (P.belongs_opposite hmem))
  rw [P.distance_first_pair,P.distance_reverse c i hi] at he
  exact he.symm
lemma run_reverse (c : {x // x∈S.cut}) : (P.run c).map α=(P.run (P.pair c)).reverse := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_reverse,run,List.length_range,P.distance_first_pair]
  · intro i hi hj
    have hi' : i≤S.distance (P.first c) := by simpa only [List.length_map,run,List.length_range,Nat.lt_succ_iff] using hi
    simp only [run,List.getElem_map,List.getElem_range,List.getElem_reverse,
      List.length_map,List.length_range,P.distance_first_pair]
    have he : S.distance (P.first c)+1-1-i=S.distance (P.first c)-i := by omega
    simpa only [he] using P.reverse_coordinate c i hi'

end Paired
namespace PairOrbit
variable {A : Type} (r : A→A) (hr : Function.Involutive r)
def relation : Setoid A where
  r x y := x=y ∨ r x=y
  iseqv := ⟨fun _ => Or.inl rfl,fun {x y} h => by
    rcases h with h|h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [←h,hr]),fun {x y z} h k => by
    rcases h with rfl|h
    · exact k
    · rcases k with rfl|k
      · exact Or.inr h
      · exact Or.inl (by rw [←k,←h,hr])⟩
abbrev Orbit := Quotient (relation r hr)
variable [Fintype A]
instance : Fintype (Orbit r hr) := Fintype.ofFinite _
def project (x : A) : Orbit r hr := Quotient.mk _ x
lemma fiber_two (hf : ∀ x,r x≠x) (c : Orbit r hr) :
    (Finset.univ.filter (fun x => project r hr x=c)).card=2 := by
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
  have he : Finset.univ.filter (fun y => project r hr y=project r hr x)={x,r x} := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    change Quotient.mk (relation r hr) y=Quotient.mk (relation r hr) x ↔ y=x ∨ y=r x
    rw [Quotient.eq]
    change (y=x ∨ r y=x) ↔ y=x ∨ y=r x
    constructor
    · rintro (h|h)
      · exact Or.inl h
      · exact Or.inr (by rw [←h,hr])
    · rintro (h|h)
      · exact Or.inl h
      · exact Or.inr (by rw [h,hr])
  change (Finset.univ.filter (fun y => project r hr y=project r hr x)).card=2
  rw [he]
  simp [Ne.symm (hf x)]
lemma card_twice (hf : ∀ x,r x≠x) : 2*Fintype.card (Orbit r hr)=Fintype.card A := by
  have h := Finset.card_eq_sum_card_fiberwise (s:=Finset.univ) (t:=Finset.univ)
    (f:=project r hr) (fun _ _ => Finset.mem_univ _)
  simpa only [fiber_two r hr hf,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_comm] using h.symm
end PairOrbit

namespace Paired
variable {S} {α : Equiv.Perm O} (P : S.Paired α)
abbrev IntervalPair := PairOrbit.Orbit P.pair P.pair_involutive
instance : Fintype P.IntervalPair := PairOrbit.instFintypeOrbit _ _
lemma twice_interval_pairs : 2*Fintype.card P.IntervalPair=S.cut.card := by
  simpa only [Fintype.card_coe] using PairOrbit.card_twice P.pair P.pair_involutive P.pair_fixed_free
lemma interval_pairs_le (pieces : ℕ) (hcut : S.cut.card≤12*pieces) :
    Fintype.card P.IntervalPair≤6*pieces := by
  have h := P.twice_interval_pairs
  omega
end Paired

/-- The literal source cut construction has at least one cut per boundary,
using one chosen indexing mark there. -/
def ofMarks [Fintype O] (α : Equiv.Perm O) (marks : Finset O)
    (hmark : ∀ x,∃ y∈marks,σ.SameCycle x y) : CutSystem σ where
  cut := PlanarRotation.cuts σ α marks
  hits x := by
    obtain ⟨y,hy,hxy⟩ := hmark x
    obtain ⟨n,hn⟩ := hxy.exists_nat_pow_eq
    refine ⟨n,?_⟩
    rw [hn]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hy)))
lemma ofMarks_paired [Fintype O] (α : Equiv.Perm O) (marks : Finset O)
    (hmark : ∀ x,∃ y∈marks,σ.SameCycle x y)
    (hr : Function.Involutive α) (hf : ∀ x,α x≠x) :
    (ofMarks α marks hmark).Paired α where
  involutive := hr
  fixed_free := hf
  good x hx := by
    by_contra hn
    exact hx (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)))))
  stable x hx := PlanarRotation.cut_stable σ α hr marks hx

/-- Exact `6N'` interval-pair count for the finite rotation data of the
manuscript. Euler planarity and the at-most-one exceptional monogon remain
explicit geometric inputs; the resulting intervals and their reversal are
constructed, not presumed. -/
theorem source_interval_bound [Fintype O] (α : Equiv.Perm O) (marks : Finset O)
    (hmark : ∀ x,∃ y∈marks,σ.SameCycle x y)
    (hr : Function.Involutive α) (hf : ∀ x,α x≠x) (pieces : ℕ)
    (heuler : Fintype.card O+4≤2*Fintype.card (PermutationCycles.Cycle σ)+
      2*Fintype.card (PermutationCycles.Cycle (opposite σ α)))
    (hmono : (PermutationCycles.fixed (opposite σ α)).card≤1)
    (hpieces : Fintype.card (PermutationCycles.Cycle σ)≤pieces)
    (hmarks : marks.card≤Fintype.card (PermutationCycles.Cycle σ)+pieces) :
    Fintype.card (ofMarks_paired α marks hmark hr hf).IntervalPair≤6*pieces := by
  apply Paired.interval_pairs_le
  exact PlanarRotation.cuts_le_twelve σ α marks pieces heuler hmono hpieces hmarks

end CutSystem
end TorsionFreeZeroDivisors.PlanarRuns

namespace TorsionFreeZeroDivisors.PlanarIntervals
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks PlanarRuns PlanarRuns.CutSystem
variable {T : Type} {len : T→ℕ} {σ α : Equiv.Perm (Position len)}
    (S : CutSystem σ) (P : S.Paired α)
    (hstep : ∀ x,x∉S.cut → (σ x).1=x.1 ∧ (σ x).2.val=x.2.val+1)

lemma position_ext {x y : Position len} (hs : x.1=y.1) (hc : x.2.val=y.2.val) : x=y := by
  rcases x with ⟨x,q⟩; rcases y with ⟨y,r⟩
  dsimp at hs hc
  subst y
  congr 1
  exact Subtype.ext hc

include hstep
lemma coordinate_iterate (x : Position len) (i : ℕ) (hi : i≤S.distance x) :
    ((σ^i) x).1=x.1 ∧ ((σ^i) x).2.val=x.2.val+i := by
  induction i with
  | zero =>
    change x.1=x.1 ∧ x.2.val=x.2.val+(0:ℤ)
    simp
  | succ i ih =>
    have hh := hstep ((σ^i) x) (S.before (by omega))
    have ih := ih (by omega)
    rw [pow_succ',Equiv.Perm.mul_apply]
    constructor
    · exact hh.1.trans ih.1
    · rw [hh.2,ih.2,Nat.cast_add,Nat.cast_one]; ring

def lower (c : {x // x∈S.cut}) : ℤ := (P.first c).2.val
def upper (c : {x // x∈S.cut}) : ℤ := c.val.2.val+1
lemma finish_coordinates (c : {x // x∈S.cut}) :
    c.val.1=(P.first c).1 ∧ upper S c=lower S P c+S.distance (P.first c)+1 := by
  have hh := coordinate_iterate S hstep (P.first c) (S.distance (P.first c)) le_rfl
  change (S.finish (P.first c)).1=_ ∧ (S.finish (P.first c)).2.val=_ at hh
  rw [P.finish_first] at hh
  exact ⟨hh.1,by dsimp only [upper,lower]; omega⟩
lemma bounds (c : {x // x∈S.cut}) :
    0≤lower S P c ∧ lower S P c<upper S c ∧ upper S c≤len (P.first c).1 := by
  have hf := (P.first c).2.property
  have hc := c.val.2.property
  rw [mem_positions] at hf hc
  have he := finish_coordinates S P hstep c
  have h0 : (0:ℝ)≤((P.first c).2.val:ℝ) := by
    have : (0:ℤ)≤(P.first c).2.val := by exact_mod_cast (show (-1:ℝ)<((P.first c).2.val:ℝ) by linarith [hf.1])
    exact_mod_cast this
  have h1 : c.val.2.val+1≤(len c.val.1:ℤ) := by
    have : (c.val.2.val:ℝ)<len c.val.1 := by linarith [hc.2]
    exact_mod_cast this
  have h1 := h1.trans_eq (congrArg (fun t => (len t : ℤ)) he.1)
  refine ⟨by exact_mod_cast h0,?_,h1⟩
  rw [he.2]
  omega

lemma finish_iff (x : Position len) (c : {x // x∈S.cut}) :
    S.finish x=c.val ↔ x.1=(P.first c).1 ∧ lower S P c≤x.2.val ∧ x.2.val<upper S c := by
  constructor
  · intro hx
    have hc := P.run_coordinates hx
    have hi : S.distance (P.first c)-S.distance x≤S.distance (P.first c) := Nat.sub_le _ _
    have hh := coordinate_iterate S hstep (P.first c) _ hi
    rw [hc] at hh
    have hd := P.distance_le_first hx
    have he := (finish_coordinates S P hstep c).2
    refine ⟨hh.1,?_,?_⟩ <;> dsimp only [lower] at * <;> omega
  · rintro ⟨hs,hl,hu⟩
    have he := (finish_coordinates S P hstep c).2
    let i := (x.2.val-lower S P c).toNat
    have hi : i≤S.distance (P.first c) := by dsimp only [i]; omega
    have hh := coordinate_iterate S hstep (P.first c) i hi
    have hp : (σ^i) (P.first c)=x := by
      apply position_ext
      · exact hh.1.trans hs.symm
      · rw [hh.2]
        dsimp only [i,lower] at *
        omega
    rw [←hp]
    exact (S.finish_iterate _ _ hi).trans (P.finish_first c)

lemma finish_real_iff (x : Position len) (c : {x // x∈S.cut}) :
    S.finish x=c.val ↔ x.1=(P.first c).1 ∧
      x.2.val∈positions (lower S P c) (upper S c) := by
  rw [finish_iff S P hstep,mem_positions]
  constructor
  · rintro ⟨hs,hl,hu⟩
    have hl' : (lower S P c:ℝ)≤x.2.val := by exact_mod_cast hl
    have hu' : (x.2.val:ℝ)+1≤upper S c := by exact_mod_cast hu
    exact ⟨hs,by linarith,by linarith⟩
  · rintro ⟨hs,hl,hu⟩
    have hl' : lower S P c≤x.2.val := by
      have : (lower S P c:ℝ)-1<x.2.val := by linarith
      have hh : lower S P c-1<x.2.val := by exact_mod_cast this
      omega
    have hu' : x.2.val<upper S c := by exact_mod_cast (show (x.2.val:ℝ)<upper S c by linarith)
    exact ⟨hs,hl',hu'⟩

lemma partner_coordinate {x : Position len} {c : {x // x∈S.cut}} (hx : S.finish x=c.val) :
    (α x).2.val=lower S P (P.pair c)+upper S c-1-x.2.val := by
  let i := S.distance (P.first c)-S.distance x
  have hi : i≤S.distance (P.first c) := Nat.sub_le _ _
  have hp := P.run_coordinates hx
  change (σ^i) (P.first c)=x at hp
  have hα := P.reverse_coordinate c i hi
  rw [hp] at hα
  have ht := coordinate_iterate S hstep (P.first (P.pair c)) (S.distance (P.first c)-i) (by
    rw [P.distance_first_pair]; omega)
  rw [←hα] at ht
  have hh := coordinate_iterate S hstep (P.first c) i hi
  rw [hp] at hh
  have he := (finish_coordinates S P hstep c).2
  dsimp only [lower] at *
  omega

/-- Every actual maximal run yields a literal integer comparison side. No
real-grid or arbitrary interval compatibility is postulated. -/
def comparisons : Comparisons (E:={x // x∈S.cut}) len where
  pairing := ⟨α,P.involutive⟩
  side x := some ⟨S.finish x,S.finish_mem x⟩
  flip := P.pair
  flip_inv := P.pair_involutive
  flip_ne := P.pair_fixed_free
  side_partner := by
    intro x c hc
    have he : S.finish x=c.val := congrArg Subtype.val (Option.some.inj hc)
    apply congrArg some
    apply Subtype.ext
    change S.finish (α x)=S.finish (α c.val)
    rw [←he,←P.finish_pair]
  none_iff x := by simp only [Option.some_ne_none,false_iff]; exact P.fixed_free x
  source c := (P.first c).1
  lo c := lower S P c
  hi c := upper S c
  reverse _ := true
  offset c := lower S P (P.pair c)+upper S c
  side_iff x c := by
    rw [Option.some.injEq,Subtype.ext_iff]
    exact finish_real_iff S P hstep x c
  partner_source := by
    intro x c hc
    have he : S.finish x=c.val := congrArg Subtype.val (Option.some.inj hc)
    have ht : S.finish (α x)=(P.pair c).val := by
      change S.finish (α x)=S.finish (α c.val)
      rw [←he,←P.finish_pair]
    exact ((finish_iff S P hstep _ _).mp ht).1
  partner_coordinate := by
    intro x c hc
    exact partner_coordinate S P hstep (congrArg Subtype.val (Option.some.inj hc))
  target_range := by
    intro c
    simp only [ite_true,Int.cast_add]
    have hb := bounds S P hstep (P.pair c)
    have h1 := (finish_coordinates S P hstep c).2
    have h2 := (finish_coordinates S P hstep (P.pair c)).2
    rw [P.distance_first_pair] at h2
    constructor
    · have hh : (0:ℝ)≤lower S P (P.pair c) := by exact_mod_cast hb.1
      linarith
    · have hh : lower S P (P.pair c)+upper S c-lower S P c≤(len (P.first (P.pair c)).1:ℤ) := by omega
      exact_mod_cast hh
end TorsionFreeZeroDivisors.PlanarIntervals
namespace TorsionFreeZeroDivisors.ExtendComparisons
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T E : Type} {len more : T → ℕ} (C : Comparisons (E:=E) len)
    (hle : ∀ t,len t ≤ more t)

lemma positions_mono {m n : ℕ} (h : m≤n) : positions 0 m⊆positions 0 n := by
  intro q hq
  rw [mem_positions] at hq ⊢
  exact ⟨hq.1,hq.2.trans_le (by exact_mod_cast h)⟩
def embed (x : Position len) : Position more :=
  ⟨x.1,⟨x.2.val,positions_mono (hle x.1) x.2.property⟩⟩
abbrev Old (x : Position more) : Prop := x.2.val∈positions 0 (len x.1)
def project (x : Position more) (h : Old (len:=len) x) : Position len := ⟨x.1,⟨x.2.val,h⟩⟩
lemma old_embed (x : Position len) : Old (len:=len) (embed hle x) := x.2.property
lemma project_embed (x : Position len) : project (embed hle x) (old_embed hle x)=x := by cases x; rfl
lemma embed_project (x : Position more) (h : Old (len:=len) x) : embed hle (project x h)=x := by cases x; rfl
lemma embed_injective : Function.Injective (embed hle) := by
  intro x y h
  apply PlanarIntervals.position_ext
  · exact congrArg (fun x : Position more => x.1) h
  · exact congrArg (fun x : Position more => x.2.val) h

def partner (x : Position more) : Position more :=
  if h : Old (len:=len) x then embed hle (C.pairing.partner (project x h)) else x
lemma partner_embed (x : Position len) : partner C hle (embed hle x)=embed hle (C.pairing.partner x) := by
  simp only [partner,dite_eq_left (old_embed hle x),project_embed]
lemma partner_new (x : Position more) (h : ¬Old (len:=len) x) : partner C hle x=x := by
  simp only [partner,dite_eq_right h]
lemma partner_inv : Function.Involutive (partner C hle) := by
  intro x
  by_cases h : Old (len:=len) x
  · rw [←embed_project hle x h,partner_embed,partner_embed,C.pairing.involutive]
  · rw [partner_new C hle x h,partner_new C hle x h]
def side (x : Position more) : Option E :=
  if h : Old (len:=len) x then C.side (project x h) else none
lemma side_embed (x : Position len) : side C (embed hle x)=C.side x := by
  simp only [side,dite_eq_left (old_embed hle x),project_embed]
lemma side_some_old {x : Position more} {e : E} (h : side C x=some e) : Old (len:=len) x := by
  by_contra hn
  simp only [side,dite_eq_right hn] at h
  cases h
lemma side_none (x : Position more) : side C x=none ↔ partner C hle x=x := by
  by_cases h : Old (len:=len) x
  · rw [←embed_project hle x h,side_embed,partner_embed]
    exact (C.none_iff _).trans (embed_injective hle).eq_iff.symm
  · simp only [side,dite_eq_right h,partner_new C hle x h]

variable (hupper : ∀ e,C.hi e≤len (C.source e))
include hupper in
lemma side_iff (x : Position more) (e : E) :
    side C x=some e ↔ x.1=C.source e ∧ x.2.val∈positions (C.lo e) (C.hi e) := by
  constructor
  · intro hx
    have ho := side_some_old C hx
    rw [side,dite_eq_left ho] at hx
    exact (C.side_iff _ _).mp hx
  · intro hx
    have ho : Old (len:=len) x := by
      apply mem_positions.mpr
      have h1 := (mem_positions.mp x.2.property).1
      have h2 := (mem_positions.mp hx.2).2
      have h3 : C.hi e≤len x.1 := by simpa only [hx.1] using hupper e
      exact ⟨h1,h2.trans_le h3⟩
    rw [side,dite_eq_left ho]
    exact (C.side_iff _ _).mpr hx

lemma partner_side {x : Position more} {e : E} (hx : side C x=some e) :
    side C (partner C hle x)=some (C.flip e) := by
  have ho := side_some_old C hx
  rw [←embed_project hle x ho,partner_embed,side_embed]
  apply C.side_partner
  rwa [←side_embed C hle,embed_project]
lemma partner_source {x : Position more} {e : E} (hx : side C x=some e) :
    (partner C hle x).1=C.source (C.flip e) := by
  have ho := side_some_old C hx
  rw [←embed_project hle x ho,partner_embed]
  exact C.partner_source _ _ (by rwa [←side_embed C hle,embed_project])
lemma partner_coordinate {x : Position more} {e : E} (hx : side C x=some e) :
    (partner C hle x).2.val=affine (C.reverse e) (C.offset e) x.2.val := by
  have ho := side_some_old C hx
  have hx' : C.side (project x ho)=some e := by
    simpa only [side,dite_eq_left ho] using hx
  have he : partner C hle x=embed hle (C.pairing.partner (project x ho)) := dite_eq_left ho
  rw [he]
  exact C.partner_coordinate (project x ho) e hx' 
include hle in
lemma target_range (e : E) : if C.reverse e then
    0≤(C.offset e:ℝ)-C.hi e ∧ (C.offset e:ℝ)-C.lo e ≤ more (C.source (C.flip e))
    else 0≤C.lo e+(C.offset e:ℝ) ∧ C.hi e+(C.offset e:ℝ) ≤ more (C.source (C.flip e)) := by
  have hh := C.target_range e
  have hn : (len (C.source (C.flip e)):ℝ) ≤ more (C.source (C.flip e)) := by exact_mod_cast hle _
  split_ifs at hh ⊢ <;> exact ⟨hh.1,hh.2.trans hn⟩

def comparisons : Comparisons (E:=E) more where
  pairing := ⟨partner C hle,partner_inv C hle⟩
  side := side C
  flip := C.flip
  flip_inv := C.flip_inv
  flip_ne := C.flip_ne
  side_partner _ _ := partner_side C hle
  none_iff := side_none C hle
  source := C.source
  lo := C.lo
  hi := C.hi
  reverse := C.reverse
  offset := C.offset
  side_iff := side_iff C hupper
  partner_source _ _ := partner_source C hle
  partner_coordinate _ _ := partner_coordinate C hle
  target_range := target_range C hle

variable [Fintype T]
include hle in
lemma old_card : (Finset.univ.filter (fun x : Position more => Old (len:=len) x)).card=
    Fintype.card (Position len) := by
  symm
  rw [←Finset.card_univ]
  apply Finset.card_bij (fun x _ => embed hle x)
  · intro x _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,old_embed hle x⟩
  · intro x _ y _ h
    exact embed_injective hle h
  · intro x hx
    have ho := (Finset.mem_filter.mp hx).2
    exact ⟨project x ho,Finset.mem_univ _,embed_project hle x ho⟩
lemma fixed_old_card : (Finset.univ.filter (fun x : Position more => Old (len:=len) x ∧ partner C hle x=x)).card=
    (Finset.univ.filter (fun x : Position len => C.pairing.partner x=x)).card := by
  symm
  apply Finset.card_bij (fun x _ => embed hle x)
  · intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,old_embed hle x,?_⟩
    rw [partner_embed,(Finset.mem_filter.mp hx).2]
  · intro x _ y _ h
    exact embed_injective hle h
  · intro x hx
    obtain ⟨ho,hf⟩ := (Finset.mem_filter.mp hx).2
    refine ⟨project x ho,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,embed_project hle x ho⟩
    apply embed_injective hle
    rw [←partner_embed,embed_project,hf]
lemma fixed_card : (Finset.univ.filter (fun x : Position more => partner C hle x=x)).card=
    (Finset.univ.filter (fun x : Position len => C.pairing.partner x=x)).card+
    (Finset.univ.filter (fun x : Position more => ¬Old (len:=len) x)).card := by
  have he : (Finset.univ.filter (fun x : Position more => partner C hle x=x))=
      (Finset.univ.filter (fun x : Position more => Old (len:=len) x ∧ partner C hle x=x))∪
      (Finset.univ.filter (fun x : Position more => ¬Old (len:=len) x)) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    by_cases h : Old (len:=len) x
    · simp only [h,true_and,not_true_eq_false,or_false]
    · simp only [h,false_and,not_false_eq_true,or_true,iff_true]
      exact partner_new C hle x h
  have hd : Disjoint (Finset.univ.filter (fun x : Position more => Old (len:=len) x ∧ partner C hle x=x))
      (Finset.univ.filter (fun x : Position more => ¬Old (len:=len) x)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx).2.1
  rw [he,Finset.card_union_of_disjoint hd,fixed_old_card]
end TorsionFreeZeroDivisors.ExtendComparisons
namespace TorsionFreeZeroDivisors.WordPositions

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
lemma bounds {n : ℕ} (q : {z // z∈positions 0 (n:ℝ)}) : 0≤q.val ∧ q.val<(n:ℤ) := by
  simpa only [AffineIntervals.nat_positions,Finset.mem_Ico] using q.property
variable {T : Type} (len : T → ℕ)
def fin : Position len ≃ ((t : T) × Fin (len t)) where
  toFun x := ⟨x.1,⟨x.2.val.toNat,by
    have hx := bounds x.2
    omega⟩⟩
  invFun x := ⟨x.1,⟨x.2.val,by
    simpa only [AffineIntervals.nat_positions,Finset.mem_Ico] using
      (show (0:ℤ)≤x.2.val ∧ (x.2.val:ℤ)<len x.1 from ⟨by omega,by exact_mod_cast x.2.isLt⟩)⟩⟩
  left_inv x := by
    apply PlanarIntervals.position_ext
    · rfl
    · have hx := bounds x.2
      dsimp only
      omega
  right_inv x := by
    rcases x with ⟨t,i⟩
    simp only [Int.toNat_natCast]
lemma fin_val (x : Position len) : (fin len x).2.val=x.2.val.toNat := rfl
lemma fin_symm_val (x : (t : T) × Fin (len t)) : ((fin len).symm x).2.val=x.2.val := rfl
variable {A : Type} (w : T → List A)
lemma dart_fin (x : (t : T) × Fin (w t).length) :
    RawDecomposition.dart w ((fin (fun t=>(w t).length)).symm x)=(w x.1).get x.2 := by
  change (w x.1).get ⟨(x.2.val:ℤ).toNat,_⟩=(w x.1).get x.2
  congr 1
lemma dart_prefix (v : T → List A) (x : Position (fun t=>(w t).length)) :
    RawDecomposition.dart (fun t=>w t++v t)
      (ExtendComparisons.embed (fun t=>by simp only [List.length_append]; omega) x)=
    RawDecomposition.dart w x := by
  dsimp only [RawDecomposition.dart,ExtendComparisons.embed]
  simpa only [List.get_eq_getElem] using List.getElem_append_left
    (show x.2.val.toNat<(w x.1).length from (fin _ x).2.isLt)

variable (cap : ℕ) (hc : 0<cap)
def joinFin : ((p : BalancedWords.Piece w cap) × Fin (BalancedWords.old w cap p)) ≃
      ((t : T) × Fin (w t).length) :=
  (Equiv.sigmaAssoc fun t i=>Fin (BalancedPieces.sizes (w t).length cap i)).trans
    (Equiv.sigmaCongrRight fun t=>ConsecutivePieces.index (w t)
      (BalancedPieces.sizes (w t).length cap) (BalancedPieces.sizes_sum hc))
def join : Position (BalancedWords.old w cap) ≃ Position (fun t=>(w t).length) :=
  (fin _).trans ((joinFin w cap hc).trans (fin _).symm)
lemma join_first (x : Position (BalancedWords.old w cap)) : (join w cap hc x).1=x.1.1 := rfl
lemma join_value (x : Position (BalancedWords.old w cap)) : (join w cap hc x).2.val=
    (ConsecutivePieces.offset (BalancedPieces.sizes (w x.1.1).length cap) x.1.2:ℤ)+x.2.val := by
  let q : Fin (BalancedPieces.sizes (w x.1.1).length cap x.1.2) :=
    ⟨x.2.val.toNat,by
      have hb := (fin _ x).2.isLt
      exact hb⟩
  change ((ConsecutivePieces.index (w x.1.1) (BalancedPieces.sizes (w x.1.1).length cap)
    (BalancedPieces.sizes_sum hc) ⟨x.1.2,q⟩).val:ℤ)=_
  rw [ConsecutivePieces.index_val,Nat.cast_add]
  congr 1
  exact Int.toNat_of_nonneg (bounds x.2).1

def segments : Position (fun p=>(BalancedWords.segment w cap hc p).length) ≃
    Position (fun t=>(w t).length) :=
  (ComparisonGeometry.position (Equiv.refl _) (BalancedWords.segment_length w cap hc)).trans (join w cap hc)
lemma segments_dart (x : Position (fun p=>(BalancedWords.segment w cap hc p).length)) :
    RawDecomposition.dart (BalancedWords.segment w cap hc) x=
      RawDecomposition.dart w (segments w cap hc x) := by
  unfold RawDecomposition.dart
  simp only [BalancedWords.segment,ConsecutivePieces.segment,List.get_eq_getElem,List.getElem_ofFn,
    Fin.getElem_fin]
  congr 1
end
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T : Type} [Fintype T] (len : T → ℕ)
lemma cardinal : Fintype.card (Position len)=∑t,len t := by
  rw [Fintype.card_congr (fin len),Fintype.card_sigma]
  simp only [Fintype.card_fin]
variable {A : Type} (w v : T → List A)
abbrev prefix_bound (t : T) : (w t).length≤(w t++v t).length := by
  simp only [List.length_append]
  omega
lemma new_card : (Finset.univ.filter (fun x : Position (fun t=>(w t++v t).length)=>
    ¬ExtendComparisons.Old (len:=fun t=>(w t).length) x)).card=∑t,(v t).length := by
  have hp := Finset.card_filter_add_card_filter_not
    (s:=Finset.univ (α:=Position (fun t=>(w t++v t).length)))
    (p:=fun x=>ExtendComparisons.Old (len:=fun t=>(w t).length) x)
  have ho := ExtendComparisons.old_card (prefix_bound w v)
  rw [ho,Finset.card_univ,cardinal,cardinal] at hp
  simp only [List.length_append,Finset.sum_add_distrib] at hp
  omega
variable {E : Type} (C : Comparisons (E:=E) (fun t=>(w t).length))
lemma fixed_card (hfull : ∀ x,C.pairing.partner x≠x) :
    (Finset.univ.filter (fun x=>ExtendComparisons.partner C (prefix_bound w v) x=x)).card=
      ∑t,(v t).length := by
  rw [ExtendComparisons.fixed_card,new_card]
  have he : (Finset.univ.filter (fun x=>C.pairing.partner x=x))=∅ := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
    exact hfull x
  rw [he,Finset.card_empty,Nat.zero_add]
omit [Fintype T] in
lemma nonfixed_old (p : Position (fun t=>(w t++v t).length))
    (hp : ExtendComparisons.partner C (prefix_bound w v) p≠p) :
    p.2.val∈positions 0 (w p.1).length := by
  by_contra hn
  exact hp (ExtendComparisons.partner_new C (prefix_bound w v) p hn)
end TorsionFreeZeroDivisors.WordPositions

namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore BlockAlignment ComparedBlocks
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
    {E : Type} [Fintype E]
    (C : Comparisons (E:=E) (fun p=>(seg s cap hc p).length))
    (lo hi : E → ℕ) (hlo : ∀ e,C.lo e=lo e) (hhi : ∀ e,C.hi e=hi e)
    (hle : ∀ e,lo e≤hi e) (hh : ∀ e,hi e≤(seg s cap hc (C.source e)).length)
    (hred : ∀ p e,C.side p=some e →
      RawDecomposition.dart (seg s cap hc) p≠RawDecomposition.dart (seg s cap hc) (C.pairing.partner p) ∧
      RawDecomposition.dart (seg s cap hc) p≠(graph rep r).reverse (RawDecomposition.dart (seg s cap hc) (C.pairing.partner p)))
    (hcomp : ∀ p e,C.side p=some e → label rep (RawDecomposition.dart (seg s cap hc) p)=
      if C.reverse e then Types.inverse (label rep (RawDecomposition.dart (seg s cap hc) (C.pairing.partner p)))
      else label rep (RawDecomposition.dart (seg s cap hc) (C.pairing.partner p)))
abbrev grow := WordPositions.prefix_bound (seg s cap hc) (tail s cap hc hL hd)
include hhi hh in
omit [Fintype E] in
lemma upper_real (e : E) : C.hi e≤((seg s cap hc (C.source e)).length:ℝ) := by
  rw [hhi]
  exact_mod_cast hh e

/-- Appending the actual short closures changes neither original comparison nor
its underlying graph lifts. Every newly added position is unpaired. -/
def system : PathSystem rep r x y where
  P := Piece s cap
  E := E
  fP := inferInstance
  fE := inferInstance
  paths := word s cap hc hL hd
  nonempty := nonempty s cap hc hL hd
  root := root s cap hc
  path_chain := chain s cap hc hL hd
  cyclic_chain := cyclic s cap hc hL hd
  comparisons := ExtendComparisons.comparisons C (grow s cap hc hL hd) (upper_real s cap hc C hi hhi hh)
  lower := lo
  upper := hi
  lower_eq := hlo
  upper_eq := hhi
  lower_le := hle
  upper_le e := (hh e).trans (grow s cap hc hL hd _)
  reduced := by
    intro p e he
    have hp := ExtendComparisons.side_some_old C he
    have he' : C.side (ExtendComparisons.project p hp)=some e := by
      simpa only [ExtendComparisons.comparisons,ExtendComparisons.side,dite_eq_left hp] using he
    have hg := hred (ExtendComparisons.project p hp) e he'
    rw [←ExtendComparisons.embed_project (grow s cap hc hL hd) p hp]
    change RawDecomposition.dart (fun p=>seg s cap hc p++tail s cap hc hL hd p) _≠
      RawDecomposition.dart _ (ExtendComparisons.partner C (grow s cap hc hL hd) _) ∧
      RawDecomposition.dart (fun p=>seg s cap hc p++tail s cap hc hL hd p) _ ≠(graph rep r).reverse (RawDecomposition.dart _ (ExtendComparisons.partner C (grow s cap hc hL hd) _))
    rw [ExtendComparisons.partner_embed]
    simpa only [word,WordPositions.dart_prefix] using hg
  rootA := rootA s cap hc hL hd
  rootB := rootB s cap hc hL hd
  compatible := by
    intro p e he
    have hp := ExtendComparisons.side_some_old C he
    have he' : C.side (ExtendComparisons.project p hp)=some e := by
      simpa only [ExtendComparisons.comparisons,ExtendComparisons.side,dite_eq_left hp] using he
    have hg := hcomp (ExtendComparisons.project p hp) e he'
    rw [←ExtendComparisons.embed_project (grow s cap hc hL hd) p hp]
    change label rep (RawDecomposition.dart (fun p=>seg s cap hc p++tail s cap hc hL hd p) _)=
      if C.reverse e then Types.inverse (label rep (RawDecomposition.dart _ (ExtendComparisons.partner C (grow s cap hc hL hd) _)))
      else label rep (RawDecomposition.dart _ (ExtendComparisons.partner C (grow s cap hc hL hd) _))
    rw [ExtendComparisons.partner_embed]
    simpa only [word,WordPositions.dart_prefix] using hg
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

namespace TorsionFreeZeroDivisors.BoundaryRotation

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T : Type} (len : T → ℕ)
def perm : Equiv.Perm (Position len) :=
  (fin len).symm.permCongr (Equiv.sigmaCongrRight fun t=>finRotate (len t))
lemma apply_fin (t : T) (i : Fin (len t)) :
    perm len ((fin len).symm ⟨t,i⟩)=(fin len).symm ⟨t,finRotate (len t) i⟩ := by
  simp only [perm,Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply,
    Equiv.sigmaCongrRight_apply]
lemma pow_fin (t : T) (i : Fin (len t)) (n : ℕ) :
    (perm len^n) ((fin len).symm ⟨t,i⟩)=(fin len).symm ⟨t,(finRotate (len t)^n) i⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,ih,apply_fin,pow_succ',Equiv.Perm.mul_apply]
lemma first (x : Position len) : (perm len x).1=x.1 := by
  rw [←(fin len).symm_apply_apply x]
  exact rfl
lemma finRotate_same {n : ℕ} (i j : Fin n) : (finRotate n).SameCycle i j := by
  by_cases hn : 2≤n
  · apply Equiv.Perm.IsCycle.sameCycle (isCycle_finRotate_of_le hn)
    · have hm : i∈(finRotate n).support := by rw [support_finRotate_of_le hn]; exact Finset.mem_univ _
      exact Equiv.Perm.mem_support.mp hm
    · have hm : j∈(finRotate n).support := by rw [support_finRotate_of_le hn]; exact Finset.mem_univ _
      exact Equiv.Perm.mem_support.mp hm
  · have he : i=j := by apply Fin.ext; omega
    exact he.sameCycle _
lemma same_first {x y : Position len} (h : x.1=y.1) : (perm len).SameCycle x y := by
  rcases x with ⟨a',i'⟩
  rcases y with ⟨b',j'⟩
  dsimp at h
  subst b'
  let u : Fin (len a') := ⟨i'.val.toNat,by have hb:=bounds i'; omega⟩
  let v : Fin (len a') := ⟨j'.val.toNat,by have hb:=bounds j'; omega⟩
  obtain ⟨n,hn⟩ := (finRotate_same u v).exists_nat_pow_eq
  refine ⟨(n:ℤ),?_⟩
  rw [zpow_natCast]
  have hh := pow_fin len a' u n
  rw [hn] at hh
  change (perm len^n) ((fin len).symm (fin len ⟨a',i'⟩))=(fin len).symm (fin len ⟨a',j'⟩) at hh
  simpa only [Equiv.symm_apply_apply] using hh
lemma next {x : Position len} (hx : x.2.val+1<(len x.1:ℤ)) :
    (perm len x).2.val=x.2.val+1 := by
  let i : Fin (len x.1) := ⟨x.2.val.toNat,by have hb:=bounds x.2; omega⟩
  have he := apply_fin len x.1 i
  change perm len ((fin len).symm (fin len x))=(fin len).symm ⟨x.1,finRotate (len x.1) i⟩ at he
  rw [Equiv.symm_apply_apply] at he
  rw [he]
  change ((finRotate (len x.1) i).val:ℤ)=x.2.val+1
  have hb := bounds x.2
  have hp : 0<len x.1 := by omega
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : len x.1≠0)
  have hc : ∀ i : Fin (len x.1),i.val+1<len x.1 → (finRotate (len x.1) i).val=i.val+1 := by
    rw [hn]
    intro i hi
    apply coe_finRotate_of_ne_last
    intro he
    rw [he,Fin.val_last] at hi
    omega
  rw [hc _ (by change x.2.val.toNat+1<len x.1; omega)]
  change ((x.2.val.toNat+1:ℕ):ℤ)=x.2.val+1
  push_cast
  rw [Int.toNat_of_nonneg hb.1]
variable [Fintype T]
lemma cycles_le : Fintype.card (Cycle (perm len))≤Fintype.card T := by
  let f : Cycle (perm len) → T := fun c=>(Quotient.out c).1
  have hi : Function.Injective f := by
    intro c d h
    have hh := same_first len h
    have he := (cycle_eq (perm len)).mpr hh
    simpa only [cycle,Quotient.out_eq] using he
  exact Fintype.card_le_of_injective f hi

def ends : Finset (Position len) := Finset.univ.filter (fun x=>x.2.val+1=len x.1)
lemma ends_le : (ends len).card≤Fintype.card T := by
  let f : {x // x∈ends len} → T := fun x=>x.val.1
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply PlanarIntervals.position_ext h
    have hx := (Finset.mem_filter.mp x.property).2
    have hy := (Finset.mem_filter.mp y.property).2
    change x.val.1=y.val.1 at h
    have hh := congrArg (fun t=>(len t:ℤ)) h
    omega
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi
lemma hits (x : Position len) : ∃ y∈ends len,(perm len).SameCycle x y := by
  have hb := bounds x.2
  let j : Fin (len x.1) := ⟨len x.1-1,by omega⟩
  refine ⟨(fin len).symm ⟨x.1,j⟩,?_,same_first len rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  change ((len x.1-1:ℕ):ℤ)+1=len x.1
  omega
end

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T A : Type} [Fintype T] (len : T → ℕ) (root : Option T)
    (label : Position len → A) (bar : A → A) (α : Equiv.Perm (Position len))
    (hr : Function.Involutive α)
    (hcomp : ∀ x,label (α x)=bar (label x))
    (hred : ∀ x,root≠some x.1 ∨ x∉ends len → label (perm len x)≠bar (label x))
include hr hcomp hred in
lemma fixed_root_end {x : Position len} (hx : PlanarRotation.opposite (perm len) α x=x) :
    root=some x.1 ∧ x∈ends len := by
  have he : perm len x=α x := by
    have hh := congrArg α hx
    change α (α (perm len x))=α x at hh
    rwa [hr] at hh
  have hl : label (perm len x)=bar (label x) := he ▸ hcomp x
  constructor
  · by_contra hn
    exact hred x (Or.inl hn) hl
  · by_contra hn
    exact hred x (Or.inr hn) hl
include hr hcomp hred in
lemma monogons_le : (fixed (PlanarRotation.opposite (perm len) α)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [fixed,Finset.mem_filter,Finset.mem_univ,true_and] at hx hy
  have hx := fixed_root_end len root label bar α hr hcomp hred hx
  have hy := fixed_root_end len root label bar α hr hcomp hred hy
  have hs : x.1=y.1 := Option.some.inj (hx.1.symm.trans hy.1)
  apply PlanarIntervals.position_ext hs
  have hx' := (Finset.mem_filter.mp hx.2).2
  have hy' := (Finset.mem_filter.mp hy.2).2
  have hh := congrArg (fun t=>(len t:ℤ)) hs
  omega
end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions
variable {T : Type} (len : T → ℕ)
lemma last_next {x : Position len} (hx : x.2.val+1=(len x.1:ℤ)) : (perm len x).2.val=0 := by
  have hb := bounds x.2
  let i : Fin (len x.1) := ⟨x.2.val.toNat,by omega⟩
  have he := apply_fin len x.1 i
  change perm len ((fin len).symm (fin len x))=(fin len).symm ⟨x.1,finRotate (len x.1) i⟩ at he
  rw [Equiv.symm_apply_apply] at he
  rw [he]
  change ((finRotate (len x.1) i).val:ℤ)=0
  have hn : len x.1≠0 := by omega
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hc : ∀ j : Fin (len x.1),j.val+1=len x.1 → (finRotate (len x.1) j).val=0 := by
    rw [hn]
    intro j hj
    have he : j=Fin.last n := by apply Fin.ext; simp only [Fin.val_last]; omega
    rw [he,finRotate_last]
    rfl
  rw [hc _ (by dsimp only [i]; omega)]
  rfl
variable {A : Type} (w : T → List A) (R : A → A → Prop)
lemma step_nonlast (hc : ∀t,(w t).IsChain R) (x : Position (fun t=>(w t).length))
    (hx : x.2.val+1<(w x.1).length) :
    R (RawDecomposition.dart w x) (RawDecomposition.dart w (perm (fun t=>(w t).length) x)) := by
  have hb := bounds x.2
  have hh := next (fun t=>(w t).length) hx
  have hi : x.2.val.toNat+1<(w x.1).length := by omega
  have hn : (perm (fun t=>(w t).length) x).2.val.toNat=x.2.val.toNat+1 := by omega
  have hc := (List.isChain_iff_getElem.mp (hc x.1)) x.2.val.toNat hi
  change R (w x.1)[x.2.val.toNat] (w x.1)[(perm (fun t=>(w t).length) x).2.val.toNat]
  simpa only [hn] using hc
lemma step_last (hne : ∀t,w t≠[]) (x : Position (fun t=>(w t).length))
    (hx : x.2.val+1=(w x.1).length)
    (hcyc : ∀ᵉ (a∈(w x.1).getLast?) (b∈(w x.1).head?),R a b) :
    R (RawDecomposition.dart w x) (RawDecomposition.dart w (perm (fun t=>(w t).length) x)) := by
  have hb := bounds x.2
  have hn : x.2.val.toNat=(w x.1).length-1 := by omega
  have hh := last_next (fun t=>(w t).length) hx
  have hc := hcyc ((w x.1).getLast (hne x.1)) (List.getLast_mem_getLast? (hne x.1))
    ((w x.1).head (hne x.1)) (List.head_mem_head? (hne x.1))
  change R (w x.1)[x.2.val.toNat] (w x.1)[(perm (fun t=>(w t).length) x).2.val.toNat]
  simpa only [hn,hh,List.getLast_eq_getElem,List.head_eq_getElem,Int.toNat_zero] using hc
end TorsionFreeZeroDivisors.BoundaryRotation

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions BoundaryRotation WeightedMoore ActualPatternEvent GirthAsymptotics
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} (s : PathSystem rep r x y)
lemma step_label {d e : DA rep⊕DB rep}
    (h : PortWalk.step (graph rep r).origin (graph rep r).reverse d e) :
    label rep e≠Types.inverse (label rep d) := by
  intro he
  exact h.2 (immersed rep r e ((graph rep r).reverse d) h.1.symm
    (he.trans (label_reverse rep r d).symm))
lemma boundary_reduced (p : Position (fun t=>(s.paths t).length))
    (hp : s.root≠some p.1 ∨ p∉BoundaryRotation.ends (fun t=>(s.paths t).length)) :
    label rep (RawDecomposition.dart s.paths (perm (fun t=>(s.paths t).length) p))≠
      Types.inverse (label rep (RawDecomposition.dart s.paths p)) := by
  have hb : 0≤p.2.val ∧ p.2.val<((s.paths p.1).length:ℤ) := bounds p.2
  apply step_label
  by_cases hl : p.2.val+1=(s.paths p.1).length
  · apply step_last s.paths _ s.nonempty p hl
    apply s.cyclic_chain p.1
    apply (ClosedWords.cyclic_iff _ _).mpr
    rcases hp with hp|hp
    · exact hp
    · exact False.elim (hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩))
  · exact step_nonlast s.paths _ s.path_chain p (by omega)
end TorsionFreeZeroDivisors.SampleGraph.PathSystem

namespace TorsionFreeZeroDivisors.PermutationTransport
variable {A B : Type} (e : A ≃ B) (f : Equiv.Perm A)
lemma pow_apply (x : A) (n : ℕ) : (e.permCongr f^n) (e x)=e ((f^n) x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Equiv.Perm.mul_apply,ih,Equiv.permCongr_apply,Equiv.symm_apply_apply]
lemma sameCycle [Finite A] {x y : A} (h : f.SameCycle x y) : (e.permCongr f).SameCycle (e x) (e y) := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  exact ⟨(n:ℤ),by rw [zpow_natCast,pow_apply,hn]⟩
lemma involutive (h : Function.Involutive f) : Function.Involutive (e.permCongr f) := by
  intro x
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  rw [h,Equiv.apply_symm_apply]
lemma fixed_free (h : ∀x,f x≠x) (x : B) : e.permCongr f x≠x := by
  intro he
  apply h (e.symm x)
  simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using congrArg e.symm he
lemma mul (g : Equiv.Perm A) : e.permCongr (f*g)=e.permCongr f*e.permCongr g := by
  ext x
  simp only [Equiv.Perm.mul_apply,Equiv.permCongr_apply,Equiv.symm_apply_apply]
end TorsionFreeZeroDivisors.PermutationTransport

namespace TorsionFreeZeroDivisors.BalancedRotation
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T A : Type} [Fintype T] (w : T → List A) (cap : ℕ) (hc : 0<cap)
abbrev len (p : BalancedWords.Piece w cap) := (BalancedWords.segment w cap hc p).length
abbrev e := WordPositions.segments w cap hc
omit [Fintype T] in
lemma source (x : Position (len w cap hc)) : (e w cap hc x).1=x.1.1 := rfl
omit [Fintype T] in
lemma value (x : Position (len w cap hc)) : (e w cap hc x).2.val=
    (ConsecutivePieces.offset (BalancedPieces.sizes (w x.1.1).length cap) x.1.2:ℤ)+x.2.val :=
  WordPositions.join_value w cap hc (ComparisonGeometry.position (Equiv.refl _) (BalancedWords.segment_length w cap hc) x)
def perm : Equiv.Perm (Position (len w cap hc)) :=
  (e w cap hc).symm.permCongr (BoundaryRotation.perm (fun t=>(w t).length))
omit [Fintype T] in
lemma transport (x : Position (len w cap hc)) :
    e w cap hc (perm w cap hc x)=BoundaryRotation.perm (fun t=>(w t).length) (e w cap hc x) := by
  simp only [perm,Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
lemma same_source {x y : Position (len w cap hc)} (h : x.1.1=y.1.1) : (perm w cap hc).SameCycle x y := by
  have hh := BoundaryRotation.same_first (fun t=>(w t).length) (x:=e w cap hc x) (y:=e w cap hc y) h
  have hp := PermutationTransport.sameCycle (e w cap hc).symm _ hh
  change ((e w cap hc).symm.permCongr (BoundaryRotation.perm (fun t=>(w t).length))).SameCycle x y
  simpa only [Equiv.symm_apply_apply] using hp
omit [Fintype T] in
lemma step {x : Position (len w cap hc)} (hx : x.2.val+1<(len w cap hc x.1:ℤ)) :
    (perm w cap hc x).1=x.1 ∧ (perm w cap hc x).2.val=x.2.val+1 := by
  have hb := bounds x.2
  let y : Position (len w cap hc) := ⟨x.1,⟨x.2.val+1,by
    simp only [AffineIntervals.nat_positions,Finset.mem_Ico]
    exact ⟨by omega,hx⟩⟩⟩
  have hy := bounds (e w cap hc y).2
  have hxe := value w cap hc x
  have hye := value w cap hc y
  dsimp only [y] at hye
  have ht : (e w cap hc x).2.val+1<((w (e w cap hc x).1).length:ℤ) := by
    have hy2 := hy.2
    change (e w cap hc y).2.val<((w x.1.1).length:ℤ) at hy2
    change (e w cap hc y).2.val=_+ (x.2.val+1) at hye
    change (e w cap hc x).2.val+1<((w x.1.1).length:ℤ)
    omega
  have he : e w cap hc (perm w cap hc x)=e w cap hc y := by
    rw [transport]
    apply PlanarIntervals.position_ext
    · exact BoundaryRotation.first _ _
    · rw [BoundaryRotation.next _ ht,hxe,hye]
      omega
  have he := (e w cap hc).injective he
  rw [he]
  exact ⟨rfl,rfl⟩
lemma hits (x : Position (len w cap hc)) :
    ∃ y∈BoundaryRotation.ends (len w cap hc),(perm w cap hc).SameCycle x y := by
  have hb := bounds x.2
  let j : Fin (len w cap hc x.1) := ⟨len w cap hc x.1-1,by omega⟩
  let y := (fin (len w cap hc)).symm ⟨x.1,j⟩
  refine ⟨y,?_,same_source w cap hc rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  change ((len w cap hc x.1-1:ℕ):ℤ)+1=len w cap hc x.1
  omega
lemma cycles_le : Fintype.card (Cycle (perm w cap hc))≤Fintype.card (BalancedWords.Piece w cap) := by
  have hT : Fintype.card (Cycle (perm w cap hc))≤Fintype.card T := by
    let f : Cycle (perm w cap hc) → T := fun c=>(Quotient.out c).1.1
    have hf : Function.Injective f := by
      intro c d hd
      have hh := same_source w cap hc hd
      have he := (cycle_eq (perm w cap hc)).mpr hh
      simpa only [cycle,Quotient.out_eq] using he
    exact Fintype.card_le_of_injective f hf
  apply hT.trans
  let f : T → BalancedWords.Piece w cap := fun t=>⟨t,⟨0,BalancedPieces.number_pos hc⟩⟩
  exact Fintype.card_le_of_injective f (fun _ _ h=>congrArg Sigma.fst h)
end TorsionFreeZeroDivisors.BalancedRotation

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
/-- The full inverse-letter pairing of the original boundary words, retaining
actual graph lifts. Planarity is additional data, not asserted here. -/
structure FullPairing (s : PathSystem rep r x y) where
  perm : Equiv.Perm (Position (fun t=>(s.paths t).length))
  involutive : Function.Involutive perm
  fixed_free : ∀p,perm p≠p
  compatible : ∀p,label rep (RawDecomposition.dart s.paths (perm p))=
    Types.inverse (label rep (RawDecomposition.dart s.paths p))
  reduced : ∀p,RawDecomposition.dart s.paths p≠RawDecomposition.dart s.paths (perm p) ∧
    RawDecomposition.dart s.paths p≠(graph rep r).reverse (RawDecomposition.dart s.paths (perm p))
namespace FullPairing
variable {s : PathSystem rep r x y} (a : FullPairing s) (cap : ℕ) (hc : 0<cap)
def α : Equiv.Perm (Position (BalancedRotation.len s.paths cap hc)) := (BalancedRotation.e s.paths cap hc).symm.permCongr a.perm
lemma α_involutive : Function.Involutive (a.α cap hc) :=
  PermutationTransport.involutive (BalancedRotation.e s.paths cap hc).symm a.perm a.involutive
lemma α_fixed_free (p : Position (BalancedRotation.len s.paths cap hc)) : a.α cap hc p≠p :=
  PermutationTransport.fixed_free (BalancedRotation.e s.paths cap hc).symm a.perm a.fixed_free p
lemma transport (p : Position (BalancedRotation.len s.paths cap hc)) : BalancedRotation.e s.paths cap hc (a.α cap hc p)=a.perm (BalancedRotation.e s.paths cap hc p) := by
  simp only [α,Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
def cuts : PlanarRuns.CutSystem (BalancedRotation.perm s.paths cap hc) :=
  PlanarRuns.CutSystem.ofMarks (a.α cap hc) (BoundaryRotation.ends (BalancedRotation.len s.paths cap hc))
    (BalancedRotation.hits s.paths cap hc)
theorem paired : (a.cuts cap hc).Paired (a.α cap hc) :=
  PlanarRuns.CutSystem.ofMarks_paired (a.α cap hc) (BoundaryRotation.ends (BalancedRotation.len s.paths cap hc))
    (BalancedRotation.hits s.paths cap hc) (a.α_involutive cap hc) (a.α_fixed_free cap hc)
lemma step (p : Position (BalancedRotation.len s.paths cap hc)) (hp : p∉(a.cuts cap hc).cut) :
    (BalancedRotation.perm s.paths cap hc p).1=p.1 ∧ (BalancedRotation.perm s.paths cap hc p).2.val=p.2.val+1 := by
  apply BalancedRotation.step
  have hb := WordPositions.bounds p.2
  have hn : p∉BoundaryRotation.ends (BalancedRotation.len s.paths cap hc) := by
    intro hm
    apply hp
    simp only [cuts,PlanarRuns.CutSystem.ofMarks,PlanarRotation.cuts,Finset.mem_union]
    exact Or.inl (Or.inr hm)
  have hn : p.2.val+1≠(BalancedRotation.len s.paths cap hc p.1:ℤ) := by
    intro he
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  omega
abbrev Side := {p // p∈(a.cuts cap hc).cut}
def comparisons : Comparisons (E:=a.Side cap hc) (BalancedRotation.len s.paths cap hc) :=
  PlanarIntervals.comparisons (a.cuts cap hc) (a.paired cap hc) (a.step cap hc)
def lower (d : a.Side cap hc) : ℕ := (PlanarIntervals.lower (a.cuts cap hc) (a.paired cap hc) d).toNat
def upper (d : a.Side cap hc) : ℕ := (PlanarIntervals.upper (a.cuts cap hc) d).toNat
lemma bounds (d : a.Side cap hc) :
    0≤PlanarIntervals.lower (a.cuts cap hc) (a.paired cap hc) d ∧
    PlanarIntervals.lower (a.cuts cap hc) (a.paired cap hc) d<PlanarIntervals.upper (a.cuts cap hc) d ∧
    PlanarIntervals.upper (a.cuts cap hc) d≤BalancedRotation.len s.paths cap hc ((a.paired cap hc).first d).1 :=
  PlanarIntervals.bounds (a.cuts cap hc) (a.paired cap hc) (a.step cap hc) d
lemma lower_eq (d : a.Side cap hc) : (a.comparisons cap hc).lo d=a.lower cap hc d := by
  change (PlanarIntervals.lower (a.cuts cap hc) (a.paired cap hc) d:ℝ)=_
  rw [lower,←Int.cast_natCast,Int.toNat_of_nonneg (a.bounds cap hc d).1]
lemma upper_eq (d : a.Side cap hc) : (a.comparisons cap hc).hi d=a.upper cap hc d := by
  change (PlanarIntervals.upper (a.cuts cap hc) d:ℝ)=_
  rw [upper,←Int.cast_natCast,Int.toNat_of_nonneg (by have := a.bounds cap hc d; omega)]
lemma lower_le (d : a.Side cap hc) : a.lower cap hc d≤a.upper cap hc d := by
  have := a.bounds cap hc d
  dsimp only [lower,upper]
  omega
lemma upper_le (d : a.Side cap hc) : a.upper cap hc d≤BalancedRotation.len s.paths cap hc ((a.comparisons cap hc).source d) := by
  exact Int.toNat_le.mpr (a.bounds cap hc d).2.2
lemma dart (p : Position (BalancedRotation.len s.paths cap hc)) : RawDecomposition.dart (ClosedWords.seg s cap hc) p=
    RawDecomposition.dart s.paths (BalancedRotation.e s.paths cap hc p) := WordPositions.segments_dart s.paths cap hc p
lemma balanced_reduced (p : Position (BalancedRotation.len s.paths cap hc)) :
    RawDecomposition.dart (ClosedWords.seg s cap hc) p≠RawDecomposition.dart (ClosedWords.seg s cap hc) (a.α cap hc p) ∧
    RawDecomposition.dart (ClosedWords.seg s cap hc) p≠(graph rep r).reverse (RawDecomposition.dart (ClosedWords.seg s cap hc) (a.α cap hc p)) := by
  rw [dart cap hc,dart cap hc,a.transport]
  exact a.reduced (BalancedRotation.e s.paths cap hc p)
lemma balanced_compatible (p : Position (BalancedRotation.len s.paths cap hc)) :
    label rep (RawDecomposition.dart (ClosedWords.seg s cap hc) p)=
      Types.inverse (label rep (RawDecomposition.dart (ClosedWords.seg s cap hc) (a.α cap hc p))) := by
  rw [dart cap hc,dart cap hc,a.transport,a.compatible,Types.inverse_inverse]
end FullPairing
end TorsionFreeZeroDivisors.SampleGraph

namespace TorsionFreeZeroDivisors.PermutationTransport
open PermutationCycles
variable {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (f : Equiv.Perm A)
lemma sameCycle_iff (x y : A) : f.SameCycle x y ↔ (e.permCongr f).SameCycle (e x) (e y) := by
  refine ⟨sameCycle e f,?_⟩
  intro h
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  refine ⟨(n:ℤ),?_⟩
  rw [zpow_natCast]
  apply e.injective
  rwa [pow_apply] at hn
def cycles : Cycle f ≃ Cycle (e.permCongr f) := Quotient.congr e (sameCycle_iff e f)
lemma card_cycles : Fintype.card (Cycle (e.permCongr f))=Fintype.card (Cycle f) :=
  (Fintype.card_congr (cycles e f)).symm
end TorsionFreeZeroDivisors.PermutationTransport

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent PermutationCycles PlanarRotation
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    {s : PathSystem rep r x y} (a : FullPairing s) (cap : ℕ) (hc : 0<cap)
lemma opposite_eq : opposite (BalancedRotation.perm s.paths cap hc) (a.α cap hc)=
    (BalancedRotation.e s.paths cap hc).symm.permCongr
      (opposite (BoundaryRotation.perm (fun t=>(s.paths t).length)) a.perm) := by
  exact (PermutationTransport.mul (BalancedRotation.e s.paths cap hc).symm a.perm _).symm
lemma opposite_transport (p : Position (BalancedRotation.len s.paths cap hc)) :
    BalancedRotation.e s.paths cap hc (opposite (BalancedRotation.perm s.paths cap hc) (a.α cap hc) p)=
      opposite (BoundaryRotation.perm (fun t=>(s.paths t).length)) a.perm (BalancedRotation.e s.paths cap hc p) := by
  change BalancedRotation.e s.paths cap hc (a.α cap hc (BalancedRotation.perm s.paths cap hc p))=_
  rw [a.transport,BalancedRotation.transport]
  rfl
lemma monogons : (fixed (opposite (BalancedRotation.perm s.paths cap hc) (a.α cap hc))).card≤1 := by
  have ho := BoundaryRotation.monogons_le (fun t=>(s.paths t).length) s.root
    (fun p=>label rep (RawDecomposition.dart s.paths p)) Types.inverse a.perm a.involutive
    a.compatible s.boundary_reduced
  apply Finset.card_le_one.mpr
  intro p hp q hq
  simp only [fixed,Finset.mem_filter,Finset.mem_univ,true_and] at hp hq
  apply (BalancedRotation.e s.paths cap hc).injective
  apply Finset.card_le_one.mp ho
  · simp only [fixed,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [←a.opposite_transport,hp]
  · simp only [fixed,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [←a.opposite_transport,hq]
/-- Only Euler planarity is needed in the interval-count argument. This file
proves neither Euler planarity for an abstract pairing nor its PL realization. -/
def Euler : Prop := Fintype.card (Position (fun t=>(s.paths t).length))+4≤
  2*Fintype.card (Cycle (BoundaryRotation.perm (fun t=>(s.paths t).length)))+
  2*Fintype.card (Cycle (opposite (BoundaryRotation.perm (fun t=>(s.paths t).length)) a.perm))
lemma balanced_euler (h : a.Euler) : Fintype.card (Position (BalancedRotation.len s.paths cap hc))+4≤
    2*Fintype.card (Cycle (BalancedRotation.perm s.paths cap hc))+
    2*Fintype.card (Cycle (opposite (BalancedRotation.perm s.paths cap hc) (a.α cap hc))) := by
  rw [a.opposite_eq,PermutationTransport.card_cycles]
  change _≤2*Fintype.card (Cycle ((BalancedRotation.e s.paths cap hc).symm.permCongr
    (BoundaryRotation.perm (fun t=>(s.paths t).length))))+_
  rw [PermutationTransport.card_cycles,Fintype.card_congr (BalancedRotation.e s.paths cap hc)]
  exact h
lemma sides_le (h : a.Euler) : Fintype.card (a.Side cap hc)≤12*Fintype.card (ClosedWords.Piece s cap) := by
  rw [Fintype.card_coe]
  apply cuts_le_twelve
  · exact a.balanced_euler cap hc h
  · exact a.monogons cap hc
  · exact BalancedRotation.cycles_le s.paths cap hc
  · have hm := BoundaryRotation.ends_le (BalancedRotation.len s.paths cap hc)
    exact hm.trans (Nat.le_add_left _ _)
end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    {s : PathSystem rep r x y} (a : FullPairing s) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
/-- The actual balanced and short-closed system, with all cut comparisons and
all closure positions left unpaired. -/
def closed : PathSystem rep r x y := ClosedWords.system s cap hc hL hd (a.comparisons cap hc)
  (a.lower cap hc) (a.upper cap hc) (a.lower_eq cap hc) (a.upper_eq cap hc)
  (a.lower_le cap hc) (a.upper_le cap hc)
  (fun p _ _=>a.balanced_reduced cap hc p) (fun p _ _=>a.balanced_compatible cap hc p)
lemma closed_fixed : (Finset.univ.filter (fun p=>(a.closed cap hc hL hd).comparisons.pairing.partner p=p)).card=
    ∑t,(ClosedWords.tail s cap hc hL hd t).length :=
  WordPositions.fixed_card (ClosedWords.seg s cap hc) (ClosedWords.tail s cap hc hL hd)
    (a.comparisons cap hc) (a.α_fixed_free cap hc)
lemma closed_old (p : Position (fun t=>((a.closed cap hc hL hd).paths t).length))
    (hp : (a.closed cap hc hL hd).comparisons.pairing.partner p≠p) :
    p.2.val∈positions 0 (BalancedWords.old s.paths cap p.1) := by
  have hh := WordPositions.nonfixed_old (ClosedWords.seg s cap hc) (ClosedWords.tail s cap hc hL hd)
    (a.comparisons cap hc) p hp
  convert hh using 2
  exact_mod_cast (BalancedWords.segment_length s.paths cap hc p.1).symm
end TorsionFreeZeroDivisors.SampleGraph.FullPairing

/-! Recursive separation. This is the actual deletion-set
construction and sharp charging estimate. The one-step Lipton–Tarjan theorem
is kept as an explicit dependency, not asserted from an unspecified planar
predicate.  No claim of a completed planar realization is made here. -/
namespace TorsionFreeZeroDivisors.RecursiveSeparator
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] (R : V → V → Prop)

/-- Every retained vertex lies in a small set closed under all retained edges. -/
def Small (S : Finset V) (K : ℕ) : Prop :=
  ∀ x∈S, ∃ T : Finset V, T⊆S ∧ x∈T ∧ T.card≤K ∧
    ∀ y∈T, ∀ z∈S, R y z → z∈T

omit [DecidableEq V] in
lemma small_of_card {S : Finset V} {K : ℕ} (h : S.card≤K) : Small R S K := by
  intro x hx
  exact ⟨S,Finset.Subset.refl _,hx,h,fun _ _ _ hz _ => hz⟩

/-- A genuine one-step separator, including its actual components/blocks. -/
structure Split (S : Finset V) where
  remove : Finset V
  parts : Finset (Finset V)
  remove_subset : remove⊆S
  cover : parts.biUnion id=S\remove
  disjoint : (parts : Set (Finset V)).Pairwise Disjoint
  closed : ∀ b∈parts,∀ x∈b,∀ y∈S\remove,R x y → y∈b
  size : ∀ b∈parts,3*b.card≤2*S.card
  cost : (remove.card : ℝ)≤2*Real.sqrt 2*Real.sqrt S.card

namespace Split
variable {R} {S : Finset V} (P : Split R S)
lemma subset {b : Finset V} (hb : b∈P.parts) : b⊆S\P.remove := by
  intro x hx
  rw [←P.cover]
  exact Finset.mem_biUnion.mpr ⟨b,hb,hx⟩
lemma mass : (∑ b∈P.parts,b.card)+P.remove.card=S.card := by
  have h := Finset.card_biUnion P.disjoint
  change (P.parts.biUnion id).card=∑ b∈P.parts,b.card at h
  rw [P.cover] at h
  rw [←h,Finset.card_sdiff_of_subset P.remove_subset]
  exact Nat.sub_add_cancel (Finset.card_le_card P.remove_subset)
lemma smaller {b : Finset V} (hb : b∈P.parts) (hS : 0<S.card) : b.card<S.card := by
  have h := P.size b hb
  omega
end Split

def q : ℝ := Real.sqrt (2/3)
def a : ℝ := 2*Real.sqrt 2
def Csep : ℝ := a/(1-q)
lemma q_pos : 0<q := Real.sqrt_pos.mpr (by norm_num)
lemma q_lt_one : q<1 := by
  unfold q
  have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤2/3) (by norm_num : (2/3:ℝ)<1)
  simpa only [Real.sqrt_one] using h
lemma a_pos : 0<a := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
lemma Csep_pos : 0<Csep := div_pos a_pos (sub_pos.mpr q_lt_one)
lemma Csep_identity : Csep*(1-q)=a := div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr q_lt_one))

lemma sqrt_size {b s : ℕ} (h : 3*b≤2*s) : Real.sqrt b≤q*Real.sqrt s := by
  unfold q
  rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤2/3)]
  apply Real.sqrt_le_sqrt
  have hh : 3*(b:ℝ)≤2*(s:ℝ) := by exact_mod_cast h
  linarith

/-- Charge bound for one recursive child, including leaves that incur no cost. -/
lemma child_charge {K s b : ℕ} (hK : 0<K) (hs : K<s) (hb : 3*b≤2*s)
    {d : ℝ} (hd : if b≤K then d=0 else d≤Csep*b/Real.sqrt K-Csep*q*Real.sqrt b) :
    d≤Csep*b/Real.sqrt K-Csep*b/Real.sqrt s := by
  have hKp : 0<Real.sqrt (K:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hK)
  have hsp : 0<Real.sqrt (s:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (hK.trans hs))
  have hKs : Real.sqrt (K:ℝ)≤Real.sqrt (s:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hs.le)
  by_cases hbK : b≤K
  · rw [ite_eq_left hbK] at hd
    rw [hd]
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left (mul_nonneg Csep_pos.le (Nat.cast_nonneg _)) hKp hKs
  · rw [ite_eq_right hbK] at hd
    apply hd.trans
    apply sub_le_sub_left
    have hh := mul_le_mul_of_nonneg_left (sqrt_size hb) (Real.sqrt_nonneg (b:ℝ))
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _)] at hh
    have hh' : (b:ℝ)/Real.sqrt s≤q*Real.sqrt b := by
      apply (div_le_iff₀ hsp).mpr
      nlinarith only [hh]
    have hh'' := mul_le_mul_of_nonneg_left hh' Csep_pos.le
    simpa only [mul_div_assoc,mul_assoc] using hh''

lemma parent_charge {K s d : ℕ} (hK : 0<K) (hs : K<s) (hd : d ≤ s)
    (hcost : (d:ℝ)≤a*Real.sqrt s) :
    (d:ℝ)+Csep*((s-d:ℕ):ℝ)/Real.sqrt K-Csep*((s-d:ℕ):ℝ)/Real.sqrt s
      ≤ Csep*s/Real.sqrt K-Csep*q*Real.sqrt s := by
  have hKp : 0<Real.sqrt (K:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hK)
  have hsp : 0<Real.sqrt (s:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (hK.trans hs))
  have hKs : Real.sqrt (K:ℝ)≤Real.sqrt (s:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hs.le)
  have hcoeff : 0≤Csep/Real.sqrt K-Csep/Real.sqrt s := sub_nonneg.mpr
    (div_le_div_of_nonneg_left Csep_pos.le hKp hKs)
  have hnonneg := mul_nonneg (Nat.cast_nonneg d) hcoeff
  have he : (s:ℝ)/Real.sqrt s=Real.sqrt s := by
    apply (div_eq_iff (ne_of_gt hsp)).mpr
    exact (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
  rw [Nat.cast_sub hd]
  have hc := Csep_identity
  calc
    _ ≤ a*Real.sqrt s+Csep*s/Real.sqrt K-Csep*s/Real.sqrt s := by
      simp only [div_eq_mul_inv] at hnonneg ⊢
      nlinarith only [hnonneg,hcost]
    _ = _ := by
      have he' : Csep*(s:ℝ)/Real.sqrt s=Csep*Real.sqrt s := by rw [mul_div_assoc,he]
      rw [he']
      have hcs := congrArg (fun x : ℝ => x*Real.sqrt s) hc
      nlinarith only [hcs]

namespace Split
variable {R} {S : Finset V} (P : Split R S) (D : Finset V → Finset V)
def combined : Finset V := P.remove∪P.parts.biUnion D
lemma child_deleted {b : Finset V} (hb : b∈P.parts) : D b⊆P.combined D := by
  intro x hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b,hb,hx⟩)
lemma combined_subset (hD : ∀ b∈P.parts,D b⊆b) : P.combined D⊆S := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx|hx
  · exact P.remove_subset hx
  · obtain ⟨b,hb,hx⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_sdiff.mp (P.subset hb (hD b hb hx))).1
lemma combined_small {K : ℕ} (hsmall : ∀ b∈P.parts,Small R (b\D b) K) :
    Small R (S\P.combined D) K := by
  intro x hx
  have hxS := (Finset.mem_sdiff.mp hx).1
  have hxr : x∉P.remove := fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ h)
  have hcover : x∈P.parts.biUnion id := by rw [P.cover]; exact Finset.mem_sdiff.mpr ⟨hxS,hxr⟩
  obtain ⟨b,hb,hxb⟩ := Finset.mem_biUnion.mp hcover
  have hxd : x∉D b := fun h => (Finset.mem_sdiff.mp hx).2 (P.child_deleted D hb h)
  obtain ⟨T,hTb,hxT,hTK,hclosed⟩ := hsmall b hb x (Finset.mem_sdiff.mpr ⟨hxb,hxd⟩)
  refine ⟨T∩(S\P.combined D),Finset.inter_subset_right,Finset.mem_inter.mpr ⟨hxT,hx⟩,
    (Finset.card_le_card Finset.inter_subset_left).trans hTK,?_⟩
  intro y hy z hz hyz
  have hyT := (Finset.mem_inter.mp hy).1
  have hyb := (Finset.mem_sdiff.mp (hTb hyT)).1
  have hzS := (Finset.mem_sdiff.mp hz).1
  have hzr : z∉P.remove := fun h => (Finset.mem_sdiff.mp hz).2 (Finset.mem_union_left _ h)
  have hzb := P.closed b hb y hyb z (Finset.mem_sdiff.mpr ⟨hzS,hzr⟩) hyz
  have hzd : z∉D b := fun h => (Finset.mem_sdiff.mp hz).2 (P.child_deleted D hb h)
  exact Finset.mem_inter.mpr ⟨hclosed y hyT z (Finset.mem_sdiff.mpr ⟨hzb,hzd⟩) hyz,hz⟩
lemma combined_card : (P.combined D).card≤P.remove.card+∑ b∈P.parts,(D b).card := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_biUnion_le) _)
end Split

/-- Exact recursive deletion, with a stronger potential bound used internally. -/
theorem recursive (K : ℕ) (hK : 0<K)
    (oneStep : ∀ S : Finset V,K<S.card → Nonempty (Split R S)) (S : Finset V) :
    ∃ D : Finset V,D⊆S ∧ Small R (S\D) K ∧
      (if S.card≤K then D=∅ else
        (D.card:ℝ)≤Csep*S.card/Real.sqrt K-Csep*q*Real.sqrt S.card) := by
  suffices ∀ m,∀ S : Finset V,S.card=m →
      ∃ D : Finset V,D⊆S ∧ Small R (S\D) K ∧
        (if S.card≤K then D=∅ else
          (D.card:ℝ)≤Csep*S.card/Real.sqrt K-Csep*q*Real.sqrt S.card) from this _ S rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro S hm
    by_cases hSK : S.card≤K
    · refine ⟨∅,Finset.empty_subset _,?_,by simp only [ite_eq_left hSK]⟩
      simpa only [Finset.sdiff_empty] using small_of_card R hSK
    have hKS : K<S.card := lt_of_not_ge hSK
    let P := (oneStep S hKS).some
    have hchild : ∀ b∈P.parts,∃ D : Finset V,D⊆b ∧ Small R (b\D) K ∧
        (if b.card≤K then D=∅ else
          (D.card:ℝ)≤Csep*b.card/Real.sqrt K-Csep*q*Real.sqrt b.card) := by
      intro b hb
      exact ih b.card (hm ▸ P.smaller hb (hK.trans hKS)) b rfl
    let D : Finset V → Finset V := fun b => if hb : b∈P.parts then (hchild b hb).choose else ∅
    have hD : ∀ b∈P.parts,D b⊆b ∧ Small R (b\D b) K ∧
        (if b.card≤K then D b=∅ else
          ((D b).card:ℝ)≤Csep*b.card/Real.sqrt K-Csep*q*Real.sqrt b.card) := by
      intro b hb
      dsimp only [D]
      rw [dite_eq_left hb]
      exact (hchild b hb).choose_spec
    refine ⟨P.combined D,P.combined_subset D (fun b hb => (hD b hb).1),
      P.combined_small D (fun b hb => (hD b hb).2.1),?_⟩
    rw [ite_eq_right hSK]
    have hcharge : ∀ b∈P.parts,((D b).card:ℝ)≤
        Csep*b.card/Real.sqrt K-Csep*b.card/Real.sqrt S.card := by
      intro b hb
      apply child_charge hK hKS (P.size b hb)
      have hh := (hD b hb).2.2
      split_ifs at hh ⊢ with hc
      · simp only [hh,Finset.card_empty,Nat.cast_zero]
      · exact hh
    have hsummass : (∑ b∈P.parts,(b.card:ℝ))=(S.card:ℝ)-P.remove.card := by
      have hh : (∑ b∈P.parts,(b.card:ℝ))+(P.remove.card:ℝ)=S.card := by exact_mod_cast P.mass
      linarith
    have hsum : (∑ b∈P.parts,((D b).card:ℝ))≤
        Csep*((S.card:ℝ)-P.remove.card)/Real.sqrt K-
        Csep*((S.card:ℝ)-P.remove.card)/Real.sqrt S.card := by
      calc
        _ ≤ ∑ b∈P.parts,(Csep*b.card/Real.sqrt K-Csep*b.card/Real.sqrt S.card) :=
          Finset.sum_le_sum hcharge
        _ = _ := by rw [Finset.sum_sub_distrib,←Finset.sum_div,←Finset.mul_sum,
          ←Finset.sum_div,←Finset.mul_sum,hsummass]
    have hcard : ((P.combined D).card:ℝ)≤P.remove.card+∑ b∈P.parts,((D b).card:ℝ) := by
      exact_mod_cast P.combined_card D
    have hp := parent_charge hK hKS (Finset.card_le_card P.remove_subset) P.cost
    rw [Nat.cast_sub (Finset.card_le_card P.remove_subset)] at hp
    linarith only [hcard,hsum,hp]

/-- Source recursive planar-separation bound, once the actual one-step planar
separator is supplied for every induced subgraph. -/
theorem separator (K : ℕ) (hK : 1≤K)
    (oneStep : ∀ S : Finset V,K<S.card → Nonempty (Split R S)) (S : Finset V) :
    ∃ D : Finset V,D⊆S ∧ Small R (S\D) K ∧ (D.card:ℝ)≤Csep*S.card/Real.sqrt K := by
  obtain ⟨D,hD,hsmall,hcost⟩ := recursive R K hK oneStep S
  refine ⟨D,hD,hsmall,?_⟩
  split_ifs at hcost with h
  · rw [hcost,Finset.card_empty,Nat.cast_zero]
    exact div_nonneg (mul_nonneg Csep_pos.le (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  · exact hcost.trans (sub_le_self _ (mul_nonneg (mul_nonneg Csep_pos.le q_pos.le) (Real.sqrt_nonneg _)))
end TorsionFreeZeroDivisors.RecursiveSeparator

namespace TorsionFreeZeroDivisors.PlanarParameters
open scoped Classical
open RecursiveSeparator
variable (ε : ℝ) (D : ℕ)
def U : ℕ := max 3 ⌈96*(D:ℝ)/ε⌉₊
def η : ℝ := min (1/(32*(U ε D:ℝ))) (ε/(64*(U ε D:ℝ)))
def K : ℕ := max 1 ⌈(Csep/η ε D)^2⌉₊
def C : ℕ := K ε D*(U ε D+D)
def C₂ : ℕ := 32*6
/-- Oriented interval sides; the manuscript's I counts pairs. -/
def sides : ℕ := 2*C₂*C ε D
lemma U_ge : 3≤U ε D := le_max_left _ _
lemma U_pos : 0<U ε D := lt_of_lt_of_le (by norm_num) (U_ge ε D)
lemma η_pos (hε : 0<ε) : 0<η ε D := by
  have hu : (0:ℝ)<U ε D := by exact_mod_cast U_pos ε D
  exact lt_min (by positivity) (by positivity)
lemma K_pos : 0<K ε D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
lemma C_pos : 0<C ε D := Nat.mul_pos (K_pos ε D) (Nat.add_pos_left (U_pos ε D) _)
lemma sides_pos : 0<sides ε D := by
  unfold sides C₂
  exact Nat.mul_pos (by norm_num) (C_pos ε D)

lemma closure_loss (hε : 0<ε) : 3*(D:ℝ)/(U ε D:ℝ)≤ε/32 := by
  have hu : (0:ℝ)<U ε D := by exact_mod_cast U_pos ε D
  have hc : 96*(D:ℝ)/ε≤U ε D :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hh := (div_le_iff₀ hε).mp hc
  apply (div_le_iff₀ hu).mpr
  nlinarith
lemma deletion_loss : 2*η ε D*(U ε D:ℝ)≤1/16 := by
  have hu : (0:ℝ)<U ε D := by exact_mod_cast U_pos ε D
  have h := min_le_left (1/(32*(U ε D:ℝ))) (ε/(64*(U ε D:ℝ)))
  change η ε D≤1/(32*(U ε D:ℝ)) at h
  have hh := (le_div_iff₀ (mul_pos (by norm_num) hu)).mp h
  nlinarith
lemma unpaired_loss : 2*η ε D*(U ε D:ℝ)≤ε/32 := by
  have hu : (0:ℝ)<U ε D := by exact_mod_cast U_pos ε D
  have h := min_le_right (1/(32*(U ε D:ℝ))) (ε/(64*(U ε D:ℝ)))
  change η ε D≤ε/(64*(U ε D:ℝ)) at h
  have hh := (le_div_iff₀ (mul_pos (by norm_num) hu)).mp h
  nlinarith
lemma separator_factor (hε : 0<ε) : Csep/Real.sqrt (K ε D:ℝ)≤η ε D := by
  have he := η_pos ε D hε
  have hk : (0:ℝ)<K ε D := by exact_mod_cast K_pos ε D
  have hq : (Csep/η ε D)^2≤K ε D :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hs := Real.sqrt_nonneg (K ε D:ℝ)
  have hs2 := Real.sq_sqrt hk.le
  have hp : 0<Csep/η ε D := div_pos Csep_pos he
  have hs' : Csep/η ε D≤Real.sqrt (K ε D:ℝ) := by nlinarith
  have hh := (div_le_iff₀ he).mp hs'
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hk)).mpr
  nlinarith

/-- No planar theorem is hidden here: this uses the actual one-step Split
objects and constructs a literal deletion set, with the fixed source K. -/
theorem delete {V : Type} [Fintype V] (R : V → V → Prop) (hε : 0<ε)
    (oneStep : ∀ S : Finset V,K ε D<S.card → Nonempty (Split R S)) :
    ∃ A : Finset V,Small R (Finset.univ\A) (K ε D) ∧
      (A.card:ℝ)≤η ε D*Fintype.card V := by
  obtain ⟨A,_hA,hsmall,hcost⟩ := separator R (K ε D) (K_pos ε D) oneStep Finset.univ
  refine ⟨A,hsmall,?_⟩
  apply hcost.trans
  rw [Finset.card_univ,mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right (separator_factor ε D hε) (Nat.cast_nonneg _)
end TorsionFreeZeroDivisors.PlanarParameters

namespace TorsionFreeZeroDivisors.LocalizationCounts
open scoped Classical BigOperators
open ComparedBlocks BlockAlignment
variable {T E : Type} [Fintype T] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop) (old : T → ℕ)
    (hprefix : ∀ p : Position len,C.pairing.partner p≠p → p.2.val∈positions 0 (old p.1))

def deletedMap (p : {p : Position len // ¬keep p.1 ∧ C.pairing.partner p≠p}) :
    Position (fun t : {t // ¬keep t}=>old t.val) :=
  ⟨⟨p.val.1,p.property.1⟩,⟨p.val.2.val,hprefix p.val p.property.2⟩⟩
omit [Fintype T] in
lemma deleted_injective : Function.Injective (deletedMap C keep old hprefix) := by
  intro a b h
  have ht : a.val.1=b.val.1 := congrArg (fun p=>p.1.val) h
  have hq : a.val.2.val=b.val.2.val := congrArg (fun p=>p.2.val) h
  apply Subtype.ext
  rcases a with ⟨⟨t,x⟩,ha⟩
  rcases b with ⟨⟨u,y⟩,hb⟩
  dsimp only at ht hq ⊢
  subst u
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hq))

include hprefix in
/-- Only deleted ORIGINAL occurrences, not closures, can destroy a partner. -/
lemma deleted_nonfixed_le :
    (Finset.univ.filter (fun p : Position len=>¬keep p.1 ∧ C.pairing.partner p≠p)).card≤
      ∑t∈Finset.univ.filter (fun t=>¬keep t),old t := by
  have hh := Fintype.card_le_of_injective _ (deleted_injective C keep old hprefix)
  have hs : (∑t : {t // ¬keep t},old t.val)=∑t∈Finset.univ.filter (fun t=>¬keep t),old t :=
    (Finset.sum_subtype _ (by intro t; simp) old).symm
  rw [FiniteChunking.position_card,hs] at hh
  simpa only [Fintype.card_subtype] using hh

/-- The exact removed-original-position bound, from the actual deletion set. -/
lemma deleted_mass {U L : ℕ} {η H₀ : ℝ}
    (hcap : ∀ t,old t≤U*L) (hη : 0≤η)
    (hcount : ((Finset.univ.filter (fun t=>¬keep t)).card:ℝ)≤η*Fintype.card T)
    (hpieces : (Fintype.card T:ℝ)*L≤2*H₀) :
    (∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ))≤2*η*U*H₀ := by
  calc
    _ ≤ ∑_t∈Finset.univ.filter (fun t=>¬keep t),(U:ℝ)*L := by
      apply Finset.sum_le_sum
      intro t _
      exact_mod_cast hcap t
    _ = ((Finset.univ.filter (fun t=>¬keep t)).card:ℝ)*(U:ℝ)*L := by simp; ring
    _ ≤ (η*Fintype.card T)*(U:ℝ)*L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ = η*U*((Fintype.card T:ℝ)*L) := by ring
    _ ≤ η*U*(2*H₀) := mul_le_mul_of_nonneg_left hpieces (mul_nonneg hη (Nat.cast_nonneg _))
    _ = _ := by ring
end TorsionFreeZeroDivisors.LocalizationCounts

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs ComparedBlocks ClusterLocalization
abbrev ε : ℝ := StageFusion.epsilon (1/600) 256
lemma ε_pos : 0<ε := StageFusion.epsilon_pos (by norm_num) (by norm_num)
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y)
local instance : Fintype s.P := s.fP
local instance : Fintype s.E := s.fE

/-- The complete deterministic separator-to-forbidden-system implication.
The one-step separator is explicitly the still-missing planar geometry input;
the deletion set, losses, clusters, and realized forbidden words are constructed. -/
theorem excluded_of_separator (D : ℕ) (H₀ : ℝ) (old : s.P → ℕ)
    (hH₀ : 0<H₀) (hL : 0<L (size rep))
    (ho : ∀ t,old t≤(s.paths t).length)
    (hcapOld : ∀ t,old t≤PlanarParameters.U ε D*L (size rep))
    (hcap : ∀ t,(s.paths t).length≤(PlanarParameters.U ε D+D)*L (size rep))
    (hbase : H₀≤∑t,(old t:ℝ))
    (hpieces : (Fintype.card s.P:ℝ)*L (size rep)≤2*H₀)
    (hadded : ((Finset.univ.filter (fun p=>s.comparisons.pairing.partner p=p)).card:ℝ)≤
      3*(D:ℝ)/PlanarParameters.U ε D*H₀)
    (hprefix : ∀ p : Position (fun t=>(s.paths t).length),s.comparisons.pairing.partner p≠p →
      p.2.val∈BlockAlignment.positions 0 (old p.1))
    (hcompare : Fintype.card s.E≤12*Fintype.card s.P)
    (hlong : ∀ t,s.root≠some t → L (size rep)≤(s.paths t).length)
    (hroot : ∀ t,s.root=some t → (s.paths t).length<L (size rep) → ((s.paths t).length:ℝ)≤H₀/2)
    (oneStep : ∀ S : Finset s.P,PlanarParameters.K ε D<S.card →
      Nonempty (RecursiveSeparator.Split
        (PairingClusters.Rel (fun p : Position (fun t=>(s.paths t).length)=>p.1) s.comparisons.pairing.partner) S))
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C ε D) (PlanarParameters.K ε D)
      (PlanarParameters.sides ε D) rep r x y)) : False := by
  classical
  let R := PairingClusters.Rel (fun p : Position (fun t=>(s.paths t).length)=>p.1) s.comparisons.pairing.partner
  obtain ⟨A,hsmall,hA⟩ := PlanarParameters.delete ε D R ε_pos oneStep
  let keep : s.P → Prop := fun t=>t∉A
  have hcount : ((Finset.univ.filter (fun t=>¬keep t)).card:ℝ)≤PlanarParameters.η ε D*Fintype.card s.P := by
    simpa only [keep,not_not,Finset.filter_mem_eq_inter,Finset.univ_inter] using hA
  have hsize : ∀ c : Cluster s.comparisons keep,(ClusterLocalization.paths s.comparisons keep c).card≤PlanarParameters.K ε D := by
    apply ClusterLocalization.paths_card_le
    intro t ht
    obtain ⟨B,_hB,htB,hBK,hcl⟩ := hsmall t (by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and] using ht)
    refine ⟨B,htB,hBK,?_⟩
    intro a ha b hb hab
    exact hcl a ha b (by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and] using hb) hab
  have hη := (PlanarParameters.η_pos ε D ε_pos).le
  have hd : (∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ))≤2*PlanarParameters.η ε D*PlanarParameters.U ε D*H₀ := by
    convert LocalizationCounts.deleted_mass keep old hcapOld hη (by
      convert hcount using 1
      congr 2
      ext t
      simp) hpieces using 1
    congr 1
    ext t
    simp
  have hdshort : (∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ))≤H₀/16 := by
    apply hd.trans
    have hh := mul_le_mul_of_nonneg_right (PlanarParameters.deletion_loss ε D) hH₀.le
    nlinarith
  have hdε : (∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ))≤ε/32*H₀ := by
    exact hd.trans (mul_le_mul_of_nonneg_right (PlanarParameters.unpaired_loss ε D) hH₀.le)
  have hb : ((Finset.univ.filter (fun p=>s.comparisons.pairing.partner p=p)).card:ℝ)+
      ((Finset.univ.filter (fun p=>¬keep p.1 ∧ s.comparisons.pairing.partner p≠p)).card:ℝ)≤ε/16*H₀ := by
    have hnew : ((Finset.univ.filter (fun p=>¬keep p.1 ∧ s.comparisons.pairing.partner p≠p)).card:ℝ)≤
        ∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ) := by
      have hn := LocalizationCounts.deleted_nonfixed_le s.comparisons keep old hprefix
      have hn' : (Finset.univ.filter (fun p=>¬keep p.1 ∧ s.comparisons.pairing.partner p≠p)).card≤
          ∑t∈Finset.univ.filter (fun t=>¬keep t),old t := by
        convert hn using 1 <;> congr 1 <;> ext t <;> simp
      exact_mod_cast hn'
    have ha := mul_le_mul_of_nonneg_right (PlanarParameters.closure_loss ε D ε_pos) hH₀.le
    linarith
  have hcomp : (Fintype.card s.E:ℝ)/2≤(192:ℝ)/(16*L (size rep))*H₀ := by
    have hh : (Fintype.card s.E:ℝ)≤12*Fintype.card s.P := by exact_mod_cast hcompare
    have hLr : (0:ℝ)<L (size rep) := by exact_mod_cast hL
    rw [show (192:ℝ)/(16*L (size rep))*H₀=12*H₀/L (size rep) by ring]
    apply (le_div_iff₀ hLr).mpr
    have hc := mul_le_mul_of_nonneg_right hh hLr.le
    nlinarith
  have hi : ⌈2*(192:ℝ)*(PlanarParameters.K ε D*(PlanarParameters.U ε D+D):ℝ)⌉₊=
      PlanarParameters.sides ε D := by
    rw [show 2*(192:ℝ)*(PlanarParameters.K ε D*(PlanarParameters.U ε D+D):ℝ)=
      (2*192*(PlanarParameters.K ε D*(PlanarParameters.U ε D+D)):ℕ) by push_cast; ring]
    rw [Nat.ceil_natCast]
    rfl
  have havoid' : IsEmpty (BoundedSystem (PlanarParameters.K ε D*(PlanarParameters.U ε D+D))
      (PlanarParameters.K ε D) ⌈2*(192:ℝ)*(PlanarParameters.K ε D*(PlanarParameters.U ε D+D):ℝ)⌉₊ rep r x y) := by
    rw [hi]
    exact havoid
  exact s.excluded_of_local_totals keep (PlanarParameters.K ε D) (PlanarParameters.U ε D+D)
    192 H₀ old ho hH₀ hL (by norm_num) hsize hcap hbase (by
      convert hdshort using 1
      congr 1
      ext t
      simp) (by
      convert hb using 1
      congr 3
      ext t
      simp) hcomp hlong hroot (by
      convert havoid' using 1
      push_cast
      rfl)
end TorsionFreeZeroDivisors.SampleGraph.PathSystem

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
abbrev U₀ : ℕ := PlanarParameters.U PathSystem.ε ClosedWords.D
lemma U₀_ge : 3≤U₀ := PlanarParameters.U_ge _ _
lemma cap_lower {rep : ℕ} (hL : 2≤L (size rep)) : 6≤U₀*L (size rep) := by
  have := U₀_ge
  nlinarith
abbrev cap_positive {rep : ℕ} (hL : 2≤L (size rep)) : 0<U₀*L (size rep) := by
  have := cap_lower hL
  omega
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    {s : PathSystem rep r x y} (a : FullPairing s) (hL : 2≤L (size rep))
    (hd : GraphSample.Diameters rep r)
def prepared : PathSystem rep r x y := a.closed (U₀*L (size rep)) (cap_positive hL) (by omega) hd
/-- Literal full-pairing exclusion. Euler planarity and the one-step separator
are the two remaining geometric inputs, not extra source hypotheses on the
main theorem. No claim of their unconditional existence is made here. -/
theorem excluded (hr : r∈samples rep) (hordinary : ∃t,s.root≠some t) (heuler : a.Euler)
    (oneStep : ∀ S : Finset (a.prepared hL hd).P,PlanarParameters.K PathSystem.ε ClosedWords.D<S.card →
      Nonempty (RecursiveSeparator.Split
        (PairingClusters.Rel (fun p : Position (fun t=>((a.prepared hL hd).paths t).length)=>p.1)
          (a.prepared hL hd).comparisons.pairing.partner) S))
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y)) : False := by
  have hLl : 1≤L (size rep) := by omega
  have hc := cap_positive hL
  have hcp := cap_lower hL
  have hH : 0<(ClosedWords.H₀ s:ℝ) := by
    have hm := ClosedWords.H₀_ge s hr hordinary
    have : 0<ClosedWords.H₀ s := by omega
    exact_mod_cast this
  apply (a.prepared hL hd).excluded_of_separator ClosedWords.D (ClosedWords.H₀ s)
    (BalancedWords.old s.paths (U₀*L (size rep))) hH (by omega)
  · exact ClosedWords.old_le_word s _ hc hLl hd
  · exact BalancedWords.old_le s.paths _ hcp
  · intro t
    change (ClosedWords.word s _ hc hLl hd t).length≤_
    have hh := ClosedWords.word_bound s _ hc hLl hd hcp t
    simpa only [Nat.add_mul] using hh
  · change (ClosedWords.H₀ s:ℝ)≤∑t : ClosedWords.Piece s (U₀*L (size rep)),
      (BalancedWords.old s.paths (U₀*L (size rep)) t:ℝ)
    rw [←Nat.cast_sum,BalancedWords.old_sum s.paths _ hc]
  · have hh := ClosedWords.piece_charge s U₀ U₀_ge hcp hr hordinary
    exact_mod_cast hh
  · change ((Finset.univ.filter (fun p=>(a.closed _ hc hLl hd).comparisons.pairing.partner p=p)).card:ℝ)≤_
    rw [a.closed_fixed,Nat.cast_sum]
    exact ClosedWords.added_real s U₀ U₀_ge hLl hcp hd
  · exact a.closed_old _ hc hLl hd
  · exact a.sides_le _ hc heuler
  · exact ClosedWords.lower_word s U₀ U₀_ge hLl hcp hd hr
  · intro t ht hs
    have hh := ClosedWords.root_mass s U₀ hLl hcp hd hr hordinary t ht hs
    have hh' : 2*((ClosedWords.word s _ hc hLl hd t).length:ℝ)≤ClosedWords.H₀ s := by exact_mod_cast hh
    change ((ClosedWords.word s _ hc hLl hd t).length:ℝ)≤_
    linarith
  · exact oneStep
  · exact havoid
end TorsionFreeZeroDivisors.SampleGraph.FullPairing

namespace TorsionFreeZeroDivisors.PermutationCycles
variable {O B : Type} [Fintype O] (f : Equiv.Perm O)
omit [Fintype O] in
lemma invariant_pow (q : O → B) (hq : ∀x,q (f x)=q x) (n : ℕ) (x : O) :
    q ((f^n) x)=q x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,hq,ih]
def lift (q : O → B) (hq : ∀x,q (f x)=q x) : Cycle f → B :=
  Quotient.lift q (by
    intro x y h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    rw [←hn]
    exact (invariant_pow f q hq n x).symm)
@[simp] lemma lift_cycle (q : O → B) (hq : ∀x,q (f x)=q x) (x : O) :
    lift f q hq (cycle f x)=q x := rfl
lemma lift_surjective (q : O → B) (hq : ∀x,q (f x)=q x) (hs : Function.Surjective q) :
    Function.Surjective (lift f q hq) := by
  intro b
  obtain ⟨x,rfl⟩ := hs b
  exact ⟨cycle f x,rfl⟩
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.InsertedRotation
open scoped Classical
open PermutationCycles
variable {O : Type} (σ α : Equiv.Perm O) (p : O)

def rotation : Equiv.Perm (O⊕Bool) :=
  Equiv.sumCongr σ (Equiv.refl _) * Equiv.swap (.inl p) (.inr true) *
    Equiv.swap (.inl p) (.inr false)
def pairing : Equiv.Perm (O⊕Bool) := Equiv.sumCongr α Equiv.boolNot
def face : Equiv.Perm (O⊕Bool) := pairing α * rotation σ p
lemma rotation_left (i : O) (hi : i≠p) : rotation σ p (.inl i)=.inl (σ i) := by
  simp [rotation,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne,hi]
@[simp] lemma rotation_p : rotation σ p (.inl p)=.inr false := by
  simp [rotation,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
@[simp] lemma rotation_false : rotation σ p (.inr false)=.inr true := by
  simp [rotation,Equiv.Perm.mul_apply]
@[simp] lemma rotation_true : rotation σ p (.inr true)=.inl (σ p) := by
  simp [rotation,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
lemma face_left (i : O) (hi : i≠p) : face σ α p (.inl i)=.inl ((α*σ) i) := by
  simp only [face,Equiv.Perm.mul_apply,rotation_left σ p i hi,pairing,Equiv.sumCongr_apply,Sum.map_inl]
@[simp] lemma face_p : face σ α p (.inl p)=.inr true := by
  simp [face,Equiv.Perm.mul_apply,pairing]
@[simp] lemma face_false : face σ α p (.inr false)=.inr false := by
  simp [face,Equiv.Perm.mul_apply,pairing]
@[simp] lemma face_true : face σ α p (.inr true)=.inl ((α*σ) p) := by
  simp [face,Equiv.Perm.mul_apply,pairing]

def classify : O⊕Bool → Option (Cycle (α*σ))
  | .inl i => some (cycle _ i)
  | .inr false => none
  | .inr true => some (cycle _ p)
lemma classify_invariant (i : O⊕Bool) : classify σ α p (face σ α p i)=classify σ α p i := by
  cases i with
  | inl i =>
    by_cases he : i=p
    · subst i; rw [face_p]; rfl
    · rw [face_left σ α p i he]
      simp only [classify,cycle_apply]
  | inr b => cases b <;> simp only [face_false,face_true,classify,cycle_apply]
lemma classify_surjective : Function.Surjective (classify σ α p) := by
  intro b
  cases b with
  | none => exact ⟨.inr false,rfl⟩
  | some c =>
    obtain ⟨i,rfl⟩ := cycle_surjective (α*σ) c
    exact ⟨.inl i,rfl⟩
variable [Fintype O]
/-- Inserting an ear creates a new face and retains all old face cycles. -/
theorem face_count : Fintype.card (Cycle (α*σ))+1≤Fintype.card (Cycle (face σ α p)) := by
  have h := Fintype.card_le_of_surjective _ (lift_surjective (face σ α p)
    (classify σ α p) (classify_invariant σ α p) (classify_surjective σ α p))
  simpa only [Fintype.card_option] using h

end TorsionFreeZeroDivisors.InsertedRotation

namespace TorsionFreeZeroDivisors.SwapCycles

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)
abbrev Away := {c : Cycle f // c≠cycle f p ∧ c≠cycle f q}
def classify (x : O) : Option (Away f p q) :=
  if h : cycle f x≠cycle f p ∧ cycle f x≠cycle f q then some ⟨cycle f x,h⟩ else none
lemma classify_apply (x : O) : classify f p q (f x)=classify f p q x := by
  simp only [classify,cycle_apply]
@[simp] lemma classify_p : classify f p q p=none := by simp [classify]
@[simp] lemma classify_q : classify f p q q=none := by simp [classify]
lemma classify_swap (x : O) : classify f p q (Equiv.swap p q x)=classify f p q x := by
  by_cases hp : x=p
  · subst x; simp
  · by_cases hq : x=q
    · subst x; simp
    · rw [Equiv.swap_apply_of_ne_of_ne hp hq]
lemma invariant (x : O) : classify f p q ((Equiv.swap p q*f) x)=classify f p q x := by
  rw [Equiv.Perm.mul_apply,classify_swap,classify_apply]
lemma surjective : Function.Surjective (classify f p q) := by
  intro b
  cases b with
  | none => exact ⟨p,classify_p f p q⟩
  | some c =>
    obtain ⟨x,hx⟩ := cycle_surjective f c.val
    refine ⟨x,?_⟩
    have h : cycle f x≠cycle f p ∧ cycle f x≠cycle f q := hx ▸ c.property
    rw [classify,dite_eq_left h]
    exact congrArg some (Subtype.ext hx)
variable [Fintype O]
lemma lower : Fintype.card (Away f p q)+1≤Fintype.card (Cycle (Equiv.swap p q*f)) := by
  have h := Fintype.card_le_of_surjective _ (lift_surjective (Equiv.swap p q*f)
    (classify f p q) (invariant f p q) (surjective f p q))
  simpa only [Fintype.card_option] using h
lemma away_count : Fintype.card (Cycle f)≤Fintype.card (Away f p q)+2 := by
  let rest : Finset (Cycle f) := Finset.univ.filter (fun c=>c≠cycle f p ∧ c≠cycle f q)
  have hs : (Finset.univ : Finset (Cycle f))⊆rest∪{cycle f p,cycle f q} := by
    intro c _
    by_cases h : c≠cycle f p ∧ c≠cycle f q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    · apply Finset.mem_union_right
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
  have h := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hr : rest.card=Fintype.card (Away f p q) := by
    simp [rest,Fintype.card_subtype]
  rw [Finset.card_univ,hr] at h
  exact h.trans (Nat.add_le_add_left (Finset.card_insert_le _ _) _)
/-- A two-endpoint switch loses at most one permutation cycle. -/
theorem count_le : Fintype.card (Cycle f)≤Fintype.card (Cycle (Equiv.swap p q*f))+1 := by
  have h₁ := lower f p q
  have h₂ := away_count f p q
  omega

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)
lemma cycle_swap (h : cycle f p=cycle f q) (x : O) :
    cycle f (Equiv.swap p q x)=cycle f x := by
  by_cases hp : x=p
  · subst x; simpa using h.symm
  · by_cases hq : x=q
    · subst x; simpa using h
    · rw [Equiv.swap_apply_of_ne_of_ne hp hq]

def adjacentClass (x : O) : Option (Cycle f) := if x=p then none else some (cycle f x)
lemma adjacent_fixed : (Equiv.swap p (f p)*f) p=p := by simp
lemma adjacentClass_invariant (x : O) :
    adjacentClass f p ((Equiv.swap p (f p)*f) x)=adjacentClass f p x := by
  by_cases hx : x=p
  · subst x; rw [adjacent_fixed]
  · have hg : (Equiv.swap p (f p)*f) x≠p := by
      intro h
      exact hx ((Equiv.swap p (f p)*f).injective (h.trans (adjacent_fixed f p).symm))
    rw [adjacentClass,ite_eq_right hg,adjacentClass,ite_eq_right hx]
    apply congrArg some
    rw [Equiv.Perm.mul_apply,cycle_swap f p (f p) (cycle_apply f p).symm,cycle_apply]
lemma adjacentClass_surjective (hp : f p≠p) : Function.Surjective (adjacentClass f p) := by
  intro c
  cases c with
  | none => exact ⟨p,by simp [adjacentClass]⟩
  | some c =>
    obtain ⟨x,rfl⟩ := cycle_surjective f c
    by_cases hx : x=p
    · subst x
      exact ⟨f p,by simp [adjacentClass,hp]⟩
    · exact ⟨x,by simp [adjacentClass,hx]⟩

variable [Fintype O]
lemma count_reverse : Fintype.card (Cycle (Equiv.swap p q*f))≤Fintype.card (Cycle f)+1 := by
  simpa only [←mul_assoc,Equiv.swap_mul_self,one_mul] using count_le (Equiv.swap p q*f) p q
/-- Switching the two arrows adjacent to a nonfixed point splits off that point
as one new actual cycle. -/
lemma adjacent_count (hp : f p≠p) :
    Fintype.card (Cycle (Equiv.swap p (f p)*f))=Fintype.card (Cycle f)+1 := by
  have h := Fintype.card_le_of_surjective _ (lift_surjective (Equiv.swap p (f p)*f)
    (adjacentClass f p) (adjacentClass_invariant f p) (adjacentClass_surjective f p hp))
  simp only [Fintype.card_option] at h
  exact Nat.le_antisymm (count_reverse f p (f p)) h
lemma adjacent_support (hp : f p≠p) :
    (Equiv.swap p (f p)*f).support.card<f.support.card := by
  have hs : (Equiv.swap p (f p)*f).support⊆f.support.erase p := by
    intro x hx
    simp only [Finset.mem_erase,Equiv.Perm.mem_support] at *
    refine ⟨?_,?_⟩
    · intro he; subst x; exact hx (adjacent_fixed f p)
    · intro he
      have hxp : x≠p := by intro h; subst x; exact hp he
      have hxf : x≠f p := by
        intro h
        have he' : f x=f p := he.trans h
        exact hxp (f.injective he')
      exact hx (by simp [Equiv.Perm.mul_apply,he,Equiv.swap_apply_of_ne_of_ne hxp hxf])
  exact (Finset.card_le_card hs).trans_lt (Finset.card_erase_lt_of_mem (Equiv.Perm.mem_support.mpr hp))

lemma away_same (h : cycle f p=cycle f q) :
    Fintype.card (Cycle f)≤Fintype.card (Away f p q)+1 := by
  let rest : Finset (Cycle f) := Finset.univ.filter (fun c=>c≠cycle f p ∧ c≠cycle f q)
  have hs : (Finset.univ : Finset (Cycle f))⊆rest∪{cycle f p} := by
    intro c _
    by_cases hc : c=cycle f p
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hc)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,by rwa [←h]⟩)
  have hh := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hr : rest.card=Fintype.card (Away f p q) := by simp [rest,Fintype.card_subtype]
  simpa [hr] using hh
lemma same_monotone (h : cycle f p=cycle f q) :
    Fintype.card (Cycle f)≤Fintype.card (Cycle (Equiv.swap p q*f)) :=
  (away_same f p q h).trans (lower f p q)

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]
lemma identity_count : Fintype.card (Cycle (1 : Equiv.Perm O))=Fintype.card O := by
  apply (Fintype.card_of_bijective (f:=cycle (1 : Equiv.Perm O)) ?_).symm
  refine ⟨?_,cycle_surjective _⟩
  intro x y h
  exact ((cycle_eq _).mp h).eq_of_left rfl
/-- The ordinary permutation sign in terms of all cycles, including fixed points. -/
lemma sign_formula (f : Equiv.Perm O) :
    Equiv.Perm.sign f=(-1 : ℤˣ)^(Fintype.card O+Fintype.card (Cycle f)) := by
  have aux : ∀m,∀g : Equiv.Perm O,g.support.card=m →
      Equiv.Perm.sign g=(-1 : ℤˣ)^(Fintype.card O+Fintype.card (Cycle g)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro g hg
      by_cases he : g=1
      · subst g
        rw [Equiv.Perm.sign_one,identity_count,←two_mul,pow_mul]
        norm_num
      · obtain ⟨p,hp⟩ : ∃p,g p≠p := by
          by_contra! h
          exact he (Equiv.ext h)
        have hsmall := adjacent_support g p hp
        have hh := ih (Equiv.swap p (g p)*g).support.card (hg ▸ hsmall)
          (Equiv.swap p (g p)*g) rfl
        rw [Equiv.Perm.sign_mul,Equiv.Perm.sign_swap hp.symm,adjacent_count g p hp,
          ←Nat.add_assoc,pow_succ,mul_comm] at hh
        exact mul_right_cancel hh
  exact aux f.support.card f rfl

/-- A switch between distinct positions of one cycle splits it in two. -/
theorem split_count (f : Equiv.Perm O) (p q : O) (hpq : p≠q)
    (h : cycle f p=cycle f q) :
    Fintype.card (Cycle (Equiv.swap p q*f))=Fintype.card (Cycle f)+1 := by
  have hlo := same_monotone f p q h
  have hhi := count_reverse f p q
  have hne : Fintype.card (Cycle (Equiv.swap p q*f))≠Fintype.card (Cycle f) := by
    intro he
    have hs : Equiv.Perm.sign (Equiv.swap p q*f)=Equiv.Perm.sign f := by
      rw [sign_formula,sign_formula,he]
    rw [Equiv.Perm.sign_mul,Equiv.Perm.sign_swap hpq] at hs
    have hn : (-1 : ℤˣ)=1 := mul_right_cancel (hs.trans (one_mul _).symm)
    norm_num at hn
  omega

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O)
omit [Fintype O] in
lemma face_switch : α*(Equiv.swap p q*σ)=Equiv.swap (α p) (α q)*(α*σ) := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply]
  exact (α.injective.swap_apply p q (σ x)).symm
/-- The global sphere Euler lower bound is preserved when one boundary cycle
is split at two distinct positions. This finite statement does not identify
which realized component contains the outer disk in a self-band surgery. -/
theorem split_euler (hpq : p≠q) (h : cycle σ p=cycle σ q)
    (he : Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle (α*σ))) :
    Fintype.card O+4≤2*Fintype.card (Cycle (Equiv.swap p q*σ))+
      2*Fintype.card (Cycle (α*(Equiv.swap p q*σ))) := by
  have hv := split_count σ p q hpq h
  have hf := count_le (α*σ) (α p) (α q)
  rw [face_switch,hv]
  omega
end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O) (p q : O)
/-- Switching two distinct cycles joins the two selected positions in one
actual new cycle. The witness follows the old cycle up to its first return. -/
lemma merge_same (h : cycle f p≠cycle f q) :
    (Equiv.swap p q*f).SameCycle p q := by
  have hp : ∃n : ℕ,0<n ∧ (f^n) p=p :=
    ⟨orderOf f,orderOf_pos f,by rw [pow_orderOf_eq_one];rfl⟩
  let n := Nat.find hp
  have hn : 0<n ∧ (f^n) p=p := Nat.find_spec hp
  have hmin : ∀k,0<k → k<n → (f^k) p≠p := by
    intro k hk hkn he
    have hh := Nat.find_min' hp ⟨hk,he⟩
    omega
  have no_q (k : ℕ) : (f^k) p≠q := by
    intro he
    exact h ((cycle_eq f).mpr ⟨(k:ℤ),by simpa only [zpow_natCast] using he⟩)
  have heq : ∀k,k<n → ((Equiv.swap p q*f)^k) p=(f^k) p := by
    intro k
    induction k with
    | zero => intro _;rfl
    | succ k ih =>
      intro hk
      rw [pow_succ',Equiv.Perm.mul_apply,ih (by omega),Equiv.Perm.mul_apply]
      have hf : f ((f^k) p)=(f^(k+1)) p := by rw [pow_succ',Equiv.Perm.mul_apply]
      rw [hf,Equiv.swap_apply_of_ne_of_ne (hmin _ (by omega) hk) (no_q _)]
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  refine ⟨(n:ℤ),?_⟩
  rw [zpow_natCast,hm,pow_succ',Equiv.Perm.mul_apply,heq m (by omega),Equiv.Perm.mul_apply]
  have he : f ((f^m) p)=p := by
    rw [←Equiv.Perm.mul_apply,←pow_succ']
    simpa only [hm, Nat.succ_eq_add_one] using hn.2
  rw [he,Equiv.swap_apply_left]

lemma merge_count (h : cycle f p≠cycle f q) :
    Fintype.card (Cycle (Equiv.swap p q*f))+1=Fintype.card (Cycle f) := by
  have hpq : p≠q := by intro he;exact h (he ▸ rfl)
  have hh := split_count (Equiv.swap p q*f) p q hpq ((cycle_eq _).mpr (merge_same f p q h))
  simpa only [←mul_assoc,Equiv.swap_mul_self,one_mul] using hh.symm
end TorsionFreeZeroDivisors.SwapCycles

namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles SwapCycles
variable {O : Type} [Fintype O]

def Refines (f g : Equiv.Perm O) : Prop := ∀x y,cycle f x=cycle f y → cycle g x=cycle g y
lemma refines_of_invariant (f g : Equiv.Perm O) (h : ∀x,cycle g (f x)=cycle g x) : Refines f g := by
  intro x y hxy
  exact congrArg (lift f (cycle g) h) hxy

lemma merge_refines (f : Equiv.Perm O) (p q : O) (h : cycle f p≠cycle f q) :
    Refines f (Equiv.swap p q*f) := by
  apply refines_of_invariant
  intro x
  have hs : cycle (Equiv.swap p q*f) p=cycle (Equiv.swap p q*f) q :=
    (cycle_eq _).mpr (merge_same f p q h)
  calc
    cycle (Equiv.swap p q*f) (f x)=cycle (Equiv.swap p q*f) (Equiv.swap p q ((Equiv.swap p q*f) x)) := by simp
    _ = cycle (Equiv.swap p q*f) ((Equiv.swap p q*f) x) := cycle_swap _ p q hs _
    _ = cycle (Equiv.swap p q*f) x := cycle_apply _ _

def merge (f : Equiv.Perm O) (p q : O) : Equiv.Perm O :=
  if cycle f p=cycle f q then f else Equiv.swap p q*f
lemma merge_refines' (f : Equiv.Perm O) (p q : O) : Refines f (merge f p q) := by
  by_cases h : cycle f p=cycle f q
  · simp only [merge,ite_eq_left h];exact fun _ _ h=>h
  · simp only [merge,ite_eq_right h];exact merge_refines f p q h
lemma merge_pair (f : Equiv.Perm O) (p q : O) : cycle (merge f p q) p=cycle (merge f p q) q := by
  by_cases h : cycle f p=cycle f q
  · rw [merge,ite_eq_left h]; exact h
  · rw [merge,ite_eq_right h]; exact (cycle_eq _).mpr (merge_same f p q h)

def forest (σ : Equiv.Perm O) : List (O×O) → Equiv.Perm O
  | []=>σ
  | e::l=>merge (forest σ l) e.1 e.2
def face (σ : Equiv.Perm O) : List (O×O) → Equiv.Perm O
  | []=>σ
  | e::l=>Equiv.swap e.1 e.2*face σ l
lemma face_invariant (σ : Equiv.Perm O) (l : List (O×O)) (x : O) :
    cycle (forest σ l) (face σ l x)=cycle (forest σ l) x := by
  induction l with
  | nil=>exact cycle_apply σ x
  | cons e l ih=>
    change cycle (merge (forest σ l) e.1 e.2) (Equiv.swap e.1 e.2 (face σ l x))=_
    rw [cycle_swap _ _ _ (merge_pair _ _ _)]
    exact merge_refines' _ _ _ _ _ ih
lemma face_refines (σ : Equiv.Perm O) (l : List (O×O)) : Refines (face σ l) (forest σ l) :=
  refines_of_invariant _ _ (face_invariant σ l)

/-- Euler's upper bound for the actual component partition formed by gluing
listed bands. The forest permutation is a computed partition, not a planar input. -/
theorem upper (σ : Equiv.Perm O) (l : List (O×O)) :
    Nat.card (Cycle σ)+Nat.card (Cycle (face σ l))≤
      l.length+2*Nat.card (Cycle (forest σ l)) := by
  induction l with
  | nil=>simp only [face,forest,List.length_nil];omega
  | cons e l ih=>
    by_cases h : cycle (forest σ l) e.1=cycle (forest σ l) e.2
    · have hf := count_reverse (face σ l) e.1 e.2
      simp only [face,forest,merge,ite_eq_left h,List.length_cons]
      simp only [←Nat.card_eq_fintype_card] at *
      omega
    · have hc := merge_count (forest σ l) e.1 e.2 h
      have hn : cycle (face σ l) e.1≠cycle (face σ l) e.2 := fun hh=>h (face_refines σ l _ _ hh)
      have hf := merge_count (face σ l) e.1 e.2 hn
      simp only [face,forest,merge,ite_eq_right h,List.length_cons]
      simp only [←Nat.card_eq_fintype_card] at *
      omega
lemma forest_refines (σ : Equiv.Perm O) (l : List (O×O)) : Refines σ (forest σ l) := by
  induction l with
  | nil=>exact fun _ _ h=>h
  | cons e l ih=>exact fun x y h=>merge_refines' (forest σ l) e.1 e.2 x y (ih x y h)
lemma forest_pair (σ : Equiv.Perm O) (l : List (O×O)) (e : O×O) (he : e∈l) :
    cycle (forest σ l) e.1=cycle (forest σ l) e.2 := by
  induction l with
  | nil=>simp at he
  | cons a l ih=>
    rcases List.mem_cons.mp he with rfl|he
    · exact merge_pair _ _ _
    · exact merge_refines' _ _ _ _ _ (ih he)

def Edge (σ : Equiv.Perm O) (l : List (O×O)) (x y : O) : Prop :=
  σ x=y ∨ (x,y)∈l
abbrev Component (σ : Equiv.Perm O) (l : List (O×O)) := Quotient (Relation.EqvGen.setoid (Edge σ l))
def component (σ : Equiv.Perm O) (l : List (O×O)) (x : O) : Component σ l := Quotient.mk _ x
lemma forest_of_component (σ : Equiv.Perm O) (l : List (O×O)) {x y : O}
    (h : component σ l x=component σ l y) : cycle (forest σ l) x=cycle (forest σ l) y := by
  have hxy : Relation.EqvGen (Edge σ l) x y := Quotient.exact h
  clear h
  induction hxy with
  | rel x y h=>
    rcases h with h|h
    · exact forest_refines σ l x y (by rw [←h,cycle_apply])
    · exact forest_pair σ l (x,y) h
  | refl=>rfl
  | symm _ _ _ ih=>exact ih.symm
  | trans _ _ _ _ _ ih ih'=>exact ih.trans ih'

omit [Fintype O] in
lemma invariant_forest {B : Type} (σ : Equiv.Perm O) (l : List (O×O)) (q : O→B)
    (hσ : ∀x,q (σ x)=q x) (hl : ∀e∈l,q e.1=q e.2) : ∀x,q (forest σ l x)=q x := by
  induction l with
  | nil=>exact hσ
  | cons e l ih=>
    have he := hl e (List.mem_cons_self)
    have hi := ih (fun a ha=>hl a (List.mem_cons_of_mem _ ha))
    intro x
    change q (merge (forest σ l) e.1 e.2 x)=q x
    dsimp only [merge]
    split
    · exact hi x
    · change q (Equiv.swap e.1 e.2 (forest σ l x))=q x
      have hs : ∀z,q (Equiv.swap e.1 e.2 z)=q z := by
        intro z
        by_cases hz : z=e.1
        · subst z;rw [Equiv.swap_apply_left];exact he.symm
        · by_cases hz' : z=e.2
          · subst z;rw [Equiv.swap_apply_right];exact he
          · rw [Equiv.swap_apply_of_ne_of_ne hz hz']
      rw [hs,hi]
omit [Fintype O] in
lemma component_invariant (σ : Equiv.Perm O) (l : List (O×O)) (x : O) :
    component σ l (forest σ l x)=component σ l x := by
  apply invariant_forest σ l
  · intro y
    exact Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)))
  · intro e he
    exact Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr (by simpa using he)))
lemma component_of_forest (σ : Equiv.Perm O) (l : List (O×O)) {x y : O}
    (h : cycle (forest σ l) x=cycle (forest σ l) y) : component σ l x=component σ l y :=
  congrArg (lift (forest σ l) (component σ l) (component_invariant σ l)) h

def componentEquiv (σ : Equiv.Perm O) (l : List (O×O)) : Cycle (forest σ l) ≃ Component σ l :=
  Equiv.ofBijective (lift (forest σ l) (component σ l) (component_invariant σ l)) ⟨by
    intro a b he
    obtain ⟨x,rfl⟩ := cycle_surjective (forest σ l) a
    obtain ⟨y,rfl⟩ := cycle_surjective (forest σ l) b
    exact forest_of_component σ l he,
    lift_surjective _ _ _ Quotient.mk_surjective⟩
lemma upper_components (σ : Equiv.Perm O) (l : List (O×O)) :
    Nat.card (Cycle σ)+Nat.card (Cycle (face σ l))≤l.length+2*Nat.card (Component σ l) := by
  have h := upper σ l
  rw [Nat.card_congr (componentEquiv σ l)] at h
  exact h
lemma connected_upper (σ : Equiv.Perm O) (l : List (O×O))
    (hc : ∀x y,Relation.EqvGen (Edge σ l) x y) :
    Nat.card (Cycle σ)+Nat.card (Cycle (face σ l))≤l.length+2 := by
  let : Subsingleton (Component σ l) := ⟨by
    intro a b
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective a
    obtain ⟨y,rfl⟩ := Quotient.mk_surjective b
    exact Quotient.sound (hc x y)⟩
  have hh : Nat.card (Component σ l)≤1 := (Finite.card_le_one_iff_subsingleton).mpr inferInstance
  have := upper_components σ l
  omega
end TorsionFreeZeroDivisors.ComponentEuler

namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
def strip : Equiv.Perm O := Equiv.swap p (α p)*α
omit [Fintype O] in
lemma strip_p : strip α p p=p := by simp [strip]
omit [Fintype O] in
include hi in
lemma strip_q : strip α p (α p)=α p := by simp only [strip,Equiv.Perm.mul_apply,hi p,Equiv.swap_apply_left]
omit [Fintype O] in
include hi in
lemma strip_away (x : O) (hp : x≠p) (hq : x≠α p) : strip α p x=α x := by
  have hxp : α x≠p := by intro h;exact hq ((hi x).symm.trans (congrArg α h))
  have hxq : α x≠α p := α.injective.ne hp
  exact Equiv.swap_apply_of_ne_of_ne hxp hxq
omit [Fintype O] in
include hi in
lemma strip_involutive : Function.Involutive (strip α p) := by
  intro x
  by_cases hp : x=p
  · subst x;rw [strip_p,strip_p]
  · by_cases hq : x=α p
    · subst x;rw [strip_q α hi p,strip_q α hi p]
    · rw [strip_away α hi p x hp hq,strip_away α hi p (α x)]
      · exact hi x
      · intro h;exact hq ((hi x).symm.trans (congrArg α h))
      · exact α.injective.ne hp
include hi in
lemma strip_support : (strip α p).support=α.support\{p,α p} := by
  ext x
  simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,not_or,Equiv.Perm.mem_support]
  constructor
  · intro h
    have hp : x≠p := by intro he;subst x;exact h (strip_p α p)
    have hq : x≠α p := by intro he;subst x;exact h (strip_q α hi p)
    exact ⟨by rwa [strip_away α hi p x hp hq] at h,hp,hq⟩
  · rintro ⟨h,hp,hq⟩
    rwa [strip_away α hi p x hp hq]
include hi in
lemma strip_card (hp : α p≠p) : (strip α p).support.card+2=α.support.card := by
  rw [strip_support α hi p,Finset.card_sdiff_of_subset]
  · have hc : ({p,α p} : Finset O).card=2 := by simp [Ne.symm hp]
    have hs : {p,α p}⊆α.support := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact Equiv.Perm.mem_support.mpr hp
      · exact Equiv.Perm.mem_support.mpr (by rw [hi];exact Ne.symm hp)
    have hh := Finset.card_le_card hs
    rw [hc] at *
    omega
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact Equiv.Perm.mem_support.mpr hp
    · exact Equiv.Perm.mem_support.mpr (by rw [hi];exact Ne.symm hp)

include hi in
/-- Every finite involution is literally a product of its own nontrivial
paired-edge swaps, with exactly one factor for each pair. -/
theorem factorization : ∃l : List (O×O),
    (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α ∧
      2*l.length=α.support.card ∧ ∀e∈l,e.1≠e.2 ∧ α e.1=e.2 := by
  generalize hn : α.support.card=n
  induction n using Nat.strong_induction_on generalizing α with
  | h n ih=>
    by_cases hn0 : n=0
    · have hs : α.support=∅ := Finset.card_eq_zero.mp (hn.trans hn0)
      have ha : α=1 := Equiv.Perm.support_eq_empty_iff.mp hs
      refine ⟨[],?_,by simp [←hn,hs],by simp⟩
      simpa using ha.symm
    · obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<α.support.card)
      have hp' := Equiv.Perm.mem_support.mp hp
      have hc := strip_card α hi p hp'
      obtain ⟨l,hl,hL,hedge⟩ := ih (strip α p).support.card (by omega)
        (strip α p) (strip_involutive α hi p) rfl
      refine ⟨(p,α p)::l,?_,?_,?_⟩
      · simp only [List.map_cons,List.prod_cons,hl,strip]
        rw [←mul_assoc,Equiv.swap_mul_self,one_mul]
      · simp only [List.length_cons]
        omega
      · intro e he
        rcases List.mem_cons.mp he with rfl|he
        · exact ⟨Ne.symm hp',rfl⟩
        · obtain ⟨hne,heq⟩ := hedge e he
          have hep : e.1≠p := by
            intro hh
            have hy : e.2=p := (heq.symm.trans (congrArg (strip α p) hh)).trans (strip_p α p)
            exact hne (hh.trans hy.symm)
          have heq' : e.1≠α p := by
            intro hh
            have hy : e.2=α p := (heq.symm.trans (congrArg (strip α p) hh)).trans (strip_q α hi p)
            exact hne (hh.trans hy.symm)
          exact ⟨hne,(strip_away α hi p e.1 hep heq').symm.trans heq⟩
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O]
omit [Fintype O] in
lemma product_invariant {B : Type} (l : List (O×O)) (q : O→B)
    (hl : ∀e∈l,q e.1=q e.2) (x : O) :
    q ((l.map (fun e=>Equiv.swap e.1 e.2)).prod x)=q x := by
  induction l with
  | nil=>rfl
  | cons e l ih=>
    have he := hl e List.mem_cons_self
    have hi := ih (fun a ha=>hl a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    have hs : ∀z,q (Equiv.swap e.1 e.2 z)=q z := by
      intro z
      by_cases hz : z=e.1
      · subst z;rw [Equiv.swap_apply_left];exact he.symm
      · by_cases hz' : z=e.2
        · subst z;rw [Equiv.swap_apply_right];exact he
        · rw [Equiv.swap_apply_of_ne_of_ne hz hz']
    rw [hs,hi]
omit [Fintype O] in
lemma face_product (σ : Equiv.Perm O) (l : List (O×O)) :
    face σ l=(l.map (fun e=>Equiv.swap e.1 e.2)).prod*σ := by
  induction l with
  | nil=>simp [face]
  | cons e l ih=>simp only [face,List.map_cons,List.prod_cons,ih,mul_assoc]

def Edge (σ α : Equiv.Perm O) (x y : O) : Prop := σ x=y ∨ α x=y
abbrev Component (σ α : Equiv.Perm O) := Quotient (Relation.EqvGen.setoid (Edge σ α))
def component (σ α : Equiv.Perm O) (x : O) : Component σ α := Quotient.mk _ x
variable (σ α : Equiv.Perm O) (l : List (O×O))
    (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
    (he : ∀e∈l,α e.1=e.2)
omit [Fintype O] in
include he in
lemma component_forest (x : O) : component σ α (forest σ l x)=component σ α x := by
  apply invariant_forest σ l
  · intro y
    exact Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)))
  · intro e h
    exact Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr (he e h)))
include hl in
lemma forest_alpha (x : O) : cycle (forest σ l) (α x)=cycle (forest σ l) x := by
  rw [←hl]
  exact product_invariant l (cycle (forest σ l)) (forest_pair σ l) x
include hl in
lemma forest_component {x y : O} (h : component σ α x=component σ α y) :
    cycle (forest σ l) x=cycle (forest σ l) y := by
  have hxy : Relation.EqvGen (Edge σ α) x y := Quotient.exact h
  clear h
  induction hxy with
  | rel x y h=>
    rcases h with h|h
    · exact forest_refines σ l x y (by rw [←h,cycle_apply])
    · rw [←h,forest_alpha σ α l hl]
  | refl=>rfl
  | symm _ _ _ ih=>exact ih.symm
  | trans _ _ _ _ _ ih ih'=>exact ih.trans ih'

def componentEquiv : Cycle (forest σ l) ≃ Component σ α :=
  Equiv.ofBijective (lift (forest σ l) (component σ α) (component_forest σ α l he)) ⟨by
    intro a b hh
    obtain ⟨x,rfl⟩ := cycle_surjective (forest σ l) a
    obtain ⟨y,rfl⟩ := cycle_surjective (forest σ l) b
    exact forest_component σ α l hl hh,
    lift_surjective _ _ _ Quotient.mk_surjective⟩
include hl he in
lemma upper_factors : Nat.card (Cycle σ)+Nat.card (Cycle (α*σ))≤l.length+2*Nat.card (Component σ α) := by
  have hh := upper σ l
  rw [face_product,hl,Nat.card_congr (componentEquiv σ α l hl he)] at hh
  exact hh

/-- Every finite orientable permutation map obeys the Euler upper bound. This
uses only its actual involution and actual connected-component equivalence;
no topological realization or Euler inequality is assumed. -/
theorem upper (hi : Function.Involutive α) :
    2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))≤α.support.card+4*Nat.card (Component σ α) := by
  obtain ⟨l,hl,hL,he⟩ := PairingFactors.factorization α hi
  have hh := upper_factors σ α l hl (fun e h=>(he e h).2)
  omega
lemma fixedFree_upper (hi : Function.Involutive α) (hf : ∀x,α x≠x) :
    2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))≤Nat.card O+4*Nat.card (Component σ α) := by
  have hs : α.support=Finset.univ := by ext x;simp [Equiv.Perm.mem_support,hf]
  have hh := upper σ α hi
  simpa only [hs,Finset.card_univ,←Nat.card_eq_fintype_card] using hh
lemma connected_upper (hi : Function.Involutive α) (hf : ∀x,α x≠x)
    (hc : ∀x y,Relation.EqvGen (Edge σ α) x y) :
    2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))≤Nat.card O+4 := by
  let : Subsingleton (Component σ α) := ⟨by
    intro a b
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective a
    obtain ⟨y,rfl⟩ := Quotient.mk_surjective b
    exact Quotient.sound (hc x y)⟩
  have hh : Nat.card (Component σ α)≤1 := Finite.card_le_one_iff_subsingleton.mpr inferInstance
  have := fixedFree_upper σ α hi hf
  omega
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles SwapCycles
variable {O : Type} [Fintype O]
/-- A handle is precisely an edge whose endpoints are already in one component
but which merges two distinct face cycles when glued. -/
def handles (σ : Equiv.Perm O) : List (O×O) → ℕ
  | []=>0
  | e::l=>handles σ l+if cycle (forest σ l) e.1=cycle (forest σ l) e.2 ∧
      cycle (face σ l) e.1≠cycle (face σ l) e.2 then 1 else 0
omit [Fintype O] in
lemma handles_tail (σ : Equiv.Perm O) (e : O×O) (l : List (O×O)) : handles σ l≤handles σ (e::l) := by
  simp only [handles];omega
lemma handles_exact (σ : Equiv.Perm O) (l : List (O×O)) (hd : ∀e∈l,e.1≠e.2) :
    Nat.card (Cycle σ)+Nat.card (Cycle (face σ l))+2*handles σ l=
      l.length+2*Nat.card (Cycle (forest σ l)) := by
  induction l with
  | nil=>simp only [face,forest,handles,List.length_nil];omega
  | cons e l ih=>
    have he := hd e List.mem_cons_self
    have hh := ih (fun a ha=>hd a (List.mem_cons_of_mem _ ha))
    by_cases hc : cycle (forest σ l) e.1=cycle (forest σ l) e.2
    · by_cases hf : cycle (face σ l) e.1=cycle (face σ l) e.2
      · have hg := split_count (face σ l) e.1 e.2 he hf
        simp only [←Nat.card_eq_fintype_card] at hg
        have hn : ¬(cycle (forest σ l) e.1=cycle (forest σ l) e.2 ∧
            cycle (face σ l) e.1≠cycle (face σ l) e.2) := fun h=>h.2 hf
        simp only [face,forest,merge,ite_eq_left hc,handles,ite_eq_right hn,List.length_cons]
        omega
      · have hg := merge_count (face σ l) e.1 e.2 hf
        simp only [←Nat.card_eq_fintype_card] at hg
        simp only [face,forest,merge,ite_eq_left hc,handles,ite_eq_left (And.intro hc hf),List.length_cons]
        omega
    · have hn : cycle (face σ l) e.1≠cycle (face σ l) e.2 := fun hh=>hc (face_refines σ l _ _ hh)
      have hg := merge_count (face σ l) e.1 e.2 hn
      have hj := merge_count (forest σ l) e.1 e.2 hc
      simp only [←Nat.card_eq_fintype_card] at hg hj
      have hn' : ¬(cycle (forest σ l) e.1=cycle (forest σ l) e.2 ∧
          cycle (face σ l) e.1≠cycle (face σ l) e.2) := fun h=>hc h.1
      simp only [face,forest,merge,ite_eq_right hc,handles,ite_eq_right hn',List.length_cons]
      omega
lemma zero_handles (σ : Equiv.Perm O) (l : List (O×O)) (hd : ∀e∈l,e.1≠e.2)
    (he : l.length+2*Nat.card (Component σ l)≤Nat.card (Cycle σ)+Nat.card (Cycle (face σ l))) :
    handles σ l=0 := by
  have hh := handles_exact σ l hd
  rw [Nat.card_congr (componentEquiv σ l)] at hh
  omega
end TorsionFreeZeroDivisors.ComponentEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
/-- Combinatorial genus zero, including disconnected maps and isolated darts.
This is a definition in permutation data, not an asserted sphere embedding. -/
def GenusZero : Prop :=
  2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))=α.support.card+4*Nat.card (Component σ α)
lemma genusZero_of_lower (hi : Function.Involutive α)
    (h : α.support.card+4*Nat.card (Component σ α)≤2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))) :
    GenusZero σ α := Nat.le_antisymm h (upper σ α hi) |>.symm
lemma genusZero_iff_handles (l : List (O×O))
    (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
    (hd : ∀e∈l,e.1≠e.2 ∧ α e.1=e.2) (hL : 2*l.length=α.support.card) :
    GenusZero σ α ↔ handles σ l=0 := by
  have hh := handles_exact σ l (fun e he=>(hd e he).1)
  rw [face_product,hl,Nat.card_congr (componentEquiv σ α l hl (fun e he=>(hd e he).2))] at hh
  dsimp only [GenusZero]
  omega
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
include hi in
lemma strip_edge {x y : O} (hne : x≠y) (he : strip α p x=y) : α x=y := by
  have hxp : x≠p := by
    intro hx
    have hy : y=p := (he.symm.trans (congrArg (strip α p) hx)).trans (strip_p α p)
    exact hne (hx.trans hy.symm)
  have hxq : x≠α p := by
    intro hx
    have hy : y=α p := (he.symm.trans (congrArg (strip α p) hx)).trans (strip_q α hi p)
    exact hne (hx.trans hy.symm)
  exact (strip_away α hi p x hxp hxq).symm.trans he
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler PairingFactors
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
include hi in
/-- Deleting an actual paired edge cannot create a handle in any component. -/
lemma genusZero_strip (hz : GenusZero σ α) (p : O) (hp : α p≠p) : GenusZero σ (strip α p) := by
  obtain ⟨l,hl,hL,he⟩ := factorization (strip α p) (strip_involutive α hi p)
  have he' : ∀e∈(p,α p)::l,e.1≠e.2 ∧ α e.1=e.2 := by
    intro e hm
    rcases List.mem_cons.mp hm with rfl|hm
    · exact ⟨Ne.symm hp,rfl⟩
    · exact ⟨(he e hm).1,strip_edge α hi p (he e hm).1 (he e hm).2⟩
  have hl' : (((p,α p)::l).map (fun e=>Equiv.swap e.1 e.2)).prod=α := by
    simp only [List.map_cons,List.prod_cons,hl,strip]
    rw [←mul_assoc,Equiv.swap_mul_self,one_mul]
  have hL' : 2*((p,α p)::l).length=α.support.card := by
    have hc := strip_card α hi p hp
    simp only [List.length_cons]
    omega
  have hh := (genusZero_iff_handles σ α ((p,α p)::l) hl' he' hL').mp hz
  have ht : handles σ l=0 := Nat.eq_zero_of_le_zero ((handles_tail σ (p,α p) l).trans_eq hh)
  exact (genusZero_iff_handles σ (strip α p) l hl he hL).mpr ht
omit [Fintype O] in
include hi in
lemma dual_rel {x y : O} (h : Relation.EqvGen (Edge σ α) x y) :
    Relation.EqvGen (Edge (α*σ) α) x y := by
  induction h with
  | rel x y h=>
    rcases h with hs|ha
    · exact Relation.EqvGen.trans x ((α*σ) x) y
        (Relation.EqvGen.rel _ _ (Or.inl rfl))
        (Relation.EqvGen.rel _ _ (Or.inr (by rw [Equiv.Perm.mul_apply,hi];exact hs)))
    · exact Relation.EqvGen.rel _ _ (Or.inr ha)
  | refl=>exact Relation.EqvGen.refl _
  | symm _ _ _ ih=>exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ih'=>exact Relation.EqvGen.trans _ _ _ ih ih'
omit [Fintype O] in
include hi in
lemma dual_twice : α*(α*σ)=σ := by
  ext x
  exact hi (σ x)
def dualEquiv : Component σ α ≃ Component (α*σ) α := Quotient.congrRight (fun x y=>⟨
  dual_rel σ α hi,fun h=>by
    have hh := dual_rel (α*σ) α hi h
    rwa [dual_twice σ α hi] at hh⟩)
include hi in
lemma genusZero_dual : GenusZero σ α ↔ GenusZero (α*σ) α := by
  have hc := Nat.card_congr (dualEquiv σ α hi)
  simp only [GenusZero,dual_twice σ α hi]
  omega
include hi in
/-- The actual band splice preserves componentwise combinatorial genus zero,
prior to bypassing its two now-unpaired occurrences. Both the merge and the
split vertex cases are covered by dual edge deletion. -/
theorem genusZero_band (hz : GenusZero σ α) (p : O) (hp : α p≠p) :
    GenusZero (Equiv.swap p (α p)*σ) (strip α p) := by
  have hd := (genusZero_dual σ α hi).mp hz
  have hs := genusZero_strip (α*σ) α hi hd p hp
  have hh := (genusZero_dual (α*σ) (strip α p) (strip_involutive α hi p)).mp hs
  have he : strip α p*(α*σ)=Equiv.swap p (α p)*σ := by
    rw [strip,mul_assoc,dual_twice σ α hi]
  rwa [he] at hh
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.DeleteCycle

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
abbrev Rest := {x : O // x ≠ p}
lemma invariant (h : f p=p) (x : O) : f x ≠ p ↔ x ≠ p := by
  constructor
  · intro hx he; exact hx (he ▸ h)
  · intro hx he; exact hx (f.injective (he.trans h.symm))
def restrict (h : f p=p) : Equiv.Perm (Rest p) := f.subtypePerm (invariant f p h)
lemma restrict_pow (h : f p=p) (x : Rest p) (k : ℕ) :
    ((restrict f p h ^ k) x).val=(f^k) x := by
  simp only [restrict,Equiv.Perm.subtypePerm_pow,Equiv.Perm.subtypePerm_apply]
variable [Fintype O]
lemma restrict_same (h : f p=p) (x y : Rest p) :
    (restrict f p h).SameCycle x y ↔ f.SameCycle x y := by
  constructor
  · intro hs
    obtain ⟨k,hk⟩ := hs.exists_nat_pow_eq
    refine ⟨(k:ℤ),?_⟩
    rw [zpow_natCast]
    exact (restrict_pow f p h x k).symm.trans (congrArg Subtype.val hk)
  · intro hs
    obtain ⟨k,hk⟩ := hs.exists_nat_pow_eq
    refine ⟨(k:ℤ),?_⟩
    rw [zpow_natCast]
    apply Subtype.ext
    exact (restrict_pow f p h x k).trans hk

def classify (h : f p=p) (x : O) : Option (Cycle (restrict f p h)) :=
  if hx : x=p then none else some (cycle (restrict f p h) ⟨x,hx⟩)
omit [Fintype O] in
lemma classify_apply (h : f p=p) (x : O) : classify f p h (f x)=classify f p h x := by
  by_cases hx : x=p
  · subst x; rw [h]
  · have hfx := (invariant f p h x).mpr hx
    rw [classify,dite_eq_right hfx,classify,dite_eq_right hx]
    apply congrArg some
    exact cycle_apply (restrict f p h) ⟨x,hx⟩
omit [Fintype O] in
lemma classify_surjective (h : f p=p) : Function.Surjective (classify f p h) := by
  intro c
  cases c with
  | none => exact ⟨p,by simp [classify]⟩
  | some c =>
    obtain ⟨x,rfl⟩ := cycle_surjective (restrict f p h) c
    exact ⟨x,by simp [classify,x.property]⟩
lemma classify_eq (h : f p=p) {x y : O} (he : classify f p h x=classify f p h y) : f.SameCycle x y := by
  by_cases hx : x=p
  · subst x
    have hy : y=p := by
      by_contra hy
      simp [classify,hy] at he
    subst y
    exact Equiv.Perm.SameCycle.refl _ _
  · by_cases hy : y=p
    · subst y; simp [classify,hx] at he
    · simp only [classify,dite_eq_right hx,dite_eq_right hy,Option.some.injEq] at he
      exact (restrict_same f p h ⟨x,hx⟩ ⟨y,hy⟩).mp ((cycle_eq _).mp he)
def cycleEquiv (h : f p=p) : Cycle f ≃ Option (Cycle (restrict f p h)) :=
  Equiv.ofBijective (lift f (classify f p h) (classify_apply f p h)) ⟨by
    intro c d he
    obtain ⟨x,rfl⟩ := cycle_surjective f c
    obtain ⟨y,rfl⟩ := cycle_surjective f d
    exact (cycle_eq f).mpr (classify_eq f p h he),
    lift_surjective f _ _ (classify_surjective f p h)⟩
lemma fixed_count (h : f p=p) :
    Fintype.card (Cycle f)=Fintype.card (Cycle (restrict f p h))+1 := by
  simpa only [Fintype.card_option] using Fintype.card_congr (cycleEquiv f p h)

/-- Delete an occurrence by bypassing it in its boundary cycle. -/
def bypass : Equiv.Perm (Rest p) := restrict (Equiv.swap p (f p)*f) p (SwapCycles.adjacent_fixed f p)
lemma bypass_count (h : f p≠p) : Fintype.card (Cycle (bypass f p))=Fintype.card (Cycle f) := by
  have h₁ := fixed_count (Equiv.swap p (f p)*f) p (SwapCycles.adjacent_fixed f p)
  have h₂ := SwapCycles.adjacent_count f p h
  change _=Fintype.card (Cycle (bypass f p))+1 at h₁
  omega
end
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
lemma bypass_apply [Fintype O] (x : Rest p) :
    (bypass f p x).val=Equiv.swap p (f p) (f x) := rfl
/-- Bypassing a point commutes with a left permutation fixing that point. -/
lemma bypass_mul [Fintype O] (a : Equiv.Perm O) (ha : a p=p) :
    bypass (a*f) p=restrict a p ha*bypass f p := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change Equiv.swap p (a (f p)) (a (f x))=a (Equiv.swap p (f p) (f x))
  simpa only [ha] using (a.injective.swap_apply p (f p) (f x))
lemma bypass_nonfixed [Fintype O] (q : Rest p) (hq : f q≠q)
    (hshort : f q=p → f p≠q) : bypass f p q≠q := by
  intro he
  have he := congrArg Subtype.val he
  rw [bypass_apply] at he
  by_cases h : f q=p
  · rw [h,Equiv.swap_apply_left] at he
    exact hshort h he
  · have hh : f q≠f p := fun he=>q.property (f.injective he)
    rw [Equiv.swap_apply_of_ne_of_ne h hh] at he
    exact hq he
variable [Fintype O]
lemma card_rest : Fintype.card (Rest p)+1=Fintype.card O := by
  have h := Fintype.card_subtype_compl (fun x : O=>x=p)
  have he : Fintype.card {x : O // x=p}=1 := Fintype.card_unique
  change Fintype.card (Rest p)=_ at h
  rw [he] at h
  have hn : 0<Fintype.card O := Fintype.card_pos_iff.mpr ⟨p⟩
  omega
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
variable {O B : Type} (σ α : Equiv.Perm O)
lemma component_rotation (x : O) : component σ α (σ x)=component σ α x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)))
lemma component_partner (x : O) : component σ α (α x)=component σ α x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl)))
def lift (q : O→B) (hσ : ∀x,q (σ x)=q x) (hα : ∀x,q (α x)=q x) : Component σ α →B :=
  Quotient.lift q (by
    intro x y h
    induction h with
    | rel x y h=>
      rcases h with h|h
      · exact (hσ x).symm.trans (congrArg q h)
      · exact (hα x).symm.trans (congrArg q h)
    | refl=>rfl
    | symm _ _ _ ih=>exact ih.symm
    | trans _ _ _ _ _ ih ih'=>exact ih.trans ih')
@[simp] lemma lift_component (q : O→B) (hσ : ∀x,q (σ x)=q x) (hα : ∀x,q (α x)=q x) (x : O) :
    lift σ α q hσ hα (component σ α x)=q x := rfl
lemma swap_invariant (q : O→B) (p r : O) (h : q p=q r) (x : O) : q (Equiv.swap p r x)=q x := by
  by_cases hp : x=p
  · subst x;rw [Equiv.swap_apply_left];exact h.symm
  · by_cases hr : x=r
    · subst x;rw [Equiv.swap_apply_right];exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hp hr]
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.MapDeletion

section
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p) (hs : σ p≠p)
abbrev rotation := bypass σ p
abbrev partner := restrict α p ha
def push (x : O) : Rest p := if hx : x=p then ⟨σ p,hs⟩ else ⟨x,hx⟩
omit [Fintype O] in
lemma push_p : push σ p hs p=⟨σ p,hs⟩ := by simp [push]
omit [Fintype O] in
lemma push_val (x : Rest p) : push σ p hs x=x := by simp [push,x.property]
lemma push_rotation (x : Rest p) : push σ p hs (σ x)=rotation σ p x := by
  apply Subtype.ext
  rw [bypass_apply]
  by_cases h : σ x=p
  · simp only [push,h,dite_eq_left trivial,Equiv.swap_apply_left]
  · have hn : σ x≠σ p := σ.injective.ne x.property
    simp only [push,dite_eq_right h,Equiv.swap_apply_of_ne_of_ne h hn]
def projectRaw (x : O) : MapEuler.Component (rotation σ p) (partner α p ha) :=
  component (rotation σ p) (partner α p ha) (push σ p hs x)
lemma project_rotation (x : O) : projectRaw σ α p ha hs (σ x)=projectRaw σ α p ha hs x := by
  by_cases hx : x=p
  · subst x
    change component _ _ (push σ p hs (σ p))=component _ _ (push σ p hs p)
    rw [push_p]
    simp only [push,dite_eq_right hs]
  · change component _ _ (push σ p hs (σ (⟨x,hx⟩ : Rest p)))=_
    rw [push_rotation]
    change component _ _ (rotation σ p ⟨x,hx⟩)=component _ _ (push σ p hs (⟨x,hx⟩ : Rest p))
    rw [push_val,component_rotation]
omit [Fintype O] in
lemma project_partner (x : O) : projectRaw σ α p ha hs (α x)=projectRaw σ α p ha hs x := by
  by_cases hx : x=p
  · subst x;rw [ha]
  · have hn : α x≠p := (DeleteCycle.invariant α p ha x).mpr hx
    change component _ _ (push σ p hs (α x))=component _ _ (push σ p hs x)
    simp only [push,dite_eq_right hx,dite_eq_right hn]
    exact component_partner (rotation σ p) (partner α p ha) ⟨x,hx⟩
def project : MapEuler.Component σ α → MapEuler.Component (rotation σ p) (partner α p ha) :=
  MapEuler.lift σ α (projectRaw σ α p ha hs) (project_rotation σ α p ha hs) (project_partner σ α p ha hs)
lemma include_rotation (x : Rest p) : component σ α (rotation σ p x)=component σ α x := by
  rw [bypass_apply,MapEuler.swap_invariant (component σ α) p (σ p) (component_rotation σ α p).symm]
  exact component_rotation σ α x
omit [Fintype O] in
lemma include_partner (x : Rest p) : component σ α (partner α p ha x)=component σ α x :=
  component_partner σ α x
def inclusion : MapEuler.Component (rotation σ p) (partner α p ha) → MapEuler.Component σ α :=
  MapEuler.lift _ _ (fun x : Rest p=>component σ α x) (include_rotation σ α p) (include_partner σ α p ha)
omit [Fintype O] in
lemma component_push (x : O) : component σ α (push σ p hs x)=component σ α x := by
  by_cases hx : x=p
  · subst x;rw [push_p];exact component_rotation σ α p
  · simp only [push,dite_eq_right hx]
lemma left_inverse : Function.LeftInverse (inclusion σ α p ha) (project σ α p ha hs) := by
  intro c
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
  exact component_push σ α p hs x
lemma project_surjective : Function.Surjective (project σ α p ha hs) := by
  intro c
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
  refine ⟨component σ α x,?_⟩
  change component _ _ (push σ p hs x)=component _ _ x
  rw [push_val]
def componentEquiv : MapEuler.Component σ α ≃ MapEuler.Component (rotation σ p) (partner α p ha) :=
  Equiv.ofBijective (project σ α p ha hs) ⟨(left_inverse σ α p ha hs).injective,project_surjective σ α p ha hs⟩
end
open scoped Classical
open DeleteCycle MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
def support_equiv : ↥(partner α p ha).support ≃ ↥α.support where
  toFun x := ⟨x.val.val,by
    have h := Equiv.Perm.mem_support.mp x.property
    exact Equiv.Perm.mem_support.mpr (fun he=>h (Subtype.ext he))⟩
  invFun x := ⟨⟨x.val,by
    intro he
    have hn := Equiv.Perm.mem_support.mp x.property
    exact hn (he ▸ ha)⟩,by
      apply Equiv.Perm.mem_support.mpr
      intro he
      exact Equiv.Perm.mem_support.mp x.property (congrArg Subtype.val he)⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
lemma support_count : (partner α p ha).support.card=α.support.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (support_equiv α p ha)
omit [Fintype O] in
include ha in
lemma face_nonfixed (hs : σ p≠p) : (α*σ) p≠p := by
  intro he
  exact hs (α.injective ((show α (σ p)=p from he).trans ha.symm))
/-- Removing a dart fixed by the partner involution preserves all actual map
components and the Euler equality when its vertex is not a singleton. -/
theorem genusZero_delete (hs : σ p≠p) (hz : GenusZero σ α) :
    GenusZero (rotation σ p) (partner α p ha) := by
  have hv := bypass_count σ p hs
  have hf := bypass_count (α*σ) p (face_nonfixed σ α p ha hs)
  rw [bypass_mul σ p α ha] at hf
  have hc := Nat.card_congr (componentEquiv σ α p ha hs)
  have he := support_count α p ha
  simp only [←Nat.card_eq_fintype_card] at hv hf
  dsimp only [GenusZero] at hz ⊢
  change Nat.card (Cycle (rotation σ p))=Nat.card (Cycle σ) at hv
  change Nat.card (Cycle (partner α p ha*rotation σ p))=Nat.card (Cycle (α*σ)) at hf
  rw [hv,hf,←hc]
  have hsup : ∀ (i j : Fintype (Rest p)) (d e : DecidableEq (Rest p)),
      @Equiv.Perm.support (Rest p) d i (partner α p ha) =
      @Equiv.Perm.support (Rest p) e j (partner α p ha) := by
    intro i j d e
    cases Subsingleton.elim i j
    cases Subsingleton.elim d e
    rfl
  convert hz using 1
  rw [←he]
  congr 1
  exact congrArg Finset.card (hsup _ _ _ _)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open PermutationCycles DeleteCycle
variable {O A : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
abbrev q' : Rest p := ⟨q,hpq.symm⟩
abbrev Residual := Rest (q' p q hpq)
def adjusted := α*Equiv.swap p q
omit [Fintype O] in
include hi hpair in
lemma adjusted_p : adjusted α p q p=p := by
  rw [adjusted,Equiv.Perm.mul_apply,Equiv.swap_apply_left]
  exact (congrArg α hpair).symm.trans (hi p)
omit [Fintype O] in
include hpair in
lemma adjusted_q : adjusted α p q q=q := by
  rw [adjusted,Equiv.Perm.mul_apply,Equiv.swap_apply_right,hpair]
def α₁ : Equiv.Perm (Rest p) := restrict (adjusted α p q) p (adjusted_p α hi p q hpair)
omit [Fintype O] in
lemma α₁_q : α₁ α hi p q hpair (q' p q hpq)=q' p q hpq := by
  apply Subtype.ext
  exact adjusted_q α p q hpair

def partner : Equiv.Perm (Residual p q hpq) :=
  restrict (α₁ α hi p q hpair) (q' p q hpq) (α₁_q α hi p q hpq hpair)
def switched : Equiv.Perm O := Equiv.swap p q*σ
def rotation : Equiv.Perm (Residual p q hpq) := bypass (bypass (switched σ p q) p) (q' p q hpq)
def face : Equiv.Perm O := α*σ

def val (x : Residual p q hpq) : O := x.val.val
omit [Fintype O] in
lemma val_ne_p (x : Residual p q hpq) : val p q hpq x≠p := x.val.property
omit [Fintype O] in
lemma val_ne_q (x : Residual p q hpq) : val p q hpq x≠q := by
  intro h
  exact x.property (Subtype.ext h)
omit [Fintype O] in
lemma val_injective : Function.Injective (val p q hpq) := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)
omit [Fintype O] in
lemma partner_val (x : Residual p q hpq) :
    val p q hpq (partner α hi p q hpq hpair x)=α (val p q hpq x) := by
  change α (Equiv.swap p q (val p q hpq x))=_
  rw [Equiv.swap_apply_of_ne_of_ne (val_ne_p p q hpq x) (val_ne_q p q hpq x)]
omit [Fintype O] in
lemma partner_involutive : Function.Involutive (partner α hi p q hpq hpair) := by
  intro x
  apply val_injective p q hpq
  rw [partner_val,partner_val,hi]
omit [Fintype O] in
include hpair in
lemma partner_distinct (hf : ∀x,α x≠x) (x : Residual p q hpq) : partner α hi p q hpq hpair x≠x := by
  intro he
  have h := congrArg (val p q hpq) he
  rw [partner_val] at h
  exact hf _ h
lemma face_eq : partner α hi p q hpq hpair*rotation σ p q hpq=
    bypass (bypass (face σ α) p) (q' p q hpq) := by
  have he : face σ α=adjusted α p q*switched σ p q := by
    simp only [face,adjusted,switched]
    rw [mul_assoc α (Equiv.swap p q),←mul_assoc (Equiv.swap p q),Equiv.swap_mul_self,one_mul]
  rw [he,bypass_mul _ _ _ (adjusted_p α hi p q hpair)]
  change _=bypass (α₁ α hi p q hpair*bypass (switched σ p q) p) (q' p q hpq)
  rw [bypass_mul _ _ _ (α₁_q α hi p q hpq hpair)]
  rfl

variable (hs : σ p≠p) (hfp : face σ α p≠p) (hfq : face σ α q≠q)
omit [Fintype O] in
include hi hpair hfp in
lemma switched_p : switched σ p q p≠p := by
  intro he
  apply hfp
  have hh : adjusted α p q*switched σ p q=face σ α := by
    simp only [adjusted,switched,face]
    rw [mul_assoc α (Equiv.swap p q),←mul_assoc (Equiv.swap p q),Equiv.swap_mul_self,one_mul]
  rw [←hh,Equiv.Perm.mul_apply,he,adjusted_p α hi p q hpair]
omit [Fintype O] in
include hpair hfq in
lemma switched_q : switched σ p q q≠q := by
  intro he
  apply hfq
  have hh : adjusted α p q*switched σ p q=face σ α := by
    simp only [adjusted,switched,face]
    rw [mul_assoc α (Equiv.swap p q),←mul_assoc (Equiv.swap p q),Equiv.swap_mul_self,one_mul]
  rw [←hh,Equiv.Perm.mul_apply,he,adjusted_q α p q hpair]
omit [Fintype O] in
include hs in
lemma switched_p_ne_q : switched σ p q p≠q := by
  intro he
  have hh := congrArg (Equiv.swap p q) he
  simp only [switched,Equiv.Perm.mul_apply,Equiv.swap_apply_self,Equiv.swap_apply_right] at hh
  exact hs hh
omit [Fintype O] in
include hs hpair in
lemma face_p_ne_q : face σ α p≠q := by
  intro he
  exact hs (α.injective (he.trans hpair.symm))
include hi hpair hs hfp hfq in
lemma rotation_count : Fintype.card (Cycle (rotation σ p q hpq))=
    Fintype.card (Cycle (switched σ p q)) := by
  rw [rotation,bypass_count]
  · exact bypass_count _ _ (switched_p σ α hi p q hpair hfp)
  · apply bypass_nonfixed
    · exact switched_q σ α p q hpair hfq
    · intro _
      exact switched_p_ne_q σ p q hs
include hs hfp hfq in
lemma face_count : Fintype.card (Cycle (partner α hi p q hpq hpair*rotation σ p q hpq))=
    Fintype.card (Cycle (face σ α)) := by
  rw [face_eq,bypass_count]
  · exact bypass_count _ _ hfp
  · apply bypass_nonfixed
    · exact hfq
    · intro _
      exact face_p_ne_q σ α p q hpair hs
lemma two_fewer : Fintype.card (Residual p q hpq)+2=Fintype.card O := by
  have h₁ := card_rest (p:=p)
  have h₂ := card_rest (p:=q' p q hpq)
  simp only [←Nat.card_eq_fintype_card] at h₁ h₂ ⊢
  change Nat.card (Residual p q hpq)+1=Nat.card (Rest p) at h₂
  omega
include hs hfp hfq in
/-- The literal removal of a paired band preserves the global sphere Euler
lower bound. No componentwise planarity or essentiality is concluded here. -/
theorem euler (he : Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle (face σ α))) :
    Fintype.card (Residual p q hpq)+4≤2*Fintype.card (Cycle (rotation σ p q hpq))+
      2*Fintype.card (Cycle (partner α hi p q hpq hpair*rotation σ p q hpq)) := by
  rw [rotation_count σ α hi p q hpq hpair hs hfp hfq,face_count σ α hi p q hpq hpair hs hfp hfq]
  have hv := SwapCycles.count_le σ p q
  have hc := two_fewer p q hpq
  change Fintype.card (Cycle σ)≤Fintype.card (Cycle (switched σ p q))+1 at hv
  omega
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
lemma genusZero_fintype {O : Type} (i j : Fintype O) (σ α : Equiv.Perm O) :
    @GenusZero O i σ α ↔ @GenusZero O j σ α := by
  cases Subsingleton.elim i j
  rfl
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
omit [Fintype O] in
include hi hpair in
lemma adjusted_strip : adjusted α p q=PairingFactors.strip α p := by
  rw [←hpair]
  ext x
  change α (Equiv.swap p (α p) x)=Equiv.swap p (α p) (α x)
  rw [←α.injective.swap_apply,hi p,Equiv.swap_comm (α p) p]
include hi hpq hpair in
lemma switched_genusZero (hz : GenusZero σ α) :
    GenusZero (switched σ p q) (adjusted α p q) := by
  rw [adjusted_strip α hi p q hpair]
  have hp : α p≠p := by rw [hpair];exact hpq.symm
  have hh := genusZero_band σ α hi hz p hp
  simpa only [switched,hpair] using hh
include hi hpair in
/-- The genuine remaining map after deleting a paired band has genus zero in
all its actual components. This strengthens the global Euler estimate and uses
no assumed planar embedding. Local degenerate faces are explicitly excluded. -/
theorem genusZero (hz : GenusZero σ α) (hs : σ p≠p)
    (hfp : face σ α p≠p) (hfq : face σ α q≠q) :
    GenusZero (rotation σ p q hpq) (partner α hi p q hpq hpair) := by
  have h₀ := switched_genusZero σ α hi p q hpq hpair hz
  have h₁ := MapDeletion.genusZero_delete (switched σ p q) (adjusted α p q) p
    (adjusted_p α hi p q hpair) (switched_p σ α hi p q hpair hfp) h₀
  have hn : bypass (switched σ p q) p (q' p q hpq)≠q' p q hpq := by
    apply bypass_nonfixed
    · exact switched_q σ α p q hpair hfq
    · intro _
      exact switched_p_ne_q σ p q hs
  have h₂ := MapDeletion.genusZero_delete (bypass (switched σ p q) p) (α₁ α hi p q hpair)
    (q' p q hpq) (α₁_q α hi p q hpq hpair) hn h₁
  exact (genusZero_fintype _ _ _ _).mp h₂
end TorsionFreeZeroDivisors.BandEuler

/-! Actual finite noncrossing word matchings, the cancellation part of the
cone-picture construction. An ear is inserted at two adjacent positions.
This file asserts no sphere realization or asphericity theorem. -/
namespace TorsionFreeZeroDivisors.WordPairing

section
variable {A : Type*} {n : ℕ}

structure Data (inv : A → A) (label : Fin n → A) where
  partner : Equiv.Perm (Fin n)
  involutive : Function.Involutive partner
  distinct : ∀ i,partner i≠i
  compatible : ∀ i,label (partner i)=inv (label i)
  noncrossing : ∀ i j,i<j → j<partner i → partner i<partner j → False

namespace Ear
variable (k : ℕ)
def raise (i : Fin n) : Fin (n+2) := ⟨if i.val<k then i.val else i.val+2,by
  split_ifs with h <;> omega⟩
lemma raise_lt (i j : Fin n) : raise k i<raise k j ↔ i<j := by
  simp only [raise,Fin.lt_def]
  split_ifs <;> omega
lemma raise_injective : Function.Injective (raise (n:=n) k) := by
  intro i j he
  apply Fin.ext
  have hh := congrArg Fin.val he
  simp only [raise] at hh
  split_ifs at hh <;> omega
lemma raise_avoid (i : Fin n) : (raise k i).val≠k ∧ (raise k i).val≠k+1 := by
  simp only [raise]
  split_ifs <;> omega

def insert (hk : k≤n) : Fin n⊕Bool → Fin (n+2)
  | .inl i => raise k i
  | .inr false => ⟨k,by omega⟩
  | .inr true => ⟨k+1,by omega⟩
lemma insert_injective (hk : k≤n) : Function.Injective (insert k hk) := by
  intro x y he
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (raise_injective k he)
    | inr b =>
      have hh := congrArg Fin.val he
      have ha := raise_avoid k i
      cases b <;> simp only [insert] at hh <;> omega
  | inr b =>
    cases y with
    | inl i =>
      have hh := congrArg Fin.val he
      have ha := raise_avoid k i
      cases b <;> simp only [insert] at hh <;> omega
    | inr c =>
      have hh := congrArg Fin.val he
      cases b <;> cases c <;> simp only [insert] at hh <;> first | rfl | omega
lemma insert_surjective (hk : k≤n) : Function.Surjective (insert k hk) := by
  intro y
  by_cases h : y.val<k
  · refine ⟨.inl ⟨y.val,by omega⟩,?_⟩
    apply Fin.ext
    simp only [insert,raise,ite_eq_left h]
  · by_cases he : y.val=k
    · exact ⟨.inr false,Fin.ext he.symm⟩
    · by_cases he' : y.val=k+1
      · exact ⟨.inr true,Fin.ext he'.symm⟩
      · refine ⟨.inl ⟨y.val-2,by omega⟩,?_⟩
        apply Fin.ext
        have hh : ¬y.val-2<k := by omega
        simp only [insert,raise,ite_eq_right hh]
        omega

def equiv (hk : k≤n) : Fin n⊕Bool ≃ Fin (n+2) :=
  Equiv.ofBijective (insert k hk) ⟨insert_injective k hk,insert_surjective k hk⟩
@[simp] lemma equiv_left (hk : k≤n) (i : Fin n) : equiv k hk (.inl i)=raise k i := rfl
@[simp] lemma equiv_false (hk : k≤n) : (equiv k hk (.inr false)).val=k := rfl
@[simp] lemma equiv_true (hk : k≤n) : (equiv k hk (.inr true)).val=k+1 := rfl

variable {inv : A → A} {label : Fin n → A} (d : Data inv label)
def sumPartner : Equiv.Perm (Fin n⊕Bool) := Equiv.sumCongr d.partner Equiv.boolNot

def partner (hk : k≤n) : Equiv.Perm (Fin (n+2)) :=
  (equiv k hk).permCongr (sumPartner d)
lemma partner_apply (hk : k≤n) (i : Fin n⊕Bool) :
    partner k d hk (equiv k hk i)=equiv k hk (sumPartner d i) := by
  simp only [partner,Equiv.permCongr_apply,Equiv.symm_apply_apply]

lemma involutive (hk : k≤n) : Function.Involutive (partner k d hk) := by
  intro i
  obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
  rw [partner_apply,partner_apply]
  congr 1
  cases i with
  | inl i => exact congrArg Sum.inl (d.involutive i)
  | inr b => cases b <;> rfl
lemma distinct (hk : k≤n) (i : Fin (n+2)) : partner k d hk i≠i := by
  obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
  rw [partner_apply]
  intro he
  have hh := (equiv k hk).injective he
  cases i with
  | inl i => exact d.distinct i (Sum.inl.inj hh)
  | inr b => cases b <;> cases hh

lemma noncrossing (hk : k≤n) : ∀ i j : Fin (n+2),
    i<j → j<partner k d hk i → partner k d hk i<partner k d hk j → False := by
  intro i j hij hjp hpp
  obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
  obtain ⟨j,rfl⟩ := (equiv k hk).surjective j
  rw [partner_apply] at hjp hpp
  rw [partner_apply] at hpp
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact d.noncrossing i j ((raise_lt k _ _).mp hij)
        ((raise_lt k _ _).mp hjp) ((raise_lt k _ _).mp hpp)
    | inr b =>
      cases b with
      | false =>
        change k < (raise k (d.partner i)).val at hjp
        change (raise k (d.partner i)).val < k+1 at hpp
        omega
      | true =>
        change k+1 < (raise k (d.partner i)).val at hjp
        change (raise k (d.partner i)).val < k at hpp
        omega
  | inr b =>
    cases b with
    | false =>
      change k < (equiv k hk j).val at hij
      change (equiv k hk j).val < k+1 at hjp
      omega
    | true =>
      change k+1 < (equiv k hk j).val at hij
      change (equiv k hk j).val < k at hjp
      omega
end Ear
end

section
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Data
variable (d : Data inv label)
lemma reindex_apply (e : Fin n ≃o Fin m) (i : Fin n) :
    e.toEquiv.permCongr d.partner (e i)=e (d.partner i) := by
  change e (d.partner (e.symm (e i)))=e (d.partner i)
  rw [e.symm_apply_apply]
def reindex (e : Fin n ≃o Fin m) (label' : Fin m → A)
    (hl : ∀ i,label' (e i)=label i) : Data inv label' where
  partner := e.toEquiv.permCongr d.partner
  involutive := by
    intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    rw [d.reindex_apply,d.reindex_apply,d.involutive]
  distinct := by
    intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    rw [d.reindex_apply]
    exact fun he=>d.distinct i (e.injective he)
  compatible := by
    intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    rw [d.reindex_apply,hl,hl]
    exact d.compatible i
  noncrossing := by
    intro i j hij hjp hpp
    obtain ⟨i,rfl⟩ := e.surjective i
    obtain ⟨j,rfl⟩ := e.surjective j
    rw [d.reindex_apply] at hjp
    rw [d.reindex_apply,d.reindex_apply] at hpp
    exact d.noncrossing i j ((e.lt_iff_lt).mp hij)
      ((e.lt_iff_lt).mp hjp) ((e.lt_iff_lt).mp hpp)
end Data

namespace Ear
variable (k : ℕ) (hk : k≤n) (a : A)
def labels (i : Fin (n+2)) : A :=
  Sum.elim label (fun b=>if b then inv a else a) ((equiv k hk).symm i)
@[simp] lemma labels_left (i : Fin n) :
    labels (label:=label) (inv:=inv) k hk a (equiv k hk (.inl i))=label i := by
  simp only [labels,Equiv.symm_apply_apply,Sum.elim_inl]
@[simp] lemma labels_false :
    labels (label:=label) (inv:=inv) k hk a (equiv k hk (.inr false))=a := by
  simp only [labels,Equiv.symm_apply_apply,Sum.elim_inr,Bool.false_eq_true,ite_false]
@[simp] lemma labels_true :
    labels (label:=label) (inv:=inv) k hk a (equiv k hk (.inr true))=inv a := by
  simp only [labels,Equiv.symm_apply_apply,Sum.elim_inr,ite_true]

def data (d : Data inv label) (ha : inv (inv a)=a) :
    Data inv (labels (label:=label) (inv:=inv) k hk a) where
  partner := partner k d hk
  involutive := involutive k d hk
  distinct := distinct k d hk
  compatible := by
    intro i
    obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
    rw [partner_apply]
    cases i with
    | inl i =>
      change labels k hk a (equiv k hk (.inl (d.partner i)))=_
      rw [labels_left,labels_left]
      exact d.compatible i
    | inr b =>
      cases b with
      | false => exact (labels_true k hk a).trans (congrArg inv (labels_false k hk a).symm)
      | true =>
        change labels k hk a (equiv k hk (.inr false))=inv (labels k hk a (equiv k hk (.inr true)))
        rw [labels_false,labels_true,ha]
  noncrossing := noncrossing k d hk
end Ear

namespace ListInsert
variable (u v : List A) (a b : A)
lemma get_old (i : ℕ) (hi : i<(u++v).length) :
    (u++a::b::v)[if i<u.length then i else i+2]'(by split_ifs <;> simp only [List.length_append,List.length_cons] at * <;> omega)=
      (u++v)[i] := by
  by_cases h : i<u.length
  · simp only [ite_eq_left h,List.getElem_append_left h]
  · have hh : ¬i+2<u.length := by omega
    have he : i+2-u.length=(i-u.length)+2 := by omega
    simp only [ite_eq_right h,List.getElem_append,dite_eq_right h,dite_eq_right hh,he,List.getElem_cons_succ]
lemma get_first :
    (u++a::b::v)[u.length]'(by simp only [List.length_append,List.length_cons];omega)=a := by
  simp only [List.getElem_append,dite_eq_right (Nat.lt_irrefl _),Nat.sub_self,List.getElem_cons_zero]
lemma get_second :
    (u++a::b::v)[u.length+1]'(by simp only [List.length_append,List.length_cons];omega)=b := by
  have hh : ¬u.length+1<u.length := by omega
  simp only [List.getElem_append,dite_eq_right hh,Nat.add_sub_cancel_left,List.getElem_cons_succ,List.getElem_cons_zero]
end ListInsert

end
variable {A : Type*}
namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
lemma length_eq : (u++v).length+2=(u++a::inv a::v).length := by
  simp only [List.length_append,List.length_cons]
  omega

def orderIso : Fin ((u++v).length+2) ≃o Fin (u++a::inv a::v).length :=
  Fin.castOrderIso (length_eq u v inv a)

lemma labels_eq (i : Fin ((u++v).length+2)) :
    (u++a::inv a::v).get (orderIso u v inv a i)=
      Ear.labels (label:=(u++v).get) (inv:=inv) u.length
        (by simp only [List.length_append];omega) a i := by
  obtain ⟨i,rfl⟩ := (Ear.equiv u.length (show u.length≤(u++v).length by
    simp only [List.length_append];omega)).surjective i
  cases i with
  | inl i =>
    rw [Ear.labels_left]
    change (u++a::inv a::v)[if i.val<u.length then i.val else i.val+2]'(by
      have hi := i.isLt
      split_ifs <;> simp only [List.length_append,List.length_cons] at * <;> omega)=
      (u++v)[i.val]
    exact get_old u v a (inv a) i.val i.isLt
  | inr b =>
    cases b with
    | false =>
      rw [Ear.labels_false]
      exact get_first u v a (inv a)
    | true =>
      rw [Ear.labels_true]
      exact get_second u v a (inv a)

def data (d : Data inv (u++v).get) (ha : inv (inv a)=a) :
    Data inv (u++a::inv a::v).get :=
  (Ear.data u.length (by simp only [List.length_append];omega) a d ha).reindex
    (orderIso u v inv a) _ (labels_eq u v inv a)
end ListInsert

def inverseLetter (p : A × Bool) : A × Bool := (p.1,!p.2)
lemma inverseLetter_involutive : Function.Involutive (inverseLetter (A:=A)) := by
  intro p
  cases p with
  | mk a b => cases b <;> rfl

def emptyData : Data (inverseLetter (A:=A)) ([] : List (A×Bool)).get where
  partner := Equiv.refl _
  involutive := fun _=>rfl
  distinct i := Fin.elim0 i
  compatible i := Fin.elim0 i
  noncrossing i := Fin.elim0 i

theorem of_reduction {w : List (A×Bool)} (h : FreeGroup.Red w []) :
    Nonempty (Data inverseLetter w.get) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨emptyData⟩
  | @head x y hxy hy ih =>
    cases hxy with
    | @not u v a b =>
      obtain ⟨d⟩ := ih
      exact ⟨ListInsert.data u v inverseLetter (a,b) d (inverseLetter_involutive _)⟩

theorem of_identity {w : List (A×Bool)} (h : FreeGroup.mk w=1) :
    Nonempty (Data inverseLetter w.get) := by
  classical
  have he : FreeGroup.reduce w=[] := by
    have hh := FreeGroup.reduce.sound h
    exact hh
  apply of_reduction
  rw [←he]
  exact FreeGroup.reduce.red

end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.Ear
open PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
lemma rotate_val (i : Fin n) : (finRotate n i).val=if i.val+1<n then i.val+1 else 0 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [coe_finRotate]
    simp only [Fin.ext_iff,Fin.val_last]
    split_ifs <;> have := i.isLt <;> omega

def previous (k : ℕ) (hk : k≤n) (hn : 0<n) : Fin n :=
  ⟨if k=0 then n-1 else k-1,by split_ifs <;> omega⟩
variable (k : ℕ) (hk : k≤n) (hn : 0<n)
lemma previous_rotate : finRotate (n+2) (raise k (previous k hk hn))=equiv k hk (.inr false) := by
  apply Fin.ext
  change (finRotate (n+2) (raise k (previous k hk hn))).val=k
  rw [rotate_val]
  simp only [raise,previous]
  split_ifs <;> omega
lemma rotate_old (i : Fin n) (hi : i≠previous k hk hn) :
    finRotate (n+2) (raise k i)=raise k (finRotate n i) := by
  apply Fin.ext
  have hi' : i.val≠(previous k hk hn).val := fun h=>hi (Fin.ext h)
  rw [rotate_val]
  simp only [raise,rotate_val,previous] at *
  have hb := i.isLt
  split_ifs at * <;> omega
lemma rotate_false : finRotate (n+2) (equiv k hk (.inr false))=equiv k hk (.inr true) := by
  apply Fin.ext
  rw [rotate_val]
  change (if k+1<n+2 then k+1 else 0)=k+1
  rw [ite_eq_left (by omega)]
lemma rotate_true : finRotate (n+2) (equiv k hk (.inr true))=
    raise k (finRotate n (previous k hk hn)) := by
  apply Fin.ext
  rw [rotate_val]
  change (if k+1+1<n+2 then k+1+1 else 0)=_
  simp only [raise,rotate_val,previous]
  split_ifs <;> omega

lemma rotation_transport (i : Fin n⊕Bool) :
    finRotate (n+2) (equiv k hk i)=equiv k hk
      (InsertedRotation.rotation (finRotate n) (previous k hk hn) i) := by
  cases i with
  | inl i =>
    by_cases hi : i=previous k hk hn
    · subst i
      rw [InsertedRotation.rotation_p,equiv_left]
      exact previous_rotate k hk hn
    · rw [InsertedRotation.rotation_left _ _ i hi,equiv_left,equiv_left]
      exact rotate_old k hk hn i hi
  | inr b =>
    cases b with
    | false => rw [InsertedRotation.rotation_false]; exact rotate_false k hk
    | true => rw [InsertedRotation.rotation_true,equiv_left]; exact rotate_true k hk hn

lemma rotation_eq : (equiv k hk).permCongr
    (InsertedRotation.rotation (finRotate n) (previous k hk hn))=finRotate (n+2) := by
  apply Equiv.ext
  intro i
  obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  exact (rotation_transport k hk hn i).symm

variable (d : Data inv label)
lemma face_eq : (equiv k hk).permCongr
    (InsertedRotation.face (finRotate n) d.partner (previous k hk hn))=
    partner k d hk *finRotate (n+2) := by
  rw [InsertedRotation.face,PermutationTransport.mul,rotation_eq k hk hn]
  rfl

include hn in
theorem face_count :
    Fintype.card (Cycle (d.partner*finRotate n))+1≤
      Fintype.card (Cycle (partner k d hk*finRotate (n+2))) := by
  rw [←face_eq k hk hn d,PermutationTransport.card_cycles]
  exact InsertedRotation.face_count _ _ _

end TorsionFreeZeroDivisors.WordPairing.Ear

namespace TorsionFreeZeroDivisors.PermutationCycles
variable (O : Type) [Fintype O]
lemma card_identity : Fintype.card (Cycle (1 : Equiv.Perm O))=Fintype.card O := by
  apply (Fintype.card_of_bijective (f:=cycle (1 : Equiv.Perm O)) ?_).symm
  refine ⟨?_,cycle_surjective _⟩
  intro x y h
  exact ((cycle_eq _).mp h).eq_of_left rfl
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.WordPairing

section
open PermutationCycles
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

/-- The disk Euler estimate for the actual circle rotation and word matching.
The empty word is distinguished, since it has no boundary occurrences. -/
def DiskEuler (d : Data inv label) : Prop :=
  n=0 ∨ n+2≤2*Fintype.card (Cycle (d.partner*finRotate n))

lemma Data.reindex_euler (d : Data inv label) (h : n=m) (label' : Fin m→A)
    (hl : ∀i,label' (Fin.castOrderIso h i)=label i) (hd : DiskEuler d) :
    DiskEuler (d.reindex (Fin.castOrderIso h) label' hl) := by
  subst m
  exact hd

namespace Ear
variable (k : ℕ) (hk : k≤n) (d : Data inv label)
lemma empty_rotation (hn : n=0) : partner k d hk=finRotate (n+2) := by
  subst n
  have he : k=0 := by omega
  subst k
  apply Equiv.ext
  intro i
  obtain ⟨i,rfl⟩ := (equiv 0 hk).surjective i
  rw [partner_apply]
  cases i with
  | inl i => exact i.elim0
  | inr b => cases b <;> rfl

lemma euler (hd : DiskEuler d) :
    n+2+2≤2*Fintype.card (Cycle (partner k d hk*finRotate (n+2))) := by
  by_cases he : n=0
  · have hrot := empty_rotation k hk d he
    have hf : partner k d hk*finRotate (n+2)=1 := by
      apply Equiv.ext
      intro i
      rw [Equiv.Perm.mul_apply,←hrot]
      exact involutive k d hk i
    rw [hf,card_identity,Fintype.card_fin,he]
  · have hn : 0<n := Nat.pos_of_ne_zero he
    have hc := face_count k hk hn d
    rcases hd with hh|hh
    · exact (he hh).elim
    · omega
end Ear

namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
lemma data_euler (d : Data inv (u++v).get) (ha : inv (inv a)=a) (hd : DiskEuler d) :
    DiskEuler (data u v inv a d ha) := by
  apply Data.reindex_euler
  apply Or.inr
  exact Ear.euler u.length (by simp only [List.length_append];omega) d hd
end ListInsert

/-- The face-count input is now proved for the matching constructed from literal
free cancellation. This does not yet claim a multi-disk PL realization. -/
theorem of_reduction_euler {w : List (A×Bool)} (h : FreeGroup.Red w []) :
    ∃ d : Data inverseLetter w.get,DiskEuler d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨emptyData,Or.inl rfl⟩
  | @head x y hxy hy ih =>
    cases hxy with
    | @not u v a b =>
      obtain ⟨d,hd⟩ := ih
      refine ⟨ListInsert.data u v inverseLetter (a,b) d (inverseLetter_involutive _),?_⟩
      exact ListInsert.data_euler u v inverseLetter (a,b) d (inverseLetter_involutive _) hd

theorem of_identity_euler {w : List (A×Bool)} (h : FreeGroup.mk w=1) :
    ∃ d : Data inverseLetter w.get,DiskEuler d := by
  classical
  have he : FreeGroup.reduce w=[] := FreeGroup.reduce.sound h
  apply of_reduction_euler
  rw [←he]
  exact FreeGroup.reduce.red

end
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
/-- Every nonempty finite noncrossing perfect matching has a literal adjacent
ear, obtained by minimizing the positive distance between matched positions. -/
theorem adjacent_ear (d : Data inv label) (hn : 0 < n) :
    ∃i : Fin n,(d.partner i).val=i.val+1 := by
  let s : Finset (Fin n) := Finset.univ.filter (fun i=> i < d.partner i)
  have hs : s.Nonempty := by
    let z : Fin n := ⟨0,hn⟩
    refine ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    have he := d.distinct z
    have hv : (d.partner z).val ≠ 0 := by intro h;exact he (Fin.ext h)
    change 0 < (d.partner z).val
    omega
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image s (fun i=> (d.partner i).val-i.val) hs
  have hip : i < d.partner i := (Finset.mem_filter.mp hi).2
  refine ⟨i,?_⟩
  by_contra he
  have hgap : i.val+1 < (d.partner i).val := by change i.val < (d.partner i).val at hip;omega
  let j : Fin n := ⟨i.val+1,lt_trans hgap (d.partner i).isLt⟩
  have hij : i < j := by change i.val < i.val+1;omega
  have hjp : j < d.partner i := hgap
  have hpj : j < d.partner j := by
    by_contra h
    have hpj : d.partner j < j := lt_of_le_of_ne (le_of_not_gt h) (d.distinct j)
    have hai : d.partner j ≠ i := by
      intro h
      have h' : j=d.partner i := (d.involutive j).symm.trans (congrArg d.partner h)
      exact (ne_of_lt hjp) h'
    have hapi : d.partner j < i := by
      have haival : (d.partner j).val ≠ i.val := by intro hh;exact hai (Fin.ext hh)
      change (d.partner j).val < i.val
      change (d.partner j).val < i.val+1 at hpj
      omega
    apply d.noncrossing (d.partner j) i hapi
    · simpa only [d.involutive j] using hij
    · simpa only [d.involutive j] using hjp
  have upper : d.partner j < d.partner i := by
    have hnlt : ¬d.partner i < d.partner j := fun h=> d.noncrossing i j hij hjp h
    have hne : d.partner j ≠ d.partner i := fun hh=> ne_of_gt hij (d.partner.injective hh)
    exact lt_of_le_of_ne (le_of_not_gt hnlt) hne
  have hmem : j∈s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpj⟩
  have hm := hmin j hmem
  change (d.partner i).val-i.val ≤ (d.partner j).val-(i.val+1) at hm
  change (d.partner j).val < (d.partner i).val at upper
  omega
end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.EraseEar
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin (n+2)→A}
  (d : Data inv label) (k : ℕ) (hk : k≤n)
  (hpair : d.partner (Ear.equiv k hk (.inr false))=Ear.equiv k hk (.inr true))
include hpair in
lemma back : d.partner (Ear.equiv k hk (.inr true))=Ear.equiv k hk (.inr false) :=
  (congrArg d.partner hpair).symm.trans (d.involutive _)
include hpair in
lemma remains (i : Fin n) : ∃j : Fin n,Ear.raise k j=d.partner (Ear.raise k i) := by
  obtain ⟨a,ha⟩ := (Ear.equiv k hk).surjective (d.partner (Ear.raise k i))
  cases a with
  | inl j => exact ⟨j,ha⟩
  | inr b =>
    cases b with
    | false =>
      have he := hpair.symm.trans ((congrArg d.partner ha).trans (d.involutive _))
      change Ear.equiv k hk (.inr true)=Ear.equiv k hk (.inl i) at he
      cases (Ear.equiv k hk).injective he
    | true =>
      have he := (back d k hk hpair).symm.trans ((congrArg d.partner ha).trans (d.involutive _))
      change Ear.equiv k hk (.inr false)=Ear.equiv k hk (.inl i) at he
      cases (Ear.equiv k hk).injective he

def lower (i : Fin n) : Fin n := Classical.choose (remains d k hk hpair i)
lemma lower_spec (i : Fin n) : Ear.raise k (lower d k hk hpair i)=d.partner (Ear.raise k i) :=
  Classical.choose_spec (remains d k hk hpair i)
lemma lower_involutive : Function.Involutive (lower d k hk hpair) := by
  intro i
  apply Ear.raise_injective k
  rw [lower_spec,lower_spec,d.involutive]

def data : Data inv (fun i=>label (Ear.raise (n:=n) k i)) where
  partner := ⟨lower d k hk hpair,lower d k hk hpair,
    lower_involutive d k hk hpair,lower_involutive d k hk hpair⟩
  involutive := lower_involutive d k hk hpair
  distinct i := by
    intro he
    have hh := congrArg (Ear.raise k) he
    change Ear.raise k (lower d k hk hpair i)=Ear.raise k i at hh
    rw [lower_spec] at hh
    exact d.distinct _ hh
  compatible i := by
    change label (Ear.raise k (lower d k hk hpair i))=inv (label (Ear.raise k i))
    rw [lower_spec,d.compatible]
  noncrossing i j hij hji hpp := by
    apply d.noncrossing (Ear.raise k i) (Ear.raise k j) ((Ear.raise_lt k i j).mpr hij)
    · rw [←lower_spec d k hk hpair i]
      exact (Ear.raise_lt k _ _).mpr hji
    · rw [←lower_spec d k hk hpair i,←lower_spec d k hk hpair j]
      exact (Ear.raise_lt k _ _).mpr hpp

lemma recover : Ear.partner k (data d k hk hpair) hk=d.partner := by
  apply Equiv.ext
  intro i
  obtain ⟨a,rfl⟩ := (Ear.equiv k hk).surjective i
  rw [Ear.partner_apply]
  cases a with
  | inl i => exact lower_spec d k hk hpair i
  | inr b =>
    cases b with
    | false => exact hpair.symm
    | true => exact (back d k hk hpair).symm

lemma euler (hd : DiskEuler (data d k hk hpair)) : DiskEuler d := by
  apply Or.inr
  rw [←recover d k hk hpair]
  exact Ear.euler k hk (data d k hk hpair) hd
end TorsionFreeZeroDivisors.WordPairing.EraseEar
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
variable {A : Type*} {inv : A → A}
/-- Every literal finite noncrossing inverse-letter matching has the disk Euler
estimate, independently of its choice as a free cancellation witness. -/
theorem Data.diskEuler {n : ℕ} {label : Fin n → A} (d : Data inv label) : DiskEuler d := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact Or.inl rfl
    | succ n =>
      cases n with
      | zero => exact False.elim (d.distinct 0 (Fin.ext (by have h := (d.partner 0).isLt; omega)))
      | succ n =>
        obtain ⟨i,hi⟩ := adjacent_ear d (by omega)
        have hk : i.val ≤ n := by have hb := (d.partner i).isLt;omega
        have hp : d.partner (Ear.equiv i.val hk (.inr false))=
            Ear.equiv i.val hk (.inr true) := by
          have he : Ear.equiv i.val hk (.inr false)=i := Fin.ext rfl
          rw [he]
          exact Fin.ext hi
        apply EraseEar.euler d i.val hk hp
        exact ih n (by omega) (EraseEar.data d i.val hk hp)
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.MapEuler
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
lemma component_sameCycle {x y : O} (h : σ.SameCycle x y) :
    component σ α x=component σ α y := by
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  have hh := PermutationCycles.invariant_pow σ (component σ α) (component_rotation σ α) k x
  rw [hk] at hh
  exact hh.symm
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
open MapEuler PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin n→A} (d : Data inv label)
lemma rotate_sameCycle (hn : 2≤n) (x y : Fin n) : (finRotate n).SameCycle x y := by
  apply (isCycle_finRotate_of_le hn).sameCycle
  · exact Equiv.Perm.mem_support.mp (by rw [support_finRotate_of_le hn];exact Finset.mem_univ _)
  · exact Equiv.Perm.mem_support.mp (by rw [support_finRotate_of_le hn];exact Finset.mem_univ _)
/-- The noncrossing cancellation matching has actual combinatorial genus zero,
not just a scalar disk face estimate. Nonempty words (necessarily of length at
least two) have a single map component; the empty case is separate. -/
theorem Data.genusZero : GenusZero (finRotate n) d.partner := by
  by_cases hn : n=0
  · subst n
    have hi : IsEmpty (Fin 0) := inferInstance
    have hV : IsEmpty (Cycle (finRotate 0)) := inferInstance
    have hF : IsEmpty (Cycle (d.partner*finRotate 0)) := inferInstance
    have hC : IsEmpty (Component (finRotate 0) d.partner) := inferInstance
    simp only [GenusZero,Nat.card_of_isEmpty,mul_zero,add_zero]
    simp only [Equiv.Perm.support,Finset.univ_eq_empty,Finset.filter_empty,Finset.card_empty]
  have hn2 : 2≤n := by
    by_contra hh
    have he : n=1 := by omega
    subst n
    exact d.distinct 0 (Subsingleton.elim _ _)
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let : Subsingleton (Cycle (finRotate n)) := ⟨by
    intro x y
    obtain ⟨a,rfl⟩ := cycle_surjective _ x
    obtain ⟨b,rfl⟩ := cycle_surjective _ y
    exact (cycle_eq _).mpr (rotate_sameCycle hn2 a b)⟩
  let : Subsingleton (Component (finRotate n) d.partner) := ⟨by
    intro x y
    obtain ⟨a,rfl⟩ := Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Quotient.mk_surjective y
    exact component_sameCycle _ _ (rotate_sameCycle hn2 a b)⟩
  let : Nonempty (Cycle (finRotate n)) := ⟨cycle _ ⟨0,by omega⟩⟩
  let : Nonempty (Component (finRotate n) d.partner) := ⟨component _ _ ⟨0,by omega⟩⟩
  have hV : Nat.card (Cycle (finRotate n))=1 := Nat.card_unique
  have hC : Nat.card (Component (finRotate n) d.partner)=1 := Nat.card_unique
  have hd := (d.diskEuler).resolve_left hn
  simp only [←Nat.card_eq_fintype_card] at hd
  apply genusZero_of_lower (finRotate n) d.partner d.involutive
  rw [hV,hC]
  have he := d.distinct
  simp only [Equiv.Perm.support,he,ne_eq,not_false_eq_true,Finset.filter_true,Finset.card_univ,Fintype.card_fin]
  omega
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.DeleteCycle
open scoped Classical
variable {O : Type} (σ : Equiv.Perm O) (p : O)
lemma bypass_fixed (h : σ p=p) : bypass σ p=restrict σ p h := by
  ext x
  change Equiv.swap p (σ p) (σ x)=σ x
  rw [h,Equiv.swap_self]
  rfl
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.IsolatedDeletion
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} (σ α : Equiv.Perm O) (p : O) (hs : σ p=p) (ha : α p=p)
def classify (x : O) : Option (Component (restrict σ p hs) (restrict α p ha)) :=
  if hx : x=p then none else some (component _ _ ⟨x,hx⟩)
lemma classify_rotation (x : O) : classify σ α p hs ha (σ x)=classify σ α p hs ha x := by
  by_cases hx : x=p
  · subst x;rw [hs]
  · rw [classify,dite_eq_right ((invariant σ p hs x).mpr hx),classify,dite_eq_right hx]
    exact congrArg some (component_rotation (restrict σ p hs) (restrict α p ha) ⟨x,hx⟩)
lemma classify_partner (x : O) : classify σ α p hs ha (α x)=classify σ α p hs ha x := by
  by_cases hx : x=p
  · subst x;rw [ha]
  · rw [classify,dite_eq_right ((invariant α p ha x).mpr hx),classify,dite_eq_right hx]
    exact congrArg some (component_partner (restrict σ p hs) (restrict α p ha) ⟨x,hx⟩)
def project : Component σ α → Option (Component (restrict σ p hs) (restrict α p ha)) :=
  MapEuler.lift σ α (classify σ α p hs ha) (classify_rotation σ α p hs ha) (classify_partner σ α p hs ha)
def inclusion : Component (restrict σ p hs) (restrict α p ha) → Component σ α :=
  MapEuler.lift _ _ (fun x : Rest p=>component σ α x)
    (fun x=>component_rotation σ α x) (fun x=>component_partner σ α x)
lemma project_injective : Function.Injective (project σ α p hs ha) := by
  intro c d he
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
  obtain ⟨y,rfl⟩ := Quotient.mk_surjective d
  change classify σ α p hs ha x=classify σ α p hs ha y at he
  by_cases hx : x=p
  · subst x
    have hy : y=p := by
      by_contra hy
      simp [classify,hy] at he
    subst y;rfl
  · by_cases hy : y=p
    · subst y;simp [classify,hx] at he
    · simp only [classify,dite_eq_right hx,dite_eq_right hy,Option.some.injEq] at he
      exact congrArg (inclusion σ α p hs ha) he
lemma project_surjective : Function.Surjective (project σ α p hs ha) := by
  intro c
  cases c with
  | none=>exact ⟨component σ α p,by simp [project,MapEuler.lift,classify,component]⟩
  | some c=>
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    refine ⟨component σ α x,?_⟩
    change classify σ α p hs ha x=some (component _ _ x)
    simp only [classify,dite_eq_right x.property]
def componentEquiv : Component σ α ≃ Option (Component (restrict σ p hs) (restrict α p ha)) :=
  Equiv.ofBijective (project σ α p hs ha) ⟨project_injective σ α p hs ha,project_surjective σ α p hs ha⟩
variable [Fintype O]
lemma component_count : Nat.card (Component σ α)=Nat.card (Component (restrict σ p hs) (restrict α p ha))+1 := by
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using Nat.card_congr (componentEquiv σ α p hs ha)
include hs in
/-- Deleting an isolated unpaired occurrence removes one vertex, one face and
one actual connected component; genus zero is preserved also in the empty case. -/
theorem genusZero (hz : GenusZero σ α) :
    GenusZero (bypass σ p) (restrict α p ha) := by
  rw [bypass_fixed σ p hs]
  have hv := fixed_count σ p hs
  have hf := fixed_count (α*σ) p (show (α*σ) p=p by change α (σ p)=p;rw [hs,ha])
  have hc := component_count σ α p hs ha
  have he := MapDeletion.support_count α p ha
  simp only [←Nat.card_eq_fintype_card] at hv hf
  have hface : restrict (α*σ) p (show (α*σ) p=p by change α (σ p)=p;rw [hs,ha])=
      restrict α p ha*restrict σ p hs := by ext x;rfl
  rw [hface] at hf
  dsimp only [GenusZero] at hz ⊢
  have hsup : (restrict α p ha).support.card=α.support.card := by
    convert he using 1
  have hh : 2*Nat.card (PermutationCycles.Cycle (restrict σ p hs))+
      2*Nat.card (PermutationCycles.Cycle (restrict α p ha*restrict σ p hs))=
      (restrict α p ha).support.card+4*Nat.card (Component (restrict σ p hs) (restrict α p ha)) := by omega
  have hinst : ∀ (i j : Fintype (Rest p)) (d e : DecidableEq (Rest p)),
      @Equiv.Perm.support (Rest p) d i (restrict α p ha)=
      @Equiv.Perm.support (Rest p) e j (restrict α p ha) := by
    intro i j d e
    cases Subsingleton.elim i j
    cases Subsingleton.elim d e
    rfl
  convert hh using 1
  congr 1
  exact congrArg Finset.card (hinst _ _ _ _)
end TorsionFreeZeroDivisors.IsolatedDeletion
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
/-- Unconditional deletion of an unpaired occurrence, including isolated
vertices/components. -/
theorem genusZero_delete_all (hz : GenusZero σ α) : GenusZero (bypass σ p) (restrict α p ha) := by
  by_cases hs : σ p=p
  · exact IsolatedDeletion.genusZero σ α p hs ha hz
  · exact genusZero_delete σ α p ha hs hz
end TorsionFreeZeroDivisors.MapDeletion

namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
include hi hpair in
/-- Paired-band deletion preserves genus zero without any degree or face
nondegeneracy assumptions. Empty residual maps, isolated disks, monogons, digons,
and split components are all included. This is purely a permutation-map result,
not an assertion that an essential sphere survives the surgery. -/
theorem genusZero_all (hz : GenusZero σ α) :
    GenusZero (rotation σ p q hpq) (partner α hi p q hpq hpair) := by
  have h₀ := switched_genusZero σ α hi p q hpq hpair hz
  have h₁ := MapDeletion.genusZero_delete_all (switched σ p q) (adjusted α p q) p
    (adjusted_p α hi p q hpair) h₀
  have h₂ := MapDeletion.genusZero_delete_all (bypass (switched σ p q) p) (α₁ α hi p q hpair)
    (q' p q hpq) (α₁_q α hi p q hpq hpair) h₁
  exact (genusZero_fintype _ _ _ _).mp h₂
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
/-- Exact Euler lower bound used by the source interval estimate, extracted
from actual combinatorial genus zero. No connectivity is assumed: one actual
occurrence suffices to make the component count positive. -/
theorem euler_of_genusZero [Nonempty O] (hz : GenusZero σ α) (hf : ∀x,α x≠x) :
    Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle (α*σ)) := by
  let : Nonempty (Component σ α) := ⟨component σ α (Classical.choice inferInstance)⟩
  have hc : 0<Nat.card (Component σ α) := Nat.card_pos
  have he : α.support.card=Fintype.card O := by
    simp only [Equiv.Perm.support,hf,ne_eq,not_false_eq_true,Finset.filter_true,Finset.card_univ]
  dsimp only [GenusZero] at hz
  simp only [Nat.card_eq_fintype_card] at hz hc
  rw [he] at hz
  omega
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.BoundarySurgery
open scoped Classical
open DeleteCycle BandEuler
variable {O V : Type} [Fintype O] (σ : Equiv.Perm O) (before after : O→V)
/-- Consecutive edge endpoint agreement. A marked exterior break can be encoded
by one extra formal item with distinct prescribed before/after endpoints. -/
def Consistent : Prop := ∀ x,after x=before (σ x)
include σ in
lemma bypass_consistent (h : Consistent σ before after) (p : O) (hp : after p=before p) :
    Consistent (bypass σ p) (fun x : Rest p=>before x) (fun x : Rest p=>after x) := by
  intro x
  change after (x : O)=before ((bypass σ p x : Rest p) : O)
  rw [bypass_apply,MapEuler.swap_invariant before p (σ p) (hp.symm.trans (h p))]
  exact h x
variable (p q : O) (hpq : p≠q)
def swappedBefore (x : O) : V := before (Equiv.swap p q x)
omit [Fintype O] in
lemma switched_consistent (h : Consistent σ before after) :
    Consistent (switched σ p q) (swappedBefore before p q) after := by
  intro x
  change after x=before (Equiv.swap p q (Equiv.swap p q (σ x)))
  rw [Equiv.swap_apply_self]
  exact h x
/-- The literal band-spliced boundary preserves the graph endpoint equations.
The two crossed endpoints are exactly those forced by an edge and its reverse.
No statement about homotopy or essentiality is hidden in this combinatorial
lemma, and neither distinct-boundary nor same-boundary cases are excluded. -/
theorem consistent (h : Consistent σ before after)
    (hp : after p=before q) (hq : after q=before p) :
    Consistent (rotation σ p q hpq) (fun x=>before (val p q hpq x))
      (fun x=>after (val p q hpq x)) := by
  have hp' : after p=swappedBefore before p q p := by rw [swappedBefore,Equiv.swap_apply_left];exact hp
  have hq' : after q=swappedBefore before p q q := by rw [swappedBefore,Equiv.swap_apply_right];exact hq
  have h₁ := bypass_consistent (switched σ p q) (swappedBefore before p q) after
    (switched_consistent σ before after p q h) p hp'
  have h₂ := bypass_consistent (bypass (switched σ p q) p)
    (fun x : Rest p=>swappedBefore before p q x) (fun x : Rest p=>after x) h₁
    (q' p q hpq) hq'
  intro x
  have hh := h₂ x
  change after (val p q hpq x)=swappedBefore before p q (val p q hpq (rotation σ p q hpq x)) at hh
  rw [swappedBefore,Equiv.swap_apply_of_ne_of_ne (val_ne_p p q hpq _) (val_ne_q p q hpq _)] at hh
  exact hh
/-- A surviving exterior marker keeps its prescribed distinct endpoints, so
its new boundary contains at least one actual edge after the deletion. -/
lemma marker_nonfixed (h : Consistent σ before after)
    (hp : after p=before q) (hq : after q=before p)
    (m : Residual p q hpq) (hm : after (val p q hpq m)≠before (val p q hpq m)) :
    rotation σ p q hpq m≠m := by
  intro he
  have hh := consistent σ before after p q hpq h hp hq m
  rw [he] at hh
  exact hm hh
end TorsionFreeZeroDivisors.BoundarySurgery

namespace TorsionFreeZeroDivisors.VertexSplit
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O)
  (l : List (O×O)) (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
  (he : ∀e∈l,α e.1=e.2)
  (hc : cycle σ p=cycle σ q)
local notation "σ'" => Equiv.swap p q*σ
local notation "L'" => (α p,α q)::l
local notation "f'" => forest σ' L'
include hl in
lemma forest_partner (x : O) : cycle f' (α x)=cycle f' x := by
  have h := MapEuler.product_invariant l (cycle f')
    (fun e h=>forest_pair σ' L' e (List.mem_cons_of_mem _ h)) x
  simpa only [hl] using h
include hl in
lemma forest_join : cycle f' p=cycle f' q := by
  have h := forest_pair σ' L' (α p,α q) List.mem_cons_self
  dsimp only at h
  rw [forest_partner σ α p q l hl,forest_partner σ α p q l hl] at h
  exact h
include hl in
lemma forest_rotation (x : O) : cycle f' (σ x)=cycle f' x := by
  have hh := forest_refines σ' L' (σ' x) x (cycle_apply σ' x)
  change cycle f' (Equiv.swap p q (σ x))=cycle f' x at hh
  rw [SwapCycles.cycle_swap f' p q (forest_join σ α p q l hl) (σ x)] at hh
  exact hh
include he hc in
lemma original_invariant (x : O) : MapEuler.component σ α (f' x)=MapEuler.component σ α x := by
  have hpq : MapEuler.component σ α p=MapEuler.component σ α q :=
    MapEuler.component_sameCycle σ α ((cycle_eq σ).mp hc)
  apply invariant_forest σ' L' (MapEuler.component σ α)
  · intro y
    change MapEuler.component σ α (Equiv.swap p q (σ y))=MapEuler.component σ α y
    rw [MapEuler.swap_invariant (MapEuler.component σ α) p q hpq]
    exact MapEuler.component_rotation σ α y
  · intro e h
    rcases List.mem_cons.mp h with rfl|h
    · dsimp only
      rw [MapEuler.component_partner,MapEuler.component_partner]
      exact hpq
    · rw [←he e h]
      exact (MapEuler.component_partner σ α e.1).symm

def toOriginal : Cycle f' → MapEuler.Component σ α :=
  PermutationCycles.lift f' (MapEuler.component σ α) (original_invariant σ α p q l he hc)
def toForest : MapEuler.Component σ α → Cycle f' :=
  MapEuler.lift σ α (cycle f') (forest_rotation σ α p q l hl) (forest_partner σ α p q l hl)
def componentEquiv : Cycle f' ≃ MapEuler.Component σ α :=
  Equiv.ofBijective (toOriginal σ α p q l he hc) ⟨by
    intro c d h
    obtain ⟨x,rfl⟩ := cycle_surjective f' c
    obtain ⟨y,rfl⟩ := cycle_surjective f' d
    exact congrArg (toForest σ α p q l hl) h,
    PermutationCycles.lift_surjective _ _ _ Quotient.mk_surjective⟩
omit [Fintype O] in
include hl in
lemma face_eq : face σ' L'=α*σ := by
  rw [MapEuler.face_product,List.map_cons,List.prod_cons,hl]
  have hs : Equiv.swap (α p) (α q)*α=α*Equiv.swap p q := by
    ext x
    exact α.injective.swap_apply p q x
  rw [hs,mul_assoc,←mul_assoc (Equiv.swap p q),Equiv.swap_mul_self,one_mul]
end TorsionFreeZeroDivisors.VertexSplit
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
include hi in
/-- Splitting a vertex along two gaps preserves combinatorial genus zero.
This permits empty/isolated components and needs no topological embedding
assumption. The two gaps must be on the same actual vertex cycle. -/
theorem genusZero_vertexSplit (hz : GenusZero σ α) (p q : O) (hpq : p≠q)
    (hc : cycle σ p=cycle σ q) : GenusZero (Equiv.swap p q*σ) α := by
  obtain ⟨l,hl,hL,he⟩ := PairingFactors.factorization α hi
  let σ' := Equiv.swap p q*σ
  let L' := (α p,α q)::l
  have hC := Nat.card_congr (VertexSplit.componentEquiv σ α p q l hl (fun e h=>(he e h).2) hc)
  have hV := SwapCycles.split_count σ p q hpq hc
  simp only [←Nat.card_eq_fintype_card] at hV
  have hF := VertexSplit.face_eq σ α p q l hl
  have hD : ∀e∈L',e.1≠e.2 := by
    intro e h
    rcases List.mem_cons.mp h with rfl|h
    · exact fun h=>hpq (α.injective h)
    · exact (he e h).1
  have hh := handles_exact σ' L' hD
  change Nat.card (Cycle σ')+Nat.card (Cycle (face σ' L'))+2*handles σ' L'=
    L'.length+2*Nat.card (Cycle (forest σ' L')) at hh
  change face σ' L'=α*σ at hF
  rw [hF,hC] at hh
  have hh₀ : handles σ' L'=0 := by
    dsimp only [L',List.length_cons] at hh
    dsimp only [GenusZero] at hz
    change Nat.card (Cycle σ')=Nat.card (Cycle σ)+1 at hV
    change handles σ' ((α p,α q)::l)=0
    omega
  have ht : handles σ' l=0 := Nat.eq_zero_of_le_zero
    ((handles_tail σ' (α p,α q) l).trans_eq hh₀)
  exact (genusZero_iff_handles σ' α l hl he hL).mpr ht
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.MapConjugation
open scoped Classical
open MapEuler PermutationCycles
variable {A B : Type} (e : A ≃ B) (σ α : Equiv.Perm A)
local notation "σ'" => e.permCongr σ
local notation "α'" => e.permCongr α
def forward : Component σ α → Component σ' α' :=
  MapEuler.lift σ α (fun x=>component σ' α' (e x))
    (fun x=>by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using component_rotation σ' α' (e x))
    (fun x=>by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using component_partner σ' α' (e x))
def backward : Component σ' α' → Component σ α :=
  MapEuler.lift σ' α' (fun x=>component σ α (e.symm x))
    (fun x=>by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using component_rotation σ α (e.symm x))
    (fun x=>by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using component_partner σ α (e.symm x))
def components : Component σ α ≃ Component σ' α' where
  toFun := forward e σ α
  invFun := backward e σ α
  left_inv c := by
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    change component σ α (e.symm (e x))=component σ α x
    rw [e.symm_apply_apply]
  right_inv c := by
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    change component σ' α' (e (e.symm x))=component σ' α' x
    rw [e.apply_symm_apply]
variable [Fintype A] [Fintype B]
def supports : ↥α.support ≃ ↥(α').support where
  toFun x := ⟨e x,by
    apply Equiv.Perm.mem_support.mpr
    intro h
    have hn := Equiv.Perm.mem_support.mp x.property
    exact hn (e.injective (by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using h))⟩
  invFun x := ⟨e.symm x,by
    apply Equiv.Perm.mem_support.mpr
    intro h
    have hn := Equiv.Perm.mem_support.mp x.property
    apply hn
    change e (α (e.symm x))=x
    rw [h,e.apply_symm_apply]⟩
  left_inv x := by ext;simp
  right_inv x := by ext;simp
lemma support_count : (α').support.card=α.support.card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (supports e α)).symm
/-- Changing the actual finite occurrence coordinates does not change genus. -/
theorem genusZero (h : GenusZero σ α) : GenusZero σ' α' := by
  have hC := Nat.card_congr (components e σ α)
  have hV := Nat.card_congr (PermutationTransport.cycles e σ)
  have hF := Nat.card_congr (PermutationTransport.cycles e (α*σ))
  rw [PermutationTransport.mul] at hF
  have hE := support_count e α
  dsimp only [GenusZero] at h ⊢
  rw [←hC,←hV,←hF,hE]
  exact h
end TorsionFreeZeroDivisors.MapConjugation

/-! The finite matching operation for the same-lifted-edge band surgery.
Deleting two inverse occurrences splices their partners unless they were already
paired. Labels, involutivity and the absence of fixed points are proved from the
actual matching. This file does not assert a surface realization or essentiality.
-/
namespace TorsionFreeZeroDivisors.MatchingSurgery
open scoped Classical
variable {O A : Type*} (α : Equiv.Perm O) (hi : Function.Involutive α)
  (hf : ∀x,α x≠x) (p q : O) (hpq : p≠q)

abbrev Remaining := {x : O // x≠p ∧ x≠q}
def splice (x : O) : O := if α x=p then α q else if α x=q then α p else α x

include hi hf in
lemma splice_avoids (x : Remaining p q) : splice α p q x≠p ∧ splice α p q x≠q := by
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    have hqp : α q≠p := by
      intro h
      have h' : q=α p := (hi _).symm.trans (congrArg α h)
      exact x.property.2 (hx ▸ h'.symm)
    rw [splice,ite_eq_left h1]
    exact ⟨hqp,hf q⟩
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      have hpq' : α p≠q := by
        intro h
        have h' : p=α q := (hi _).symm.trans (congrArg α h)
        exact x.property.1 (hx ▸ h'.symm)
      rw [splice,ite_eq_right h1,ite_eq_left h2]
      exact ⟨hf p,hpq'⟩
    · rw [splice,ite_eq_right h1,ite_eq_right h2]
      exact ⟨h1,h2⟩

def apply (x : Remaining p q) : Remaining p q := ⟨splice α p q x,splice_avoids α hi hf p q x⟩

include hpq in
lemma involutive : Function.Involutive (apply α hi hf p q) := by
  intro x
  apply Subtype.ext
  change splice α p q (splice α p q x)=x
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    have hs : splice α p q x=α q := by rw [splice,ite_eq_left h1]
    rw [hs,splice,hi q,ite_eq_right hpq.symm,ite_eq_left rfl]
    exact hx
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      have hs : splice α p q x=α p := by rw [splice,ite_eq_right h1,ite_eq_left h2]
      rw [hs,splice,hi p,ite_eq_left rfl]
      exact hx
    · have hs : splice α p q x=α x := by rw [splice,ite_eq_right h1,ite_eq_right h2]
      rw [hs,splice,hi x,ite_eq_right x.property.1,ite_eq_right x.property.2]

include hpq in
lemma distinct (x : Remaining p q) : apply α hi hf p q x≠x := by
  intro he
  have he := congrArg Subtype.val he
  change splice α p q x=x at he
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    rw [splice,ite_eq_left h1] at he
    exact hpq (α.injective (hx.trans he.symm))
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      rw [splice,ite_eq_right h1,ite_eq_left h2] at he
      exact hpq (α.injective (he.trans hx.symm))
    · exact hf x (by simpa [splice,h1,h2] using he)

def partner : Equiv.Perm (Remaining p q) := ⟨apply α hi hf p q,apply α hi hf p q,involutive α hi hf p q hpq,involutive α hi hf p q hpq⟩

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))
include hinv hl hlabel in
lemma compatible (x : Remaining p q) :
    label (partner α hi hf p q hpq x)=inv (label x) := by
  change label (splice α p q x)=_
  by_cases h1 : α x=p
  · rw [splice,ite_eq_left h1,hl,hlabel,hinv]
    exact (congrArg label h1).symm.trans (hl x)
  · by_cases h2 : α x=q
    · rw [splice,ite_eq_right h1,ite_eq_left h2,hl,←hlabel]
      exact (congrArg label h2).symm.trans (hl x)
    · rw [splice,ite_eq_right h1,ite_eq_right h2,hl]

end TorsionFreeZeroDivisors.MatchingSurgery
namespace TorsionFreeZeroDivisors.Smoothing
open scoped Classical
open DeleteCycle
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (hf : ∀x,α x≠x)
  (p q : O) (hpq : p≠q) (hsp : σ p=q) (hsq : σ q=p)

include hsp hsq in
lemma rotation_invariant (x : O) : (σ x≠p ∧ σ x≠q) ↔ (x≠p ∧ x≠q) := by
  constructor
  · rintro ⟨hp,hq⟩
    exact ⟨fun h=>hq (h ▸ hsp),fun h=>hp (h ▸ hsq)⟩
  · rintro ⟨hp,hq⟩
    exact ⟨fun h=>hq (σ.injective (h.trans hsq.symm)),fun h=>hp (σ.injective (h.trans hsp.symm))⟩
def rotation : Equiv.Perm (MatchingSurgery.Remaining p q) :=
  σ.subtypePerm (rotation_invariant σ p q hsp hsq)

abbrev r := α p
include hf in
lemma pr : p≠r α p := (hf p).symm
include hf hpq in
lemma rename_invariant (x : O) :
    (Equiv.swap q (r α p) x≠p ∧ Equiv.swap q (r α p) x≠q) ↔ (x≠p ∧ x≠r α p) := by
  have hp : Equiv.swap q (r α p) p=p := Equiv.swap_apply_of_ne_of_ne hpq (pr α hf p)
  have hr : Equiv.swap q (r α p) (r α p)=q := Equiv.swap_apply_right _ _
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨fun h=>h1 (h ▸ hp),fun h=>h2 (h ▸ hr)⟩
  · rintro ⟨h1,h2⟩
    exact ⟨fun h=>h1 ((Equiv.swap q (r α p)).injective (h.trans hp.symm)),
      fun h=>h2 ((Equiv.swap q (r α p)).injective (h.trans hr.symm))⟩
def flatten : BandEuler.Residual p (r α p) (pr α hf p) ≃ MatchingSurgery.Remaining p (r α p) where
  toFun x := ⟨BandEuler.val p (r α p) (pr α hf p) x,
    BandEuler.val_ne_p p (r α p) (pr α hf p) x,BandEuler.val_ne_q p (r α p) (pr α hf p) x⟩
  invFun x := ⟨⟨x,x.property.1⟩,fun he=>x.property.2 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl
def rename : MatchingSurgery.Remaining p (r α p) ≃ MatchingSurgery.Remaining p q :=
  (Equiv.swap q (r α p)).subtypeEquiv (fun x=>(rename_invariant α hf p q hpq x).symm)
def coordinates : BandEuler.Residual p (r α p) (pr α hf p) ≃ MatchingSurgery.Remaining p q :=
  (flatten α hf p).trans (rename α hf p q hpq)
lemma coordinates_val (x : BandEuler.Residual p (r α p) (pr α hf p)) :
    (coordinates α hf p q hpq x).val=Equiv.swap q (r α p) (BandEuler.val p (r α p) (pr α hf p) x) := rfl

lemma partner_commutes (x : BandEuler.Residual p (r α p) (pr α hf p)) :
    coordinates α hf p q hpq (BandEuler.partner α hi p (r α p) (pr α hf p) rfl x)=
      MatchingSurgery.partner α hi hf p q hpq (coordinates α hf p q hpq x) := by
  apply Subtype.ext
  rw [coordinates_val,BandEuler.partner_val]
  change Equiv.swap q (α p) (α (BandEuler.val p (α p) (pr α hf p) x))=
    MatchingSurgery.splice α p q (Equiv.swap q (α p) (BandEuler.val p (α p) (pr α hf p) x))
  let v := BandEuler.val p (α p) (pr α hf p) x
  change Equiv.swap q (α p) (α v)=MatchingSurgery.splice α p q (Equiv.swap q (α p) v)
  have hvp : v≠p := BandEuler.val_ne_p _ _ _ x
  have hvr : v≠α p := BandEuler.val_ne_q _ _ _ x
  have havp : α v≠p := fun h=>hvr ((hi _).symm.trans (congrArg α h))
  have havr : α v≠α p := α.injective.ne hvp
  by_cases hvq : v=q
  · rw [hvq,Equiv.swap_apply_left,MatchingSurgery.splice,hi p,ite_eq_left rfl]
    have hαq : α q≠q := hf q
    have hαqr : α q≠α p := α.injective.ne hpq.symm
    exact Equiv.swap_apply_of_ne_of_ne hαq hαqr
  · rw [Equiv.swap_apply_of_ne_of_ne hvq hvr,MatchingSurgery.splice,ite_eq_right havp]
    by_cases havq : α v=q
    · rw [ite_eq_left havq,havq,Equiv.swap_apply_left]
    · rw [ite_eq_right havq,Equiv.swap_apply_of_ne_of_ne havq havr]

lemma bypass_value (f : Equiv.Perm O) (a : O) (x : Rest a) :
    (bypass f a x).val=if f x=a then f a else f x := by
  change Equiv.swap a (f a) (f x)=_
  by_cases h : f x=a
  · rw [ite_eq_left h,h,Equiv.swap_apply_left]
  · rw [ite_eq_right h,Equiv.swap_apply_of_ne_of_ne h (f.injective.ne x.property)]
lemma rotation_value (a b : O) (hab : a≠b) (x : BandEuler.Residual a b hab) :
    BandEuler.val a b hab (BandEuler.rotation σ a b hab x)=
      let f := BandEuler.switched σ a b
      let g := fun y=>if f y=a then f a else f y
      if g (BandEuler.val a b hab x)=b then g b else g (BandEuler.val a b hab x) := by
  let f := BandEuler.switched σ a b
  let g := fun y=>if f y=a then f a else f y
  change ((bypass (bypass f a) (BandEuler.q' a b hab) x).val).val=
    if g x.val.val=b then g b else g x.val.val
  have he : bypass f a x.val=BandEuler.q' a b hab ↔ g x.val.val=b := by
    rw [Subtype.ext_iff,bypass_value]
  by_cases hc : g x.val.val=b
  · rw [ite_eq_left hc]
    have hv := bypass_value (bypass f a) (BandEuler.q' a b hab) x
    rw [ite_eq_left (he.mpr hc)] at hv
    exact (congrArg Subtype.val hv).trans (bypass_value f a (BandEuler.q' a b hab))
  · rw [ite_eq_right hc]
    have hv := bypass_value (bypass f a) (BandEuler.q' a b hab) x
    rw [ite_eq_right (fun h=>hc (he.mp h))] at hv
    exact (congrArg Subtype.val hv).trans (bypass_value f a x.val)

include hsp hsq hpq in
lemma smoothing_value (r v : O) (hpr : p≠r) (hvp : v≠p) (hvr : v≠r) :
    let f := Equiv.swap p r*σ
    let g := fun y=>if f y=p then f p else f y
    Equiv.swap q r (if g v=r then g r else g v)=σ (Equiv.swap q r v) := by
  let f := Equiv.swap p r*σ
  let g := fun y=>if f y=p then f p else f y
  change Equiv.swap q r (if g v=r then g r else g v)=_
  by_cases hqr : q=r
  · subst r
    have hsvp : σ v≠p := fun h=>hvr (σ.injective (h.trans hsq.symm))
    have hsvq : σ v≠q := fun h=>hvp (σ.injective (h.trans hsp.symm))
    have hfv : f v=σ v := Equiv.swap_apply_of_ne_of_ne hsvp hsvq
    have hg : g v=σ v := by
      change (if f v=p then f p else f v)=σ v
      simp only [hfv,ite_eq_right hsvp]
    rw [hg,ite_eq_right hsvq,Equiv.swap_self]
    rfl
  · have hfp : f p=q := by
      dsimp only [f,Equiv.Perm.mul_apply]
      rw [hsp,Equiv.swap_apply_of_ne_of_ne hpq.symm hqr]
    have hG (y : O) (hyp : y≠p) (hyq : y≠q) : Equiv.swap q r (g y)=σ y := by
      have hsyp : σ y≠p := fun h=>hyq (σ.injective (h.trans hsq.symm))
      have hsyq : σ y≠q := fun h=>hyp (σ.injective (h.trans hsp.symm))
      by_cases hsyr : σ y=r
      · have hfy : f y=p := by simp only [f,Equiv.Perm.mul_apply,hsyr,Equiv.swap_apply_right]
        change Equiv.swap q r (if f y=p then f p else f y)=σ y
        rw [ite_eq_left hfy,hfp,Equiv.swap_apply_left,hsyr]
      · have hfy : f y=σ y := by
          exact Equiv.swap_apply_of_ne_of_ne hsyp hsyr
        change Equiv.swap q r (if f y=p then f p else f y)=σ y
        simp only [hfy,ite_eq_right hsyp,Equiv.swap_apply_of_ne_of_ne hsyq hsyr]
    by_cases hvq : v=q
    · have hfq : f q=r := by simp only [f,Equiv.Perm.mul_apply,hsq,Equiv.swap_apply_left]
      have hgq : g q=r := by
        change (if f q=p then f p else f q)=r
        simp only [hfq,ite_eq_right hpr.symm]
      rw [hvq,hgq,ite_eq_left rfl,Equiv.swap_apply_left]
      exact hG r hpr.symm (Ne.symm hqr)
    · have hgv : g v≠r := by
        intro he
        have hh := hG v hvp hvq
        rw [he,Equiv.swap_apply_right] at hh
        exact hvp (σ.injective (hh.symm.trans hsp.symm))
      rw [ite_eq_right hgv,Equiv.swap_apply_of_ne_of_ne hvq hvr]
      exact hG v hvp hvq

lemma rotation_commutes (x : BandEuler.Residual p (r α p) (pr α hf p)) :
    coordinates α hf p q hpq (BandEuler.rotation σ p (r α p) (pr α hf p) x)=
      rotation σ p q hsp hsq (coordinates α hf p q hpq x) := by
  apply Subtype.ext
  rw [coordinates_val,rotation_value]
  exact smoothing_value σ p q hpq hsp hsq (r α p)
    (BandEuler.val p (r α p) (pr α hf p) x) (pr α hf p)
    (BandEuler.val_ne_p _ _ _ x) (BandEuler.val_ne_q _ _ _ x)

variable [Fintype O]
/-- Suppressing an actual two-occurrence boundary splices its matching partners,
including the already-paired case, and preserves combinatorial genus zero. -/
theorem genusZero (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero (rotation σ p q hsp hsq)
      (MatchingSurgery.partner α hi hf p q hpq) := by
  let e := coordinates α hf p q hpq
  let σ₀ := BandEuler.rotation σ p (r α p) (pr α hf p)
  let α₀ := BandEuler.partner α hi p (r α p) (pr α hf p) rfl
  have hz₀ : MapEuler.GenusZero σ₀ α₀ := BandEuler.genusZero_all σ α hi p
    (r α p) (pr α hf p) rfl hz
  have h := MapConjugation.genusZero e σ₀ α₀ hz₀
  have hσ : e.permCongr σ₀=rotation σ p q hsp hsq := by
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    exact rotation_commutes σ α hf p q hpq hsp hsq x
  have hα : e.permCongr α₀=MatchingSurgery.partner α hi hf p q hpq := by
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    exact partner_commutes α hi hf p q hpq x
  rwa [hσ,hα] at h

end TorsionFreeZeroDivisors.Smoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
open PermutationCycles
variable {O V : Type} (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)
def isolate : Equiv.Perm O := Equiv.swap p (σ q)*σ
include hpq hsp in
lemma q_ne_next : q≠σ q := fun h=>hpq (σ.injective (hsp.trans h))
include hpq hsp in
lemma isolate_p : isolate σ p q p=q := by
  change Equiv.swap p (σ q) (σ p)=q
  rw [hsp,Equiv.swap_apply_of_ne_of_ne hpq.symm (q_ne_next σ p q hpq hsp)]
lemma isolate_q : isolate σ p q q=p := Equiv.swap_apply_right _ _
def rotation : Equiv.Perm (MatchingSurgery.Remaining p q) :=
  Smoothing.rotation (isolate σ p q) p q (isolate_p σ p q hpq hsp) (isolate_q σ p q)

variable [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (hf : ∀x,α x≠x)
include hsp hi in
lemma isolate_genusZero (hz : MapEuler.GenusZero σ α) : MapEuler.GenusZero (isolate σ p q) α := by
  by_cases he : p=σ q
  · have hs : isolate σ p q=σ := by rw [isolate,←he,Equiv.swap_self];rfl
    rwa [hs]
  · apply MapEuler.genusZero_vertexSplit σ α hi hz p (σ q) he
    rw [cycle_apply,←hsp,cycle_apply]
/-- Deleting an actual adjacent backtracking pair from its boundary, with the
forced partner splice, preserves genus zero even if the two occurrences were
not paired. This supplies the finite-map part of cyclic tightening. -/
theorem genusZero (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero (rotation σ p q hpq hsp) (MatchingSurgery.partner α hi hf p q hpq) :=
  Smoothing.genusZero (isolate σ p q) α hi hf p q hpq
    (isolate_p σ p q hpq hsp) (isolate_q σ p q) (isolate_genusZero σ p q hsp α hi hz)

variable (before after : O→V)
omit [Fintype O] in
/-- The graph endpoint conditions, not just the rose labels, survive the
backtracking deletion. The second occurrence really returns to the first
occurrence's starting vertex. -/
theorem consistent (h : BoundarySurgery.Consistent σ before after) (hq : after q=before p) :
    BoundarySurgery.Consistent (rotation σ p q hpq hsp)
      (fun x=>before x) (fun x=>after x) := by
  have he : before p=before (σ q) := hq.symm.trans (h q)
  intro x
  change after (x : O)=before (Equiv.swap p (σ q) (σ x))
  rw [MapEuler.swap_invariant before p (σ q) he]
  exact h x
omit [Fintype O] in
lemma marker_nonfixed (h : BoundarySurgery.Consistent σ before after) (hq : after q=before p)
    (m : MatchingSurgery.Remaining p q) (hm : after m≠before m) :
    rotation σ p q hpq hsp m≠m := by
  intro he
  have hh := consistent σ p q hpq hsp before after h hq m
  rw [he] at hh
  exact hm hh
end TorsionFreeZeroDivisors.Tightening

/-! The finite matching operation for the same-lifted-edge band surgery.
Deleting two inverse occurrences splices their partners unless they were already
paired. Labels, involutivity and the absence of fixed points are proved from the
actual matching. This file does not assert a surface realization or essentiality.
-/
namespace TorsionFreeZeroDivisors.PartialMatchingSurgery
open scoped Classical
variable {O A : Type*} (α : Equiv.Perm O) (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q)

abbrev Remaining := {x : O // x≠p ∧ x≠q}
def splice (x : O) : O := if α x=p then α q else if α x=q then α p else α x

include hi hfp hfq in
lemma splice_avoids (x : Remaining p q) : splice α p q x≠p ∧ splice α p q x≠q := by
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    have hqp : α q≠p := by
      intro h
      have h' : q=α p := (hi _).symm.trans (congrArg α h)
      exact x.property.2 (hx ▸ h'.symm)
    rw [splice,ite_eq_left h1]
    exact ⟨hqp,hfq⟩
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      have hpq' : α p≠q := by
        intro h
        have h' : p=α q := (hi _).symm.trans (congrArg α h)
        exact x.property.1 (hx ▸ h'.symm)
      rw [splice,ite_eq_right h1,ite_eq_left h2]
      exact ⟨hfp,hpq'⟩
    · rw [splice,ite_eq_right h1,ite_eq_right h2]
      exact ⟨h1,h2⟩

def apply (x : Remaining p q) : Remaining p q := ⟨splice α p q x,splice_avoids α hi p q hfp hfq x⟩

include hpq in
lemma involutive : Function.Involutive (apply α hi p q hfp hfq) := by
  intro x
  apply Subtype.ext
  change splice α p q (splice α p q x)=x
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    have hs : splice α p q x=α q := by rw [splice,ite_eq_left h1]
    rw [hs,splice,hi q,ite_eq_right hpq.symm,ite_eq_left rfl]
    exact hx
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      have hs : splice α p q x=α p := by rw [splice,ite_eq_right h1,ite_eq_left h2]
      rw [hs,splice,hi p,ite_eq_left rfl]
      exact hx
    · have hs : splice α p q x=α x := by rw [splice,ite_eq_right h1,ite_eq_right h2]
      rw [hs,splice,hi x,ite_eq_right x.property.1,ite_eq_right x.property.2]

include hpq in
lemma distinct (x : Remaining p q) (hfx : α x≠x) : apply α hi p q hfp hfq x≠x := by
  intro he
  have he := congrArg Subtype.val he
  change splice α p q x=x at he
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    rw [splice,ite_eq_left h1] at he
    exact hpq (α.injective (hx.trans he.symm))
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      rw [splice,ite_eq_right h1,ite_eq_left h2] at he
      exact hpq (α.injective (he.trans hx.symm))
    · exact hfx (by simpa [splice,h1,h2] using he)

def partner : Equiv.Perm (Remaining p q) := ⟨apply α hi p q hfp hfq,apply α hi p q hfp hfq,involutive α hi p q hpq hfp hfq,involutive α hi p q hpq hfp hfq⟩

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))
include hinv hl hlabel in
lemma compatible (x : Remaining p q) :
    label (partner α hi p q hpq hfp hfq x)=inv (label x) := by
  change label (splice α p q x)=_
  by_cases h1 : α x=p
  · rw [splice,ite_eq_left h1,hl,hlabel,hinv]
    exact (congrArg label h1).symm.trans (hl x)
  · by_cases h2 : α x=q
    · rw [splice,ite_eq_right h1,ite_eq_left h2,hl,←hlabel]
      exact (congrArg label h2).symm.trans (hl x)
    · rw [splice,ite_eq_right h1,ite_eq_right h2,hl]

lemma fixed (x : Remaining p q) (hx : α x=x) : partner α hi p q hpq hfp hfq x=x := by
  apply Subtype.ext
  change splice α p q x=x
  rw [splice,hx,ite_eq_right x.property.1,ite_eq_right x.property.2]

end TorsionFreeZeroDivisors.PartialMatchingSurgery
namespace TorsionFreeZeroDivisors.PartialSmoothing
open scoped Classical
open DeleteCycle
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q) (hsp : σ p=q) (hsq : σ q=p)

include hsp hsq in
lemma rotation_invariant (x : O) : (σ x≠p ∧ σ x≠q) ↔ (x≠p ∧ x≠q) := by
  constructor
  · rintro ⟨hp,hq⟩
    exact ⟨fun h=>hq (h ▸ hsp),fun h=>hp (h ▸ hsq)⟩
  · rintro ⟨hp,hq⟩
    exact ⟨fun h=>hq (σ.injective (h.trans hsq.symm)),fun h=>hp (σ.injective (h.trans hsp.symm))⟩
def rotation : Equiv.Perm (PartialMatchingSurgery.Remaining p q) :=
  σ.subtypePerm (rotation_invariant σ p q hsp hsq)

abbrev r := α p
include hfp in
lemma pr : p≠r α p := (hfp).symm
include hfp hpq in
lemma rename_invariant (x : O) :
    (Equiv.swap q (r α p) x≠p ∧ Equiv.swap q (r α p) x≠q) ↔ (x≠p ∧ x≠r α p) := by
  have hp : Equiv.swap q (r α p) p=p := Equiv.swap_apply_of_ne_of_ne hpq (pr α p hfp)
  have hr : Equiv.swap q (r α p) (r α p)=q := Equiv.swap_apply_right _ _
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨fun h=>h1 (h ▸ hp),fun h=>h2 (h ▸ hr)⟩
  · rintro ⟨h1,h2⟩
    exact ⟨fun h=>h1 ((Equiv.swap q (r α p)).injective (h.trans hp.symm)),
      fun h=>h2 ((Equiv.swap q (r α p)).injective (h.trans hr.symm))⟩
def flatten : BandEuler.Residual p (r α p) (pr α p hfp) ≃ PartialMatchingSurgery.Remaining p (r α p) where
  toFun x := ⟨BandEuler.val p (r α p) (pr α p hfp) x,
    BandEuler.val_ne_p p (r α p) (pr α p hfp) x,BandEuler.val_ne_q p (r α p) (pr α p hfp) x⟩
  invFun x := ⟨⟨x,x.property.1⟩,fun he=>x.property.2 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl
def rename : PartialMatchingSurgery.Remaining p (r α p) ≃ PartialMatchingSurgery.Remaining p q :=
  (Equiv.swap q (r α p)).subtypeEquiv (fun x=>(rename_invariant α p q hpq hfp x).symm)
def coordinates : BandEuler.Residual p (r α p) (pr α p hfp) ≃ PartialMatchingSurgery.Remaining p q :=
  (flatten α p hfp).trans (rename α p q hpq hfp)
lemma coordinates_val (x : BandEuler.Residual p (r α p) (pr α p hfp)) :
    (coordinates α p q hpq hfp x).val=Equiv.swap q (r α p) (BandEuler.val p (r α p) (pr α p hfp) x) := rfl

lemma partner_commutes (x : BandEuler.Residual p (r α p) (pr α p hfp)) :
    coordinates α p q hpq hfp (BandEuler.partner α hi p (r α p) (pr α p hfp) rfl x)=
      PartialMatchingSurgery.partner α hi p q hpq hfp hfq (coordinates α p q hpq hfp x) := by
  apply Subtype.ext
  rw [coordinates_val,BandEuler.partner_val]
  change Equiv.swap q (α p) (α (BandEuler.val p (α p) (pr α p hfp) x))=
    PartialMatchingSurgery.splice α p q (Equiv.swap q (α p) (BandEuler.val p (α p) (pr α p hfp) x))
  let v := BandEuler.val p (α p) (pr α p hfp) x
  change Equiv.swap q (α p) (α v)=PartialMatchingSurgery.splice α p q (Equiv.swap q (α p) v)
  have hvp : v≠p := BandEuler.val_ne_p _ _ _ x
  have hvr : v≠α p := BandEuler.val_ne_q _ _ _ x
  have havp : α v≠p := fun h=>hvr ((hi _).symm.trans (congrArg α h))
  have havr : α v≠α p := α.injective.ne hvp
  by_cases hvq : v=q
  · rw [hvq,Equiv.swap_apply_left,PartialMatchingSurgery.splice,hi p,ite_eq_left rfl]
    have hαq : α q≠q := hfq
    have hαqr : α q≠α p := α.injective.ne hpq.symm
    exact Equiv.swap_apply_of_ne_of_ne hαq hαqr
  · rw [Equiv.swap_apply_of_ne_of_ne hvq hvr,PartialMatchingSurgery.splice,ite_eq_right havp]
    by_cases havq : α v=q
    · rw [ite_eq_left havq,havq,Equiv.swap_apply_left]
    · rw [ite_eq_right havq,Equiv.swap_apply_of_ne_of_ne havq havr]

lemma bypass_value (f : Equiv.Perm O) (a : O) (x : Rest a) :
    (bypass f a x).val=if f x=a then f a else f x := by
  change Equiv.swap a (f a) (f x)=_
  by_cases h : f x=a
  · rw [ite_eq_left h,h,Equiv.swap_apply_left]
  · rw [ite_eq_right h,Equiv.swap_apply_of_ne_of_ne h (f.injective.ne x.property)]
lemma rotation_value (a b : O) (hab : a≠b) (x : BandEuler.Residual a b hab) :
    BandEuler.val a b hab (BandEuler.rotation σ a b hab x)=
      let f := BandEuler.switched σ a b
      let g := fun y=>if f y=a then f a else f y
      if g (BandEuler.val a b hab x)=b then g b else g (BandEuler.val a b hab x) := by
  let f := BandEuler.switched σ a b
  let g := fun y=>if f y=a then f a else f y
  change ((bypass (bypass f a) (BandEuler.q' a b hab) x).val).val=
    if g x.val.val=b then g b else g x.val.val
  have he : bypass f a x.val=BandEuler.q' a b hab ↔ g x.val.val=b := by
    rw [Subtype.ext_iff,bypass_value]
  by_cases hc : g x.val.val=b
  · rw [ite_eq_left hc]
    have hv := bypass_value (bypass f a) (BandEuler.q' a b hab) x
    rw [ite_eq_left (he.mpr hc)] at hv
    exact (congrArg Subtype.val hv).trans (bypass_value f a (BandEuler.q' a b hab))
  · rw [ite_eq_right hc]
    have hv := bypass_value (bypass f a) (BandEuler.q' a b hab) x
    rw [ite_eq_right (fun h=>hc (he.mp h))] at hv
    exact (congrArg Subtype.val hv).trans (bypass_value f a x.val)

include hsp hsq hpq in
lemma smoothing_value (r v : O) (hpr : p≠r) (hvp : v≠p) (hvr : v≠r) :
    let f := Equiv.swap p r*σ
    let g := fun y=>if f y=p then f p else f y
    Equiv.swap q r (if g v=r then g r else g v)=σ (Equiv.swap q r v) := by
  let f := Equiv.swap p r*σ
  let g := fun y=>if f y=p then f p else f y
  change Equiv.swap q r (if g v=r then g r else g v)=_
  by_cases hqr : q=r
  · subst r
    have hsvp : σ v≠p := fun h=>hvr (σ.injective (h.trans hsq.symm))
    have hsvq : σ v≠q := fun h=>hvp (σ.injective (h.trans hsp.symm))
    have hfv : f v=σ v := Equiv.swap_apply_of_ne_of_ne hsvp hsvq
    have hg : g v=σ v := by
      change (if f v=p then f p else f v)=σ v
      simp only [hfv,ite_eq_right hsvp]
    rw [hg,ite_eq_right hsvq,Equiv.swap_self]
    rfl
  · have hfp : f p=q := by
      dsimp only [f,Equiv.Perm.mul_apply]
      rw [hsp,Equiv.swap_apply_of_ne_of_ne hpq.symm hqr]
    have hG (y : O) (hyp : y≠p) (hyq : y≠q) : Equiv.swap q r (g y)=σ y := by
      have hsyp : σ y≠p := fun h=>hyq (σ.injective (h.trans hsq.symm))
      have hsyq : σ y≠q := fun h=>hyp (σ.injective (h.trans hsp.symm))
      by_cases hsyr : σ y=r
      · have hfy : f y=p := by simp only [f,Equiv.Perm.mul_apply,hsyr,Equiv.swap_apply_right]
        change Equiv.swap q r (if f y=p then f p else f y)=σ y
        rw [ite_eq_left hfy,hfp,Equiv.swap_apply_left,hsyr]
      · have hfy : f y=σ y := by
          exact Equiv.swap_apply_of_ne_of_ne hsyp hsyr
        change Equiv.swap q r (if f y=p then f p else f y)=σ y
        simp only [hfy,ite_eq_right hsyp,Equiv.swap_apply_of_ne_of_ne hsyq hsyr]
    by_cases hvq : v=q
    · have hfq : f q=r := by simp only [f,Equiv.Perm.mul_apply,hsq,Equiv.swap_apply_left]
      have hgq : g q=r := by
        change (if f q=p then f p else f q)=r
        simp only [hfq,ite_eq_right hpr.symm]
      rw [hvq,hgq,ite_eq_left rfl,Equiv.swap_apply_left]
      exact hG r hpr.symm (Ne.symm hqr)
    · have hgv : g v≠r := by
        intro he
        have hh := hG v hvp hvq
        rw [he,Equiv.swap_apply_right] at hh
        exact hvp (σ.injective (hh.symm.trans hsp.symm))
      rw [ite_eq_right hgv,Equiv.swap_apply_of_ne_of_ne hvq hvr]
      exact hG v hvp hvq

lemma rotation_commutes (x : BandEuler.Residual p (r α p) (pr α p hfp)) :
    coordinates α p q hpq hfp (BandEuler.rotation σ p (r α p) (pr α p hfp) x)=
      rotation σ p q hsp hsq (coordinates α p q hpq hfp x) := by
  apply Subtype.ext
  rw [coordinates_val,rotation_value]
  exact smoothing_value σ p q hpq hsp hsq (r α p)
    (BandEuler.val p (r α p) (pr α p hfp) x) (pr α p hfp)
    (BandEuler.val_ne_p _ _ _ x) (BandEuler.val_ne_q _ _ _ x)

variable [Fintype O]
/-- Suppressing an actual two-occurrence boundary splices its matching partners,
including the already-paired case, and preserves combinatorial genus zero. -/
theorem genusZero (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero (rotation σ p q hsp hsq)
      (PartialMatchingSurgery.partner α hi p q hpq hfp hfq) := by
  let e := coordinates α p q hpq hfp
  let σ₀ := BandEuler.rotation σ p (r α p) (pr α p hfp)
  let α₀ := BandEuler.partner α hi p (r α p) (pr α p hfp) rfl
  have hz₀ : MapEuler.GenusZero σ₀ α₀ := BandEuler.genusZero_all σ α hi p
    (r α p) (pr α p hfp) rfl hz
  have h := MapConjugation.genusZero e σ₀ α₀ hz₀
  have hσ : e.permCongr σ₀=rotation σ p q hsp hsq := by
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    exact rotation_commutes σ α p q hpq hfp hsp hsq x
  have hα : e.permCongr α₀=PartialMatchingSurgery.partner α hi p q hpq hfp hfq := by
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    exact partner_commutes α hi p q hpq hfp hfq x
  rwa [hσ,hα] at h

end TorsionFreeZeroDivisors.PartialSmoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
variable {O : Type} [Fintype O] (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)
  (α : Equiv.Perm O) (hi : Function.Involutive α) (hfp : α p≠p) (hfq : α q≠q)
/-- The tightening operation also allows unrelated unpaired markers. Only the
actual two deleted letter occurrences are required to be nonfixed. -/
theorem partial_genusZero (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero (rotation σ p q hpq hsp)
      (PartialMatchingSurgery.partner α hi p q hpq hfp hfq) :=
  PartialSmoothing.genusZero (isolate σ p q) α hi p q hpq hfp hfq
    (isolate_p σ p q hpq hsp) (isolate_q σ p q) (isolate_genusZero σ p q hsp α hi hz)
end TorsionFreeZeroDivisors.Tightening
namespace TorsionFreeZeroDivisors.FinitePicture
open scoped Classical
open PortSubdivision
variable {V D A O : Type} (Γ : PortGraph V D) (label : D→A) (inv : A→A) (x y : V) [Fintype O]
/-- A purely finite lifted boundary certificate. The single unpaired marker
records the break from the exterior endpoint y back to the prescribed root x.
No surface map, cone filling, essentiality, or CW realization is asserted. -/
structure Data where
  rotation : Equiv.Perm O
  partner : Equiv.Perm O
  involutive : Function.Involutive partner
  marker : O
  marker_fixed : partner marker=marker
  fixed_only : ∀ i,partner i=i → i=marker
  dart : O→Option D
  none_iff : ∀i,dart i=none ↔ i=marker
  before : O→V
  after : O→V
  begins : ∀i d,dart i=some d → before i=Γ.origin d
  ends : ∀i d,dart i=some d → after i=Γ.origin (Γ.reverse d)
  marker_before : before marker=y
  marker_after : after marker=x
  consistent : BoundarySurgery.Consistent rotation before after
  compatible : ∀i,(dart (partner i)).map label=(dart i).map (inv ∘ label)
  genusZero : MapEuler.GenusZero rotation partner
namespace Data
variable {Γ label inv x y} (a : Data (O:=O) Γ label inv x y)
lemma nonfixed {p : O} (hp : p≠a.marker) : a.partner p≠p := fun h=>hp (a.fixed_only p h)
lemma partner_ne_marker {p : O} (hp : p≠a.marker) : a.partner p≠a.marker :=
  fun h=>hp (a.partner.injective (h.trans a.marker_fixed.symm))
lemma swap_endpoints {p q : O} (hp : p≠a.marker)
    (he : a.dart q=(a.dart p).map Γ.reverse) :
    a.after p=a.before q ∧ a.after q=a.before p := by
  cases hd : a.dart p with
  | none => exact False.elim (hp ((a.none_iff p).mp hd))
  | some d =>
    have hq : a.dart q=some (Γ.reverse d) := by simpa only [hd,Option.map_some] using he
    constructor
    · rw [a.ends p d hd,a.begins q (Γ.reverse d) hq]
    · rw [a.ends q (Γ.reverse d) hq,Γ.reverse_reverse d,a.begins p d hd]
lemma marker_not_fixed_rotation (hxy : x≠y) : a.rotation a.marker≠a.marker := by
  intro h
  have hh := a.consistent a.marker
  rw [h,a.marker_before,a.marker_after] at hh
  exact hxy hh

variable {O' : Type} [Fintype O']
def reindex (e : O≃O') : Data (O:=O') Γ label inv x y where
  rotation := e.permCongr a.rotation
  partner := e.permCongr a.partner
  involutive := by
    intro i
    simp only [Equiv.permCongr_apply,e.symm_apply_apply]
    rw [a.involutive (e.symm i),e.apply_symm_apply]
  marker := e a.marker
  marker_fixed := by simp only [Equiv.permCongr_apply,e.symm_apply_apply,a.marker_fixed]
  fixed_only i hi := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    apply a.fixed_only
    have hh := congrArg e.symm hi
    simpa only [Equiv.permCongr_apply,e.symm_apply_apply] using hh
  dart i := a.dart (e.symm i)
  none_iff i := by
    rw [a.none_iff]
    exact ⟨fun h=>(e.apply_symm_apply i).symm.trans (congrArg e h),
      fun h=>(congrArg e.symm h).trans (e.symm_apply_apply a.marker)⟩
  before i := a.before (e.symm i)
  after i := a.after (e.symm i)
  begins i d h := a.begins _ d h
  ends i d h := a.ends _ d h
  marker_before := by rw [e.symm_apply_apply,a.marker_before]
  marker_after := by rw [e.symm_apply_apply,a.marker_after]
  consistent i := by simpa only [Equiv.permCongr_apply,e.symm_apply_apply] using a.consistent (e.symm i)
  compatible i := by simpa only [Equiv.permCongr_apply,e.symm_apply_apply] using a.compatible (e.symm i)
  genusZero := MapConjugation.genusZero e _ _ a.genusZero

variable (p q : O) (hpq : p≠q) (hp : p≠a.marker) (hq : q≠a.marker)
abbrev bandMarker : BandEuler.Residual p q hpq := ⟨⟨a.marker,hp.symm⟩,fun he=>hq (congrArg Subtype.val he).symm⟩
def band (hpair : a.partner p=q) (he : a.dart q=(a.dart p).map Γ.reverse) :
    Data (O:=BandEuler.Residual p q hpq) Γ label inv x y where
  rotation := BandEuler.rotation a.rotation p q hpq
  partner := BandEuler.partner a.partner a.involutive p q hpq hpair
  involutive := BandEuler.partner_involutive a.partner a.involutive p q hpq hpair
  marker := a.bandMarker p q hpq hp hq
  marker_fixed := by
    apply BandEuler.val_injective p q hpq
    rw [BandEuler.partner_val]
    exact a.marker_fixed
  fixed_only i hi := by
    apply BandEuler.val_injective p q hpq
    apply a.fixed_only
    have hh := congrArg (BandEuler.val p q hpq) hi
    rwa [BandEuler.partner_val] at hh
  dart i := a.dart (BandEuler.val p q hpq i)
  none_iff i := by
    rw [a.none_iff]
    exact ⟨fun h=>BandEuler.val_injective p q hpq h,fun h=>congrArg (BandEuler.val p q hpq) h⟩
  before i := a.before (BandEuler.val p q hpq i)
  after i := a.after (BandEuler.val p q hpq i)
  begins i d h := a.begins _ d h
  ends i d h := a.ends _ d h
  marker_before := a.marker_before
  marker_after := a.marker_after
  consistent := BoundarySurgery.consistent a.rotation a.before a.after p q hpq a.consistent
    (a.swap_endpoints hp he).1 (a.swap_endpoints hp he).2
  compatible i := by
    rw [BandEuler.partner_val]
    exact a.compatible _
  genusZero := BandEuler.genusZero_all a.rotation a.partner a.involutive p q hpq hpair a.genusZero

abbrev tightMarker : PartialMatchingSurgery.Remaining p q := ⟨a.marker,hp.symm,hq.symm⟩
lemma option_inverse (hinv : Function.Involutive inv) : Function.Involutive (Option.map inv) := by
  intro z
  cases z with
  | none => rfl
  | some z => simp only [Option.map_some,hinv z]
lemma option_compatible (i : O) :
    (a.dart (a.partner i)).map label=((a.dart i).map label).map inv := by
  rw [Option.map_map]
  exact a.compatible i
lemma option_backtrack (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
    (he : a.dart q=(a.dart p).map Γ.reverse) :
    (a.dart q).map label=((a.dart p).map label).map inv := by
  rw [he,Option.map_map,Option.map_map]
  congr 1
  exact funext hlabel
/-- The actual adjacent reverse-edge deletion with the forced partner splice.
In contrast to the paired band move, p and q need not be partners. -/
def tighten (hinv : Function.Involutive inv)
    (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
    (hsp : a.rotation p=q) (he : a.dart q=(a.dart p).map Γ.reverse) :
    Data (O:=PartialMatchingSurgery.Remaining p q) Γ label inv x y where
  rotation := Tightening.rotation a.rotation p q hpq hsp
  partner := PartialMatchingSurgery.partner a.partner a.involutive p q hpq (a.nonfixed hp) (a.nonfixed hq)
  involutive := PartialMatchingSurgery.involutive a.partner a.involutive p q hpq (a.nonfixed hp) (a.nonfixed hq)
  marker := a.tightMarker p q hp hq
  marker_fixed := PartialMatchingSurgery.fixed a.partner a.involutive p q hpq (a.nonfixed hp) (a.nonfixed hq)
    (a.tightMarker p q hp hq) a.marker_fixed
  fixed_only i hi := by
    apply Subtype.ext
    by_contra h
    exact PartialMatchingSurgery.distinct a.partner a.involutive p q hpq (a.nonfixed hp) (a.nonfixed hq)
      i (a.nonfixed h) hi
  dart i := a.dart i
  none_iff i := by
    rw [a.none_iff]
    exact ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
  before i := a.before i
  after i := a.after i
  begins i d h := a.begins _ d h
  ends i d h := a.ends _ d h
  marker_before := a.marker_before
  marker_after := a.marker_after
  consistent := Tightening.consistent a.rotation p q hpq hsp a.before a.after a.consistent
    (a.swap_endpoints hp he).2
  compatible i := by
    have h := PartialMatchingSurgery.compatible a.partner a.involutive p q hpq (a.nonfixed hp) (a.nonfixed hq)
      (Option.map inv) (option_inverse hinv) (fun z=>(a.dart z).map label) a.option_compatible
      (a.option_backtrack p q hlabel he) i
    rw [Option.map_map] at h
    exact h
  genusZero := Tightening.partial_genusZero a.rotation p q hpq hsp a.partner a.involutive
    (a.nonfixed hp) (a.nonfixed hq) a.genusZero
include hp in
lemma unequal_backtrack (he : a.dart q=(a.dart p).map Γ.reverse) : p≠q := by
  intro h
  subst q
  cases hd : a.dart p with
  | none => exact hp ((a.none_iff p).mp hd)
  | some d =>
    have h' : d=Γ.reverse d := Option.some.inj (by simpa only [hd,Option.map_some] using he)
    exact Γ.reverse_ne d h'.symm
/-- Both kinds of shortening forbidden in a least marked finite certificate. -/
def Reduced : Prop :=
  (∀p,p≠a.marker → a.dart (a.partner p)≠(a.dart p).map Γ.reverse) ∧
  (∀p,p≠a.marker → a.rotation p≠a.marker → a.dart (a.rotation p)≠(a.dart p).map Γ.reverse)
def deletionCoordinates : BandEuler.Residual p q hpq ≃ PartialMatchingSurgery.Remaining p q where
  toFun z := ⟨BandEuler.val p q hpq z,BandEuler.val_ne_p p q hpq z,BandEuler.val_ne_q p q hpq z⟩
  invFun z := ⟨⟨z,z.property.1⟩,fun he=>z.property.2 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl
include hpq in
lemma remaining_two_fewer : Fintype.card (PartialMatchingSurgery.Remaining p q)+2=Fintype.card O := by
  rw [←Fintype.card_congr (deletionCoordinates p q hpq)]
  exact BandEuler.two_fewer p q hpq
theorem reduced_of_minimum (hinv : Function.Involutive inv)
    (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
    (hmin : ∀ {M : Type} [Fintype M],Data (O:=M) Γ label inv x y → Nat.card O≤Nat.card M) :
    a.Reduced := by
  constructor
  · intro p hp he
    let q := a.partner p
    have hq : q≠a.marker := a.partner_ne_marker hp
    have hpq : p≠q := (a.nonfixed hp).symm
    let c := a.band p q hpq hp hq rfl he
    have hc := BandEuler.two_fewer p q hpq
    have hm := hmin c
    simp only [←Nat.card_eq_fintype_card] at hc
    omega
  · intro p hp hq he
    let q := a.rotation p
    have hpq : p≠q := a.unequal_backtrack p q hp he
    let c := a.tighten p q hpq hp hq hinv hlabel rfl he
    have hc := remaining_two_fewer p q hpq
    have hm := hmin c
    simp only [←Nat.card_eq_fintype_card] at hc
    omega
include a in
/-- From an actual finite marked certificate obtain one with the same distinct
endpoints and with no same-lift paired band or adjacent backtracking. This is a
finite combinatorial reduction, not existence of a certificate for a null word. -/
theorem exists_reduced (hinv : Function.Involutive inv)
    (hlabel : ∀d,label (Γ.reverse d)=inv (label d)) :
    ∃n,n≤Fintype.card O ∧ ∃b : Data (O:=Fin n) Γ label inv x y,b.Reduced := by
  let P := fun n=>Nonempty (Data (O:=Fin n) Γ label inv x y)
  have hx : ∃n,P n := ⟨Fintype.card O,⟨a.reindex (Fintype.equivFin O)⟩⟩
  let n := Nat.find hx
  obtain ⟨b⟩ := Nat.find_spec hx
  have hn : n≤Fintype.card O := Nat.find_min' hx ⟨a.reindex (Fintype.equivFin O)⟩
  refine ⟨n,hn,b,b.reduced_of_minimum hinv hlabel ?_⟩
  intro M _ c
  have hm : n≤Fintype.card M := Nat.find_min' hx ⟨c.reindex (Fintype.equivFin M)⟩
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using hm
end Data
end TorsionFreeZeroDivisors.FinitePicture

namespace TorsionFreeZeroDivisors.PermutationCycles
open scoped Classical BigOperators
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
private lemma excess_identity {C : Type} [Fintype C] (len : C→ℕ) (hp : ∀ c,0<len c) :
    (∑ c,(len c-2))+2*Fintype.card C=(∑ c,len c)+
      (Finset.univ.filter (fun c => len c=1)).card := by
  calc
    _ = ∑ c,(len c-2+2) := by simp [Finset.sum_add_distrib,Nat.mul_comm]
    _ = ∑ c,(len c+if len c=1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro c _
      have h := hp c
      split_ifs <;> omega
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_boole,Nat.cast_id]
lemma twice_cycles_le : 2*Fintype.card (Cycle f)≤Fintype.card O+(fixed f).card := by
  have he := excess_identity (fun c=>(members f c).card)
    (fun c=>Finset.card_pos.mpr (members_nonempty f c))
  rw [sum_card] at he
  have hm := singleton_cycles_le_fixed f
  omega
end TorsionFreeZeroDivisors.PermutationCycles
namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
open DeleteCycle MapEuler PermutationCycles
variable {V D A O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D}
  {label : D→A} {inv : A→A} {x y : V} (a : Data (O:=O) Γ label inv x y)
abbrev Occ := Rest a.marker
def closedRotation : Equiv.Perm a.Occ := bypass a.rotation a.marker
def fullPartner : Equiv.Perm a.Occ := restrict a.partner a.marker a.marker_fixed
lemma fullPartner_val (i : a.Occ) : (a.fullPartner i).val=a.partner i := rfl
lemma fullPartner_involutive : Function.Involutive a.fullPartner := by
  intro i
  apply Subtype.ext
  exact a.involutive i
lemma fullPartner_nonfixed (i : a.Occ) : a.fullPartner i≠i := by
  intro he
  exact a.nonfixed i.property (congrArg Subtype.val he)
lemma dart_isSome (i : a.Occ) : (a.dart i).isSome := by
  apply Option.isSome_iff_ne_none.mpr
  exact fun he=>i.property ((a.none_iff i).mp he)
def edge (i : a.Occ) : D := (a.dart i).get (a.dart_isSome i)
lemma some_edge (i : a.Occ) : some (a.edge i)=a.dart i := Option.some_get _
lemma edge_begins (i : a.Occ) : a.before i=Γ.origin (a.edge i) := a.begins _ _ (a.some_edge i).symm
lemma edge_ends (i : a.Occ) : a.after i=Γ.origin (Γ.reverse (a.edge i)) := a.ends _ _ (a.some_edge i).symm
lemma edge_compatible (i : a.Occ) : label (a.edge (a.fullPartner i))=inv (label (a.edge i)) := by
  have h := a.compatible i
  change (a.dart (a.fullPartner i).val).map label=(a.dart i).map (inv ∘ label) at h
  rw [←a.some_edge (a.fullPartner i),←a.some_edge i] at h
  exact Option.some.inj h
variable (hxy : x≠y)
def first : a.Occ := ⟨a.rotation a.marker,a.marker_not_fixed_rotation hxy⟩
lemma first_start : Γ.origin (a.edge (a.first hxy))=x := by
  rw [←a.edge_begins]
  exact (a.consistent a.marker).symm.trans a.marker_after
lemma closedRotation_at_first (i : a.Occ) : a.closedRotation i=a.first hxy ↔ a.rotation i=a.marker := by
  constructor
  · intro he
    have hh := congrArg Subtype.val he
    change Equiv.swap a.marker (a.rotation a.marker) (a.rotation i)=a.rotation a.marker at hh
    exact (Equiv.swap a.marker (a.rotation a.marker)).injective
      (hh.trans (Equiv.swap_apply_left _ _).symm)
  · intro he
    apply Subtype.ext
    change Equiv.swap a.marker (a.rotation a.marker) (a.rotation i)=a.rotation a.marker
    rw [he,Equiv.swap_apply_left]
lemma closedRotation_val (i : a.Occ) (hi : a.closedRotation i≠a.first hxy) :
    (a.closedRotation i).val=a.rotation i := by
  have h₁ : a.rotation i≠a.marker := fun h=>hi ((a.closedRotation_at_first hxy i).mpr h)
  have h₂ : a.rotation i≠a.rotation a.marker := a.rotation.injective.ne i.property
  change Equiv.swap a.marker (a.rotation a.marker) (a.rotation i)=a.rotation i
  exact Equiv.swap_apply_of_ne_of_ne h₁ h₂
/-- All joins other than the unique root break are actual graph joins. -/
lemma edge_consistent (i : a.Occ) (hi : a.closedRotation i≠a.first hxy) :
    Γ.origin (Γ.reverse (a.edge i))=Γ.origin (a.edge (a.closedRotation i)) := by
  rw [←a.edge_ends,←a.edge_begins,a.closedRotation_val hxy i hi]
  exact a.consistent i
lemma last_end (i : a.Occ) (hi : a.closedRotation i=a.first hxy) :
    Γ.origin (Γ.reverse (a.edge i))=y := by
  rw [←a.edge_ends,a.consistent i,(a.closedRotation_at_first hxy i).mp hi,a.marker_before]
include hxy in
lemma closedRotation_genusZero : GenusZero a.closedRotation a.fullPartner :=
  MapDeletion.genusZero_delete a.rotation a.partner a.marker a.marker_fixed
    (a.marker_not_fixed_rotation hxy) a.genusZero
include hxy in
/-- The unmarked pairing is nonempty and has the literal sphere Euler bound.
This proves the scalar input needed by interval cutting, not a PL realization. -/
lemma closedRotation_euler : Fintype.card a.Occ+4≤2*Fintype.card (Cycle a.closedRotation)+
    2*Fintype.card (Cycle (a.fullPartner*a.closedRotation)) := by
  let : Nonempty a.Occ := ⟨a.first hxy⟩
  exact MapEuler.euler_of_genusZero _ _ (a.closedRotation_genusZero hxy) a.fullPartner_nonfixed
variable (hr : a.Reduced)
include hr in
lemma edge_partner_not_reverse (i : a.Occ) : a.edge (a.fullPartner i)≠Γ.reverse (a.edge i) := by
  intro he
  apply hr.1 i i.property
  change a.dart (a.fullPartner i).val=(a.dart i).map Γ.reverse
  rw [←a.some_edge (a.fullPartner i),←a.some_edge i,Option.map_some,he]
lemma edge_partner_not_same (hn : ∀d,inv (label d)≠label d) (i : a.Occ) :
    a.edge i≠a.edge (a.fullPartner i) := by
  intro he
  have h := a.edge_compatible i
  rw [←he] at h
  exact hn _ h.symm
include hr in
lemma edge_reduced (hn : ∀d,inv (label d)≠label d) (i : a.Occ) :
    a.edge i≠a.edge (a.fullPartner i) ∧ a.edge i≠Γ.reverse (a.edge (a.fullPartner i)) := by
  refine ⟨a.edge_partner_not_same hn i,?_⟩
  intro he
  apply a.edge_partner_not_reverse hr i
  have hh := congrArg Γ.reverse he
  rw [Γ.reverse_reverse] at hh
  exact hh.symm
include hr in
lemma edge_no_backtrack (i : a.Occ) (hi : a.closedRotation i≠a.first hxy) :
    a.edge (a.closedRotation i)≠Γ.reverse (a.edge i) := by
  intro he
  have hn : a.rotation i≠a.marker := fun h=>hi ((a.closedRotation_at_first hxy i).mpr h)
  apply hr.2 i i.property hn
  rw [←a.closedRotation_val hxy i hi,←a.some_edge (a.closedRotation i),←a.some_edge i,Option.map_some,he]
variable (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
  (himm : ∀d e,Γ.origin d=Γ.origin e → label d=label e → d=e)
include hr hlabel himm in
lemma face_fixed_break (i : a.Occ) (hf : (a.fullPartner*a.closedRotation) i=i) :
    a.closedRotation i=a.first hxy := by
  by_contra hi
  have he : a.closedRotation i=a.fullPartner i := by
    have hh := congrArg a.fullPartner hf
    change a.fullPartner (a.fullPartner (a.closedRotation i))=a.fullPartner i at hh
    rwa [a.fullPartner_involutive] at hh
  apply a.edge_no_backtrack hxy hr i hi
  symm
  apply himm
  · exact a.edge_consistent hxy i hi
  · rw [hlabel,he,a.edge_compatible]
include hxy hr hlabel himm in
lemma face_monogons_le : (fixed (a.fullPartner*a.closedRotation)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply a.closedRotation.injective
  have hfi : (a.fullPartner*a.closedRotation) i=i := by
    simpa only [fixed,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hfj : (a.fullPartner*a.closedRotation) j=j := by
    simpa only [fixed,Finset.mem_filter,Finset.mem_univ,true_and] using hj
  exact (a.face_fixed_break hxy hr hlabel himm i hfi).trans
    (a.face_fixed_break hxy hr hlabel himm j hfj).symm
include hxy hr hlabel himm in
/-- A reduced distinct-endpoint certificate necessarily contains an ordinary
boundary, not just the exceptional root cycle. This includes singleton cycles. -/
lemma at_least_two_boundaries : 2≤Fintype.card (Cycle a.closedRotation) := by
  have he := a.closedRotation_euler hxy
  have hf := twice_cycles_le (a.fullPartner*a.closedRotation)
  have hm := a.face_monogons_le hxy hr hlabel himm
  omega
include hr hlabel himm in
lemma ordinary_boundary : ∃c : Cycle a.closedRotation,c≠cycle a.closedRotation (a.first hxy) := by
  by_contra he
  push Not at he
  have hi : Function.Injective (fun _ : Cycle a.closedRotation=>(() : Unit)) := by
    intro c d _
    exact (he c).trans (he d).symm
  have hc := Fintype.card_le_of_injective _ hi
  simp only [Fintype.card_unit] at hc
  have hb := a.at_least_two_boundaries hxy hr hlabel himm
  omega
end TorsionFreeZeroDivisors.FinitePicture.Data

/-! Exact finite permutation cycles, including singleton cycles, as nonempty
lists with their literal successor. This is the coordinate bridge from marked
picture surgery to boundary words; it asserts no geometric realization. -/

end

end OAI
