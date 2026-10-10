import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.MixedWords
import OAI.Analysis.TracialCohomology.MatrixExtensions

namespace OAI

/-! Marked words for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
variable {C B G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

abbrev Mark (C B : Type*) := C ⊕ (B × Bool)
abbrev Block (C B : Type*) := B × List (Letter C B)
def oldMark : Letter C B → Mark C B := Sum.map id (fun b => (b,false))
def eraseMark : Mark C B → Letter C B := Sum.map id Prod.fst

def freshs (m : List (Mark C B)) : List B := m.filterMap (fun x =>
  match x with
  | .inl _ => none
  | .inr (b,t) => if t then some b else none)
def markedValue (a : C → M) (γ : B → G) (v w : Rep G M) : Mark C B → M :=
  Sum.elim a (fun bt => if bt.2 then w (γ bt.1) else v (γ bt.1))
def markedEval (a : C → M) (γ : B → G) (v w : Rep G M) (m : List (Mark C B)) : M :=
  (m.map (markedValue a γ v w)).prod

@[simp] lemma erase_old (x : Letter C B) : eraseMark (oldMark x)=x := by cases x <;> rfl
@[simp] lemma erase_old_list (l : List (Letter C B)) : (l.map oldMark).map eraseMark=l := by
  simpa only [List.map_map] using (show l.map (eraseMark ∘ oldMark)=l from by
    have he : eraseMark ∘ oldMark = (id : Letter C B → Letter C B) := funext erase_old
    rw [he,List.map_id])
@[simp] lemma freshs_old (l : List (Letter C B)) : freshs (l.map oldMark)=[] := by
  induction l with
  | nil => rfl
  | cons x l ih => cases x <;> simp [freshs,oldMark]
@[simp] lemma freshs_append (l k : List (Mark C B)) : freshs (l++k)=freshs l++freshs k :=
  List.filterMap_append
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma markedEval_old (a : C → M) (γ : B → G) (v w : Rep G M) (l : List (Letter C B)) :
    markedEval a γ v w (l.map oldMark)=evaluate a γ v l := by
  simp only [markedEval,evaluate,List.map_map]
  congr 2
  funext x; cases x <;> rfl
omit [PartialOrder M] [StarOrderedRing M] in
lemma markedEval_append (a : C → M) (γ : B → G) (v w : Rep G M) (l k : List (Mark C B)) :
    markedEval a γ v w (l++k)=markedEval a γ v w l*markedEval a γ v w k := by
  simp only [markedEval,List.map_append,List.prod_append]

def variants : List (Letter C B) → List (List (Mark C B))
  | [] => [[]]
  | .inl c :: l => (variants l).map (List.cons (.inl c))
  | .inr b :: l => (variants l).map (List.cons (.inr (b,false))) ++
      (variants l).map (List.cons (.inr (b,true)))

lemma erase_variant (l : List (Letter C B)) (m : List (Mark C B)) (hm : m ∈ variants l) :
    m.map eraseMark=l := by
  induction l generalizing m with
  | nil => simpa [variants] using hm
  | cons x l ih =>
    cases x with
    | inl c =>
      obtain ⟨m,hm0,rfl⟩ := List.mem_map.mp hm
      change Sum.inl c :: m.map eraseMark = Sum.inl c :: l
      rw [ih m hm0]
    | inr b =>
      rcases List.mem_append.mp hm with hm1|hm1
      · obtain ⟨m,hm0,rfl⟩ := List.mem_map.mp hm1
        change Sum.inr b :: m.map eraseMark = Sum.inr b :: l
        rw [ih m hm0]
      · obtain ⟨m,hm0,rfl⟩ := List.mem_map.mp hm1
        change Sum.inr b :: m.map eraseMark = Sum.inr b :: l
        rw [ih m hm0]

lemma variants_length_le (l : List (Letter C B)) : (variants l).length ≤ 2^l.length := by
  induction l with
  | nil => simp [variants]
  | cons x l ih =>
    cases x <;> simp only [variants,List.length_append,List.length_map,List.length_cons,pow_succ] <;> omega

omit [PartialOrder M] [StarOrderedRing M] in
lemma evaluate_add_expansion (a : C → M) (γ : B → G) (v w : Rep G M) (hw)
    (l : List (Letter C B)) :
    evaluate a γ (v.add w hw) l = ((variants l).map (markedEval a γ v w)).sum := by
  induction l with
  | nil => simp [variants,markedEval]
  | cons x l ih =>
    cases x with
    | inl c =>
      simp only [evaluate_cons,letterValue,Sum.elim_inl,variants,List.map_map]
      change a c*evaluate a γ (v.add w hw) l=
        ((variants l).map (fun m => a c*markedEval a γ v w m)).sum
      rw [ih,List.sum_map_mul_left]
    | inr b =>
      simp only [evaluate_cons,letterValue,Sum.elim_inr,Rep.add_apply,variants,
        List.map_append,List.sum_append,List.map_map]
      change (v (γ b)+w (γ b))*evaluate a γ (v.add w hw) l=
        ((variants l).map (fun m => v (γ b)*markedEval a γ v w m)).sum+
        ((variants l).map (fun m => w (γ b)*markedEval a γ v w m)).sum
      rw [ih,add_mul,List.sum_map_mul_left,List.sum_map_mul_left]

def splitMarked : List (Mark C B) → List (Letter C B) × List (Block C B)
  | [] => ([],[])
  | .inl c :: m => let (l,b) := splitMarked m; (.inl c::l,b)
  | .inr (c,false) :: m => let (l,b) := splitMarked m; (.inr c::l,b)
  | .inr (c,true) :: m => let (l,b) := splitMarked m; ([],(c,l)::b)

def flattenBlocks (b : List (Block C B)) : List (Mark C B) :=
  b.flatMap (fun j => .inr (j.1,true)::j.2.map oldMark)
def eraseBlocks (b : List (Block C B)) : List (Letter C B) :=
  b.flatMap (fun j => .inr j.1::j.2)

lemma splitMarked_spec (m : List (Mark C B)) :
    m=(splitMarked m).1.map oldMark++flattenBlocks (splitMarked m).2 := by
  induction m with
  | nil => rfl
  | cons x m ih =>
    cases x with
    | inl c => simpa [splitMarked,oldMark] using congrArg (List.cons (.inl c)) ih
    | inr bt =>
      rcases bt with ⟨b,t⟩
      cases t
      · simpa [splitMarked,oldMark] using congrArg (List.cons (.inr (b,false))) ih
      · simpa [splitMarked,flattenBlocks] using congrArg (List.cons (.inr (b,true))) ih

@[simp] lemma erase_flatten (b : List (Block C B)) :
    (flattenBlocks b).map eraseMark=eraseBlocks b := by
  induction b with
  | nil => rfl
  | cons j b ih =>
    change ((Sum.inr (j.1,true)::j.2.map oldMark)++flattenBlocks b).map eraseMark=
      (Sum.inr j.1::j.2)++eraseBlocks b
    rw [List.map_append,List.map_cons,erase_old_list,ih]
    rfl

@[simp] lemma freshs_flatten (b : List (Block C B)) : freshs (flattenBlocks b)=b.map Prod.fst := by
  induction b with
  | nil => rfl
  | cons j b ih =>
    simp only [flattenBlocks,List.flatMap_cons,freshs_append]
    change (j.1::freshs (j.2.map oldMark))++freshs (flattenBlocks b)=_
    rw [freshs_old,ih]
    rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma markedEval_flatten (a : C → M) (γ : B → G) (v w : Rep G M) (b : List (Block C B)) :
    markedEval a γ v w (flattenBlocks b)=(b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod := by
  induction b with
  | nil => rfl
  | cons j b ih =>
    simp only [flattenBlocks,List.flatMap_cons,markedEval_append,List.map_cons,List.prod_cons]
    change (w (γ j.1)*markedEval a γ v w (j.2.map oldMark))*markedEval a γ v w (flattenBlocks b)= _
    rw [markedEval_old,ih]

def appendTail : List (Block C B) → List (Letter C B) → List (Block C B)
  | [], _ => []
  | [b], l => [(b.1,b.2++l)]
  | b::c::cs, l => b::appendTail (c::cs) l

lemma appendTail_spec (b : List (Block C B)) (l : List (Letter C B)) (hb : b ≠ []) :
    flattenBlocks (appendTail b l)=flattenBlocks b++l.map oldMark := by
  induction b with
  | nil => exact False.elim (hb rfl)
  | cons j b ih =>
    cases b with
    | nil => simp [appendTail,flattenBlocks]
    | cons k b =>
      change (Sum.inr (j.1,true)::j.2.map oldMark)++flattenBlocks (appendTail (k::b) l)=
        ((Sum.inr (j.1,true)::j.2.map oldMark)++flattenBlocks (k::b))++l.map oldMark
      rw [show flattenBlocks (appendTail (k::b) l)=flattenBlocks (k::b)++l.map oldMark from ih (by simp)]
      simp only [flattenBlocks,List.flatMap_cons,List.append_assoc]

lemma freshs_nonempty_split (m : List (Mark C B)) (hm : freshs m ≠ []) : (splitMarked m).2 ≠ [] := by
  intro h
  have hh := congrArg freshs (splitMarked_spec m)
  simp only [freshs_append,freshs_old,freshs_flatten,h,List.map_nil,List.nil_append] at hh
  exact hm hh

lemma degree_rotation_ne_one (γ : B → G) (a b : List (Letter C B))
    (h : degree γ (a++b) ≠ 1) : degree γ (b++a) ≠ 1 := by
  rw [degree_append] at h ⊢
  exact fun he => h (mul_eq_one_comm.mp he)

omit [StarOrderedRing M] in
lemma cyclic_blocks (τ : M →ₚ[ℂ] ℂ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (a : C → M) (γ : B → G) (v w : Rep G M) (m : List (Mark C B))
    (hm : freshs m ≠ []) (hd : degree γ (m.map eraseMark) ≠ 1) :
    ∃ b : List (Block C B), b ≠ [] ∧ b.map Prod.fst=freshs m ∧
      (eraseBlocks b).length=m.length ∧ degree γ (eraseBlocks b) ≠ 1 ∧
      τ (markedEval a γ v w m)=τ ((b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod) ∧
      τ (evaluate a γ v (m.map eraseMark))=τ (evaluate a γ v (eraseBlocks b)) := by
  let pre := (splitMarked m).1
  let bs := (splitMarked m).2
  have hbs : bs ≠ [] := freshs_nonempty_split m hm
  let b := appendTail bs pre
  have he : flattenBlocks b=flattenBlocks bs++pre.map oldMark := appendTail_spec bs pre hbs
  have hm' : m=pre.map oldMark++flattenBlocks bs := splitMarked_spec m
  have her : m.map eraseMark=pre++eraseBlocks bs := by rw [hm']; simp only [List.map_append,erase_old_list,erase_flatten]
  have he' : eraseBlocks b=eraseBlocks bs++pre := by
    rw [←erase_flatten,he,List.map_append,erase_flatten,erase_old_list]
  have hf : b.map Prod.fst=freshs m := by
    rw [←freshs_flatten,he,hm']
    simp
  have hlen : (eraseBlocks b).length=m.length := by
    rw [he',List.length_append,hm',List.length_append,List.length_map]
    have hh := congrArg List.length (erase_flatten bs)
    simp only [List.length_map] at hh
    omega
  refine ⟨b,fun hh => hm (by rw [←hf,hh,List.map_nil]),hf,hlen,?_,?_,?_⟩
  · rw [he']
    exact degree_rotation_ne_one γ pre (eraseBlocks bs) (by rwa [her] at hd)
  · rw [←markedEval_flatten,he,hm',markedEval_append,markedEval_append]
    exact htr _ _
  · rw [her,he',evaluate_append,evaluate_append]
    exact htr _ _
end PopaPatching

open scoped ComplexOrder
namespace PopaPatching
variable {C B G : Type*} [Group G]

def newVariants : List (Letter C B) → List (List (Mark C B))
  | [] => []
  | .inl c :: l => (newVariants l).map (List.cons (.inl c))
  | .inr b :: l => (newVariants l).map (List.cons (.inr (b,false))) ++
      (variants l).map (List.cons (.inr (b,true)))

lemma variants_eq (l : List (Letter C B)) : variants l=l.map oldMark::newVariants l := by
  induction l with
  | nil => rfl
  | cons x l ih => cases x <;> simp [variants,newVariants,ih,oldMark]

lemma mem_newVariants (l : List (Letter C B)) (m : List (Mark C B)) (hm : m ∈ newVariants l) :
    m ∈ variants l ∧ freshs m ≠ [] := by
  refine ⟨by rw [variants_eq]; exact List.mem_cons_of_mem _ hm,?_⟩
  induction l generalizing m with
  | nil => simp [newVariants] at hm
  | cons x l ih =>
    cases x with
    | inl c =>
      obtain ⟨m,hm0,rfl⟩ := List.mem_map.mp hm
      exact ih m hm0
    | inr b =>
      rcases List.mem_append.mp hm with hm1|hm1
      · obtain ⟨m,hm0,rfl⟩ := List.mem_map.mp hm1
        exact ih m hm0
      · obtain ⟨m,hm0,rfl⟩ := List.mem_map.mp hm1
        simp [freshs]

lemma newVariants_length_le (l : List (Letter C B)) : (newVariants l).length≤2^l.length := by
  have hh := variants_length_le l
  rw [variants_eq,List.length_cons] at hh
  omega

lemma eraseBlocks_append (b c : List (Block C B)) : eraseBlocks (b++c)=eraseBlocks b++eraseBlocks c :=
  List.flatMap_append

lemma blocks_length_le (b : List (Block C B)) : b.length ≤ (eraseBlocks b).length := by
  induction b with
  | nil => rfl
  | cons j b ih =>
    change (j::b).length ≤ ((Sum.inr j.1::j.2)++eraseBlocks b).length
    simp only [List.length_append,List.length_cons]
    omega

lemma segment_length_bound (b : List (Block C B)) (j : Block C B) (hj : j ∈ b) :
    j.2.length+b.length ≤ (eraseBlocks b).length := by
  obtain ⟨s,t,rfl⟩ := List.mem_iff_append.mp hj
  have hs := blocks_length_le s
  have ht := blocks_length_le t
  rw [eraseBlocks_append]
  change j.2.length+(s++j::t).length≤(eraseBlocks s++((Sum.inr j.1::j.2)++eraseBlocks t)).length
  simp only [List.length_append,List.length_cons]
  omega

lemma blocks_degree (γ : B → G) (b : List (Block C B))
    (hb : ∀ j ∈ b, degree γ j.2=1) : degree γ (eraseBlocks b)=(b.map (fun j => γ j.1)).prod := by
  induction b with
  | nil => rfl
  | cons j b ih =>
    change degree γ ((Sum.inr j.1::j.2)++eraseBlocks b)=_
    rw [degree_append,degree_cons,hb j (by simp)]
    change (γ j.1*1)*degree γ (eraseBlocks b)=γ j.1*(b.map (fun j => γ j.1)).prod
    rw [mul_one,ih (fun k hk => hb k (by simp [hk]))]

lemma exists_nontrivial_segment (γ : B → G) (b : List (Block C B))
    (hd : degree γ (eraseBlocks b) ≠ 1) (hg : (b.map (fun j => γ j.1)).prod=1) :
    ∃ j ∈ b, degree γ j.2 ≠ 1 := by
  by_contra hh
  push Not at hh
  exact hd ((blocks_degree γ b hh).trans hg)

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
omit [PartialOrder M] [StarOrderedRing M] in
lemma evaluate_blocks (a : C → M) (γ : B → G) (v : Rep G M) (b : List (Block C B)) :
    evaluate a γ v (eraseBlocks b)=(b.map (fun j => v (γ j.1)*evaluate a γ v j.2)).prod := by
  induction b with
  | nil => rfl
  | cons j b ih =>
    change evaluate a γ v ((Sum.inr j.1::j.2)++eraseBlocks b)=_
    rw [evaluate_append,evaluate_cons,ih]
    rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma evaluate_add_new_expansion (a : C → M) (γ : B → G) (v w : Rep G M) (hw)
    (l : List (Letter C B)) : evaluate a γ (v.add w hw) l=
      evaluate a γ v l+((newVariants l).map (markedEval a γ v w)).sum := by
  rw [evaluate_add_expansion,variants_eq,List.map_cons,List.sum_cons,markedEval_old]
end PopaPatching

end

end OAI
