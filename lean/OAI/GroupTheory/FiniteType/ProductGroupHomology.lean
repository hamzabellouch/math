import Mathlib
import OAI.GroupTheory.FiniteType.SurjectiveTrivialInduction

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
namespace ProductGroupHomology
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [-instance] AddCommGroup.toIntModule
variable {ι : Type} [Finite ι] (K : ι → Type) [∀ i, Group (K i)]
  [∀ i, Group.IsFinitelyPresented (K i)]

theorem finitePiProducts
    (hz : ∀ i (I : Type) (n : ℕ), IsZero (groupHomology (RegularProductR.rep ℤ (K i) I) (n+1))) :
    ∀ (I : Type) (n : ℕ), IsZero (groupHomology (RegularProductR.rep ℤ (∀ i, K i) I) (n+1)) := by
  classical
  let := Fintype.ofFinite ι
  suffices hh : ∀ m (L : Fin m → Type) [∀ i, Group (L i)]
      [∀ i, Group.IsFinitelyPresented (L i)],
      (∀ i (I : Type) (n : ℕ), IsZero (groupHomology (RegularProductR.rep ℤ (L i) I) (n+1))) →
      ∀ (I : Type) (n : ℕ), IsZero (groupHomology (RegularProductR.rep ℤ (∀ i, L i) I) (n+1)) by
    let e := Fintype.equivFin ι
    let e' : (∀ i, K i) ≃* (∀ i, K (e.symm i)) :=
      { (Equiv.piCongrLeft K e.symm).symm with map_mul' := fun _ _ => rfl }
    intro I n
    exact (hh (Fintype.card ι) (fun i => K (e.symm i)) (fun i => hz (e.symm i)) I n).of_iso
      (RegularProductR.homologyRelabel e' I (n+1))
  intro m
  induction m with
  | zero =>
    intro L _ _ hz I n
    exact isZero_groupHomology_succ_of_subsingleton _ n
  | succ m ih =>
    intro L _ _ hz I n
    let e : (∀ i, L i) ≃* L 0 × (∀ i : Fin m, L i.succ) :=
      { toFun f := (f 0,fun i => f i.succ)
        invFun p := Fin.cases p.1 p.2
        left_inv f := by funext i; exact Fin.cases rfl (fun _ => rfl) i
        right_inv p := rfl
        map_mul' _ _ := rfl }
    let := ActionPresentation.finite_pi_finitelyPresented (fun i : Fin m => L i.succ)
    let := ActionPresentation.fg_of_fp (G := L 0)
    let := ActionPresentation.fg_of_fp (G := ∀ i : Fin m, L i.succ)
    obtain ⟨P,hP⟩ := ProductFiniteResolution.finite_free_resolution_of_products (L 0) (by
      intro J j hj
      obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      exact hz 0 J q)
    exact (products (H := ∀ i : Fin m, L i.succ) P hP (ih _ (fun i => hz i.succ)) I n).of_iso
      (RegularProductR.homologyRelabel e I (n+1))
end ProductGroupHomology

open Set Function
open scoped Pointwise

universe u v
namespace TwistedBrin
abbrev Cantor := Stream' Bool
instance : TopologicalSpace Cantor := inferInstanceAs (TopologicalSpace (ℕ → Bool))
instance : CompactSpace Cantor := inferInstanceAs (CompactSpace (ℕ → Bool))
instance : T2Space Cantor := inferInstanceAs (T2Space (ℕ → Bool))
abbrev Box (S : Type u) := S → Cantor

lemma continuous_get (n : ℕ) : Continuous (fun x : Cantor => x.get n) := continuous_apply n

structure Prefix (S : Type u) where
  word : S → List Bool
  finite_support : {s | word s ≠ []}.Finite

namespace Prefix
variable {S : Type u}
instance : CoeFun (Prefix S) (fun _ => S → List Bool) := ⟨Prefix.word⟩
@[ext] theorem ext {p q : Prefix S} (h : ∀ s, p s = q s) : p = q := by
  cases p; cases q; simp_all only [mk.injEq]; exact funext h

def empty : Prefix S := ⟨fun _ => [], by simp⟩
@[simp] lemma empty_apply (s : S) : (empty : Prefix S) s = [] := rfl

def append (p q : Prefix S) : Prefix S where
  word s := p s ++ q s
  finite_support := (p.finite_support.union q.finite_support).subset (by
    intro s hs
    simp only [mem_ofPred_eq, mem_union] at *
    by_contra h
    push Not at h
    simp [h.1,h.2] at hs)
@[simp] lemma append_apply (p q : Prefix S) (s : S) : append p q s = p s ++ q s := rfl
@[simp] lemma empty_append (p : Prefix S) : append empty p = p := by ext; simp
@[simp] lemma append_empty (p : Prefix S) : append p empty = p := by ext; simp
lemma append_assoc (p q r : Prefix S) : append (append p q) r = append p (append q r) := by
  ext; simp [List.append_assoc]

def chart (p : Prefix S) : Box S → Box S := fun x s => Stream'.appendStream' (p s) (x s)
def tail (p : Prefix S) : Box S → Box S := fun x s => Stream'.drop (p s).length (x s)
def brick (p : Prefix S) : Set (Box S) := Set.range p.chart

@[simp] lemma chart_empty (x : Box S) : (empty : Prefix S).chart x = x := rfl
@[simp] lemma tail_chart (p : Prefix S) (x : Box S) : p.tail (p.chart x) = x := by
  funext s
  exact Stream'.drop_append_stream (p s) (x s)
lemma chart_injective (p : Prefix S) : Function.Injective p.chart :=
  Function.LeftInverse.injective (tail_chart p)
@[simp] lemma chart_mem_brick (p : Prefix S) (x : Box S) : p.chart x ∈ p.brick := ⟨x,rfl⟩
lemma chart_tail {p : Prefix S} {x : Box S} (h : x ∈ p.brick) : p.chart (p.tail x) = x := by
  obtain ⟨y,rfl⟩ := h
  rw [tail_chart]
lemma mem_brick_iff (p : Prefix S) (x : Box S) : x ∈ p.brick ↔
    ∀ s, Stream'.take (p s).length (x s) = p s := by
  constructor
  · rintro ⟨y,rfl⟩ s
    simpa only [chart,List.take_length] using
      Stream'.take_append_of_le_length (p s).length (p s) (y s) le_rfl
  · intro h
    refine ⟨p.tail x,?_⟩
    funext s
    change Stream'.appendStream' (p s) (Stream'.drop (p s).length (x s)) = x s
    nth_rw 1 [← h s]
    exact Stream'.append_take_drop (p s).length (x s)
@[simp] lemma brick_empty : (empty : Prefix S).brick = Set.univ := by
  ext; simp [brick]
@[simp] lemma chart_append (p q : Prefix S) (x : Box S) :
    (append p q).chart x = p.chart (q.chart x) := by
  funext s
  exact Stream'.append_append_stream (p s) (q s) (x s)
lemma brick_append_subset (p q : Prefix S) : (append p q).brick ⊆ p.brick := by
  rintro _ ⟨x,rfl⟩
  rw [chart_append]
  exact chart_mem_brick _ _

def suffix (p r : Prefix S) : Prefix S where
  word s := (r s).drop (p s).length
  finite_support := r.finite_support.subset (by
    intro s hs hz
    simp only [mem_ofPred_eq] at hs hz
    simp [hz] at hs)
@[simp] lemma suffix_apply (p r : Prefix S) (s : S) : suffix p r s = (r s).drop (p s).length := rfl

def Extends (p r : Prefix S) : Prop := ∀ s, p s <+: r s
lemma append_suffix {p r : Prefix S} (h : Extends p r) : append p (suffix p r) = r := by
  apply Prefix.ext
  intro s
  obtain ⟨l,hl⟩ := h s
  change p s ++ (r s).drop (p s).length = r s
  rw [← hl]
  simp
lemma brick_subset_of_extends {p r : Prefix S} (h : Extends p r) : r.brick ⊆ p.brick := by
  rw [← append_suffix h]
  exact brick_append_subset p (suffix p r)

noncomputable def common (x : Box S) (p q : Prefix S) : Prefix S where
  word s := Stream'.take (max (p s).length (q s).length) (x s)
  finite_support := (p.finite_support.union q.finite_support).subset (by
    intro s hs
    simp only [mem_ofPred_eq, mem_union] at *
    by_contra h
    push Not at h
    simp [h.1,h.2] at hs)
@[simp] lemma common_apply (x : Box S) (p q : Prefix S) (s : S) :
    common x p q s = Stream'.take (max (p s).length (q s).length) (x s) := rfl
lemma mem_common (x : Box S) (p q : Prefix S) : x ∈ (common x p q).brick := by
  apply (mem_brick_iff _ _).mpr
  intro s
  simp
lemma extends_common_left {x : Box S} {p q : Prefix S} (hp : x ∈ p.brick) :
    Extends p (common x p q) := by
  intro s
  rw [← (mem_brick_iff p x).mp hp s]
  exact Stream'.take_prefix_take_left _ _ _ (le_max_left _ _)
lemma extends_common_right {x : Box S} {p q : Prefix S} (hq : x ∈ q.brick) :
    Extends q (common x p q) := by
  intro s
  rw [← (mem_brick_iff q x).mp hq s]
  exact Stream'.take_prefix_take_left _ _ _ (le_max_right _ _)

noncomputable def permute (σ : Equiv.Perm S) (p : Prefix S) : Prefix S where
  word s := p (σ.symm s)
  finite_support := p.finite_support.preimage σ.symm.injective.injOn
@[simp] lemma permute_apply (σ : Equiv.Perm S) (p : Prefix S) (s : S) :
    permute σ p s = p (σ.symm s) := rfl
end Prefix

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

def twist (a : A) : Equiv.Perm (Box S) where
  toFun x s := x (ρ a⁻¹ s)
  invFun x s := x (ρ a s)
  left_inv x := by funext s; simp
  right_inv x := by funext s; simp
@[simp] lemma twist_apply (a : A) (x : Box S) (s : S) : twist ρ a x s = x (ρ a⁻¹ s) := rfl
@[simp] lemma twist_one (x : Box S) : twist ρ 1 x = x := by ext; simp
lemma twist_mul (a b : A) (x : Box S) : twist ρ (a*b) x = twist ρ a (twist ρ b x) := by
  ext s n
  simp only [twist_apply,mul_inv_rev,map_mul,Equiv.Perm.coe_mul,Function.comp_apply]
lemma twist_inv (a : A) (x : Box S) : twist ρ a⁻¹ (twist ρ a x) = x := by
  rw [← twist_mul,inv_mul_cancel,twist_one]
lemma twist_chart (a : A) (p : Prefix S) (x : Box S) :
    twist ρ a (p.chart x) = (p.permute (ρ a)).chart (twist ρ a x) := by
  ext s n
  simp only [twist_apply,Prefix.chart,Prefix.permute_apply,map_inv,Equiv.Perm.inv_def]
lemma twist_prefix_inv (a : A) (p : Prefix S) :
    (p.permute (ρ a⁻¹)).permute (ρ a) = p := by
  apply Prefix.ext
  intro s
  simp only [Prefix.permute_apply,map_inv,Equiv.Perm.inv_def,Equiv.symm_symm,
    Equiv.apply_symm_apply]

def LocallyStandard (f : Box S → Box S) : Prop :=
  ∀ x : Box S, ∃ (p q : Prefix S) (a : A), x ∈ p.brick ∧
    ∀ y : Box S, f (p.chart y) = q.chart (twist ρ a y)

def IsLocal (f : Equiv.Perm (Box S)) : Prop := LocallyStandard ρ f

lemma isLocal_one : IsLocal ρ 1 := by
  intro x
  refine ⟨Prefix.empty,Prefix.empty,1,?_,?_⟩
  · simp
  · intro y; simp

lemma isLocal_inv {f : Equiv.Perm (Box S)} (hf : IsLocal ρ f) : IsLocal ρ f⁻¹ := by
  intro x
  obtain ⟨p,q,a,hx,h⟩ := hf (f⁻¹ x)
  have hx' : x ∈ q.brick := by
    obtain ⟨y,hy⟩ := hx
    refine ⟨twist ρ a y,?_⟩
    rw [← h,hy]
    exact f.apply_symm_apply x
  refine ⟨q,p,a⁻¹,hx',?_⟩
  intro y
  apply f.injective
  rw [Equiv.Perm.inv_def,f.apply_symm_apply,h]
  rw [← twist_mul,mul_inv_cancel,twist_one]

lemma isLocal_mul {f g : Equiv.Perm (Box S)} (hf : IsLocal ρ f) (hg : IsLocal ρ g) :
    IsLocal ρ (f*g) := by
  intro x
  obtain ⟨p,q,a,hx,hg'⟩ := hg x
  obtain ⟨r,s,b,hy,hf'⟩ := hf (g x)
  have hyq : g x ∈ q.brick := by
    obtain ⟨y,rfl⟩ := hx
    rw [hg']
    exact Prefix.chart_mem_brick _ _
  let v := Prefix.common (g x) q r
  let c := Prefix.suffix q v
  let d := Prefix.suffix r v
  have hc : Prefix.append q c = v := Prefix.append_suffix (Prefix.extends_common_left hyq)
  have hd : Prefix.append r d = v := Prefix.append_suffix (Prefix.extends_common_right hy)
  let c' := c.permute (ρ a⁻¹)
  let p' := Prefix.append p c'
  let s' := Prefix.append s (d.permute (ρ b))
  have hg_ref (y : Box S) : g (p'.chart y) = v.chart (twist ρ a y) := by
    dsimp [p']
    rw [Prefix.chart_append,hg',twist_chart,twist_prefix_inv,← Prefix.chart_append,hc]
  have hp' : x ∈ p'.brick := by
    obtain ⟨y,hy⟩ := Prefix.mem_common (g x) q r
    refine ⟨twist ρ a⁻¹ y,?_⟩
    apply g.injective
    rw [hg_ref,← twist_mul,mul_inv_cancel,twist_one,hy]
  refine ⟨p',s',b*a,hp',?_⟩
  intro y
  change f (g (p'.chart y)) = _
  rw [hg_ref,← hd,Prefix.chart_append,hf',twist_chart,← Prefix.chart_append]
  rw [twist_mul]

def localGroup : Subgroup (Equiv.Perm (Box S)) where
  carrier := IsLocal ρ
  one_mem' := isLocal_one ρ
  inv_mem' := isLocal_inv ρ
  mul_mem' := isLocal_mul ρ

end TwistedBrin

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma mem_brick_iff_get (p : Prefix S) (x : Box S) : x ∈ p.brick ↔
    ∀ s (n : ℕ) (hn : n < (p s).length), (x s).get n = (p s)[n] := by
  rw [mem_brick_iff]
  constructor
  · intro h s n hn
    have he := congrArg (fun l : List Bool => l[n]?) (h s)
    simpa only [List.getElem?_eq_getElem hn,Stream'.getElem?_take hn,Option.some.injEq] using he
  · intro h s
    apply List.ext_getElem (Stream'.length_take _ _)
    intro n hn hn'
    rw [Stream'.take_get]
    exact h s n hn'

lemma isOpen_brick (p : Prefix S) : IsOpen p.brick := by
  classical
  let : Finite {s : S // p s ≠ []} := p.finite_support.to_subtype
  let I := (s : {s : S // p s ≠ []}) × Fin (p s.1).length
  have he : p.brick = ⋂ j : I, {x | (x j.1.1).get j.2 = (p j.1.1)[j.2]} := by
    ext x
    simp only [mem_brick_iff_get,mem_iInter,mem_ofPred_eq]
    constructor
    · intro h j; exact h j.1.1 j.2 j.2.isLt
    · intro h s n hn
      have hs : p s ≠ [] := by intro he; simp [he] at hn
      exact h ⟨⟨s,hs⟩,⟨n,hn⟩⟩
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  exact (isOpen_discrete {(p j.1.1)[j.2]}).preimage
    ((continuous_get (j.2.val)).comp (continuous_apply j.1.1))

lemma continuous_chart (p : Prefix S) : Continuous p.chart := by
  apply continuous_pi
  intro s
  apply continuous_pi
  intro n
  change Continuous (fun x : Box S => (p.chart x s).get n)
  by_cases hn : n < (p s).length
  · have h : (fun x : Box S => (p.chart x s).get n) = fun _ => (p s)[n] := by
      funext x
      exact Stream'.get_append_left _ _ _ hn
    rw [h]
    exact continuous_const
  · have h : (fun x : Box S => (p.chart x s).get n) = fun x => (x s).get (n-(p s).length) := by
      funext x
      nth_rw 1 [← Nat.add_sub_of_le (le_of_not_gt hn)]
      exact Stream'.get_append_right _ _ _
    rw [h]
    exact (continuous_get _).comp (continuous_apply _)
lemma continuous_tail (p : Prefix S) : Continuous p.tail := by
  apply continuous_pi
  intro s
  apply continuous_pi
  intro n
  change Continuous (fun x : Box S => (x s).get (n+(p s).length))
  exact (continuous_get _).comp (continuous_apply _)

lemma extends_of_mem_of_length_le {p r : Prefix S} {x : Box S}
    (hp : x ∈ p.brick) (hr : x ∈ r.brick) (hl : ∀ s, (p s).length ≤ (r s).length) :
    Extends p r := by
  intro s
  have hp' := (mem_brick_iff p x).mp hp s
  have hr' := (mem_brick_iff r x).mp hr s
  rw [← hp',← hr']
  exact Stream'.take_prefix_take_left _ _ _ (hl s)

noncomputable def lengths (p : Prefix S) : S →₀ ℕ :=
  Finsupp.ofSupportFinite (fun s => (p s).length) (by simpa [Function.support] using p.finite_support)
@[simp] lemma lengths_apply (p : Prefix S) (s : S) : p.lengths s = (p s).length := rfl

end TwistedBrin.Prefix

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

def IsPartition {I : Type*} (p : I → Prefix S) : Prop :=
  ∀ x : Box S, ∃! i : I, x ∈ (p i).brick

structure Table where
  size : ℕ
  dom : Fin size → Prefix S
  ran : Fin size → Prefix S
  label : Fin size → A
  dom_partition : IsPartition dom
  ran_partition : IsPartition ran

def HasTable (f : Equiv.Perm (Box S)) : Prop :=
  ∃ T : Table (A := A) (S := S), ∀ i y,
    f ((T.dom i).chart y) = (T.ran i).chart (twist ρ (T.label i) y)

lemma isLocal_of_hasTable {f : Equiv.Perm (Box S)} (hf : HasTable ρ f) : IsLocal ρ f := by
  obtain ⟨T,h⟩ := hf
  intro x
  obtain ⟨i,hi,_⟩ := T.dom_partition x
  exact ⟨T.dom i,T.ran i,T.label i,hi,h i⟩

def Oligomorphic : Prop :=
  ∀ n : ℕ, ∃ R : Finset (Finset S), ∀ F : Finset S, F.card = n →
    ∃ (E : Finset S), E ∈ R ∧ ∃ a : A, F.map (ρ a).toEmbedding = E

noncomputable def setwiseStabilizer (F : Set S) : Subgroup A := by
  letI : MulAction A S := MulAction.compHom S ρ
  exact MulAction.stabilizer A F

end

def GeometricTransferObligation : Prop :=
  ∀ (A S : Type) [Group A] (ρ : A →* Equiv.Perm S),
    Function.Injective ρ → Countable S → Infinite S → Oligomorphic ρ →
    SimpleFInftyOvergroups.HasTypeFInfty A →
    (∀ F : Set S, F.Finite →
      SimpleFInftyOvergroups.HasTypeFInfty (setwiseStabilizer ρ F)) →
    SimpleFInftyOvergroups.HasTypeFInfty (localGroup ρ)
end TwistedBrin

namespace TwistedBrin.Prefix
variable {S : Type u}

noncomputable def Grid (b : S →₀ ℕ) := (s : b.support) → Fin (b s) → Bool
noncomputable instance (b : S →₀ ℕ) : Fintype (Grid b) := by
  classical
  unfold Grid
  infer_instance

noncomputable def gridPrefix (b : S →₀ ℕ) (z : Grid b) : Prefix S := by
  classical
  exact {
    word := fun s => if hs : s ∈ b.support then List.ofFn (z ⟨s,hs⟩) else []
    finite_support := b.support.finite_toSet.subset (by
      intro s hs
      change s ∈ b.support
      by_contra hn
      change (if h : s ∈ b.support then List.ofFn (z ⟨s,h⟩) else []) ≠ [] at hs
      rw [dite_eq_right hn] at hs
      exact hs rfl) }

lemma gridPrefix_length (b : S →₀ ℕ) (z : Grid b) (s : S) :
    (gridPrefix b z s).length = b s := by
  classical
  by_cases hs : s ∈ b.support
  · simp only [gridPrefix,dite_eq_left hs,List.length_ofFn]
  · simp only [gridPrefix,dite_eq_right hs,List.length_nil,Finsupp.notMem_support_iff.mp hs]

lemma gridPrefix_get (b : S →₀ ℕ) (z : Grid b) (s : b.support) (n : Fin (b s)) :
    (gridPrefix b z s)[n.val]'(by rw [gridPrefix_length]; exact n.isLt) = z s n := by
  classical
  simp only [gridPrefix,dite_eq_left s.property,List.getElem_ofFn]

noncomputable def gridPoint (b : S →₀ ℕ) (x : Box S) : Grid b :=
  fun s n => (x s).get n

lemma mem_gridPrefix (b : S →₀ ℕ) (x : Box S) :
    x ∈ (gridPrefix b (gridPoint b x)).brick := by
  classical
  apply (mem_brick_iff_get _ _).mpr
  intro s n hn
  have hn' : n < b s := by simpa only [gridPrefix_length] using hn
  have hs : s ∈ b.support := Finsupp.mem_support_iff.mpr (by omega)
  exact (gridPrefix_get b (gridPoint b x) ⟨s,hs⟩ ⟨n,hn'⟩).symm

lemma eq_gridPoint_of_mem {b : S →₀ ℕ} {z : Grid b} {x : Box S}
    (hx : x ∈ (gridPrefix b z).brick) : z = gridPoint b x := by
  funext s n
  have h := (mem_brick_iff_get _ _).mp hx s n (by rw [gridPrefix_length]; exact n.isLt)
  rw [gridPrefix_get] at h
  exact h.symm

lemma grid_partition (b : S →₀ ℕ) : TwistedBrin.IsPartition (gridPrefix b) := by
  intro x
  exact ⟨gridPoint b x,mem_gridPrefix b x,fun z hz => eq_gridPoint_of_mem hz⟩

end TwistedBrin.Prefix

end

end OAI
