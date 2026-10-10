import Mathlib
import OAI.GroupTheory.FiniteType.ProductGroupHomology

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma finite_local_cover {f : Equiv.Perm (Box S)} (hf : IsLocal ρ f) :
    ∃ (I : Finset (Box S)) (p q : Box S → Prefix S) (a : Box S → A),
      (∀ i y, f ((p i).chart y) = (q i).chart (twist ρ (a i) y)) ∧
      ∀ x, ∃ i ∈ I, x ∈ (p i).brick := by
  classical
  choose p q a hp he using hf
  have hcover : (Set.univ : Set (Box S)) ⊆ ⋃ i, (p i).brick := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,hp x⟩
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (p i).brick) (fun i => (p i).isOpen_brick) hcover
  refine ⟨I,p,q,a,he,?_⟩
  intro x
  simpa only [Set.mem_iUnion,exists_prop] using hI (Set.mem_univ x)

lemma finite_grid_refinement (I : Finset (Box S)) (p : Box S → Prefix S)
    (hc : ∀ x, ∃ i ∈ I, x ∈ (p i).brick) :
    ∃ b : S →₀ ℕ, ∀ z : Prefix.Grid b, ∃ i ∈ I,
      Prefix.Extends (p i) (Prefix.gridPrefix b z) := by
  classical
  let b : S →₀ ℕ := ∑ i ∈ I, (p i).lengths
  refine ⟨b,?_⟩
  intro z
  let x : Box S := (Prefix.gridPrefix b z).chart (fun _ _ => false)
  obtain ⟨i,hi,hix⟩ := hc x
  refine ⟨i,hi,Prefix.extends_of_mem_of_length_le hix (Prefix.chart_mem_brick _ _) ?_⟩
  intro s
  rw [Prefix.gridPrefix_length]
  change (p i).lengths s ≤ b s
  have hl : (p i).lengths ≤ ∑ j ∈ I, (p j).lengths :=
    Finset.single_le_sum (f := fun j => (p j).lengths) (fun _ _ s => Nat.zero_le _) hi
  exact hl s

lemma hasTable_of_isLocal {f : Equiv.Perm (Box S)} (hf : IsLocal ρ f) : HasTable ρ f := by
  classical
  obtain ⟨I,p,q,a,he,hc⟩ := finite_local_cover ρ hf
  obtain ⟨b,hb⟩ := finite_grid_refinement I p hc
  choose i hi hr using hb
  let r : Prefix.Grid b → Prefix S := Prefix.gridPrefix b
  let t : Prefix.Grid b → Prefix S := fun z =>
    Prefix.append (q (i z)) ((Prefix.suffix (p (i z)) (r z)).permute (ρ (a (i z))))
  have hchart (z : Prefix.Grid b) (y : Box S) :
      f ((r z).chart y) = (t z).chart (twist ρ (a (i z)) y) := by
    change f ((Prefix.gridPrefix b z).chart y) = _
    nth_rw 1 [← Prefix.append_suffix (hr z)]
    rw [Prefix.chart_append,he,twist_chart,← Prefix.chart_append]
  have ht : IsPartition t := by
    intro x
    obtain ⟨z,hz,hzu⟩ := Prefix.grid_partition b (f.symm x)
    have hmem : x ∈ (t z).brick := by
      obtain ⟨y,hy⟩ := hz
      refine ⟨twist ρ (a (i z)) y,?_⟩
      rw [← hchart,hy,f.apply_symm_apply]
    refine ⟨z,hmem,?_⟩
    intro w hw
    apply hzu w
    obtain ⟨y,hy⟩ := hw
    refine ⟨twist ρ (a (i w))⁻¹ y,?_⟩
    apply f.injective
    rw [hchart,← twist_mul,mul_inv_cancel,twist_one,hy,f.apply_symm_apply]
  let e := Fintype.equivFin (Prefix.Grid b)
  let T : Table (A := A) (S := S) := {
    size := Fintype.card (Prefix.Grid b)
    dom := fun j => r (e.symm j)
    ran := fun j => t (e.symm j)
    label := fun j => a (i (e.symm j))
    dom_partition := by
      intro x
      obtain ⟨z,hz,hu⟩ := Prefix.grid_partition b x
      refine ⟨e z,by simpa using hz,?_⟩
      intro j hj
      exact (e.symm_apply_eq).mp (hu _ hj)
    ran_partition := by
      intro x
      obtain ⟨z,hz,hu⟩ := ht x
      refine ⟨e z,by simpa using hz,?_⟩
      intro j hj
      exact (e.symm_apply_eq).mp (hu _ hj) }
  exact ⟨T,fun j y => hchart (e.symm j) y⟩

lemma hasTable_iff_isLocal (f : Equiv.Perm (Box S)) :
    HasTable ρ f ↔ IsLocal ρ f :=
  ⟨isLocal_of_hasTable ρ,hasTable_of_isLocal ρ⟩

lemma locallyStandard_id : LocallyStandard ρ id := isLocal_one ρ

lemma locallyStandard_comp {f g : Box S → Box S} (hf : LocallyStandard ρ f)
    (hg : LocallyStandard ρ g) (hgi : Function.Injective g) :
    LocallyStandard ρ (f ∘ g) := by
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
    apply hgi
    rw [hg_ref,← twist_mul,mul_inv_cancel,twist_one,hy]
  refine ⟨p',s',b*a,hp',?_⟩
  intro y
  change f (g (p'.chart y)) = _
  rw [hg_ref,← hd,Prefix.chart_append,hf',twist_chart,← Prefix.chart_append]
  rw [twist_mul]

structure LocalEmbedding extends Box S ↪ Box S where
  locally_standard : LocallyStandard ρ toFun

namespace LocalEmbedding
instance : CoeFun (LocalEmbedding ρ) (fun _ => Box S → Box S) := ⟨fun h => h.toEmbedding⟩
@[ext] lemma ext {h k : LocalEmbedding ρ} (he : ∀ x, h x = k x) : h = k := by
  cases h; cases k
  simp_all only [mk.injEq]
  exact DFunLike.ext _ _ he

lemma injective (h : LocalEmbedding ρ) : Function.Injective h := h.toEmbedding.injective

def identity : LocalEmbedding ρ where
  toEmbedding := Function.Embedding.refl _
  locally_standard := locallyStandard_id ρ

@[simp] lemma identity_apply (x : Box S) : identity ρ x = x := rfl

def comp (h k : LocalEmbedding ρ) : LocalEmbedding ρ where
  toFun x := h (k x)
  inj' := h.injective.comp k.injective
  locally_standard := locallyStandard_comp ρ (f := h) (g := k)
    h.locally_standard k.locally_standard k.injective

@[simp] lemma comp_apply (h k : LocalEmbedding ρ) (x : Box S) : comp ρ h k x = h (k x) := rfl
lemma comp_assoc (h k l : LocalEmbedding ρ) : comp ρ (comp ρ h k) l = comp ρ h (comp ρ k l) := rfl
@[simp] lemma identity_comp (h : LocalEmbedding ρ) : comp ρ (identity ρ) h = h := by ext; rfl
@[simp] lemma comp_identity (h : LocalEmbedding ρ) : comp ρ h (identity ρ) = h := by ext; rfl

def ofPrefix (p : Prefix S) : LocalEmbedding ρ where
  toEmbedding := ⟨p.chart,p.chart_injective⟩
  locally_standard := by
    intro x
    refine ⟨Prefix.empty,p,1,by simp,?_⟩
    intro y
    simp
@[simp] lemma ofPrefix_apply (p : Prefix S) (x : Box S) : ofPrefix ρ p x = p.chart x := rfl

def global (a : A) : LocalEmbedding ρ where
  toEmbedding := (twist ρ a).toEmbedding
  locally_standard := by
    intro x
    exact ⟨Prefix.empty,Prefix.empty,a,by simp,fun _ => rfl⟩
@[simp] lemma global_apply (a : A) (x : Box S) : global ρ a x = twist ρ a x := rfl
@[simp] lemma global_one : global ρ 1 = identity ρ := by ext; simp
lemma global_mul (a b : A) : global ρ (a*b) = comp ρ (global ρ a) (global ρ b) := by
  apply LocalEmbedding.ext
  intro x
  exact twist_mul ρ a b x

def ofGroup (g : localGroup ρ) : LocalEmbedding ρ where
  toEmbedding := g.val.toEmbedding
  locally_standard := g.property
@[simp] lemma ofGroup_apply (g : localGroup ρ) (x : Box S) : ofGroup ρ g x = g.val x := rfl

def Gauge (h k : LocalEmbedding ρ) : Prop := ∃ a : A, h = comp ρ k (global ρ a)

lemma gauge_refl (h : LocalEmbedding ρ) : Gauge ρ h h := by
  refine ⟨1,?_⟩; simp
lemma gauge_symm {h k : LocalEmbedding ρ} (he : Gauge ρ h k) : Gauge ρ k h := by
  obtain ⟨a,rfl⟩ := he
  refine ⟨a⁻¹,?_⟩
  ext x
  simp only [comp_apply,global_apply,← twist_mul,mul_inv_cancel,twist_one]
lemma gauge_trans {h k l : LocalEmbedding ρ} (hh : Gauge ρ h k) (hk : Gauge ρ k l) :
    Gauge ρ h l := by
  obtain ⟨a,rfl⟩ := hh
  obtain ⟨b,rfl⟩ := hk
  refine ⟨b*a,?_⟩
  ext x
  simp only [comp_apply,global_apply,twist_mul]

instance gaugeSetoid : Setoid (LocalEmbedding ρ) where
  r := Gauge ρ
  iseqv := ⟨gauge_refl ρ,fun h => gauge_symm ρ h,fun h k => gauge_trans ρ h k⟩

lemma gauge_range_eq {h k : LocalEmbedding ρ} (he : Gauge ρ h k) : Set.range h = Set.range k := by
  obtain ⟨a,rfl⟩ := he
  change Set.range (k ∘ twist ρ a) = _
  rw [Set.range_comp,Set.range_eq_univ.mpr (twist ρ a).surjective,Set.image_univ]

lemma gauge_comp_left (g : LocalEmbedding ρ) {h k : LocalEmbedding ρ} (he : Gauge ρ h k) :
    Gauge ρ (comp ρ g h) (comp ρ g k) := by
  obtain ⟨a,rfl⟩ := he
  exact ⟨a,rfl⟩

end LocalEmbedding

def GermBrick := Quotient (LocalEmbedding.gaugeSetoid ρ)

namespace GermBrick

def mk (h : LocalEmbedding ρ) : GermBrick ρ := Quotient.mk' h

def region : GermBrick ρ → Set (Box S) :=
  Quotient.lift (fun h : LocalEmbedding ρ => Set.range h) (fun _ _ he => LocalEmbedding.gauge_range_eq ρ he)
@[simp] lemma region_mk (h : LocalEmbedding ρ) : region ρ (mk ρ h) = Set.range h := rfl

lemma region_nonempty (b : GermBrick ρ) : (region ρ b).Nonempty := by
  induction b using Quotient.inductionOn with | h h =>
    exact ⟨h (fun _ _ => false),⟨fun _ _ => false,rfl⟩⟩

def map (g : LocalEmbedding ρ) : GermBrick ρ → GermBrick ρ :=
  Quotient.map (LocalEmbedding.comp ρ g) (fun _ _ he => LocalEmbedding.gauge_comp_left ρ g he)
@[simp] lemma map_mk (g h : LocalEmbedding ρ) : map ρ g (mk ρ h) = mk ρ (LocalEmbedding.comp ρ g h) := rfl

@[simp] lemma map_identity (b : GermBrick ρ) : map ρ (LocalEmbedding.identity ρ) b = b := by
  induction b using Quotient.inductionOn with | h h =>
    change mk ρ (LocalEmbedding.comp ρ (LocalEmbedding.identity ρ) h) = mk ρ h
    rw [LocalEmbedding.identity_comp]
lemma map_comp (g h : LocalEmbedding ρ) (b : GermBrick ρ) :
    map ρ (LocalEmbedding.comp ρ g h) b = map ρ g (map ρ h b) := by
  induction b using Quotient.inductionOn with | h k => rfl

lemma region_map (g : LocalEmbedding ρ) (b : GermBrick ρ) :
    region ρ (map ρ g b) = g '' region ρ b := by
  induction b using Quotient.inductionOn with | h h =>
    exact Set.range_comp g h

end GermBrick
end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace LocalEmbedding

@[simp] lemma ofGroup_one : ofGroup ρ 1 = identity ρ := rfl
lemma ofGroup_mul (g h : localGroup ρ) :
    ofGroup ρ (g*h) = comp ρ (ofGroup ρ g) (ofGroup ρ h) := rfl
@[simp] lemma ofPrefix_empty : ofPrefix ρ Prefix.empty = identity ρ := rfl
lemma ofPrefix_append (p q : Prefix S) :
    ofPrefix ρ (p.append q) = comp ρ (ofPrefix ρ p) (ofPrefix ρ q) := by
  apply LocalEmbedding.ext
  intro x
  exact Prefix.chart_append p q x
lemma global_ofPrefix (a : A) (p : Prefix S) :
    comp ρ (global ρ a) (ofPrefix ρ p) =
      comp ρ (ofPrefix ρ (p.permute (ρ a))) (global ρ a) := by
  apply LocalEmbedding.ext
  intro x
  exact twist_chart ρ a p x

end LocalEmbedding
namespace GermBrick

noncomputable def representative (b : GermBrick ρ) : LocalEmbedding ρ := Quotient.out b
@[simp] lemma mk_representative (b : GermBrick ρ) : mk ρ (representative ρ b) = b := Quotient.out_eq b
lemma mk_eq_iff (h k : LocalEmbedding ρ) : mk ρ h = mk ρ k ↔ LocalEmbedding.Gauge ρ h k :=
  Quotient.eq
lemma mk_gauge (h : LocalEmbedding ρ) (a : A) :
    mk ρ (LocalEmbedding.comp ρ h (LocalEmbedding.global ρ a)) = mk ρ h :=
  (mk_eq_iff ρ _ _).mpr ⟨a,rfl⟩

def groupEquiv (g : localGroup ρ) : Equiv.Perm (GermBrick ρ) where
  toFun := map ρ (LocalEmbedding.ofGroup ρ g)
  invFun := map ρ (LocalEmbedding.ofGroup ρ g⁻¹)
  left_inv b := by
    rw [← map_comp,← LocalEmbedding.ofGroup_mul,inv_mul_cancel,LocalEmbedding.ofGroup_one,map_identity]
  right_inv b := by
    rw [← map_comp,← LocalEmbedding.ofGroup_mul,mul_inv_cancel,LocalEmbedding.ofGroup_one,map_identity]

@[simp] lemma groupEquiv_apply (g : localGroup ρ) (b : GermBrick ρ) :
    groupEquiv ρ g b = map ρ (LocalEmbedding.ofGroup ρ g) b := rfl

def action : localGroup ρ →* Equiv.Perm (GermBrick ρ) where
  toFun := groupEquiv ρ
  map_one' := by apply Equiv.ext; intro b; exact map_identity ρ b
  map_mul' g h := by
    apply Equiv.ext
    intro b
    change map ρ (LocalEmbedding.ofGroup ρ (g*h)) b =
      map ρ (LocalEmbedding.ofGroup ρ g) (map ρ (LocalEmbedding.ofGroup ρ h) b)
    rw [LocalEmbedding.ofGroup_mul,map_comp]

lemma region_groupEquiv (g : localGroup ρ) (b : GermBrick ρ) :
    region ρ (groupEquiv ρ g b) = g.val '' region ρ b := region_map ρ _ _

def Restricts (c b : GermBrick ρ) : Prop :=
  ∃ (h : LocalEmbedding ρ) (p : Prefix S), b = mk ρ h ∧
    c = mk ρ (LocalEmbedding.comp ρ h (LocalEmbedding.ofPrefix ρ p))

lemma restricts_refl (b : GermBrick ρ) : Restricts ρ b b := by
  refine ⟨representative ρ b,Prefix.empty,?_,?_⟩ <;> simp

lemma restricts_trans {a b c : GermBrick ρ} (hab : Restricts ρ a b) (hbc : Restricts ρ b c) :
    Restricts ρ a c := by
  obtain ⟨h,p,hc,rfl⟩ := hbc
  obtain ⟨k,q,hk,rfl⟩ := hab
  obtain ⟨α,hk'⟩ := (mk_eq_iff ρ _ _).mp hk.symm
  subst k
  refine ⟨h,p.append (q.permute (ρ α)),hc,?_⟩
  rw [LocalEmbedding.ofPrefix_append]
  simp only [LocalEmbedding.comp_assoc]
  rw [LocalEmbedding.global_ofPrefix]
  simp only [← LocalEmbedding.comp_assoc]
  exact mk_gauge ρ _ α

lemma region_subset_of_restricts {a b : GermBrick ρ} (hab : Restricts ρ a b) :
    region ρ a ⊆ region ρ b := by
  obtain ⟨h,p,rfl,rfl⟩ := hab
  rintro _ ⟨x,rfl⟩
  exact ⟨p.chart x,rfl⟩

lemma restricts_map (g : LocalEmbedding ρ) {a b : GermBrick ρ} (hab : Restricts ρ a b) :
    Restricts ρ (map ρ g a) (map ρ g b) := by
  obtain ⟨h,p,rfl,rfl⟩ := hab
  exact ⟨LocalEmbedding.comp ρ g h,p,rfl,rfl⟩

lemma restricts_prefix {p r : Prefix S} (h : Prefix.Extends p r) :
    Restricts ρ (mk ρ (LocalEmbedding.ofPrefix ρ r)) (mk ρ (LocalEmbedding.ofPrefix ρ p)) := by
  refine ⟨LocalEmbedding.ofPrefix ρ p,p.suffix r,rfl,?_⟩
  rw [← LocalEmbedding.ofPrefix_append,Prefix.append_suffix h]

end GermBrick

structure Basis where
  pieces : Finset (GermBrick ρ)
  partition : ∀ x : Box S, ∃! b : {b // b ∈ pieces}, x ∈ GermBrick.region ρ b.1

namespace Basis

instance : CoeSort (Basis ρ) (Type _) := ⟨fun B => {b // b ∈ B.pieces}⟩
instance (B : Basis ρ) : Fintype B := inferInstanceAs (Fintype {b // b ∈ B.pieces})

def rank (B : Basis ρ) : ℕ := B.pieces.card

noncomputable def chart (B : Basis ρ) (b : B) : LocalEmbedding ρ :=
  GermBrick.representative ρ b.1
lemma chart_region (B : Basis ρ) (b : B) : Set.range (chart ρ B b) = GermBrick.region ρ b.1 := by
  change GermBrick.region ρ (GermBrick.mk ρ (GermBrick.representative ρ b.1)) = _
  rw [GermBrick.mk_representative]

noncomputable def evaluate (B : Basis ρ) (z : B × Box S) : Box S := chart ρ B z.1 z.2

lemma evaluate_bijective (B : Basis ρ) : Function.Bijective (evaluate ρ B) := by
  constructor
  · rintro ⟨b,x⟩ ⟨c,y⟩ h
    have hb : evaluate ρ B (b,x) ∈ GermBrick.region ρ b.1 := by
      rw [← chart_region]
      exact ⟨x,rfl⟩
    have hc : evaluate ρ B (b,x) ∈ GermBrick.region ρ c.1 := by
      rw [h,← chart_region]
      exact ⟨y,rfl⟩
    have he := (B.partition (evaluate ρ B (b,x))).unique hb hc
    subst c
    have hxy : x = y := (chart ρ B b).toEmbedding.injective h
    subst y
    rfl
  · intro x
    obtain ⟨b,hb,_⟩ := B.partition x
    rw [← chart_region ρ B b] at hb
    obtain ⟨y,rfl⟩ := hb
    exact ⟨(b,y),rfl⟩

noncomputable def equivalence (B : Basis ρ) : B × Box S ≃ Box S :=
  Equiv.ofBijective (evaluate ρ B) (evaluate_bijective ρ B)

@[simp] lemma equivalence_apply (B : Basis ρ) (z : B × Box S) :
    equivalence ρ B z = chart ρ B z.1 z.2 := rfl

noncomputable def trivial : Basis ρ := by
  classical
  exact {
    pieces := {GermBrick.mk ρ (LocalEmbedding.identity ρ)}
    partition := fun x => ⟨⟨_,Finset.mem_singleton_self _⟩,⟨x,rfl⟩,fun b _ =>
      Subtype.ext (Finset.mem_singleton.mp b.property)⟩ }

noncomputable def translate (g : localGroup ρ) (B : Basis ρ) : Basis ρ := by
  classical
  exact {
    pieces := B.pieces.map (GermBrick.groupEquiv ρ g).toEmbedding
    partition := by
      intro x
      obtain ⟨b,hb,hu⟩ := B.partition (g.val.symm x)
      let c : {c // c ∈ B.pieces.map (GermBrick.groupEquiv ρ g).toEmbedding} :=
        ⟨GermBrick.groupEquiv ρ g b.1,Finset.mem_map.mpr ⟨b.1,b.property,rfl⟩⟩
      refine ⟨c,?_,?_⟩
      · change x ∈ GermBrick.region ρ (GermBrick.groupEquiv ρ g b.1)
        rw [GermBrick.region_groupEquiv]
        exact ⟨g.val.symm x,hb,g.val.apply_symm_apply x⟩
      · intro d hd
        obtain ⟨e,he,hed⟩ := Finset.mem_map.mp d.property
        have hd' : g.val.symm x ∈ GermBrick.region ρ e := by
          rw [← hed] at hd
          change x ∈ GermBrick.region ρ (GermBrick.groupEquiv ρ g e) at hd
          rw [GermBrick.region_groupEquiv] at hd
          obtain ⟨y,hy,hyx⟩ := hd
          have hey : y = g.val.symm x := (g.val.eq_symm_apply).mpr hyx
          rwa [hey] at hy
        have hh : (⟨e,he⟩ : B) = b := hu _ hd'
        apply Subtype.ext
        exact hed.symm.trans (congrArg (GermBrick.groupEquiv ρ g) (congrArg Subtype.val hh)) }

@[simp] lemma rank_translate (g : localGroup ρ) (B : Basis ρ) :
    rank ρ (translate ρ g B) = rank ρ B := Finset.card_map _

def Refines (B C : Basis ρ) : Prop :=
  ∀ c : C, ∃ b : B, GermBrick.Restricts ρ c.1 b.1

lemma refines_refl (B : Basis ρ) : Refines ρ B B := fun b => ⟨b,GermBrick.restricts_refl ρ b.1⟩
lemma refines_trans {B C D : Basis ρ} (hBC : Refines ρ B C) (hCD : Refines ρ C D) :
    Refines ρ B D := by
  intro d
  obtain ⟨c,hc⟩ := hCD d
  obtain ⟨b,hb⟩ := hBC c
  exact ⟨b,GermBrick.restricts_trans ρ hc hb⟩

end Basis
end TwistedBrin

end

end OAI
