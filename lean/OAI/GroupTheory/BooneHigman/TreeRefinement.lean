import OAI.GroupTheory.BooneHigman.FinitePresentation

namespace OAI

noncomputable section

/-!
Tree prefixes, common refinements, and quotient refinement relations.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type v}

lemma comp_left_injective (p : Prefix X) : Function.Injective p.comp := by
  intro q r h
  apply Prefix.ext
  intro x
  exact List.append_cancel_left (congrArg (fun t : Prefix X => t.word x) h)

lemma oneBit_comp_comm {x y : X} (hxy : x≠y) (a b : Bool) :
    (oneBit x a).comp (oneBit y b)=(oneBit y b).comp (oneBit x a) := by
  ext z
  by_cases hzx : z=x
  · subst z; simp [hxy]
  · by_cases hzy : z=y
    · subst z; simp [Ne.symm hxy]
    · simp [hzx,hzy]

lemma oneBit_comp_disjoint (x : X) {a b : Bool} (hab : a≠b) (p q : Prefix X) :
    (oneBit x a).comp p≠(oneBit x b).comp q := by
  intro he
  have hh := congrArg (fun t : Prefix X => t.word x) he
  simp only [comp_word,oneBit_word] at hh
  exact hab (List.cons.inj hh).1
end Prefix
namespace Tree
variable {X : Type v}

/-- Syntactic coherence generated exclusively by commuting two different
coordinate splits. No semantic equality is admitted as a generating relation. -/
inductive Coherent : Tree X → Tree X → Prop
  | refl (t) : Coherent t t
  | symm {s t} : Coherent s t → Coherent t s
  | trans {r s t} : Coherent r s → Coherent s t → Coherent r t
  | split (x) {a b c d} : Coherent a c → Coherent b d →
      Coherent (.split x a b) (.split x c d)
  | interchange {x y : X} (hxy : x≠y) (a b c d) :
      Coherent (.split x (.split y a b) (.split y c d))
        (.split y (.split x a c) (.split x b d))

instance leaves_nonempty (t : Tree X) : Nonempty t.Leaves := by
  induction t with
  | leaf => exact inferInstanceAs (Nonempty PUnit)
  | split x a b ha hb =>
    obtain ⟨i⟩ := ha
    exact ⟨Sum.inl i⟩

def brickSet (t : Tree X) : Set (Prefix X) := Set.range t.brick

@[simp] lemma brickSet_leaf : brickSet (.leaf : Tree X)={Prefix.empty} := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩; rfl
  · intro hp; exact ⟨PUnit.unit,hp.symm⟩

@[simp] lemma brickSet_split (x : X) (a b : Tree X) :
    brickSet (.split x a b)=
      (Prefix.oneBit x false).comp '' brickSet a ∪
      (Prefix.oneBit x true).comp '' brickSet b := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨a.brick i,⟨i,rfl⟩,rfl⟩
    | inr i => exact Or.inr ⟨b.brick i,⟨i,rfl⟩,rfl⟩
  · rintro (⟨q,⟨i,rfl⟩,rfl⟩|⟨q,⟨i,rfl⟩,rfl⟩)
    · exact ⟨Sum.inl i,rfl⟩
    · exact ⟨Sum.inr i,rfl⟩

lemma image_comp_comp (p q : Prefix X) (A : Set (Prefix X)) :
    p.comp '' (q.comp '' A)=(p.comp q).comp '' A := by
  rw [Set.image_image]
  congr 1
  funext r
  exact (Prefix.comp_assoc p q r).symm

lemma Coherent.brickSet_eq {s t : Tree X} (h : Coherent s t) : brickSet s=brickSet t := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | split x _ _ ih₁ ih₂ => simp only [brickSet_split,ih₁,ih₂]
  | @interchange x y hxy a b c d =>
    simp only [brickSet_split,Set.image_union,image_comp_comp]
    rw [Prefix.oneBit_comp_comm hxy false false,
      Prefix.oneBit_comp_comm hxy false true,
      Prefix.oneBit_comp_comm hxy true false,
      Prefix.oneBit_comp_comm hxy true true]
    ac_rfl

/-- If every leaf has already read a bit on x, the x split can be commuted
all the way to the root. This is the nontrivial coordinate-coherence step. -/
lemma extract_root (x : X) (t : Tree X)
    (h : ∀ i,(t.brick i).word x≠[]) :
    ∃ a b,Coherent t (.split x a b) := by
  induction t with
  | leaf => exact False.elim (h PUnit.unit rfl)
  | split y a b ha hb =>
    by_cases hyx : y=x
    · subst y; exact ⟨a,b,.refl _⟩
    · have hxa : ∀ i,(a.brick i).word x≠[] := by
        intro i hi
        apply h (Sum.inl i)
        change (Prefix.oneBit y false).word x ++ (a.brick i).word x=[]
        simp [Prefix.oneBit_word,Ne.symm hyx,hi]
      have hxb : ∀ i,(b.brick i).word x≠[] := by
        intro i hi
        apply h (Sum.inr i)
        change (Prefix.oneBit y true).word x ++ (b.brick i).word x=[]
        simp [Prefix.oneBit_word,Ne.symm hyx,hi]
      obtain ⟨a₀,a₁,ha'⟩ := ha hxa
      obtain ⟨b₀,b₁,hb'⟩ := hb hxb
      exact ⟨.split y a₀ b₀,.split y a₁ b₁,
        (Coherent.split y ha' hb').trans (.interchange hyx a₀ a₁ b₀ b₁)⟩

lemma brickSet_split_injective (x : X) {a b c d : Tree X}
    (h : brickSet (.split x a b)=brickSet (.split x c d)) :
    brickSet a=brickSet c ∧ brickSet b=brickSet d := by
  simp only [brickSet_split] at h
  have halves (β : Bool) (A B C D : Set (Prefix X))
      (he : (Prefix.oneBit x β).comp '' A ∪ (Prefix.oneBit x (!β)).comp '' B=
        (Prefix.oneBit x β).comp '' C ∪ (Prefix.oneBit x (!β)).comp '' D) : A=C := by
    apply Set.Subset.antisymm
    · intro p hp
      have hm : (Prefix.oneBit x β).comp p∈
          (Prefix.oneBit x β).comp '' C ∪ (Prefix.oneBit x (!β)).comp '' D := by
        rw [← he]; exact Or.inl ⟨p,hp,rfl⟩
      rcases hm with ⟨q,hq,hqp⟩|⟨q,hq,hqp⟩
      · exact (Prefix.comp_left_injective _ hqp) ▸ hq
      · exact False.elim (Prefix.oneBit_comp_disjoint x (by cases β <;> decide) _ _ hqp.symm)
    · intro p hp
      have hm : (Prefix.oneBit x β).comp p∈
          (Prefix.oneBit x β).comp '' A ∪ (Prefix.oneBit x (!β)).comp '' B := by
        rw [he]; exact Or.inl ⟨p,hp,rfl⟩
      rcases hm with ⟨q,hq,hqp⟩|⟨q,hq,hqp⟩
      · exact (Prefix.comp_left_injective _ hqp) ▸ hq
      · exact False.elim (Prefix.oneBit_comp_disjoint x (by cases β <;> decide) _ _ hqp.symm)
  refine ⟨halves false _ _ _ _ h,halves true (brickSet b) (brickSet a) (brickSet d) (brickSet c) ?_⟩
  simpa only [Bool.not_true,Set.union_comm] using h

lemma brickSet_eq_leaf {t : Tree X} (h : brickSet t=brickSet (.leaf : Tree X)) : t=.leaf := by
  cases t with
  | leaf => rfl
  | split x a b =>
    let i : a.Leaves := Classical.arbitrary a.Leaves
    have hm : (Tree.split x a b).brick (Sum.inl i)∈brickSet (.leaf : Tree X) :=
      h ▸ ⟨Sum.inl i,rfl⟩
    rw [brickSet_leaf,Set.mem_singleton_iff] at hm
    have he := congrArg (fun p : Prefix X => p.word x) hm
    simp [brick,Prefix.empty] at he

/-- Completeness of local interchange for finite coloured trees. The proof
uses tree induction and root extraction, not an equality-as-relation shortcut. -/
lemma coherent_of_brickSet_eq (s t : Tree X) (h : brickSet s=brickSet t) : Coherent s t := by
  induction s generalizing t with
  | leaf =>
    have ht := brickSet_eq_leaf h.symm
    subst t
    exact .refl _
  | split x a b ha hb =>
    have ht : ∀ i,(t.brick i).word x≠[] := by
      intro i hi
      have hm : t.brick i∈brickSet (.split x a b) := h.symm ▸ ⟨i,rfl⟩
      rcases hm with ⟨j,hj⟩
      have hje := congrArg (fun p : Prefix X => p.word x) hj
      cases j <;> simp [brick,hi] at hje
    obtain ⟨c,d,hcd⟩ := extract_root x t ht
    have he := h.trans hcd.brickSet_eq
    obtain ⟨hac,hbd⟩ := brickSet_split_injective x he
    exact (Coherent.split x (ha c hac) (hb d hbd)).trans hcd.symm

lemma coherent_iff_brickSet_eq (s t : Tree X) : Coherent s t ↔ brickSet s=brickSet t :=
  ⟨Coherent.brickSet_eq,coherent_of_brickSet_eq s t⟩

end Tree
end

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Tree
variable {X : Type v}

def mapColors (f : X → X) : Tree X → Tree X
  | .leaf => .leaf
  | .split x a b => .split (f x) (mapColors f a) (mapColors f b)

@[simp] lemma mapColors_id (t : Tree X) : mapColors id t=t := by
  induction t with
  | leaf => rfl
  | split x a b ha hb => simp [mapColors,ha,hb]

lemma mapColors_comp (f g : X → X) (t : Tree X) :
    mapColors f (mapColors g t)=mapColors (f ∘ g) t := by
  induction t with
  | leaf => rfl
  | split x a b ha hb => simp [mapColors,ha,hb]

lemma Coherent.mapColors {s t : Tree X} (h : Coherent s t) (f : X → X)
    (hf : Function.Injective f) : Coherent (mapColors f s) (mapColors f t) := by
  induction h with
  | refl t => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | split x _ _ ih₁ ih₂ => exact .split (f x) ih₁ ih₂
  | @interchange x y hxy a b c d =>
    exact .interchange (fun he => hxy (hf he)) _ _ _ _

variable {Γ : Type u} [Group Γ] [MulAction Γ X]

@[simp] lemma mapColors_smul_inv (g : Γ) (t : Tree X) :
    mapColors (fun x => g • x) (mapColors (fun x => g⁻¹ • x) t)=t := by
  rw [mapColors_comp]
  have he : (fun x : X => g • x) ∘ (fun x => g⁻¹ • x)=id := by
    funext x; exact smul_inv_smul g x
  rw [he,mapColors_id]

/-- A single coloured-interchange schema and its acting-group translates,
closed under tree contexts. The action's two-transitivity is not hidden in the
constructors: it is used explicitly in the completeness theorem below. -/
inductive OrbitCoherent (x₀ y₀ : X) : Tree X → Tree X → Prop
  | refl (t) : OrbitCoherent x₀ y₀ t t
  | symm {s t} : OrbitCoherent x₀ y₀ s t → OrbitCoherent x₀ y₀ t s
  | trans {r s t} : OrbitCoherent x₀ y₀ r s → OrbitCoherent x₀ y₀ s t → OrbitCoherent x₀ y₀ r t
  | split (x) {a b c d} : OrbitCoherent x₀ y₀ a c → OrbitCoherent x₀ y₀ b d →
      OrbitCoherent x₀ y₀ (.split x a b) (.split x c d)
  | conjugate (g : Γ) {s t} : OrbitCoherent x₀ y₀ s t →
      OrbitCoherent x₀ y₀ (mapColors (fun x => g • x) s) (mapColors (fun x => g • x) t)
  | interchange (a b c d) :
      OrbitCoherent x₀ y₀ (.split x₀ (.split y₀ a b) (.split y₀ c d))
        (.split y₀ (.split x₀ a c) (.split x₀ b d))

variable (x₀ y₀ : X) (h₀ : x₀≠y₀)

include h₀ in
lemma OrbitCoherent.coherent {s t : Tree X} (h : OrbitCoherent (Γ:=Γ) x₀ y₀ s t) :
    Coherent s t := by
  induction h with
  | refl t => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | split x _ _ ih₁ ih₂ => exact .split x ih₁ ih₂
  | conjugate g _ ih => exact ih.mapColors _ (MulAction.injective g)
  | interchange a b c d => exact .interchange h₀ a b c d

variable (htwo : ∀ x₁ x₂ y₁ y₂ : X,x₁≠x₂ → y₁≠y₂ →
  ∃ g : Γ,g • x₁=y₁ ∧ g • x₂=y₂)
include h₀ htwo

lemma coherent_orbit_complete {s t : Tree X} (h : Coherent s t) :
    OrbitCoherent (Γ:=Γ) x₀ y₀ s t := by
  induction h with
  | refl t => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | split x _ _ ih₁ ih₂ => exact .split x ih₁ ih₂
  | @interchange x y hxy a b c d =>
    obtain ⟨g,hgx,hgy⟩ := htwo x₀ y₀ x y h₀ hxy
    have hr : OrbitCoherent (Γ:=Γ) x₀ y₀
        (.split x₀ (.split y₀ (mapColors (fun z => g⁻¹ • z) a) (mapColors (fun z => g⁻¹ • z) b))
          (.split y₀ (mapColors (fun z => g⁻¹ • z) c) (mapColors (fun z => g⁻¹ • z) d)))
        (.split y₀ (.split x₀ (mapColors (fun z => g⁻¹ • z) a) (mapColors (fun z => g⁻¹ • z) c))
          (.split x₀ (mapColors (fun z => g⁻¹ • z) b) (mapColors (fun z => g⁻¹ • z) d))) :=
      .interchange _ _ _ _
    have hg := OrbitCoherent.conjugate g hr
    simpa only [mapColors,hgx,hgy,mapColors_smul_inv] using hg

lemma orbitCoherent_iff_brickSet_eq (s t : Tree X) :
    OrbitCoherent (Γ:=Γ) x₀ y₀ s t ↔ brickSet s=brickSet t := by
  constructor
  · intro h; exact (h.coherent x₀ y₀ h₀).brickSet_eq
  · intro h; exact coherent_orbit_complete x₀ y₀ h₀ htwo (coherent_of_brickSet_eq s t h)

end Tree
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
namespace Move
variable {x : X} {s t : Tree X}

lemma element_eq_of_leaves (h k : Move (Γ:=Γ) x s t) (he : h.leaves=k.leaves) :
    h.element=k.element := by
  rw [h.element_eq_chart,k.element_eq_chart,he]

/-- Symmetry of the two subtrees, with its literal untwisted cube chart. -/
def exchange [MulAction.IsPretransitive Γ X] (x : X) (a b : Tree X) :
    Move (Γ:=Γ) x (.split x a b) (.split x b a) where
  leaves := Equiv.sumComm _ _
  element := flip x
  mem_subgroup := flip_mem x
  chart i z := by
    cases i with
    | inl i =>
      change (flip (Γ:=Γ) x).val (((left x).comp (a.brick i)).attach z)=
        ((right x).comp (a.brick i)).attach z
      simpa only [left,right,Prefix.comp_attach,Bool.not_false] using
        flip_attach (Γ:=Γ) x false ((a.brick i).attach z)
    | inr i =>
      change (flip (Γ:=Γ) x).val (((right x).comp (b.brick i)).attach z)=
        ((left x).comp (b.brick i)).attach z
      simpa only [left,right,Prefix.comp_attach,Bool.not_true] using
        flip_attach (Γ:=Γ) x true ((b.brick i).attach z)
end Move
variable (x : X) [MulAction.IsPretransitive Γ X]

/-- The actual associator satisfies the pentagon, proved by its four leaf
charts, not imposed on the constructed group as an extra hypothesis. -/
lemma associator_pentagon :
    associator (Γ:=Γ) x * associator x =
      localize (left x) (associator x) * associator x * localize (right x) (associator x) := by
  let l : Tree X := .leaf
  let r := Move.rotate (Γ:=Γ) x l l l
  let h₁ := (Move.refl (Γ:=Γ) (x:=x) l).join r x
  let h₂ := Move.rotate (Γ:=Γ) x l (.split x l l) l
  let h₃ := r.join (Move.refl l) x
  let k₁ := Move.rotate (Γ:=Γ) x l l (.split x l l)
  let k₂ := Move.rotate (Γ:=Γ) x (.split x l l) l l
  have he : ((h₁.trans h₂).trans h₃).leaves=(k₁.trans k₂).leaves := by
    apply Equiv.ext
    intro i
    rcases i with i | i | i | i <;> rfl
  have hh := Move.element_eq_of_leaves ((h₁.trans h₂).trans h₃) (k₁.trans k₂) he
  simpa only [h₁,h₂,h₃,k₁,k₂,r,Move.trans,Move.join,Move.refl,Move.rotate,
    sumElement,map_one,one_mul,mul_one,mul_assoc] using hh.symm

/-- The actual associator and half swaps satisfy the symmetry hexagon. -/
lemma flip_hexagon :
    flip (Γ:=Γ) x = associator x * localize (right x) (flip x) * (associator x)⁻¹ *
      localize (left x) (flip x) * associator x := by
  let l : Tree X := .leaf
  let a := Move.rotate (Γ:=Γ) x l l l
  let c := Move.exchange (Γ:=Γ) x l l
  let h₁ := a
  let h₂ := c.join (Move.refl l) x
  let h₃ := a.symm
  let h₄ := (Move.refl l).join c x
  let h₅ := a
  let k := Move.exchange (Γ:=Γ) x l (.split x l l)
  have he : ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).leaves=k.leaves := by
    apply Equiv.ext
    intro i
    rcases i with i | i | i <;> rfl
  have hh := Move.element_eq_of_leaves ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅) k he
  simpa only [h₁,h₂,h₃,h₄,h₅,k,a,c,Move.trans,Move.join,Move.refl,Move.rotate,
    Move.exchange,Move.symm,sumElement,map_one,one_mul,mul_one,mul_assoc] using hh.symm

omit [MulAction.IsPretransitive Γ X] in
lemma associator_middle_naturality (g : group (Γ:=Γ) (X:=X)) :
    associator x * localize (right x) (localize (left x) g) * (associator x)⁻¹=
      localize (left x) (localize (right x) g) := by
  rw [← localize_comp,← localize_comp]
  exact localize_conj _ (associator_middle x) g

omit [MulAction.IsPretransitive Γ X] in
lemma associator_right_naturality (g : group (Γ:=Γ) (X:=X)) :
    associator x * localize (right x) (localize (right x) g) * (associator x)⁻¹=
      localize (right x) g := by
  rw [← localize_comp]
  exact localize_conj _ (associator_right x) g

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

/-- The lifted right localization is obtained by the actual half swap. -/
def rightLocalizationSeed : Seed (Γ:=Γ) x →* Seed (Γ:=Γ) x :=
  (MulAut.conj (flipWord x)).toMonoidHom.comp (localizationSeed x)

lemma evaluation_rightLocalizationSeed (w : Seed (Γ:=Γ) x) :
    evaluation (Γ:=Γ) x (rightLocalizationSeed x w)=
      localize (right x) (evaluation (Γ:=Γ) x w) := by
  change evaluation (Γ:=Γ) x (flipWord x * localizationSeed x w * (flipWord x)⁻¹)=_
  rw [map_mul,map_mul,map_inv,evaluation_flipWord,evaluation_localizationSeed]
  exact localize_conj _ (flip_left x) _

def structuralComm (g h : Seed (Γ:=Γ) x) : Seed (Γ:=Γ) x :=
  localizationSeed x g * rightLocalizationSeed x h *
    (localizationSeed x g)⁻¹ * (rightLocalizationSeed x h)⁻¹

def structuralMiddle (g : Seed (Γ:=Γ) x) : Seed (Γ:=Γ) x :=
  (associatorWord x * rightLocalizationSeed x (localizationSeed x g) * (associatorWord x)⁻¹) *
    (localizationSeed x (rightLocalizationSeed x g))⁻¹

def structuralRight (g : Seed (Γ:=Γ) x) : Seed (Γ:=Γ) x :=
  (associatorWord x * rightLocalizationSeed x (rightLocalizationSeed x g) * (associatorWord x)⁻¹) *
    (rightLocalizationSeed x g)⁻¹

def pentagonWord : Seed (Γ:=Γ) x :=
  (associatorWord x * associatorWord x) *
    (localizationSeed x (associatorWord x) * associatorWord x *
      rightLocalizationSeed x (associatorWord x))⁻¹

def hexagonWord : Seed (Γ:=Γ) x :=
  flipWord x * (associatorWord x * rightLocalizationSeed x (flipWord x) * (associatorWord x)⁻¹ *
    localizationSeed x (flipWord x) * associatorWord x)⁻¹

/-- All root-level structural laws are finite after checking naturality and
commutation only on a finite generating family of Seed. -/
def structuralRelations (s : Finset (Seed (Γ:=Γ) x)) : Finset (Seed (Γ:=Γ) x) :=
  (s ×ˢ s).image (fun gh => structuralComm x gh.1 gh.2) ∪
    s.image (structuralMiddle x) ∪ s.image (structuralRight x) ∪
      {flipWord x * flipWord x,pentagonWord x,hexagonWord x}

lemma evaluation_structuralComm (g h : Seed (Γ:=Γ) x) :
    evaluation x (structuralComm x g h)=1 := by
  simp only [structuralComm,map_mul,map_inv,evaluation_localizationSeed,evaluation_rightLocalizationSeed]
  rw [(half_copies_commute x (evaluation x g) (evaluation x h)).eq]
  group
lemma evaluation_structuralMiddle (g : Seed (Γ:=Γ) x) :
    evaluation x (structuralMiddle x g)=1 := by
  simp only [structuralMiddle,map_mul,map_inv,evaluation_associatorWord,
    evaluation_localizationSeed,evaluation_rightLocalizationSeed,associator_middle_naturality,mul_inv_cancel]
lemma evaluation_structuralRight (g : Seed (Γ:=Γ) x) :
    evaluation x (structuralRight x g)=1 := by
  simp only [structuralRight,map_mul,map_inv,evaluation_associatorWord,
    evaluation_rightLocalizationSeed,associator_right_naturality,mul_inv_cancel]
lemma evaluation_pentagonWord : evaluation (Γ:=Γ) x (pentagonWord (Γ:=Γ) x)=1 := by
  simp only [pentagonWord,map_mul,map_inv,evaluation_associatorWord,
    evaluation_localizationSeed,evaluation_rightLocalizationSeed]
  rw [← associator_pentagon,mul_inv_cancel]
lemma evaluation_hexagonWord : evaluation (Γ:=Γ) x (hexagonWord (Γ:=Γ) x)=1 := by
  simp only [hexagonWord,map_mul,map_inv,evaluation_associatorWord,evaluation_flipWord,
    evaluation_localizationSeed,evaluation_rightLocalizationSeed]
  rw [← flip_hexagon,mul_inv_cancel]

lemma structuralRelations_valid (s : Finset (Seed (Γ:=Γ) x)) :
    ∀ g∈structuralRelations x s,evaluation x g=1 := by
  intro g hg
  simp only [structuralRelations,Finset.mem_union,Finset.mem_image,Finset.mem_insert,
    Finset.mem_singleton] at hg
  rcases hg with ((⟨⟨g,h⟩,_,rfl⟩|⟨g,_,rfl⟩)|⟨g,_,rfl⟩)|(rfl|rfl|rfl)
  · exact evaluation_structuralComm x g h
  · exact evaluation_structuralMiddle x g
  · exact evaluation_structuralRight x g
  · rw [map_mul,evaluation_flipWord,flip_mul_self]
  · exact evaluation_pentagonWord x
  · exact evaluation_hexagonWord x

/-- Finitely presented structural quotient with genuine evaluation map.
The absence of an injectivity assertion is substantive: coloured coherence
and label covariance/completeness are still required for the main theorem. -/
abbrev StructuralQuotient (s : Finset (Seed (Γ:=Γ) x)) := LocalQuotient x s (structuralRelations x s)

instance structuralQuotient_finitelyPresented [Group.IsFinitelyPresented Γ]
    (s : Finset (Seed (Γ:=Γ) x)) : Group.IsFinitelyPresented (StructuralQuotient x s) := inferInstance

def structuralEvaluation (s : Finset (Seed (Γ:=Γ) x)) :
    StructuralQuotient x s →* group (Γ:=Γ) (X:=X) :=
  localEvaluation x s (structuralRelations x s) (structuralRelations_valid x s)

lemma structuralEvaluation_surjective (s : Finset (Seed (Γ:=Γ) x)) :
    Function.Surjective (structuralEvaluation x s) :=
  localEvaluation_surjective x s (structuralRelations x s) (structuralRelations_valid x s)

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X] (s : Finset (Seed (Γ:=Γ) x))

def structuralProject : Seed (Γ:=Γ) x →* StructuralQuotient x s :=
  FiniteLocalizationClosure.project _ _ _ _

lemma structuralProject_rel {g : Seed (Γ:=Γ) x} (hg : g∈structuralRelations x s) :
    structuralProject x s g=1 :=
  FiniteLocalizationClosure.project_base _ _ _ _ (Finset.mem_union_left _ hg)

lemma structuralProject_comm {g h : Seed (Γ:=Γ) x} (hg : g∈s) (hh : h∈s) :
    Commute (structuralProject x s (localizationSeed x g))
      (structuralProject x s (rightLocalizationSeed x h)) := by
  have hm : structuralComm x g h∈structuralRelations x s := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(g,h),Finset.mem_product.mpr ⟨hg,hh⟩,rfl⟩
  have he := structuralProject_rel x s hm
  simp only [structuralComm,map_mul,map_inv] at he
  apply mul_inv_eq_one.mp
  simpa only [mul_inv_rev,mul_assoc] using he

lemma structuralProject_middle {g : Seed (Γ:=Γ) x} (hg : g∈s) :
    structuralProject x s (associatorWord x * rightLocalizationSeed x (localizationSeed x g) *
      (associatorWord x)⁻¹)=structuralProject x s (localizationSeed x (rightLocalizationSeed x g)) := by
  have hm : structuralMiddle x g∈structuralRelations x s := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨g,hg,rfl⟩
  have he := structuralProject_rel x s hm
  change structuralProject x s (_*_⁻¹)=1 at he
  rw [map_mul,map_inv] at he
  exact mul_inv_eq_one.mp he

lemma structuralProject_right {g : Seed (Γ:=Γ) x} (hg : g∈s) :
    structuralProject x s (associatorWord x * rightLocalizationSeed x (rightLocalizationSeed x g) *
      (associatorWord x)⁻¹)=structuralProject x s (rightLocalizationSeed x g) := by
  have hm : structuralRight x g∈structuralRelations x s := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨g,hg,rfl⟩
  have he := structuralProject_rel x s hm
  change structuralProject x s (_*_⁻¹)=1 at he
  rw [map_mul,map_inv] at he
  exact mul_inv_eq_one.mp he

variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)
include hs

/-- Infinite naturality families are consequences of their finite generator
checks. This is an algebraic reduction, not an appeal to diagram coherence. -/
lemma structuralProject_comm_all (g h : Seed (Γ:=Γ) x) :
    Commute (structuralProject x s (localizationSeed x g))
      (structuralProject x s (rightLocalizationSeed x h)) :=
  commute_homs_of_generators (s : Set (Seed (Γ:=Γ) x)) hs
    ((structuralProject x s).comp (localizationSeed x))
    ((structuralProject x s).comp (rightLocalizationSeed x))
    (fun _ hg _ hh => structuralProject_comm x s hg hh) g h

lemma structuralProject_middle_all (g : Seed (Γ:=Γ) x) :
    structuralProject x s (associatorWord x * rightLocalizationSeed x (localizationSeed x g) *
      (associatorWord x)⁻¹)=structuralProject x s (localizationSeed x (rightLocalizationSeed x g)) := by
  have he : (structuralProject x s).comp
      ((MulAut.conj (associatorWord x)).toMonoidHom.comp
        ((rightLocalizationSeed x).comp (localizationSeed x)))=
      (structuralProject x s).comp ((localizationSeed x).comp (rightLocalizationSeed x)) := by
    apply MonoidHom.eq_of_eqOn_dense hs
    intro g hg
    exact structuralProject_middle x s hg
  exact DFunLike.congr_fun he g

lemma structuralProject_right_all (g : Seed (Γ:=Γ) x) :
    structuralProject x s (associatorWord x * rightLocalizationSeed x (rightLocalizationSeed x g) *
      (associatorWord x)⁻¹)=structuralProject x s (rightLocalizationSeed x g) := by
  have he : (structuralProject x s).comp
      ((MulAut.conj (associatorWord x)).toMonoidHom.comp
        ((rightLocalizationSeed x).comp (rightLocalizationSeed x)))=
      (structuralProject x s).comp (rightLocalizationSeed x) := by
    apply MonoidHom.eq_of_eqOn_dense hs
    intro g hg
    exact structuralProject_right x s hg
  exact DFunLike.congr_fun he g

lemma structuralProject_left_all (g : Seed (Γ:=Γ) x) :
    structuralProject x s (localizationSeed x (localizationSeed x g))=
      structuralProject x s (associatorWord x * localizationSeed x g * (associatorWord x)⁻¹) :=
  FiniteLocalizationClosure.twice_eq_conjugate _ _ _ _ hs g

/-- The endomorphism exists on the finitely presented structural quotient,
not just on its semantic image in the actual table group. -/
def structuralLocalization : StructuralQuotient x s →* StructuralQuotient x s :=
  FiniteLocalizationClosure.localization _ _ _ _ hs

lemma structuralLocalization_project (g : Seed (Γ:=Γ) x) :
    structuralLocalization x s hs (structuralProject x s g)=
      structuralProject x s (localizationSeed x g) := rfl

omit hs in
lemma structuralProject_flip_square :
    structuralProject x s (flipWord x) * structuralProject x s (flipWord x)=1 := by
  rw [← map_mul]
  exact structuralProject_rel x s (Finset.mem_union_right _ (by simp))

omit hs in
lemma structuralProject_pentagon : structuralProject x s (pentagonWord (Γ:=Γ) x)=1 :=
  structuralProject_rel x s (Finset.mem_union_right _ (by simp))

omit hs in
lemma structuralProject_hexagon : structuralProject x s (hexagonWord (Γ:=Γ) x)=1 :=
  structuralProject_rel x s (Finset.mem_union_right _ (by simp))

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X] (s : Finset (Seed (Γ:=Γ) x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

lemma structuralProject_surjective : Function.Surjective (structuralProject (Γ:=Γ) x s) :=
  QuotientGroup.mk'_surjective _

def structuralSymmetry : StructuralQuotient (Γ:=Γ) x s := structuralProject x s (flipWord x)
def structuralAssociator : StructuralQuotient (Γ:=Γ) x s := structuralProject x s (associatorWord x)

lemma structuralSymmetry_square : structuralSymmetry (Γ:=Γ) x s * structuralSymmetry x s=1 :=
  structuralProject_flip_square x s

lemma structuralSymmetry_inv : (structuralSymmetry (Γ:=Γ) x s)⁻¹=structuralSymmetry x s := by
  exact inv_eq_of_mul_eq_one_right (structuralSymmetry_square x s)

def structuralRightLocalization : StructuralQuotient (Γ:=Γ) x s →* StructuralQuotient x s :=
  (MulAut.conj (structuralSymmetry x s)).toMonoidHom.comp (structuralLocalization x s hs)

lemma structuralRightLocalization_project (g : Seed (Γ:=Γ) x) :
    structuralRightLocalization x s hs (structuralProject x s g)=
      structuralProject x s (rightLocalizationSeed x g) := by
  change structuralProject x s (flipWord x) * structuralProject x s (localizationSeed x g) *
    (structuralProject x s (flipWord x))⁻¹=structuralProject x s
      (flipWord x * localizationSeed x g * (flipWord x)⁻¹)
  simp only [map_mul,map_inv]

lemma structuralLocalizations_commute (g h : StructuralQuotient (Γ:=Γ) x s) :
    Commute (structuralLocalization x s hs g) (structuralRightLocalization x s hs h) := by
  obtain ⟨g,rfl⟩ := structuralProject_surjective x s g
  obtain ⟨h,rfl⟩ := structuralProject_surjective x s h
  rw [structuralLocalization_project,structuralRightLocalization_project]
  exact structuralProject_comm_all x s hs g h

/-- A genuine binary tensor homomorphism on the actual finite structural
quotient. Its functoriality follows from the finitely generated disjointness
relations, not from semantic equality after evaluation. -/
def structuralTensor : StructuralQuotient (Γ:=Γ) x s × StructuralQuotient x s →*
    StructuralQuotient x s :=
  (structuralLocalization x s hs).noncommCoprod (structuralRightLocalization x s hs)
    (structuralLocalizations_commute x s hs)

lemma structuralTensor_apply (g h : StructuralQuotient (Γ:=Γ) x s) :
    structuralTensor x s hs (g,h)=structuralLocalization x s hs g *
      structuralRightLocalization x s hs h := rfl

lemma structuralConjugate_left (g : StructuralQuotient (Γ:=Γ) x s) :
    structuralAssociator x s * structuralLocalization x s hs g * (structuralAssociator x s)⁻¹=
      structuralLocalization x s hs (structuralLocalization x s hs g) := by
  obtain ⟨g,rfl⟩ := structuralProject_surjective x s g
  symm
  simpa only [structuralAssociator,structuralLocalization_project,map_mul,map_inv] using
    structuralProject_left_all x s hs g

lemma structuralConjugate_middle (g : StructuralQuotient (Γ:=Γ) x s) :
    structuralAssociator x s * structuralRightLocalization x s hs (structuralLocalization x s hs g) *
      (structuralAssociator x s)⁻¹=
      structuralLocalization x s hs (structuralRightLocalization x s hs g) := by
  obtain ⟨g,rfl⟩ := structuralProject_surjective x s g
  simpa only [structuralAssociator,structuralLocalization_project,
    structuralRightLocalization_project,map_mul,map_inv] using structuralProject_middle_all x s hs g

lemma structuralConjugate_right (g : StructuralQuotient (Γ:=Γ) x s) :
    structuralAssociator x s * structuralRightLocalization x s hs (structuralRightLocalization x s hs g) *
      (structuralAssociator x s)⁻¹=structuralRightLocalization x s hs g := by
  obtain ⟨g,rfl⟩ := structuralProject_surjective x s g
  simpa only [structuralAssociator,structuralLocalization_project,
    structuralRightLocalization_project,map_mul,map_inv] using structuralProject_right_all x s hs g

/-- Associativity is natural for every morphism of the finite quotient. -/
lemma structuralTensor_associativity (g h k : StructuralQuotient (Γ:=Γ) x s) :
    structuralAssociator x s * structuralTensor x s hs (g,structuralTensor x s hs (h,k)) *
      (structuralAssociator x s)⁻¹=
      structuralTensor x s hs (structuralTensor x s hs (g,h),k) := by
  simp only [structuralTensor_apply,map_mul]
  calc
    _=(structuralAssociator x s * structuralLocalization x s hs g * (structuralAssociator x s)⁻¹) *
        (structuralAssociator x s * structuralRightLocalization x s hs (structuralLocalization x s hs h) *
          (structuralAssociator x s)⁻¹) *
        (structuralAssociator x s * structuralRightLocalization x s hs (structuralRightLocalization x s hs k) *
          (structuralAssociator x s)⁻¹) := by group
    _=_ := by rw [structuralConjugate_left,structuralConjugate_middle,structuralConjugate_right]

lemma structuralSymmetry_localization (g : StructuralQuotient (Γ:=Γ) x s) :
    structuralSymmetry x s * structuralRightLocalization x s hs g * (structuralSymmetry x s)⁻¹=
      structuralLocalization x s hs g := by
  change structuralSymmetry x s * (structuralSymmetry x s * structuralLocalization x s hs g *
    (structuralSymmetry x s)⁻¹) * (structuralSymmetry x s)⁻¹=_
  rw [structuralSymmetry_inv]
  have h := structuralSymmetry_square (Γ:=Γ) x s
  calc
    _=(structuralSymmetry x s * structuralSymmetry x s) * structuralLocalization x s hs g *
        (structuralSymmetry x s * structuralSymmetry x s) := by group
    _=_ := by rw [h,one_mul,mul_one]

/-- The symmetry is natural, using involutivity and disjointness inside the
finite quotient, not merely a relation holding in the semantic group. -/
lemma structuralTensor_symmetry (g h : StructuralQuotient (Γ:=Γ) x s) :
    structuralSymmetry x s * structuralTensor x s hs (g,h) * (structuralSymmetry x s)⁻¹=
      structuralTensor x s hs (h,g) := by
  rw [structuralTensor_apply,structuralTensor_apply]
  calc
    _=(structuralSymmetry x s * structuralLocalization x s hs g * (structuralSymmetry x s)⁻¹) *
      (structuralSymmetry x s * structuralRightLocalization x s hs h * (structuralSymmetry x s)⁻¹) := by group
    _=structuralRightLocalization x s hs g * structuralLocalization x s hs h := by
      rw [structuralSymmetry_localization]; rfl
    _=_ := (structuralLocalizations_commute x s hs h g).eq.symm

lemma structuralTensor_pentagon :
    structuralAssociator (Γ:=Γ) x s * structuralAssociator x s=
      structuralLocalization x s hs (structuralAssociator x s) * structuralAssociator x s *
        structuralRightLocalization x s hs (structuralAssociator x s) := by
  have h := structuralProject_pentagon (Γ:=Γ) x s
  simp only [pentagonWord,map_mul,map_inv] at h
  exact mul_inv_eq_one.mp h

lemma structuralTensor_hexagon :
    structuralSymmetry (Γ:=Γ) x s =
      structuralAssociator x s * structuralRightLocalization x s hs (structuralSymmetry x s) *
        (structuralAssociator x s)⁻¹ * structuralLocalization x s hs (structuralSymmetry x s) *
          structuralAssociator x s := by
  have h := structuralProject_hexagon (Γ:=Γ) x s
  simp only [hexagonWord,map_mul,map_inv] at h
  exact mul_inv_eq_one.mp h

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
