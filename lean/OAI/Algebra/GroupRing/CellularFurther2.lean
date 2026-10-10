import Mathlib
import OAI.Algebra.GroupRing.HomotopyFunctor

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology

namespace GroupRingTopology.Cellular

section
open Set Metric Topology
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

/-- The actual attaching maps of a classical CW skeleton. -/
def skeletonBoundary (n : ℕ) (i : RelCWComplex.cell C n) :
    C(Attachment.Sphere n,Skeleton C n) :=
  ⟨fun x => ⟨characteristic n i (boundary n x),sphere_mem_skeleton n i x⟩,
    ((characteristic n i).continuous.comp (continuous_boundary n)).subtype_mk _⟩

def skeletonBase (n : ℕ) : C(Skeleton C n,Skeleton C (n+1)) :=
  ⟨fun x => ⟨x.1,skeleton_mono (Nat.le_succ n) x.2⟩,continuous_subtype_val.subtype_mk _⟩

def skeletonCell (n : ℕ) (i : RelCWComplex.cell C n) :
    C(Attachment.Disk n,Skeleton C (n+1)) :=
  ⟨fun x => ⟨characteristic n i x,characteristic_mem_skeleton (Nat.lt_succ_self n) i x⟩,
    (characteristic n i).continuous.subtype_mk _⟩

def skeletonAssembly (n : ℕ) : C(Attachment.Space (skeletonBoundary (C := C) n),Skeleton C (n+1)) :=
  Attachment.lift _ (skeletonBase n) (skeletonCell n) (fun _ _ => rfl)

lemma skeletonAssembly_base (n : ℕ) (x : Skeleton C n) :
    skeletonAssembly n (Attachment.base _ x) = skeletonBase n x :=
  Attachment.lift_base _ _ _ _ x

lemma skeletonAssembly_cell (n : ℕ) (i : RelCWComplex.cell C n) (x : Disk n) :
    skeletonAssembly n (Attachment.cell _ i x) = skeletonCell n i x :=
  Attachment.lift_cell _ _ _ _ i x

lemma skeletonAssembly_interior (n : ℕ) (i : RelCWComplex.cell C n) (x : Attachment.OpenDisk n) :
    skeletonAssembly n (Sum.inr ⟨i,x⟩) = skeletonCell n i (Attachment.interior n x) := by
  rw [← Attachment.cell_interior (skeletonBoundary n) i x,skeletonAssembly_cell]

lemma skeletonAssembly_injective (n : ℕ) : Function.Injective (skeletonAssembly (C := C) n) := by
  intro a b hab
  rcases a with a|⟨i,a⟩ <;> rcases b with b|⟨j,b⟩
  · change skeletonAssembly n (Attachment.base _ a) = skeletonAssembly n (Attachment.base _ b) at hab
    rw [skeletonAssembly_base,skeletonAssembly_base] at hab
    exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : Skeleton C (n+1) => z.1) hab))
  · have hh := congrArg Subtype.val hab
    rw [← show Attachment.base (skeletonBoundary n) a = Sum.inl a from rfl,
      skeletonAssembly_base,skeletonAssembly_interior] at hh
    have hm : a.1 ∈ CWComplex.openCell n j := ⟨b.1,b.2,hh.symm⟩
    exact False.elim (openCell_not_skeleton n j hm a.2)
  · have hh := congrArg Subtype.val hab
    rw [skeletonAssembly_interior,
      ← show Attachment.base (skeletonBoundary n) b = Sum.inl b from rfl,
      skeletonAssembly_base] at hh
    have hm : b.1 ∈ CWComplex.openCell n i := ⟨a.1,a.2,hh⟩
    exact False.elim (openCell_not_skeleton n i hm b.2)
  · have hh := congrArg Subtype.val hab
    rw [skeletonAssembly_interior,skeletonAssembly_interior] at hh
    have hij : i = j := by
      by_contra hne
      have hd := CWComplex.disjoint_openCell_of_ne (C := C) (i := i) (j := j)
        (fun h => hne (sigma_mk_injective h))
      exact Set.disjoint_left.mp hd ⟨a.1,a.2,rfl⟩ ⟨b.1,b.2,hh.symm⟩
    subst j
    have he : a = b := Subtype.ext ((RelCWComplex.map n i).injOn
      (by simpa only [RelCWComplex.source_eq] using a.2)
      (by simpa only [RelCWComplex.source_eq] using b.2) hh)
    subst b; rfl

lemma skeletonAssembly_surjective (n : ℕ) : Function.Surjective (skeletonAssembly (C := C) n) := by
  intro x
  have hx := x.2
  have heq : Skeleton C (n+1) = Skeleton C n ∪
      ⋃ i : RelCWComplex.cell C n,CWComplex.closedCell n i := by
    simpa only [Skeleton,Nat.cast_add,Nat.cast_one] using
      (CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) n).symm
  have hx' := (congrArg (fun S : Set X => x.1 ∈ S) heq).mp hx
  rcases hx' with hx|hx
  · exact ⟨Attachment.base _ ⟨x.1,hx⟩,skeletonAssembly_base n _⟩
  · obtain ⟨i,y,hy,he⟩ := Set.mem_iUnion.mp hx
    refine ⟨Attachment.cell _ i ⟨y,hy⟩,?_⟩
    rw [skeletonAssembly_cell]
    exact Subtype.ext he

lemma skeletonAssembly_closed (n : ℕ) : IsClosedMap (skeletonAssembly (C := C) n) := by
  intro S hS
  let e : Attachment.Space (skeletonBoundary (C := C) n) → X :=
    fun x => (skeletonAssembly n x).1
  have hei : Function.Injective e := Subtype.val_injective.comp (skeletonAssembly_injective n)
  have hclosed : IsClosed (e '' S) := by
    apply (CWComplex.closed (Skeleton C (n+1)) _ ?_).mpr
    · intro m j
      have hm : m < n+1 := by
        have hh : (m : ℕ∞) < ((n+1 : ℕ) : ℕ∞) := by
          simpa only [RelCWComplex.skeletonLT_I,Set.mem_ofPred_eq] using j.2
        exact_mod_cast hh
      have hu : ∃ u : C(Disk m,Attachment.Space (skeletonBoundary (C := C) n)),
          ∀ x, e (u x) = characteristic m j.1 x := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm|hm
        · refine ⟨⟨fun x => Attachment.base _
            ⟨characteristic m j.1 x,characteristic_mem_skeleton hm j.1 x⟩,
            (Attachment.continuous_base _).comp ((characteristic m j.1).continuous.subtype_mk _)⟩,?_⟩
          intro x; exact congrArg Subtype.val (skeletonAssembly_base n _)
        · subst m
          exact ⟨Attachment.cell _ j.1,fun x => congrArg Subtype.val (skeletonAssembly_cell n j.1 x)⟩
      obtain ⟨u,hu⟩ := hu
      have heq : (e '' S) ∩ CWComplex.closedCell m j =
          characteristic m j.1 '' (u ⁻¹' S) := by
        ext x
        constructor
        · rintro ⟨⟨y,hy,rfl⟩,z,hz,he⟩
          refine ⟨⟨z,hz⟩,?_,he⟩
          change u ⟨z,hz⟩ ∈ S
          have hh : u ⟨z,hz⟩ = y := hei ((hu _).trans he)
          rwa [hh]
        · rintro ⟨z,hz,rfl⟩
          exact ⟨⟨u z,hz,hu z⟩,z.1,z.2,rfl⟩
      rw [heq]
      exact ((hS.preimage u.continuous).isCompact.image (characteristic m j.1).continuous).isClosed
    · rintro x ⟨y,hy,rfl⟩
      exact (skeletonAssembly n y).2
  have h : IsClosed ((Subtype.val : Skeleton C (n+1) → X) ⁻¹' (e '' S)) :=
    hclosed.preimage continuous_subtype_val
  convert h using 1
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩; exact ⟨y,hy,rfl⟩
  · rintro ⟨y,hy,he⟩; exact ⟨y,hy,Subtype.ext he⟩

/-- A classical CW skeleton is literally the topological adjunction of the
previous skeleton and its disks, including arbitrary infinite cell families. -/
def skeletonHomeomorph (n : ℕ) :
    Attachment.Space (skeletonBoundary (C := C) n) ≃ₜ Skeleton C (n+1) :=
  (isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨(skeletonAssembly n).continuous,skeletonAssembly_closed n,
      skeletonAssembly_injective n,skeletonAssembly_surjective n⟩).homeomorph _
end

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)

omit [ContinuousConstSMul G X] in
include hσ in
lemma skeleton_smul_mem (n : ℕ) (g : G) {x : X} (hx : x ∈ Skeleton (univ : Set X) n) :
    g • x ∈ Skeleton (univ : Set X) n := by
  obtain ⟨m,hm,j,y,hy,rfl⟩ := (CWComplex.mem_skeletonLT_iff (C := (univ : Set X))).mp hx
  let i := (σ m).symm j
  have hj : σ m i = j := (σ m).apply_symm_apply j
  apply (CWComplex.mem_skeletonLT_iff (C := (univ : Set X))).mpr
  refine ⟨m,hm,σ m (g*i.1,i.2),y,hy,?_⟩
  rw [hσ]
  exact congrArg (fun j => g • RelCWComplex.map m j y) hj

def skeletonTranslate (n : ℕ) (g : G) : C(Skeleton (univ : Set X) n,Skeleton (univ : Set X) n) :=
  ⟨fun x => ⟨g • x.1,skeleton_smul_mem σ hσ n g x.2⟩,
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩

lemma skeletonTranslate_base (n : ℕ) (g : G) (x : Skeleton (univ : Set X) n) :
    skeletonTranslate σ hσ (n+1) g (skeletonBase n x) =
      skeletonBase n (skeletonTranslate σ hσ n g x) := rfl

lemma skeletonTranslate_cell (n : ℕ) (g h : G) (i : ι n) (x : Disk n) :
    skeletonTranslate σ hσ (n+1) g (skeletonCell n (σ n (h,i)) x) =
      skeletonCell n (σ n (g*h,i)) x := by
  apply Subtype.ext
  exact (hσ n g h i x.1).symm

variable {E : Type u} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]

lemma exists_equivariant_skeleton_extension (n : ℕ)
    (b : C(Skeleton (univ : Set X) n,E))
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)
    (hfill : ∀ a : C(Sphere n,E), ∃ d : C(Disk n,E), ∀ x, d (boundary n x) = a x) :
    ∃ e : C(Skeleton (univ : Set X) (n+1),E),
      (∀ x, e (skeletonBase n x) = b x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
  let a (i : ι n) := b.comp (skeletonBoundary n (σ n (1,i)))
  choose d hd using fun i => hfill (a i)
  let D (j : RelCWComplex.cell (univ : Set X) n) : C(Disk n,E) :=
    ⟨fun x => ((σ n).symm j).1 • d ((σ n).symm j).2 x,
      (continuous_const_smul _).comp (d _).continuous⟩
  have hD (j : RelCWComplex.cell (univ : Set X) n) (x : Sphere n) :
      D j (boundary n x) = b (skeletonBoundary n j x) := by
    obtain ⟨⟨g,i⟩,rfl⟩ := (σ n).surjective j
    change ((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 (boundary n x) = _
    rw [Equiv.symm_apply_apply,hd]
    change g • b (skeletonBoundary n (σ n (1,i)) x) = _
    rw [←hb]
    congr 1
    apply Subtype.ext
    exact (hσ n g 1 i x.1).symm.trans (by rw [mul_one]; rfl)
  let f := Attachment.lift (skeletonBoundary (C := (univ : Set X)) n) b D hD
  let e : C(Skeleton (univ : Set X) (n+1),E) := f.comp ⟨(skeletonHomeomorph n).symm,(skeletonHomeomorph n).symm.continuous⟩
  have he_base (x : Skeleton (univ : Set X) n) : e (skeletonBase n x) = b x := by
    change f ((skeletonHomeomorph n).symm (skeletonBase n x)) = _
    rw [←skeletonAssembly_base]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.base _ x))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have he_cell (j : RelCWComplex.cell (univ : Set X) n) (x : Disk n) :
      e (skeletonCell n j x) = D j x := by
    change f ((skeletonHomeomorph n).symm (skeletonCell n j x)) = _
    rw [←skeletonAssembly_cell]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.cell _ j x))) = _
    rw [Homeomorph.symm_apply_apply]
    exact Attachment.lift_cell _ _ _ _ _ _
  refine ⟨e,he_base,?_⟩
  intro g x
  obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
  cases y with
  | inl x =>
    change e (skeletonTranslate σ hσ (n+1) g (skeletonBase n x)) = g • e (skeletonBase n x)
    rw [skeletonTranslate_base,he_base,he_base,hb]
  | inr p =>
    obtain ⟨⟨h,i⟩,hj⟩ := (σ n).surjective p.1
    have heq : skeletonAssembly n (Sum.inr p) = skeletonCell n p.1 (Attachment.interior n p.2) := by
      exact skeletonAssembly_interior n p.1 p.2
    rw [heq,←hj,skeletonTranslate_cell,he_cell,he_cell]
    change ((σ n).symm (σ n (g*h,i))).1 • d ((σ n).symm (σ n (g*h,i))).2 _ =
      g • (((σ n).symm (σ n (h,i))).1 • d ((σ n).symm (σ n (h,i))).2 _)
    simp only [Equiv.symm_apply_apply,mul_smul]
end

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G B]

lemma exists_equivariant_skeleton_lift (n : ℕ) (p : C(E,B))
    (hp : ∀ (g : G) e, p (g • e) = g • p e) (hRLP : DiskRLP p)
    (F : C(Skeleton (univ : Set X) (n+1),B))
    (hF : ∀ (g : G) x, F (skeletonTranslate σ hσ (n+1) g x) = g • F x)
    (b : C(Skeleton (univ : Set X) n,E))
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)
    (hbF : ∀ x, p (b x) = F (skeletonBase n x)) :
    ∃ e : C(Skeleton (univ : Set X) (n+1),E),
      (∀ x, e (skeletonBase n x) = b x) ∧ (∀ x, p (e x) = F x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
  let a (i : ι n) := b.comp (skeletonBoundary n (σ n (1,i)))
  let c (i : ι n) := F.comp (skeletonCell n (σ n (1,i)))
  have hsq (i : ι n) (x : Sphere n) : p (a i x) = c i (boundary n x) := by
    change p (b (skeletonBoundary n (σ n (1,i)) x)) = F (skeletonCell n (σ n (1,i)) (boundary n x))
    rw [hbF]
    rfl
  choose d hd hf using fun i => hRLP n (a i) (c i) (hsq i)
  let D (j : RelCWComplex.cell (univ : Set X) n) : C(Disk n,E) :=
    ⟨fun x => ((σ n).symm j).1 • d ((σ n).symm j).2 x,
      (continuous_const_smul _).comp (d _).continuous⟩
  have hD (j : RelCWComplex.cell (univ : Set X) n) (x : Sphere n) :
      D j (boundary n x) = b (skeletonBoundary n j x) := by
    obtain ⟨⟨g,i⟩,rfl⟩ := (σ n).surjective j
    change ((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 (boundary n x) = _
    rw [Equiv.symm_apply_apply,hd]
    change g • b (skeletonBoundary n (σ n (1,i)) x) = _
    rw [←hb]
    congr 1
    apply Subtype.ext
    exact (hσ n g 1 i x.1).symm.trans (by rw [mul_one]; rfl)
  let f := Attachment.lift (skeletonBoundary (C := (univ : Set X)) n) b D hD
  let e : C(Skeleton (univ : Set X) (n+1),E) := f.comp ⟨(skeletonHomeomorph n).symm,(skeletonHomeomorph n).symm.continuous⟩
  have he_base (x : Skeleton (univ : Set X) n) : e (skeletonBase n x) = b x := by
    change f ((skeletonHomeomorph n).symm (skeletonBase n x)) = _
    rw [←skeletonAssembly_base]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.base _ x))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have he_cell (j : RelCWComplex.cell (univ : Set X) n) (x : Disk n) :
      e (skeletonCell n j x) = D j x := by
    change f ((skeletonHomeomorph n).symm (skeletonCell n j x)) = _
    rw [←skeletonAssembly_cell]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.cell _ j x))) = _
    rw [Homeomorph.symm_apply_apply]
    exact Attachment.lift_cell _ _ _ _ _ _
  have he (g : G) (x : Skeleton (univ : Set X) (n+1)) :
      e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
    obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
    cases y with
    | inl x =>
      change e (skeletonTranslate σ hσ (n+1) g (skeletonBase n x)) = g • e (skeletonBase n x)
      rw [skeletonTranslate_base,he_base,he_base,hb]
    | inr q =>
      obtain ⟨⟨h,i⟩,hj⟩ := (σ n).surjective q.1
      have heq : skeletonAssembly n (Sum.inr q) = skeletonCell n q.1 (Attachment.interior n q.2) :=
        skeletonAssembly_interior n q.1 q.2
      rw [heq,←hj,skeletonTranslate_cell,he_cell,he_cell]
      change ((σ n).symm (σ n (g*h,i))).1 • d ((σ n).symm (σ n (g*h,i))).2 _ =
        g • (((σ n).symm (σ n (h,i))).1 • d ((σ n).symm (σ n (h,i))).2 _)
      simp only [Equiv.symm_apply_apply,mul_smul]
  refine ⟨e,he_base,?_,he⟩
  intro x
  obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
  cases y with
  | inl x =>
    change p (e (skeletonBase n x)) = F (skeletonBase n x)
    rw [he_base,hbF]
  | inr q =>
    rw [skeletonAssembly_interior,he_cell]
    obtain ⟨⟨g,i⟩,hj⟩ := (σ n).surjective q.1
    rw [←hj]
    change p (((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 _) = _
    rw [Equiv.symm_apply_apply,hp,hf]
    change g • F (skeletonCell n (σ n (1,i)) _) = _
    rw [←hF,skeletonTranslate_cell,mul_one]
end

open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)
omit [MulAction G X] [ContinuousConstSMul G X] in
lemma isEmpty_skeleton_zero : IsEmpty (Skeleton (univ : Set X) 0) := by
  refine ⟨fun x => ?_⟩
  have hx := x.2
  change x.1 ∈ (CWComplex.skeletonLT (univ : Set X) 0 : Set X) at hx
  rw [CWComplex.skeletonLT_zero_eq_empty] at hx
  exact hx

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G B]

lemma exists_equivariant_lift_on_skeleton (d : ℕ) (p : C(E,B))
    (hp : ∀ (g : G) e, p (g • e) = g • p e) (hRLP : DiskRLP p)
    (F : C(Skeleton (univ : Set X) d,B))
    (hF : ∀ (g : G) x, F (skeletonTranslate σ hσ d g x) = g • F x) :
    ∃ e : C(Skeleton (univ : Set X) d,E), (∀ x, p (e x) = F x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ d g x) = g • e x := by
  induction d with
  | zero =>
    let := isEmpty_skeleton_zero (X := X)
    exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun x => isEmptyElim x,fun _ x => isEmptyElim x⟩
  | succ d ih =>
    obtain ⟨b,hbF,hb⟩ := ih (F.comp (skeletonBase d)) (fun g x => by
      change F (skeletonBase d (skeletonTranslate σ hσ d g x)) = g • F (skeletonBase d x)
      rw [←skeletonTranslate_base,hF])
    obtain ⟨e,_,heF,he⟩ := exists_equivariant_skeleton_lift σ hσ d p hp hRLP F hF b hb hbF
    exact ⟨e,heF,he⟩

lemma exists_equivariant_map_on_skeleton (d : ℕ)
    (hfill : ∀ n < d, ∀ a : C(Sphere n,E), ∃ e : C(Disk n,E), ∀ x, e (boundary n x) = a x) :
    ∃ e : C(Skeleton (univ : Set X) d,E),
      ∀ (g : G) x, e (skeletonTranslate σ hσ d g x) = g • e x := by
  induction d with
  | zero =>
    let := isEmpty_skeleton_zero (X := X)
    exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun _ x => isEmptyElim x⟩
  | succ d ih =>
    obtain ⟨b,hb⟩ := ih (fun n hn => hfill n (Nat.lt_succ_of_lt hn))
    obtain ⟨e,_,he⟩ := exists_equivariant_skeleton_extension σ hσ d b hb (hfill d (Nat.lt_succ_self d))
    exact ⟨e,he⟩

variable {Y : Type u} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
lemma exists_equivariant_homotopy_on_skeleton (d : ℕ) (hY : SphereFillable Y)
    (a b : C(Skeleton (univ : Set X) d,Y))
    (ha : ∀ (g : G) x, a (skeletonTranslate σ hσ d g x) = g • a x)
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ d g x) = g • b x) :
    ∃ H : a.Homotopy b, ∀ (g : G) t x,
      H (t,skeletonTranslate σ hσ d g x) = g • H (t,x) := by
  let F : C(Skeleton (univ : Set X) d,Y × Y) := a.prodMk b
  have hF (g : G) x : F (skeletonTranslate σ hσ d g x) = g • F x := by
    exact Prod.ext (ha g x) (hb g x)
  obtain ⟨e,heF,he⟩ := exists_equivariant_lift_on_skeleton σ hσ d pathEndpoint
    (fun _ _ => rfl) (pathEndpoint_RLP hY) F hF
  let H : a.Homotopy b :=
    { toFun := fun z => e z.2 z.1
      continuous_toFun := e.continuous.comp continuous_snd |>.eval continuous_fst
      map_zero_left := fun x => congrArg Prod.fst (heF x)
      map_one_left := fun x => congrArg Prod.snd (heF x) }
  refine ⟨H,?_⟩
  intro g t x
  exact ContinuousMap.congr_fun (he g x) t

omit [MulAction G X] [ContinuousConstSMul G X] in
def skeletonChart (n m : ℕ) (hm : m < n) (i : RelCWComplex.cell (univ : Set X) m) :
    C(Disk m,Skeleton (univ : Set X) n) :=
  ⟨fun z => ⟨characteristic m i z,characteristic_mem_skeleton hm i z⟩,
    (characteristic m i).continuous.subtype_mk _⟩

lemma skeleton_compact_representatives (n : ℕ) [∀ m,Finite (ι m)] :
    ∃ K : Set (Skeleton (univ : Set X) n), IsCompact K ∧
      ∀ x, ∃ g : G, ∃ y ∈ K, x = skeletonTranslate σ hσ n g y := by
  let K := ⋃ m : Fin n, ⋃ i : ι m, Set.range (skeletonChart n m m.2 (σ m (1,i)))
  have hK : IsCompact K := isCompact_iUnion fun m => isCompact_iUnion fun i =>
    isCompact_range (skeletonChart n m m.2 (σ m (1,i))).continuous
  refine ⟨K,hK,?_⟩
  intro x
  obtain ⟨m,hm,j,z,hz,hj⟩ := (CWComplex.mem_skeletonLT_iff (C := (univ : Set X))).mp x.2
  obtain ⟨⟨g,i⟩,rfl⟩ := (σ m).surjective j
  have hmn : m < n := by exact_mod_cast hm
  let y := skeletonChart n m hmn (σ m (1,i)) ⟨z,ball_subset_closedBall hz⟩
  refine ⟨g,y,Set.mem_iUnion.mpr ⟨⟨m,hmn⟩,Set.mem_iUnion.mpr ⟨i,Set.mem_range_self _⟩⟩,?_⟩
  apply Subtype.ext
  change x.1 = g • RelCWComplex.map m (σ m (1,i)) z
  rw [←hσ,mul_one]
  exact hj.symm
end GroupRingTopology.Cellular

end

end OAI
