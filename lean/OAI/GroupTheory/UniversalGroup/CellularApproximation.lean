import OAI.GroupTheory.UniversalGroup.GeneralPosition

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

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

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

section
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
end

open Set Metric Topology
universe u v
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]
variable {K : Type v} [MetricSpace K] [CompactSpace K]

def skeletonInclusion (n : ℕ) : C(Skeleton C n,X) := ⟨Subtype.val,continuous_subtype_val⟩

lemma deform_skeleton_succ (n : ℕ) (f : C(K,Skeleton C (n+1)))
    (hdim : dimH (Set.univ : Set K) < n) :
    ∃ (g : C(K,Skeleton C n))
      (H : f.Homotopy ((skeletonBase n).comp g)),
      ∀ t x, (f x).1 ∈ Skeleton C n → H (t,x) = f x := by
  let e := skeletonHomeomorph (C := C) n
  let : T2Space (Attachment.Space (skeletonBoundary (C := C) n)) := e.symm.t2Space
  let f' : C(K,Attachment.Space (skeletonBoundary (C := C) n)) := (⟨e.symm,e.symm.continuous⟩ : C(_, _)).comp f
  obtain ⟨g,H,hH⟩ := Attachment.exists_deformation_into_base (skeletonBoundary (C := C) n) f' hdim
  have h0 : (⟨e,e.continuous⟩ : C(_, _)).comp f' = f := by apply ContinuousMap.ext; intro x; exact e.apply_symm_apply (f x)
  have h1 : (⟨e,e.continuous⟩ : C(_, _)).comp
      ((⟨Attachment.base _,Attachment.continuous_base _⟩ : C(_, _)).comp g) =
      (skeletonBase n).comp g := by apply ContinuousMap.ext; intro x; exact skeletonAssembly_base n (g x)
  let J := (ContinuousMap.Homotopy.refl (⟨e,e.continuous⟩ : C(_, _))).comp H
  refine ⟨g,J.cast h0 h1,?_⟩
  intro t x hx
  change e (H (t,x)) = f x
  have hr : f' x ∈ Set.range (Attachment.base (skeletonBoundary (C := C) n)) := by
    refine ⟨⟨(f x).1,hx⟩,?_⟩
    apply e.injective
    change skeletonAssembly n (Attachment.base _ _) = e (e.symm (f x))
    rw [skeletonAssembly_base,e.apply_symm_apply]
    rfl
  rw [hH t x hr]
  exact e.apply_symm_apply (f x)

lemma deform_bounded_skeleton (d m : ℕ) (f : C(K,Skeleton C m))
    (hdim : dimH (Set.univ : Set K) < d) :
    ∃ (g : C(K,Skeleton C d))
      (H : ((skeletonInclusion m).comp f).Homotopy ((skeletonInclusion d).comp g)),
      ∀ t x, (f x).1 ∈ Skeleton C d → H (t,x) = (f x).1 := by
  induction m with
  | zero =>
    let g : C(K,Skeleton C d) := ⟨fun x => ⟨(f x).1,skeleton_mono (Nat.zero_le d) (f x).2⟩,
      f.continuous.subtype_val.subtype_mk _⟩
    exact ⟨g,.refl _,fun _ _ _ => rfl⟩
  | succ m ih =>
    by_cases hmd : m+1 ≤ d
    · let g : C(K,Skeleton C d) := ⟨fun x => ⟨(f x).1,skeleton_mono hmd (f x).2⟩,
        f.continuous.subtype_val.subtype_mk _⟩
      exact ⟨g,.refl _,fun _ _ _ => rfl⟩
    · have hdm : d ≤ m := by omega
      obtain ⟨g,H,hH⟩ := deform_skeleton_succ m f (hdim.trans_le (by exact_mod_cast hdm))
      obtain ⟨g',J,hJ⟩ := ih g
      let H' : ((skeletonInclusion (C := C) (m+1)).comp f).Homotopy
          ((skeletonInclusion m).comp g) :=
        (ContinuousMap.Homotopy.refl (skeletonInclusion (C := C) (m+1))).comp H
      refine ⟨g',H'.trans J,?_⟩
      intro t x hx
      have hh (s : unitInterval) : H' (s,x) = (f x).1 := by
        exact congrArg Subtype.val (hH s x (skeleton_mono hdm hx))
      have hg : (g x).1 = (f x).1 := by
        have he := hh 1
        rw [ContinuousMap.Homotopy.apply_one] at he
        exact he
      have hj (s : unitInterval) : J (s,x) = (f x).1 := by
        rw [hJ s x (hg.symm ▸ hx),hg]
      rw [ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact hh _
      · exact hj _

theorem exists_cellular_approximation (d : ℕ) (f : C(K,X)) (hf : ∀ x,f x ∈ C)
    (hdim : dimH (Set.univ : Set K) < d) :
    ∃ (g : C(K,Skeleton C d)) (H : f.Homotopy ((skeletonInclusion d).comp g)),
      ∀ t x, f x ∈ Skeleton C d → H (t,x) = f x := by
  obtain ⟨m,hm⟩ := compactMap_bounded_skeleton f hf
  let f' : C(K,Skeleton C m) := ⟨fun x => ⟨f x,hm x⟩,f.continuous.subtype_mk _⟩
  exact deform_bounded_skeleton d m f' hdim
end UniversalFInfinity.Cellular
namespace UniversalFInfinity.SphereTopology
open Set Metric Topology
universe u
variable {Y : Type u} [TopologicalSpace Y]
lemma fill_zero [Nonempty Y] (a : C(Cellular.Sphere 0,Y)) :
    ∃ e : C(Cellular.Disk 0,Y), ∀ x, e (Cellular.boundary 0 x) = a x := by
  refine ⟨.const _ (Classical.choice ‹Nonempty Y›),?_⟩
  intro x
  have hx := x.2
  have hz : x.1 = 0 := Subsingleton.elim _ _
  simp only [hz,mem_sphere,dist_self] at hx
  exact False.elim (zero_ne_one hx)
lemma fill_one [PathConnectedSpace Y] (a : C(Cellular.Sphere 1,Y)) :
    ∃ e : C(Cellular.Disk 1,Y), ∀ x, e (Cellular.boundary 1 x) = a x := by
  let p := (PathConnectedSpace.joined (a Cayley.minus) (a Cayley.plus)).somePath
  let e : C(Cellular.Disk 1,Y) := p.toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩
  refine ⟨e,?_⟩
  intro x
  obtain rfl|rfl := Cayley.sphere_one_eq x
  · change p (Cayley.edgeTime (Attachment.boundary 1 Cayley.minus)) = _
    rw [Cayley.edgeTime_minus,p.source]
  · change p (Cayley.edgeTime (Attachment.boundary 1 Cayley.plus)) = _
    rw [Cayley.edgeTime_plus,p.target]
end UniversalFInfinity.SphereTopology

namespace UniversalFInfinity.Milnor

section
open Set Metric Topology Cellular
universe u
variable {G : Type u} [Group G]
variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u} [∀ m,Finite (ι m)]
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)

lemma controlled_skeleton_homotopy (d : ℕ) (a b : C(Skeleton (univ : Set X) d,Space G))
    (H : a.Homotopy b)
    (hH : ∀ (g : G) t x, H (t,skeletonTranslate σ hσ d g x) = g • H (t,x)) :
    ∃ S : Shapes G, Set.range H ⊆ Set.range (stageFull G S) := by
  obtain ⟨K,hK,hcov⟩ := skeleton_compact_representatives σ hσ d
  obtain ⟨S,hS⟩ := compact_orbit_controlled G ((isCompact_univ.prod hK).image H.continuous)
  refine ⟨S,?_⟩
  rintro _ ⟨⟨t,x⟩,rfl⟩
  obtain ⟨g,y,hy,rfl⟩ := hcov x
  rw [hH]
  exact hS g ⟨H (t,y),⟨(t,y),⟨Set.mem_univ _,hy⟩,rfl⟩,rfl⟩

end
open Set Metric Topology Cellular
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {A : Type u} [Finite A] (s : A → G)
variable (rels : Set (FreeGroup A)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)

include hrel in

lemma uniform_low_connectivity (hrels : rels.Finite)
    (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) (S : Shapes G) :
    ∃ (T : Shapes G) (hST : S ⊆ T), ∀ n : ℕ, n = 1 ∨ n = 2 →
      ∀ a : C(Sphere n,Stage G S), ∃ d : C(Disk n,Stage G T),
        ∀ x, d (boundary n x) = stageIncl G S T hST (a x) := by
  classical
  let Z := Cayley.PresentationCover s rels hrel
  let : PathConnectedSpace Z := Cayley.presentationCover_pathConnected s rels hrel hs
  let : CWComplex (univ : Set (Stage G S)) := stageEquivariantCW G S
  let σ : ∀ n, (G × CellOrbits G S n) ≃ RelCWComplex.cell (univ : Set (Stage G S)) n :=
    fun _ => Equiv.refl _
  have hσ : ∀ n (g h : G) (i : CellOrbits G S n) (x : Fin n → ℝ),
    RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x := by
    intro n g h i x
    exact mul_smul g h _
  have hfill : ∀ n < 2, ∀ a : C(Sphere n,Z), ∃ e : C(Disk n,Z),
      ∀ x, e (boundary n x) = a x := by
    intro n hn
    have hn' : n=0 ∨ n=1 := by omega
    rcases hn' with rfl|rfl
    · exact SphereTopology.fill_zero
    · exact SphereTopology.fill_one
  obtain ⟨r,hr⟩ := exists_equivariant_map_on_skeleton σ hσ 2 hfill
  obtain ⟨q,hq⟩ := presentation_equivariant_map s rels hrel
  obtain ⟨P,hP⟩ := equivariant_controlled G (presentation_compactFundamentalSet s rels hrel hrels) q hq
  let a := (stageFull G S).comp (skeletonInclusion (C := (univ : Set (Stage G S))) 2)
  let b := q.comp r
  have ha (g : G) x : a (skeletonTranslate σ hσ 2 g x) = g • a x :=
    stageFull_smul G S g x.1
  have hb (g : G) x : b (skeletonTranslate σ hσ 2 g x) = g • b x := by
    change q (r (skeletonTranslate σ hσ 2 g x)) = g • q (r x)
    rw [hr,hq]
  obtain ⟨H,hH⟩ := exists_equivariant_homotopy_on_skeleton σ hσ 2 (sphereFillable (1:G)) a b ha hb
  obtain ⟨Q,hQ⟩ := controlled_skeleton_homotopy σ hσ 2 a b H hH
  let T := S ∪ P ∪ Q
  have hST : S ⊆ T := Finset.subset_union_left.trans Finset.subset_union_left
  have hPT : P ⊆ T := Finset.subset_union_right.trans Finset.subset_union_left
  have hQT : Q ⊆ T := Finset.subset_union_right
  have hpT : Set.range q ⊆ Set.range (stageFull G T) := by
    rintro _ ⟨z,rfl⟩
    obtain ⟨y,hy⟩ := hP (Set.mem_range_self z)
    exact ⟨stageIncl G P T hPT y,hy⟩
  have hhT : Set.range H ⊆ Set.range (stageFull G T) := by
    rintro _ ⟨z,rfl⟩
    obtain ⟨y,hy⟩ := hQ (Set.mem_range_self z)
    exact ⟨stageIncl G Q T hQT y,hy⟩
  let qT := factorStage G q T hpT
  let HTmap := factorStage G H.toContinuousMap T hhT
  let inc := stageIncl G S T hST
  let HT : (inc.comp (skeletonInclusion (C := (univ : Set (Stage G S))) 2)).Homotopy (qT.comp r) :=
    { toContinuousMap := HTmap
      map_zero_left := fun x => by
        apply (stageFull_embedding G T).injective
        change stageFull G T (HTmap (0,x)) = stageFull G T (inc x.1)
        rw [factorStage_spec]
        exact H.apply_zero x
      map_one_left := fun x => by
        apply (stageFull_embedding G T).injective
        change stageFull G T (HTmap (1,x)) = stageFull G T (qT (r x))
        rw [factorStage_spec,factorStage_spec]
        exact H.apply_one x }
  refine ⟨T,hST,?_⟩
  intro n hn k
  have hdim : dimH (univ : Set (Sphere n)) < 2 := by
    rcases hn with rfl|rfl
    · exact (GeneralPosition.dimH_cube_boundary_subtype_le 0).trans_lt (by norm_num)
    · exact (GeneralPosition.dimH_cube_boundary_subtype_le 1).trans_lt (by norm_num)
  let : Nonempty (Sphere n) := by
    rcases hn with rfl|rfl
    · exact SphereTopology.sphere_nonempty 0
    · exact SphereTopology.sphere_nonempty 1
  obtain ⟨v,J,_⟩ := exists_cellular_approximation 2 k (fun _ => Set.mem_univ _) hdim
  have hz : SphereTopology.Extends (r.comp v) := by
    rcases hn with rfl|rfl
    · obtain ⟨e,he⟩ := SphereTopology.fill_one (r.comp v)
      exact ⟨e,ContinuousMap.ext he⟩
    · exact Cayley.presentationCover_sphereFill s rels hrel hs hker (r.comp v)
  obtain ⟨e,he⟩ := hz
  have hzT : SphereTopology.Extends ((qT.comp r).comp v) := by
    refine ⟨qT.comp e,?_⟩
    apply ContinuousMap.ext; intro x
    exact congrArg qT (ContinuousMap.congr_fun he x)
  let J' := (ContinuousMap.Homotopy.refl inc).comp J
  obtain ⟨d,hd⟩ := SphereTopology.extends_of_homotopy (J'.trans (HT.compContinuousMap v)) hzT
  exact ⟨d,fun x => ContinuousMap.congr_fun hd x⟩
end UniversalFInfinity.Milnor

open scoped TensorProduct

end

end OAI
