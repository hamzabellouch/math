import OAI.GroupTheory.UniversalGroup.TorusSpheres

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
open scoped TensorProduct

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)

variable {E : Type u} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]

lemma exists_equivariant_skeleton_extension_cells (n : ℕ)
    (b : C(Skeleton (univ : Set X) n,E))
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)
    (hfill : ∀ i : ι n, ∃ d : C(Disk n,E), ∀ x, d (boundary n x) = b (skeletonBoundary n (σ n (1,i)) x)) :
    ∃ e : C(Skeleton (univ : Set X) (n+1),E),
      (∀ x, e (skeletonBase n x) = b x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
  choose d hd using hfill
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
variable {E : Type u} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]
variable (n : ℕ) (b : C(Skeleton (univ : Set X) n,E))
variable (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)

def skeletonObstructions (i : ι n) : C(Sphere n,E) :=
  b.comp (skeletonBoundary n (σ n (1,i)))

abbrev SkeletonAttachment :=
  Attachment.Space (Attachment.equivariantFamily (G := G) (skeletonObstructions σ n b))

def attachmentBase : C(E,SkeletonAttachment σ n b) :=
  ⟨Attachment.base _,Attachment.continuous_base _⟩

include hb in

theorem extend_by_cell_orbits :
    ∃ e : C(Skeleton (univ : Set X) (n+1),SkeletonAttachment σ n b),
      (∀ x, e (skeletonBase n x) = attachmentBase σ n b (b x)) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
  apply exists_equivariant_skeleton_extension_cells σ hσ n ((attachmentBase σ n b).comp b)
  · intro g x
    change Attachment.base _ (b (skeletonTranslate σ hσ n g x)) = _
    rw [hb]
    rfl
  · intro i
    refine ⟨Attachment.cell _ (1,i),?_⟩
    intro x
    have hc := Attachment.cell_boundary (Attachment.equivariantFamily (G := G) (skeletonObstructions σ n b)) (show Attachment.FreeIndex G (ι n) from (1,i)) x
    change _ = _ at hc
    exact hc.trans (by
      change Attachment.base _ ((1:G) • b (skeletonBoundary n (σ n (1,i)) x)) = _
      rw [one_smul]
      rfl)
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

lemma exists_equivariant_skeleton_lift_cells (n : ℕ) (p : C(E,B))
    (hp : ∀ (g : G) e, p (g • e) = g • p e)
    (F : C(Skeleton (univ : Set X) (n+1),B))
    (hF : ∀ (g : G) x, F (skeletonTranslate σ hσ (n+1) g x) = g • F x)
    (b : C(Skeleton (univ : Set X) n,E))
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)
    (hfill : ∀ i : ι n, ∃ d : C(Disk n,E),
      (∀ x,d (boundary n x) = b (skeletonBoundary n (σ n (1,i)) x)) ∧
      ∀ x,p (d x) = F (skeletonCell n (σ n (1,i)) x))
    (hbF : ∀ x, p (b x) = F (skeletonBase n x)) :
    ∃ e : C(Skeleton (univ : Set X) (n+1),E),
      (∀ x, e (skeletonBase n x) = b x) ∧ (∀ x, p (e x) = F x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
  choose d hd hf using hfill
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
universe u v w
variable {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]

lemma cylinder_filling_from_disk {n : ℕ} (q : C(Y,Z))
    (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
    (h : ∀ x, pathEndpoint (a x) = b (boundary n x))
    (F : C(Disk (n+1),Z)) (hF : ∀ x,F (boundary (n+1) x) = q (cylinderBoundaryMap a b h x)) :
    ∃ e : C(Disk n,C(unitInterval,Z)),
      (∀ x t, e (boundary n x) t = q (a x t)) ∧
      ∀ x, pathEndpoint (e x) = (q (b x).1,q (b x).2) := by
  let e : C(Disk n,C(unitInterval,Z)) :=
    (F.comp ⟨fun p : Disk n × unitInterval => diskCons p.1 p.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = q (a x t)
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change q (a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t))) = q (a x t)
    rw [diskTime_cons]
    congr 2
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = q (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change q (b (diskTail (diskCons x 0))).1 = q (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = q (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change q (b (diskTail (diskCons x 1))).2 = q (b x).2
      rw [diskTail_cons]

end UniversalFInfinity.Cellular

namespace UniversalFInfinity.Attachment
open Cellular
universe u v
variable {G : Type u} [Group G] {E : Type v} [TopologicalSpace E]
variable [MulAction G E] [ContinuousConstSMul G E] {ι : Type v} {n : ℕ}
variable (a : ι → C(Sphere n,E))
lemma representative_filling (i : ι) :
    ∃ F : C(Disk n,Space (equivariantFamily (G := G) a)),
      ∀ x,F (boundary n x) = base _ (a i x) := by
  refine ⟨cell _ (show FreeIndex G ι from (1,i)),?_⟩
  intro x
  exact (cell_boundary _ _ x).trans (congrArg (base _) (one_smul G (a i x)))
end UniversalFInfinity.Attachment

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
open scoped unitInterval
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (κ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hκ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (κ n (g*h,i)) x = g • RelCWComplex.map n (κ n (h,i)) x)
variable {E : Type u} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]
variable (n : ℕ) (a b : C(Skeleton (univ : Set X) (n+1),E))
variable (H : C(Skeleton (univ : Set X) n,C(I,E)))
variable (hH : ∀ x,pathEndpoint (H x) = (a (skeletonBase n x),b (skeletonBase n x)))

def homotopyObstructions (i : ι n) : C(Sphere (n+1),E) :=
  cylinderBoundaryMap (H.comp (skeletonBoundary n (κ n (1,i))))
    ((a.prodMk b).comp (skeletonCell n (κ n (1,i)))) (by
      intro x; exact hH (skeletonBoundary n (κ n (1,i)) x))

abbrev HomotopyAttachment :=
  Attachment.Space (Attachment.equivariantFamily (G := G) (homotopyObstructions κ n a b H hH))

def homotopyAttachmentBase : C(E,HomotopyAttachment κ n a b H hH) :=
  ⟨Attachment.base _,Attachment.continuous_base _⟩

theorem homotopy_extend_by_cell_orbits
    (ha : ∀ (g : G) x,a (skeletonTranslate κ hκ (n+1) g x) = g • a x)
    (hb : ∀ (g : G) x,b (skeletonTranslate κ hκ (n+1) g x) = g • b x)
    (hHe : ∀ (g : G) x,H (skeletonTranslate κ hκ n g x) = g • H x) :
    ∃ J : C(Skeleton (univ : Set X) (n+1),C(I,HomotopyAttachment κ n a b H hH)),
      (∀ x,J (skeletonBase n x) = (postPath (homotopyAttachmentBase κ n a b H hH)) (H x)) ∧
      (∀ x,pathEndpoint (J x) =
        (homotopyAttachmentBase κ n a b H hH (a x),homotopyAttachmentBase κ n a b H hH (b x))) ∧
      ∀ (g : G) x,J (skeletonTranslate κ hκ (n+1) g x) = g • J x := by
  let q := homotopyAttachmentBase κ n a b H hH
  let F := (q.comp a).prodMk (q.comp b)
  let L := (postPath q).comp H
  apply exists_equivariant_skeleton_lift_cells κ hκ n pathEndpoint (fun _ _ => rfl)
    F (fun g x => ?_) L (fun g x => ?_) (fun i => ?_) (fun x => ?_)
  · apply Prod.ext
    · change Attachment.base _ (a (skeletonTranslate κ hκ (n+1) g x)) = _
      rw [ha]; rfl
    · change Attachment.base _ (b (skeletonTranslate κ hκ (n+1) g x)) = _
      rw [hb]; rfl
  · apply ContinuousMap.ext; intro t
    change Attachment.base _ (H (skeletonTranslate κ hκ n g x) t) = _
    rw [hHe]; rfl
  · obtain ⟨D,hD⟩ := Attachment.representative_filling (G := G) (homotopyObstructions κ n a b H hH) i
    obtain ⟨e,he,hp⟩ := cylinder_filling_from_disk q
      (H.comp (skeletonBoundary n (κ n (1,i))))
      ((a.prodMk b).comp (skeletonCell n (κ n (1,i))))
      (fun x => hH (skeletonBoundary n (κ n (1,i)) x)) D hD
    refine ⟨e,fun x => ContinuousMap.ext (he x),hp⟩
  · exact Prod.ext (congrArg q (congrArg Prod.fst (hH x)))
      (congrArg q (congrArg Prod.snd (hH x)))
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

lemma exists_equivariant_skeleton_lift_cells_pred (n : ℕ) (p : C(E,B))
    (hp : ∀ (g : G) e, p (g • e) = g • p e)
    (P : E → Prop) (hP : ∀ (g : G) x,P x → P (g • x))
    (F : C(Skeleton (univ : Set X) (n+1),B))
    (hF : ∀ (g : G) x, F (skeletonTranslate σ hσ (n+1) g x) = g • F x)
    (b : C(Skeleton (univ : Set X) n,E))
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)
    (hbP : ∀ x,P (b x))
    (hfill : ∀ i : ι n, ∃ d : C(Disk n,E),
      (∀ x,d (boundary n x) = b (skeletonBoundary n (σ n (1,i)) x)) ∧
      (∀ x,p (d x) = F (skeletonCell n (σ n (1,i)) x)) ∧ ∀ x,P (d x))
    (hbF : ∀ x, p (b x) = F (skeletonBase n x)) :
    ∃ e : C(Skeleton (univ : Set X) (n+1),E),
      (∀ x, e (skeletonBase n x) = b x) ∧ (∀ x, p (e x) = F x) ∧
      (∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x) ∧ ∀ x,P (e x) := by
  choose d hd hf hdP using hfill
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
  refine ⟨e,he_base,?_,he,?_⟩
  · intro x
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
  · intro x
    obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
    cases y with
    | inl x =>
      change P (e (skeletonBase n x))
      rw [he_base]
      exact hbP x
    | inr q =>
      rw [skeletonAssembly_interior,he_cell]
      exact hP _ _ (hdP _ _)

end

open Set Metric Topology
universe u
variable {Y : Type u} [TopologicalSpace Y]
def pathZero : C(C(unitInterval,Y),Y) := ⟨fun p => p 0,continuous_eval_const 0⟩
def pathOne : C(C(unitInterval,Y),Y) := ⟨fun p => p 1,continuous_eval_const 1⟩

def pathEvaluation : (pathZero (Y := Y)).Homotopy pathOne where
  toFun z := z.2 z.1
  continuous_toFun := continuous_eval.comp (continuous_snd.prodMk continuous_fst)
  map_zero_left _ := rfl
  map_one_left _ := rfl

def pausePaths : C(C(unitInterval,Y),C(unitInterval,Y)) :=
  ContinuousMap.curry (((pathEvaluation (Y := Y)).trans (ContinuousMap.Homotopy.refl pathOne)).toContinuousMap.comp
    ⟨Prod.swap,continuous_swap⟩)

lemma pausePaths_zero (p : C(unitInterval,Y)) : pausePaths p 0 = p 0 :=
  ((pathEvaluation (Y := Y)).trans (ContinuousMap.Homotopy.refl pathOne)).apply_zero p
lemma pausePaths_one (p : C(unitInterval,Y)) : pausePaths p 1 = p 1 :=
  ((pathEvaluation (Y := Y)).trans (ContinuousMap.Homotopy.refl pathOne)).apply_one p

lemma pausePaths_smul {G : Type*} [Group G] [MulAction G Y] [ContinuousConstSMul G Y]
    (g : G) (p : C(unitInterval,Y)) : pausePaths (g • p) = g • pausePaths p := by
  apply ContinuousMap.ext; intro t
  change ((pathEvaluation (Y := Y)).trans (ContinuousMap.Homotopy.refl pathOne)) (t,g • p) =
    g • (((pathEvaluation (Y := Y)).trans (ContinuousMap.Homotopy.refl pathOne)) (t,p))
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl

variable [T2Space Y] [CWComplex (univ : Set Y)]
omit [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)] in
lemma dimH_disk_le (m : ℕ) : dimH (Set.univ : Set (Disk m)) ≤ m := by
  rw [← isometry_subtype_coe.dimH_image]
  have hm := dimH_mono (Set.subset_univ (closedBall (0 : Fin m → ℝ) 1))
  simpa only [Set.image_univ,Subtype.range_coe_subtype,Set.ofPred_mem_eq,Real.dimH_univ_pi_fin] using hm

lemma disk_homotopy_into_skeleton {n d : ℕ} (hnd : n < d)
    (f : C(Disk n,Y)) (H : C(Sphere n,C(unitInterval,Y)))
    (h0 : ∀ x,H x 0 = f (boundary n x))
    (h1 : ∀ x,H x 1 ∈ Skeleton (univ : Set Y) d) :
    ∃ e : C(Disk n,C(unitInterval,Y)),
      (∀ x,e (boundary n x) = pausePaths (H x)) ∧
      (∀ x,e x 0 = f x) ∧ ∀ x,e x 1 ∈ Skeleton (univ : Set Y) d := by
  let B : C(unitInterval × Sphere n,Y) :=
    H.uncurry.comp ⟨Prod.swap,continuous_swap⟩
  let E := Cylinder.extension f B h0
  let f₁ : C(Disk n,Y) := E.comp ⟨fun x => (1,x),continuous_const.prodMk continuous_id⟩
  have hs (x : Sphere n) : f₁ (boundary n x) = H x 1 :=
    Cylinder.extension_boundary f B h0 1 x
  obtain ⟨g,J,hJ⟩ := exists_cellular_approximation d f₁ (fun _ => Set.mem_univ _)
    ((dimH_disk_le n).trans_lt (by exact_mod_cast hnd))
  let K : f.Homotopy f₁ :=
    { toContinuousMap := E
      map_zero_left := Cylinder.extension_zero f B h0
      map_one_left := fun _ => rfl }
  let L := K.trans J
  let e := ContinuousMap.curry (L.toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩)
  refine ⟨e,?_,fun x => L.apply_zero x,fun x => ?_⟩
  · intro x
    apply ContinuousMap.ext; intro t
    change (K.trans J) (t,boundary n x) =
      ((pathEvaluation (Y := Y)).trans (ContinuousMap.Homotopy.refl pathOne)) (t,H x)
    simp only [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact Cylinder.extension_boundary f B h0 _ x
    · exact (hJ _ _ (hs x ▸ h1 x)).trans (hs x)
  · change L (1,x) ∈ _
    rw [ContinuousMap.Homotopy.apply_one]
    exact (g x).2
end UniversalFInfinity.Cellular

end

end OAI
