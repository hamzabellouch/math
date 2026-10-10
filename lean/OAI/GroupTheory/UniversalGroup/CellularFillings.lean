import OAI.GroupTheory.UniversalGroup.CellularChains

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
variable {G : Type u} [Group G] {X Y : Type u}
  [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  [MulAction G X] [ContinuousConstSMul G X]
  [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
  [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι κ : ℕ → Type u}
variable (a : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
  (ha : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
    RelCWComplex.map n (a n (g*h,i)) x = g • RelCWComplex.map n (a n (h,i)) x)
variable (b : ∀ n, (G × κ n) ≃ RelCWComplex.cell (univ : Set Y) n)
  (hb : ∀ n (g h : G) (i : κ n) (x : Fin n → ℝ),
    RelCWComplex.map n (b n (g*h,i)) x = g • RelCWComplex.map n (b n (h,i)) x)

include hb in

theorem exists_equivariant_cellular_homotopy (d n : ℕ) (hnd : n ≤ d)
    (f : C(Skeleton (univ : Set X) n,Y))
    (hf : ∀ (g : G) x, f (skeletonTranslate a ha n g x) = g • f x) :
    ∃ e : C(Skeleton (univ : Set X) n,C(unitInterval,Y)),
      (∀ (g : G) x, e (skeletonTranslate a ha n g x) = g • e x) ∧
      (∀ x,e x 0 = f x) ∧ ∀ x,e x 1 ∈ Skeleton (univ : Set Y) d := by
  induction n with
  | zero =>
    have : IsEmpty (Skeleton (univ : Set X) 0) := by
      refine ⟨fun x => ?_⟩
      have hx := x.2
      change x.1 ∈ (CWComplex.skeletonLT (univ : Set X) 0 : Set X) at hx
      rw [CWComplex.skeletonLT_zero_eq_empty] at hx
      exact hx
    exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun _ x => isEmptyElim x,
      fun x => isEmptyElim x,fun x => isEmptyElim x⟩
  | succ n ih =>
    obtain ⟨H,hH,hH0,hH1⟩ := ih (Nat.le_of_succ_le hnd) (f.comp (skeletonBase n)) (fun g x => by
      change f (skeletonBase n (skeletonTranslate a ha n g x)) = g • f (skeletonBase n x)
      rw [←skeletonTranslate_base,hf])
    let H' := pausePaths.comp H
    have hH' (g : G) x : H' (skeletonTranslate a ha n g x) = g • H' x := by
      change pausePaths (H (skeletonTranslate a ha n g x)) = g • pausePaths (H x)
      rw [hH,pausePaths_smul]
    have hH'0 (x) : pathZero (H' x) = f (skeletonBase n x) := by
      exact (pausePaths_zero (H x)).trans (hH0 x)
    have hH'1 (x) : pathOne (H' x) ∈ Skeleton (univ : Set Y) d := by
      change pausePaths (H x) 1 ∈ _
      rw [pausePaths_one]
      exact hH1 x
    have hfill (i : ι n) : ∃ D : C(Disk n,C(unitInterval,Y)),
        (∀ x,D (boundary n x) = H' (skeletonBoundary n (a n (1,i)) x)) ∧
        (∀ x,pathZero (D x) = f (skeletonCell n (a n (1,i)) x)) ∧
        ∀ x,pathOne (D x) ∈ Skeleton (univ : Set Y) d := by
      apply disk_homotopy_into_skeleton (Nat.lt_of_succ_le hnd)
        (f.comp (skeletonCell n (a n (1,i)))) (H.comp (skeletonBoundary n (a n (1,i))))
      · intro x
        exact hH0 (skeletonBoundary n (a n (1,i)) x)
      · intro x
        exact hH1 _
    obtain ⟨e,_,he0,he,he1⟩ := exists_equivariant_skeleton_lift_cells_pred a ha n
      pathZero (fun _ _ => rfl) (fun p => pathOne p ∈ Skeleton (univ : Set Y) d)
      (fun g p hp => skeleton_smul_mem b hb d g hp) f hf H' hH' hH'1 hfill hH'0
    exact ⟨e,he,he0,he1⟩
end

section
open Set Metric Topology
universe u

def LowFillable (X : Type*) [TopologicalSpace X] (d : ℕ) : Prop :=
  ∀ n ≤ d, ∀ a : C(Sphere n,X), ∃ e : C(Disk n,X), ∀ x,e (boundary n x) = a x

lemma pathEndpoint_lift_at {Y : Type*} [TopologicalSpace Y] (n : ℕ)
    (hfill : ∀ a : C(Sphere (n+1),Y), ∃ e : C(Disk (n+1),Y), ∀ x,e (boundary (n+1) x) = a x)
    (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
    (h : ∀ x,pathEndpoint (a x) = b (boundary n x)) :
    ∃ e : C(Disk n,C(unitInterval,Y)),
      (∀ x,e (boundary n x) = a x) ∧ ∀ x,pathEndpoint (e x) = b x := by
  obtain ⟨F,hF⟩ := hfill (cylinderBoundaryMap a b h)
  obtain ⟨e,he,hp⟩ := cylinder_filling_from_disk (.id Y) a b h F hF
  exact ⟨e,fun x => ContinuousMap.ext (he x),hp⟩

variable {G : Type u} [Group G] {X Y : Type u}
  [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  [MulAction G X] [ContinuousConstSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι : ℕ → Type u}
variable (κ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
  (hκ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
    RelCWComplex.map n (κ n (g*h,i)) x = g • RelCWComplex.map n (κ n (h,i)) x)

lemma equivariant_low_homotopy (d : ℕ) (hfill : LowFillable Y d)
    (a b : C(Skeleton (univ : Set X) d,Y))
    (ha : ∀ (g : G) x,a (skeletonTranslate κ hκ d g x) = g • a x)
    (hb : ∀ (g : G) x,b (skeletonTranslate κ hκ d g x) = g • b x) :
    ∃ H : C(Skeleton (univ : Set X) d,C(unitInterval,Y)),
      (∀ x,pathEndpoint (H x) = (a x,b x)) ∧
      ∀ (g : G) x,H (skeletonTranslate κ hκ d g x) = g • H x := by
  induction d with
  | zero =>
    let := isEmpty_skeleton_zero (X := X)
    exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun x => isEmptyElim x,fun _ x => isEmptyElim x⟩
  | succ d ih =>
    obtain ⟨H,hH,hHe⟩ := ih (fun n hn => hfill n (hn.trans (Nat.le_succ d)))
      (a.comp (skeletonBase d)) (b.comp (skeletonBase d))
      (fun g x => by change a (skeletonBase d (skeletonTranslate κ hκ d g x)) = g • a (skeletonBase d x); rw [←skeletonTranslate_base,ha])
      (fun g x => by change b (skeletonBase d (skeletonTranslate κ hκ d g x)) = g • b (skeletonBase d x); rw [←skeletonTranslate_base,hb])
    obtain ⟨e,_,he,hee⟩ := exists_equivariant_skeleton_lift_cells κ hκ d pathEndpoint
      (fun _ _ => rfl) (a.prodMk b) (fun g x => Prod.ext (ha g x) (hb g x)) H hHe
      (fun i => pathEndpoint_lift_at d (hfill (d+1) le_rfl)
        (H.comp (skeletonBoundary d (κ d (1,i))))
        ((a.prodMk b).comp (skeletonCell d (κ d (1,i))))
        (fun x => hH (skeletonBoundary d (κ d (1,i)) x))) hH
    exact ⟨e,he,hee⟩
end

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X Y : Type u}
  [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  [MulAction G X] [ContinuousConstSMul G X]
  [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
  [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι κ : ℕ → Type u}
variable (α : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
  (hα : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
    RelCWComplex.map n (α n (g*h,i)) x = g • RelCWComplex.map n (α n (h,i)) x)
variable (β : ∀ n, (G × κ n) ≃ RelCWComplex.cell (univ : Set Y) n)
  (hβ : ∀ n (g h : G) (i : κ n) (x : Fin n → ℝ),
    RelCWComplex.map n (β n (g*h,i)) x = g • RelCWComplex.map n (β n (h,i)) x)
variable (n : ℕ) (q : C(Skeleton (univ : Set X) (n+1),Skeleton (univ : Set Y) (n+1)))
  (r : C(Skeleton (univ : Set Y) (n+1),X))
variable (H : C(Skeleton (univ : Set X) n,C(unitInterval,X)))
  (hH : ∀ x,pathEndpoint (H x) = ((skeletonBase n x).1,r (q (skeletonBase n x))))

def brownObstructions : κ (n+1) ⊕ ι n → C(Sphere (n+1),X) :=
  Sum.elim (skeletonObstructions β (n+1) r)
    (homotopyObstructions α n (skeletonInclusion (n+1)) (r.comp q) H hH)

abbrev BrownAttachment := Attachment.Space (Attachment.equivariantFamily (G := G)
  (brownObstructions α β n q r H hH))

def brownBase : C(X,BrownAttachment α β n q r H hH) :=
  ⟨Attachment.base _,Attachment.continuous_base _⟩

include hβ in
lemma brown_map_extension
    (hr : ∀ (g : G) x,r (skeletonTranslate β hβ (n+1) g x) = g • r x) :
    ∃ e : C(Skeleton (univ : Set Y) (n+2),BrownAttachment α β n q r H hH),
      (∀ x,e (skeletonBase (n+1) x) = brownBase α β n q r H hH (r x)) ∧
      ∀ (g : G) x,e (skeletonTranslate β hβ (n+2) g x) = g • e x := by
  apply exists_equivariant_skeleton_extension_cells β hβ (n+1)
    ((brownBase α β n q r H hH).comp r)
  · intro g x
    change Attachment.base _ (r (skeletonTranslate β hβ (n+1) g x)) = _
    rw [hr]; rfl
  · intro i
    obtain ⟨D,hD⟩ := Attachment.representative_filling (G := G)
      (brownObstructions α β n q r H hH) (Sum.inl i)
    exact ⟨D,hD⟩

include hα hβ in
lemma brown_homotopy_extension
    (hq : ∀ (g : G) x,q (skeletonTranslate α hα (n+1) g x) = skeletonTranslate β hβ (n+1) g (q x))
    (hr : ∀ (g : G) x,r (skeletonTranslate β hβ (n+1) g x) = g • r x)
    (hHe : ∀ (g : G) x,H (skeletonTranslate α hα n g x) = g • H x) :
    ∃ J : C(Skeleton (univ : Set X) (n+1),C(unitInterval,BrownAttachment α β n q r H hH)),
      (∀ x,pathEndpoint (J x) =
        (brownBase α β n q r H hH x.1,brownBase α β n q r H hH (r (q x)))) ∧
      ∀ (g : G) x,J (skeletonTranslate α hα (n+1) g x) = g • J x := by
  let b := brownBase α β n q r H hH
  let F := (b.comp (skeletonInclusion (n+1))).prodMk (b.comp (r.comp q))
  let L := (postPath b).comp H
  have hb (g : G) (x : X) : b (g • x) = g • b x := rfl
  have hF (g : G) x : F (skeletonTranslate α hα (n+1) g x) = g • F x := by
    apply Prod.ext
    · exact hb g x.1
    · change b (r (q (skeletonTranslate α hα (n+1) g x))) = g • b (r (q x))
      rw [hq,hr,hb]
  have hL (g : G) x : L (skeletonTranslate α hα n g x) = g • L x := by
    apply ContinuousMap.ext; intro t
    change b (H (skeletonTranslate α hα n g x) t) = g • b (H x t)
    rw [hHe]; rfl
  have hc (i : ι n) : ∃ e : C(Disk n,C(unitInterval,BrownAttachment α β n q r H hH)),
      (∀ x,e (boundary n x) = L (skeletonBoundary n (α n (1,i)) x)) ∧
      ∀ x,pathEndpoint (e x) = F (skeletonCell n (α n (1,i)) x) := by
    obtain ⟨D,hD⟩ := Attachment.representative_filling (G := G)
      (brownObstructions α β n q r H hH) (Sum.inr i)
    obtain ⟨e,he,hp⟩ := cylinder_filling_from_disk b
      (H.comp (skeletonBoundary n (α n (1,i))))
      (((skeletonInclusion (n+1)).prodMk (r.comp q)).comp (skeletonCell n (α n (1,i))))
      (fun x => hH (skeletonBoundary n (α n (1,i)) x)) D hD
    exact ⟨e,fun x => ContinuousMap.ext (he x),hp⟩
  have hL0 (x) : pathEndpoint (L x) = F (skeletonBase n x) :=
    Prod.ext (congrArg b (congrArg Prod.fst (hH x)))
      (congrArg b (congrArg Prod.snd (hH x)))
  obtain ⟨J,_,hJ,hJe⟩ := exists_equivariant_skeleton_lift_cells α hα n pathEndpoint
    (fun _ _ => rfl) F hF L hL hc hL0
  exact ⟨J,hJ,hJe⟩
end

open Set Metric Topology
universe u v w
variable {X : Type u} {Y : Type v} {W : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
  [TopologicalSpace W]

lemma fill_through_next_skeleton (d : ℕ) (q : C(X,Skeleton (univ : Set Y) d))
    (e : C(Skeleton (univ : Set Y) (d+1),W))
    (hq : ((skeletonInclusion d).comp q).Nullhomotopic)
    {m : ℕ} (hm : m ≤ d) [Nonempty (Sphere m)] (a : C(Sphere m,X)) :
    SphereTopology.Extends ((e.comp ((skeletonBase d).comp q)).comp a) := by
  obtain ⟨z,⟨H⟩⟩ := hq
  obtain ⟨F,hF⟩ := SphereTopology.extends_of_nullhomotopic (H.compContinuousMap a).symm
  obtain ⟨b,J,hstat⟩ := exists_cellular_approximation (d+1) F (fun _ => mem_univ _)
    ((Attachment.dimH_disk_subtype_le m).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hm))
  refine ⟨e.comp b,?_⟩
  ext x
  apply congrArg e
  apply Subtype.ext
  have hFx : F (boundary m x) = (q (a x)).1 := ContinuousMap.congr_fun hF x
  have hx : F (boundary m x) ∈ Skeleton (univ : Set Y) (d+1) := by
    rw [hFx]
    exact (skeletonBase d (q (a x))).2
  have h := hstat 1 (boundary m x) hx
  exact (J.apply_one (boundary m x)).symm.trans h |>.trans hFx

lemma filling_after_skeletal_domination (d : ℕ)
    (q : C(X,Skeleton (univ : Set Y) d)) (e : C(Skeleton (univ : Set Y) (d+1),W))
    (hq : ((skeletonInclusion d).comp q).Nullhomotopic)
    (b : C(X,W)) (H : b.Homotopy (e.comp ((skeletonBase d).comp q)))
    {m : ℕ} (hm : m ≤ d) [Nonempty (Sphere m)] (a : C(Sphere m,X)) :
    SphereTopology.Extends (b.comp a) :=
  SphereTopology.extends_of_homotopy (H.compContinuousMap a)
    (fill_through_next_skeleton d q e hq hm a)
end UniversalFInfinity.Cellular

namespace UniversalFInfinity.Attachment
open Set Metric Topology Cellular
variable {G : Type*} [Group G] {X : Type*} [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X] [Nonempty X]
variable {ι : Type*} {d : ℕ} (a : ι → C(Sphere d,X))
variable [T2Space (Space (equivariantFamily (G := G) a))]

lemma lowFillable_of_kills_old
    (hkill : ∀ m ≤ d, ∀ s : C(Sphere m,X),
      SphereTopology.Extends ((⟨base (equivariantFamily (G := G) a),continuous_base _⟩ :
        C(X,Space (equivariantFamily (G := G) a))).comp s)) :
    LowFillable (Space (equivariantFamily (G := G) a)) d := by
  intro m hm s
  cases m with
  | zero =>
    let : Nonempty (Space (equivariantFamily (G := G) a)) := ⟨base _ (Classical.choice ‹Nonempty X›)⟩
    exact SphereTopology.fill_zero s
  | succ m =>
    let := SphereTopology.sphere_nonempty m
    have hdim : dimH (Set.univ : Set (Sphere (m+1))) < d :=
      (GeneralPosition.dimH_cube_boundary_subtype_le m).trans_lt (by exact_mod_cast Nat.lt_of_succ_le hm)
    obtain ⟨s',H,_⟩ := exists_deformation_into_base (equivariantFamily (G := G) a) s hdim
    obtain ⟨F,hF⟩ := SphereTopology.extends_of_homotopy H (hkill (m+1) hm s')
    exact ⟨F,fun x => ContinuousMap.congr_fun hF x⟩
end UniversalFInfinity.Attachment

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G] {X Y : Type u}
  [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  [MulAction G X] [ContinuousConstSMul G X]
  [TopologicalSpace Y] [T2Space Y] [CWComplex (univ : Set Y)]
  [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι κ : ℕ → Type u}
variable (α : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
  (hα : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
    RelCWComplex.map n (α n (g*h,i)) x = g • RelCWComplex.map n (α n (h,i)) x)
variable (β : ∀ n, (G × κ n) ≃ RelCWComplex.cell (univ : Set Y) n)
  (hβ : ∀ n (g h : G) (i : κ n) (x : Fin n → ℝ),
    RelCWComplex.map n (β n (g*h,i)) x = g • RelCWComplex.map n (β n (h,i)) x)
variable (n : ℕ) (q : C(Skeleton (univ : Set X) (n+1),Skeleton (univ : Set Y) (n+1)))
  (r : C(Skeleton (univ : Set Y) (n+1),X))
variable (H : C(Skeleton (univ : Set X) n,C(unitInterval,X)))
  (hH : ∀ x,pathEndpoint (H x) = ((skeletonBase n x).1,r (q (skeletonBase n x))))

include hα hβ in
lemma brown_lowFillable [Nonempty X] [T2Space (BrownAttachment α β n q r H hH)]
    (hdim : Skeleton (univ : Set X) (n+1) = univ)
    (hqnull : ((skeletonInclusion (n+1)).comp q).Nullhomotopic)
    (hq : ∀ (g : G) x,q (skeletonTranslate α hα (n+1) g x) = skeletonTranslate β hβ (n+1) g (q x))
    (hr : ∀ (g : G) x,r (skeletonTranslate β hβ (n+1) g x) = g • r x)
    (hHe : ∀ (g : G) x,H (skeletonTranslate α hα n g x) = g • H x) :
    LowFillable (BrownAttachment α β n q r H hH) (n+1) := by
  obtain ⟨e,he,_⟩ := brown_map_extension α β hβ n q r H hH hr
  obtain ⟨J,hJ,_⟩ := brown_homotopy_extension α hα β hβ n q r H hH hq hr hHe
  let back : C(X,Skeleton (univ : Set X) (n+1)) :=
    ⟨fun x => ⟨x,by rw [hdim]; trivial⟩,continuous_id.subtype_mk (fun x => by rw [hdim]; trivial)⟩
  let q' := q.comp back
  let b := brownBase α β n q r H hH
  have hnull : ((skeletonInclusion (n+1)).comp q').Nullhomotopic := by
    obtain ⟨z,⟨K⟩⟩ := hqnull
    exact ⟨z,⟨K.compContinuousMap back⟩⟩
  let K : b.Homotopy (e.comp ((skeletonBase (n+1)).comp q')) :=
    { toFun := fun z => J (back z.2) z.1
      continuous_toFun := (J.continuous.comp (back.continuous.comp continuous_snd)).eval continuous_fst
      map_zero_left := fun x => congrArg Prod.fst (hJ (back x))
      map_one_left := fun x => (congrArg Prod.snd (hJ (back x))).trans (he (q (back x))).symm }
  apply Attachment.lowFillable_of_kills_old (G := G) (brownObstructions α β n q r H hH)
  intro m hm a
  cases m with
  | zero =>
    let : Nonempty (BrownAttachment α β n q r H hH) := ⟨b (Classical.choice ‹Nonempty X›)⟩
    obtain ⟨F,hF⟩ := SphereTopology.fill_zero (b.comp a)
    exact ⟨F,ContinuousMap.ext hF⟩
  | succ m =>
    let := SphereTopology.sphere_nonempty m
    exact filling_after_skeletal_domination (n+1) q' e hnull b K hm a
end

section
open Set Metric Topology
universe u
variable {G : Type u} [Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq _
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  [MulAction G X] [ContinuousConstSMul G X]
variable {ι : ℕ → Type u} [∀ m,Finite (ι m)]
variable (α : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
  (hα : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
    RelCWComplex.map n (α n (g*h,i)) x = g • RelCWComplex.map n (α n (h,i)) x)

lemma controlled_map_on_skeleton (d : ℕ) (e : C(Skeleton (univ : Set X) d,Milnor.Space G))
    (he : ∀ (g : G) x,e (skeletonTranslate α hα d g x) = g • e x) :
    ∃ S : Milnor.Shapes G, Set.range e ⊆ Set.range (Milnor.stageFull G S) := by
  obtain ⟨K,hK,hcov⟩ := skeleton_compact_representatives α hα d
  obtain ⟨S,hS⟩ := Milnor.compact_orbit_controlled G (hK.image e.continuous)
  refine ⟨S,?_⟩
  rintro _ ⟨x,rfl⟩
  obtain ⟨g,y,hy,rfl⟩ := hcov x
  rw [he]
  exact hS g ⟨e y,⟨y,hy,rfl⟩,rfl⟩

lemma exists_brown_data
    (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)
    (n : ℕ) (hfill : LowFillable X n) :
    ∃ T : Milnor.Shapes G,
    letI cw := Milnor.stageEquivariantCW G T
    let β : ∀ m, (G × Milnor.CellOrbits G T m) ≃ cw.cell m := fun _ => Equiv.refl _
    let hβ : ∀ m (g h : G) (i : Milnor.CellOrbits G T m) (x : Fin m → ℝ),
      cw.map m (β m (g*h,i)) x = g • cw.map m (β m (h,i)) x := fun _ g h _ _ => mul_smul g h _
    ∃ (q : C(Skeleton (univ : Set X) (n+1),Skeleton (univ : Set (Milnor.Stage G T)) (n+1)))
      (r : C(Skeleton (univ : Set (Milnor.Stage G T)) (n+1),X))
      (H : C(Skeleton (univ : Set X) n,C(unitInterval,X))),
      ((skeletonInclusion (n+1)).comp q).Nullhomotopic ∧
      (∀ (g : G) x,q (skeletonTranslate α hα (n+1) g x) = skeletonTranslate β hβ (n+1) g (q x)) ∧
      (∀ (g : G) x,r (skeletonTranslate β hβ (n+1) g x) = g • r x) ∧
      (∀ x,pathEndpoint (H x) = ((skeletonBase n x).1,r (q (skeletonBase n x)))) ∧
      ∀ (g : G) x,H (skeletonTranslate α hα n g x) = g • H x := by
  obtain ⟨e,he⟩ := exists_equivariant_map_on_skeleton α hα (n+1)
    (fun m _ => Milnor.sphereFillable (1:G) m)
  obtain ⟨S,hS⟩ := controlled_map_on_skeleton α hα (n+1) e he
  let eS := Milnor.factorStage G e S hS
  have heS (g : G) x : eS (skeletonTranslate α hα (n+1) g x) = g • eS x := by
    apply (Milnor.stageFull_embedding G S).injective
    rw [Milnor.factorStage_spec,Milnor.stageFull_smul,Milnor.factorStage_spec,he]
  obtain ⟨T,hST,z,⟨K⟩⟩ := hunif S
  let : CWComplex (univ : Set (Milnor.Stage G T)) := Milnor.stageEquivariantCW G T
  let β : ∀ m, (G × Milnor.CellOrbits G T m) ≃ RelCWComplex.cell (univ : Set (Milnor.Stage G T)) m :=
    fun _ => Equiv.refl _
  have hβ : ∀ m (g h : G) (i : Milnor.CellOrbits G T m) (x : Fin m → ℝ),
      RelCWComplex.map m (β m (g*h,i)) x = g • RelCWComplex.map m (β m (h,i)) x :=
    fun _ g h _ _ => mul_smul g h _
  let f := (Milnor.stageIncl G S T hST).comp eS
  have hf (g : G) x : f (skeletonTranslate α hα (n+1) g x) = g • f x := by
    change Milnor.stageIncl G S T hST (eS _) = _
    rw [heS,Milnor.stageIncl_smul]
    rfl
  obtain ⟨J,hJe,hJ0,hJ1⟩ := exists_equivariant_cellular_homotopy α hα β hβ (n+1) (n+1) le_rfl f hf
  let q : C(Skeleton (univ : Set X) (n+1),Skeleton (univ : Set (Milnor.Stage G T)) (n+1)) :=
    ⟨fun x => ⟨J x 1,hJ1 x⟩,(J.continuous.eval_const _).subtype_mk _⟩
  have hq (g : G) x : q (skeletonTranslate α hα (n+1) g x) = skeletonTranslate β hβ (n+1) g (q x) := by
    apply Subtype.ext
    exact ContinuousMap.congr_fun (hJe g x) 1
  let J' : f.Homotopy ((skeletonInclusion (n+1)).comp q) :=
    { toFun := fun z => J z.2 z.1
      continuous_toFun := (J.continuous.comp continuous_snd).eval continuous_fst
      map_zero_left := hJ0
      map_one_left := fun _ => rfl }
  have hqnull : ((skeletonInclusion (n+1)).comp q).Nullhomotopic :=
    ⟨z,⟨J'.symm.trans (K.compContinuousMap eS)⟩⟩
  obtain ⟨r,hr⟩ := exists_equivariant_map_on_skeleton β hβ (n+1)
    (fun m hm => hfill m (Nat.le_of_lt_succ hm))
  let a := skeletonInclusion (C := (univ : Set X)) n
  let b := r.comp (q.comp (skeletonBase n))
  have ha (g : G) x : a (skeletonTranslate α hα n g x) = g • a x := rfl
  have hb (g : G) x : b (skeletonTranslate α hα n g x) = g • b x := by
    change r (q (skeletonBase n (skeletonTranslate α hα n g x))) = _
    rw [←skeletonTranslate_base,hq,hr]
    rfl
  obtain ⟨H,hH,hHe⟩ := equivariant_low_homotopy α hα n hfill a b ha hb
  exact ⟨T,q,r,H,hqnull,hq,hr,hH,hHe⟩
end

open Set Metric Topology
universe u
variable {G : Type u} [Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq _
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
  [MulAction G X] [ContinuousConstSMul G X] [Nonempty X]
variable {ι : ℕ → Type u} [∀ m,Finite (ι m)]
variable (α : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
  (hα : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
    RelCWComplex.map n (α n (g*h,i)) x = g • RelCWComplex.map n (α n (h,i)) x)

omit [MulAction G X] [ContinuousConstSMul G X] [Nonempty X] in
lemma skeleton_eq_univ_of_dimension (n : ℕ)
    (hdim : ∀ m (_ : RelCWComplex.cell (univ : Set X) m),m ≤ n) :
    Skeleton (univ : Set X) (n+1) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ (univ : Set X) := trivial
  rw [←CWComplex.union (C := (univ : Set X))] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨m,i,y,hy,rfl⟩ := hx
  exact characteristic_mem_skeleton (Nat.lt_succ_of_le (hdim m i)) i ⟨y,hy⟩

include hα in
lemma exists_finite_brown_attachment
    (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)
    (n : ℕ) (hfill : LowFillable X n)
    (hdim : ∀ m (_ : RelCWComplex.cell (univ : Set X) m),m ≤ n)
    (hsep : Attachment.RealSeparated X) :
    ∃ (I : Type u) (_ : Finite I) (a : I → C(Sphere (n+1),X)),
      LowFillable (Attachment.Space (Attachment.equivariantFamily (G := G) a)) (n+1) := by
  obtain ⟨T,q,r,H,hqnull,hq,hr,hH,hHe⟩ := exists_brown_data α hα hunif n hfill
  let cw := Milnor.stageEquivariantCW G T
  let β : ∀ m,(G × Milnor.CellOrbits G T m) ≃ cw.cell m := fun _ => Equiv.refl _
  have hβ : ∀ m (g h : G) (i : Milnor.CellOrbits G T m) (x : Fin m → ℝ),
      cw.map m (β m (g*h,i)) x = g • cw.map m (β m (h,i)) x := fun _ g h _ _ => mul_smul g h _
  let a := brownObstructions α β n q r H hH
  let := Attachment.t2Space (Attachment.equivariantFamily (G := G) a) hsep
  exact ⟨_,inferInstance,a,brown_lowFillable α hα β hβ n q r H hH
    (skeleton_eq_univ_of_dimension n hdim) hqnull hq hr hHe⟩
end UniversalFInfinity.Cellular

namespace UniversalFInfinity.Attachment
open Set Metric Topology Cellular
universe u
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X] [Nonempty X]
  [CWComplex (univ : Set X)] [MulAction G X] [ContinuousConstSMul G X]
variable {ι : ℕ → Type u} (α : ∀ m,(G × ι m) ≃ OldCell (X := X) m)
  (hα : ∀ m (g h : G) (i : ι m) (x : Fin m → ℝ),
    RelCWComplex.map m (α m (g*h,i)) x = g • RelCWComplex.map m (α m (h,i)) x)
variable {I : Type u} {n : ℕ} (a : I → C(Sphere n,X))

abbrev LayerOrbits (m : ℕ) := ι m ⊕ CellIndex.{u,u} m n I

def layerEquiv (m : ℕ) : (G × LayerOrbits (ι := ι) (I := I) (n := n) m) ≃
    LayerCell (X := X) (ι := FreeIndex G I) (n := n) m where
  toFun p := match p.2 with
    | Sum.inl i => Sum.inl (α m (p.1,i))
    | Sum.inr i => Sum.inr ⟨⟨i.down.1,(p.1,i.down.2)⟩⟩
  invFun p := match p with
    | Sum.inl i => (((α m).symm i).1,Sum.inl (((α m).symm i).2))
    | Sum.inr i => (i.down.2.1,Sum.inr ⟨⟨i.down.1,i.down.2.2⟩⟩)
  left_inv := by rintro ⟨g,i⟩; cases i <;> simp
  right_inv := by
    intro cell
    cases cell with
    | inl cell => simp
    | inr cell =>
      obtain ⟨⟨dimension,group,index⟩⟩ := cell
      rfl

omit [T2Space X] in
include hα in
lemma layerEquiv_map_disk (m : ℕ) (g h : G) (i : LayerOrbits (ι := ι) (I := I) (n := n) m)
    (x : Fin m → ℝ) (hx : x ∈ closedBall 0 1) :
    layerMap (equivariantFamily (G := G) a) m (layerEquiv α m (g*h,i)) x =
      g • layerMap (equivariantFamily (G := G) a) m (layerEquiv α m (h,i)) x := by
  cases i with
  | inl i =>
    change base _ (RelCWComplex.map m (α m (g*h,i)) x) = g • base _ (RelCWComplex.map m (α m (h,i)) x)
    rw [hα]; rfl
  | inr i =>
    obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
    subst m
    change characteristic (equivariantFamily (G := G) a) (g*h,i) x =
      g • characteristic (equivariantFamily (G := G) a) (h,i) x
    exact (characteristic_disk _ (g*h,i) ⟨x,hx⟩).trans
      ((smul_cell _ (equivariantFamily_smul a) g (h,i) ⟨x,hx⟩).symm.trans
        (congrArg (g • ·) (characteristic_disk _ (h,i) ⟨x,hx⟩).symm))

variable (hdim : ∀ m (_ : OldCell (X := X) m),m < n)

omit [T2Space X] in
include hα in
lemma layerEquiv_image (m : ℕ) (g : G) (i : LayerOrbits (ι := ι) (I := I) (n := n) m)
    (A : Set (Fin m → ℝ)) (hA : A ⊆ closedBall 0 1) :
    (fun z => g • z) '' (layerMap (equivariantFamily (G := G) a) m (layerEquiv α m (1,i)) '' A) =
      layerMap (equivariantFamily (G := G) a) m (layerEquiv α m (g,i)) '' A := by
  rw [←Set.image_comp]
  apply Set.image_congr
  intro x hx
  have h := layerEquiv_map_disk α hα a m g 1 i x (hA hx)
  simpa only [mul_one,Function.comp_apply] using h.symm

variable [T2Space (Space (equivariantFamily (G := G) a))]

@[instance_reducible]
def equivariantLayerCW : CWComplex (univ : Set (Space (equivariantFamily (G := G) a))) := by
  let := layerCW (equivariantFamily (G := G) a) hdim
  exact actionCW (layerEquiv α)
    (fun m g i => layerEquiv_image α hα a m g i _ ball_subset_closedBall)
    (fun m g i => layerEquiv_image α hα a m g i _ subset_rfl)

lemma equivariantLayerCW_dims (m : ℕ) (i : (equivariantLayerCW α hα a hdim).cell m) : m < n+1 :=
  layerCW_dimensions (equivariantFamily (G := G) a) hdim m (layerEquiv α m i)

lemma equivariantLayerCW_smul (m : ℕ) (g h : G)
    (i : LayerOrbits (ι := ι) (I := I) (n := n) m) (x : Fin m → ℝ) :
    (equivariantLayerCW α hα a hdim).map m (g*h,i) x =
      g • (equivariantLayerCW α hα a hdim).map m (h,i) x := by
  change (g*h) • layerMap (equivariantFamily (G := G) a) m (layerEquiv α m (1,i)) x =
    g • (h • layerMap (equivariantFamily (G := G) a) m (layerEquiv α m (1,i)) x)
  exact mul_smul _ _ _

def layerOld (m : ℕ) (i : OldCell (X := X) m) :
    (equivariantLayerCW α hα a hdim).cell m :=
  (((α m).symm i).1,Sum.inl ((α m).symm i).2)

lemma layerOld_injective (m : ℕ) : Function.Injective (layerOld α hα a hdim m) := by
  intro i j h
  apply (α m).symm.injective
  have h1 := congrArg Prod.fst h
  have h2 := Sum.inl_injective (congrArg Prod.snd h)
  exact Prod.ext h1 h2

lemma layerOld_map (m : ℕ) (i : OldCell (X := X) m) (x : Fin m → ℝ) :
    (equivariantLayerCW α hα a hdim).map m (layerOld α hα a hdim m i) x =
      base (equivariantFamily (G := G) a) (RelCWComplex.map m i x) := by
  change ((α m).symm i).1 • base (equivariantFamily (G := G) a) (RelCWComplex.map m (α m (1,((α m).symm i).2)) x) = _
  change base (equivariantFamily (G := G) a) (((α m).symm i).1 • RelCWComplex.map m (α m (1,((α m).symm i).2)) x) = _
  rw [←hα,mul_one,Equiv.apply_symm_apply]

lemma layerOld_exhaustive (m : ℕ) (hm : m ≠ n)
    (i : (equivariantLayerCW α hα a hdim).cell m) :
    ∃ j,layerOld α hα a hdim m j = i := by
  obtain ⟨g,i⟩ := i
  cases i with
  | inl i => exact ⟨α m (g,i),by simp only [layerOld,Equiv.symm_apply_apply]⟩
  | inr i => exact (hm i.down.1.down).elim
end UniversalFInfinity.Attachment

end

end OAI
