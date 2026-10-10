import Mathlib
import OAI.CategoryTheory.Thomason.FiniteChains
import OAI.CategoryTheory.Thomason.GlobularGeneration

namespace OAI

/-! Interval Extension. -/

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open CategoryTheory DirectedComplex DirectedComplex.Table

lemma bounded_table_classification {i k : ℕ} (t : Table (complex.{u} i))
    (ht : truncate k false t = t) :
    ∃ p b, p ≤ i ∧ p ≤ k ∧ t = truncate p b (topTable i) := by
  obtain ⟨p,b,hpi,he⟩ := table_classification t
  refine ⟨p,b,hpi,?_,he⟩
  by_contra hn
  have hkp : k < p := by omega
  rw [he, truncate_truncate, ite_eq_left hkp] at ht
  have hp := top_face_dimension (hkp.le.trans hpi) hpi false b ht
  omega

def sourceCollapse (i k : ℕ) : Hom (complex.{u} i) (complex.{u} i) :=
  tableMap i (truncate k false (topTable i))

lemma sourceCollapse_top (i k : ℕ) :
    (sourceCollapse.{u} i k).nu.map (topTable i) = truncate k false (topTable i) := by
  rw [sourceCollapse, tableMap_nu_top]
  change (complex i).nu.source i ((complex i).nu.source k (topTable i)) = _
  erw [(complex i).nu.source_source, min_comm, ← (complex i).nu.source_source]
  change truncate k false (truncate i false (topTable i)) = _
  rw [topTable_bounded]

lemma sourceCollapse_bounded {i k r : ℕ} (hrk : r < k) (t : Table (complex.{u} i))
    (ht : truncate r false t = t) : (sourceCollapse i k).nu.map t = t := by
  obtain ⟨p,b,_,hpr,rfl⟩ := bounded_table_classification t ht
  change (sourceCollapse i k).table (truncate p b (topTable i)) = _
  rw [Hom.table_truncate]
  change truncate p b ((sourceCollapse i k).nu.map (topTable i)) = _
  rw [sourceCollapse_top, truncate_truncate, ite_eq_left (by omega)]

lemma sourceCollapse_comp_truncated {i k : ℕ} {Y : OmegaCategory.{v}}
    (hk : Y.IsTruncated k) (F : OmegaCategory.Functor (complex.{u} i).nu Y) :
    OmegaCategory.Functor.comp (sourceCollapse i k).nu F = F := by
  apply functor_ext
  change F.map ((sourceCollapse i k).nu.map (topTable i)) = F.map (topTable i)
  rw [sourceCollapse_top]
  change F.map ((complex i).nu.source k (topTable i)) = F.map (topTable i)
  erw [F.map_source, hk]

def faceRetraction (i k : ℕ) : Hom (complex.{u} i) (complex.{u} k) :=
  tableMap i (topTable k)

lemma faceRetraction_top {i k : ℕ} (hki : k ≤ i) :
    (faceRetraction.{u} i k).nu.map (topTable i) = topTable k := by
  rw [faceRetraction, tableMap_nu_top]
  exact (complex k).nu.source_fixed_upwards hki (topTable_bounded k)

lemma faceMap_retraction {i k : ℕ} (hki : k ≤ i) :
    Hom.comp (faceMap.{u} i k false) (faceRetraction i k) = Hom.id (complex k) := by
  apply hom_ext
  change (faceRetraction i k).nu.map ((faceMap i k false).nu.map (topTable k)) = topTable k
  rw [faceMap_top]
  change (faceRetraction i k).table (truncate k false (topTable i)) = topTable k
  rw [Hom.table_truncate]
  change truncate k false ((faceRetraction i k).nu.map (topTable i)) = topTable k
  rw [faceRetraction_top hki, topTable_bounded]

lemma retraction_faceMap {i k : ℕ} (hki : k ≤ i) :
    Hom.comp (faceRetraction.{u} i k) (faceMap i k false) = sourceCollapse i k := by
  apply hom_ext
  change (faceMap i k false).nu.map ((faceRetraction i k).nu.map (topTable i)) = _
  rw [faceRetraction_top hki, faceMap_top, sourceCollapse_top]

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex

lemma cylinder_map_endpoint {i j : ℕ} (f : Hom (complex.{u} i) (complex.{u} j))
    (a : Bool) (x : Table (complex i)) :
    f.cylinder.nu.map (atEnd a x) = atEnd a (f.nu.map x) :=
  congrArg (fun g : Hom (complex i) (K j) => g.nu.map x) (f.cylinder_endpoint a)

lemma sourceCollapse_cylinder_truncated {i k : ℕ} {Y : OmegaCategory.{v}}
    (hk : Y.IsTruncated k) (F : OmegaCategory.Functor (K.{u} i).nu Y) :
    OmegaCategory.Functor.comp (sourceCollapse i k).cylinder.nu F = F := by
  apply functor_ext_truncated hk
  · intro a x _
    change F.map ((sourceCollapse i k).cylinder.nu.map (atEnd a x)) = F.map (atEnd a x)
    rw [cylinder_map_endpoint]
    let E : OmegaCategory.Functor (complex i).nu Y :=
      OmegaCategory.Functor.comp ((complex i).cylinderEndpoint a).nu F
    exact congrArg (fun g : OmegaCategory.Functor (complex i).nu Y => g.map x)
      (sourceCollapse_comp_truncated hk E)
  · intro r hr x hx
    change F.map ((sourceCollapse i k).cylinder.nu.map (verticalTable x)) = F.map (verticalTable x)
    rw [verticalTable_natural, sourceCollapse_bounded hr x hx]

def truncatedRestrictionEquiv {i k : ℕ} (hki : k ≤ i) {Y : OmegaCategory.{v}}
    (hk : Y.IsTruncated k) :
    OmegaCategory.Functor (K.{u} i).nu Y ≃ OmegaCategory.Functor (K.{u} k).nu Y where
  toFun F := OmegaCategory.Functor.comp (faceMap i k false).cylinder.nu F
  invFun F := OmegaCategory.Functor.comp (faceRetraction i k).cylinder.nu F
  left_inv F := by
    have ht : Hom.comp (faceRetraction i k).cylinder (faceMap i k false).cylinder =
        (sourceCollapse.{u} i k).cylinder := by
      rw [← Hom.cylinder_comp, retraction_faceMap hki]
    change OmegaCategory.Functor.comp
      (Hom.comp (faceRetraction i k).cylinder (faceMap i k false).cylinder).nu F = F
    rw [ht]
    exact sourceCollapse_cylinder_truncated hk F
  right_inv F := by
    have ht : Hom.comp (faceMap i k false).cylinder (faceRetraction i k).cylinder =
        Hom.id (K.{u} k) := by
      rw [← Hom.cylinder_comp, faceMap_retraction hki, Hom.cylinder_id]
    change OmegaCategory.Functor.comp
      (Hom.comp (faceMap i k false).cylinder (faceRetraction i k).cylinder).nu F = F
    rw [ht]
    rfl

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma internalHom_truncated (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    {Y : OmegaCategory.{u}} {k : ℕ} (hk : Y.IsTruncated k) :
    (R.obj Y).IsTruncated k := by
  intro x
  obtain ⟨i,hi⟩ := (R.obj Y).finite_dimension x
  let F : (complex i).nu ⟶ R.obj Y := lift x hi
  let P : T.tensor.obj (complex i).nu ⟶ Y := (adj.homEquiv _ _).symm F
  let G : (complex i).cylinder.nu ⟶ Y := (T.globe i).inv ≫ P
  let q := sourceCollapse.{u} i k
  have hG : q.cylinder.nu ≫ G = G :=
    GrayRecursive.sourceCollapse_cylinder_truncated hk G
  have he : P = (T.globe i).hom ≫ G := by
    dsimp [G]
    simp
  have hP : T.tensor.map q.nu ≫ P = P := by
    calc
      T.tensor.map q.nu ≫ P = T.tensor.map q.nu ≫ (T.globe i).hom ≫ G := by rw [← he]
      _ = (T.globe i).hom ≫ q.cylinder.nu ≫ G := by
        rw [← Category.assoc, T.globe_natural, Category.assoc]
      _ = (T.globe i).hom ≫ G := by rw [hG]
      _ = P := he.symm
  have hF : q.nu ≫ F = F := by
    calc
      q.nu ≫ F = q.nu ≫ (adj.homEquiv _ _) P := by rw [Equiv.apply_symm_apply]
      _ = (adj.homEquiv _ _) (T.tensor.map q.nu ≫ P) :=
        (adj.homEquiv_naturality_left q.nu P).symm
      _ = (adj.homEquiv _ _) P := by rw [hP]
      _ = F := Equiv.apply_symm_apply _ _
  have hh := congrArg (fun f : (complex i).nu ⟶ R.obj Y => f.map (topTable i)) hF
  change F.map (q.nu.map (topTable i)) = F.map (topTable i) at hh
  rw [sourceCollapse_top] at hh
  change F.map ((complex i).nu.source k (topTable i)) = F.map (topTable i) at hh
  erw [F.map_source] at hh
  simpa only [F, lift_top] using hh

def truncatedCylinderEquiv (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (k : ℕ) (X Y : OmegaCategory.{u}) (hk : Y.IsTruncated k) :
    (T.tensor.obj (truncation k X).val ⟶ Y) ≃ (T.tensor.obj X ⟶ Y) :=
  ((adj.homEquiv (truncation k X).val Y).trans
    (truncationHomEquiv k X ⟨R.obj Y, T.internalHom_truncated R adj hk⟩)).trans
      (adj.homEquiv X Y).symm

lemma truncatedCylinderEquiv_apply (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (k : ℕ) (X Y : OmegaCategory.{u}) (hk : Y.IsTruncated k)
    (P : T.tensor.obj (truncation k X).val ⟶ Y) :
    T.truncatedCylinderEquiv R adj k X Y hk P = T.tensor.map (truncationUnit k X) ≫ P := by
  apply (adj.homEquiv X Y).injective
  change (adj.homEquiv X Y) ((adj.homEquiv X Y).symm
    (truncationUnit k X ≫ (adj.homEquiv (truncation k X).val Y) P)) = _
  erw [Equiv.apply_symm_apply, adj.homEquiv_naturality_left]
  rfl

lemma truncatedCylinderEquiv_endpoint (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (k : ℕ) (X Y : OmegaCategory.{u}) (hk : Y.IsTruncated k)
    (P : T.tensor.obj (truncation k X).val ⟶ Y) (a : Bool) :
    (T.endpoint a).app X ≫ T.truncatedCylinderEquiv R adj k X Y hk P =
      truncationUnit k X ≫ (T.endpoint a).app (truncation k X).val ≫ P := by
  erw [T.truncatedCylinderEquiv_apply, ← Category.assoc,
    ← (T.endpoint a).naturality, Category.assoc]

end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory Limits OmegaCategory

variable (T : RightIntervalExtension.{u})
variable (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)

def finiteInternalHom (n : ℕ) : NCategory.{u} n ⥤ NCategory.{u} n where
  obj Y := ⟨R.obj Y.val, T.internalHom_truncated R adj Y.property⟩
  map f := R.map f
  map_id Y := R.map_id Y.val
  map_comp f g := R.map_comp f g

def finiteTranspose (n : ℕ) (X Y : NCategory.{u} n) :
    (T.tensor.obj X.val ⟶ Y.val) ≃ (X ⟶ (T.finiteInternalHom R adj n).obj Y) :=
  adj.homEquiv X.val Y.val

section FiniteDescent
variable {n : ℕ} {A B X Y Z : NCategory.{u} n}
variable {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
variable (sq : IsPushout i a b j)

def finiteGlue (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.obj Y.val ⟶ Z.val :=
  (T.finiteTranspose R adj n Y Z).symm
    (sq.desc ((T.finiteTranspose R adj n B Z) PB) ((T.finiteTranspose R adj n X Z) PX)
      (by
        change OmegaCategory.Functor.comp i ((adj.homEquiv _ _) PB) =
          OmegaCategory.Functor.comp a ((adj.homEquiv _ _) PX)
        exact (adj.homEquiv_naturality_left i PB).symm.trans
          ((congrArg (adj.homEquiv _ _) h).trans (adj.homEquiv_naturality_left a PX))))

lemma finiteGlue_left (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.map b ≫ T.finiteGlue R adj sq PB PX h = PB := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left]
  change b ≫ (T.finiteTranspose R adj n Y Z)
    ((T.finiteTranspose R adj n Y Z).symm _) = _
  rw [Equiv.apply_symm_apply, sq.inl_desc]
  rfl

lemma finiteGlue_right (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.map j ≫ T.finiteGlue R adj sq PB PX h = PX := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left]
  change j ≫ (T.finiteTranspose R adj n Y Z)
    ((T.finiteTranspose R adj n Y Z).symm _) = _
  rw [Equiv.apply_symm_apply, sq.inr_desc]
  rfl

include R adj sq in
lemma finiteCylinder_hom_ext {P Q : T.tensor.obj Y.val ⟶ Z.val}
    (hb : T.tensor.map b ≫ P = T.tensor.map b ≫ Q)
    (hj : T.tensor.map j ≫ P = T.tensor.map j ≫ Q) : P = Q := by
  apply (T.finiteTranspose R adj n Y Z).injective
  apply sq.hom_ext
  · change OmegaCategory.Functor.comp b ((adj.homEquiv _ _) P) =
      OmegaCategory.Functor.comp b ((adj.homEquiv _ _) Q)
    exact (adj.homEquiv_naturality_left b P).symm.trans
      ((congrArg (adj.homEquiv _ _) hb).trans (adj.homEquiv_naturality_left b Q))
  · change OmegaCategory.Functor.comp j ((adj.homEquiv _ _) P) =
      OmegaCategory.Functor.comp j ((adj.homEquiv _ _) Q)
    exact (adj.homEquiv_naturality_left j P).symm.trans
      ((congrArg (adj.homEquiv _ _) hj).trans (adj.homEquiv_naturality_left j Q))

lemma finiteGlue_endpoint_left
    (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) (ε : Bool) :
    OmegaCategory.Functor.comp b
        ((T.endpoint ε).app Y.val ≫ T.finiteGlue R adj sq PB PX h) =
      (T.endpoint ε).app B.val ≫ PB := by
  have hb := (T.endpoint ε).naturality b
  exact (congrArg (fun f : B.val ⟶ T.tensor.obj Y.val =>
    f ≫ T.finiteGlue R adj sq PB PX h) hb).trans
    (congrArg (fun f => (T.endpoint ε).app B.val ≫ f)
      (T.finiteGlue_left R adj sq PB PX h))

lemma finiteGlue_endpoint_right
    (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) (ε : Bool) :
    OmegaCategory.Functor.comp j
        ((T.endpoint ε).app Y.val ≫ T.finiteGlue R adj sq PB PX h) =
      (T.endpoint ε).app X.val ≫ PX := by
  have hj := (T.endpoint ε).naturality j
  exact (congrArg (fun f : X.val ⟶ T.tensor.obj Y.val =>
    f ≫ T.finiteGlue R adj sq PB PX h) hj).trans
    (congrArg (fun f => (T.endpoint ε).app X.val ≫ f)
      (T.finiteGlue_right R adj sq PB PX h))

include R adj sq in

theorem finite_stationary_gluing
    (P : T.tensor.obj B.val ⟶ B.val)
    (F : Bool → (B ⟶ B))
    (he : ∀ ε, (T.endpoint ε).app B.val ≫ P = F ε)
    (hs : T.tensor.map i ≫ P = (T.projection.app A.val) ≫ i) :
    ∃ Q : T.tensor.obj Y.val ⟶ Y.val,
      T.tensor.map b ≫ Q = P ≫ b ∧
      T.tensor.map j ≫ Q = T.projection.app X.val ≫ j ∧
      (∀ ε, OmegaCategory.Functor.comp b ((T.endpoint ε).app Y.val ≫ Q) = F ε ≫ b) ∧
      (∀ ε, OmegaCategory.Functor.comp j ((T.endpoint ε).app Y.val ≫ Q) = j) ∧
      (∀ Q' : T.tensor.obj Y.val ⟶ Y.val,
        T.tensor.map b ≫ Q' = P ≫ b →
        T.tensor.map j ≫ Q' = T.projection.app X.val ≫ j → Q' = Q) := by
  have hc : T.tensor.map i ≫ (P ≫ b) =
      T.tensor.map a ≫ (T.projection.app X.val ≫ j) := by
    calc
      _ = (T.projection.app A.val) ≫ (show A.val ⟶ Y.val from i ≫ b) := by
        rw [← Category.assoc, hs, Category.assoc]
      _ = (T.projection.app A.val) ≫ (show A.val ⟶ Y.val from a ≫ j) :=
        congrArg (fun f : A ⟶ Y => T.projection.app A.val ≫ f) sq.w
      _ = _ := by
        have ha := T.projection.naturality a
        change _ = (T.tensor.map a ≫ T.projection.app X.val) ≫ j
        rw [ha]
        rfl
  let Q := T.finiteGlue R adj sq (P ≫ b) (T.projection.app X.val ≫ j) hc
  refine ⟨Q, T.finiteGlue_left R adj sq _ _ hc,
    T.finiteGlue_right R adj sq _ _ hc, ?_, ?_, ?_⟩
  · intro ε
    rw [T.finiteGlue_endpoint_left, ← Category.assoc, he ε]
    rfl
  · intro ε
    rw [T.finiteGlue_endpoint_right, ← Category.assoc]
    have hε := congrArg (fun α => α.app X.val) (T.endpoint_projection ε)
    change (T.endpoint ε).app X.val ≫ T.projection.app X.val = 𝟙 X.val at hε
    rw [hε]; rfl
  · intro Q' hb hj
    apply T.finiteCylinder_hom_ext R adj sq
    · exact hb.trans (T.finiteGlue_left R adj sq _ _ hc).symm
    · exact hj.trans (T.finiteGlue_right R adj sq _ _ hc).symm

include R adj sq in

lemma finite_stationary_gluing_natural
    {X' Y' : NCategory.{u} n} {j' : X' ⟶ Y'} {b' : B ⟶ Y'}
    (w : X ⟶ X') (v : Y ⟶ Y') (hvB : b ≫ v = b') (hvX : j ≫ v = w ≫ j')
    (P : T.tensor.obj B.val ⟶ B.val)
    (Q : T.tensor.obj Y.val ⟶ Y.val) (Q' : T.tensor.obj Y'.val ⟶ Y'.val)
    (hB : T.tensor.map b ≫ Q = P ≫ b)
    (hX : T.tensor.map j ≫ Q = T.projection.app X.val ≫ j)
    (hB' : T.tensor.map b' ≫ Q' = P ≫ b')
    (hX' : T.tensor.map j' ≫ Q' = T.projection.app X'.val ≫ j') :
    T.tensor.map v ≫ Q' = Q ≫ v := by
  apply T.finiteCylinder_hom_ext R adj sq
  · calc
      _ = T.tensor.map (show B.val ⟶ Y'.val from b ≫ v) ≫ Q' := by
        rw [T.tensor.map_comp, Category.assoc]
      _ = T.tensor.map b' ≫ Q' :=
        congrArg (fun f : B ⟶ Y' => T.tensor.map f ≫ Q') hvB
      _ = P ≫ b' := hB'
      _ = (P ≫ b) ≫ v :=
        congrArg (fun f : B ⟶ Y' => P ≫ f) hvB.symm
      _ = _ := by rw [← hB, Category.assoc]
  · calc
      _ = T.tensor.map (show X.val ⟶ Y'.val from j ≫ v) ≫ Q' := by
        rw [T.tensor.map_comp, Category.assoc]
      _ = T.tensor.map (show X.val ⟶ Y'.val from w ≫ j') ≫ Q' :=
        congrArg (fun f : X ⟶ Y' => T.tensor.map f ≫ Q') hvX
      _ = T.tensor.map w ≫ (T.tensor.map j' ≫ Q') := by
        rw [T.tensor.map_comp, Category.assoc]
      _ = T.tensor.map w ≫ (T.projection.app X'.val ≫ j') := by rw [hX']
      _ = T.projection.app X.val ≫ (show X.val ⟶ Y'.val from w ≫ j') := by
        rw [← Category.assoc, T.projection.naturality w]; rfl
      _ = (T.projection.app X.val ≫ j) ≫ v :=
        congrArg (fun f : X ⟶ Y' => T.projection.app X.val ≫ f) hvX.symm
      _ = _ := by rw [← hX, Category.assoc]

end FiniteDescent
end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory Simplicial MonoidalCategory Opposite
open DirectedComplex NormalizedChains OmegaCategory

variable (T : RightIntervalExtension.{u})

lemma simplex_inverse_natural {P Q : Type u} [LinearOrder P] [Finite P]
    [LinearOrder Q] [Finite Q] (f : Hom (complex P) (complex Q)) :
    f.cylinder.nu ≫ (T.simplex Q).inv = (T.simplex P).inv ≫ T.tensor.map f.nu := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← T.simplex_natural, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

def cut {P : Type u} [LinearOrder P] [Finite P] (θ : P →o Fin 2) :
    (complex P).nu ⟶ T.tensor.obj (complex P).nu :=
  (awHom θ).nu ≫ (T.simplex P).inv

lemma cut_natural {P Q : Type u} [LinearOrder P] [Finite P]
    [LinearOrder Q] [Finite Q] (f : P →o Q) (θ : Q →o Fin 2) :
    (complexMap f).nu ≫ T.cut θ = T.cut (θ.comp f) ≫ T.tensor.map (complexMap f).nu := by
  change (Hom.comp (complexMap f) (awHom θ)).nu ≫ (T.simplex Q).inv = _
  rw [awHom_naturality]
  change (awHom (θ.comp f)).nu ≫ ((complexMap f).cylinder.nu ≫ (T.simplex Q).inv) = _
  rw [T.simplex_inverse_natural]
  rfl

lemma cut_endpoint {P : Type u} [LinearOrder P] [Finite P] (ε : Bool) :
    T.cut (OrderHom.const P (if ε then 1 else 0)) = (T.endpoint ε).app (complex P).nu := by
  unfold cut
  rw [awHom_endpoint, ← T.simplex_endpoint, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

lemma cut_projection {P : Type u} [LinearOrder P] [Finite P] (θ : P →o Fin 2) :
    T.cut θ ≫ T.projection.app (complex P).nu = 𝟙 (complex P).nu := by
  unfold cut
  rw [← T.simplex_projection]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg Hom.nu (awHom_projection θ)

def raiseSimplex {X : OmegaCategory.{u}} {m : ℕ} (F : OmegaCategory.Functor (Oriental m) X) :
    (complex (ULift.{u} (Fin (m+1)))).nu ⟶ X :=
  OmegaCategory.Functor.comp (complexMap (orderULiftDown _)).nu F

lemma up_raiseSimplex {X : OmegaCategory.{u}} {m : ℕ}
    (F : OmegaCategory.Functor (Oriental m) X) :
    OmegaCategory.Functor.comp (complexMap (orderULiftUp.{0,u} (Fin (m+1)))).nu
      (raiseSimplex F) = F := by
  have h := congrArg Hom.nu (complexMap_comp (orderULiftUp.{0,u} (Fin (m+1)))
    (orderULiftDown _))
  rw [orderULiftUp_down, complexMap_id] at h
  exact congrArg (fun a => OmegaCategory.Functor.comp a F) h.symm

lemma raiseSimplex_precomp {X : OmegaCategory.{u}} {m n : ℕ}
    (a : Fin (m+1) →o Fin (n+1)) (F : OmegaCategory.Functor (Oriental n) X) :
    raiseSimplex (OmegaCategory.Functor.comp (complexMap a).nu F) =
      (complexMap ((orderULiftUp _).comp (a.comp (orderULiftDown _)))).nu ≫
        raiseSimplex F := by
  have h₁ := complexMap_comp (orderULiftDown.{0,u} (Fin (m+1))) a
  have h₂ := complexMap_comp
    ((orderULiftUp.{0,u} (Fin (n+1))).comp (a.comp (orderULiftDown _))) (orderULiftDown _)
  have hc : (orderULiftDown (Fin (n+1))).comp
      ((orderULiftUp.{0,u} _).comp (a.comp (orderULiftDown _))) = a.comp (orderULiftDown _) := rfl
  rw [hc, h₁] at h₂
  exact congrArg (fun f => OmegaCategory.Functor.comp f.nu F) h₂

lemma up_simplexMap {m n : ℕ} (a : Fin (m+1) →o Fin (n+1)) :
    OmegaCategory.Functor.comp (complexMap (orderULiftUp.{0,u} (Fin (m+1)))).nu
      (complexMap ((orderULiftUp.{0,u} (Fin (n+1))).comp (a.comp (orderULiftDown _)))).nu =
    OmegaCategory.Functor.comp (complexMap a).nu
      (complexMap (orderULiftUp.{0,u} (Fin (n+1)))).nu := by
  have h₁ := complexMap_comp (orderULiftUp.{0,u} (Fin (m+1)))
    ((orderULiftUp.{0,u} (Fin (n+1))).comp (a.comp (orderULiftDown _)))
  have hc : ((orderULiftUp.{0,u} (Fin (n+1))).comp
    (a.comp (orderULiftDown _))).comp (orderULiftUp (Fin (m+1))) =
      (orderULiftUp _).comp a := rfl
  rw [hc, complexMap_comp] at h₁
  exact congrArg Hom.nu h₁.symm

def nerveCylinderSimplex {X Y : OmegaCategory.{u}}
    (P : T.tensor.obj X ⟶ Y) (m : ℕ) (F : OmegaCategory.Functor (Oriental m) X)
    (θ : Fin (m+1) →o Fin 2) : OmegaCategory.Functor (Oriental m) Y :=
  OmegaCategory.Functor.comp (complexMap (orderULiftUp.{0,u} (Fin (m+1)))).nu
    (T.cut (θ.comp (orderULiftDown _)) ≫ T.tensor.map (raiseSimplex F) ≫ P)

lemma nerveCylinderSimplex_natural {X Y : OmegaCategory.{u}}
    (P : T.tensor.obj X ⟶ Y) {m n : ℕ} (a : Fin (m+1) →o Fin (n+1))
    (F : OmegaCategory.Functor (Oriental n) X) (θ : Fin (n+1) →o Fin 2) :
    T.nerveCylinderSimplex P m (OmegaCategory.Functor.comp (complexMap a).nu F)
      (θ.comp a) = OmegaCategory.Functor.comp (complexMap a).nu
        (T.nerveCylinderSimplex P n F θ) := by
  unfold nerveCylinderSimplex
  rw [raiseSimplex_precomp, T.tensor.map_comp]
  let b := (orderULiftUp.{0,u} (Fin (n+1))).comp (a.comp (orderULiftDown _))
  have hc : (θ.comp a).comp (orderULiftDown _) =
      (θ.comp (orderULiftDown _)).comp b := rfl
  rw [hc]
  have hcut := T.cut_natural b (θ.comp (orderULiftDown _))
  have h := congrArg (fun f => OmegaCategory.Functor.comp
    (complexMap (orderULiftUp.{0,u} (Fin (m+1)))).nu
    (f ≫ T.tensor.map (raiseSimplex F) ≫ P)) hcut.symm
  apply h.trans
  exact congrArg (fun f => OmegaCategory.Functor.comp f
    (T.cut (θ.comp (orderULiftDown _)) ≫ T.tensor.map (raiseSimplex F) ≫ P))
      (up_simplexMap a)

lemma nerveCylinderSimplex_endpoint {X Y : OmegaCategory.{u}}
    (P : T.tensor.obj X ⟶ Y) (m : ℕ) (F : OmegaCategory.Functor (Oriental m) X) (ε : Bool) :
    T.nerveCylinderSimplex P m F (OrderHom.const _ (if ε then 1 else 0)) =
      OmegaCategory.Functor.comp F ((T.endpoint ε).app X ≫ P) := by
  unfold nerveCylinderSimplex
  have hc : (OrderHom.const (Fin (m+1)) (if ε then (1 : Fin 2) else 0)).comp
      (orderULiftDown.{0,u} (Fin (m+1))) = OrderHom.const _ (if ε then 1 else 0) := rfl
  rw [hc, T.cut_endpoint]
  have hn := (T.endpoint ε).naturality (raiseSimplex F)
  exact (congrArg (fun f => OmegaCategory.Functor.comp
    (complexMap (orderULiftUp.{0,u} (Fin (m+1)))).nu (f ≫ P)) hn.symm).trans
    (congrArg (fun f => OmegaCategory.Functor.comp f ((T.endpoint ε).app X ≫ P))
      (up_raiseSimplex F))

def nerveCylinder {X Y : OmegaCategory.{u}} (P : T.tensor.obj X ⟶ Y) :
    streetNerve X ⊗ Δ[1] ⟶ streetNerve Y where
  app m := ↾fun x => T.nerveCylinderSimplex P m.unop.len x.1
    (SSet.stdSimplex.objEquiv x.2).toOrderHom
  naturality m n a := by
    apply ConcreteCategory.hom_ext
    intro x
    exact T.nerveCylinderSimplex_natural P a.unop.toOrderHom x.1
      (SSet.stdSimplex.objEquiv x.2).toOrderHom

lemma nerveCylinder_endpoint {X Y : OmegaCategory.{u}} (P : T.tensor.obj X ⟶ Y)
    (ε : Bool) : (if ε then SSet.ι₁ else SSet.ι₀) ≫ T.nerveCylinder P =
      streetNerveMap ((T.endpoint ε).app X ≫ P) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  cases ε
  · exact T.nerveCylinderSimplex_endpoint P m.unop.len F false
  · exact T.nerveCylinderSimplex_endpoint P m.unop.len F true

def nerveHomotopy {X Y : OmegaCategory.{u}} (P : T.tensor.obj X ⟶ Y) :
    SSet.Homotopy (streetNerveMap ((T.endpoint false).app X ≫ P))
      (streetNerveMap ((T.endpoint true).app X ≫ P)) where
  h := T.nerveCylinder P
  h₀ := T.nerveCylinder_endpoint P false
  h₁ := T.nerveCylinder_endpoint P true
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x, hx⟩, θ⟩
    exact False.elim hx

lemma nerveCylinder_postcomp {X Y Z : OmegaCategory.{u}}
    (P : T.tensor.obj X ⟶ Y) (v : Y ⟶ Z) :
    T.nerveCylinder (P ≫ v) = T.nerveCylinder P ≫ streetNerveMap v := rfl

lemma nerveCylinder_precomp {A X Y : OmegaCategory.{u}}
    (i : A ⟶ X) (P : T.tensor.obj X ⟶ Y) :
    streetNerveMap i ▷ Δ[1] ≫ T.nerveCylinder P = T.nerveCylinder (T.tensor.map i ≫ P) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  rintro ⟨F,θ⟩
  change T.nerveCylinderSimplex P _ (OmegaCategory.Functor.comp F i) _ = _
  unfold nerveCylinderSimplex
  have hr : raiseSimplex (OmegaCategory.Functor.comp F i) = raiseSimplex F ≫ i := rfl
  rw [hr, T.tensor.map_comp]
  rfl

open CartesianMonoidalCategory in
lemma nerveCylinder_projection (X : OmegaCategory.{u}) :
    T.nerveCylinder (T.projection.app X) = fst (streetNerve X) Δ[1] := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  rintro ⟨F,θ⟩
  change T.nerveCylinderSimplex (T.projection.app X) m.unop.len F _ = F
  unfold nerveCylinderSimplex
  rw [T.projection.naturality, ← Category.assoc, T.cut_projection, Category.id_comp]
  exact up_raiseSimplex F

open CartesianMonoidalCategory in

lemma nerveCylinder_stationary {A X Y : OmegaCategory.{u}}
    (i : A ⟶ X) (v : A ⟶ Y) (P : T.tensor.obj X ⟶ Y)
    (hs : T.tensor.map i ≫ P = T.projection.app A ≫ v) :
    streetNerveMap i ▷ Δ[1] ≫ T.nerveCylinder P = fst (streetNerve A) Δ[1] ≫ streetNerveMap v := by
  rw [T.nerveCylinder_precomp, hs, T.nerveCylinder_postcomp, T.nerveCylinder_projection]

lemma nerve_weak_iff {X Y : OmegaCategory.{u}} (P : T.tensor.obj X ⟶ Y) :
    simplicialWeakEquivalences (streetNerveMap ((T.endpoint false).app X ≫ P)) ↔
      simplicialWeakEquivalences (streetNerveMap ((T.endpoint true).app X ≫ P)) :=
  simplicialWeakEquivalences_homotopy (T.nerveHomotopy P)

end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.RelativePrismData
open DirectedComplex NormalizedChains

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable {P Q : Type u} [LinearOrder P] [LinearOrder Q] [Finite P] [Finite Q]

def finiteImage (σ : P →o E) : FiniteVertexChain E where
  vertices := Set.range (d.f ∘ σ) ∪ Set.range (d.g ∘ σ)
  finite := (Set.finite_range _).union (Set.finite_range _)
  total := by
    have hfg (x y : P) : d.f (σ x) ≤ d.g (σ y) ∨ d.g (σ y) ≤ d.f (σ x) := by
      by_cases hy : σ y ∈ A
      · rw [← d.agree (σ y) hy]
        exact (le_total x y).imp
          (fun h => d.f.monotone (σ.monotone h)) (fun h => d.f.monotone (σ.monotone h))
      · left
        rcases le_total x y with h | h
        · exact (d.f.monotone (σ.monotone h)).trans (d.below _)
        · have hx : σ x ∉ A := fun hx => hy (d.lowerSet (σ.monotone h) hx)
          rw [d.constant (σ y) hy (σ x) hx]
          exact d.below _
    rintro e (⟨x,rfl⟩ | ⟨x,rfl⟩) e' (⟨y,rfl⟩ | ⟨y,rfl⟩)
    · exact (le_total x y).imp
        (fun h => d.f.monotone (σ.monotone h)) (fun h => d.f.monotone (σ.monotone h))
    · exact hfg x y
    · exact (hfg y x).symm
    · exact (le_total x y).imp
        (fun h => d.g.monotone (σ.monotone h)) (fun h => d.g.monotone (σ.monotone h))

def finiteImageLeft (σ : P →o E) : P →o (d.finiteImage σ).vertices where
  toFun x := ⟨d.f (σ x), Or.inl ⟨x,rfl⟩⟩
  monotone' _ _ h := d.f.monotone (σ.monotone h)

def finiteImageRight (σ : P →o E) : P →o (d.finiteImage σ).vertices where
  toFun x := ⟨d.g (σ x), Or.inr ⟨x,rfl⟩⟩
  monotone' _ _ h := d.g.monotone (σ.monotone h)

lemma finiteImage_mono (σ : Q →o E) (α : P →o Q) :
    (d.finiteImage (σ.comp α)).vertices ⊆ (d.finiteImage σ).vertices := by
  rintro e (⟨i,hi⟩ | ⟨i,hi⟩)
  · exact Or.inl ⟨α i,hi⟩
  · exact Or.inr ⟨α i,hi⟩

def finiteAntihomotopy (σ : P →o E) :
    PositiveAntihomotopy (complexMap (d.finiteImageLeft σ))
      (complexMap (d.finiteImageRight σ)) := by
  refine PositiveAntihomotopy.lift (complexMap (d.finiteImageLeft σ))
    (complexMap (d.finiteImageRight σ)) (complexMap (d.finiteImage σ).inclusion)
    ?_ (d.antihomotopy.precomp (complexMap σ)) ?_ ?_
    (gradedPrism (d.finiteImageLeft σ) (d.finiteImageRight σ)) ?_ ?_
  · intro p x y h
    apply Subtype.ext
    have hv : map (d.finiteImage σ).inclusion x.val =
        map (d.finiteImage σ).inclusion y.val :=
      congrArg (fun z : grade (E := E) (p+1) => z.val) h
    apply map_orderEmbedding_injective
      (OrderEmbedding.subtype (d.finiteImage σ).vertices)
    exact hv
  · intro p x
    apply Subtype.ext
    change map (d.finiteImage σ).inclusion (map (d.finiteImageLeft σ) x.val) =
      map d.f (map σ x.val)
    simp only [← map_comp]
    rfl
  · intro p x
    apply Subtype.ext
    change map (d.finiteImage σ).inclusion (map (d.finiteImageRight σ) x.val) =
      map d.g (map σ x.val)
    simp only [← map_comp]
    rfl
  · intro p x hx
    exact prism_positive _ _ hx
  · intro p x
    apply Subtype.ext
    change map (d.finiteImage σ).inclusion
      (prism (d.finiteImageLeft σ) (d.finiteImageRight σ) x.val) =
      prism d.f d.g (map σ x.val)
    rw [map_prism _ _ (fun i => d.below (σ i)), prism_map]
    rfl

def finiteCylinderChainMap (σ : P →o E) :
    Hom (complex P).cylinder (complex (d.finiteImage σ).vertices) :=
  (d.finiteAntihomotopy σ).cylinderHom

lemma finiteCylinderChainMap_inclusion (σ : P →o E) :
    Hom.comp (d.finiteCylinderChainMap σ) (complexMap (d.finiteImage σ).inclusion) =
      Hom.comp (complexMap σ).cylinder d.cylinderChainMap := by
  ext p x
  cases p with
  | zero =>
    apply Subtype.ext
    change map (d.finiteImage σ).inclusion
      (map (d.finiteImageLeft σ) x.1.val + map (d.finiteImageRight σ) x.2.val) =
      map d.f (map σ x.1.val) + map d.g (map σ x.2.val)
    simp only [map_add, ← map_comp]
    rfl
  | succ p =>
    apply Subtype.ext
    change map (d.finiteImage σ).inclusion
      (map (d.finiteImageLeft σ) x.1.val + map (d.finiteImageRight σ) x.2.1.val +
        prism (d.finiteImageLeft σ) (d.finiteImageRight σ) x.2.2.val) =
      map d.f (map σ x.1.val) + map d.g (map σ x.2.1.val) +
        prism d.f d.g (map σ x.2.2.val)
    simp only [map_add, ← map_comp]
    rw [map_prism _ _ (fun i => d.below (σ i)), prism_map]
    rfl

lemma finiteCylinderChainMap_natural (σ : Q →o E) (α : P →o Q) :
    Hom.comp (d.finiteCylinderChainMap (σ.comp α))
      (complexMap ((d.finiteImage (σ.comp α)).subInclusion (d.finiteImage σ)
        (d.finiteImage_mono σ α))) =
      Hom.comp (complexMap α).cylinder (d.finiteCylinderChainMap σ) := by
  ext p x
  apply complexMap_orderEmbedding_injective (OrderEmbedding.subtype (d.finiteImage σ).vertices) p
  have hl := congrArg (fun h => h.map p x) (d.finiteCylinderChainMap_inclusion (σ.comp α))
  have hr := congrArg (fun h => h.map p ((complexMap α).cylinder.map p x))
    (d.finiteCylinderChainMap_inclusion σ)
  have he : Hom.comp (complexMap ((d.finiteImage (σ.comp α)).subInclusion (d.finiteImage σ)
      (d.finiteImage_mono σ α))) (complexMap (d.finiteImage σ).inclusion) =
      complexMap (d.finiteImage (σ.comp α)).inclusion := by
    rw [← complexMap_comp]; rfl
  have hc : Hom.comp (complexMap α).cylinder (complexMap σ).cylinder =
      (complexMap (σ.comp α)).cylinder := by rw [complexMap_comp, Hom.cylinder_comp]
  change (Hom.comp (complexMap ((d.finiteImage (σ.comp α)).subInclusion (d.finiteImage σ)
      (d.finiteImage_mono σ α))) (complexMap (d.finiteImage σ).inclusion)).map p
      ((d.finiteCylinderChainMap (σ.comp α)).map p x) = _
  rw [he]
  dsimp only [Hom.comp, AddMonoidHom.comp_apply] at hl hr ⊢
  exact hl.trans ((congrArg (fun h => d.cylinderChainMap.map p (h.map p x)) hc.symm).trans hr.symm)

lemma finiteCylinderChainMap_stationary (σ : P →o E) (hs : ∀ p, σ p ∈ A) :
    d.finiteCylinderChainMap σ =
      Hom.comp (complex P).cylinderProjection (complexMap (d.finiteImageLeft σ)) := by
  ext p x
  apply complexMap_orderEmbedding_injective (OrderEmbedding.subtype (d.finiteImage σ).vertices) p
  have h := congrArg (fun f => f.map p x) ((d.finiteCylinderChainMap_inclusion σ).trans
    (d.cylinderChainMap_stationary σ hs))
  have hc : Hom.comp (complexMap (d.finiteImageLeft σ))
      (complexMap (d.finiteImage σ).inclusion) = complexMap (d.f.comp σ) := by
    rw [← complexMap_comp]; rfl
  exact h.trans (congrArg (fun f => f.map p ((complex P).cylinderProjection.map p x)) hc.symm)

end Thomason.RelativePrismData

end

end OAI
