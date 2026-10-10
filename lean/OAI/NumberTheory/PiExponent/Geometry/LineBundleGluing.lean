import OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor

namespace OAI

noncomputable section

namespace PiExponentSeshadri.LineBundleGluing

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry

variable {X : Scheme} {ι : Type} (U : ι → X.Opens)

structure Cocycle where
  transition (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) : Γ(X,W)ˣ
  restriction (i j : ι) {V W : X.Opens} (h : V ≤ W) (hi : W ≤ U i) (hj : W ≤ U j) :
    X.presheaf.map (homOfLE h).op (transition i j W hi hj : Γ(X,W)) =
      (transition i j V (h.trans hi) (h.trans hj) : Γ(X,V))
  identity (i : ι) (W : X.Opens) (hi : W ≤ U i) :
    transition i i W hi hi = 1
  cocycle (i j k : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    transition i j W hi hj * transition j k W hj hk = transition i k W hi hk

def LocalIndex (V : X.Opens) := Σ i : ι, {W : X.Opens // W ≤ V ∧ W ≤ U i}

abbrev Family (V : X.Opens) := ∀ p : LocalIndex U V, Γ(X,p.2.val)

@[instance_reducible]
def localModule (V : X.Opens) (p : LocalIndex U V) :
    Module Γ(X,V) Γ(X,p.2.val) :=
  Module.compHom _ (X.presheaf.map (homOfLE p.2.property.1).op).hom

instance familyModule (V : X.Opens) : Module Γ(X,V) (Family U V) := by
  letI (p : LocalIndex U V) : Module Γ(X,V) Γ(X,p.2.val) := localModule U V p
  exact Pi.module _ _ _

variable {U} (c : Cocycle U)

def sections (V : X.Opens) : Submodule Γ(X,V) (Family U V) where
  carrier := {s | (∀ (i : ι) (W W' : X.Opens) (hW : W ≤ V) (hi : W ≤ U i)
    (h : W' ≤ W), X.presheaf.map (homOfLE h).op (s ⟨i,W,hW,hi⟩) =
      s ⟨i,W',h.trans hW,h.trans hi⟩) ∧
    (∀ (i j : ι) (W : X.Opens) (hW : W ≤ V) (hi : W ≤ U i) (hj : W ≤ U j),
      s ⟨i,W,hW,hi⟩ = (c.transition i j W hi hj : Γ(X,W)) * s ⟨j,W,hW,hj⟩)}
  zero_mem' := by
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op (0 : Γ(X, W)) = 0
      exact map_zero _
    · intro i j W hW hi hj
      change (0 : Γ(X, W)) = (c.transition i j W hi hj : Γ(X, W)) * 0
      simp only [mul_zero]
  add_mem' := by
    intro a b ha hb
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op (a ⟨i,W,hW,hi⟩ + b ⟨i,W,hW,hi⟩) = _
      rw [map_add, ha.1 i W W' hW hi h, hb.1 i W W' hW hi h]
      rfl
    · intro i j W hW hi hj
      change a ⟨i,W,hW,hi⟩ + b ⟨i,W,hW,hi⟩ = _
      rw [ha.2 i j W hW hi hj, hb.2 i j W hW hi hj, ← mul_add]
      rfl
  smul_mem' := by
    intro a s hs
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE hW).op a * s ⟨i,W,hW,hi⟩) =
        X.presheaf.map (homOfLE (h.trans hW)).op a * s ⟨i,W',h.trans hW,h.trans hi⟩
      rw [map_mul, hs.1 i W W' hW hi h]
      congr 1
      change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
      rw [← Functor.map_comp]
      rfl
    · intro i j W hW hi hj
      change X.presheaf.map (homOfLE hW).op a * s ⟨i,W,hW,hi⟩ =
        (c.transition i j W hi hj : Γ(X,W)) *
          (X.presheaf.map (homOfLE hW).op a * s ⟨j,W,hW,hj⟩)
      rw [hs.2 i j W hW hi hj]
      ring

def restrict {V W : X.Opens} (h : V ≤ W) : sections c W →+ sections c V where
  toFun s := ⟨fun p => s.val ⟨p.1,p.2.val,p.2.property.1.trans h,p.2.property.2⟩,
    ⟨fun i A B hA hi hBA => s.property.1 i A B (hA.trans h) hi hBA,
     fun i j A hA hi hj => s.property.2 i j A (hA.trans h) hi hj⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

lemma restrict_smul {V W : X.Opens} (h : V ≤ W) (a : Γ(X,W)) (s : sections c W) :
    restrict c h (a • s) = X.presheaf.map (homOfLE h).op a • restrict c h s := by
  apply Subtype.ext
  funext p
  change X.presheaf.map (homOfLE (p.2.property.1.trans h)).op a * _ =
    X.presheaf.map (homOfLE p.2.property.1).op
      (X.presheaf.map (homOfLE h).op a) * _
  congr 1
  change _ = (X.presheaf.map _ ≫ X.presheaf.map _) a
  rw [← Functor.map_comp]
  rfl

def presheaf : PresheafOfModules X.ringCatSheaf.obj where
  obj V := ModuleCat.of Γ(X, V.unop) (sections c V.unop)
  map {V W} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.presheaf.map f).hom).obj
      (ModuleCat.of Γ(X, W.unop) (sections c W.unop)))
    { toFun := restrict c (leOfHom f.unop)
      map_add' := fun a b => (restrict c (leOfHom f.unop)).map_add a b
      map_smul' := fun a s => restrict_smul c _ a s }
  map_id V := by ext; rfl
  map_comp f g := by ext; rfl

def fromChart {V : X.Opens} (i : ι) (hi : V ≤ U i) (a : Γ(X,V)) : sections c V :=
  ⟨fun p => (c.transition p.1 i p.2.val p.2.property.2 (p.2.property.1.trans hi) :
      Γ(X,p.2.val)) * X.presheaf.map (homOfLE p.2.property.1).op a,
    by
      constructor
      · intro j W W' hW hj h
        change X.presheaf.map (homOfLE h).op
          ((c.transition j i W hj (hW.trans hi) : Γ(X,W)) *
            X.presheaf.map (homOfLE hW).op a) = _
        rw [map_mul, c.restriction]
        congr 1
        change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
        rw [← Functor.map_comp]
        rfl
      · intro j k W hW hj hk
        change (c.transition j i W hj (hW.trans hi) : Γ(X,W)) *
            X.presheaf.map (homOfLE hW).op a =
          (c.transition j k W hj hk : Γ(X,W)) *
            ((c.transition k i W hk (hW.trans hi) : Γ(X,W)) *
              X.presheaf.map (homOfLE hW).op a)
        rw [← mul_assoc, ← Units.val_mul, c.cocycle]⟩

def chartEquiv {V : X.Opens} (i : ι) (hi : V ≤ U i) :
    sections c V ≃ₗ[Γ(X,V)] Γ(X,V) where
  toFun s := s.val ⟨i,V,le_rfl,hi⟩
  invFun := fromChart c i hi
  left_inv s := by
    apply Subtype.ext
    funext p
    change (c.transition p.1 i p.2.val p.2.property.2 (p.2.property.1.trans hi) :
      Γ(X,p.2.val)) * X.presheaf.map (homOfLE p.2.property.1).op
        (s.val ⟨i,V,le_rfl,hi⟩) = s.val p
    rw [s.property.1 i V p.2.val le_rfl hi p.2.property.1]
    exact (s.property.2 p.1 i p.2.val p.2.property.1 p.2.property.2
      (p.2.property.1.trans hi)).symm
  right_inv a := by
    change (c.transition i i V hi hi : Γ(X,V)) *
      X.presheaf.map (homOfLE (show V ≤ V from le_rfl)).op a = a
    rw [c.identity]
    simp
  map_add' _ _ := rfl
  map_smul' a s := by
    change X.presheaf.map (homOfLE (show V ≤ V from le_rfl)).op a * _ = a * _
    simp

lemma chartEquiv_restrict {V W : X.Opens} (h : V ≤ W) (i : ι) (hi : W ≤ U i)
    (s : sections c W) :
    chartEquiv c i (h.trans hi) (restrict c h s) =
      X.presheaf.map (homOfLE h).op (chartEquiv c i hi s) :=
  (s.property.1 i W V le_rfl hi h).symm

lemma chartEquiv_change {V : X.Opens} (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j)
    (s : sections c V) :
    chartEquiv c i hi s = (c.transition i j V hi hj : Γ(X,V)) * chartEquiv c j hj s :=
  s.property.2 i j V le_rfl hi hj

def openPresheafFrame (i : ι) (W : X.Opens) (hW : W ≤ U i) :
    (modulePresheafRestrict W.ι).obj (presheaf c) ≅
      (SheafOfModules.unit W.toScheme.ringCatSheaf).val :=
  (modulePresheafRestrictOpensIso W).app _ ≪≫
    PresheafOfModules.isoMk
      (fun V => (chartEquiv c i ((W.ι_image_le V.unop).trans hW)).toModuleIso)
      (fun {V V'} f => by
        ext s
        exact chartEquiv_restrict c
          (Scheme.Hom.image_mono W.ι (leOfHom f.unop)) i
          ((W.ι_image_le V.unop).trans hW) s)

def chartPresheafFrame (i : ι) :
    (modulePresheafRestrict (U i).ι).obj (presheaf c) ≅
      (SheafOfModules.unit (U i).toScheme.ringCatSheaf).val :=
  openPresheafFrame c i (U i) le_rfl

def sheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (presheaf c)

def openFrame (i : ι) (W : X.Opens) (hW : W ≤ U i) :
    (sheaf c).restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
  (moduleSheafificationRestrict W.ι).app (presheaf c) ≪≫
    (PresheafOfModules.sheafification (𝟙 W.toScheme.ringCatSheaf.obj)).mapIso
      (openPresheafFrame c i W hW) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := W.toScheme.ringCatSheaf)
      (𝟙 W.toScheme.ringCatSheaf.obj)).counit).app
      (SheafOfModules.unit W.toScheme.ringCatSheaf)

def lineBundle (hcover : ⊤ ≤ ⨆ i, U i) : LineBundle X where
  sheaf := sheaf c
  locallyRankOne x := by
    have hx : x ∈ ⨆ i, U i := hcover (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨U i,hi,⟨openFrame c i (U i) le_rfl⟩⟩

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X : Scheme}

def restrictUnit {V W : X.Opens} (h : V ≤ W) : Γ(X,W)ˣ →* Γ(X,V)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom

@[simp] lemma restrictUnit_val {V W : X.Opens} (h : V ≤ W) (a : Γ(X,W)ˣ) :
    (restrictUnit h a : Γ(X,V)) = X.presheaf.map (homOfLE h).op (a : Γ(X,W)) := rfl

@[simp] lemma restrictUnit_trans {V W Z : X.Opens}
    (h : V ≤ W) (k : W ≤ Z) (a : Γ(X,Z)ˣ) :
    restrictUnit h (restrictUnit k a) = restrictUnit (h.trans k) a := by
  apply Units.ext
  change (X.presheaf.map (homOfLE k).op ≫ X.presheaf.map (homOfLE h).op) _ = _
  rw [← Functor.map_comp]
  rfl

@[simp] lemma restrictUnit_refl (V : X.Opens) (a : Γ(X,V)ˣ) :
    restrictUnit (le_refl V) a = a := by
  apply Units.ext
  simp [restrictUnit]

variable {ι : Type} (U : ι → X.Opens)

structure PairCocycle where
  pair (i j : ι) : Γ(X,U i ⊓ U j)ˣ
  identity (i : ι) :
    restrictUnit (show U i ≤ U i ⊓ U i from le_inf le_rfl le_rfl) (pair i i) = 1
  cocycle (i j k : ι) :
    restrictUnit (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left) (pair i j) *
      restrictUnit (show (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k from
        le_inf (inf_le_left.trans inf_le_right) inf_le_right) (pair j k) =
      restrictUnit (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right) (pair i k)

variable {U}

def PairCocycle.toCocycle (g : PairCocycle U) : Cocycle U where
  transition i j W hi hj := restrictUnit (le_inf hi hj) (g.pair i j)
  restriction i j {V W} h hi hj := by
    exact congrArg Units.val (restrictUnit_trans h (le_inf hi hj) (g.pair i j))
  identity i W hi := by
    have h := congrArg (restrictUnit hi) (g.identity i)
    simpa only [map_one, restrictUnit_trans] using h
  cocycle i j k W hi hj hk := by
    have h := congrArg (restrictUnit (le_inf (le_inf hi hj) hk)) (g.cocycle i j k)
    simpa only [map_mul, restrictUnit_trans] using h

@[simp] lemma PairCocycle.toCocycle_transition (g : PairCocycle U)
    (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    g.toCocycle.transition i j W hi hj = restrictUnit (le_inf hi hj) (g.pair i j) := rfl

def PairCocycle.lineBundle (g : PairCocycle U) (hcover : ⊤ ≤ ⨆ i, U i) :
    PiExponentSeshadri.Geometry.LineBundle X :=
  LineBundleGluing.lineBundle g.toCocycle hcover

end PiExponentSeshadri.LineBundleGluing

end

end OAI
