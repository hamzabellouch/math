import OAI.AlgebraicTopology.IntegralHomology.Equivalence
import Mathlib.Analysis.Complex.Convex

namespace OAI

noncomputable section

namespace Kaplansky

/-! Product-pair homology, pair homotopies, and diagonal normalization. -/

section
open CategoryTheory Limits ContinuousMap
variable {B V : Type} [TopologicalSpace B] [TopologicalSpace V]

/-- Projection from a product with an actually contractible base, keeping
the projection itself as the forward map. -/
def contractibleProductProjection [ContractibleSpace B] (V : Type) [TopologicalSpace V] :
    B × V ≃ₕ V := by
  let e := Classical.choice (ContractibleSpace.hequiv_unit B)
  exact (e.prodCongr (ContinuousMap.HomotopyEquiv.refl V)).trans
    (Homeomorph.uniqueProd Unit V).toHomotopyEquiv

theorem contractibleProductProjection_apply [ContractibleSpace B] (z : B × V) :
    (contractibleProductProjection (B := B) V).toFun z = z.2 := rfl

/-- The punctured trivial-bundle subspace really is the product of the
base and the punctured model. -/
def productSubspaceHomeomorph (W : Set V) :
    ({z : B × V | z.2 ∈ W} : Set (B × V)) ≃ₜ B × W where
  toFun z := (z.1.1, ⟨z.1.2, z.2⟩)
  invFun z := ⟨(z.1, z.2.1), z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def productPairProjection (W : Set V) (n : ℕ) :=
  relativeHomologyMap (subspaceInclusion {z : B × V | z.2 ∈ W})
    (subspaceInclusion W)
    (subspaceMap _ _ ⟨Prod.snd, continuous_snd⟩ (fun _ h => h))
    (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (by rfl) n

/-- Genuine relative homology normalization for a trivial bundle over any
contractible base, with no homology or orientation assumption. -/
theorem productPairProjection_isIso [ContractibleSpace B] (W : Set V) (n : ℕ) :
    IsIso (productPairProjection (B := B) W n) := by
  let a := (productSubspaceHomeomorph (B := B) W).toHomotopyEquiv.trans
    (contractibleProductProjection (B := B) W)
  exact relativeHomologyMap_isIso_of_equivalences _ _ a
    (contractibleProductProjection (B := B) V) (by rfl) n

def productPairProjectionIso [ContractibleSpace B] (W : Set V) (n : ℕ) :=
  @asIso _ _ _ _ (productPairProjection (B := B) W n) (productPairProjection_isIso W n)

/-- Composition of homeomorphisms agrees with composition on relative homology. -/
theorem relativeHomologyHomeomorphIso_trans_hom
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (f : Y ≃ₜ Z) (U : Set X) (V : Set Y) (W : Set Z)
    (he : ∀ x, x ∈ U ↔ e x ∈ V) (hf : ∀ y, y ∈ V ↔ f y ∈ W) (n : ℕ) :
    (relativeHomologyHomeomorphIso (e.trans f) U W
      (fun x => (he x).trans (hf (e x))) n).hom =
      (relativeHomologyHomeomorphIso e U V he n).hom ≫
        (relativeHomologyHomeomorphIso f V W hf n).hom := by
  simp only [relativeHomologyHomeomorphIso_hom]
  rw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

/-- Restricting product coordinates commutes with projection to relative fiber homology. -/
theorem productPairNormalization_restrict
    {X Y A B V : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace V] [Zero V]
    (U : Set X) (W : Set Y) (i : C(X,Y)) (hi : Set.MapsTo i U W)
    (e : X ≃ₜ A × V) (f : Y ≃ₜ B × V)
    (he : ∀ x, x ∈ U ↔ (e x).2 ≠ 0) (hf : ∀ y, y ∈ W ↔ (f y).2 ≠ 0)
    (hcoords : ∀ x, (f (i x)).2 = (e x).2) (n : ℕ) :
    relativeHomologyMap (subspaceInclusion U) (subspaceInclusion W)
        (subspaceMap U W i hi) (TopCat.ofHom i) (subspaceMap_square U W i hi) n ≫
      ((relativeHomologyHomeomorphIso f W {z | z.2 ≠ 0} hf n).hom ≫
        productPairProjection (B := B) ({0}ᶜ : Set V) n) =
      (relativeHomologyHomeomorphIso e U {z | z.2 ≠ 0} he n).hom ≫
        productPairProjection (B := A) ({0}ᶜ : Set V) n := by
  simp only [relativeHomologyHomeomorphIso_hom]
  unfold productPairProjection
  erw [← Category.assoc, relativeHomologyMap_comp, relativeHomologyMap_comp,
    relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  ext x : 1
  exact hcoords x

end

section
open CategoryTheory ContinuousMap
section
variable {B V : Type} [TopologicalSpace B] [TopologicalSpace V]

/-- Inclusion of one genuine fiber of a product pair. -/
def productPairFiberMap (b : B) (W : Set V) (n : ℕ) :=
  relativeHomologyMap (subspaceInclusion W)
    (subspaceInclusion {z : B × V | z.2 ∈ W})
    (subspaceMap _ _ ⟨fun v => (b,v), continuous_const.prodMk continuous_id⟩ (fun _ h => h))
    (TopCat.ofHom ⟨fun v => (b,v), continuous_const.prodMk continuous_id⟩) (by rfl) n

/-- The fiber inclusion is split injective over ANY base containing that point. -/
theorem productPairFiberMap_projection (b : B) (W : Set V) (n : ℕ) :
    productPairFiberMap b W n ≫ productPairProjection W n = 𝟙 _ := by
  unfold productPairFiberMap productPairProjection
  erw [relativeHomologyMap_comp, ← relativeHomologyMap_id (subspaceInclusion W) n]
  apply relativeHomologyMap_congr_ambient
  rfl

theorem productPairFiberMap_mono (b : B) (W : Set V) (n : ℕ) :
    Mono (productPairFiberMap b W n) := by
  have : Mono (productPairFiberMap b W n ≫ productPairProjection W n) := by
    rw [productPairFiberMap_projection]
    infer_instance
  exact mono_of_mono (productPairFiberMap b W n) (productPairProjection W n)

/-- Over a contractible base the actual inclusion is the inverse normalization. -/
theorem productPairFiberMap_eq_inv [ContractibleSpace B] (b : B) (W : Set V) (n : ℕ) :
    productPairFiberMap b W n = (productPairProjectionIso (B := B) W n).inv := by
  have := productPairProjection_isIso (B := B) W n
  apply (cancel_mono (productPairProjection (B := B) W n)).mp
  rw [productPairFiberMap_projection]
  exact (productPairProjectionIso (B := B) W n).inv_hom_id.symm

theorem productPairFiberMap_eq [ContractibleSpace B] (b c : B) (W : Set V) (n : ℕ) :
    productPairFiberMap b W n = productPairFiberMap c W n := by
  rw [productPairFiberMap_eq_inv, productPairFiberMap_eq_inv]

end

open CategoryTheory ContinuousMap
open scoped unitInterval
section
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homotopy that carries the removed subspace into the removed subspace
at EVERY time gives equal maps on relative singular homology. The proof uses
the actual cylinder projection and its two equal inverse inclusions. -/
theorem relativeHomologyMap_homotopy (U : Set X) (V : Set Y)
    {f g : C(X,Y)} (hf : Set.MapsTo f U V) (hg : Set.MapsTo g U V)
    (H : Homotopy f g) (hH : ∀ t : I, ∀ x ∈ U, H (t,x) ∈ V) (n : ℕ) :
    relativeHomologyMap (subspaceInclusion U) (subspaceInclusion V)
      (subspaceMap U V f hf) (TopCat.ofHom f) (by rfl) n =
    relativeHomologyMap (subspaceInclusion U) (subspaceInclusion V)
      (subspaceMap U V g hg) (TopCat.ofHom g) (by rfl) n := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let h := relativeHomologyMap (subspaceInclusion {z : I × X | z.2 ∈ U})
    (subspaceInclusion V)
    (subspaceMap _ _ H.toContinuousMap (fun z hz => hH z.1 z.2 hz))
    (TopCat.ofHom H.toContinuousMap) (by rfl) n
  have endpoint (t : I) (k : C(X,Y)) (hk : Set.MapsTo k U V)
      (he : ∀ x, H (t,x) = k x) :
      productPairFiberMap t U n ≫ h =
        relativeHomologyMap (subspaceInclusion U) (subspaceInclusion V)
          (subspaceMap U V k hk) (TopCat.ofHom k) (by rfl) n := by
    unfold productPairFiberMap
    change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n = _
    erw [relativeHomologyMap_comp]
    apply relativeHomologyMap_congr_ambient
    ext x : 1
    exact he x
  rw [← endpoint 0 f hf (H.apply_zero), ← endpoint 1 g hg (H.apply_one),
    productPairFiberMap_eq (0 : I) 1 U n]

/-- Fiber inclusions agree along any actual path in the base. -/
theorem productPairFiberMap_eq_of_joined {B V : Type} [TopologicalSpace B]
    [TopologicalSpace V] {b c : B} (hbc : Joined b c) (W : Set V) (n : ℕ) :
    productPairFiberMap b W n = productPairFiberMap c W n := by
  obtain ⟨γ⟩ := hbc
  let H : Homotopy
      (⟨fun v : V => (b,v), continuous_const.prodMk continuous_id⟩ : C(V,B × V))
      ⟨fun v => (c,v), continuous_const.prodMk continuous_id⟩ :=
    { toFun := fun z => (γ z.1,z.2)
      continuous_toFun := (γ.continuous.comp continuous_fst).prodMk continuous_snd
      map_zero_left := fun _ => by simp
      map_one_left := fun _ => by simp }
  exact relativeHomologyMap_homotopy W {z : B × V | z.2 ∈ W}
    (fun _ h => h) (fun _ h => h) H (fun _ _ h => h) n

end

end

section
open CategoryTheory ContinuousMap
open scoped unitInterval
variable {ι : Type}

/-- Complex diagonal coordinate change with every multiplier invertible. -/
def complexDiagonalMap (a : ι → ℂˣ) : C((ι → ℂ),(ι → ℂ)) :=
  ⟨fun v i => (a i : ℂ) * v i, continuous_pi (fun i => continuous_const.mul (continuous_apply i))⟩

theorem complexDiagonalMap_nonzero (a : ι → ℂˣ) :
    Set.MapsTo (complexDiagonalMap a) ({0}ᶜ : Set (ι → ℂ)) {0}ᶜ := by
  intro v hv he
  apply hv
  funext i
  have h : (a i : ℂ) * v i = 0 := congrFun he i
  exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero (a i))

/-- A path through complex units supplies a genuine nonzero-preserving
homotopy to the identity; no determinant-to-degree assertion is assumed. -/
def complexDiagonalHomotopy (a : ι → ℂˣ) :
    Homotopy (complexDiagonalMap a) (ContinuousMap.id (ι → ℂ)) := by
  let γ : Path a (fun _ => (1 : ℂˣ)) :=
    Classical.choice (PathConnectedSpace.joined a (fun _ => (1 : ℂˣ)))
  exact
    { toFun := fun z i => (γ z.1 i : ℂ) * z.2 i
      continuous_toFun := continuous_pi (fun i =>
        (Units.continuous_val.comp ((continuous_apply i).comp
          (γ.continuous.comp continuous_fst))).mul ((continuous_apply i).comp continuous_snd))
      map_zero_left := fun v => by ext i; simp [complexDiagonalMap]
      map_one_left := fun v => by ext i; simp }

theorem complexDiagonalHomotopy_nonzero (a : ι → ℂˣ) :
    ∀ t : I, ∀ v ∈ ({0}ᶜ : Set (ι → ℂ)), complexDiagonalHomotopy a (t,v) ∈ ({0}ᶜ : Set (ι → ℂ)) := by
  intro t v hv
  exact complexDiagonalMap_nonzero _ hv

def complexDiagonalRelativeMap (a : ι → ℂˣ) (n : ℕ) :=
  relativeHomologyMap (subspaceInclusion ({0}ᶜ : Set (ι → ℂ)))
    (subspaceInclusion ({0}ᶜ : Set (ι → ℂ)))
    (subspaceMap _ _ (complexDiagonalMap a) (complexDiagonalMap_nonzero a))
    (TopCat.ofHom (complexDiagonalMap a)) (by rfl) n

/-- Every invertible complex diagonal change acts as the identity on actual
integral local relative homology, in every degree. -/
theorem complexDiagonalRelativeMap_eq_id (a : ι → ℂˣ) (n : ℕ) :
    complexDiagonalRelativeMap a n = 𝟙 _ := by
  have h := relativeHomologyMap_homotopy ({0}ᶜ : Set (ι → ℂ)) {0}ᶜ
    (complexDiagonalMap_nonzero a) (fun _ h => h)
    (complexDiagonalHomotopy a) (complexDiagonalHomotopy_nonzero a) n
  change complexDiagonalRelativeMap a n = _ at h
  rw [h, ← relativeHomologyMap_id (subspaceInclusion ({0}ᶜ : Set (ι → ℂ))) n]
  apply relativeHomologyMap_congr_ambient
  rfl

end

open CategoryTheory ContinuousMap
section
variable {B ι : Type} [TopologicalSpace B]

/-- A map from a product pair to its fiber pair. -/
def productPairCoordinateMap (f : C(B × (ι → ℂ),(ι → ℂ)))
    (hf : ∀ z, z.2 ≠ 0 → f z ≠ 0) (n : ℕ) :=
  relativeHomologyMap (subspaceInclusion {z : B × (ι → ℂ) | z.2 ≠ 0})
    (subspaceInclusion ({0}ᶜ : Set (ι → ℂ)))
    (subspaceMap _ _ f (fun z hz => hf z hz)) (TopCat.ofHom f) (by rfl) n

/-- Over an actually contractible base, checking one fiber suffices. An
invertible complex diagonal change there preserves the full normalization.
The map away from that fiber may vary arbitrarily and need not be linear. -/
theorem productPairCoordinateMap_eq_projection [ContractibleSpace B]
    (f : C(B × (ι → ℂ),(ι → ℂ))) (hf : ∀ z, z.2 ≠ 0 → f z ≠ 0)
    (b : B) (a : ι → ℂˣ) (he : ∀ v, f (b,v) = complexDiagonalMap a v) (n : ℕ) :
    productPairCoordinateMap f hf n =
      productPairProjection (B := B) ({0}ᶜ : Set (ι → ℂ)) n := by
  have : IsIso (productPairFiberMap b ({0}ᶜ : Set (ι → ℂ)) n) := by
    rw [productPairFiberMap_eq_inv]
    infer_instance
  apply (cancel_epi (productPairFiberMap b ({0}ᶜ : Set (ι → ℂ)) n)).mp
  rw [productPairFiberMap_projection]
  have hc : productPairFiberMap b ({0}ᶜ : Set (ι → ℂ)) n ≫
      productPairCoordinateMap f hf n = complexDiagonalRelativeMap a n := by
    unfold productPairFiberMap productPairCoordinateMap complexDiagonalRelativeMap
    erw [relativeHomologyMap_comp]
    apply relativeHomologyMap_congr_ambient
    ext v : 1
    exact he v
  rw [hc, complexDiagonalRelativeMap_eq_id]

/-- The unit comparing two genuine complex coordinates on a line. -/
def complexLineCoordinateUnit {L : Type} [AddCommGroup L] [Module ℂ L]
    (e f : L ≃ₗ[ℂ] ℂ) : ℂˣ :=
  Units.mk0 (f (e.symm 1)) (by
    intro h
    have he := f.injective (h.trans (map_zero f).symm)
    have hz := congrArg e he
    simp at hz)

theorem complexLineCoordinate_change {L : Type} [AddCommGroup L] [Module ℂ L]
    (e f : L ≃ₗ[ℂ] ℂ) (z : ℂ) :
    f (e.symm z) = (complexLineCoordinateUnit e f : ℂ) * z := by
  have h : e.symm z = z • e.symm 1 := by
    rw [← map_smul]
    simp
  rw [h, map_smul]
  change z * f (e.symm 1) = f (e.symm 1) * z
  exact mul_comm _ _

end

end Kaplansky

end

end OAI
