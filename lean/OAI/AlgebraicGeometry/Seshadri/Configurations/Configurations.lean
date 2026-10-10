import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Model
import OAI.AlgebraicGeometry.Seshadri.Bertini.Derivations
import OAI.AlgebraicGeometry.Seshadri.Configurations.SmoothRationalPoints

namespace OAI


                                        
section

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open scoped TensorProduct

variable {F : Type} [Field F] [IsAlgClosed F] [Uncountable F]

omit [Uncountable F] in
lemma affine_pullback_isIntegral {A B : CommRingCat} [IsDomain A] [IsDomain B]
    (f : Spec A ⟶ Spec (CommRingCat.of F))
    (g : Spec B ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] : IsIntegral (pullback f g) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  have hft : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp
    (inferInstance : LocallyOfFiniteType (Spec.map φ))
  algebraize [φ.hom, ψ.hom]
  let : IsDomain (A ⊗[F] B) := tensorProduct_isDomain
  exact IsIntegral.of_isIso (pullbackSpecIso F A B).inv

def nonemptyAffineCover (X : Scheme) : X.OpenCover where
  I₀ := { U : X.Opens // IsAffineOpen U ∧ Nonempty U }
  X i := Spec Γ(X, i.1)
  f i := i.2.1.fromSpec
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    let i : { U : X.Opens // IsAffineOpen U ∧ Nonempty U } :=
      ⟨U, hU, ⟨⟨x, hxU⟩⟩⟩
    refine ⟨i, ?_⟩
    rw [hU.range_fromSpec]
    exact hxU

instance nonemptyAffineCover_nonempty (X : Scheme) (i : (nonemptyAffineCover X).I₀) :
    Nonempty ((nonemptyAffineCover X).X i) := by
  let : Nonempty i.1 := i.2.2
  exact Nonempty.map i.2.1.isoSpec.hom inferInstance

instance nonemptyAffineCover_integral (X : Scheme) [IsIntegral X]
    (i : (nonemptyAffineCover X).I₀) : IsIntegral ((nonemptyAffineCover X).X i) :=
  isIntegral_of_isOpenImmersion ((nonemptyAffineCover X).f i)

omit [Uncountable F] in
theorem scheme_product_isIntegral {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (CommRingCat.of F)) (g : Y ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] : IsIntegral (pullback f g) := by
  classical
  let C := Scheme.Pullback.openCoverOfLeftRight (nonemptyAffineCover X)
    (nonemptyAffineCover Y) f g
  have hInt (i : C.I₀) : IsIntegral (C.X i) := by
    change IsIntegral (pullback ((nonemptyAffineCover X).f i.1 ≫ f)
      ((nonemptyAffineCover Y).f i.2 ≫ g))
    let : Nonempty i.1.1 := i.1.2.2
    let : Nonempty i.2.1 := i.2.2.2
    let : IsOpenImmersion ((nonemptyAffineCover X).f i.1) := inferInstance
    let : LocallyOfFiniteType ((nonemptyAffineCover X).f i.1) := inferInstance
    let hfcomp : LocallyOfFiniteType ((nonemptyAffineCover X).f i.1 ≫ f) := inferInstance
    exact @affine_pullback_isIntegral F _ _ Γ(X, i.1.1) Γ(Y, i.2.1)
      inferInstance inferInstance ((nonemptyAffineCover X).f i.1 ≫ f)
      ((nonemptyAffineCover Y).f i.2 ≫ g) hfcomp
  let : ∀ i, IsReduced (C.X i) := fun i => by
    let := hInt i
    infer_instance
  let : IsReduced (pullback f g) := IsReduced.of_openCover _ C
  let x : X := Classical.ofNonempty
  let y : Y := Classical.ofNonempty
  obtain ⟨i, a, _⟩ := (nonemptyAffineCover X).exists_eq x
  obtain ⟨j, b, _⟩ := (nonemptyAffineCover Y).exists_eq y
  let c : C.I₀ := (i, j)
  let := hInt c
  have hdx : Dense (Set.range ((nonemptyAffineCover X).f i)) :=
    ((nonemptyAffineCover X).f i).isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty _)
  have hdy : Dense (Set.range ((nonemptyAffineCover Y).f j)) :=
    ((nonemptyAffineCover Y).f j).isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty _)
  have hdc : Dense (Set.range (C.f c)) := by
    change Dense (Set.range (pullback.map
      ((nonemptyAffineCover X).f i ≫ f) ((nonemptyAffineCover Y).f j ≫ g)
      f g ((nonemptyAffineCover X).f i) ((nonemptyAffineCover Y).f j)
      (𝟙 _) (Category.comp_id _) (Category.comp_id _)))
    rw [Scheme.Pullback.range_map]
    exact (hdx.preimage (pullback.fst f g).isOpenMap).inter_of_isOpen_left
      (hdy.preimage (pullback.snd f g).isOpenMap)
      (((nonemptyAffineCover X).f i).isOpenEmbedding.isOpen_range.preimage
        (pullback.fst f g).continuous)
  have hic : IsIrreducible (Set.range (C.f c)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := C.X c)).image (C.f c)
        (C.f c).continuous.continuousOn
  let : IrreducibleSpace (pullback f g : Scheme) :=
    (irreducibleSpace_def (pullback f g : Scheme)).mpr (by
      change IsIrreducible (Set.univ : Set (pullback f g : Scheme))
      rw [← hdc.closure_eq]
      exact hic.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

def powerSuccIso {C : Type*} [Category C] [HasFiniteProducts C] (X : C) (n : ℕ) :
    (∏ᶜ (fun _ : Fin (n + 1) => X)) ≅ X ⨯ (∏ᶜ (fun _ : Fin n => X)) where
  hom := prod.lift (Pi.π _ 0) (Pi.lift fun i => Pi.π _ i.succ)
  inv := Pi.lift (Fin.cases prod.fst (fun i => prod.snd ≫ Pi.π _ i))
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  inv_hom_id := by
    apply prod.hom_ext
    · simp
    · apply Pi.hom_ext
      intro i
      simp

def overPowerZeroIso {C : Type*} [Category C] [HasFiniteLimits C] {B : C}
    (X : Over B) : (∏ᶜ (fun _ : Fin 0 => X)) ≅ Over.mk (𝟙 B) where
  hom := Over.homMk (∏ᶜ (fun _ : Fin 0 => X)).hom
  inv := Pi.lift (fun i => i.elim0)
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    exact i.elim0
  inv_hom_id := Over.mkIdTerminal.hom_ext _ _

def overLeftIso {C : Type*} [Category C] {B : C} {X Y : Over B} (e : X ≅ Y) :
    X.left ≅ Y.left where
  hom := e.hom.left
  inv := e.inv.left
  hom_inv_id := by simp [← Over.comp_left]
  inv_hom_id := by simp [← Over.comp_left]

theorem scheme_power_isIntegral {F : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    (X : Over (Spec (CommRingCat.of F))) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (n : ℕ) :
    IsIntegral (∏ᶜ (fun _ : Fin n => X)).left := by
  induction n with
  | zero =>
    let : IsIntegral (Over.mk (𝟙 (Spec (CommRingCat.of F)))).left :=
      inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
    exact IsIntegral.of_isIso (overLeftIso (overPowerZeroIso X)).inv
  | succ n hn =>
    let : IsIntegral (∏ᶜ (fun _ : Fin n => X)).left := hn
    let : IsIntegral (pullback X.hom (∏ᶜ (fun _ : Fin n => X)).hom) :=
      scheme_product_isIntegral X.hom _
    let e : (∏ᶜ (fun _ : Fin (n + 1) => X)).left ≅
        pullback X.hom (∏ᶜ (fun _ : Fin n => X)).hom :=
      (overLeftIso (powerSuccIso X n)).trans
      (Over.prodLeftIsoPullback X (∏ᶜ (fun _ : Fin n => X)))
    exact IsIntegral.of_isIso e.inv

theorem scheme_power_locallyOfFiniteType {F : Type} [Field F]
    (X : Over (Spec (CommRingCat.of F))) [LocallyOfFiniteType X.hom] (n : ℕ) :
    LocallyOfFiniteType (∏ᶜ (fun _ : Fin n => X)).hom := by
  induction n with
  | zero =>
    change LocallyOfFiniteType (overLeftIso (overPowerZeroIso X)).hom
    infer_instance
  | succ n hn =>
    let e : (∏ᶜ (fun _ : Fin (n + 1) => X)).left ≅
        pullback X.hom (∏ᶜ (fun _ : Fin n => X)).hom :=
      (overLeftIso (powerSuccIso X n)).trans
      (Over.prodLeftIsoPullback X (∏ᶜ (fun _ : Fin n => X)))
    have he : (∏ᶜ (fun _ : Fin (n + 1) => X)).hom =
        e.hom ≫ pullback.fst _ _ ≫ X.hom := by
      dsimp only [e]
      simp only [Iso.trans_hom, Category.assoc,
        Over.prodLeftIsoPullback_hom_fst_assoc]
      change _ = (powerSuccIso X n).hom.left ≫
        (prod.fst : X ⨯ (∏ᶜ (fun _ : Fin n => X)) ⟶ X).left ≫ X.hom
      rw [Over.w, Over.w]
    let : LocallyOfFiniteType (∏ᶜ (fun _ : Fin n => X)).hom := hn
    rw [he]
    infer_instance

end
end MaximalSeshadri
namespace MaximalSeshadri
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

theorem scheme_rational_point_outside_countable_closed
    {F : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f]
    (Z : ℕ → Set X) (hclosed : ∀ n, IsClosed (Z n))
    (hproper : ∀ n, Z n ≠ Set.univ) :
    ∃ p : Spec (CommRingCat.of F) ⟶ X,
      p ≫ f = 𝟙 _ ∧ ∀ n, p (fieldPoint F) ∉ Z n := by
  classical
  let x : X := Classical.ofNonempty
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let A := Γ(X, U)
  let i : Spec A ⟶ X := hU.fromSpec
  let g : CommRingCat.of F ⟶ A := Spec.homEquiv (i ≫ f)
  have hg : Spec.map g = i ≫ f := Spec.homEquiv.symm_apply_apply _
  let : LocallyOfFiniteType (Spec.map g) := hg ▸ inferInstance
  have hft : g.hom.FiniteType := HasRingHomProperty.Spec_iff.mp (inferInstance : LocallyOfFiniteType (Spec.map g))
  algebraize [g.hom]
  let Z' : ℕ → Set (PrimeSpectrum A) := fun n => i ⁻¹' Z n
  have hclosed' (n : ℕ) : IsClosed (Z' n) := (hclosed n).preimage i.continuous
  have hproper' (n : ℕ) : Z' n ≠ Set.univ := by
    intro heq
    have hUZ : (U : Set X) ⊆ Z n := by
      rw [← hU.range_fromSpec]
      rintro _ ⟨a, rfl⟩
      have : a ∈ Z' n := heq ▸ Set.mem_univ a
      exact this
    have hd : Dense (U : Set X) := U.isOpen.dense ⟨x, hxU⟩
    apply hproper n
    apply Set.eq_univ_of_univ_subset
    rw [← hd.closure_eq]
    exact (hclosed n).closure_subset_iff.mpr hUZ
  obtain ⟨φ, hφ⟩ := rational_point_outside_countable_closed (F := F) Z' hclosed' hproper'
  let p := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ i
  refine ⟨p, ?_, fun n => ?_⟩
  · dsimp [p]
    rw [Category.assoc, ← hg, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    exact φ.comp_algebraMap
  · change i ((Spec.map (CommRingCat.ofHom φ.toRingHom)) (fieldPoint F)) ∉ Z n
    exact hφ n

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

theorem rationalPoint_image_injective {F : Type} [Field F]
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of F)) (o : Spec (CommRingCat.of F)) :
    Function.Injective
      (fun p : {p : Spec (CommRingCat.of F) ⟶ X // p ≫ f = 𝟙 _} => p.val o) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
  apply Subtype.ext
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective p
  obtain ⟨⟨y, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective q
  change (Spec.map φ ≫ X.fromSpecResidueField x) o =
    (Spec.map ψ ≫ X.fromSpecResidueField y) o at hpq
  have hxy : x = y := by simpa only [Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply] using hpq
  subst y
  change Spec.map φ ≫ X.fromSpecResidueField x ≫ f = 𝟙 _ at hp
  change Spec.map ψ ≫ X.fromSpecResidueField x ≫ f = 𝟙 _ at hq
  let a : CommRingCat.of F ⟶ X.residueField x :=
    Spec.homEquiv (X.fromSpecResidueField x ≫ f)
  have ha : Spec.map a = X.fromSpecResidueField x ≫ f :=
    Spec.homEquiv.symm_apply_apply _
  have hap : a ≫ φ = 𝟙 _ := by
    apply Spec.map_inj.mp
    rw [Spec.map_comp, Spec.map_id, ha]
    exact hp
  have haq : a ≫ ψ = 𝟙 _ := by
    apply Spec.map_inj.mp
    rw [Spec.map_comp, Spec.map_id, ha]
    exact hq
  have has : Function.Surjective a.hom := by
    intro z
    refine ⟨φ.hom z, φ.hom.injective ?_⟩
    exact congrArg (fun k : CommRingCat.of F ⟶ CommRingCat.of F => k.hom (φ.hom z)) hap
  have hφψ : φ = ψ := by
    ext z
    obtain ⟨c, rfl⟩ := has z
    exact (congrArg (fun k : CommRingCat.of F ⟶ CommRingCat.of F => k.hom c) hap).trans
      (congrArg (fun k : CommRingCat.of F ⟶ CommRingCat.of F => k.hom c) haq).symm
  exact congrArg (fun k => (Scheme.SpecToEquivOfField F X).symm ⟨x, k⟩) hφψ

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {F : Type} [Field F]

abbrev RationalPoint (X : Over (Spec (CommRingCat.of F))) :=
  Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ X

def rationalImage {X : Over (Spec (CommRingCat.of F))} (p : RationalPoint X) : X.left :=
  p.left (fieldPoint F)

theorem rationalImage_injective (X : Over (Spec (CommRingCat.of F))) :
    Function.Injective (rationalImage (X := X)) := by
  intro p q h
  have hh := rationalPoint_image_injective X.hom (fieldPoint F)
    (a₁ := ⟨p.left, Over.w p⟩) (a₂ := ⟨q.left, Over.w q⟩) h
  apply Over.OverMorphism.ext
  exact congrArg Subtype.val hh

def rationalTupleImage (X : Over (Spec (CommRingCat.of F))) (r : ℕ)
    (p : Fin r → RationalPoint X) : (∏ᶜ (fun _ : Fin r => X)).left :=
  (Pi.lift p).left (fieldPoint F)

lemma rationalImage_projection (X : Over (Spec (CommRingCat.of F))) (r : ℕ)
    (p : Fin r → RationalPoint X) (i : Fin r) :
    (Pi.π (fun _ : Fin r => X) i).left (rationalTupleImage X r p) =
      rationalImage (p i) := by
  change ((Pi.lift p).left ≫ (Pi.π (fun _ : Fin r => X) i).left) (fieldPoint F) = _
  rw [← Over.comp_left, Pi.lift_comp_π]
  rfl

theorem exists_distinct_rational_tuple [IsAlgClosed F] [Uncountable F]
    (X : Over (Spec (CommRingCat.of F))) [IsIntegral X.left]
    (n : ℕ) (hn : 0 < n) [SmoothOfRelativeDimension n X.hom] (r : ℕ) :
    ∃ p : Fin r → RationalPoint X, Function.Injective (fun i => rationalImage (p i)) := by
  classical
  have hu := smooth_scheme_uncountable_rational_points X.hom n hn
  let R := Set.range fun p : {p : Spec (CommRingCat.of F) ⟶ X.left // p ≫ X.hom = 𝟙 _} =>
    p.val (fieldPoint F)
  let : Infinite R := (show R.Infinite from fun h => hu h.countable).to_subtype
  let b : ℕ ↪ R := Infinite.natEmbedding R
  choose p hp using (fun k : ℕ => (b k).property)
  refine ⟨fun i => Over.homMk (p i.val).val (p i.val).property, ?_⟩
  intro i j h
  apply Fin.val_injective
  apply b.injective
  apply Subtype.ext
  change (p i.val).val (fieldPoint F) = (p j.val).val (fieldPoint F) at h
  simpa only [hp] using h

def pairProjection (X : Over (Spec (CommRingCat.of F))) (r : ℕ) (i j : Fin r) :
    (∏ᶜ (fun _ : Fin r => X)).left ⟶ pullback X.hom X.hom :=
  pullback.lift (Pi.π (fun _ : Fin r => X) i).left
    (Pi.π (fun _ : Fin r => X) j).left ((Over.w _).trans (Over.w _).symm)

def pairDiagonal (X : Over (Spec (CommRingCat.of F))) (r : ℕ) (i j : Fin r) :
    Set (∏ᶜ (fun _ : Fin r => X)).left :=
  pairProjection X r i j ⁻¹' Set.range (pullback.diagonal X.hom)

lemma pairDiagonal_closed (X : Over (Spec (CommRingCat.of F))) [IsSeparated X.hom]
    (r : ℕ) (i j : Fin r) : IsClosed (pairDiagonal X r i j) := by
  exact (pullback.diagonal X.hom).isClosedEmbedding.isClosed_range.preimage
    (pairProjection X r i j).continuous

lemma pairDiagonal_tuple_iff (X : Over (Spec (CommRingCat.of F))) (r : ℕ)
    (p : Fin r → RationalPoint X) (i j : Fin r) :
    rationalTupleImage X r p ∈ pairDiagonal X r i j ↔
      rationalImage (p i) = rationalImage (p j) := by
  constructor
  · rintro ⟨x, hx⟩
    have hi := congrArg (pullback.fst X.hom X.hom) hx
    have hj := congrArg (pullback.snd X.hom X.hom) hx
    have hfst : (pullback.fst X.hom X.hom) (pairProjection X r i j
        (rationalTupleImage X r p)) = rationalImage (p i) := by
      change (pairProjection X r i j ≫ pullback.fst X.hom X.hom)
        (rationalTupleImage X r p) = _
      simp only [pairProjection, pullback.lift_fst, rationalImage_projection]
    have hsnd : (pullback.snd X.hom X.hom) (pairProjection X r i j
        (rationalTupleImage X r p)) = rationalImage (p j) := by
      change (pairProjection X r i j ≫ pullback.snd X.hom X.hom)
        (rationalTupleImage X r p) = _
      simp only [pairProjection, pullback.lift_snd, rationalImage_projection]
    have hid : (pullback.fst X.hom X.hom) ((pullback.diagonal X.hom) x) = x := by
      change (pullback.diagonal X.hom ≫ pullback.fst X.hom X.hom) x = x
      simp
    have hjd : (pullback.snd X.hom X.hom) ((pullback.diagonal X.hom) x) = x := by
      change (pullback.diagonal X.hom ≫ pullback.snd X.hom X.hom) x = x
      simp
    exact (hfst.symm.trans (hi.symm.trans hid)).trans (hjd.symm.trans (hj.trans hsnd))
  · intro h
    have hp := rationalImage_injective X h
    refine ⟨rationalImage (p i), ?_⟩
    have hm : (Pi.lift p).left ≫ pairProjection X r i j =
        (p i).left ≫ pullback.diagonal X.hom := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pairProjection, pullback.lift_fst,
          pullback.diagonal_fst, Category.comp_id, ← Over.comp_left, Pi.lift_comp_π]
      · simp only [Category.assoc, pairProjection, pullback.lift_snd,
          pullback.diagonal_snd, Category.comp_id, ← Over.comp_left, Pi.lift_comp_π, hp]
    exact (congrArg (fun f : Spec (CommRingCat.of F) ⟶ pullback X.hom X.hom =>
      f (fieldPoint F)) hm).symm

def collisionLocus (X : Over (Spec (CommRingCat.of F))) (r : ℕ) :
    Set (∏ᶜ (fun _ : Fin r => X)).left :=
  ⋃ ij : {ij : Fin r × Fin r // ij.1 ≠ ij.2}, pairDiagonal X r ij.val.1 ij.val.2

lemma collisionLocus_closed (X : Over (Spec (CommRingCat.of F))) [IsSeparated X.hom]
    (r : ℕ) : IsClosed (collisionLocus X r) := by
  exact isClosed_iUnion_of_finite (fun ij => pairDiagonal_closed X r ij.val.1 ij.val.2)

lemma tuple_not_collision_iff (X : Over (Spec (CommRingCat.of F))) (r : ℕ)
    (p : Fin r → RationalPoint X) :
    rationalTupleImage X r p ∉ collisionLocus X r ↔
      Function.Injective (fun i => rationalImage (p i)) := by
  constructor
  · intro h i j hij
    by_contra hne
    apply h
    exact Set.mem_iUnion.mpr ⟨⟨(i, j), hne⟩,
      (pairDiagonal_tuple_iff X r p i j).mpr hij⟩
  · intro h hbad
    obtain ⟨⟨⟨i, j⟩, hne⟩, hij⟩ := Set.mem_iUnion.mp hbad
    exact hne (h ((pairDiagonal_tuple_iff X r p i j).mp hij))

lemma collisionLocus_proper [IsAlgClosed F] [Uncountable F]
    (X : Over (Spec (CommRingCat.of F))) [IsIntegral X.left]
    (n : ℕ) (hn : 0 < n) [SmoothOfRelativeDimension n X.hom] (r : ℕ) :
    collisionLocus X r ≠ Set.univ := by
  obtain ⟨p, hp⟩ := exists_distinct_rational_tuple X n hn r
  intro heq
  exact (tuple_not_collision_iff X r p).mpr hp (heq ▸ Set.mem_univ _)

lemma rationalTupleImage_projections (X : Over (Spec (CommRingCat.of F))) (r : ℕ)
    (q : RationalPoint (∏ᶜ (fun _ : Fin r => X))) :
    rationalTupleImage X r (fun i => q ≫ Pi.π _ i) = rationalImage q := by
  have heq : Pi.lift (fun i => q ≫ Pi.π (fun _ : Fin r => X) i) = q := by
    apply Pi.hom_ext
    intro i
    simp
  exact congrArg (fun p : RationalPoint (∏ᶜ (fun _ : Fin r => X)) =>
    p.left (fieldPoint F)) heq

def SchemeConfiguration (X : Over (Spec (CommRingCat.of F))) (r : ℕ) :=
  {p : Fin r → RationalPoint X // Function.Injective (fun i => rationalImage (p i))}

instance schemeConfigurationTopology (X : Over (Spec (CommRingCat.of F))) (r : ℕ) :
    TopologicalSpace (SchemeConfiguration X r) :=
  TopologicalSpace.induced (fun p => rationalTupleImage X r p.val) inferInstance

theorem configuration_outside_countable_closed [IsAlgClosed F] [Uncountable F]
    (X : Over (Spec (CommRingCat.of F))) [IsIntegral X.left] [IsSeparated X.hom]
    (n : ℕ) (hn : 0 < n) [SmoothOfRelativeDimension n X.hom] (r : ℕ)
    (Z : ℕ → Set (SchemeConfiguration X r)) (hclosed : ∀ k, IsClosed (Z k))
    (hproper : ∀ k, Z k ≠ Set.univ) :
    ∃ p : SchemeConfiguration X r, ∀ k, p ∉ Z k := by
  classical
  have hex (k : ℕ) : ∃ W : Set (∏ᶜ (fun _ : Fin r => X)).left,
      IsClosed W ∧ (fun p : SchemeConfiguration X r => rationalTupleImage X r p.val) ⁻¹' W = Z k :=
    isClosed_induced_iff.mp (hclosed k)
  choose W hW hWZ using hex
  have hWP (k : ℕ) : W k ≠ Set.univ := by
    intro heq
    apply hproper k
    rw [← hWZ k, heq]
    exact Set.preimage_univ
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth n X.hom
  let Y := ∏ᶜ (fun _ : Fin r => X)
  let : IsIntegral Y.left := scheme_power_isIntegral X r
  let : LocallyOfFiniteType Y.hom := scheme_power_locallyOfFiniteType X r
  let bad : ℕ → Set Y.left := fun k => Nat.casesOn k (collisionLocus X r) W
  have hbc (k : ℕ) : IsClosed (bad k) := by
    cases k with
    | zero => exact collisionLocus_closed X r
    | succ k => exact hW k
  have hbp (k : ℕ) : bad k ≠ Set.univ := by
    cases k with
    | zero => exact collisionLocus_proper X n hn r
    | succ k => exact hWP k
  obtain ⟨q, hq, ha⟩ := scheme_rational_point_outside_countable_closed Y.hom bad hbc hbp
  let q' : RationalPoint Y := Over.homMk q hq
  let p : Fin r → RationalPoint X := fun i => q' ≫ Pi.π _ i
  have hpi : rationalTupleImage X r p = q (fieldPoint F) :=
    rationalTupleImage_projections X r q'
  have hp : Function.Injective (fun i => rationalImage (p i)) := by
    apply (tuple_not_collision_iff X r p).mp
    rw [hpi]
    exact ha 0
  refine ⟨⟨p, hp⟩, fun k hk => ?_⟩
  apply ha (k + 1)
  change q (fieldPoint F) ∈ W k
  rw [← hpi]
  have hmem : (⟨p, hp⟩ : SchemeConfiguration X r) ∈
      (fun p : SchemeConfiguration X r => rationalTupleImage X r p.val) ⁻¹' W k := by
    rw [hWZ k]
    exact hk
  exact hmem

end
end MaximalSeshadri
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

instance complexUncountable : Uncountable ℂ := by
  apply not_countable_iff.mp
  intro h
  let := h
  exact not_countable Complex.ofReal_injective.countable

instance projectiveSpaceToSpec_separated (N : ℕ) : IsSeparated (projectiveSpaceToSpec N) := by
  unfold projectiveSpaceToSpec
  exact IsSeparated.stableUnderComposition.comp_mem _ _ (Proj.isSeparated _) inferInstance

instance Surface.separated (S : Surface) : IsSeparated S.structureMap := by
  rw [← S.overComplex]
  exact IsSeparated.stableUnderComposition.comp_mem _ _ inferInstance inferInstance

lemma configurationTopology_eq (S : Surface) (r : ℕ) :
    configurationTopology S r =
      schemeConfigurationTopology (Over.mk S.structureMap) r := by
  unfold configurationTopology schemeConfigurationTopology
  change TopologicalSpace.induced Subtype.val
      (TopologicalSpace.induced (tupleImage S r) inferInstance) = _
  rw [induced_compose]
  rfl

theorem surface_configuration_outside_countable_closed
    (S : Surface) (r : ℕ) (Z : ℕ → Set (Configuration S r))
    (hclosed : ∀ k, IsClosed (Z k)) (hproper : ∀ k, Z k ≠ Set.univ) :
    ∃ p : Configuration S r, ∀ k, p ∉ Z k := by
  let : IsIntegral (Over.mk S.structureMap).left := S.integral
  let : SmoothOfRelativeDimension 2 (Over.mk S.structureMap).hom := S.smooth
  let : IsSeparated (Over.mk S.structureMap).hom := S.separated
  have ht := configurationTopology_eq S r
  let T : ℕ → Set (SchemeConfiguration (Over.mk S.structureMap) r) := Z
  have hc : ∀ k, @IsClosed _ (schemeConfigurationTopology (Over.mk S.structureMap) r) (T k) := by
    intro k
    rw [← ht]
    exact hclosed k
  exact configuration_outside_countable_closed (Over.mk S.structureMap) 2 (by norm_num) r T hc hproper

end
end MaximalSeshadri.Geometry

end

end OAI
