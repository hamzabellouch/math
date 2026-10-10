import OAI.NumberTheory.PiExponent.Approximation.SectionOpens
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
variable {A R σ : Type u} [CommRing A] [CommRing R] [SetLike σ A]
  [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
  (f : A →+* R)

def evalAway (s : A) (hs : IsUnit (f s)) : Away 𝒜 s →+* R :=
  (IsLocalization.Away.lift s hs : Localization.Away s →+* R).comp
    (algebraMap (Away 𝒜 s) (Localization.Away s))

lemma evalAway_val (s : A) (hs : IsUnit (f s)) (x : Away 𝒜 s) :
    evalAway f s hs x = IsLocalization.Away.lift s hs x.val := rfl

lemma evalAway_transition {s t : A} {d : ℕ} (ht : t ∈ 𝒜 d)
    (hs : IsUnit (f s)) (hst : IsUnit (f (s * t))) :
    (evalAway f (s * t) hst).comp (awayMap 𝒜 ht rfl) = evalAway f s hs := by
  have hunit : IsUnit (algebraMap A (Localization.Away (s * t)) s) :=
    IsLocalization.Away.isUnit_of_dvd (s * t) (dvd_mul_right s t)
  have H : (IsLocalization.Away.lift (s * t) hst : Localization.Away (s * t) →+* R).comp
      (Localization.awayLift (algebraMap A (Localization.Away (s * t))) s hunit) =
      (IsLocalization.Away.lift s hs : Localization.Away s →+* R) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    simp
  apply RingHom.ext
  intro x
  simpa only [RingHom.comp_apply, evalAway_val, val_awayMap] using RingHom.congr_fun H x.val

lemma evalAway_natural {T : Type u} [CommRing T] (g : R →+* T)
    (s : A) (hs : IsUnit (f s)) :
    g.comp (evalAway (𝒜 := 𝒜) f s hs) = evalAway (g.comp f) s (hs.map g) := by
  have H : g.comp (IsLocalization.Away.lift s hs : Localization.Away s →+* R) =
      (IsLocalization.Away.lift (g := g.comp f) s (hs.map g) : Localization.Away s →+* T) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    simp
  exact congrArg (fun h : Localization.Away s →+* T =>
    h.comp (algebraMap (Away 𝒜 s) (Localization.Away s))) H

lemma evalAway_mk_clear {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hu : IsUnit (f s))
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    evalAway f s hu (Away.mk 𝒜 hs n a ha) * f s ^ n = f a := by
  rw [evalAway_val, Away.val_mk, Localization.mk_eq_mk']
  have H := IsLocalization.mk'_spec (Localization.Away s) a
    (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s)
  apply_fun (IsLocalization.Away.lift s hu : Localization.Away s →+* R) at H
  simpa only [map_mul, IsLocalization.Away.lift_eq, map_pow] using H

lemma evalAway_scale {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hu : IsUnit (f s))
    (g : A →+* R) (hv : IsUnit (g s)) (c : Rˣ)
    (hscale : ∀ n a, a ∈ 𝒜 n → g a = (c : R) ^ n * f a) :
    evalAway (𝒜 := 𝒜) f s hu = evalAway g s hv := by
  apply RingHom.ext
  intro x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
  apply (hv.pow n).mul_right_cancel
  have Hf := evalAway_mk_clear f hs hu n a ha
  have Hg := evalAway_mk_clear g hs hv n a ha
  rw [Hg, hscale d s hs, hscale _ a ha, mul_pow, ← pow_mul]
  rw [smul_eq_mul, Nat.mul_comm n d]
  calc
    _ = (c : R) ^ (d * n) * (evalAway f s hu (Away.mk 𝒜 hs n a ha) * f s ^ n) := by ring
    _ = _ := by rw [Hf]

def fromUnitCoordinate {s : A} {d : ℕ} (hd : 0 < d) (hs : s ∈ 𝒜 d)
    (hu : IsUnit (f s)) : Spec (CommRingCat.of R) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (evalAway f s hu)) ≫ Proj.awayι 𝒜 s hs hd

lemma fromUnitCoordinate_mul {s t : A} {d e : ℕ} (hd : 0 < d)
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hu : IsUnit (f s))
    (hut : IsUnit (f (s * t))) :
    fromUnitCoordinate f hd hs hu =
      fromUnitCoordinate f (Nat.add_pos_left hd e) (SetLike.mul_mem_graded hs ht) hut := by
  unfold fromUnitCoordinate
  rw [← Proj.SpecMap_awayMap_awayι 𝒜 hs hd ht rfl, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, evalAway_transition f ht hu hut]

@[reassoc]
lemma fromUnitCoordinate_natural {T : Type u} [CommRing T] (g : R →+* T)
    {s : A} {d : ℕ} (hd : 0 < d) (hs : s ∈ 𝒜 d) (hu : IsUnit (f s)) :
    Spec.map (CommRingCat.ofHom g) ≫ fromUnitCoordinate f hd hs hu =
      fromUnitCoordinate (g.comp f) hd hs (hu.map g) := by
  unfold fromUnitCoordinate
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, evalAway_natural]

lemma fromUnitCoordinate_scale {s : A} {d : ℕ} (hd : 0 < d)
    (hs : s ∈ 𝒜 d) (hu : IsUnit (f s)) (g : A →+* R) (hv : IsUnit (g s))
    (c : Rˣ) (hscale : ∀ n a, a ∈ 𝒜 n → g a = (c : R) ^ n * f a) :
    fromUnitCoordinate f hd hs hu = fromUnitCoordinate g hd hs hv := by
  unfold fromUnitCoordinate
  rw [evalAway_scale f hs hu g hv c hscale]

lemma fromUnitCoordinate_preimage {s t : A} {e : ℕ} (hs : s ∈ 𝒜 1)
    (hu : IsUnit (f s)) (hsone : f s = 1) (he : 0 < e) (ht : t ∈ 𝒜 e) :
    fromUnitCoordinate f (by decide) hs hu ⁻¹ᵁ Proj.basicOpen 𝒜 t =
      PrimeSpectrum.basicOpen (f t) := by
  rw [fromUnitCoordinate, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜 hs (by decide) ht he, SpecMap_preimage_basicOpen]
  congr 1
  change evalAway f s hu (Away.isLocalizationElem hs ht) = f t
  have H := evalAway_mk_clear f hs hu e (t ^ 1)
    (show t ^ 1 ∈ 𝒜 (e • 1) from by simpa using ht)
  simpa only [Away.isLocalizationElem, hsone, one_pow, mul_one, pow_one] using H

theorem fromUnitCoordinate_eq {s t : A} {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hu : IsUnit (f s)) (hv : IsUnit (f t)) :
    fromUnitCoordinate f hd hs hu = fromUnitCoordinate f he ht hv := by
  have huv : IsUnit (f (s * t)) := by rw [map_mul]; exact hu.mul hv
  have hvu : IsUnit (f (t * s)) := by rw [map_mul]; exact hv.mul hu
  rw [fromUnitCoordinate_mul f hd hs ht hu huv,
    fromUnitCoordinate_mul f he ht hs hv hvu]
  congr 1 <;> ac_rfl

end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coordinates_X_mem (i : σ) : MvPolynomial.X i ∈ homogeneousSubmodule σ K 1 :=
  isHomogeneous_X K i

def coordinatesMap (X : Scheme.{u}) (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤))
    (i : σ) (hi : a i = 1) : X ⟶ Proj (homogeneousSubmodule σ K) :=
  X.toSpecΓ ≫ fromUnitCoordinate (eval₂Hom k a) (by decide)
    (coordinates_X_mem (K := K) i) (by simpa only [eval₂Hom_X', hi] using isUnit_one)

lemma coordinates_eval_natural {R T : Type u} [CommRing R] [CommRing T]
    (g : R →+* T) (k : K →+* R) (a : σ → R) :
    g.comp (eval₂Hom k a) = eval₂Hom (g.comp k) (fun j => g (a j)) := by
  apply MvPolynomial.ringHom_ext <;> intro j <;> simp

@[reassoc]
lemma coordinatesMap_natural {X Y : Scheme.{u}} (φ : Y ⟶ X)
    (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) :
    φ ≫ coordinatesMap X k a i hi =
      coordinatesMap Y (φ.appTop.hom.comp k) (fun j => φ.appTop (a j)) i
        (by simp only [hi, map_one]) := by
  unfold coordinatesMap
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ]
  congr 1
  change Spec.map (CommRingCat.ofHom φ.appTop.hom) ≫ _ = _
  rw [fromUnitCoordinate_natural]
  congr 1
  exact coordinates_eval_natural φ.appTop.hom k a

lemma coordinatesMap_scale (X : Scheme.{u}) (k : K →+* Γ(X, ⊤))
    (a b : σ → Γ(X, ⊤)) (i j : σ) (hi : a i = 1) (hj : b j = 1)
    (c : Γ(X, ⊤)ˣ) (hscale : ∀ q, b q = (c : Γ(X, ⊤)) * a q) :
    coordinatesMap X k a i hi = coordinatesMap X k b j hj := by
  let f := eval₂Hom k a
  let g := eval₂Hom k b
  have hf : IsUnit (f (MvPolynomial.X (R := K) i)) := by
    simpa only [f, eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(X, ⊤)))
  have hg : IsUnit (g (MvPolynomial.X (R := K) i)) := by
    simpa only [g, eval₂Hom_X', hscale i, hi, mul_one] using c.isUnit
  have hg' : IsUnit (g (MvPolynomial.X (R := K) j)) := by
    simpa only [g, eval₂Hom_X', hj] using (isUnit_one : IsUnit (1 : Γ(X, ⊤)))
  have H : ∀ n p, p ∈ homogeneousSubmodule σ K n →
      g p = (c : Γ(X, ⊤)) ^ n * f p := by
    intro n p hp
    change eval₂ k b p = _
    have hb : b = fun q => (c : Γ(X, ⊤)) * a q := funext hscale
    rw [hb]
    exact homogeneous_eval₂_scale hp k a c
  unfold coordinatesMap
  congr 1
  exact (fromUnitCoordinate_scale (𝒜 := homogeneousSubmodule σ K) (d := 1) f (by decide) (coordinates_X_mem (K := K) i)
    hf g hg c H).trans
      (fromUnitCoordinate_eq (𝒜 := homogeneousSubmodule σ K) (d := 1) (e := 1) g (by decide) (by decide)
        (coordinates_X_mem (K := K) i) (coordinates_X_mem (K := K) j) hg hg')

lemma coordinatesMap_preimage (X : Scheme.{u}) (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) (j : σ) :
    coordinatesMap X k a i hi ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j) = X.basicOpen (a j) := by
  rw [coordinatesMap, Scheme.Hom.comp_preimage,
    fromUnitCoordinate_preimage _ (coordinates_X_mem (K := K) i) _
      (by simpa only [eval₂Hom_X'] using hi) (by decide) (coordinates_X_mem (K := K) j),
    eval₂Hom_X', Scheme.toSpecΓ_preimage_basicOpen]

structure CoordinateAtlas (X : Scheme.{u}) where
  cover : X.OpenCover
  scalars : ∀ i : cover.I₀, K →+* Γ(cover.X i, ⊤)
  coordinates : ∀ i : cover.I₀, σ → Γ(cover.X i, ⊤)
  index : cover.I₀ → σ
  normalized : ∀ i, coordinates i (index i) = 1
  scalarOverlap : ∀ i j,
    (pullback.fst (cover.f i) (cover.f j)).appTop.hom.comp (scalars i) =
      (pullback.snd (cover.f i) (cover.f j)).appTop.hom.comp (scalars j)
  coordinateOverlap : ∀ i j,
    ∃ c : Γ(pullback (cover.f i) (cover.f j), ⊤)ˣ, ∀ q,
      (pullback.snd (cover.f i) (cover.f j)).appTop (coordinates j q) =
        (c : Γ(pullback (cover.f i) (cover.f j), ⊤)) *
          (pullback.fst (cover.f i) (cover.f j)).appTop (coordinates i q)

variable {X : Scheme.{u}} (D : CoordinateAtlas (K := K) (σ := σ) X)

def CoordinateAtlas.localMap (i : D.cover.I₀) :
    D.cover.X i ⟶ Proj (homogeneousSubmodule σ K) :=
  coordinatesMap _ (D.scalars i) (D.coordinates i) (D.index i) (D.normalized i)

lemma CoordinateAtlas.compatible (i j : D.cover.I₀) :
    pullback.fst (D.cover.f i) (D.cover.f j) ≫ D.localMap i =
      pullback.snd (D.cover.f i) (D.cover.f j) ≫ D.localMap j := by
  unfold CoordinateAtlas.localMap
  rw [coordinatesMap_natural, coordinatesMap_natural]
  obtain ⟨c, hc⟩ := D.coordinateOverlap i j
  simpa only [D.scalarOverlap i j] using
    coordinatesMap_scale _
      ((pullback.fst (D.cover.f i) (D.cover.f j)).appTop.hom.comp (D.scalars i))
      _ _ (D.index i) (D.index j)
      (by simp only [D.normalized, map_one])
      (by simp only [D.normalized, map_one]) c hc

def CoordinateAtlas.morphism : X ⟶ Proj (homogeneousSubmodule σ K) :=
  D.cover.glueMorphisms D.localMap D.compatible

@[reassoc, simp]
lemma CoordinateAtlas.cover_morphism (i : D.cover.I₀) :
    D.cover.f i ≫ D.morphism = D.localMap i :=
  D.cover.ι_glueMorphisms _ _ i

end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}

def atlasOfFramedSections {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (𝒰 : X.OpenCover)
    (e : ∀ i, M.restrict (𝒰.f i) ≅ O (𝒰.X i)) (index : 𝒰.I₀ → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (𝒰.f i) (s (index i))) = 1) :
    CoordinateAtlas (K := K) (σ := σ) X where
  cover := 𝒰
  scalars i := (𝒰.f i).appTop.hom.comp k
  coordinates i q := coefficient (e i) (restrictSection (𝒰.f i) (s q))
  index := index
  normalized := hnorm
  scalarOverlap i j := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    congr 1
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      congrArg (fun f : pullback (𝒰.f i) (𝒰.f j) ⟶ X => f.appTop.hom)
        (pullback.condition (f := 𝒰.f i) (g := 𝒰.f j))
  coordinateOverlap i j := by
    obtain ⟨c, hc⟩ := overlap_coefficients (𝒰.f i) (𝒰.f j)
      (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd (𝒰.f i) (𝒰.f j))
      (pullback.condition (f := 𝒰.f i) (g := 𝒰.f j)) (e i) (e j)
    exact ⟨c, fun q => hc (s q)⟩

def sectionFrame {M : X.Modules} (s : O X ⟶ M) :
    M.restrict (SectionOpens.isoOpen s).ι ≅ O (SectionOpens.isoOpen s).toScheme := by
  letI := SectionOpens.isIso_restrict_isoOpen s
  exact (asIso ((Scheme.Modules.restrictFunctor (SectionOpens.isoOpen s).ι).map s)).symm ≪≫
    Scheme.Modules.restrictUnitIso (SectionOpens.isoOpen s).ι

lemma sectionFrame_normalized {M : X.Modules} (s : O X ⟶ M) :
    coefficient (sectionFrame s) (restrictSection (SectionOpens.isoOpen s).ι s) = 1 := by
  change coefficient (sectionFrame s) (sectionFrame s).inv = 1
  exact coefficient_frame (sectionFrame s)

def sectionsMorphism {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K) :=
  (atlasOfFramedSections k s
    (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover)
    (fun i => sectionFrame (s i)) id (fun i => sectionFrame_normalized (s i))).morphism

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma sectionsMorphism_local {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (i : σ) :
    (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hcover =
      coordinatesMap (SectionOpens.isoOpen (s i)).toScheme
        ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))) i
        (sectionFrame_normalized (s i)) := by
  exact CoordinateAtlas.cover_morphism
    (atlasOfFramedSections k s
      (X.openCoverOfIsOpenCover (fun a => SectionOpens.isoOpen (s a)) hcover)
      (fun a => sectionFrame (s a)) id (fun a => sectionFrame_normalized (s a))) i

theorem sectionsMorphism_preimage {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (j : σ) :
    sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j) =
      SectionOpens.isoOpen (s j) := by
  ext x
  have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let U := SectionOpens.isoOpen (s i)
  have H : U.ι ⁻¹ᵁ (sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j)) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen (s j) := by
    rw [← Scheme.Hom.comp_preimage, sectionsMorphism_local,
      coordinatesMap_preimage, preimage_isoOpen (s j) U.ι (sectionFrame (s i))]
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : U.toScheme)

end
section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open PiExponentSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K]
variable (M : (Proj (PolyGrade K σ)).Modules)
variable (k : K →+* Γ(Proj (PolyGrade K σ),⊤))
variable (s : σ → (O (Proj (PolyGrade K σ)) ⟶ M))
variable (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (hid : sectionsMorphism k s hc = 𝟙 (Proj (PolyGrade K σ)))

include hid

lemma identityCoordinateOpen (i : σ) :
    SectionOpens.isoOpen (s i) = Proj.basicOpen (PolyGrade K σ) (X i) := by
  have h := sectionsMorphism_preimage k s hc i
  rw [hid] at h
  exact h.symm

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme} {M : X.Modules}

def sectionFrameOn (s : O X ⟶ M) (U : X.Opens) (hU : SectionOpens.isoOpen s = U) :
    M.restrict U.ι ≅ O U.toScheme := hU ▸ sectionFrame s

lemma sectionFrameOn_normalized (s : O X ⟶ M) (U : X.Opens)
    (hU : SectionOpens.isoOpen s = U) :
    coefficient (sectionFrameOn s U hU) (restrictSection U.ι s) = 1 := by
  subst U
  exact sectionFrame_normalized s

end PiExponentSeshadri.Projective

end

end OAI
