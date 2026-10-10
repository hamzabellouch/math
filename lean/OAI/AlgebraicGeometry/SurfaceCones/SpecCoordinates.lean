import OAI.AlgebraicGeometry.SurfaceCones.PolynomialRangeTranscendence

namespace OAI


/-! Coordinate maps for checking the source-chart evaluation glue. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
variable {Z Y : _root_.AlgebraicGeometry.Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B]

def coordinateMap (f : Z ⟶ _root_.AlgebraicGeometry.Spec (.of R)) : R →+* Γ(Z, ⊤) :=
  ((_root_.AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom

lemma coordinateMap_injective :
    Function.Injective (coordinateMap (Z := Z) (R := R)) := by
  intro f g h
  apply _root_.AlgebraicGeometry.ext_to_Spec
  exact CommRingCat.hom_ext h

lemma coordinateMap_comp (f : Z ⟶ _root_.AlgebraicGeometry.Spec (.of B)) (φ : R →+* B) :
    coordinateMap (f ≫ _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) =
      (coordinateMap f).comp φ := by
  unfold coordinateMap
  rw [_root_.AlgebraicGeometry.Scheme.Hom.comp_appTop, ← Category.assoc, ← _root_.AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality]
  rfl

lemma coordinateMap_precomp (α : Z ⟶ Y) (f : Y ⟶ _root_.AlgebraicGeometry.Spec (.of R)) :
    coordinateMap (α ≫ f) = α.appTop.hom.comp (coordinateMap f) := by
  unfold coordinateMap
  rw [_root_.AlgebraicGeometry.Scheme.Hom.comp_appTop, ← Category.assoc]
  rfl

end AlgebraicGeometry.Scheme

end


/-! Transition identity for homogeneous evaluation, used to glue the actual
source cone morphism. No geometric hypothesis is added. -/
noncomputable section
open _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization
namespace HomogeneousLocalization
open scoped _root_.HomogeneousLocalization
variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
  {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)

lemma awayMap_ratio_transition (n : ℕ) (b : A) (hb : b ∈ 𝒜 n) :
    _root_.HomogeneousLocalization.awayMap 𝒜 hg (rfl : f * g = f * g)
        (_root_.HomogeneousLocalization.Away.mk 𝒜 hf n b (by simpa using hb)) *
      (_root_.HomogeneousLocalization.awayMap 𝒜 hf (mul_comm f g)
        (_root_.HomogeneousLocalization.Away.mk 𝒜 hg 1 f (by simpa using hf))) ^ n =
    _root_.HomogeneousLocalization.awayMap 𝒜 hf (mul_comm f g)
      (_root_.HomogeneousLocalization.Away.mk 𝒜 hg n b (by simpa using hb)) := by
  apply HomogeneousLocalization.val_injective
  simp only [_root_.HomogeneousLocalization.val_mul, _root_.HomogeneousLocalization.val_pow, _root_.HomogeneousLocalization.awayMap_mk, _root_.HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_pow, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_iff_exists.mpr
  use 1
  simp only [Submonoid.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    pow_one]
  ring

end HomogeneousLocalization

end


/-! The genuine homogeneous transition identity on the overlap of two
surface charts. This will identify the previously constructed evaluations
on the actual source fiber product. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SectionCompletion
variable {k K : Type} [Field k] [Field K] [Algebra k K]
  (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

lemma dehomogenize_homogeneous (c : K) (hc : c ∈ T 1) (hn : c ≠ 0)
    (n : ℕ) (b : polynomials T) (hb : b ∈ homogeneous T n) :
    dehomogenize T c hc hn b = Away.mk (homogeneous T)
      (linearSection_homogeneous T c hc) n b (by simpa using hb) := by
  apply homogeneousChartMap_injective T c hc hn
  rw [homogeneousChartMap_dehomogenize, homogeneousChartMap_mk]
  exact evaluateInv_homogeneous T c n b (by simpa using hb)

lemma scheme_chart_transition {Z : Scheme}
    (c d : K) (hc : c ∈ T 1) (hd : d ∈ T 1) (hcn : c ≠ 0) (hdn : d ≠ 0)
    (u : Z ⟶ Spec (.of (homogeneousChart T c hc)))
    (v : Z ⟶ Spec (.of (homogeneousChart T d hd)))
    (huv : u ≫ Proj.awayι (homogeneous T) (linearSection T c hc)
        (linearSection_homogeneous T c hc) zero_lt_one =
      v ≫ Proj.awayι (homogeneous T) (linearSection T d hd)
        (linearSection_homogeneous T d hd) zero_lt_one)
    (n : ℕ) (b : polynomials T) (hb : b ∈ homogeneous T n) :
    Scheme.coordinateMap u (dehomogenize T c hc hcn b) *
        Scheme.coordinateMap v (dehomogenize T d hd hdn (linearSection T c hc)) ^ n =
      Scheme.coordinateMap v (dehomogenize T d hd hdn b) := by
  let e := Proj.pullbackAwayιIso (homogeneous T)
    (linearSection_homogeneous T c hc) zero_lt_one
    (linearSection_homogeneous T d hd) zero_lt_one rfl
  let w := pullback.lift u v huv ≫ e.hom
  let fi := awayMap (homogeneous T) (linearSection_homogeneous T d hd)
    (rfl : linearSection T c hc * linearSection T d hd = _)
  let fj := awayMap (homogeneous T) (linearSection_homogeneous T c hc)
    (mul_comm (linearSection T c hc) (linearSection T d hd))
  have hwi : w ≫ Spec.map (CommRingCat.ofHom fi) = u := by
    simp only [w, e, fi, Category.assoc,
      Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left, pullback.lift_fst]
  have hwj : w ≫ Spec.map (CommRingCat.ofHom fj) = v := by
    simp only [w, e, fj, Category.assoc,
      Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right, pullback.lift_snd]
  rw [dehomogenize_homogeneous T c hc hcn n b hb,
    dehomogenize_linearSection,
    dehomogenize_homogeneous T d hd hdn n b hb]
  have hui : Scheme.coordinateMap u = (Scheme.coordinateMap w).comp fi := by
    rw [← hwi, Scheme.coordinateMap_comp]
  have hvj : Scheme.coordinateMap v = (Scheme.coordinateMap w).comp fj := by
    rw [← hwj, Scheme.coordinateMap_comp]
  rw [hui, hvj]
  have ht := congrArg (Scheme.coordinateMap w) (awayMap_ratio_transition (homogeneous T)
      (linearSection_homogeneous T c hc) (linearSection_homogeneous T d hd) n b hb)
  rw [(Scheme.coordinateMap w).map_mul, (Scheme.coordinateMap w).map_pow] at ht
  exact ht

end SectionCompletion
namespace SourcePullbackChart

lemma blowupIota_blowdown (i : Fin 3) :
    blowupIota i ≫ KummerSourceModel.blowdown =
      Spec.map (CommRingCat.ofHom (baseMap i)) := by
  unfold KummerSourceModel.blowdown
  rw [← Category.assoc]
  have h := Proj.awayι_toSpecZero grades (sourceSection i)
    (sourceSection_homogeneous i) zero_lt_one
  change blowupIota i ≫ Proj.toSpecZero grades = _ at h
  rw [h]
  have hz : KummerSourceModel.zeroSpecIso.hom =
      Spec.map (CommRingCat.ofHom baseToZero) := rfl
  rw [hz, ← Spec.map_comp]
  apply congrArg Spec.map
  rfl

end SourcePullbackChart

end


/-! Gluing the actual local cone evaluations. The gluing proof uses neither
an assumed source comparison nor a numerical Chern premise. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization _root_.Polynomial _root_.OAI.Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
open SectionCompletion
local instance pullbackCommRing (i : Fin 3) : CommRing (pullbackChart i) := inferInstance
local instance pullbackMonoid (i : Fin 3) : Monoid (pullbackChart i) := (pullbackCommRing i).toMonoid
local instance pullbackMul (i : Fin 3) : Mul (pullbackChart i) := ⟨(pullbackCommRing i).mul⟩
local instance pullbackAdd (i : Fin 3) : Add (pullbackChart i) := ⟨(pullbackCommRing i).add⟩

lemma coneEvaluation_homogeneous (i : Fin 3) (n : ℕ) (b : sectionRing)
    (hb : b ∈ homogeneous ExplicitCone.pieces n) :
    coneEvaluation i b =
      surfaceIn i (dehomogenize ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
        (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i) b) *
      fiberParameter i ^ n := by
  change Polynomial.eval₂ (surfaceIn i) (fiberParameter i)
    (chartEvaluation ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i) b) = _
  exact (congrArg (Polynomial.eval₂ (surfaceIn i) (fiberParameter i))
    (chartEvaluation_homogeneous ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i) n b hb)).trans
    (Polynomial.eval₂_monomial _ _)

lemma fiberParameter_relation (i j : Fin 3) :
    surfaceIn j (dehomogenize ExplicitCone.pieces (ExplicitCone.projectiveParameter j)
      (ExplicitCone.projectiveParameter_mem j) (ExplicitCone.projectiveParameter_ne_zero j)
      (linearSection ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
        (ExplicitCone.projectiveParameter_mem i))) * fiberParameter j =
      blowupIn j (baseMap j (MvPolynomial.X i)) := by
  rw [← surfaceDirectionMap_ratio, tensor_balance]
  change blowupIn j _ * blowupIn j _ = _
  rw [← (blowupIn j).map_mul, ratio_relation]

@[reassoc] lemma pullbackIota_base (i : Fin 3) :
    pullbackIota i ≫ KummerSourceModel.g₀ ≫ KummerSourceModel.blowdown =
      Spec.map (CommRingCat.ofHom ((blowupIn i).comp (baseMap i))) := by
  rw [pullbackIota_blowup_assoc, blowupIota_blowdown, ← Spec.map_comp]
  rfl

lemma surfaceMap_compatible {Z : Scheme} (i j : Fin 3)
    (α : Z ⟶ Spec (.of (pullbackChart i))) (β : Z ⟶ Spec (.of (pullbackChart j)))
    (hαβ : α ≫ pullbackIota i = β ≫ pullbackIota j) :
    (α ≫ Spec.map (CommRingCat.ofHom (surfaceIn i))) ≫ surfaceIota i =
      (β ≫ Spec.map (CommRingCat.ofHom (surfaceIn j))) ≫ surfaceIota j := by
  calc
    _ = (α ≫ pullbackIota i) ≫ pullback.fst _ _ := by
      simpa only [Category.assoc] using
        (congrArg (fun f => α ≫ f) (pullbackIota_surface i)).symm
    _ = (β ≫ pullbackIota j) ≫ pullback.fst _ _ := by rw [hαβ]
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun f => β ≫ f) (pullbackIota_surface j)

lemma baseMap_compatible {Z : Scheme} (i j : Fin 3)
    (α : Z ⟶ Spec (.of (pullbackChart i))) (β : Z ⟶ Spec (.of (pullbackChart j)))
    (hαβ : α ≫ pullbackIota i = β ≫ pullbackIota j) :
    α ≫ Spec.map (CommRingCat.ofHom ((blowupIn i).comp (baseMap i))) =
      β ≫ Spec.map (CommRingCat.ofHom ((blowupIn j).comp (baseMap j))) := by
  calc
    _ = (α ≫ pullbackIota i) ≫ KummerSourceModel.g₀ ≫ KummerSourceModel.blowdown := by
      simpa only [Category.assoc] using
        (congrArg (fun f => α ≫ f) (pullbackIota_base i)).symm
    _ = (β ≫ pullbackIota j) ≫ KummerSourceModel.g₀ ≫ KummerSourceModel.blowdown := by rw [hαβ]
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun f => β ≫ f) (pullbackIota_base j)

lemma fiberParameter_compatible {Z : Scheme} (i j : Fin 3)
    (α : Z ⟶ Spec (.of (pullbackChart i))) (β : Z ⟶ Spec (.of (pullbackChart j)))
    (hαβ : α ≫ pullbackIota i = β ≫ pullbackIota j) :
    Scheme.coordinateMap α (fiberParameter i) =
      Scheme.coordinateMap β (surfaceIn j
        (dehomogenize ExplicitCone.pieces (ExplicitCone.projectiveParameter j)
          (ExplicitCone.projectiveParameter_mem j) (ExplicitCone.projectiveParameter_ne_zero j)
          (linearSection ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
            (ExplicitCone.projectiveParameter_mem i)))) *
          Scheme.coordinateMap β (fiberParameter j) := by
  have hh := congrArg (fun f => Scheme.coordinateMap f (MvPolynomial.X i))
    (baseMap_compatible i j α β hαβ)
  simp only [Scheme.coordinateMap_comp, RingHom.comp_apply] at hh
  change Scheme.coordinateMap α (fiberParameter i) =
    Scheme.coordinateMap β (blowupIn j (baseMap j (MvPolynomial.X i))) at hh
  rw [hh, ← fiberParameter_relation, (Scheme.coordinateMap β).map_mul]

private lemma homogeneous_evaluation_calculation {T : Type*} [CommRing T]
    (a b c s t : T) (n : ℕ) (ht : a * c ^ n = b) (hp : s = c * t) :
    a * s ^ n = b * t ^ n := by
  rw [hp, mul_pow, ← mul_assoc, ht]

private lemma map_mul_pow {T U : Type*} [CommRing T] [CommRing U]
    (u : T →+* U) (a b : T) (n : ℕ) : u (a * b ^ n) = u a * u b ^ n := by
  rw [u.map_mul, u.map_pow]

lemma map_coneEvaluation_homogeneous (i : Fin 3) {T : Type*} [CommRing T]
    (u : pullbackChart i →+* T) (n : ℕ) (b : sectionRing)
    (hb : b ∈ homogeneous ExplicitCone.pieces n) :
    u (coneEvaluation i b) =
      u (surfaceIn i (dehomogenize ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
        (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i) b)) *
      u (fiberParameter i) ^ n :=
  (congrArg u (coneEvaluation_homogeneous i n b hb)).trans (map_mul_pow u _ _ n)

lemma evaluation_homogeneous_compatible {Z : Scheme} (i j : Fin 3)
    (α : Z ⟶ Spec (.of (pullbackChart i))) (β : Z ⟶ Spec (.of (pullbackChart j)))
    (hαβ : α ≫ pullbackIota i = β ≫ pullbackIota j)
    (n : ℕ) (b : sectionRing) (hb : b ∈ homogeneous ExplicitCone.pieces n) :
    Scheme.coordinateMap α (coneEvaluation i b) =
      Scheme.coordinateMap β (coneEvaluation j b) := by
  let u := Scheme.coordinateMap α
  let v := Scheme.coordinateMap β
  have ht := scheme_chart_transition ExplicitCone.pieces
    (ExplicitCone.projectiveParameter i) (ExplicitCone.projectiveParameter j)
    (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_mem j)
    (ExplicitCone.projectiveParameter_ne_zero i) (ExplicitCone.projectiveParameter_ne_zero j)
    (α ≫ Spec.map (CommRingCat.ofHom (surfaceIn i)))
    (β ≫ Spec.map (CommRingCat.ofHom (surfaceIn j))) (surfaceMap_compatible i j α β hαβ) n b hb
  simp only [Scheme.coordinateMap_comp, RingHom.comp_apply] at ht
  have hp := fiberParameter_compatible i j α β hαβ
  exact (map_coneEvaluation_homogeneous i u n b hb).trans
    ((homogeneous_evaluation_calculation _ _ _ _ _ n ht hp).trans
      (map_coneEvaluation_homogeneous j v n b hb).symm)

/-- Compatibility of the local evaluations under any two maps into source
charts whose actual source maps agree. In particular this applies on overlaps. -/
lemma evaluation_compatible {Z : Scheme} (i j : Fin 3)
    (α : Z ⟶ Spec (.of (pullbackChart i))) (β : Z ⟶ Spec (.of (pullbackChart j)))
    (hαβ : α ≫ pullbackIota i = β ≫ pullbackIota j) :
    α ≫ Spec.map (CommRingCat.ofHom (coneEvaluation i)) =
      β ≫ Spec.map (CommRingCat.ofHom (coneEvaluation j)) := by
  classical
  apply Scheme.coordinateMap_injective
  rw [Scheme.coordinateMap_comp, Scheme.coordinateMap_comp]
  apply RingHom.ext
  intro b
  rw [← DirectSum.sum_support_decompose (homogeneous ExplicitCone.pieces) b]
  simp only [RingHom.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact evaluation_homogeneous_compatible i j α β hαβ n _
    (DirectSum.decompose (homogeneous ExplicitCone.pieces) b n).property

/-- The source's cone-evaluation morphism before completion, constructed by
honest gluing on the literal W₀ = X ×[P²] V₀. -/
def coneMorphism : KummerSourceModel.W₀ ⟶ Spec (.of sectionRing) :=
  sourceCover.glueMorphisms
    (fun i => Spec.map (CommRingCat.ofHom (coneEvaluation i)))
    (fun i j => evaluation_compatible i j (pullback.fst _ _) (pullback.snd _ _)
      pullback.condition)

@[reassoc] lemma pullbackIota_coneMorphism (i : Fin 3) :
    pullbackIota i ≫ coneMorphism = Spec.map (CommRingCat.ofHom (coneEvaluation i)) :=
  sourceCover.ι_glueMorphisms _ _ i

/-- The glued evaluation is a morphism over the exact polynomial parameters. -/
@[reassoc] lemma coneMorphism_parameters :
    coneMorphism ≫ Spec.map (CommRingCat.ofHom parameterMap.toRingHom) =
      KummerSourceModel.g₀ ≫ KummerSourceModel.blowdown := by
  apply sourceCover.hom_ext
  intro i
  change Fin 3 at i
  change pullbackIota i ≫ _ = pullbackIota i ≫ _
  erw [pullbackIota_coneMorphism_assoc, pullbackIota_base, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (coneEvaluation_comp_parameters i)

end SourcePullbackChart

end


/-! The literal source chart is the full inverse image of the corresponding
blowup chart. Needed to pass the local punctured-ring calculation to p. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart

lemma tensorChart_isPullback (i : Fin 3) :
    IsPullback (Spec.map (CommRingCat.ofHom (surfaceIn i)))
      (Spec.map (CommRingCat.ofHom (blowupIn i)))
      (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
      (Spec.map (CommRingCat.ofHom (directionMap i))) := by
  apply (IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
    (Spec.map (CommRingCat.ofHom (directionMap i)))).of_iso'
      (pullbackSpecIso (planeChart i) (surfaceChart i) (chart i)).symm
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    exact pullbackSpecIso_inv_fst (planeChart i) (surfaceChart i) (chart i)
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    exact pullbackSpecIso_inv_snd (planeChart i) (surfaceChart i) (chart i)
  · simp
  · simp

lemma sourceChart_isPullback (i : Fin 3) :
    IsPullback (pullbackIota i) (Spec.map (CommRingCat.ofHom (blowupIn i)))
      KummerSourceModel.g₀ (blowupIota i) := by
  have hh := (tensorChart_isPullback i).paste_horiz (surface_isPullback i)
  rw [← pullbackIota_surface, ← blowup_chart_square] at hh
  exact hh.of_right (pullbackIota_blowup i)
    (IsPullback.of_hasPullback ExplicitCone.projectiveNormalization KummerSourceModel.direction)

lemma pullbackIota_opensRange (i : Fin 3) :
    (pullbackIota i).opensRange = KummerSourceModel.g₀ ⁻¹ᵁ (blowupIota i).opensRange := by
  have hh := (Scheme.Hom.opensRange_comp_of_isIso
    (sourceChart_isPullback i).isoPullback.hom
    (pullback.fst KummerSourceModel.g₀ (blowupIota i))).trans
      (Scheme.Hom.opensRange_pullbackFst (blowupIota i) KummerSourceModel.g₀)
  simpa only [(sourceChart_isPullback i).isoPullback_hom_fst] using hh

end SourcePullbackChart

end


/-! The literal W₀ is isomorphic to the cone over the union of the three
parameter punctures. This is the source map required in the manuscript, lines 243–280. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart

lemma blowdown_mem (x : KummerSourceModel.V₀) (a : S) :
    a ∈ (KummerSourceModel.blowdown x).asIdeal ↔
      algebraMap S Rees a ∈ x.asHomogeneousIdeal := by
  change baseToZero a ∈ (Proj.toSpecZero grades x).asIdeal ↔ _
  exact ProjZeroPoints.toSpecZero_mem grades x (baseToZero a)

lemma blowdown_preimage_le_chart (i : Fin 3) :
    KummerSourceModel.blowdown ⁻¹ᵁ PrimeSpectrum.basicOpen (MvPolynomial.X i) ≤
      (blowupIota i).opensRange := by
  simp only [blowupIota, Proj.opensRange_awayι]
  intro x hx
  change ¬ sourceSection i ∈ x.asHomogeneousIdeal
  intro hi
  have hbase : ¬ algebraMap S Rees (MvPolynomial.X i) ∈ x.asHomogeneousIdeal :=
    (blowdown_mem x (MvPolynomial.X i)).not.mp hx
  have hall (j : Fin 3) : sourceSection j ∈ x.asHomogeneousIdeal := by
    have hm : algebraMap S Rees (MvPolynomial.X i) * sourceSection j ∈
        x.asHomogeneousIdeal := by
      rw [mul_comm, sourceSection_cross]
      exact x.asHomogeneousIdeal.toIdeal.mul_mem_right _ hi
    exact (x.isPrime.mem_or_mem hm).resolve_left hbase
  have hh : x ∈ (⨆ j : Fin 3, Proj.basicOpen grades (sourceSection j)) := by
    rw [KummerSourceModel.sourceSections_cover]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hh
  exact hj (hall j)

lemma coneMorphism_preimage_le_chart (i : Fin 3) :
    coneMorphism ⁻¹ᵁ PrimeSpectrum.basicOpen (coneSection i) ≤ (pullbackIota i).opensRange := by
  rw [pullbackIota_opensRange, coneSection_eq]
  change coneMorphism ⁻¹ᵁ
    ((Spec.map (CommRingCat.ofHom parameterMap.toRingHom)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (MvPolynomial.X i)) ≤ _
  erw [← Scheme.Hom.comp_preimage, coneMorphism_parameters, Scheme.Hom.comp_preimage]
  exact KummerSourceModel.g₀.preimage_mono (blowdown_preimage_le_chart i)

/-- The full inverse image of a cone puncture, not just an auxiliary chart,
is the same punctured affine scheme. -/
lemma coneMorphism_restrict_isIso (i : Fin 3) :
    IsIso (coneMorphism ∣_ PrimeSpectrum.basicOpen (coneSection i)) := by
  have : IsIso ((pullbackIota i ≫ coneMorphism) ∣_ PrimeSpectrum.basicOpen (coneSection i)) := by
    rw [pullbackIota_coneMorphism]
    exact coneEvaluation_restrict_isIso i
  exact SchemeRestrictionImage.isIso_of_chart (pullbackIota i) coneMorphism
    (PrimeSpectrum.basicOpen (coneSection i)) (coneMorphism_preimage_le_chart i)

def conePuncturedOpen : (Spec (.of sectionRing)).Opens :=
  ⨆ i : Fin 3, PrimeSpectrum.basicOpen (coneSection i)

instance : IsIso (coneMorphism ∣_ conePuncturedOpen) :=
  SchemeRestrictionImage.isIso_restrict_iSup coneMorphism _ coneMorphism_restrict_isIso

end SourcePullbackChart

end


/-! The uncompleted literal model is reduced and its actual cone puncture is
schematically dense. This is the source-dependent input for integrality of
W after the flat completion, needed for the double-dual extension. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
local instance integralSurfaceCommRing (i : Fin 3) : CommRing (surfaceChart i) := inferInstance
local instance integralSurfaceSemiring (i : Fin 3) : Semiring (surfaceChart i) :=
  (integralSurfaceCommRing i).toSemiring
local instance integralPullbackCommRing (i : Fin 3) : CommRing (pullbackChart i) := inferInstance
local instance integralPullbackSemiring (i : Fin 3) : Semiring (pullbackChart i) :=
  (integralPullbackCommRing i).toSemiring

instance surfaceChart_domain (i : Fin 3) : IsDomain (surfaceChart i) :=
  Function.Injective.isDomain
    (SectionCompletion.homogeneousChartMap ExplicitCone.pieces
      (ExplicitCone.projectiveParameter i) (ExplicitCone.projectiveParameter_mem i)
      (ExplicitCone.projectiveParameter_ne_zero i))
    (SectionCompletion.homogeneousChartMap_injective ExplicitCone.pieces
      (ExplicitCone.projectiveParameter i) (ExplicitCone.projectiveParameter_mem i)
      (ExplicitCone.projectiveParameter_ne_zero i))

instance pullbackChart_domain (i : Fin 3) : IsDomain (pullbackChart i) := by
  let := surfaceChart_domain i
  exact Function.Injective.isDomain (pullbackPolynomialEquiv i).toRingHom
    (pullbackPolynomialEquiv i).injective

instance uncompleted_reduced : IsReduced KummerSourceModel.W₀ := by
  have (i : sourceCover.I₀) : IsReduced (sourceCover.X i) := by
    change IsReduced (Spec (.of (pullbackChart i)))
    let := pullbackChart_domain i
    infer_instance
  exact IsReduced.of_openCover _ sourceCover

instance uncompleted_noetherian : IsLocallyNoetherian KummerSourceModel.W₀ := by
  have := KummerSourceModel.g₀_finite
  exact LocallyOfFiniteType.isLocallyNoetherian (KummerSourceModel.g₀ ≫ KummerSourceModel.blowdown)

abbrev sourcePuncture : KummerSourceModel.W₀.Opens := coneMorphism ⁻¹ᵁ conePuncturedOpen

lemma chartPuncture_nonempty (i : Fin 3) :
    ((pullbackIota i) ⁻¹ᵁ sourcePuncture : Set (Spec (.of (pullbackChart i)))).Nonempty := by
  have hn : coneEvaluation i (coneSection i) ≠ 0 := by
    intro h
    have he := pullbackPolynomialEquiv_coneSection i
    rw [h, map_zero] at he
    exact Polynomial.X_ne_zero he.symm
  have hne : (PrimeSpectrum.basicOpen (coneEvaluation i (coneSection i)) :
      Set (PrimeSpectrum (pullbackChart i))).Nonempty := by
    rw [← Opens.ne_bot_iff_nonempty]
    intro he
    exact hn ((PrimeSpectrum.basicOpen_eq_bot_iff _).mp he).eq_zero
  apply hne.mono
  change (Spec.map (CommRingCat.ofHom (coneEvaluation i))) ⁻¹ᵁ
    PrimeSpectrum.basicOpen (coneSection i) ≤ _
  erw [← pullbackIota_coneMorphism, Scheme.Hom.comp_preimage]
  exact (pullbackIota i).preimage_mono
    (coneMorphism.preimage_mono (le_iSup (fun i => PrimeSpectrum.basicOpen (coneSection i)) i))

lemma sourcePuncture_dense : Dense (sourcePuncture : Set KummerSourceModel.W₀) := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, y, rfl⟩ := sourceCover.exists_eq x
  change Fin 3 at i
  have hd := ((pullbackIota i) ⁻¹ᵁ sourcePuncture).isOpen.dense (chartPuncture_nonempty i)
  obtain ⟨z, hz₁, hz₂⟩ := hd.inter_open_nonempty
    ((pullbackIota i) ⁻¹' U) (hU.preimage (pullbackIota i).continuous) ⟨y, hx⟩
  exact ⟨pullbackIota i z, hz₁, hz₂⟩

instance sourcePuncture_dominant : IsDominant sourcePuncture.ι := by
  rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
  exact sourcePuncture_dense

instance sourcePuncture_schematicallyDominant : IsSchemeTheoreticallyDominant sourcePuncture.ι :=
  IsSchemeTheoreticallyDominant.of_isDominant _

end SourcePullbackChart

end


/-! The actual zero-section equations in each polynomial-blowup chart.
These are used to identify the closed fiber with the literal plane, and then
with the actual projectiveSurface after its finite base change. -/
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
local instance originChartCommRing (i : Fin 3) : CommRing (chart i) := inferInstance
local instance originChartSemiring (i : Fin 3) : Semiring (chart i) :=
  (originChartCommRing i).toSemiring
local instance originPlaneCommRing (i : Fin 3) : CommRing (planeChart i) := inferInstance
local instance originPlaneSemiring (i : Fin 3) : Semiring (planeChart i) :=
  (originPlaneCommRing i).toSemiring

/-- Set the genuine fiber coordinate to zero. -/
def zeroEvaluation (i : Fin 3) : chart i →+* planeChart i :=
  (Polynomial.evalRingHom 0).comp (planePolynomialEquiv i).symm.toRingHom

@[simp] lemma zeroEvaluation_direction (i : Fin 3) (a : planeChart i) :
    zeroEvaluation i (directionMap i a) = a := by
  rw [← planePolynomialEquiv_C]
  change (Polynomial.evalRingHom 0)
    ((planePolynomialEquiv i).symm ((planePolynomialEquiv i) (C a))) = a
  rw [AlgEquiv.symm_apply_apply]
  exact Polynomial.eval_C

@[simp] lemma zeroEvaluation_fiber (i : Fin 3) :
    zeroEvaluation i (baseMap i (MvPolynomial.X i)) = 0 := by
  rw [← planePolynomialEquiv_X]
  change (Polynomial.evalRingHom 0)
    ((planePolynomialEquiv i).symm ((planePolynomialEquiv i) X)) = 0
  rw [AlgEquiv.symm_apply_apply]
  exact Polynomial.eval_X

lemma zeroEvaluation_base (i : Fin 3) :
    (zeroEvaluation i).comp (baseMap i) =
      (algebraMap ℂ (planeChart i)).comp MvPolynomial.constantCoeff := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, MvPolynomial.constantCoeff_C]
    rw [← directionMap_scalar, zeroEvaluation_direction]
  · intro j
    simp only [RingHom.comp_apply, MvPolynomial.constantCoeff_X, map_zero]
    rw [← ratio_relation i j, map_mul, zeroEvaluation_fiber, mul_zero]

lemma zeroEvaluation_surjective (i : Fin 3) : Function.Surjective (zeroEvaluation i) :=
  fun a => ⟨directionMap i a, zeroEvaluation_direction i a⟩

lemma origin_image_principal (i : Fin 3) :
    origin.map (baseMap i) = Ideal.span {baseMap i (MvPolynomial.X i)} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, origin, Ideal.span_le]
    rintro x ⟨j, rfl⟩
    change baseMap i (MvPolynomial.X j) ∈ Ideal.span {baseMap i (MvPolynomial.X i)}
    rw [← ratio_relation i j]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    rintro x rfl
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i))

end SourcePullbackChart

end


/-! Actual Cartier zero-section algebra on the tensor charts of W₀.
All maps are induced by the source's fixed three projective parameters. -/
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring

def pullbackBaseMap (i : Fin 3) : S →+* pullbackChart i := (blowupIn i).comp (baseMap i)
local instance pullbackBaseAlgebra (i : Fin 3) : Algebra S (pullbackChart i) :=
  (pullbackBaseMap i).toAlgebra
local instance surfaceOriginAlgebra (i : Fin 3) : Algebra S (surfaceChart i) :=
  ((algebraMap ℂ (surfaceChart i)).comp MvPolynomial.constantCoeff).toAlgebra

def pullbackZeroEvaluation (i : Fin 3) : pullbackChart i →+* surfaceChart i :=
  (Polynomial.evalRingHom 0).comp (pullbackPolynomialEquiv i).toRingHom

@[simp] lemma pullbackZeroEvaluation_surface (i : Fin 3) (a : surfaceChart i) :
    pullbackZeroEvaluation i (surfaceIn i a) = a := by
  change Polynomial.eval 0 (pullbackPolynomialEquiv i (surfaceIn i a)) = a
  rw [pullbackPolynomialEquiv_surface, Polynomial.eval_C]

@[simp] lemma pullbackZeroEvaluation_fiber (i : Fin 3) :
    pullbackZeroEvaluation i (fiberParameter i) = 0 := by
  change Polynomial.eval 0 (pullbackPolynomialEquiv i (fiberParameter i)) = 0
  rw [pullbackPolynomialEquiv_fiber, Polynomial.eval_X]

lemma pullbackZeroEvaluation_base (i : Fin 3) :
    (pullbackZeroEvaluation i).comp (pullbackBaseMap i) =
      (algebraMap ℂ (surfaceChart i)).comp MvPolynomial.constantCoeff := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change pullbackZeroEvaluation i (blowupIn i (baseMap i (MvPolynomial.C a))) =
      algebraMap ℂ (surfaceChart i) (MvPolynomial.constantCoeff (MvPolynomial.C a))
    have hh := RingHom.congr_fun (coneEvaluation_comp_parameters i) (MvPolynomial.C a)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hh
    rw [← hh]
    have hpar : parameterMap (MvPolynomial.C a) = algebraMap ℂ sectionRing a := parameterMap.commutes a
    rw [hpar, coneEvaluation_scalar, pullbackZeroEvaluation_surface, MvPolynomial.constantCoeff_C]
  · intro j
    change pullbackZeroEvaluation i (blowupIn i (baseMap i (MvPolynomial.X j))) =
      algebraMap ℂ (surfaceChart i) (MvPolynomial.constantCoeff (MvPolynomial.X j))
    rw [← ratio_relation i j, map_mul, map_mul]
    change _ * pullbackZeroEvaluation i (fiberParameter i) = _
    rw [pullbackZeroEvaluation_fiber, mul_zero, MvPolynomial.constantCoeff_X, map_zero]

def pullbackZeroAlg (i : Fin 3) : pullbackChart i →ₐ[S] surfaceChart i :=
  { pullbackZeroEvaluation i with
    commutes' := fun a => RingHom.congr_fun (pullbackZeroEvaluation_base i) a }

lemma pullbackZeroEvaluation_surjective (i : Fin 3) :
    Function.Surjective (pullbackZeroEvaluation i) :=
  fun a => ⟨surfaceIn i a, pullbackZeroEvaluation_surface i a⟩

lemma pullbackZeroEvaluation_kernel (i : Fin 3) :
    RingHom.ker (pullbackZeroEvaluation i) = Ideal.span {fiberParameter i} := by
  ext a
  change pullbackZeroEvaluation i a = 0 ↔ a ∈ Ideal.span {fiberParameter i}
  rw [Ideal.mem_span_singleton]
  change Polynomial.eval 0 (pullbackPolynomialEquiv i a) = 0 ↔ _
  rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.X_dvd_iff]
  rw [← pullbackPolynomialEquiv_fiber i]
  exact map_dvd_iff (pullbackPolynomialEquiv i)

lemma fiberParameter_regular (i : Fin 3) : IsSMulRegular (pullbackChart i) (fiberParameter i) := by
  apply IsSMulRegular.of_ne_zero
  intro h
  have hh := pullbackPolynomialEquiv_fiber i
  rw [h, map_zero] at hh
  exact Polynomial.X_ne_zero hh.symm

/-- The exact quotient at the zero section, with its S-algebra map. -/
def pullbackZeroQuotient (i : Fin 3) :
    (pullbackChart i ⧸ RingHom.ker (pullbackZeroEvaluation i)) ≃ₐ[S] surfaceChart i :=
  Ideal.quotientKerAlgEquivOfSurjective (f := pullbackZeroAlg i)
    (pullbackZeroEvaluation_surjective i)

end SourcePullbackChart

end


/-! Completion does not change the actual scalar-origin fiber. This lemma
is used on the genuine polynomial charts of the manuscript's zero section. -/
noncomputable section
open TensorProduct
namespace OriginScalarBaseChange
variable (σ k D : Type*) [Fintype σ] [CommRing k] [CommRing D] [Algebra k D]
abbrev S := MvPolynomial σ k
abbrev A := MvPowerSeries σ k
variable [Algebra (S σ k) D]
variable (h : algebraMap (S σ k) D = (algebraMap k D).comp MvPolynomial.constantCoeff)

omit [Fintype σ] in
lemma constantCoeff_polynomial (a : S σ k) :
    MvPowerSeries.constantCoeff (algebraMap (S σ k) (A σ k) a) =
      MvPolynomial.constantCoeff a := by
  rfl

def evaluation : A σ k →ₐ[S σ k] D :=
  { (algebraMap k D).comp MvPowerSeries.constantCoeff with
    commutes' := fun a => by
      change algebraMap k D (MvPowerSeries.constantCoeff (algebraMap (S σ k) (A σ k) a)) = _
      rw [constantCoeff_polynomial, h]; rfl }

abbrev tensor := D ⊗[S σ k] A σ k

def tensorEvaluation : tensor σ k D →ₐ[S σ k] D :=
  Algebra.TensorProduct.lift (AlgHom.id _ _) (evaluation σ k D h) (fun _ _ => Commute.all _ _)

include h

omit [Fintype σ] in
lemma tensor_X_zero (i : σ) : (1 : D) ⊗ₜ[S σ k] (MvPowerSeries.X i) = (0 : tensor σ k D) := by
  have hh := RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    (R := S σ k) (A := D) (B := A σ k)) (MvPolynomial.X i)
  change algebraMap (S σ k) D (MvPolynomial.X i) ⊗ₜ[S σ k] (1 : A σ k) =
    (1 : D) ⊗ₜ[S σ k] algebraMap (S σ k) (A σ k) (MvPolynomial.X i) at hh
  have he : algebraMap (S σ k) D (MvPolynomial.X i) = 0 := by
    rw [h]
    change algebraMap k D (MvPolynomial.constantCoeff (MvPolynomial.X i)) = 0
    simp
  rw [he, zero_tmul] at hh
  simpa only [MvPowerSeries.algebraMap_apply', MvPolynomial.coe_X,
    MvPowerSeries.map_X, Algebra.TensorProduct.includeRight_apply] using hh.symm

lemma tensor_constant (a : A σ k) :
    (1 : D) ⊗ₜ[S σ k] a = algebraMap k D (MvPowerSeries.constantCoeff a) ⊗ₜ[S σ k] (1 : A σ k) := by
  have hle : Ideal.span (Set.range (MvPowerSeries.X : σ → A σ k)) ≤
      RingHom.ker (Algebra.TensorProduct.includeRight.toRingHom : A σ k →+* tensor σ k D) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact tensor_X_zero σ k D h i
  have ha := hle (mvPowerSeries_constantCoeff_zero_mem_vars
    (a - MvPowerSeries.C (MvPowerSeries.constantCoeff a)) (by simp))
  change (Algebra.TensorProduct.includeRight.toRingHom : A σ k →+* tensor σ k D)
    (a - MvPowerSeries.C (MvPowerSeries.constantCoeff a)) = 0 at ha
  rw [map_sub, sub_eq_zero] at ha
  change (1 : D) ⊗ₜ[S σ k] a = (1 : D) ⊗ₜ[S σ k] MvPowerSeries.C _ at ha
  rw [ha]
  have hh := RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    (R := S σ k) (A := D) (B := A σ k))
      (MvPolynomial.C (MvPowerSeries.constantCoeff a))
  change algebraMap (S σ k) D (MvPolynomial.C (MvPowerSeries.constantCoeff a)) ⊗ₜ[S σ k] (1 : A σ k) =
    (1 : D) ⊗ₜ[S σ k] algebraMap (S σ k) (A σ k) (MvPolynomial.C (MvPowerSeries.constantCoeff a)) at hh
  simpa only [h, RingHom.comp_apply, MvPolynomial.constantCoeff_C,
    MvPowerSeries.algebraMap_apply', MvPolynomial.coe_C, MvPowerSeries.map_C,
    Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.includeRight_apply] using hh.symm

omit [Fintype σ] in
lemma tensorEvaluation_tmul (d : D) (a : A σ k) :
    tensorEvaluation σ k D h (d ⊗ₜ[S σ k] a) =
      d * algebraMap k D (MvPowerSeries.constantCoeff a) := by
  simp only [tensorEvaluation, Algebra.TensorProduct.lift_tmul]
  rfl

/-- Exact origin scalar base change, including its canonical maps. -/
def equiv : tensor σ k D ≃+* D :=
  { (tensorEvaluation σ k D h).toRingHom with
    invFun := fun d => d ⊗ₜ[S σ k] 1
    left_inv := by
      intro x
      change tensorEvaluation σ k D h x ⊗ₜ[S σ k] (1 : A σ k) = x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
      | tmul d a =>
        rw [tensorEvaluation_tmul]
        calc
          _ = (d ⊗ₜ[S σ k] (1 : A σ k)) *
              (algebraMap k D (MvPowerSeries.constantCoeff a) ⊗ₜ[S σ k] (1 : A σ k)) := by
                rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
          _ = _ := by rw [← tensor_constant σ k D h, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    right_inv := by
      intro d
      change tensorEvaluation σ k D h (d ⊗ₜ[S σ k] (1 : A σ k)) = d
      rw [tensorEvaluation_tmul, map_one, map_one, mul_one] }

@[simp] lemma equiv_tmul (d : D) (a : A σ k) :
    equiv σ k D h (d ⊗ₜ[S σ k] a) = d * algebraMap k D (MvPowerSeries.constantCoeff a) :=
  tensorEvaluation_tmul σ k D h d a

end OriginScalarBaseChange

end


/-! Flatness of the exact polynomial-to-multivariate-power-series map.
Used for the Cartier zero section and schematically dense puncture of the
literal model in the manuscript, lines 243–280. -/
noncomputable section
namespace MvPowerSeries
open scoped _root_.MvPowerSeries
variable {σ k : Type*}
instance flat_polynomial [CommRing k] [IsNoetherianRing k] [Finite σ] :
    Module.Flat (MvPolynomial σ k) (MvPowerSeries σ k) :=
  Module.Flat.of_linearEquiv (_root_.MvPowerSeries.toAdicCompletionAlgEquiv σ k).toLinearEquiv
end MvPowerSeries


/-! Quotient tensor comparison specialized by the source zero-section proof.
Keeping the genuine general comparison opaque avoids elaborating its large
coordinate-ring instances repeatedly. -/
open TensorProduct
namespace ScalarQuotientBaseChange
variable {R B D A : Type*} [CommRing R] [CommRing B] [CommRing D] [CommRing A]
  [Algebra R B] [Algebra R D] [Algebra R A]
variable (f : B →ₐ[R] D) (hf : Function.Surjective f)

abbrev ideal : Ideal (B ⊗[R] A) := (RingHom.ker f.toRingHom).map (algebraMap B (B ⊗[R] A))

def equiv : ((B ⊗[R] A) ⧸ ideal (A := A) f) ≃+* D ⊗[R] A :=
  (Algebra.TensorProduct.quotientTensorEquiv (R := R) R A B (RingHom.ker f.toRingHom)).symm.toRingEquiv |>.trans
    (Algebra.TensorProduct.congr (Ideal.quotientKerAlgEquivOfSurjective hf)
      (AlgEquiv.refl : A ≃ₐ[R] A)).toRingEquiv

lemma equiv_tmul (b : B) (a : A) :
    equiv f hf (Ideal.Quotient.mk _ (b ⊗ₜ[R] a)) = f b ⊗ₜ[R] a := by
  change Algebra.TensorProduct.congr (Ideal.quotientKerAlgEquivOfSurjective hf)
    (AlgEquiv.refl : A ≃ₐ[R] A)
    ((Algebra.TensorProduct.quotientTensorEquiv (R := R) R A B (RingHom.ker f.toRingHom)).symm
      (Ideal.Quotient.mk _ (b ⊗ₜ[R] a))) = _
  rw [Algebra.TensorProduct.quotientTensorEquiv_symm_apply_tmul]
  rfl
end ScalarQuotientBaseChange

end


/-! The true scalar-extended source chart has a regular Cartier equation
and its actual quotient is the unchanged projective-surface chart. -/
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
open KummerSourceModel
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra

local instance completedPullbackModule (i : Fin 3) : Module S (pullbackChart i) :=
  (pullbackBaseAlgebra i).toModule
local instance completedPullbackAction (i : Fin 3) : MulAction S (pullbackChart i) :=
  (completedPullbackModule i).toMulAction
local instance completedPullbackSMul (i : Fin 3) : SMul S (pullbackChart i) :=
  (completedPullbackModule i).toSMul
local instance completedPullbackTower (i : Fin 3) : IsScalarTower S S (pullbackChart i) := inferInstance
local instance completedSurfaceModule (i : Fin 3) : Module S (surfaceChart i) :=
  (surfaceOriginAlgebra i).toModule
local instance completedSeriesModule : Module S A := inferInstance

abbrev completedSourceChart (i : Fin 3) := pullbackChart i ⊗[S] A
local instance completedSourceChartCommRing (i : Fin 3) : CommRing (completedSourceChart i) := inferInstance
local instance completedSourceChartSemiring (i : Fin 3) : Semiring (completedSourceChart i) :=
  (completedSourceChartCommRing i).toSemiring

local instance completedSourceAlgebra (i : Fin 3) : Algebra S (completedSourceChart i) :=
  Algebra.TensorProduct.instAlgebra

def completedFiberParameter (i : Fin 3) : completedSourceChart i := fiberParameter i ⊗ₜ[S] 1

abbrev completedZeroIdeal (i : Fin 3) : Ideal (completedSourceChart i) :=
  (RingHom.ker (pullbackZeroEvaluation i)).map (algebraMap (pullbackChart i) (completedSourceChart i))

local instance completedQuotAlgebra (i : Fin 3) :
    Algebra S (completedSourceChart i ⧸ completedZeroIdeal i) := Ideal.Quotient.algebra S

lemma completedZeroIdeal_eq (i : Fin 3) : completedZeroIdeal i = Ideal.span {completedFiberParameter i} := by
  simp only [completedZeroIdeal, pullbackZeroEvaluation_kernel, Ideal.map_span, Set.image_singleton]
  rfl

/-- The zero-section quotient remains exactly D_i after completion. -/
def completedZeroQuotient (i : Fin 3) :
    (completedSourceChart i ⧸ completedZeroIdeal i) ≃+* surfaceChart i :=
  (ScalarQuotientBaseChange.equiv (A := A) (pullbackZeroAlg i)
    (pullbackZeroEvaluation_surjective i)).trans
      (OriginScalarBaseChange.equiv (Fin 3) ℂ (surfaceChart i) rfl)

def completedZeroEvaluation (i : Fin 3) : completedSourceChart i →+* surfaceChart i :=
  (completedZeroQuotient i).toRingHom.comp (Ideal.Quotient.mk (completedZeroIdeal i))

lemma completedZeroEvaluation_tmul (i : Fin 3) (q : pullbackChart i) (a : A) :
    completedZeroEvaluation i (q ⊗ₜ[S] a) =
      pullbackZeroEvaluation i q * algebraMap ℂ (surfaceChart i) (MvPowerSeries.constantCoeff a) := by
  change OriginScalarBaseChange.equiv (Fin 3) ℂ (surfaceChart i) rfl
    (ScalarQuotientBaseChange.equiv (A := A) (pullbackZeroAlg i)
      (pullbackZeroEvaluation_surjective i) (Ideal.Quotient.mk _ (q ⊗ₜ[S] a))) = _
  erw [ScalarQuotientBaseChange.equiv_tmul, OriginScalarBaseChange.equiv_tmul]
  rfl

lemma completedZeroEvaluation_surjective (i : Fin 3) : Function.Surjective (completedZeroEvaluation i) :=
  (completedZeroQuotient i).surjective.comp Ideal.Quotient.mk_surjective

lemma completedZeroEvaluation_kernel (i : Fin 3) :
    RingHom.ker (completedZeroEvaluation i) = Ideal.span {completedFiberParameter i} := by
  rw [← completedZeroIdeal_eq]
  ext a
  change completedZeroQuotient i (Ideal.Quotient.mk (completedZeroIdeal i) a) = 0 ↔ a ∈ completedZeroIdeal i
  rw [RingEquiv.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

lemma completedFiberParameter_regular (i : Fin 3) :
    IsSMulRegular (completedSourceChart i) (completedFiberParameter i) := by
  exact (fiberParameter_regular i).of_flat

instance completedZeroIdeal_prime (i : Fin 3) : (completedZeroIdeal i).IsPrime := by
  let : IsDomain (completedSourceChart i ⧸ completedZeroIdeal i) :=
    Function.Injective.isDomain (completedZeroQuotient i).toRingHom (completedZeroQuotient i).injective
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

end SourcePullbackChart

end

end OAI
