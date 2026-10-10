import OAI.AlgebraicGeometry.SurfaceCones.ExteriorChangeScalars

namespace OAI

/-! Homogeneous fractions and evaluation in a field. -/
noncomputable section
open _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization
namespace HomogeneousEvaluation
variable {A F σ : Type*} [CommRing A] [Field F] [SetLike σ A]
  [AddSubgroupClass σ A] (G : ℕ → σ) [GradedRing G] (e : A →+* F)

def evaluate (f : A) (hf : e f ≠ 0) : Away G f →+* F :=
  (Localization.awayLift e f (isUnit_iff_ne_zero.mpr hf)).comp
    (algebraMap (Away G f) (Localization.Away f))

lemma evaluate_mk {f : A} {d : ℕ} (hf : e f ≠ 0) (hd : f ∈ G d)
    (n : ℕ) (a : A) (ha : a ∈ G (n • d)) :
    evaluate G e f hf (Away.mk G hd n a ha) = e a / (e f)^n := by
  simp only [evaluate, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  rw [Localization.awayLift_mk _ _ _ _ (mul_inv_cancel₀ hf)]
  simp only [div_eq_mul_inv, inv_pow]

lemma evaluate_awayMap {f g x : A} {d b : ℕ}
    (hf : e f ≠ 0) (hg : e g ≠ 0) (hd : f ∈ G d) (he : g ∈ G b) (hx : x = f * g)
    (h : e x ≠ 0) (a : Away G f) :
    evaluate G e x h (awayMap G he hx a) = evaluate G e f hf a := by
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective G hd a
  rw [awayMap_mk, evaluate_mk, evaluate_mk, map_mul, map_pow, hx, map_mul, mul_pow]
  exact mul_div_mul_right _ _ (pow_ne_zero n hg)

end HomogeneousEvaluation

end

/-! Homogeneous product charts describe the intersections of coefficient charts. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace SourceSymmetry
open ExplicitCone _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization

abbrev projSection_degree (t : SectionIndex) : projSection t ∈ grading 1 :=
  SectionCompletion.linearSection_homogeneous pieces _ _

abbrev projPairChart (s t : SectionIndex) :=
  Away grading (projSection s * projSection t)

lemma projChartEquiv_localizationElem (s t : SectionIndex) (hs : Good s) :
    projChartEquiv s hs (Away.isLocalizationElem (projSection_degree s) (projSection_degree t)) =
      chartRatio s t := by
  apply Subtype.ext
  change SectionCompletion.homogeneousChartMap pieces (sectionCoefficient s)
    (sectionCoefficient_mem_piece s) (coefficient_ne_zero s)
      (Away.isLocalizationElem (projSection_degree s) (projSection_degree t)) = _
  unfold Away.isLocalizationElem
  rw [SectionCompletion.homogeneousChartMap_mk]
  simp [projSection, SectionCompletion.linearSection, chartRatio]

local instance pairChartAlgebra (s t : SectionIndex) :
    Algebra (projChart s) (projPairChart s t) :=
  (awayMap grading (projSection_degree t) rfl).toAlgebra

local instance pairChartLocalization (s t : SectionIndex) :
    IsLocalization.Away
      (Away.isLocalizationElem (projSection_degree s) (projSection_degree t)) (projPairChart s t) :=
  Away.isLocalization_mul (projSection_degree s) (projSection_degree t) rfl (by decide)

/-- The homogeneous product chart is the common field-principal open. -/
def projPairChartEquiv (s t : SectionIndex) (hs : Good s) :
    projPairChart s t ≃+* coefficientOverlap s t :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (Away.isLocalizationElem (projSection_degree s) (projSection_degree t)))
    (T := Submonoid.powers (chartRatio s t))
    (projPairChart s t) (coefficientOverlap s t) (projChartEquiv s hs).toRingEquiv (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers (projChartEquiv_localizationElem s t hs))

lemma projPairChartEquiv_awayMap (s t : SectionIndex) (hs : Good s) (a : projChart s) :
    projPairChartEquiv s t hs (awayMap grading (projSection_degree t) rfl a) =
      Subalgebra.inclusion (coefficientChart_le_overlap_left s t) (projChartEquiv s hs a) := by
  change projPairChartEquiv s t hs (algebraMap (projChart s) (projPairChart s t) a) = _
  simp only [projPairChartEquiv, IsLocalization.ringEquivOfRingEquiv_eq]
  rfl

/-- The same evaluation at one used in constructing the section ring. -/
abbrev projEval (f : SectionCompletion.polynomials pieces)
    (hf : SectionCompletion.evaluateOne pieces f ≠ 0) : Away grading f →+* L :=
  HomogeneousEvaluation.evaluate grading (SectionCompletion.evaluateOne pieces) f hf

lemma projEval_awayMap {f g x : SectionCompletion.polynomials pieces} {d e : ℕ}
    (hf : SectionCompletion.evaluateOne pieces f ≠ 0)
    (hg : SectionCompletion.evaluateOne pieces g ≠ 0)
    (hd : f ∈ grading d) (he : g ∈ grading e) (hx : x = f * g)
    (h : SectionCompletion.evaluateOne pieces x ≠ 0) (a : Away grading f) :
    projEval x h (awayMap grading he hx a) = projEval f hf a :=
  HomogeneousEvaluation.evaluate_awayMap grading (SectionCompletion.evaluateOne pieces)
    hf hg hd he hx h a

lemma projSection_eval_ne_zero (s : SectionIndex) :
    SectionCompletion.evaluateOne pieces (projSection s) ≠ 0 := by
  simpa only [SectionCompletion.evaluateOne_linearSection] using coefficient_ne_zero s

lemma projEval_eq_chart (s : SectionIndex) (hs : Good s) (a : projChart s) :
    projEval (projSection s) (projSection_eval_ne_zero s) a = (projChartEquiv s hs a : L) := by
  rfl

lemma projPairEval_eq (s t : SectionIndex) (hs : Good s)
    (h : SectionCompletion.evaluateOne pieces (projSection s * projSection t) ≠ 0)
    (a : projPairChart s t) :
    projEval (projSection s * projSection t) h a = (projPairChartEquiv s t hs a : L) := by
  have hh : projEval (projSection s * projSection t) h =
      (coefficientOverlap s t).val.toRingHom.comp (projPairChartEquiv s t hs).toRingHom := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (Away.isLocalizationElem (projSection_degree s) (projSection_degree t)))
    apply RingHom.ext
    intro z
    change projEval _ h (awayMap grading (projSection_degree t) rfl z) = _
    have h₁ := projEval_awayMap (projSection_eval_ne_zero s) (projSection_eval_ne_zero t)
      (projSection_degree s) (projSection_degree t) rfl h z
    have h₂ := projEval_eq_chart s hs z
    have h₃ := congrArg (fun x : coefficientOverlap s t => (x : L))
      (projPairChartEquiv_awayMap s t hs z)
    exact h₁.trans (h₂.trans h₃.symm)
  exact DFunLike.congr_fun hh a

lemma projPairChartEquiv_awayMap_right (s t : SectionIndex) (hs : Good s) (ht : Good t)
    (a : projChart t) :
    projPairChartEquiv s t hs (awayMap grading (projSection_degree s) (mul_comm _ _) a) =
      Subalgebra.inclusion (coefficientChart_le_overlap_right s t) (projChartEquiv t ht a) := by
  apply Subtype.ext
  have h : SectionCompletion.evaluateOne pieces (projSection s * projSection t) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero (projSection_eval_ne_zero s) (projSection_eval_ne_zero t)
  have h₁ := projPairEval_eq s t hs h (awayMap grading (projSection_degree s) (mul_comm _ _) a)
  have h₂ := projEval_awayMap (projSection_eval_ne_zero t) (projSection_eval_ne_zero s)
    (projSection_degree t) (projSection_degree s) (mul_comm _ _) h a
  exact h₁.symm.trans (h₂.trans (projEval_eq_chart t ht a))


end SourceSymmetry

end

/-! Commuting squares for the coefficient-chart inclusions. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization
namespace SourceSymmetry
open ExplicitCone

instance pairChartEquiv_isIso (s t : SectionIndex) (hs : Good s) :
    IsIso (CommRingCat.ofHom (R := projPairChart s t) (S := coefficientOverlap s t)
      (projPairChartEquiv s t hs).toRingHom) :=
by
  refine ⟨⟨CommRingCat.ofHom (projPairChartEquiv s t hs).symm.toRingHom, ?_, ?_⟩⟩
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    exact (projPairChartEquiv s t hs).symm_apply_apply
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    exact (projPairChartEquiv s t hs).apply_symm_apply

lemma pairChart_left_square (s t : SectionIndex) (hs : Good s) :
    CommRingCat.ofHom (projChartEquiv s hs).toRingHom ≫
      CommRingCat.ofHom (Subalgebra.inclusion (coefficientChart_le_overlap_left s t)).toRingHom =
      CommRingCat.ofHom (awayMap grading (projSection_degree t) rfl) ≫
        CommRingCat.ofHom (projPairChartEquiv s t hs).toRingHom := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (projPairChartEquiv_awayMap s t hs a).symm

lemma pairChart_right_square (s t : SectionIndex) (hs : Good s) (ht : Good t) :
    CommRingCat.ofHom (projChartEquiv t ht).toRingHom ≫
      CommRingCat.ofHom (Subalgebra.inclusion (coefficientChart_le_overlap_right s t)).toRingHom =
      CommRingCat.ofHom (awayMap grading (projSection_degree s) (mul_comm _ _)) ≫
        CommRingCat.ofHom (projPairChartEquiv s t hs).toRingHom := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (projPairChartEquiv_awayMap_right s t hs ht a).symm

end SourceSymmetry

end

/-! Compatibility of Proj away maps in a fixed degree. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization
namespace AlgebraicGeometry.Proj
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Proj
universe u
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
lemma awayMap_awayι_fixed_degree {m n : ℕ} {f g x : A}
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hx : x = f * g)
    (hd : x ∈ 𝒜 (m+n)) (hmn : 0 < m+n) :
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (awayMap 𝒜 hg hx)) ≫ _root_.AlgebraicGeometry.Proj.awayι 𝒜 f hf hm =
      _root_.AlgebraicGeometry.Proj.awayι 𝒜 x hd hmn := _root_.AlgebraicGeometry.Proj.SpecMap_awayMap_awayι 𝒜 hf hm hg hx
end AlgebraicGeometry.Proj

end

/-! The two maps from a homogeneous product chart. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization
namespace SourceSymmetry
open ExplicitCone
abbrev projPairDegree (s t : SectionIndex) :
    projSection s * projSection t ∈ grading (1 + 1) :=
  SetLike.mul_mem_graded (projSection_degree s) (projSection_degree t)
lemma pair_left_away_spec (s t : SectionIndex) :
    Spec.map (CommRingCat.ofHom (awayMap grading (projSection_degree t) rfl)) ≫
      Proj.awayι grading (projSection s) (projSection_degree s) (by decide) =
      Proj.awayι grading (projSection s * projSection t) (projPairDegree s t) (by decide) :=
  Proj.awayMap_awayι_fixed_degree grading (projSection_degree s) (by decide)
    (projSection_degree t) rfl (projPairDegree s t) (by decide)
lemma pair_right_away_spec (s t : SectionIndex) :
    Spec.map (CommRingCat.ofHom (awayMap grading (projSection_degree s) (mul_comm _ _))) ≫
      Proj.awayι grading (projSection t) (projSection_degree t) (by decide) =
      Proj.awayι grading (projSection s * projSection t) (projPairDegree s t) (by decide) :=
  Proj.awayMap_awayι_fixed_degree grading (projSection_degree t) (by decide)
    (projSection_degree s) (mul_comm _ _) (projPairDegree s t) (by decide)
end SourceSymmetry

end

/-! Transport of homogeneous product charts. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
lemma specChart_square {A B C D : CommRingCat} {X : _root_.AlgebraicGeometry.Scheme}
    (f : A ⟶ B) (g : C ⟶ D) (e : A ⟶ C) (e' : B ⟶ D)
    (i : _root_.AlgebraicGeometry.Spec A ⟶ X) (j : _root_.AlgebraicGeometry.Spec B ⟶ X)
    (h : e ≫ g = f ≫ e') (hi : _root_.AlgebraicGeometry.Spec.map f ≫ i = j) :
    _root_.AlgebraicGeometry.Spec.map g ≫ (_root_.AlgebraicGeometry.Spec.map e ≫ i) = _root_.AlgebraicGeometry.Spec.map e' ≫ j := by
  rw [← Category.assoc, ← _root_.AlgebraicGeometry.Spec.map_comp, h, _root_.AlgebraicGeometry.Spec.map_comp, Category.assoc, hi]

def openIsoOfOpensRange {X Y : _root_.AlgebraicGeometry.Scheme} (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsOpenImmersion f]
    (U : Y.Opens) (h : f.opensRange = U) : X ≅ U.toScheme :=
  _root_.AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq f U.ι (by
    have he := congrArg (fun V : Y.Opens => (V : Set Y)) h
    exact he.trans (_root_.AlgebraicGeometry.Scheme.Opens.range_ι U).symm)
end AlgebraicGeometry

end

/-! Geometric realization of the intersections in the twelve-chart cover. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace SourceSymmetry
open ExplicitCone _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization

/-- The common open inclusion into the projective surface. -/
def coefficientOverlapIota (s t : SectionIndex) (hs : Good s) :
    Spec (CommRingCat.of (coefficientOverlap s t)) ⟶ projectiveSurface :=
  Spec.map (CommRingCat.ofHom (projPairChartEquiv s t hs).toRingHom) ≫
    Proj.awayι grading (projSection s * projSection t) (projPairDegree s t) (by decide)

lemma coefficientIota_eq (s : SectionIndex) (hs : Good s) :
    coefficientIota s hs = Spec.map (CommRingCat.ofHom (projChartEquiv s hs).toRingHom) ≫
      Proj.awayι grading (projSection s) (projSection_degree s) (by decide) := by
  rfl

instance coefficientOverlapIota_open (s t : SectionIndex) (hs : Good s) :
    IsOpenImmersion (coefficientOverlapIota s t hs) := by
  dsimp only [coefficientOverlapIota]
  let : IsIso (CommRingCat.ofHom (R := projPairChart s t) (S := coefficientOverlap s t)
      (projPairChartEquiv s t hs).toRingHom) := pairChartEquiv_isIso s t hs
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (R := projPairChart s t) (S := coefficientOverlap s t)
      (projPairChartEquiv s t hs).toRingHom)) :=
    inferInstance
  exact IsOpenImmersion.comp
    (Spec.map (CommRingCat.ofHom (R := projPairChart s t) (S := coefficientOverlap s t)
      (projPairChartEquiv s t hs).toRingHom))
    (Proj.awayι grading (projSection s * projSection t) (projPairDegree s t) (by decide))

lemma coefficientOverlapIota_left (s t : SectionIndex) (hs : Good s) :
    Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (coefficientChart_le_overlap_left s t)).toRingHom) ≫
        coefficientIota s hs = coefficientOverlapIota s t hs := by
  rw [coefficientIota_eq]
  exact specChart_square _ _ _ _ _ _ (pairChart_left_square s t hs)
    (pair_left_away_spec s t)

lemma coefficientOverlapIota_right (s t : SectionIndex) (hs : Good s) (ht : Good t) :
    Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (coefficientChart_le_overlap_right s t)).toRingHom) ≫
        coefficientIota t ht = coefficientOverlapIota s t hs := by
  rw [coefficientIota_eq]
  exact specChart_square _ _ _ _ _ _ (pairChart_right_square s t hs ht)
    (pair_right_away_spec s t)

lemma coefficientOverlapIota_opensRange (s t : SectionIndex) (hs : Good s) :
    (coefficientOverlapIota s t hs).opensRange =
      Proj.basicOpen grading (projSection s) ⊓ Proj.basicOpen grading (projSection t) := by
  change (Spec.map _ ≫ Proj.awayι grading _ _ _).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι, Proj.basicOpen_mul]

/-- The scheme overlap. This isomorphism is -/
def coefficientOverlapIso (s t : SectionIndex) (hs : Good s) :
    Spec (CommRingCat.of (coefficientOverlap s t)) ≅
      (Proj.basicOpen grading (projSection s) ⊓ Proj.basicOpen grading (projSection t)).toScheme :=
  openIsoOfOpensRange (coefficientOverlapIota s t hs) _
    (coefficientOverlapIota_opensRange s t hs)

end SourceSymmetry

end

/-! The cotangent comparisons preserve universal differential sections. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCotangent
universe u
variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [IsOpenImmersion f]

lemma openIso_hom : (openIso f g).hom =
    openInverseHomEquiv f g _ (𝟙 (sheaf (f ≫ g))) := rfl

lemma homEquiv_id : homEquiv g (sheaf g) (𝟙 _) = derivation g := by
  ext U a
  rfl

lemma restrictDerivation_postcomp {M N : Y.Modules}
    (D : PresheafOfModulesOfCommRing.Derivation' (M.val) (constants g)) (a : M ⟶ N) :
    restrictDerivation f g N (D.postcomp a.val) =
      (restrictDerivation f g M D).postcomp
        ((Scheme.Modules.restrictFunctor f).map a).val := by
  ext U x
  rfl

omit [IsOpenImmersion f] in
lemma derivation_postcomp_comp {M N P : X.Modules}
    (D : PresheafOfModulesOfCommRing.Derivation' (M.val) (constants (f ≫ g))) (a : M ⟶ N) (b : N ⟶ P) :
    (D.postcomp a.val).postcomp b.val = D.postcomp (a ≫ b).val := by
  ext U x
  rfl

lemma restrict_homEquiv (N : X.Modules) (a : (sheaf g).restrict f ⟶ N) :
    pullDerivation f g N
      (homEquiv g _ ((Scheme.Modules.restrictAdjunction f).homEquiv _ _ a)) =
      (restrictDerivation f g _ (derivation g)).postcomp a.val := by
  rw [homEquiv_apply]
  dsimp only [pullDerivation]
  rw [restrictDerivation_postcomp, derivation_postcomp_comp]
  congr 1
  exact congrArg (fun b : (sheaf g).restrict f ⟶ N => b.val)
    (((Scheme.Modules.restrictAdjunction f).homEquiv _ _).symm_apply_apply a)

lemma openIso_derivation :
    (restrictDerivation f g _ (derivation g)).postcomp (openIso f g).hom.val =
      derivation (f ≫ g) := by
  rw [openIso_hom, ← restrict_homEquiv, openInverseHomEquiv_eval, homEquiv_id]
  exact pull_push f g _ _

end ActualCotangent

end

/-! The affine cotangent comparison on coordinate differentials. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCotangent
universe u
variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]

local instance (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))

local instance (priority := 3000) (M : (Spec (.of R)).Modules)
    (U : (Spec (.of R)).Opens) : Module Γ(Spec (.of R),U) Γ(M,U) :=
  (M.val.obj (.op U)).isModule
local instance (priority := 2000) (M : (Spec (.of R)).Modules)
    (U : (Spec (.of R)).Opens) : Module R Γ(M,U) :=
  inferInstanceAs (Module R ((modulesSpecToSheaf.obj M).obj.obj (.op U)))
local instance (M : (Spec (.of R)).Modules) : Module k Γ(M,⊤) :=
  Module.compHom Γ(M,⊤) (algebraMap k R)
local instance (M : (Spec (.of R)).Modules) : IsScalarTower k R Γ(M,⊤) :=
  IsScalarTower.of_compHom k R _

lemma affineIso_inv : (affineIso k R).inv =
    affineHomEquiv k R _ (𝟙 (sheaf (Spec.map (CommRingCat.ofHom (algebraMap k R))))) := rfl

lemma affineIso_inv_adjoint :
    (tilde.adjunction (R := CommRingCat.of R)).homEquiv _ _ (affineIso k R).inv =
      ModuleCat.ofHom (show Derivation k R Γ(sheaf (Spec.map (CommRingCat.ofHom (algebraMap k R))), ⊤) from
        AffineDerivation.global k R _
          (derivation (Spec.map (CommRingCat.ofHom (algebraMap k R))))).liftKaehlerDifferential := by
  rw [affineIso_inv, affineHomEquiv_adjoint, homEquiv_id]
  rfl

lemma affineIso_inv_D (x : R) :
    ((moduleSpecΓFunctor (R := CommRingCat.of R)).map (affineIso k R).inv).hom
      (((tilde.adjunction (R := CommRingCat.of R)).unit.app (affineModule (k := k) R)).hom
        (KaehlerDifferential.D k R x)) =
      (derivation (Spec.map (CommRingCat.ofHom (algebraMap k R)))).d
        (algebraMap R Γ(Spec (.of R),⊤) x) := by
  have h := congrArg (fun a : affineModule (k := k) R ⟶
      (moduleSpecΓFunctor (R := CommRingCat.of R)).obj
        (sheaf (Spec.map (CommRingCat.ofHom (algebraMap k R)))) =>
      a.hom (KaehlerDifferential.D k R x)) (affineIso_inv_adjoint k R)
  change _ = (show Derivation k R Γ(sheaf (Spec.map (CommRingCat.ofHom (algebraMap k R))), ⊤) from
    AffineDerivation.global k R _
      (derivation (Spec.map (CommRingCat.ofHom (algebraMap k R))))).liftKaehlerDifferential
      (KaehlerDifferential.D k R x) at h
  rw [Derivation.liftKaehlerDifferential_comp_D] at h
  exact h

end ActualCotangent

end

/-! Coordinate differentials on affine opens of a scheme. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCotangent
universe u
variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [IsOpenImmersion f]

lemma openIso_D (U : X.Opens) (a : Γ(X,U)) :
    (openIso f g).hom.val.app (.op U)
      ((derivation g).d ((f.appIso U).inv a)) =
      (derivation (f ≫ g)).d a :=
  congrArg (fun D => D.d (X := .op U) a) (openIso_derivation f g)

lemma openIso_inv_D (U : X.Opens) (a : Γ(X,U)) :
    (openIso f g).inv.val.app (.op U) ((derivation (f ≫ g)).d a) =
      (derivation g).d ((f.appIso U).inv a) := by
  rw [← openIso_D f g U a]
  exact congrArg (fun b : (sheaf g).restrict f ⟶ (sheaf g).restrict f =>
    b.val.app (.op U) ((derivation g).d ((f.appIso U).inv a))) (openIso f g).hom_inv_id

lemma eqToIso_inv_D {f g : X ⟶ Spec (.of k)} (h : f = g)
    (U : X.Opens) (a : Γ(X,U)) :
    (eqToIso (congrArg sheaf h)).inv.val.app (.op U) ((derivation g).d a) =
      (derivation f).d a := by
  subst g
  rfl

end ActualCotangent

end

/-! Section formulas for compositions of module-sheaf isomorphisms. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
universe u
variable {X : Scheme.{u}} {M N P : X.Modules}
lemma iso_trans_inv_apply (e : M ≅ N) (f : N ≅ P) (U : X.Opens) (x : Γ(P,U)) :
    (e ≪≫ f).inv.val.app (.op U) x = e.inv.val.app (.op U) (f.inv.val.app (.op U) x) := rfl
end ActualSections

end

/-! Section comparison equations for sheaf isomorphisms. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
universe u
variable {R : CommRingCat.{u}} {M N : (Spec R).Modules}
lemma affine_global_app (f : M ⟶ N) (x : Γ(M,⊤)) :
    ((moduleSpecΓFunctor (R := R)).map f).hom x = f.val.app (.op ⊤) x := rfl
lemma tilde_unit_top (P : ModuleCat.{u} R) (x : P) :
    (((tilde.adjunction (R := R)).unit.app P).hom x : Γ(tilde P,⊤)) =
      tilde.toOpen (R := R) P ⊤ x := rfl
end ActualSections

end

/-! Composition of section comparison equations. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
universe u
variable {X : Scheme.{u}} {M N P Q : X.Modules}
lemma iso_chain_inv_apply (e : M ≅ N) (f : N ≅ P) (g : P ≅ Q) (U : X.Opens)
    (a : Γ(Q,U)) (b : Γ(P,U)) (c : Γ(N,U)) (d : Γ(M,U))
    (ha : g.inv.val.app (.op U) a = b) (hb : f.inv.val.app (.op U) b = c)
    (hc : e.inv.val.app (.op U) c = d) :
    (e ≪≫ f ≪≫ g).inv.val.app (.op U) a = d := by
  change e.inv.val.app (.op U) (f.inv.val.app (.op U) (g.inv.val.app (.op U) a)) = d
  rw [ha, hb, hc]

lemma iso_inv_apply_congr (e f : M ≅ N) (h : e = f) (U : X.Opens) (a : Γ(N,U)) :
    e.inv.val.app (.op U) a = f.inv.val.app (.op U) a := by subst f; rfl

variable {R : CommRingCat.{u}} (T : ModuleCat.{u} R) (S : (Spec R).Modules)
lemma affine_map_unit (f : tilde T ⟶ S) (a : T) :
    f.val.app (.op ⊤) (tilde.toOpen (R := R) T ⊤ a) =
      ((moduleSpecΓFunctor (R := R)).map f).hom
        (((tilde.adjunction (R := R)).unit.app T).hom a) := rfl
end ActualSections

end

/-! The open affine cotangent comparison on coordinate differential sections. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCotangent
attribute [local irreducible] sheaf affineIso openIso openAffineIso derivation
universe u
variable {k : Type u} [CommRing k] {Y : Scheme.{u}}
  (g : Y ⟶ Spec (.of k))
variable (R : Type u) [CommRing R] [Algebra k R]
local instance (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))

lemma openAffineIso_eq (i : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion i]
    (h : i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k R))) :
    openAffineIso g R i h = openIso i g ≪≫ eqToIso (congrArg sheaf h) ≪≫ affineIso k R := by
  unfold openAffineIso
  rfl

lemma affineIso_inv_D_section (x : R) :
    (affineIso k R).inv.val.app (.op ⊤)
      (tilde.toOpen (R := .of R) (affineModule (k := k) R) ⊤ (KaehlerDifferential.D k R x)) =
      (derivation (Spec.map (CommRingCat.ofHom (algebraMap k R)))).d
        (algebraMap R Γ(Spec (.of R),⊤) x) := by
  exact (ActualSections.affine_map_unit (R := CommRingCat.of R)
    (affineModule (k := k) R) (sheaf (Spec.map (CommRingCat.ofHom (algebraMap k R))))
    (affineIso k R).inv (KaehlerDifferential.D k R x)).trans (affineIso_inv_D k R x)

end ActualCotangent

end

/-! Evaluation of coordinate differential sections through the cotangent comparison. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
universe u
variable {X : Scheme.{u}} {M N P Q : X.Modules}
def moduleApply (f : M ⟶ N) (U : X.Opens) : Γ(M,U) → Γ(N,U) := f.app U
def isoInv (e : M ≅ N) (U : X.Opens) : Γ(N,U) → Γ(M,U) := moduleApply e.inv U
lemma isoInv_trans (e : M ≅ N) (f : N ≅ P) (U : X.Opens) (x : Γ(P,U)) :
    isoInv (e ≪≫ f) U x = isoInv e U (isoInv f U x) := rfl
lemma isoInv_chain (e : M ≅ N) (f : N ≅ P) (g : P ≅ Q) (U : X.Opens)
    (a : Γ(Q,U)) (b : Γ(P,U)) (c : Γ(N,U)) (d : Γ(M,U))
    (ha : isoInv g U a = b) (hb : isoInv f U b = c) (hc : isoInv e U c = d) :
    isoInv (e ≪≫ f ≪≫ g) U a = d := by
  rw [isoInv_trans, isoInv_trans, ha, hb, hc]
lemma isoInv_congr (e f : M ≅ N) (h : e = f) (U : X.Opens) (a : Γ(N,U)) :
    isoInv e U a = isoInv f U a := by rw [h]
end ActualSections
namespace ActualSections
universe u
variable {X : Scheme.{u}} {M N : X.Modules}
lemma isoInv_val (e : M ≅ N) (U : X.Opens) (x : Γ(N,U)) :
    isoInv e U x = e.inv.val.app (.op U) x := rfl
end ActualSections

end

noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCotangent
attribute [local irreducible] sheaf affineIso openIso openAffineIso derivation
universe u
variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  (g : Y ⟶ Spec (.of k)) (R : Type u) [CommRing R] [Algebra k R]
local instance (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))
lemma affineInv_eval_D (x : R) : ActualSections.isoInv (affineIso k R) ⊤
      (tilde.toOpen (R := .of R) (affineModule (k := k) R) ⊤ (KaehlerDifferential.D k R x)) =
      (derivation (Spec.map (CommRingCat.ofHom (algebraMap k R)))).d
        (algebraMap R Γ(Spec (.of R),⊤) x) := affineIso_inv_D_section (k := k) R x
lemma eqToIso_eval_D {f g : X ⟶ Spec (.of k)} (h : f = g) (U : X.Opens) (a : Γ(X,U)) :
    ActualSections.isoInv (eqToIso (congrArg sheaf h)) U ((derivation g).d a) =
      (derivation f).d a := by
  subst g
  rfl
lemma openInv_eval_D (i : X ⟶ Y) [IsOpenImmersion i] (U : X.Opens) (a : Γ(X,U)) :
    ActualSections.isoInv (openIso i g) U ((derivation (i ≫ g)).d a) =
      (derivation g).d ((i.appIso U).inv a) := openIso_inv_D i g U a
end ActualCotangent

end

/-! Evaluation of sections through a sheaf isomorphism. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCotangent
attribute [local irreducible] sheaf affineIso openIso openAffineIso derivation
universe u
variable {k : Type u} [CommRing k] {Y : Scheme.{u}}
  (g : Y ⟶ Spec (.of k)) (R : Type u) [CommRing R] [Algebra k R]
local instance (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))

lemma openAffineIso_inv_D_wrapped (i : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion i]
    (h : i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k R))) (x : R) :
    ActualSections.isoInv (openAffineIso g R i h) ⊤
      (tilde.toOpen (R := .of R) (affineModule (k := k) R) ⊤ (KaehlerDifferential.D k R x)) =
      (derivation g).d (X := .op (i ''ᵁ ⊤)) ((i.appIso ⊤).inv (algebraMap R Γ(Spec (.of R),⊤) x)) := by
  have ha : ActualSections.isoInv (affineIso k R) ⊤
      (tilde.toOpen (R := .of R) (affineModule (k := k) R) ⊤ (KaehlerDifferential.D k R x)) =
      (derivation (Spec.map (CommRingCat.ofHom (algebraMap k R)))).d
        (algebraMap R Γ(Spec (.of R),⊤) x) := affineInv_eval_D (k := k) R x
  have hb : ActualSections.isoInv (eqToIso (congrArg sheaf h)) ⊤
      ((derivation (Spec.map (CommRingCat.ofHom (algebraMap k R)))).d
        (algebraMap R Γ(Spec (.of R),⊤) x)) =
      (derivation (i ≫ g)).d (algebraMap R Γ(Spec (.of R),⊤) x) :=
    eqToIso_eval_D h ⊤ (algebraMap R Γ(Spec (.of R),⊤) x)
  have hc : ActualSections.isoInv (openIso i g) ⊤
      ((derivation (i ≫ g)).d (algebraMap R Γ(Spec (.of R),⊤) x)) =
      (derivation g).d (X := .op (i ''ᵁ ⊤)) ((i.appIso ⊤).inv (algebraMap R Γ(Spec (.of R),⊤) x)) :=
    openInv_eval_D g i ⊤ (algebraMap R Γ(Spec (.of R),⊤) x)
  rw [openAffineIso_eq]
  exact ActualSections.isoInv_chain (openIso i g) (eqToIso (congrArg sheaf h))
    (affineIso k R) ⊤ _ _ _ _ ha hb hc
end ActualCotangent

end

/-! The open affine cotangent comparison on differential sections. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCotangent
attribute [local irreducible] sheaf affineIso openIso openAffineIso derivation
universe u
variable {k : Type u} [CommRing k] {Y : Scheme.{u}}
  (g : Y ⟶ Spec (.of k))
variable (R : Type u) [CommRing R] [Algebra k R]
local instance (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))

lemma openAffineIso_inv_D (i : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion i]
    (h : i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k R))) (x : R) :
    ActualSections.isoInv (openAffineIso g R i h) ⊤
      (tilde.toOpen (R := .of R) (affineModule (k := k) R) ⊤ (KaehlerDifferential.D k R x)) =
      (derivation g).d (X := .op (i ''ᵁ ⊤)) ((i.appIso ⊤).inv (algebraMap R Γ(Spec (.of R),⊤) x)) := openAffineIso_inv_D_wrapped g R i h x


end ActualCotangent

end

/-! Wedge sections of exterior sheaves and their functoriality. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualExterior
universe u
variable {X Y : Scheme.{u}}

local instance (U : X.Opens) : CommRing ((X.ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj (.op U)))

/-- The wedge of sections, followed by the sheafification map. -/
def wedgeSection (M : X.Modules) (n : ℕ) (U : X.Opens) (z : Fin n → Γ(M,U)) :
    Γ((sheafFunctor X n).obj M,U) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (presheaf M.val n)).app (.op U)) (ModuleCat.exteriorPower.mk (M := M.val.obj (.op U)) z)

lemma wedgeSection_map (M : X.Modules) (n : ℕ) {U V : X.Opens} (h : U ≤ V)
    (z : Fin n → Γ(M,V)) :
    ((sheafFunctor X n).obj M).val.map (homOfLE h).op (wedgeSection M n V z) =
      wedgeSection M n U (fun i => M.val.map (homOfLE h).op (z i)) := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (presheaf M.val n)
  have hn := PresheafOfModules.naturality_apply η (homOfLE h).op
    (ModuleCat.exteriorPower.mk (M := M.val.obj (.op V)) z)
  change η.app (.op U) (powerMap (R := X.presheaf) M.val n (homOfLE h).op
    (ModuleCat.exteriorPower.mk (M := M.val.obj (.op V)) z)) = _ at hn
  erw [powerMap_ι] at hn
  exact hn.symm

lemma map_wedgeSection {M N : X.Modules} (a : M ⟶ N) (n : ℕ) (U : X.Opens)
    (z : Fin n → Γ(M,U)) :
    ((sheafFunctor X n).map a).val.app (.op U) (wedgeSection M n U z) =
      wedgeSection N n U (fun i => a.val.app (.op U) (z i)) := by
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
    (presheafMap a.val n)
  have hh := congrArg (fun b : presheaf M.val n ⟶
      ((sheafFunctor X n).obj N).val => b.app (.op U) (ModuleCat.exteriorPower.mk (M := M.val.obj (.op U)) z)) hn
  change (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (presheaf N.val n)).app (.op U))
      (ModuleCat.exteriorPower.map (a.val.app (.op U)) n (ModuleCat.exteriorPower.mk (M := M.val.obj (.op U)) z)) = _ at hh
  erw [ModuleCat.exteriorPower.map_mk] at hh
  exact hh.symm

end ActualExterior

end

/-! Wedge sections commute with open restriction. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualExterior
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

local instance (U : X.Opens) : CommRing ((X.ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj (.op U)))
local instance (U : Y.Opens) : CommRing ((Y.ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing (Y.sheaf.obj.obj (.op U)))

lemma reindexIso_mk (M : Y.Modules) (n : ℕ) (U : X.Opens)
    (z : Fin n → Γ(M, f ''ᵁ U)) :
    ((reindexIso f.opensFunctor (openRingIso f) M.val n).hom.app (.op U))
      (ModuleCat.exteriorPower.mk (M := M.val.obj (.op (f ''ᵁ U))) z) =
      ModuleCat.exteriorPower.mk (M := (M.restrict f).val.obj (.op U)) z := by
  exact reindexIso_apply_mk f.opensFunctor (openRingIso f) M.val n (.op U) z

lemma sheafify_map_unit {P Q : PresheafOfModules X.ringCatSheaf.obj}
    (a : P ⟶ Q) (U : X.Opens) (x : P.obj (.op U)) :
    ((schemeSheafification X).map a).val.app (.op U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app
        (.op U) x) =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app Q).app
        (.op U) (a.app (.op U) x)) := by
  exact (congrArg (fun b : P ⟶ ((schemeSheafification X).obj Q).val => b.app (.op U) x)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality a)).symm

lemma openSheafifyMap_unit (P : PresheafOfModules Y.ringCatSheaf.obj) (U : X.Opens)
    (x : P.obj (.op (f ''ᵁ U))) :
    (openSheafifyMap f P).val.app (.op U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((reindex f.opensFunctor (openRingIso f)).obj P)).app (.op U) x) =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P).app
        (.op (f ''ᵁ U)) x) := by
  exact congrArg (fun b : ((reindex f.opensFunctor (openRingIso f)).obj P) ⟶
      (((schemeSheafification Y).obj P).restrict f).val => b.app (.op U) x)
    (ModuleSheafification.comparison_unit f.opensFunctor (openRingHom f) P)

lemma openIso_wedgeSection (M : Y.Modules) (n : ℕ) (U : X.Opens)
    (z : Fin n → Γ(M,f ''ᵁ U)) :
    (openIso f M n).hom.val.app (.op U) (wedgeSection M n (f ''ᵁ U) z) =
      wedgeSection (M.restrict f) n U z := by
  rw [show wedgeSection M n (f ''ᵁ U) z =
      (openSheafifyMap f (presheaf M.val n)).val.app (.op U)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((reindex f.opensFunctor (openRingIso f)).obj (presheaf M.val n))).app (.op U)
          (ModuleCat.exteriorPower.mk (M := M.val.obj (.op (f ''ᵁ U))) z)) from (openSheafifyMap_unit f _ U _).symm]
  dsimp only [openIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  let P := (schemeSheafification X).obj
    ((reindex f.opensFunctor (openRingIso f)).obj (presheaf M.val n))
  let x : P.val.obj (.op U) :=
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((reindex f.opensFunctor (openRingIso f)).obj (presheaf M.val n))).app (.op U)
      (ModuleCat.exteriorPower.mk (M := M.val.obj (.op (f ''ᵁ U))) z))
  have hc : (@asIso _ _ _ _ (openSheafifyMap f (presheaf M.val n))
      (openSheafifyMap_isIso f (presheaf M.val n))).inv.val.app (.op U)
      ((openSheafifyMap f (presheaf M.val n)).val.app (.op U) x) = x :=
    congrArg (fun a : P ⟶ P => a.val.app (.op U) x)
      (@asIso _ _ _ _ (openSheafifyMap f (presheaf M.val n))
      (openSheafifyMap_isIso f (presheaf M.val n))).hom_inv_id
  change ((schemeSheafification X).map
      (reindexIso f.opensFunctor (openRingIso f) M.val n).hom).val.app (.op U)
      ((@asIso _ _ _ _ (openSheafifyMap f (presheaf M.val n))
      (openSheafifyMap_isIso f (presheaf M.val n))).inv.val.app (.op U)
        ((openSheafifyMap f (presheaf M.val n)).val.app (.op U) x)) = _
  rw [hc]
  dsimp only [x]
  erw [sheafify_map_unit]
  exact congrArg (fun v =>
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (presheaf ((reindex f.opensFunctor (openRingIso f)).obj M.val) n)).app (.op U)) v)
    (reindexIso_mk f M n U z)

end ActualExterior

end

/-! Cancellation formulas for section maps of module-sheaf isomorphisms. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
universe u
variable {X : Scheme.{u}} {M N : X.Modules}
lemma iso_inv_hom_apply (e : M ≅ N) (U : X.Opens) (x : Γ(M,U)) :
    e.inv.val.app (.op U) (e.hom.val.app (.op U) x) = x :=
  congrArg (fun a : M ⟶ M => a.val.app (.op U) x) e.hom_inv_id
lemma iso_hom_inv_apply (e : M ≅ N) (U : X.Opens) (x : Γ(N,U)) :
    e.hom.val.app (.op U) (e.inv.val.app (.op U) x) = x :=
  congrArg (fun a : N ⟶ N => a.val.app (.op U) x) e.inv_hom_id
end ActualSections

end

end OAI
