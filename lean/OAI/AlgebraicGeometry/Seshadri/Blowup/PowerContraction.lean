import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.PointSmoothness
import OAI.AlgebraicGeometry.Seshadri.Blowup.OrderContraction

namespace OAI

section
namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct ReesGrading
open MaximalSeshadri.Geometry MaximalSeshadri.IdealPullback
variable (K : Type) [Field K]

theorem blowup_power_contraction {A : Type} [CommRing A] [Algebra (PlaneRing K) A]
    [Module.Flat (PlaneRing K) A]
    {B : Scheme} {π : B ⟶ Spec (CommRingCat.of A)}
    (hπ : IsBlowup (specIdeal ((originIdeal K).map (algebraMap (PlaneRing K) A))) π)
    (m : ℕ) :
    (((specIdeal ((originIdeal K).map (algebraMap (PlaneRing K) A))).comap π)^m).map π =
      specIdeal (((originIdeal K).map (algebraMap (PlaneRing K) A))^m) := by
  let J : Ideal A := (originIdeal K).map (algebraMap (PlaneRing K) A)
  let S := chart (originIdeal K) (coordinate K 0)
  let : Algebra (PlaneRing K) S := (chartBase (originIdeal K) (coordinate K 0)).toAlgebra
  let C := A ⊗[PlaneRing K] S
  let α : A →+* C := algebraMap A C
  let β : S →+* C := (Algebra.TensorProduct.includeRight (R := PlaneRing K) (A := A)).toRingHom
  have hcomm : α.comp (algebraMap (PlaneRing K) A) =
      β.comp (chartBase (originIdeal K) (coordinate K 0)) := by
    apply RingHom.ext
    intro x
    change (algebraMap (PlaneRing K) A) x ⊗ₜ[PlaneRing K] (1 : S) =
      (1 : A) ⊗ₜ[PlaneRing K] (algebraMap (PlaneRing K) S) x
    simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  have hmap : J.map α = (exceptionalChartIdeal K 0).map β := by
    change ((originIdeal K).map _).map _ = _
    rw [Ideal.map_map, hcomm, ← Ideal.map_map, map_ideal_principal]
    rfl
  have hf : InvertiblePullbackIdeal (specIdeal J) (Spec.map (CommRingCat.ofHom α)) := by
    apply InvertibleLocal.invertible_Spec_of_span_regular J α
      (β (chartBase (originIdeal K) (coordinate K 0) (MvPolynomial.X 0)))
    · exact InvertibleLocal.regular_map_flat β FlatContraction.includeRight_flat
        (chart_generator_regular (originIdeal K) (coordinate K 0))
    · rw [hmap]
      exact Ideal.map_span β {chartBase (originIdeal K) (coordinate K 0) (MvPolynomial.X 0)} |>.trans
        (by rw [Set.image_singleton])
  obtain ⟨e, he, _⟩ := hπ.2 _ _ hf
  have hcontract : ((J.map α)^m).comap α = J^m := by
    rw [hmap, ← Ideal.map_pow]
    exact flat_chart_order K 0 m
  apply le_antisymm
  · have hh := Scheme.IdealSheafData.map_mono π
      ((((specIdeal J).comap π)^m).le_map_comap e)
    dsimp only at hh
    rw [← Scheme.IdealSheafData.map_comp, he, comap_pow,
      ← Scheme.IdealSheafData.comap_comp, he, specIdeal_comap,
      ← specIdeal_pow, specIdeal_map, hcontract] at hh
    exact hh
  · rw [specIdeal_pow, ← comap_pow]
    exact ((specIdeal J)^m).le_map_comap π

end
end MaximalSeshadri.PlaneBlowup

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
variable {X Y X' Y' : Scheme}

lemma comap_map_le_of_commSq (I : X.IdealSheafData)
    (f : X ⟶ Y) (g : X' ⟶ X) (j : Y' ⟶ Y) (f' : X' ⟶ Y')
    (h : g ≫ f = f' ≫ j) :
    (I.map f).comap j ≤ (I.comap g).map f' := by
  rw [Scheme.IdealSheafData.le_map_iff_comap_le,
    ← Scheme.IdealSheafData.comap_comp, ← h, Scheme.IdealSheafData.comap_comp]
  exact Scheme.IdealSheafData.comap_mono g (I.comap_map_le f)

lemma le_of_openCover (C : Y.OpenCover) {I J : Y.IdealSheafData}
    (h : ∀ i, I.comap (C.f i) ≤ J.comap (C.f i)) : I ≤ J := by
  let U (i : Σ i : C.I₀, (C.X i).affineOpens) : Y.affineOpens :=
    ⟨C.f i.1 ''ᵁ i.2.1, i.2.2.image_of_isOpenImmersion (C.f i.1)⟩
  apply Scheme.IdealSheafData.le_of_iSup_eq_top U
  · apply top_unique
    intro y _
    obtain ⟨i, x, rfl⟩ := C.exists_eq y
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : (C.X i).Opens) from trivial)
    exact Opens.mem_iSup.mpr ⟨⟨i, ⟨V, hV⟩⟩, x, hxV, rfl⟩
  · intro i
    have hi := h i.1 i.2
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hi
    exact Ideal.comap_le_comap_iff_of_surjective _
      (ConcreteCategory.bijective_of_isIso (C.f i.1 |>.appIso i.2).inv).surjective _ _ |>.mp hi

lemma power_contraction_of_openCover (I : Y.IdealSheafData) (f : X ⟶ Y)
    (C : Y.OpenCover) (m : ℕ)
    (h : ∀ i, (((I.comap (C.f i)).comap (pullback.fst (C.f i) f))^m).map
      (pullback.fst (C.f i) f) = (I.comap (C.f i))^m) :
    ((I.comap f)^m).map f = I^m := by
  apply le_antisymm
  · apply le_of_openCover C
    intro i
    have hi := comap_map_le_of_commSq ((I.comap f)^m) f
      (pullback.snd (C.f i) f) (C.f i) (pullback.fst (C.f i) f)
      (pullback.condition.symm)
    rw [comap_pow, ← Scheme.IdealSheafData.comap_comp, ← pullback.condition,
      Scheme.IdealSheafData.comap_comp, h i] at hi
    simpa only [comap_pow] using hi
  · rw [← comap_pow]
    exact (I^m).le_map_comap f

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.PointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry MaximalSeshadri.AlgebraicJets MaximalSeshadri.IdealPullback
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

theorem point_power_contraction
    [Algebra.IsStandardSmoothOfRelativeDimension 2 K S] (ρ : S →ₐ[K] K)
    {B : Scheme} (π : B ⟶ Spec (.of S))
    (hπ : IsBlowup (specIdeal (RingHom.ker ρ)) π) (m : ℕ) :
    (((specIdeal (RingHom.ker ρ)).comap π)^m).map π =
      (specIdeal (RingHom.ker ρ))^m := by
  obtain ⟨x, s, hs, _, hj, hI⟩ := exists_centered_etale_point_chart 2 ρ
  let φ := (algebraMap S (Localization.Away s)).comp (MvPolynomial.aeval (R := K) x).toRingHom
  let a := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))
  let I := specIdeal (RingHom.ker ρ)
  let U : (Spec (.of S)).Opens := I.support.compl
  let obj : Bool → Scheme := fun b => if b then U.toScheme else Spec (.of (Localization.Away s))
  let map : (b : Bool) → obj b ⟶ Spec (.of S) := fun b => Bool.rec a U.ι b
  have cover : ∀ p : Spec (.of S), ∃ b y, map b y = p := by
    intro p
    by_cases hp : p ∈ (I.support : Set (Spec (.of S)))
    · have hq : RingHom.ker ρ ≤ p.asIdeal := by
        rw [show (I.support : Set (Spec (.of S))) = PrimeSpectrum.zeroLocus (RingHom.ker ρ)
          from specIdeal_support _] at hp
        exact (PrimeSpectrum.mem_zeroLocus p _).mp hp
      have hmax : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective ρ
        (fun c => ⟨algebraMap K S c, by simp⟩)
      have heq : p.asIdeal = RingHom.ker ρ := (hmax.eq_of_le p.isPrime.ne_top hq).symm
      have hm : s ∉ p.asIdeal := by simpa only [heq, RingHom.mem_ker] using hs
      have hp' : p ∈ Set.range a := by
        change p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away s)))
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away s) s]
        exact hm
      obtain ⟨y, hy⟩ := hp'
      exact ⟨false, y, hy⟩
    · exact ⟨true, (⟨p, hp⟩ : U), rfl⟩
  let C : (Spec (.of S)).OpenCover := .mkOfCovers Bool obj map cover
    (by intro b; cases b <;> dsimp [map, obj] <;> infer_instance)
  apply power_contraction_of_openCover I π C m
  intro b
  cases b
  · change (((I.comap a).comap (pullback.fst a π))^m).map (pullback.fst a π) = (I.comap a)^m
    have he : I.comap a = specIdeal ((PlaneBlowup.originIdeal K).map φ) := by
      rw [specIdeal_comap]
      exact congrArg specIdeal hI
    rw [he]
    let : Algebra (PlaneBlowup.PlaneRing K) (Localization.Away s) := φ.toAlgebra
    have : Algebra.Etale (PlaneBlowup.PlaneRing K) (Localization.Away s) :=
      RingHom.etale_algebraMap.mp hj
    have hθ : IsBlowup (specIdeal ((PlaneBlowup.originIdeal K).map φ)) (pullback.fst a π) := by
      have hb : IsBlowup (I.comap a) (pullback.fst a π) := hπ.flat_baseChange a
      rwa [he] at hb
    rw [← specIdeal_pow]
    exact PlaneBlowup.blowup_power_contraction K hθ m
  · change (((I.comap U.ι).comap (pullback.fst U.ι π))^m).map (pullback.fst U.ι π) =
      (I.comap U.ι)^m
    have he : I.comap U.ι = ⊤ := by
      apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
      rw [Scheme.IdealSheafData.support_comap]
      ext p
      exact iff_false_intro p.property
    rw [he, Scheme.IdealSheafData.comap_top]
    simp only [← Scheme.IdealSheafData.one_eq_top, one_pow]
    exact Scheme.IdealSheafData.map_top (pullback.fst U.ι π)

end

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme}

theorem rational_point_power_contraction (f : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 2 f] (p : Spec (.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (π : B ⟶ X) (hπ : IsBlowup p.ker π) (m : ℕ) :
    ((p.ker.comap π)^m).map π = p.ker^m := by
  let point : Spec (.of K) := ⟨⊥, Ideal.isPrime_bot⟩
  let := isClosedImmersion_of_comp_eq_id f p hp
  obtain ⟨U, hU, V, hV, hxV, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 2) (f := f) (p point)
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = f (p point) := Subsingleton.elim _ _
    rw [hy]
    exact e hxV
  subst U
  let A := Γ(X, V)
  let g : CommRingCat.of K ⟶ A :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ V e
  have hng : RingHom.IsStandardSmoothOfRelativeDimension 2 g.hom := by
    let e₀ : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
      RingEquiv.ofBijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
    convert hg.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e₀) using 1
    rfl
  algebraize [g.hom]
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 K A := hng.toAlgebra
  let j := hV.fromSpec
  have hmap : Spec.map g = j ≫ f := by
    dsimp only [g]
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV e
  have hps : Set.range p ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    rw [show z = point from Subsingleton.elim _ _]
    rwa [hV.range_fromSpec]
  let l := IsOpenImmersion.lift j p hps
  have hlj : l ≫ j = p := IsOpenImmersion.lift_fac j p hps
  let q := Spec.preimage l
  have hq : Spec.map q = l := Spec.map_preimage l
  have hqg : g ≫ q = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hq, hmap, ← Category.assoc, hlj, hp, Spec.map_id]
  let ρ : A →ₐ[K] K :=
    { q.hom with commutes' := fun c => CategoryTheory.congr_fun hqg c }
  have hker : p.ker.comap j = IdealPullback.specIdeal (RingHom.ker ρ) := by
    have sq := IsOpenImmersion.isPullback_lift_id p j hps
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion p j,
      ← Scheme.Hom.ker_comp_of_isIso sq.isoPullback.hom,
      sq.isoPullback_hom_fst]
    change l.ker = _
    rw [← hq]
    exact IdealPullback.specMap_ker q.hom
  let W : X.Opens := p.ker.support.compl
  let obj : Bool → Scheme := fun b => if b then W.toScheme else Spec A
  let map : (b : Bool) → obj b ⟶ X := fun b => Bool.rec j W.ι b
  have cover : ∀ x : X, ∃ b y, map b y = x := by
    intro x
    by_cases hx : x ∈ (p.ker.support : Set X)
    · rw [Scheme.Hom.support_ker, p.isClosedEmbedding.isClosed_range.closure_eq] at hx
      obtain ⟨y, hy⟩ := hps hx
      exact ⟨false, y, hy⟩
    · exact ⟨true, (⟨x, hx⟩ : W), rfl⟩
  let C : X.OpenCover := .mkOfCovers Bool obj map cover
    (by intro b; cases b <;> dsimp [map, obj] <;> infer_instance)
  apply IdealPullback.power_contraction_of_openCover p.ker π C m
  intro b
  cases b
  · change (((p.ker.comap j).comap (pullback.fst j π))^m).map (pullback.fst j π) =
      (p.ker.comap j)^m
    rw [hker]
    exact point_power_contraction ρ _ (by simpa only [hker] using hπ.flat_baseChange j) m
  · change (((p.ker.comap W.ι).comap (pullback.fst W.ι π))^m).map (pullback.fst W.ι π) =
      (p.ker.comap W.ι)^m
    have he : p.ker.comap W.ι = ⊤ := by
      apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
      rw [Scheme.IdealSheafData.support_comap]
      ext x
      exact iff_false_intro x.property
    rw [he, Scheme.IdealSheafData.comap_top]
    simp only [← Scheme.IdealSheafData.one_eq_top, one_pow]
    exact Scheme.IdealSheafData.map_top (pullback.fst W.ι π)

end
end MaximalSeshadri.PointBlowup

end

end OAI
