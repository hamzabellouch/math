import Mathlib
import OAI.AlgebraicGeometry.LogKodaira.Basic

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.SmoothDimension

 

theorem smooth_dimension_unique {K : Type*} [Field K]
    (X : Scheme) [Nonempty X] (f : X ⟶ Spec (CommRingCat.of K)) (n m : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m f] : n = m := by
  classical
  let x : X := Classical.arbitrary X
  have chart (d : ℕ) [SmoothOfRelativeDimension d f] :
      ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ ⊤),
        RingHom.IsStandardSmoothOfRelativeDimension d (f.appLE ⊤ V e).hom := by
    obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
        (n := d) (f := f) x
    have hUt : U = ⊤ := by
      apply top_unique
      intro y _
      have ht := e hx
      change f x ∈ U at ht
      simpa only [Subsingleton.elim y (f x)] using ht
    subst U
    exact ⟨V, hV, hx, e, hf⟩
  obtain ⟨V, hV, hxV, eV, hn⟩ := chart n
  obtain ⟨W, hW, hxW, eW, hm⟩ := chart m
  obtain ⟨r, t, hrt, hxr⟩ := exists_basicOpen_le_affine_inter hV hW x ⟨hxV, hxW⟩
  have refine_chart (d : ℕ) (A : X.Opens) (hA : IsAffineOpen A)
      (eA : A ≤ f ⁻¹ᵁ ⊤)
      (hd : RingHom.IsStandardSmoothOfRelativeDimension d (f.appLE ⊤ A eA).hom)
      (a : Γ(X, A)) :
      RingHom.IsStandardSmoothOfRelativeDimension d
        (f.appLE ⊤ (X.basicOpen a) ((X.basicOpen_le a).trans eA)).hom := by
    let := hA.isLocalization_basicOpen a
    have hz := RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway
      (Rᵣ := Γ(X, X.basicOpen a)) a
    have hc := RingHom.IsStandardSmoothOfRelativeDimension.comp hz hd
    simpa only [Nat.zero_add, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_map] using hc
  have hnr := refine_chart n V hV eV hn r
  have hmt := refine_chart m W hW eW hm t
  have hmr : RingHom.IsStandardSmoothOfRelativeDimension m
      (f.appLE ⊤ (X.basicOpen r) ((X.basicOpen_le r).trans eV)).hom := by
    exact (f.appLE_congr ((X.basicOpen_le r).trans eV) rfl hrt
      (fun {_ _} h => RingHom.IsStandardSmoothOfRelativeDimension m h.hom)).mpr hmt
  let : Nonempty (X.basicOpen r) := ⟨⟨x, hxr⟩⟩
  let := (f.appLE ⊤ (X.basicOpen r) ((X.basicOpen_le r).trans eV)).hom.toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension n
      Γ(Spec (CommRingCat.of K), ⊤) Γ(X, X.basicOpen r) := hnr
  let : Algebra.IsStandardSmoothOfRelativeDimension m
      Γ(Spec (CommRingCat.of K), ⊤) Γ(X, X.basicOpen r) := hmr
  have hnrank := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Spec (CommRingCat.of K), ⊤)) (S := Γ(X, X.basicOpen r)) n
  have hmrank := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Spec (CommRingCat.of K), ⊤)) (S := Γ(X, X.basicOpen r)) m
  exact_mod_cast hnrank.symm.trans hmrank

end ReverseLogKodaira.SmoothDimension

namespace ReverseLogKodaira.SmoothDimension

 

theorem smooth_relative_dimension_subtraction {K : Type*} [Field K]
    {X Y : Scheme} [Nonempty X] (sX : X ⟶ Spec (CommRingCat.of K))
    (sY : Y ⟶ Spec (CommRingCat.of K)) (a b : ℕ)
    [SmoothOfRelativeDimension a sX] [SmoothOfRelativeDimension b sY]
    (f : X ⟶ Y) [Smooth f] (h : f ≫ sY = sX) :
    b ≤ a ∧ SmoothOfRelativeDimension (a - b) f := by
  classical
  have chart (x : X) :
      ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
        (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
        RingHom.IsStandardSmoothOfRelativeDimension (a - b) (f.appLE U V e).hom ∧ b ≤ a := by
    obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
    let : Nonempty V := ⟨⟨x, hx⟩⟩
    let := (f.appLE U V e).hom.toAlgebra
    let : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := hf
    obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hf.out
    let := hσ
    let := hι
    have hr : RingHom.IsStandardSmoothOfRelativeDimension P.dimension
        (f.appLE U V e).hom := P.isStandardSmoothOfRelativeDimension rfl
    let : IsAffine U := hU
    let : IsAffine V := hV
    have hrel : SmoothOfRelativeDimension P.dimension (f.resLE U V e) := by
      rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)]
      apply ((RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso).arrow_mk_iso_iff
        (arrowResLEAppIso f U V e)).mpr
      exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hr
    let := hrel
    let hsa : SmoothOfRelativeDimension a (V.ι ≫ sX) := by
      simpa only [Nat.zero_add] using
        (inferInstance : SmoothOfRelativeDimension (0 + a) (V.ι ≫ sX))
    let hsb : SmoothOfRelativeDimension b (U.ι ≫ sY) := by
      simpa only [Nat.zero_add] using
        (inferInstance : SmoothOfRelativeDimension (0 + b) (U.ι ≫ sY))
    have he : f.resLE U V e ≫ (U.ι ≫ sY) = V.ι ≫ sX := by
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, h]
    have hh : SmoothOfRelativeDimension (P.dimension + b) (V.ι ≫ sX) := by
      rw [← he]
      infer_instance
    let := hh
    have hd := smooth_dimension_unique V.toScheme (V.ι ≫ sX) a (P.dimension + b)
    have hdim : a - b = P.dimension := by omega
    exact ⟨U, hU, V, hV, hx, e, hdim ▸ hr, by omega⟩
  constructor
  · obtain ⟨U, hU, V, hV, hx, e, hr, hab⟩ := chart (Classical.arbitrary X)
    exact hab
  · constructor
    intro x
    obtain ⟨U, hU, V, hV, hx, e, hr, hab⟩ := chart x
    exact ⟨U, hU, V, hV, hx, e, hr⟩

end ReverseLogKodaira.SmoothDimension

namespace ReverseLogKodaira.RelativeCharts

 

theorem exists_standard_chart_over_smooth_open
    {X Y : Scheme} (f : X ⟶ Y) (n : ℕ)
    (U : Y.affineOpens) [SmoothOfRelativeDimension n (f ∣_ U.1)] (V : X.Opens) (x : X) (hx : x ∈ V)
    (hfx : f x ∈ U.1) :
    ∃ (W : X.affineOpens), x ∈ W.1 ∧ W.1 ≤ V ∧
      ∃ (e : W.1 ≤ f ⁻¹ᵁ U.1),
        RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U.1 W.1 e).hom := by
  classical
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hx₀, hV₀le⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (V ⊓ f ⁻¹ᵁ U.1 : X.Opens) from ⟨hx, hfx⟩)
      (V ⊓ f ⁻¹ᵁ U.1).isOpen
  have e₀ : V₀ ≤ f ⁻¹ᵁ U.1 := fun z hz => (hV₀le hz).2
  let : IsAffine V₀ := hV₀
  have hres : SmoothOfRelativeDimension n (f.resLE U.1 V₀ e₀) := by
    unfold Scheme.Hom.resLE
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n)
        (X.homOfLE e₀ ≫ f ∣_ U.1))
  have hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (f.appLE U.1 V₀ e₀).hom := by
    apply ((RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).arrow_mk_iso_iff
        (arrowResLEAppIso f U.1 V₀ e₀)).mp
    exact (HasRingHomProperty.iff_of_isAffine
      (P := @SmoothOfRelativeDimension n)).mp hres
  obtain ⟨s, hs, hsm⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).mp hlocal
  let hprime := (hV₀.primeIdealOf ⟨x, hx₀⟩)
  obtain ⟨t, ht, htx⟩ : ∃ t ∈ s, t ∉ hprime.asIdeal := by
    by_contra! hh
    have hle : Ideal.span (s : Set Γ(X, V₀)) ≤ hprime.asIdeal :=
      Ideal.span_le.mpr hh
    rw [hs] at hle
    exact hprime.isPrime.ne_top (top_unique hle)
  have hxB : x ∈ X.basicOpen t := by
    have hm : hV₀.fromSpec (hV₀.primeIdealOf ⟨x, hx₀⟩) ∈ X.basicOpen t := by
      change hV₀.primeIdealOf ⟨x, hx₀⟩ ∈ hV₀.fromSpec ⁻¹ᵁ X.basicOpen t
      rw [hV₀.fromSpec_preimage_basicOpen]
      exact htx
    have he : hV₀.fromSpec (hV₀.primeIdealOf ⟨x, hx₀⟩) = x :=
      hV₀.fromSpec_primeIdealOf ⟨x, hx₀⟩
    exact he ▸ hm
  let e : X.basicOpen t ≤ f ⁻¹ᵁ U.1 := (X.basicOpen_le t).trans e₀
  refine ⟨⟨X.basicOpen t, hV₀.basicOpen t⟩, hxB,
    (X.basicOpen_le t).trans (fun z hz => (hV₀le hz).1), e, ?_⟩
  let := hV₀.isLocalization_basicOpen t
  have h := hsm t ht Γ(X, X.basicOpen t)
  convert h using 1
  exact congrArg CommRingCat.Hom.hom (f.appLE_map e₀ (homOfLE (X.basicOpen_le t)).op).symm

end ReverseLogKodaira.RelativeCharts

namespace ReverseLogKodaira.RelativeCharts

lemma smooth_dimension_restrict_le {X Y : Scheme} (f : X ⟶ Y) (n : ℕ)
    (U V : Y.Opens) (h : U ≤ V) [SmoothOfRelativeDimension n (f ∣_ V)] :
    SmoothOfRelativeDimension n (f ∣_ U) := by
  have ho : IsPullback (X.homOfLE (f.preimage_mono h) ≫ (f ⁻¹ᵁ V).ι)
      (f ∣_ U) f (Y.homOfLE h ≫ V.ι) := by
    simpa only [Scheme.homOfLE_ι] using (isPullback_morphismRestrict f U).flip
  have hs := ho.of_right (morphismRestrict_homOfLE f U V h).symm
    (isPullback_morphismRestrict f V).flip
  let := smoothOfRelativeDimension_isStableUnderBaseChange n
  exact MorphismProperty.of_isPullback hs (inferInstance : SmoothOfRelativeDimension n (f ∣_ V))

end ReverseLogKodaira.RelativeCharts

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

theorem exists_relative_log_chart
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (O : X.scheme.Opens) (x : X.scheme) (hx : x ∈ O) (hfx : f.hom x ∈ U.1) :
    ∃ (V : X.scheme.affineOpens), x ∈ V.1 ∧ V.1 ≤ O ∧
      ∃ (e : V.1 ≤ f.hom ⁻¹ᵁ U.1),
        RingHom.IsStandardSmoothOfRelativeDimension (X.dimension - Y.dimension)
          (f.hom.appLE U.1 V.1 e).hom ∧
        ∃ t : Γ(X.scheme, V.1), t ≠ 0 ∧ E.ideal.ideal V = Ideal.span {t} := by
  classical
  let Q := D.complement
  let P := f.hom ⁻¹ᵁ Q
  let : Nonempty P := ⟨⟨x, hU hfx⟩⟩
  let sP : P.toScheme ⟶ complexBase := P.ι ≫ X.structural
  let sQ : Q.toScheme ⟶ complexBase := Q.ι ≫ Y.structural
  let : SmoothOfRelativeDimension X.dimension sP := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + X.dimension) (P.ι ≫ X.structural))
  let : SmoothOfRelativeDimension Y.dimension sQ := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + Y.dimension) (Q.ι ≫ Y.structural))
  let : Smooth (f.hom ∣_ Q) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using f.smooth
  have hw : (f.hom ∣_ Q) ≫ sQ = sP := by
    dsimp only [sP, sQ, P, Q]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, f.over_base]
  have hr := (SmoothDimension.smooth_relative_dimension_subtraction
    sP sQ X.dimension Y.dimension (f.hom ∣_ Q) hw).2
  let := hr
  let := RelativeCharts.smooth_dimension_restrict_le f.hom
    (X.dimension - Y.dimension) U.1 Q hU
  obtain ⟨A, hxA, t, ht, hEt⟩ := E.union_cartier x
  obtain ⟨V, hxV, hVO, e, hsm⟩ :=
    RelativeCharts.exists_standard_chart_over_smooth_open f.hom (X.dimension - Y.dimension)
      U (O ⊓ A.1) x ⟨hx, hxA⟩ hfx
  have hVA : V.1 ≤ A.1 := fun z hz => (hVO hz).2
  let : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  let tV := X.scheme.presheaf.map (homOfLE hVA).op t
  refine ⟨V, hxV, fun z hz => (hVO hz).1, e, hsm, tV, ?_, ?_⟩
  · simpa only [map_zero] using
      ((map_injective_of_isIntegral X.scheme (homOfLE hVA)).ne ht)
  · change E.ideal.ideal A = Ideal.span {t} at hEt
    rw [← E.ideal.map_ideal (show V ≤ A from hVA), hEt, Ideal.map_span]
    simp only [Set.image_singleton]
    rfl

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothDimension

 

theorem smooth_fiber_dimension {K : Type*} [Field K]
    {X Y T : Scheme} [Nonempty T]
    (sX : X ⟶ Spec (CommRingCat.of K)) (sY : Y ⟶ Spec (CommRingCat.of K))
    (a b : ℕ) [SmoothOfRelativeDimension a sX] [SmoothOfRelativeDimension b sY]
    (f : X ⟶ Y) (h : f ≫ sY = sX)
    (y : Spec (CommRingCat.of K) ⟶ Y) (i : T ⟶ X) (sT : T ⟶ Spec (CommRingCat.of K))
    (sq : IsPullback i sT f y) (U : Y.Opens) (hy : Set.range y ⊆ U)
    (hf : Smooth (f ∣_ U)) :
    b ≤ a ∧ SmoothOfRelativeDimension (a - b) sT := by
  classical
  let y' : Spec (CommRingCat.of K) ⟶ U := IsOpenImmersion.lift U.ι y (by simpa using hy)
  have hi : Set.range i ⊆ (f ⁻¹ᵁ U : Set X) := by
    rintro _ ⟨z, rfl⟩
    change f (i z) ∈ U
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
    exact hy ⟨_, rfl⟩
  let i' : T ⟶ (f ⁻¹ᵁ U) := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι i (by simpa using hi)
  let : Nonempty (f ⁻¹ᵁ U) := ⟨i' (Classical.arbitrary T)⟩
  let sa : (f ⁻¹ᵁ U).toScheme ⟶ Spec (CommRingCat.of K) := (f ⁻¹ᵁ U).ι ≫ sX
  let sb : U.toScheme ⟶ Spec (CommRingCat.of K) := U.ι ≫ sY
  let : SmoothOfRelativeDimension a sa := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + a) ((f ⁻¹ᵁ U).ι ≫ sX))
  let : SmoothOfRelativeDimension b sb := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + b) (U.ι ≫ sY))
  let := hf
  have hab : f ∣_ U ≫ sb = sa := by
    dsimp only [sa, sb]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, h]
  obtain ⟨hle, hr⟩ := smooth_relative_dimension_subtraction sa sb a b (f ∣_ U) hab
  refine ⟨hle, ?_⟩
  have hw : i' ≫ (f ∣_ U) = sT ≫ y' := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, y', IsOpenImmersion.lift_fac]
    rw [morphismRestrict_ι, ← Category.assoc]
    simp only [i', IsOpenImmersion.lift_fac, sq.w]
  have ho : IsPullback (i' ≫ (f ⁻¹ᵁ U).ι) sT f (y' ≫ U.ι) := by
    simpa only [i', y', IsOpenImmersion.lift_fac] using sq
  have hs := ho.of_right hw (isPullback_morphismRestrict f U).flip
  let := smoothOfRelativeDimension_isStableUnderBaseChange (a - b)
  exact MorphismProperty.of_isPullback hs hr

end ReverseLogKodaira.SmoothDimension

end

end OAI
