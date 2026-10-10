import Mathlib

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri
noncomputable section
open Cardinal

theorem algebraic_of_countable_presentation
    {F E σ : Type} [Field F] [Uncountable F] [Field E] [Algebra F E]
    [Countable σ] (φ : MvPolynomial σ F →ₐ[F] E) (hφ : Function.Surjective φ) :
    Algebra.IsAlgebraic F E := by
  constructor
  intro x
  by_contra hx
  have hLI := (show Transcendental F x from hx).linearIndependent_sub_inv
  have hrank : Module.rank F E ≤ ℵ₀ := by
    calc
      _ ≤ Module.rank F (MvPolynomial σ F) :=
        LinearMap.rank_le_of_surjective φ.toLinearMap hφ
      _ = #(σ →₀ ℕ) := MvPolynomial.rank_eq
      _ ≤ ℵ₀ := Cardinal.mk_le_aleph0
  exact (not_le_of_gt (Cardinal.aleph0_lt_mk (α := F)))
    (hLI.cardinal_le_rank.trans hrank)

theorem point_of_countable_presentation
    {F A σ : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [Nontrivial A] [Algebra F A] [Countable σ]
    (φ : MvPolynomial σ F →ₐ[F] A) (hφ : Function.Surjective φ) :
    Nonempty (A →ₐ[F] F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let q : A →ₐ[F] A ⧸ m := Ideal.Quotient.mkₐ F m
  let ψ : MvPolynomial σ F →ₐ[F] A ⧸ m := q.comp φ
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.mk_surjective).comp hφ
  let : Algebra.IsAlgebraic F (A ⧸ m) :=
    algebraic_of_countable_presentation ψ hψ
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] F).comp q⟩

theorem point_avoiding_sequence_of_countable_presentation
    {F A σ : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [IsDomain A] [Algebra F A] [Countable σ]
    (φ : MvPolynomial σ F →ₐ[F] A) (hφ : Function.Surjective φ)
    (a : ℕ → A) (ha : ∀ n, a n ≠ 0) :
    ∃ f : A →ₐ[F] F, ∀ n, f (a n) ≠ 0 := by
  classical
  let S : Submonoid A := Submonoid.closure (Set.range a)
  have hcount : (S : Set A).Countable := by
    change ((Submonoid.closure (Set.range a) : Submonoid A) : Set A).Countable
    rw [← FreeMonoid.mrange_lift, MonoidHom.coe_mrange]
    exact Set.countable_range _
  let : Countable S := hcount.to_subtype
  have hden : S ≤ nonZeroDivisors A := by
    apply Submonoid.closure_le.mpr
    rintro b ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (ha n)
  let B := Localization S
  let : IsDomain B := IsLocalization.isDomain_localization hden
  let j : A →ₐ[F] B := IsScalarTower.toAlgHom F A B
  let vals : σ ⊕ S → B := Sum.elim (fun i => j (φ (MvPolynomial.X i)))
    (fun s => IsLocalization.mk' B 1 s)
  let ψ : MvPolynomial (σ ⊕ S) F →ₐ[F] B := MvPolynomial.aeval vals
  have hre : ψ.comp (MvPolynomial.rename Sum.inl) = j.comp φ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [ψ, vals]
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq S z
    obtain ⟨p, rfl⟩ := hφ b
    refine ⟨MvPolynomial.rename Sum.inl p * MvPolynomial.X (Sum.inr s), ?_⟩
    rw [map_mul]
    have he := DFunLike.congr_fun hre p
    change ψ (MvPolynomial.rename Sum.inl p) = j (φ p) at he
    rw [he]
    simp only [ψ, MvPolynomial.aeval_X, vals, Sum.elim_inr]
    exact (IsLocalization.mk'_eq_mul_mk'_one _ _).symm
  obtain ⟨g⟩ := point_of_countable_presentation ψ hψ
  refine ⟨g.comp j, fun n => ?_⟩
  let s : S := ⟨a n, Submonoid.subset_closure ⟨n, rfl⟩⟩
  exact ((IsLocalization.map_units B s).map g.toMonoidHom).ne_zero

theorem point_avoiding_sequence
    {F A : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [IsDomain A] [Algebra F A] [Algebra.FiniteType F A]
    (a : ℕ → A) (ha : ∀ n, a n ≠ 0) :
    ∃ f : A →ₐ[F] F, ∀ n, f (a n) ≠ 0 := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType F A)
  exact point_avoiding_sequence_of_countable_presentation φ hφ a ha

theorem rational_point_outside_countable_closed
    {F A : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [IsDomain A] [Algebra F A] [Algebra.FiniteType F A]
    (Z : ℕ → Set (PrimeSpectrum A)) (hclosed : ∀ n, IsClosed (Z n))
    (hproper : ∀ n, Z n ≠ Set.univ) :
    ∃ f : A →ₐ[F] F, ∀ n,
      (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum A) ∉ Z n := by
  classical
  choose I hI using fun n => (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (Z n)).mp
    (hclosed n)
  have hIbot (n : ℕ) : I n ≠ ⊥ := by
    intro heq
    apply hproper n
    rw [hI n, heq, PrimeSpectrum.zeroLocus_bot]
  have hex (n : ℕ) : ∃ a, a ∈ I n ∧ a ≠ 0 := by
    by_contra h
    apply hIbot n
    apply le_antisymm _ bot_le
    intro a ha
    simp only [Ideal.mem_bot]
    by_contra hn
    exact h ⟨a, ha, hn⟩
  choose a ha hane using hex
  obtain ⟨f, hf⟩ := point_avoiding_sequence (F := F) a hane
  refine ⟨f, fun n hn => hf n ?_⟩
  rw [hI n] at hn
  exact hn (ha n)

end

noncomputable section
open scoped TensorProduct

lemma smooth_positive_dimension_nontrivial_kernel
    {F A : Type} [Field F] [CommRing A] [Nontrivial A] [Algebra F A]
    (n : ℕ) (hn : 0 < n) [Algebra.IsStandardSmoothOfRelativeDimension n F A]
    (p : A →ₐ[F] F) : ∃ a : A, a ≠ 0 ∧ p a = 0 := by
  classical
  by_contra h
  have hi : Function.Injective p := by
    intro a b hab
    apply sub_eq_zero.mp
    by_contra hab'
    exact h ⟨a - b, hab', by simp [hab]⟩
  have hs : Function.Surjective p := fun a => ⟨algebraMap F A a, p.commutes a⟩
  let e : A ≃ₐ[F] F := AlgEquiv.ofBijective p ⟨hi, hs⟩
  let : Algebra.FormallyUnramified F A := Algebra.FormallyUnramified.of_equiv e.symm
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := F) (S := A) n
  rw [rank_subsingleton'] at hr
  have : n = 0 := by exact_mod_cast hr.symm
  omega

theorem smooth_affine_uncountable_rational_points
    {F A : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [IsDomain A] [Algebra F A]
    (n : ℕ) (hn : 0 < n) [Algebra.IsStandardSmoothOfRelativeDimension n F A] :
    Uncountable (A →ₐ[F] F) := by
  classical
  let : Algebra.IsStandardSmooth F A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let : Algebra.FiniteType F A := inferInstance
  obtain ⟨p, _⟩ := point_avoiding_sequence (F := F) (A := A) (fun _ => 1)
    (fun _ => one_ne_zero)
  let : Nonempty (A →ₐ[F] F) := ⟨p⟩
  apply not_countable_iff.mp
  intro hcount
  let := hcount
  obtain ⟨q, hq⟩ := exists_surjective_nat (A →ₐ[F] F)
  choose a hane ha using fun k => smooth_positive_dimension_nontrivial_kernel n hn (q k)
  obtain ⟨p', hp'⟩ := point_avoiding_sequence (F := F) a hane
  obtain ⟨k, rfl⟩ := hq p'
  exact hp' k (ha k)

theorem rational_kernel_injective {F A : Type} [Field F] [CommRing A] [Algebra F A] :
    Function.Injective (fun p : A →ₐ[F] F => RingHom.ker p.toRingHom) := by
  intro p q h
  ext a
  have hzero : a - algebraMap F A (q a) ∈ RingHom.ker q.toRingHom := by
    simp
  change RingHom.ker p.toRingHom = RingHom.ker q.toRingHom at h
  rw [← h] at hzero
  simpa [sub_eq_zero] using hzero

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

def fieldPoint (F : Type) [Field F] : Spec (CommRingCat.of F) :=
  ⟨⊥, Ideal.isPrime_bot⟩

theorem smooth_scheme_uncountable_rational_points
    {F : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of F))
    (n : ℕ) (hn : 0 < n) [SmoothOfRelativeDimension n f] :
    ¬ (Set.range fun p : {p : Spec (CommRingCat.of F) ⟶ X // p ≫ f = 𝟙 _} =>
      p.val (fieldPoint F)).Countable := by
  classical
  let x : X := Classical.ofNonempty
  obtain ⟨U, hU, V, hV, hxV, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := f) x
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = f x := Subsingleton.elim _ _
    simpa only [Scheme.Hom.mem_preimage, hy] using e hxV
  subst U
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  let A := Γ(X, V)
  let g : CommRingCat.of F ⟶ A :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ f.appLE ⊤ V e
  have hng : RingHom.IsStandardSmoothOfRelativeDimension n g.hom := by
    let e₀ : F ≃+* Γ(Spec (CommRingCat.of F), ⊤) :=
      RingEquiv.ofBijective (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv)
    have he := RingHom.IsStandardSmoothOfRelativeDimension.equiv e₀
    convert hg.comp he using 1
    rfl
  algebraize [g.hom]
  let : Algebra.IsStandardSmoothOfRelativeDimension n F A := hng.toAlgebra
  let : Uncountable (A →ₐ[F] F) := smooth_affine_uncountable_rational_points n hn
  have hmap : Spec.map g = hV.fromSpec ≫ f := by
    dsimp only [g]
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV e
  let p (φ : A →ₐ[F] F) : {p : Spec (CommRingCat.of F) ⟶ X // p ≫ f = 𝟙 _} :=
    ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hV.fromSpec, by
      rw [Category.assoc, ← hmap, ← Spec.map_comp, ← Spec.map_id]
      congr 1
      apply CommRingCat.hom_ext
      exact φ.comp_algebraMap⟩
  have hi : Function.Injective (fun φ : A →ₐ[F] F => (p φ).val (fieldPoint F)) := by
    intro φ ψ h
    apply rational_kernel_injective
    have heq :
        (⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime φ.toRingHom⟩ : PrimeSpectrum A) =
        (⟨RingHom.ker ψ.toRingHom, RingHom.ker_isPrime ψ.toRingHom⟩ : PrimeSpectrum A) :=
      hV.fromSpec.isOpenEmbedding.injective h
    exact congrArg PrimeSpectrum.asIdeal heq
  intro hcount
  let : Countable (Set.range fun q : {q : Spec (CommRingCat.of F) ⟶ X // q ≫ f = 𝟙 _} =>
      q.val (fieldPoint F)) := hcount.to_subtype
  let j (φ : A →ₐ[F] F) :
      Set.range (fun q : {q : Spec (CommRingCat.of F) ⟶ X // q ≫ f = 𝟙 _} =>
        q.val (fieldPoint F)) := ⟨(p φ).val (fieldPoint F), ⟨p φ, rfl⟩⟩
  have hij : Function.Injective j := by
    intro φ ψ h
    apply hi
    have heq := congrArg (fun z : Set.range (fun q :
      {q : Spec (CommRingCat.of F) ⟶ X // q ≫ f = 𝟙 _} =>
        q.val (fieldPoint F)) => (z : X)) h
    exact heq
  exact not_countable hij.countable

end
end MaximalSeshadri
end


end
end

end OAI
