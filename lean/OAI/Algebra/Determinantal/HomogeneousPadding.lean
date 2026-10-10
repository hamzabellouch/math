import OAI.Algebra.Determinantal.AffineSelectors

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial
variable {A B R : Type*} [Fintype A] [Fintype B] [CommSemiring R]
 theorem weight_one_sumElim (d : A →₀ ℕ) (e : B →₀ ℕ) :
    Finsupp.weight (1 : A ⊕ B → ℕ) (d.sumElim e) =
      Finsupp.weight (1 : A → ℕ) d + Finsupp.weight (1 : B → ℕ) e := by
  simp only [Finsupp.weight_eq_sum, Pi.one_apply, smul_eq_mul, mul_one,
    Fintype.sum_sum_type, Finsupp.sumElim_inl, Finsupp.sumElim_inr]

 theorem homogeneous_coefficient {p : MvPolynomial (A ⊕ B) R} {r : ℕ}
    (hp : p.IsHomogeneous r) (d : A →₀ ℕ) :
    ((sumRingEquiv R A B p).coeff d).IsHomogeneous
      (r - Finsupp.weight (1 : A → ℕ) d) := by
  intro e he
  rw [← coeff_nested] at he
  have hh := hp he
  rw [weight_one_sumElim] at hh
  omega

variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable def universalHomogeneousPencil (θ : I → R) :
    Matrix I I (MvPolynomial (Fin 2 ⊕ (I × I)) R) :=
  Matrix.of fun i j => X (.inr (i,j)) +
    if i=j then X (.inl 0) + C (θ i)*X (.inl 1) else 0

 theorem universalHomogeneousPencil_permanent (θ : I → R) :
    (universalHomogeneousPencil θ).permanent.IsHomogeneous (Fintype.card I) := by
  classical
  unfold Matrix.permanent
  apply IsHomogeneous.sum
  intro σ _
  convert IsHomogeneous.prod Finset.univ
    (fun i => universalHomogeneousPencil θ (σ i) i) (fun _ => 1) ?_ using 1 <;> try simp
  intro i _
  apply IsHomogeneous.add (isHomogeneous_X _ _)
  split_ifs
  · exact (isHomogeneous_X _ _).add (isHomogeneous_C_mul_X _ _)
  · exact isHomogeneous_zero _ _ _

 theorem coefficientPolynomial_homogeneous (θ : I → R) (q : ℕ) :
    (diagonalCoefficient (Matrix.of fun i j => (X (i,j) : MvPolynomial (I × I) R))
      (fun i => C (θ i)) q).IsHomogeneous (Fintype.card I - 2*q) := by
  classical
  have hm : sumRingEquiv R (Fin 2) (I × I) (universalHomogeneousPencil θ).permanent =
      ((Matrix.of fun i j => C (X (i,j))) +
        Matrix.diagonal (fun i => X (0 : Fin 2) + C (C (θ i))*X 1)).permanent := by
    unfold Matrix.permanent
    simp only [map_sum, map_prod]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : σ i = i
    · simp [universalHomogeneousPencil, hi]
    · simp [universalHomogeneousPencil, hi]
  have hw : Finsupp.weight (1 : Fin 2 → ℕ) (countIndex q) = 2*q := by
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, countIndex]
  have h := homogeneous_coefficient (universalHomogeneousPencil_permanent θ) (countIndex q)
  rw [hm, hw] at h
  exact h
end PermanentBorder.Selector

namespace PermanentBorder.HomogeneousPadding
open MvPolynomial
variable {σ τ R : Type*} [Fintype σ] [CommRing R]

noncomputable def dehomogenize : MvPolynomial (Option σ) R →+* MvPolynomial σ R :=
  (Polynomial.evalRingHom 1).comp (optionEquivLeft R σ).toRingHom

 theorem weight_optionElim (d : σ →₀ ℕ) (i : ℕ) :
    Finsupp.weight (1 : Option σ → ℕ) (d.optionElim i) =
      i + Finsupp.weight (1 : σ → ℕ) d := by
  simp only [Finsupp.weight_eq_sum, Pi.one_apply, smul_eq_mul, mul_one,
    Fintype.sum_option, Finsupp.optionElim_apply_none, Finsupp.optionElim_apply_some]

 theorem weight_some (d : Option σ →₀ ℕ) :
    Finsupp.weight (1 : Option σ → ℕ) d =
      d none + Finsupp.weight (1 : σ → ℕ) d.some := by
  convert weight_optionElim d.some (d none) using 1; simp

 theorem dehomogenize_coeff_of_homogeneous {p : MvPolynomial (Option σ) R} {m : ℕ}
    (hp : p.IsHomogeneous m) (d : Option σ →₀ ℕ)
    (hd : Finsupp.weight (1 : Option σ → ℕ) d = m) :
    (dehomogenize p).coeff d.some = p.coeff d := by
  classical
  change (((optionEquivLeft R σ p).eval 1)).coeff d.some = _
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, one_pow, mul_one, coeff_sum]
  rw [← optionEquivLeft_coeff_some_coeff_none R σ d p]
  apply Finset.sum_eq_single (d none)
  · intro i hi hne
    rw [optionEquivLeft_coeff_coeff]
    apply IsWeightedHomogeneous.coeff_eq_zero hp
    rw [weight_optionElim]
    rw [weight_some] at hd
    omega
  · intro hn
    have hh := Polynomial.notMem_support_iff.mp hn
    rw [hh, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

 theorem homogeneous_eq_of_dehomogenize_eq {p q : MvPolynomial (Option σ) R} {m : ℕ}
    (hp : p.IsHomogeneous m) (hq : q.IsHomogeneous m)
    (h : dehomogenize p = dehomogenize q) : p=q := by
  apply sub_eq_zero.mp
  have hsub := hp.sub hq
  have hzero : dehomogenize (p-q) = 0 := by rw [map_sub,h,sub_self]
  ext d
  by_cases hd : Finsupp.weight (1 : Option σ → ℕ) d = m
  · have hc := dehomogenize_coeff_of_homogeneous hsub d hd
    rw [hzero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
    exact hc.symm
  · exact IsWeightedHomogeneous.coeff_eq_zero hsub d hd

omit [Fintype σ] in
@[simp] theorem dehomogenize_C (r : R) : dehomogenize (C r : MvPolynomial (Option σ) R) = C r := by
  simp [dehomogenize]
omit [Fintype σ] in
@[simp] theorem dehomogenize_none : dehomogenize (X (none : Option σ) : MvPolynomial (Option σ) R) = 1 := by
  simp [dehomogenize]
omit [Fintype σ] in
@[simp] theorem dehomogenize_some (i : σ) : dehomogenize (X (some i) : MvPolynomial (Option σ) R) = X i := by
  simp [dehomogenize]
omit [Fintype σ] in
@[simp] theorem dehomogenize_rename (p : MvPolynomial σ R) :
    dehomogenize (rename some p) = p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]

variable [Fintype τ]
noncomputable def affineSubstitution (b : σ → R) (B : σ → τ → R) :
    MvPolynomial σ R →+* MvPolynomial τ R :=
  eval₂Hom C (fun i => C (b i) + ∑ j, C (B i j)*X j)
noncomputable def homogeneousSubstitution (b : σ → R) (B : σ → τ → R) :
    MvPolynomial σ R →+* MvPolynomial (Option τ) R :=
  eval₂Hom C (fun i => C (b i)*X none + ∑ j, C (B i j)*X (some j))

omit [Fintype σ] in
 theorem dehomogenize_homogeneousSubstitution (b : σ → R) (B : σ → τ → R)
    (p : MvPolynomial σ R) :
    dehomogenize (homogeneousSubstitution b B p) = affineSubstitution b B p := by
  have he : (dehomogenize (σ := τ) (R := R)).comp (homogeneousSubstitution b B) =
      affineSubstitution b B := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, homogeneousSubstitution, affineSubstitution,
        eval₂Hom_C, dehomogenize_C]
    · intro i
      simp only [RingHom.comp_apply, homogeneousSubstitution, affineSubstitution,
        eval₂Hom_X', map_add, map_mul, map_sum, dehomogenize_C,
        dehomogenize_none, dehomogenize_some, mul_one]
  exact RingHom.congr_fun he p

omit [Fintype σ] in

 theorem independent_padding {p : MvPolynomial σ R} {g : MvPolynomial τ R}
    {m r : ℕ} (hp : p.IsHomogeneous m) (hg : g.IsHomogeneous r) (hrm : r ≤ m)
    (b : σ → R) (B : σ → τ → R) (h : affineSubstitution b B p = g) :
    homogeneousSubstitution b B p = (X none)^(m-r) * rename some g := by
  apply homogeneous_eq_of_dehomogenize_eq (m := m)
  · change (eval₂ C _ p).IsHomogeneous m
    convert hp.eval₂ C _ (fun a => isHomogeneous_C _ a) (fun i =>
      (isHomogeneous_C_mul_X (b i) none).add
        (IsHomogeneous.sum Finset.univ _ 1 (fun j _ => isHomogeneous_C_mul_X (B i j) (some j)))) using 1; simp
  · have hg' := (isHomogeneous_X_pow (none : Option τ) (m-r)).mul (hg.rename_isHomogeneous (f := some))
    simpa only [Nat.sub_add_cancel hrm] using hg'
  · simp [dehomogenize_homogeneousSubstitution,h]
end PermanentBorder.HomogeneousPadding

namespace PermanentBorder
open MvPolynomial

 theorem permanentPolynomial_homogeneous (m : ℕ) :
    (permanentPolynomial m).IsHomogeneous m := by
  classical
  unfold permanentPolynomial
  apply IsHomogeneous.sum
  intro τ _
  convert IsHomogeneous.prod Finset.univ
    (fun i : Fin m => (X (i,τ i) : Poly (Variables m))) (fun _ => 1)
    (fun i _ => isHomogeneous_X _ _) using 1; simp

 theorem coefficientPolynomial_homogeneous (k q : ℕ) (θ : Fin k → ℂ) :
    (coefficientPolynomial k q θ).IsHomogeneous (k-2*q) := by
  simpa only [coefficientPolynomial,Fintype.card_fin] using
    Selector.coefficientPolynomial_homogeneous θ q

 theorem exists_selector_projection_homogeneous (k q m : ℕ)
    (hk : 1 ≤ k) (hq : q ≤ k/2) (hm : 11*k-2*q ≤ m) (θ : Fin k → ℂ) :
    ∃ (b : Variables m → ℂ) (B : Variables m → Variables k → ℂ),
      affineSubstitution b B (permanentPolynomial m) =
        selectorScalar k q • coefficientPolynomial k q θ ∧
      HomogeneousPadding.homogeneousSubstitution b B (permanentPolynomial m) =
        selectorScalar k q • ((X (none : Option (Variables k)))^(m-(k-2*q)) *
          rename some (coefficientPolynomial k q θ)) := by
  have hqk : q ≤ k := hq.trans (Nat.div_le_self ..)
  obtain ⟨b,B,h⟩ := exists_selector_affine_projection k q m hqk hm θ
  refine ⟨b,B,h,?_⟩
  have hg : (selectorScalar k q • coefficientPolynomial k q θ).IsHomogeneous (k-2*q) := by
    rw [smul_eq_C_mul]
    simpa only [zero_add] using
      (isHomogeneous_C (Variables k) (selectorScalar k q)).mul
        (coefficientPolynomial_homogeneous k q θ)
  have h' : HomogeneousPadding.affineSubstitution b B (permanentPolynomial m) =
      selectorScalar k q • coefficientPolynomial k q θ := h
  have hh := HomogeneousPadding.independent_padding (permanentPolynomial_homogeneous m)
    hg (by omega : k-2*q ≤ m) b B h'
  rw [hh,smul_eq_C_mul,map_mul,rename_C]
  simp only [smul_eq_C_mul]
  ring
end PermanentBorder
namespace PermanentBorder.Selector
open MvPolynomial

lemma diagonalCoefficient_map {I R S : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (M : Matrix I I R) (θ : I → R) (q : ℕ) :
    φ (diagonalCoefficient M θ q) =
      diagonalCoefficient (fun i j => φ (M i j)) (fun i => φ (θ i)) q := by
  classical
  unfold diagonalCoefficient
  rw [← coeff_map]
  apply congrArg (fun polynomial : MvPolynomial (Fin 2) S => polynomial.coeff (countIndex q))
  unfold Matrix.permanent
  simp only [map_sum,map_prod]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.prod_congr rfl
  intro i _
  simp only [Matrix.add_apply, Matrix.of_apply,Matrix.diagonal_apply,map_add,map_C]
  split_ifs <;> simp

noncomputable def integralCoefficientFamily (k q : ℕ) :
    MvPolynomial (Variables k) (MvPolynomial (Fin k) ℤ) :=
  diagonalCoefficient (Matrix.of fun i j => X (i,j)) (fun i => C (X i)) q

lemma integralCoefficientFamily_homogeneous (k q : ℕ) :
    (integralCoefficientFamily k q).IsHomogeneous (k-2*q) := by
  simpa only [integralCoefficientFamily,Fintype.card_fin] using
    coefficientPolynomial_homogeneous (fun i : Fin k => (X i : MvPolynomial (Fin k) ℤ)) q

lemma integralCoefficientFamily_specialize {K : Type*} [CommRing K]
    (k q : ℕ) (θ : Fin k → K) :
    map (eval₂Hom (Int.castRingHom K) θ) (integralCoefficientFamily k q) =
      diagonalCoefficient (Matrix.of fun i j => (X (i,j) : MvPolynomial (Variables k) K))
        (fun i => C (θ i)) q := by
  unfold integralCoefficientFamily
  rw [diagonalCoefficient_map]
  simp only [Matrix.of_apply,map_X,map_C,eval₂Hom_X']
  rfl

lemma integralCoefficientFamily_complex (k q : ℕ) (θ : Fin k → ℂ) :
    map (eval₂Hom (Int.castRingHom ℂ) θ) (integralCoefficientFamily k q) =
      coefficientPolynomial k q θ := by
  exact integralCoefficientFamily_specialize k q θ
end PermanentBorder.Selector

namespace PermanentBorder.AlgebraicDimension

open Order

theorem krullDim_le_of_injective_integral {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (hi : f.IsIntegral) :
    ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hi⟩
  change (⨆ l : LTSeries (PrimeSpectrum R), (l.length : WithBot ℕ∞)) ≤ _
  apply iSup_le
  intro l
  have h0 : (⊥ : Ideal S).comap (algebraMap R S) ≤ l.head.asIdeal := by
    rw [← RingHom.ker_eq_comap_bot]
    change RingHom.ker f ≤ _
    rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
    exact bot_le
  obtain ⟨P, _, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    l.head.asIdeal (⊥ : Ideal S) h0
  let : P.IsPrime := hP
  let : P.LiesOver l.head.asIdeal := ⟨hPc.symm⟩
  obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact le_krullDim_iff.mpr ⟨L, hlen⟩

universe u

theorem trdeg_le_of_krullDim_le {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (n : ℕ) (h : ringKrullDim A ≤ n) :
    Algebra.trdeg K A ≤ (n : Cardinal) := by
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  let : IsScalarTower K R A := IsScalarTower.of_algebraMap_eq fun k => (g.commutes k).symm
  let : Algebra.IsIntegral R A := ⟨hint⟩
  have hs : s ≤ n := by
    have hd := (krullDim_le_of_injective_integral g.toRingHom hg hint).trans h
    simpa using hd
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  have ht : Algebra.trdeg K A = s := by
    rw [← trdeg_add_eq K R (A := A), trdeg_eq_zero (R := R), add_zero]
    simp [R]
  rw [ht]
  exact_mod_cast hs

theorem field_image_trdeg_le {K A L : Type u} [Field K] [CommRing A]
    [Field L] [Algebra K A] [Algebra K L] [Algebra.FiniteType K A]
    (n : ℕ) (h : ringKrullDim A ≤ n) (f : A →ₐ[K] L) :
    Algebra.trdeg K f.range ≤ (n : Cardinal) := by
  let : Algebra.FiniteType K f.range := Algebra.FiniteType.of_surjective
    f.rangeRestrict f.rangeRestrict_surjective
  have hd : ringKrullDim f.range ≤ ringKrullDim A :=
    ringKrullDim_le_of_surjective f.rangeRestrict.toRingHom f.rangeRestrict_surjective
  exact trdeg_le_of_krullDim_le n (hd.trans h)

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem point_field_trdeg_le {K L : Type u} [Field K] [Field L] [Algebra K L]
    {v : ℕ} (I : Ideal (MvPolynomial (Fin v) K)) (n : ℕ)
    (h : ringKrullDim (MvPolynomial (Fin v) K ⧸ I) ≤ n)
    (x : Fin v → L) (hx : ∀ p ∈ I, MvPolynomial.aeval x p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) ≤ (n : Cardinal) := by
  let f := Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) hx
  have hr : f.range = Algebra.adjoin K (Set.range x) := by
    rw [← MvPolynomial.aeval_range]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨Ideal.Quotient.mk I p, rfl⟩
  have ht := field_image_trdeg_le n h f
  rw [hr] at ht
  rw [← trdeg_add_eq K (Algebra.adjoin K (Set.range x)),
    trdeg_eq_zero (R := Algebra.adjoin K (Set.range x)), add_zero]
  exact ht

end PermanentBorder.AlgebraicDimension

namespace PermanentBorder.SliceParameters

universe u
open MvPolynomial

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

open scoped IntermediateField.algebraAdjoinAdjoin in
lemma field_adjoin_trdeg_le {κ : Type*} [Fintype κ] (x : κ → L) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) ≤
      (Fintype.card κ : Cardinal) := by
  let A := Algebra.adjoin K (Set.range x)
  let y : κ → A := fun i => ⟨x i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  have htop : Algebra.adjoin K (Set.range y) = ⊤ := by
    apply Subalgebra.map_injective (show Function.Injective A.val from Subtype.val_injective)
    rw [AlgHom.map_adjoin, Algebra.map_top, A.range_val, ← Set.range_comp]
    rfl
  let : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range y)) A := by
    constructor
    intro a
    have ha : a ∈ Algebra.adjoin K (Set.range y) := by rw [htop]; trivial
    exact isAlgebraic_algebraMap (R := Algebra.adjoin K (Set.range y)) ⟨a, ha⟩
  have hA : Algebra.trdeg K A ≤ (Fintype.card κ : Cardinal) := by
    calc
      Algebra.trdeg K A ≤ Cardinal.mk (Set.range y) :=
        Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range y)
      _ ≤ Fintype.card κ := by
        simpa using (Cardinal.mk_range_le_lift (f := y))
  rw [← trdeg_add_eq K A, trdeg_eq_zero (R := A), add_zero]
  exact hA

lemma add_parameters {κ : Type*} [Fintype κ] (F : IntermediateField K L)
    (n : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal)) (z : κ → L) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ (∀ i, z i ∈ E) ∧
      Algebra.trdeg K E ≤ (n + Fintype.card κ : ℕ) := by
  let E := IntermediateField.adjoin F (Set.range z)
  let : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).mpr
    (algebraMap F E).injective
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨E.restrictScalars K, ?_, ?_, ?_⟩
  · intro x hx
    exact E.algebraMap_mem ⟨x, hx⟩
  · intro i
    exact IntermediateField.subset_adjoin F _ (Set.mem_range_self i)
  · change Algebra.trdeg K E ≤ _
    rw [← trdeg_add_eq K F]
    exact (add_le_add hF (field_adjoin_trdeg_le (K := F) z)).trans_eq (by simp)

lemma independent_card_le {κ : Type*} [Fintype κ] (H : κ → L)
    (hH : AlgebraicIndependent K H) (F : IntermediateField K L)
    (hF : ∀ i, H i ∈ F) (n : ℕ) (ht : Algebra.trdeg K F ≤ (n : Cardinal)) :
    Fintype.card κ ≤ n := by
  let x : κ → F := fun i => ⟨H i, hF i⟩
  have hx : AlgebraicIndependent K x := hH.of_comp F.val
  have hc := hx.lift_cardinalMk_le_trdeg.trans (Cardinal.lift_le.mpr ht)
  simpa using hc

end PermanentBorder.SliceParameters

end OAI
