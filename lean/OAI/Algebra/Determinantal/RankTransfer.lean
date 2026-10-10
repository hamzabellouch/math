import OAI.Algebra.Determinantal.GenericPolars

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma exists_matrix_right_inverse {K α β : Type*} [Field K] [Fintype α] [Fintype β] [DecidableEq α]
    (A : Matrix α β K) (hA : Function.Surjective A.mulVec) :
    ∃ B : Matrix β α K, A * B = 1 := by
  classical
  choose b hb using fun i : α => hA (Pi.single i 1)
  refine ⟨fun j i => b i j, ?_⟩
  ext i j
  change (A.mulVec (b j)) i = (1 : Matrix α α K) i j
  rw [hb]
  simp [Matrix.one_apply, Pi.single_apply]

theorem integer_polynomial_rank_transfer {K L σ α β : Type*}
    [Field K] [Field L] [CharZero L] [Infinite L] [Fintype α] [Fintype β]
    (P : Matrix α β (MvPolynomial σ ℤ)) (x : σ → K)
    (hP : Function.Surjective (P.map (eval₂Hom (Int.castRingHom K) x)).mulVec) :
    ∃ y : σ → L,
      Function.Surjective (P.map (eval₂Hom (Int.castRingHom L) y)).mulVec := by
  classical
  let τ := σ ⊕ (β × α)
  let A : Matrix α β (MvPolynomial τ ℤ) := P.map (rename Sum.inl)
  let B : Matrix β α (MvPolynomial τ ℤ) := fun i j => X (Sum.inr (i,j))
  let p : MvPolynomial τ ℤ := (A*B).det
  obtain ⟨b,hb⟩ := exists_matrix_right_inverse _ hP
  let z : τ → K := Sum.elim x (fun ij => b ij.1 ij.2)
  let φ : MvPolynomial τ ℤ →+* K := eval₂Hom (Int.castRingHom K) z
  have hA : A.map φ = P.map (eval₂Hom (Int.castRingHom K) x) := by
    ext i j
    simp [A, φ, z, Matrix.map_apply, eval₂_rename, Function.comp_def]
  have hB : B.map φ = b := by
    ext i j
    change φ (X (Sum.inr (i,j))) = b i j
    exact eval₂_X _ _ _
  have hp : φ p = 1 := by
    rw [show φ p = (φ.mapMatrix (A*B)).det from RingHom.map_det φ (A*B)]
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, hA, hB, hb]
    exact Matrix.det_one
  have hpn : p ≠ 0 := by
    intro h
    have : (0 : K) = 1 := by simpa only [h, map_zero] using hp
    exact zero_ne_one this
  let pL : MvPolynomial τ L := map (Int.castRingHom L) p
  have hpLn : pL ≠ 0 := by
    simpa only [map_zero] using
      (MvPolynomial.map_injective (Int.castRingHom L) Int.cast_injective).ne hpn
  obtain ⟨w,hw⟩ : ∃ w : τ → L, eval w pL ≠ 0 := by
    by_contra h
    apply hpLn
    apply MvPolynomial.funext
    intro w
    simp only [map_zero]
    exact not_not.mp (not_exists.mp h w)
  let ψ : MvPolynomial τ ℤ →+* L := eval₂Hom (Int.castRingHom L) w
  have hψ : ψ p ≠ 0 := by
    simpa only [pL, eval_map, ψ, coe_eval₂Hom] using hw
  have hu : IsUnit ((A*B).map ψ) := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.mpr hψ
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  refine ⟨fun i => w (Sum.inl i), ?_⟩
  have hAL : A.map ψ = P.map (eval₂Hom (Int.castRingHom L) (fun i => w (Sum.inl i))) := by
    ext i j
    simp [A, ψ, Matrix.map_apply, eval₂_rename, Function.comp_def]
  intro v
  obtain ⟨t,ht⟩ := hs v
  refine ⟨(B.map ψ).mulVec t, ?_⟩
  rw [← hAL, Matrix.mulVec_mulVec]
  simpa only [Matrix.map_mul] using ht

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

theorem polynomial_rank_specialize {K L σ α β : Type*}
    [Field K] [Field L] [Algebra K L] [Infinite K] [Fintype α] [Fintype β]
    (P : Matrix α β (MvPolynomial σ K)) (x : σ → L)
    (hP : Function.Surjective (P.map (eval₂Hom (algebraMap K L) x)).mulVec) :
    ∃ y : σ → K,
      Function.Surjective (P.map (eval₂Hom (RingHom.id K) y)).mulVec := by
  classical
  let τ := σ ⊕ (β × α)
  let A : Matrix α β (MvPolynomial τ K) := P.map (rename Sum.inl)
  let B : Matrix β α (MvPolynomial τ K) := fun i j => X (Sum.inr (i,j))
  let p : MvPolynomial τ K := (A*B).det
  obtain ⟨b,hb⟩ := exists_matrix_right_inverse _ hP
  let z : τ → L := Sum.elim x (fun ij => b ij.1 ij.2)
  let φ : MvPolynomial τ K →+* L := eval₂Hom (algebraMap K L) z
  have hA : A.map φ = P.map (eval₂Hom (algebraMap K L) x) := by
    ext i j
    simp [A, φ, z, Matrix.map_apply, eval₂_rename, Function.comp_def]
  have hB : B.map φ = b := by
    ext i j
    change φ (X (Sum.inr (i,j))) = b i j
    exact eval₂_X _ _ _
  have hp : φ p = 1 := by
    rw [show φ p = (φ.mapMatrix (A*B)).det from RingHom.map_det φ (A*B)]
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, hA, hB, hb]
    exact Matrix.det_one
  have hpn : p ≠ 0 := by
    intro h
    have : (0 : L) = 1 := by simpa only [h, map_zero] using hp
    exact zero_ne_one this
  obtain ⟨w,hw⟩ : ∃ w : τ → K, eval w p ≠ 0 := by
    by_contra h
    apply hpn
    apply MvPolynomial.funext
    intro w
    simp only [map_zero]
    exact not_not.mp (not_exists.mp h w)
  let ψ : MvPolynomial τ K →+* K := eval₂Hom (RingHom.id K) w
  have hψ : ψ p ≠ 0 := by
    exact hw
  have hu : IsUnit ((A*B).map ψ) := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.mpr hψ
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  refine ⟨fun i => w (Sum.inl i), ?_⟩
  have hAL : A.map ψ = P.map (eval₂Hom (RingHom.id K) (fun i => w (Sum.inl i))) := by
    ext i j
    simp [A, ψ, Matrix.map_apply, eval₂_rename, Function.comp_def]
  intro v
  obtain ⟨t,ht⟩ := hs v
  refine ⟨(B.map ψ).mulVec t, ?_⟩
  rw [← hAL, Matrix.mulVec_mulVec]
  simpa only [Matrix.map_mul] using ht

end PermanentBorder.SliceParameters

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters

lemma smooth_extension {K L σ : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
    [Fintype σ] (f : MvPolynomial σ K)
    (hs : ∀ y : σ → K, eval y f = 0 → (∀ j, eval y (pderiv j f) = 0) → y = 0)
    (y : σ → L) (hf : aeval y f = 0) (hd : ∀ j, aeval y (pderiv j f) = 0) : y = 0 := by
  classical
  let F : Option σ → MvPolynomial σ K := fun i => match i with
    | none => f
    | some j => pderiv j f
  let I := Ideal.span (Set.range F)
  have hz : ∀ x ∈ zeroLocus K I, x = 0 := by
    intro x hx
    apply hs x
    · exact hx _ (Ideal.subset_span ⟨none,rfl⟩)
    · intro j
      exact hx _ (Ideal.subset_span ⟨some j,rfl⟩)
  have hy : y ∈ zeroLocus L I := by
    rw [zeroLocus_span]
    rintro _ ⟨i,rfl⟩
    cases i with
    | none => exact hf
    | some j => exact hd j
  ext j
  obtain ⟨n,hn⟩ := variable_power_certificate I hz j
  have hpow : y j ^ n = 0 := by simpa using hy _ hn
  by_contra h
  exact pow_ne_zero n h hpow

section Generic
variable {K τ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

lemma generic_bad_zero (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → K, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0)
    (y : PolarVars τ → E)
    (hy : ∀ i, eval y (badPolarSystem genericDirections genericLinear (map (algebraMap K E) f) i) = 0) :
    y = 0 := by
  classical
  by_contra hyn
  have hf : aeval y f = 0 := by simpa [badPolarSystem, eval_map, aeval_def] using hy none
  have hp : ∀ i, polarValue genericDirections f y i = 0 := by
    intro i
    simpa only [badPolarSystem, eval_polarPolynomial] using hy (some (some i))
  have hg : ∃ j, aeval y (pderiv j f) ≠ 0 := by
    by_contra h
    exact hyn (smooth_extension f hs y hf (by simpa only [not_exists, not_not] using h))
  have hn : ∑ j, genericLinear j * y j ≠ 0 := fun h =>
    hyn (generic_no_infinity f hh y hf hp hg h)
  have hu := generic_square_isUnit f hh y hf hp hyn hg
  have hj : (squareJacobian genericDirections genericLinear f y).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hb := hy (some none)
  simp only [badPolarSystem, map_mul, eval_linearPolynomial, RingHom.map_det,
    RingHom.mapMatrix_apply, eval_squarePolynomial] at hb
  exact (mul_ne_zero hn hj) hb

noncomputable def universalBadPolar (f : MvPolynomial (PolarVars τ) K) :
    PolarVars τ → MvPolynomial (PolarVars τ) (MvPolynomial P K) :=
  badPolarSystem (fun i j => X (some i,j)) (fun j => X (none,j)) (map C f)

omit [CharZero K] [IsAlgClosed K] in
lemma universalBadPolar_specialize {L : Type*} [Field L] [Algebra K L]
    (f : MvPolynomial (PolarVars τ) K) (w : P → L) (i : PolarVars τ) :
    map (eval₂Hom (algebraMap K L) w) (universalBadPolar f i) =
      badPolarSystem (fun i j => w (some i,j)) (fun j => w (none,j))
        (map (algebraMap K L) f) i := by
  rw [universalBadPolar, map_badPolarSystem, MvPolynomial.map_map]
  have hc : (eval₂Hom (algebraMap K L) w).comp C = algebraMap K L := by ext; simp
  rw [hc]
  simp only [MvPolynomial.eval₂Hom_X']

theorem exists_good_polar_certificate (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → K, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → K, ∃ l : PolarVars τ → K, ∃ D : ℕ,
      Function.Surjective (macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ))
        (badPolarSystem w l f) D).mulVec := by
  classical
  let F := badPolarSystem (genericDirections (K := K) (τ := τ)) genericLinear
    (map (algebraMap K E) f)
  have hhom (i : PolarVars τ) : (F i).IsHomogeneous (badPolarDegrees τ r i) :=
    badPolarSystem_homogeneous _ _ (hh.map _) i
  have hz : ∀ y ∈ zeroLocus E (Ideal.span (Set.range F)), y = 0 := by
    intro y hy
    apply generic_bad_zero f hh hs y
    intro i
    exact hy _ Ideal.mem_span_range_self
  obtain ⟨D,hD⟩ := homogeneous_piece_certificate (Ideal.span (Set.range F)) hz
  have hM : Function.Surjective
      (macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) F D).mulVec := by
    apply (macaulay_surjective_iff _ _ (fun i => homogeneous_intWeight (hhom i)) D).mpr
    intro p hp
    exact hD p (intWeight_homogeneous hp)
  let M := macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) (universalBadPolar f) D
  have hMa : Function.Surjective (M.map (eval₂Hom (algebraMap K E) (genericParameter K P))).mulVec := by
    have he : M.map (eval₂Hom (algebraMap K E) (genericParameter K P)) =
        macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) F D := by
      rw [← macaulayMatrix_map]
      apply congrArg (fun Q => macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) Q D)
      funext i
      exact universalBadPolar_specialize f (genericParameter K P) i
    rwa [he]
  obtain ⟨a,ha⟩ := polynomial_rank_specialize M (genericParameter K P) hMa
  refine ⟨fun i j => a (some i,j), fun j => a (none,j), D, ?_⟩
  have he : M.map (eval₂Hom (RingHom.id K) a) =
      macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ))
        (badPolarSystem (fun i j => a (some i,j)) (fun j => a (none,j)) f) D := by
    rw [← macaulayMatrix_map]
    apply congrArg (fun Q => macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ)) Q D)
    funext i
    simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using universalBadPolar_specialize f a i
  rwa [he] at ha

end Generic
end PermanentBorder.Polar

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters
open scoped Classical
variable {τ : Type*} [Fintype τ]

noncomputable def hypersurfacePolars (w : τ → PolarVars τ → ℂ)
    (f : MvPolynomial (PolarVars τ) ℂ) : Option τ → MvPolynomial (PolarVars τ) ℂ :=
  Option.elim' f (polarPolynomial w f)

def hypersurfaceDegrees (r : ℕ) : Option τ → ℕ := Option.elim' r (fun _ => r-1)

lemma hypersurfacePolars_homogeneous (w : τ → PolarVars τ → ℂ)
    {f : MvPolynomial (PolarVars τ) ℂ} {r : ℕ} (hh : f.IsHomogeneous r) (i : Option τ) :
    (hypersurfacePolars w f i).IsHomogeneous (hypersurfaceDegrees r i) := by
  cases i with
  | none => exact hh
  | some i => exact polarPolynomial_homogeneous w hh i

def swapFirstRows : Equiv.Perm (PolarVars τ) where
  toFun := Option.elim' (some none) (Option.elim' none (fun i => some (some i)))
  invFun := Option.elim' (some none) (Option.elim' none (fun i => some (some i)))
  left_inv := by rintro (_ | (_ | i)) <;> rfl
  right_inv := by rintro (_ | (_ | i)) <;> rfl

lemma hypersurfacePolars_square (w : τ → PolarVars τ → ℂ) (l : PolarVars τ → ℂ)
    (f : MvPolynomial (PolarVars τ) ℂ) :
    CI.square (hypersurfacePolars w f) l =
      (squarePolynomial w l f).submatrix swapFirstRows id := by
  ext i j
  rcases i with _ | (_ | i) <;>
    simp [CI.square, hypersurfacePolars, squarePolynomial, Matrix.submatrix, swapFirstRows]

lemma determinant_permutation_ne_zero {n : Type*} [Fintype n]
    (d₁ d₂ : DecidableEq n) (A B : Matrix n n ℂ) (e : Equiv.Perm n)
    (he : B = A.submatrix e id) (ha : @Matrix.det n d₁ _ ℂ _ A ≠ 0) :
    @Matrix.det n d₂ _ ℂ _ B ≠ 0 := by
  subst B
  cases Subsingleton.elim d₁ d₂
  rw [Matrix.det_permute]
  exact mul_ne_zero (by exact_mod_cast (Equiv.Perm.sign e).ne_zero) ha

lemma polar_certificate_good (w : τ → PolarVars τ → ℂ) (l : PolarVars τ → ℂ)
    (f : MvPolynomial (PolarVars τ) ℂ) {r : ℕ} (hh : f.IsHomogeneous r) (D : ℕ)
    (hM : Function.Surjective (macaulayMatrix (fun i => (badPolarDegrees τ r i : ℤ))
      (badPolarSystem w l f) D).mulVec) : CI.Good (hypersurfacePolars w f) l := by
  classical
  have hz := macaulay_surjective_zero (badPolarSystem w l f) (badPolarDegrees τ r)
    (badPolarSystem_homogeneous w l hh) D hM
  intro y hn hy
  have hp : eval y (linearPolynomial l) * ((squarePolynomial w l f).map (eval y)).det ≠ 0 := by
    intro he
    apply hn (hz y ?_)
    rintro (_ | (_ | i))
    · exact hy none
    · simpa only [badPolarSystem, map_mul, RingHom.map_det, RingHom.mapMatrix_apply] using he
    · exact hy (some i)
  refine ⟨(mul_ne_zero_iff.mp hp).1, ?_⟩
  have he : (CI.square (hypersurfacePolars w f) l).map (eval y) =
      ((squarePolynomial w l f).map (eval y)).submatrix swapFirstRows id := by
    rw [hypersurfacePolars_square]
    rfl
  exact determinant_permutation_ne_zero _ _ _ _ swapFirstRows he (mul_ne_zero_iff.mp hp).2

theorem smooth_polar_count (f : MvPolynomial (PolarVars τ) ℂ) {r : ℕ} (hr : 2 ≤ r)
    (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → ℂ, ∃ l : PolarVars τ → ℂ,
      CI.Good (hypersurfacePolars w f) l ∧
      Nat.card (CI.Roots (hypersurfacePolars w f) l) = r * (r-1) ^ Fintype.card τ := by
  obtain ⟨w,l,D,hD⟩ := exists_good_polar_certificate f hh hs
  have hg := polar_certificate_good w l f hh D hD
  refine ⟨w,l,hg,?_⟩
  have hc := CI.good_card (hypersurfacePolars w f) l (hypersurfaceDegrees r)
    (by rintro (_ | i) <;> simp only [hypersurfaceDegrees,Option.elim'_none,Option.elim'_some] <;> omega)
    (hypersurfacePolars_homogeneous w hh) hg
  simpa [hypersurfaceDegrees] using hc

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

noncomputable def coordinateSplit (l : Option ι → ℂ) (h : l none ≠ 0) :
    (Option ι → ℂ) ≃ₗ[ℂ] (Option ι → ℂ) where
  toFun y := Option.elim' (∑ j, l j * y j) (fun i => y (some i))
  invFun z := Option.elim' ((z none - ∑ i, l (some i) * z (some i)) / l none)
    (fun i => z (some i))
  left_inv y := by
    funext i
    cases i with
    | none => simp only [Option.elim'_none, Option.elim'_some, Fintype.sum_option]
              field_simp
              ring
    | some i => rfl
  right_inv z := by
    funext i
    cases i with
    | none => simp only [Option.elim'_none, Option.elim'_some, Fintype.sum_option]
              field_simp
              ring
    | some i => rfl
  map_add' y z := by
    funext i
    cases i <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    funext i
    cases i with
    | none =>
      change (∑ j, l j * (c * y j)) = c * ∑ j, l j * y j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    | some i => rfl

lemma coordinateSplit_none (l : Option ι → ℂ) (h : l none ≠ 0) (y : Option ι → ℂ) :
    coordinateSplit l h y none = ∑ j, l j * y j := rfl

lemma exists_normalizer_equiv (l : Option ι → ℂ) (hl : l ≠ 0) :
    ∃ e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ),
      ∀ y, e y none = ∑ j, l j * y j := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, l i ≠ 0 := by
    by_contra! h
    exact hl (funext h)
  let p := Equiv.swap none i
  let c : (Option ι → ℂ) ≃ₗ[ℂ] (Option ι → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ p.symm
  have hc (y : Option ι → ℂ) (j : Option ι) : c y j = y (p j) := rfl
  let l' := fun j => l (p j)
  have hl' : l' none ≠ 0 := by simpa [l',p] using hi
  let e := c.trans (coordinateSplit l' hl')
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  intro y
  change (coordinateSplit l' hl' (c y)) none = _
  rw [coordinateSplit_none]
  change (∑ j, l (p j) * y (p j)) = _
  exact Equiv.sum_comp p (fun j => l j * y j)

noncomputable def optionInsert : (ι → ℂ) →L[ℂ] (Option ι → ℂ) :=
  ContinuousLinearMap.pi (fun i => match i with
    | none => 0
    | some j => ContinuousLinearMap.proj j)

omit [Fintype ι] in
@[simp] lemma optionInsert_none (v : ι → ℂ) : optionInsert v none = 0 := rfl
omit [Fintype ι] in
@[simp] lemma optionInsert_some (v : ι → ℂ) (i : ι) : optionInsert v (some i) = v i := rfl

noncomputable def affineNormChart
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) (z : ι → ℂ) : Option ι → ℂ :=
  e.symm (Option.elim' 1 z)

lemma affineNormChart_hasFDerivAt
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) (z : ι → ℂ) :
    HasFDerivAt (affineNormChart e)
      (e.symm.toContinuousLinearMap.comp optionInsert) z := by
  have h : HasFDerivAt (fun z : ι → ℂ => Option.elim' 1 z) optionInsert z := by
    apply hasFDerivAt_pi.mpr
    rintro (_ | i)
    · exact hasFDerivAt_const _ _
    · exact (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt
  exact e.symm.hasFDerivAt.comp z h

lemma affineNormChart_contDiff
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) (n : ℕ∞) :
    ContDiff ℂ n (affineNormChart e) := by
  apply e.symm.contDiff.comp
  apply contDiff_pi.mpr
  rintro (_ | i)
  · exact contDiff_const
  · exact contDiff_apply ℂ ℂ i

omit [Fintype ι] in
lemma affineNormChart_injective
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) : Function.Injective (affineNormChart e) := by
  intro x y h
  have hxy := e.symm.injective h
  exact funext (fun i => congrFun hxy (some i))

omit [Fintype ι] in
lemma exists_chart_preimage
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) {y : Option ι → ℂ}
    (hy : e y none = 1) : ∃ z, affineNormChart e z = y := by
  refine ⟨fun i => e y (some i), ?_⟩
  apply e.injective
  rw [affineNormChart, e.apply_symm_apply]
  funext i
  cases i <;> simp [hy]

lemma affineNormChart_eq
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) (z : ι → ℂ) (j : Option ι) :
    affineNormChart e z j = e.symm (Pi.single none 1) j +
      ∑ i, e.symm (Pi.single (some i) 1) j * z i := by
  classical
  have hd : Option.elim' 1 z = Pi.single none 1 + ∑ i, z i • Pi.single (some i) 1 := by
    funext j
    cases j <;> simp [Pi.single_apply]
  rw [affineNormChart, hd, map_add, map_sum]
  simp [Finset.sum_apply, mul_comm]

end PermanentBorder.Polar

end OAI
