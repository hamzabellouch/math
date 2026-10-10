import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupIntegral

namespace OAI


                                       
section

namespace MaximalSeshadri.Hartogs
noncomputable section
open MvPolynomial
open scoped Pointwise
variable (K : Type) [Field K]

lemma variable_pow_dvd_iff {σ : Type} [DecidableEq σ]
    (i : σ) (m : ℕ) (p : MvPolynomial σ K) :
    X i ^ m ∣ p ↔ ∀ d : σ →₀ ℕ, d i < m → p.coeff d = 0 := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero]
  constructor
  · intro h d hd
    have he : ¬ Finsupp.single i m ≤ d := by
      simpa only [Finsupp.single_le_iff] using (not_le.mpr hd)
    simp only [← MvPolynomial.coeff_modMonomial_of_not_le p he, h,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · intro h
    ext d
    by_cases hd : Finsupp.single i m ≤ d
    · simp [MvPolynomial.coeff_modMonomial_of_le p hd]
    · rw [MvPolynomial.coeff_modMonomial_of_not_le p hd, AddMonoidAlgebra.coeff_zero]
      exact h d (by simpa only [Finsupp.single_le_iff, not_le] using hd)

lemma power_variable_dvd_other_mul {σ : Type} [DecidableEq σ]
    (i j : σ) (hij : i ≠ j) (m n : ℕ) (p : MvPolynomial σ K)
    (hp : X i ^ m ∣ X j ^ n * p) : X i ^ m ∣ p := by
  rw [variable_pow_dvd_iff] at hp ⊢
  intro d hd
  have h := hp (Finsupp.single j n + d) (by simpa [Finsupp.single_eq_of_ne hij] using hd)
  rw [X_pow_eq_monomial, coeff_monomial_mul, one_mul] at h
  exact h

lemma mem_smul_top_iff_dvd {A : Type*} [CommRing A] (x a : A) :
    a ∈ x • (⊤ : Submodule A A) ↔ x ∣ a := by
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
    smul_eq_mul, dvd_def, eq_comm]

lemma polynomial_power_sequence {σ : Type} [DecidableEq σ] (i j : σ)
    (hij : i ≠ j) (m n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ K) [(X i : MvPolynomial σ K) ^ m, X j ^ n] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_cons_iff]
  refine ⟨(isRegular_iff_ne_zero.mpr (pow_ne_zero m (X_ne_zero i))).isSMulRegular, ?_,
    RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro p hp
  rw [mem_smul_top_iff_dvd] at hp ⊢
  exact power_variable_dvd_other_mul K i j hij m n p hp

lemma flat_power_sequence {A : Type*} [CommRing A]
    [Algebra (MvPolynomial (Fin 2) K) A] [Module.Flat (MvPolynomial (Fin 2) K) A]
    (m n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular A
      [(algebraMap (MvPolynomial (Fin 2) K) A (X 0))^m,
       (algebraMap (MvPolynomial (Fin 2) K) A (X 1))^n] := by
  simpa using (polynomial_power_sequence K (0 : Fin 2) 1 (by decide) m n).of_flat (S := A)

lemma flat_cancel_other_coordinate {A : Type*} [CommRing A]
    [Algebra (MvPolynomial (Fin 2) K) A] [Module.Flat (MvPolynomial (Fin 2) K) A]
    (m n : ℕ) (a : A)
    (h : (algebraMap (MvPolynomial (Fin 2) K) A (X 0))^m ∣
      (algebraMap (MvPolynomial (Fin 2) K) A (X 1))^n * a) :
    (algebraMap (MvPolynomial (Fin 2) K) A (X 0))^m ∣ a := by
  have hs := flat_power_sequence K (A := A) m n
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_cons_iff] at hs
  have ht := (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mp hs.2.1 a
  simpa only [mem_smul_top_iff_dvd, smul_eq_mul] using ht (by
    simpa only [mem_smul_top_iff_dvd, smul_eq_mul] using h)

theorem flat_hartogs {A F : Type*} [CommRing A] [IsDomain A] [Field F]
    [Algebra (MvPolynomial (Fin 2) K) A] [Module.Flat (MvPolynomial (Fin 2) K) A]
    [Algebra A F] [IsFractionRing A F] (z : F)
    (hx : ∃ m : ℕ, ∃ a : A,
      algebraMap A F ((algebraMap (MvPolynomial (Fin 2) K) A (X 0))^m) * z = algebraMap A F a)
    (hy : ∃ n : ℕ, ∃ b : A,
      algebraMap A F ((algebraMap (MvPolynomial (Fin 2) K) A (X 1))^n) * z = algebraMap A F b) :
    ∃ c : A, algebraMap A F c = z := by
  obtain ⟨m, a, ha⟩ := hx
  obtain ⟨n, b, hb⟩ := hy
  let x : A := algebraMap (MvPolynomial (Fin 2) K) A (X 0)
  let y : A := algebraMap (MvPolynomial (Fin 2) K) A (X 1)
  have hc : y^n * a = x^m * b := by
    apply IsFractionRing.injective A F
    simp only [map_mul]
    change algebraMap A F (y^n) * algebraMap A F a =
      algebraMap A F (x^m) * algebraMap A F b
    rw [← ha, ← hb]
    ring
  obtain ⟨c, hc⟩ := flat_cancel_other_coordinate K m n a ⟨b, hc⟩
  refine ⟨c, ?_⟩
  have hx0 : x ≠ 0 := by
    have hr := (flat_power_sequence K (A := A) 1 0)
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hr
    have hi := hr.1
    simp only [pow_one] at hi
    intro hx0
    have he : x • (1 : A) = x • (0 : A) := by simp [hx0]
    exact one_ne_zero (hi he)
  have hxF : algebraMap A F (x^m) ≠ 0 :=
    fun h => pow_ne_zero m hx0 ((IsFractionRing.injective A F) (by simpa using h))
  apply mul_left_cancel₀ hxF
  rw [← map_mul, ← hc]
  exact ha.symm

end
end MaximalSeshadri.Hartogs

namespace MaximalSeshadri.Hartogs
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable (K : Type) [Field K] (X : Scheme) [IsIntegral X] [IsAffine X]

local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

omit [IsAffine X] in
lemma functionField_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : U ≤ V) (s : Γ(X, V)) :
    X.germToFunctionField U (X.presheaf.map (homOfLE h).op s) =
      X.germToFunctionField V s :=
  X.presheaf.germ_res_apply (homOfLE h) _ _ s

omit [IsAffine X] in
lemma basicOpen_nonempty (x : Γ(X, ⊤)) (hx : x ≠ 0) : Nonempty (X.basicOpen x) := by
  by_contra h
  exact hx ((basicOpen_eq_bot_iff x).mp ((Opens.not_nonempty_iff_eq_bot _).mp (fun ⟨p, hp⟩ => h ⟨⟨p, hp⟩⟩)))

lemma coordinate_denominator {U : X.Opens} [Nonempty U] (s : Γ(X, U))
    (x : Γ(X, ⊤)) (hx : x ≠ 0) (h : X.basicOpen x ≤ U) :
    ∃ m : ℕ, ∃ a : Γ(X, ⊤),
      algebraMap Γ(X, ⊤) X.functionField (x^m) * X.germToFunctionField U s =
        algebraMap Γ(X, ⊤) X.functionField a := by
  let := basicOpen_nonempty X x hx
  let t : Γ(X, X.basicOpen x) := X.presheaf.map (homOfLE h).op s
  let q := IsLocalization.Away.sec x t
  refine ⟨q.2, q.1, ?_⟩
  have he := congrArg (X.germToFunctionField (X.basicOpen x))
    (IsLocalization.Away.sec_spec x t)
  change (X.germToFunctionField (X.basicOpen x)).hom
      (t * algebraMap Γ(X, ⊤) Γ(X, X.basicOpen x) (x^q.2)) =
    (X.germToFunctionField (X.basicOpen x)).hom
      (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen x) q.1) at he
  rw [map_mul] at he
  change X.germToFunctionField (X.basicOpen x) t *
      X.germToFunctionField (X.basicOpen x)
        (X.presheaf.map (homOfLE (X.basicOpen_le x)).op (x^q.2)) =
    X.germToFunctionField (X.basicOpen x)
      (X.presheaf.map (homOfLE (X.basicOpen_le x)).op q.1) at he
  rw [functionField_restrict, functionField_restrict] at he
  dsimp only [t] at he
  rw [functionField_restrict] at he
  exact (mul_comm _ _).trans he

theorem affine_hartogs
    [Algebra (MvPolynomial (Fin 2) K) Γ(X, ⊤)]
    [Module.Flat (MvPolynomial (Fin 2) K) Γ(X, ⊤)]
    (U : X.Opens)
    (h0 : X.basicOpen (algebraMap (MvPolynomial (Fin 2) K) Γ(X, ⊤)
      (MvPolynomial.X 0)) ≤ U)
    (h1 : X.basicOpen (algebraMap (MvPolynomial (Fin 2) K) Γ(X, ⊤)
      (MvPolynomial.X 1)) ≤ U) (s : Γ(X, U)) :
    ∃! t : Γ(X, ⊤), X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op t = s := by
  let x : Γ(X, ⊤) := algebraMap (MvPolynomial (Fin 2) K) Γ(X, ⊤) (MvPolynomial.X 0)
  let y : Γ(X, ⊤) := algebraMap (MvPolynomial (Fin 2) K) Γ(X, ⊤) (MvPolynomial.X 1)
  have hreg := flat_power_sequence K (A := Γ(X, ⊤)) 1 1
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hreg
  have hx : x ≠ 0 := by
    intro he
    have hi := hreg.1
    simp only [pow_one] at hi
    apply one_ne_zero (hi (a₁ := (1 : Γ(X, ⊤))) (a₂ := 0) ?_)
    change x * 1 = x * 0
    simp [he]
  have hy : y ≠ 0 := by
    have hs := (polynomial_power_sequence K (1 : Fin 2) 0 (by decide) 1 1).of_flat
      (S := Γ(X, ⊤))
    simp only [List.map_cons, List.map_nil] at hs
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hs
    have hi := hs.1
    simp only [pow_one] at hi
    intro he
    apply one_ne_zero (hi (a₁ := (1 : Γ(X, ⊤))) (a₂ := 0) ?_)
    change y * 1 = y * 0
    simp [he]
  let : Nonempty U := (basicOpen_nonempty X x hx).map fun p => ⟨p.1, h0 p.2⟩
  let := functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  obtain ⟨t, ht⟩ := flat_hartogs K (X.germToFunctionField U s)
    (coordinate_denominator X s x hx h0) (coordinate_denominator X s y hy h1)
  refine ⟨t, ?_, ?_⟩
  · apply X.germToFunctionField_injective U
    rw [functionField_restrict]
    exact ht
  · intro t' ht'
    apply X.germToFunctionField_injective ⊤
    change algebraMap Γ(X, ⊤) X.functionField t' =
      algebraMap Γ(X, ⊤) X.functionField t
    rw [ht]
    rw [← ht', functionField_restrict]
    rfl

end
end MaximalSeshadri.Hartogs

namespace MaximalSeshadri.Hartogs
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {X B U : Scheme.{0}}

lemma open_appTop_injective [IsIntegral X] [Nonempty U]
    (j : U ⟶ X) [IsOpenImmersion j] : Function.Injective j.appTop := by
  let : Nonempty (j.opensRange ⊓ ⊤ : X.Opens) :=
    Nonempty.map (fun u : U => ⟨j u, ⟨⟨u, rfl⟩, trivial⟩⟩) inferInstance
  intro a b h
  apply map_injective_of_isIntegral X (homOfLE (show j.opensRange ⊓ ⊤ ≤ ⊤ from le_top))
  have he := congrArg (IsOpenImmersion.ΓIso j ⊤).hom h
  change (j.app ⊤ ≫ (IsOpenImmersion.ΓIso j ⊤).hom) a =
    (j.app ⊤ ≫ (IsOpenImmersion.ΓIso j ⊤).hom) b at he
  rwa [IsOpenImmersion.app_ΓIso_hom] at he

lemma restrict_topIso (V : X.Opens) :
    V.ι.appTop ≫ V.topIso.hom = X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
  exact (X.presheaf.map_comp (homOfLE (x := V.ι ''ᵁ ⊤) le_top).op
    (eqToHom V.ι_image_top.symm).op).symm

theorem blowup_descend (K : Type) [Field K] [IsIntegral X] [IsAffine X] [IsIntegral B]
    [Algebra (MvPolynomial (Fin 2) K) Γ(X, ⊤)]
    [Module.Flat (MvPolynomial (Fin 2) K) Γ(X, ⊤)]
    {I : X.IdealSheafData} {π : B ⟶ X} (hπ : Geometry.IsBlowup I π)
    (hI : I.support ≠ ⊤)
    (h0 : X.basicOpen (algebraMap (MvPolynomial (Fin 2) K) Γ(X, ⊤)
      (MvPolynomial.X 0)) ≤ Geometry.centreComplement I)
    (h1 : X.basicOpen (algebraMap (MvPolynomial (Fin 2) K) Γ(X, ⊤)
      (MvPolynomial.X 1)) ≤ Geometry.centreComplement I)
    (s : Γ(B, ⊤)) : ∃! a : Γ(X, ⊤), π.appTop a = s := by
  let V := Geometry.centreComplement I
  let : Nonempty V.toScheme := Geometry.complement_nonempty hI
  let t : Γ(X, V) := V.topIso.hom (hπ.complementLift.appTop s)
  obtain ⟨a, ha, huniq⟩ := affine_hartogs K X V h0 h1 t
  have hae : π.appTop a = s := by
    apply open_appTop_injective hπ.complementLift
    apply (ConcreteCategory.bijective_of_isIso V.topIso.hom).injective
    change (π.appTop ≫ hπ.complementLift.appTop ≫ V.topIso.hom) a = t
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, Geometry.IsBlowup.complementLift_comp,
      restrict_topIso]
    exact ha
  refine ⟨a, hae, fun b hb => ?_⟩
  apply huniq b
  change (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op) b = t
  rw [← restrict_topIso]
  rw [← Geometry.IsBlowup.complementLift_comp hπ, Scheme.Hom.comp_appTop]
  change V.topIso.hom (hπ.complementLift.appTop (π.appTop b)) = t
  rw [hb]

end
end MaximalSeshadri.Hartogs

end

end OAI
