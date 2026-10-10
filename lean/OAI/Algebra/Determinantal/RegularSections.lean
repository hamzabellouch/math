import OAI.Algebra.Determinantal.BilinearCounts

namespace OAI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
section Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι]

noncomputable def linear (l : Option ι → R) : MvPolynomial (Option ι) R :=
  ∑ j, C (l j) * X j

noncomputable def normalized (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) :
    Option ι → MvPolynomial (Option ι) R := Option.elim' (linear l - 1) H

noncomputable def square (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) :
    Matrix (Option ι) (Option ι) (MvPolynomial (Option ι) R) :=
  fun i j => match i with | none => C (l j) | some k => pderiv j (H k)

noncomputable def bad (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) :
    Option ι → MvPolynomial (Option ι) R := Option.elim' (linear l * (square H l).det) H

def degrees (e : ι → ℕ) : Option ι → ℕ := Option.elim' (1 + ∑ i, (e i - 1)) e

lemma linear_homogeneous (l : Option ι → R) : (linear l).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  simpa using (isHomogeneous_C (Option ι) (l j)).mul (isHomogeneous_X R j)

lemma pderiv_linear (l : Option ι → R) (j : Option ι) : pderiv j (linear l) = C (l j) := by
  classical
  cases j <;> simp [linear, pderiv_X, Pi.single_apply]

lemma pderiv_normalized (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R)
    (i j : Option ι) : pderiv j (normalized H l i) = square H l i j := by
  cases i <;> simp [normalized, square, pderiv_linear]

lemma eval_linear (l y : Option ι → R) : eval y (linear l) = ∑ j, l j * y j := by
  simp [linear]

lemma det_homogeneous {σ n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial σ R)) (e : n → ℕ)
    (hA : ∀ i j, (A i j).IsHomogeneous (e i)) : A.det.IsHomogeneous (∑ i, e i) := by
  classical
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro p _
  have hp : (∏ i, A (p i) i).IsHomogeneous (∑ i, e (p i)) :=
    IsHomogeneous.prod _ _ _ (fun i _ => hA _ _)
  rw [Equiv.sum_comp] at hp
  change (p.sign : ℤ) • (∏ i, A (p i) i) ∈
    (homogeneousSubmodule σ R (∑ i, e i)).restrictScalars ℤ
  exact Submodule.smul_mem _ _ hp

lemma square_det_homogeneous (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R)
    (e : ι → ℕ) (hH : ∀ i, (H i).IsHomogeneous (e i)) :
    (square H l).det.IsHomogeneous (∑ i, (e i - 1)) := by
  classical
  have h := det_homogeneous (square H l) (Option.elim' 0 (fun i => e i - 1)) (by
    intro i j
    cases i with
    | none => exact isHomogeneous_C _ _
    | some i => exact (hH i).pderiv)
  simpa using h

lemma bad_homogeneous (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R)
    (e : ι → ℕ) (hH : ∀ i, (H i).IsHomogeneous (e i)) (i : Option ι) :
    (bad H l i).IsHomogeneous (degrees e i) := by
  cases i with
  | none => exact (linear_homogeneous l).mul (square_det_homogeneous H l e hH)
  | some i => exact hH i

end Algebra
section Good
variable {K ι : Type*} [Field K] [Fintype ι]

def Good (H : ι → MvPolynomial (Option ι) K) (l : Option ι → K) : Prop :=
  ∀ y : Option ι → K, y ≠ 0 → (∀ i, eval y (H i) = 0) →
    eval y (linear l) ≠ 0 ∧ (square H l |>.map (eval y)).det ≠ 0

lemma good_iff_bad (H : ι → MvPolynomial (Option ι) K) (l : Option ι → K) :
    Good H l ↔ ∀ y : Option ι → K, (∀ i, eval y (bad H l i) = 0) → y = 0 := by
  classical
  constructor
  · intro hg y hy
    by_contra hn
    obtain ⟨hl,hj⟩ := hg y hn (fun i => hy (some i))
    have h := hy none
    change eval y (linear l * (square H l).det) = 0 at h
    rw [map_mul, RingHom.map_det] at h
    exact (mul_ne_zero hl hj) h
  · intro hz y hn hH
    have h : eval y (linear l * (square H l).det) ≠ 0 := by
      intro h
      exact hn (hz y (by intro i; cases i; exact h; exact hH _))
    rw [map_mul, RingHom.map_det] at h
    exact mul_ne_zero_iff.mp h

end Good
end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
variable {ι : Type*} [Fintype ι]

noncomputable def powers (e : ι → ℕ) : ι → MvPolynomial (Option ι) ℂ :=
  fun i => X (some i) ^ e i - X none ^ e i
noncomputable def coordinate : Option ι → ℂ := Pi.single none 1

omit [Fintype ι] in
lemma powers_homogeneous (e : ι → ℕ) (i : ι) : (powers e i).IsHomogeneous (e i) := by
  simpa [powers] using ((isHomogeneous_X ℂ (some i)).pow (e i)).sub
    ((isHomogeneous_X ℂ (none : Option ι)).pow (e i))

lemma eval_coordinate (y : Option ι → ℂ) : eval y (linear (coordinate (ι := ι))) = y none := by
  simp [linear, coordinate, Pi.single_apply]

lemma powers_good (e : ι → ℕ) (he : ∀ i, 0 < e i) : Good (powers e) coordinate := by
  intro y hy hH
  have hp (i : ι) : y (some i) ^ e i = y none ^ e i := by
    simpa [powers, sub_eq_zero] using hH i
  have hn : y none ≠ 0 := by
    intro hn
    apply hy
    funext i
    cases i with
    | none => exact hn
    | some i =>
      have hh : y (some i) ^ e i = 0 := by rw [hp i, hn, zero_pow (ne_of_gt (he i))]
      exact eq_zero_of_pow_eq_zero hh
  have hs (i : ι) : y (some i) ≠ 0 := by
    intro hz
    have hh := hp i
    rw [hz, zero_pow (ne_of_gt (he i))] at hh
    exact (pow_ne_zero _ hn) hh.symm
  refine ⟨by simpa only [eval_coordinate] using hn, ?_⟩
  let A := (square (powers e) (coordinate (ι := ι))).map (eval y)
  have h0 (v : Option ι → ℂ) : A.mulVec v none = v none := by
    simp [A, square, coordinate, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hd (i : ι) (j : Option ι) : eval y (pderiv j (powers e i)) =
      (if some i = j then (e i : ℂ) * y (some i) ^ (e i - 1) else 0) -
      (if none = j then (e i : ℂ) * y none ^ (e i - 1) else 0) := by
    by_cases ha : some i = j <;> by_cases hb : none = j <;>
      simp [powers, pderiv_X, ha, hb]
  have h1 (v : Option ι → ℂ) (i : ι) :
      A.mulVec v (some i) = (e i : ℂ) * y (some i) ^ (e i - 1) * v (some i) -
        (e i : ℂ) * y none ^ (e i - 1) * v none := by
    change (∑ j, eval y (pderiv j (powers e i)) * v j) = _
    simp only [hd, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hi : Function.Injective A.mulVec := by
    change Function.Injective A.mulVecLin
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    change A.mulVec v = 0 at hv
    have hv0 : v none = 0 := by simpa only [h0, Pi.zero_apply] using congrFun hv none
    funext j
    cases j with
    | none => exact hv0
    | some i =>
      have hh := congrFun hv (some i)
      rw [h1, hv0, mul_zero, sub_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left
        (mul_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt (he i))) (pow_ne_zero _ (hs i)))
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi))

def Roots (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ) :=
  {y : Option ι → ℂ // (∀ i, eval y (H i) = 0) ∧ eval y (linear l) = 1}

noncomputable def powersRootsEquiv (e : ι → ℕ) :
    Roots (powers e) coordinate ≃ (∀ i, {z : ℂ // z ^ e i = 1}) where
  toFun y i := ⟨y.val (some i), by
    have h0 : y.val none = 1 := by simpa only [eval_coordinate] using y.property.2
    simpa [powers, h0, sub_eq_zero] using y.property.1 i⟩
  invFun z := ⟨Option.elim' 1 (fun i => (z i).val), by
    constructor
    · intro i
      simp [powers, (z i).property]
    · simp only [eval_coordinate, Option.elim'_none]⟩
  left_inv y := by
    apply Subtype.ext
    funext j
    cases j with
    | none =>
      have h0 : y.val none = 1 := by simpa only [eval_coordinate] using y.property.2
      exact h0.symm
    | some i => rfl
  right_inv z := by funext i; rfl

lemma card_power_roots (n : ℕ) (hn : 0 < n) : Nat.card {z : ℂ // z^n=1} = n := by
  let : NeZero n := ⟨ne_of_gt hn⟩
  let e := (rootsOfUnityEquivNthRoots ℂ n).trans
    (Equiv.subtypeEquivRight (fun _ => Polynomial.mem_nthRoots hn))
  rw [← Nat.card_congr e]
  exact Complex.card_rootsOfUnity n

lemma powers_card (e : ι → ℕ) (he : ∀ i, 0 < e i) :
    Nat.card (Roots (powers e) coordinate) = ∏ i, e i := by
  rw [Nat.card_congr (powersRootsEquiv e), Nat.card_pi]
  exact Finset.prod_congr rfl (fun i _ => card_power_roots (e i) (he i))

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
section
variable {σ : Type*} [Fintype σ]

noncomputable def polynomialDerivative (p : MvPolynomial σ ℂ) (x : σ → ℂ) :
    (σ → ℂ) →L[ℂ] ℂ :=
  ∑ i, MvPolynomial.eval x (pderiv i p) • ContinuousLinearMap.proj i

@[simp] lemma polynomialDerivative_apply (p : MvPolynomial σ ℂ) (x v : σ → ℂ) :
    polynomialDerivative p x v = ∑ i, MvPolynomial.eval x (pderiv i p) * v i := by
  classical
  simp [polynomialDerivative]

lemma hasFDerivAt_eval (p : MvPolynomial σ ℂ) (x : σ → ℂ) :
    HasFDerivAt (fun y => MvPolynomial.eval y p) (polynomialDerivative p x) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have he : polynomialDerivative (C a) x = 0 := by ext v; simp
    rw [he]
    simpa only [eval_C] using (hasFDerivAt_const (𝕜 := ℂ) a x)
  | add p q hp hq =>
    have he : polynomialDerivative (p+q) x = polynomialDerivative p x + polynomialDerivative q x := by
      ext v
      simp [add_mul, Finset.sum_add_distrib]
    have hd := (hp.add hq).congr_fderiv he.symm
    convert! hd using 1
    ext y
    simp
  | mul_X p i hp =>
    have he : polynomialDerivative (p*X i) x =
        (eval x p) • ContinuousLinearMap.proj i + (x i) • polynomialDerivative p x := by
      ext v
      simp [polynomialDerivative, pderiv_X, Pi.single_apply,
        mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        mul_comm, mul_left_comm, apply_ite]
    have hd := hp.mul ((ContinuousLinearMap.proj i : (σ → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := x))
    have hd' := hd.congr_fderiv he.symm
    convert! hd' using 1
    ext y
    simp

lemma contDiff_eval (p : MvPolynomial σ ℂ) :
    ContDiff ℂ 1 (fun x : σ → ℂ => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℂ 1 (fun _ : σ → ℂ => a))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul, eval_X] using hp.mul (contDiff_apply ℂ ℂ i)

noncomputable def jacobian (P : σ → MvPolynomial σ ℂ) (x : σ → ℂ) : Matrix σ σ ℂ :=
  fun i j => eval x (pderiv j (P i))

lemma system_fderiv (P : σ → MvPolynomial σ ℂ) (x : σ → ℂ) :
    fderiv ℂ (fun y i => eval y (P i)) x =
      ContinuousLinearMap.pi (fun i => polynomialDerivative (P i) x) :=
  (hasFDerivAt_pi.mpr (fun i => hasFDerivAt_eval (P i) x)).fderiv

lemma system_fderiv_apply (P : σ → MvPolynomial σ ℂ) (x v : σ → ℂ) :
    fderiv ℂ (fun y i => eval y (P i)) x v = (jacobian P x).mulVec v := by
  rw [system_fderiv]
  ext i
  simp [jacobian, Matrix.mulVec, dotProduct]

lemma system_fderiv_invertible [DecidableEq σ] (P : σ → MvPolynomial σ ℂ) (x : σ → ℂ)
    (h : (jacobian P x).det ≠ 0) :
    (fderiv ℂ (fun y i => eval y (P i)) x).IsInvertible := by
  have hu : IsUnit (jacobian P x) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
  have he : ⇑(fderiv ℂ (fun y i => eval y (P i)) x) = (jacobian P x).mulVec :=
    funext (system_fderiv_apply P x)
  have hb : Function.Bijective (fderiv ℂ (fun y i => eval y (P i)) x) := by
    rw [he]
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu, Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩
  obtain ⟨u,hu⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr hb
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩
end
end PermanentBorder.CI

namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

theorem localHomeomorph_restrictPreimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (h : IsLocalHomeomorph f) (s : Set Y) :
    IsLocalHomeomorph (s.restrictPreimage f) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨U,hU,hE⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp h x.val
  let V : Set (f ⁻¹' s) := Subtype.val ⁻¹' U
  let e : V ≃ₜ ((U.domRestrict f) ⁻¹' s) :=
    { toFun := fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩
      invFun := fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨V, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
  exact (hE.restrictPreimage s).comp e.isOpenEmbedding

theorem zero_projection_chart {X F P : Type*} [TopologicalSpace X]
    [TopologicalSpace F] [TopologicalSpace P] [Zero F]
    (f : X → F) (p : X → P) (x : {x : X // f x = 0})
    (e : OpenPartialHomeomorph X (F × P)) (hx : x.val ∈ e.source)
    (he : ∀ z, e z = (f z,p z)) :
    ∃ U ∈ 𝓝 x, IsOpenEmbedding (U.domRestrict (fun z : {x : X // f x = 0} => p z)) := by
  let U : Set {x : X // f x = 0} := Subtype.val ⁻¹' e.source
  let A : Set (F × P) := {v | v.1 = 0}
  let h : U ≃ₜ ((e.source.domRestrict e) ⁻¹' A) :=
    { toFun := fun z => ⟨⟨z.val.val,z.property⟩,by simpa [A, he] using z.val.property⟩
      invFun := fun z => ⟨⟨z.val.val,by simpa [A, he] using z.property⟩,z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let g : A ≃ₜ P :=
    { toFun := fun v => v.val.2
      invFun := fun b => ⟨(0,b),rfl⟩
      left_inv := fun v => by apply Subtype.ext; exact Prod.ext v.property.symm rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨U, (e.open_source.preimage continuous_subtype_val).mem_nhds hx, ?_⟩
  have H := g.isOpenEmbedding.comp ((e.isOpenEmbedding_restrict.restrictPreimage A).comp
    h.isOpenEmbedding)
  convert H using 1
  funext z
  exact (congrArg Prod.snd (he z.val.val)).symm

theorem implicit_zero_projection {𝕜 P V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
    (f : P × V → V)
    (h : ∀ x : {x : P × V // f x = 0}, ∃ D : P × V →L[𝕜] V,
      HasStrictFDerivAt f D x.val ∧ (D ∘L ContinuousLinearMap.inr 𝕜 P V).IsInvertible) :
    IsLocalHomeomorph (fun x : {x : P × V // f x = 0} => x.val.1) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨D,hd,hi⟩ := h x
  let φ := hd.implicitFunctionDataOfProdDomain hi
  exact zero_projection_chart f Prod.fst x φ.toOpenPartialHomeomorph
    φ.pt_mem_toOpenPartialHomeomorph_source φ.toOpenPartialHomeomorph_apply

theorem covering_card_locallyConstant {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (h : IsCoveringMap f) :
    IsLocallyConstant (fun y => Nat.card (f ⁻¹' {y})) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro y
  obtain ⟨hd,U,hy,hU,hf,H,hH⟩ := h y
  filter_upwards [hU.mem_nhds hy] with z hz
  have he : IsEvenlyCovered f z (f ⁻¹' {y}) := ⟨hd,U,hz,hU,hf,H,hH⟩
  exact Nat.card_congr he.fiberHomeomorph.toEquiv.symm

theorem proper_localHomeomorph_card {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] [PreconnectedSpace Y] {f : X → Y}
    (hp : IsProperMap f) (hl : IsLocalHomeomorph f) (y z : Y) :
    Nat.card (f ⁻¹' {y}) = Nat.card (f ⁻¹' {z}) := by
  have hfin (a : Y) : (f ⁻¹' {a}).Finite := by
    let : CompactSpace (f ⁻¹' {a}) := isCompact_iff_compactSpace.mp
      (hp.isCompact_preimage isCompact_singleton)
    let : DiscreteTopology (f ⁻¹' {a}) :=
      (localHomeomorph_restrictPreimage hl {a}).comap_discreteTopology
    exact Set.finite_coe_iff.mp finite_of_compact_of_discrete
  have hcov : IsCoveringMap f := by
    apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
    exact hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
      (fun a _ => hfin a) hl.isLocalHomeomorphOn
  exact (covering_card_locallyConstant hcov).apply_eq_of_preconnectedSpace y z

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

theorem localHomeomorphOn_restrictPreimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (s : Set Y)
    (h : IsLocalHomeomorphOn f (f ⁻¹' s)) :
    IsLocalHomeomorph (s.restrictPreimage f) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨U,hU,hE⟩ := (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mp h x.val x.property
  let V : Set (f ⁻¹' s) := Subtype.val ⁻¹' U
  let e : V ≃ₜ ((U.domRestrict f) ⁻¹' s) :=
    { toFun := fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩
      invFun := fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨V, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
  exact (hE.restrictPreimage s).comp e.isOpenEmbedding

theorem implicit_zero_projection_on {𝕜 P V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
    (f : P × V → V) (s : Set P)
    (h : ∀ x : {x : P × V // f x = 0}, x.val.1 ∈ s → ∃ D : P × V →L[𝕜] V,
      HasStrictFDerivAt f D x.val ∧ (D ∘L ContinuousLinearMap.inr 𝕜 P V).IsInvertible) :
    IsLocalHomeomorph (s.restrictPreimage
      (fun x : {x : P × V // f x = 0} => x.val.1)) := by
  apply localHomeomorphOn_restrictPreimage
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mpr
  intro x hx
  obtain ⟨D,hd,hi⟩ := h x hx
  let φ := hd.implicitFunctionDataOfProdDomain hi
  exact zero_projection_chart f Prod.fst x φ.toOpenPartialHomeomorph
    φ.pt_mem_toOpenPartialHomeomorph_source φ.toOpenPartialHomeomorph_apply

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open Topology Set

theorem homogeneous_normalized_proper {T V : Type*} [TopologicalSpace T]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [ProperSpace V]
    (H : T → V → Prop) (hH : IsClosed {z : T × V | H z.1 z.2})
    (hsmul : ∀ t y (c : ℂ), H t y → H t (c • y))
    (L : T → V →ₗ[ℂ] ℂ) (hL : Continuous (fun z : T × V => L z.1 z.2))
    (hno : ∀ t y, H t y → L t y = 0 → y = 0) :
    IsProperMap (fun z : {z : T × V // H z.1 z.2 ∧ L z.1 z.2 = 1} => z.val.1) := by
  let S := Metric.sphere (0 : V) 1
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  let Q := {z : T × S // H z.1 z.2.val}
  let Z := {z : T × V // H z.1 z.2 ∧ L z.1 z.2 = 1}
  have hn (z : Q) : L z.val.1 z.val.2.val ≠ 0 := by
    intro h
    have he := hno _ _ z.property h
    have hh := z.val.2.property
    simp [S, he] at hh
  let q : Q → Z := fun z => ⟨(z.val.1,(L z.val.1 z.val.2.val)⁻¹ • z.val.2.val),
    hsmul _ _ _ z.property, by simp [map_smul, hn z]⟩
  have hq : Continuous q := by
    have hval : Continuous (fun z : Q => (z.val.1,z.val.2.val) : Q → T × V) := by fun_prop
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (((hL.comp hval).inv₀ hn).smul (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val)))
  have hsurj : Function.Surjective q := by
    intro z
    have hz : z.val.2 ≠ 0 := by
      intro he
      have hh := z.property.2
      simp [he] at hh
    have hc : (‖z.val.2‖ : ℂ) ≠ 0 := by simpa using (norm_ne_zero_iff.mpr hz)
    let y : S := ⟨(‖z.val.2‖ : ℂ)⁻¹ • z.val.2, by
      simp only [S, Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)⟩
    refine ⟨⟨(z.val.1,y), hsmul _ _ _ z.property.1⟩, ?_⟩
    apply Subtype.ext
    refine Prod.ext rfl ?_
    change (L z.val.1 ((‖z.val.2‖ : ℂ)⁻¹ • z.val.2))⁻¹ •
      ((‖z.val.2‖ : ℂ)⁻¹ • z.val.2) = z.val.2
    simp [map_smul, z.property.2, smul_smul, hc]
  have hclosed : IsClosed {z : T × S | H z.1 z.2.val} :=
    hH.preimage (show Continuous (fun z : T × S => (z.1,z.2.val)) by fun_prop)
  have hp : IsProperMap (fun z : Q => z.val.1) :=
    isProperMap_fst_of_compactSpace.comp hclosed.isProperMap_subtypeVal
  exact isProperMap_of_comp_of_surj hq (by fun_prop) hp hsurj

end PermanentBorder.Polar

end OAI
