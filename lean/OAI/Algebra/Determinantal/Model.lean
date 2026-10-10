import OAI.Algebra.Determinantal.RankTransfer

namespace OAI

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma isInvertible_of_injective (D : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hD : Function.Injective D) : D.IsInvertible := by
  have hs : Function.Surjective D := (LinearMap.injective_iff_surjective).mp hD
  let e := LinearEquiv.ofBijective D.toLinearMap ⟨hD,hs⟩
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

lemma normalizer_simple_restrict
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ))
    (F : (Option ι → ℂ) → (Option ι → ℂ))
    (hfirst : ∀ y, F y none = e y none - 1) (z : ι → ℂ)
    (hF : DifferentiableAt ℂ F (affineNormChart e z))
    (hs : (fderiv ℂ F (affineNormChart e z)).IsInvertible) :
    (fderiv ℂ (fun z i => F (affineNormChart e z) (some i)) z).IsInvertible := by
  let D := (fderiv ℂ F (affineNormChart e z)).comp
    (e.symm.toContinuousLinearMap.comp optionInsert)
  have hfull : HasFDerivAt (fun z => F (affineNormChart e z)) D z :=
    hF.hasFDerivAt.comp z (affineNormChart_hasFDerivAt e z)
  let E : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
    ContinuousLinearMap.pi (fun i => (ContinuousLinearMap.proj (some i)).comp D)
  have hred : HasFDerivAt (fun z i => F (affineNormChart e z) (some i)) E z :=
    hasFDerivAt_pi.mpr (fun i => (ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp z hfull)
  have hzero : (fun z => F (affineNormChart e z) none) = fun _ => (0 : ℂ) := by
    funext z
    rw [hfirst, affineNormChart, e.apply_symm_apply]
    simp
  have hnone : (ContinuousLinearMap.proj none).comp D = 0 := by
    have hd := (ContinuousLinearMap.proj none : (Option ι → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp z hfull
    change HasFDerivAt (fun z => F (affineNormChart e z) none) _ z at hd
    rw [hzero] at hd
    exact hd.unique (hasFDerivAt_const _ _)
  rw [hred.fderiv]
  apply isInvertible_of_injective
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hd : D v = 0 := by
    funext i
    cases i with
    | none => exact congrArg (fun T : (ι → ℂ) →L[ℂ] ℂ => T v) hnone
    | some i => exact congrFun hv i
  have he : e.symm (optionInsert v) = 0 := hs.injective (hd.trans (map_zero _).symm)
  have hi : optionInsert v = 0 := e.symm.injective (he.trans (map_zero _).symm)
  exact funext (fun i => congrFun hi (some i))

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

theorem smooth_polar_affine_certificate (f : MvPolynomial (PolarVars τ) ℂ)
    {r : ℕ} (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → ℂ,
    ∃ e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ),
    ∃ x : Fin (r * (r-1)^Fintype.card τ) → Option τ → ℂ,
      Function.Injective x ∧
      ∀ i, (fun j => eval (affineNormChart e (x i)) (hypersurfacePolars w f j)) = 0 ∧
        (fderiv ℂ (fun z j => eval (affineNormChart e z)
          (hypersurfacePolars w f j)) (x i)).IsInvertible := by
  classical
  obtain ⟨w,l,hg,hcard⟩ := smooth_polar_count f hr hh hs
  let R := CI.Roots (hypersurfacePolars w f) l
  have hpos : 0 < Nat.card R := by
    rw [show Nat.card R = _ from hcard]
    exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have : Finite R := (Nat.card_pos_iff.mp hpos).2
  let : Fintype R := Fintype.ofFinite R
  have hcard' : Fintype.card R = r * (r-1)^Fintype.card τ := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  let q : Fin (r * (r-1)^Fintype.card τ) ≃ R := (Fintype.equivFinOfCardEq hcard').symm
  have hl : l ≠ 0 := by
    intro hz
    obtain ⟨y⟩ := (Nat.card_pos_iff.mp hpos).1
    have hy := y.property.2
    simp [CI.eval_linear, hz] at hy
  obtain ⟨e,he⟩ := exists_normalizer_equiv l hl
  have hy (i : Fin (r * (r-1)^Fintype.card τ)) : e (q i).val none = 1 := by
    rw [he, ← CI.eval_linear]
    exact (q i).property.2
  choose x hx using fun i => exists_chart_preimage e (hy i)
  refine ⟨w,e,x,?_,?_⟩
  · intro i j hij
    apply q.injective
    apply Subtype.ext
    rw [← hx i, ← hx j, hij]
  · intro i
    have hz : (fun j => eval (q i).val (CI.normalized (hypersurfacePolars w f) l j)) = 0 :=
      (CI.normalized_eval_zero_iff _ _ _).mpr (q i).property
    constructor
    · rw [hx i]
      exact funext (q i).property.1
    · have hfirst (y : PolarVars τ → ℂ) :
          eval y (CI.normalized (hypersurfacePolars w f) l none) = e y none - 1 := by
        change eval y (CI.linear l - 1) = _
        rw [map_sub, map_one, CI.eval_linear, he]
      apply normalizer_simple_restrict e
        (fun y j => eval y (CI.normalized (hypersurfacePolars w f) l j)) hfirst (x i)
      · exact ((contDiff_pi.mpr (fun j => CI.contDiff_eval
          (CI.normalized (hypersurfacePolars w f) l j))).differentiable (by decide)) _
      · rw [hx i]
        exact CI.good_derivative_invertible _ _ _ hg hz

end PermanentBorder.Polar

namespace PermanentBorder

open Filter
open scoped Topology

abbrev Variables (m : ℕ) := Fin m × Fin m
abbrev Poly (σ : Type*) := MvPolynomial σ ℂ

noncomputable def permanentPolynomial (m : ℕ) : Poly (Variables m) :=
  ∑ τ : Equiv.Perm (Fin m), ∏ i : Fin m, MvPolynomial.X (i, τ i)

noncomputable def affineMatrixPolynomial {σ : Type*} [Fintype σ] (n : ℕ)
    (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : σ → Matrix (Fin n) (Fin n) ℂ) : Poly σ :=
  Matrix.det (fun i j => MvPolynomial.C (A₀ i j) +
    ∑ v : σ, MvPolynomial.C (A v i j) * MvPolynomial.X v)

def HasBorderDeterminant {σ : Type*} [Fintype σ] (n : ℕ) (p : Poly σ) : Prop :=
  0 < n ∧ ∃ (A₀ : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (A : ℕ → σ → Matrix (Fin n) (Fin n) ℂ),
    ∀ d : σ →₀ ℕ, Tendsto
      (fun j => (affineMatrixPolynomial n (A₀ j) (A j)).coeff d)
      atTop (𝓝 (p.coeff d))

def HasExactDeterminant {σ : Type*} [Fintype σ] (n : ℕ) (p : Poly σ) : Prop :=
  0 < n ∧ ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : σ → Matrix (Fin n) (Fin n) ℂ), affineMatrixPolynomial n A₀ A = p

theorem HasExactDeterminant.hasBorderDeterminant {σ : Type*} [Fintype σ]
    {n : ℕ} {p : Poly σ} (h : HasExactDeterminant n p) :
    HasBorderDeterminant n p := by
  rcases h with ⟨hn, A₀, A, hp⟩
  refine ⟨hn, (fun _ => A₀), (fun _ => A), ?_⟩
  intro d
  simpa only [hp] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => p.coeff d) atTop (𝓝 (p.coeff d)))

end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section FixedCoefficientSpace
variable {σ τ : Type*} [Fintype σ]

noncomputable def exponentCube (n : ℕ) : Finset (σ →₀ ℕ) :=
  by
    classical
    exact Finset.Iic (Finsupp.equivFunOnFinite.symm (fun _ : σ => n))

@[simp] theorem mem_exponentCube (n : ℕ) (d : σ →₀ ℕ) :
    d ∈ exponentCube (σ := σ) n ↔ ∀ i, d i ≤ n := by
  classical
  simp only [exponentCube, Finset.mem_Iic, Finsupp.le_def]
  rfl

theorem support_subset_exponentCube {P : Poly σ} {n : ℕ} (hP : P.totalDegree ≤ n) :
    P.support ⊆ exponentCube n := by
  intro d hd
  rw [mem_exponentCube]
  intro i
  exact (monomial_le_degreeOf i hd).trans ((degreeOf_le_totalDegree P i).trans hP)

theorem sum_over_exponentCube {P : Poly σ} {n : ℕ}
    (hP : P.support ⊆ exponentCube n) :
    P = ∑ d ∈ exponentCube n, monomial d (P.coeff d) := by
  calc
    P = ∑ d ∈ P.support, monomial d (P.coeff d) := MvPolynomial.as_sum P
    _ = _ := ?_
  apply Finset.sum_subset hP
  intro d _ hd
  simp only [notMem_support_iff.mp hd, map_zero]

theorem coeff_linear_map_cube (F : Poly σ →ₗ[ℂ] Poly τ) {P : Poly σ} {n : ℕ}
    (hP : P.support ⊆ exponentCube n) (e : τ →₀ ℕ) :
    (F P).coeff e = ∑ d ∈ exponentCube n,
      P.coeff d * (F (monomial d 1)).coeff e := by
  conv_lhs => rw [sum_over_exponentCube hP]
  simp only [map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [show monomial d (P.coeff d) = P.coeff d • monomial d (1 : ℂ) by simp [smul_monomial],
    map_smul, coeff_smul, smul_eq_mul]

theorem support_subset_cube_of_limit {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    p.support ⊆ exponentCube n := by
  classical
  intro d hd
  by_contra hn
  have hz : ∀ j, (P j).coeff d = 0 := by
    intro j
    apply notMem_support_iff.mp
    exact fun hj => hn (hP j hj)
  have ht : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (p.coeff d)) := by
    simpa only [hz] using hp d
  have he : p.coeff d = 0 := (tendsto_nhds_unique tendsto_const_nhds ht).symm
  exact mem_support_iff.mp hd he

theorem coefficientwise_linear_map_limit (F : Poly σ →ₗ[ℂ] Poly τ)
    {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    ∀ e, Tendsto (fun j => (F (P j)).coeff e) atTop (𝓝 ((F p).coeff e)) := by
  intro e
  have hc := support_subset_cube_of_limit hP hp
  have ht := tendsto_finsetSum (exponentCube (σ := σ) n)
    (fun d _ => (hp d).mul (tendsto_const_nhds (x := (F (monomial d 1)).coeff e)))
  convert ht using 1
  · funext j
    exact coeff_linear_map_cube F (hP j) e
  · congr 1
    exact coeff_linear_map_cube F hc e
end FixedCoefficientSpace

section DeterminantDegree
variable {σ : Type*} [Fintype σ]

theorem degree_affine_form (b : ℂ) (a : σ → ℂ) :
    (C b + ∑ v : σ, C (a v) * X v : Poly σ).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply totalDegree_finsetSum_le
    intro v _
    exact (totalDegree_mul _ _).trans (by simp)

theorem degree_affineMatrixPolynomial (n : ℕ)
    (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    (affineMatrixPolynomial n A₀ A).totalDegree ≤ n := by
  classical
  unfold affineMatrixPolynomial
  have he := Matrix.det_apply (show Matrix (Fin n) (Fin n) (Poly σ) from
    fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v)
  rw [he]
  apply totalDegree_finsetSum_le
  intro s _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum fun i _ => degree_affine_form _ _
    _ = n := by simp
end DeterminantDegree

section AffineSubstitution
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def affineSubstitution (b : σ → ℂ) (B : σ → τ → ℂ) :
    Poly σ →ₐ[ℂ] Poly τ :=
  MvPolynomial.aeval (fun v => C (b v) + ∑ w : τ, C (B v w) * X w)

theorem affineSubstitution_matrix (b : σ → ℂ) (B : σ → τ → ℂ)
    (n : ℕ) (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    affineSubstitution b B (affineMatrixPolynomial n A₀ A) =
      affineMatrixPolynomial n
        (fun i j => A₀ i j + ∑ v : σ, A v i j * b v)
        (fun w i j => ∑ v : σ, A v i j * B v w) := by
  classical
  unfold affineMatrixPolynomial
  have he := RingHom.map_det (affineSubstitution b B).toRingHom
    (show Matrix (Fin n) (Fin n) (Poly σ) from
      fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v)
  refine he.trans ?_
  apply congrArg Matrix.det
  funext i j
  change (affineSubstitution b B) (C (A₀ i j) + ∑ v, C (A v i j) * X v) =
    C (A₀ i j + ∑ v, A v i j * b v) + ∑ w, C (∑ v, A v i j * B v w) * X w
  simp only [affineSubstitution, map_add, map_sum, map_mul,
    aeval_C, aeval_X, algebraMap_eq]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, ← map_mul]
  rw [← add_assoc]
  congr 1
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, map_mul, mul_assoc]

theorem HasBorderDeterminant.affineSubstitution {n : ℕ} {p : Poly σ}
    (h : HasBorderDeterminant n p) (b : σ → ℂ) (B : σ → τ → ℂ) :
    HasBorderDeterminant n (affineSubstitution b B p) := by
  classical
  obtain ⟨hn, A₀, A, hlim⟩ := h
  refine ⟨hn,
    (fun l i j => A₀ l i j + ∑ v : σ, A l v i j * b v),
    (fun l w i j => ∑ v : σ, A l v i j * B v w), ?_⟩
  have hf := coefficientwise_linear_map_limit (PermanentBorder.affineSubstitution b B).toLinearMap
    (fun l => support_subset_exponentCube (degree_affineMatrixPolynomial n (A₀ l) (A l))) hlim
  intro e
  simpa only [AlgHom.toLinearMap_apply, affineSubstitution_matrix] using hf e
end AffineSubstitution
end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section ScalarNormalization
variable {σ : Type*} [Fintype σ]

theorem affineMatrixPolynomial_scaleRow (n : ℕ) (i₀ : Fin n) (a : ℂ)
    (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    affineMatrixPolynomial n (A₀.updateRow i₀ (a • A₀ i₀))
      (fun v => (A v).updateRow i₀ (a • A v i₀)) =
    a • affineMatrixPolynomial n A₀ A := by
  classical
  let M : Matrix (Fin n) (Fin n) (Poly σ) :=
    fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v
  let M' : Matrix (Fin n) (Fin n) (Poly σ) := fun i j =>
    C ((A₀.updateRow i₀ (a • A₀ i₀)) i j) +
      ∑ v, C (((A v).updateRow i₀ (a • A v i₀)) i j) * X v
  have hM : M' = M.updateRow i₀ ((C a : Poly σ) • M i₀) := by
    funext i j
    change C ((A₀.updateRow i₀ (a • A₀ i₀)) i j) + (∑ v,
      C (((A v).updateRow i₀ (a • A v i₀)) i j) * X v) = _
    by_cases hi : i = i₀
    · subst i
      rw [Matrix.updateRow_self, Matrix.updateRow_self]
      simp only [Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul, map_mul]
      change _ = C a * (C (A₀ i₀ j) + ∑ v, C (A v i₀ j) * X v)
      simp only [mul_add, Finset.mul_sum, mul_assoc]
    · rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi]
      simp only [Matrix.updateRow_ne hi]
      rfl
  change M'.det = a • M.det
  rw [hM]
  rw [Matrix.det_updateRow_smul]
  rw [Matrix.updateRow_eq_self]
  exact (MvPolynomial.smul_eq_C_mul M.det a).symm

theorem HasBorderDeterminant.smul {n : ℕ} {p : Poly σ}
    (h : HasBorderDeterminant n p) (a : ℂ) : HasBorderDeterminant n (a • p) := by
  classical
  obtain ⟨hn, A₀, A, hlim⟩ := h
  let i₀ : Fin n := ⟨0, hn⟩
  refine ⟨hn, (fun l => (A₀ l).updateRow i₀ (a • A₀ l i₀)),
    (fun l v => (A l v).updateRow i₀ (a • A l v i₀)), ?_⟩
  intro e
  simp only [affineMatrixPolynomial_scaleRow, coeff_smul, smul_eq_mul]
  exact tendsto_const_nhds.mul (hlim e)

theorem HasBorderDeterminant.affineSubstitution_smul
    {τ : Type*} [Fintype τ] {n : ℕ} {p : Poly σ}
    (h : HasBorderDeterminant n p) (b : σ → ℂ) (B : σ → τ → ℂ) (a : ℂ) :
    HasBorderDeterminant n (a • PermanentBorder.affineSubstitution b B p) :=
  (h.affineSubstitution b B).smul a
end ScalarNormalization
end PermanentBorder

end OAI
