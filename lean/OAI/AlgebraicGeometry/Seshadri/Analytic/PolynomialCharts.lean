import Mathlib

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
open scoped BigOperators
variable {𝕜 ι E : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def polynomialDifferential (L : ι → E →L[𝕜] 𝕜) (p : MvPolynomial ι 𝕜) (x : E) :
    E →L[𝕜] 𝕜 := ∑ i, eval (fun i => L i x) (pderiv i p) • L i

lemma polynomialDifferential_C (L : ι → E →L[𝕜] 𝕜) (c : 𝕜) (x : E) :
    polynomialDifferential L (C c) x = 0 := by
  ext v
  simp [polynomialDifferential]

lemma polynomialDifferential_add (L : ι → E →L[𝕜] 𝕜) (p q : MvPolynomial ι 𝕜) (x : E) :
    polynomialDifferential L (p + q) x =
      polynomialDifferential L p x + polynomialDifferential L q x := by
  ext v
  simp [polynomialDifferential, add_mul, Finset.sum_add_distrib]

lemma polynomialDifferential_mul (L : ι → E →L[𝕜] 𝕜) (p q : MvPolynomial ι 𝕜) (x : E) :
    polynomialDifferential L (p * q) x =
      eval (fun i => L i x) p • polynomialDifferential L q x +
        eval (fun i => L i x) q • polynomialDifferential L p x := by
  ext v
  simp [polynomialDifferential, Derivation.leibniz, smul_eq_mul, add_mul, mul_assoc,
    Finset.sum_add_distrib, Finset.mul_sum]

lemma polynomialDifferential_X (L : ι → E →L[𝕜] 𝕜) (i : ι) (x : E) :
    polynomialDifferential L (X i) x = L i := by
  classical
  ext v
  simp [polynomialDifferential, pderiv_X, Pi.single_apply, apply_ite, ite_apply]

theorem hasFDerivAt_polynomialEval (L : ι → E →L[𝕜] 𝕜) (p : MvPolynomial ι 𝕜) (x : E) :
    HasFDerivAt (fun y => eval (fun i => L i y) p) (polynomialDifferential L p x) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa [polynomialDifferential_C] using hasFDerivAt_const (𝕜 := 𝕜) c x
  | add p q hp hq =>
      simpa [polynomialDifferential_add, Pi.add_def] using hp.add hq
  | mul_X p i hp =>
      simpa [polynomialDifferential_mul, polynomialDifferential_X, Pi.mul_def] using
        hp.mul ((L i).hasFDerivAt (x := x))

theorem analyticAt_polynomial_eval (p : MvPolynomial ι 𝕜) (x : ι → 𝕜) :
    AnalyticAt 𝕜 (fun y => eval y p) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using analyticAt_const (𝕜 := 𝕜) (E := ι → 𝕜) (v := c) (x := x)
  | add p q hp hq => simpa [Pi.add_def] using hp.add hq
  | mul_X p i hp =>
      simpa [Pi.mul_def] using hp.mul ((ContinuousLinearMap.proj (R := 𝕜) i).analyticAt x)

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators Matrix
variable {F ι σ : Type*} [Field F] [Fintype ι] [Fintype σ] [DecidableEq ι] [DecidableEq σ]

def augmentedLinear (j : σ → ι) (J : Matrix σ ι F) :
    (ι → F) →ₗ[F] ((σ → F) × ({i : ι // i ∉ Set.range j} → F)) :=
  (Matrix.toLin' J).prod (LinearMap.pi fun i => LinearMap.proj i.val)

omit [Fintype σ] [DecidableEq σ] in
lemma augmentedLinear_apply (j : σ → ι) (J : Matrix σ ι F) (v : ι → F) :
    augmentedLinear j J v = (J.mulVec v, fun i => v i.val) := rfl

theorem augmentedLinear_bijective (j : σ → ι) (hj : Function.Injective j)
    (J : Matrix σ ι F) (hJ : IsUnit (J.submatrix id j).det) :
    Function.Bijective (augmentedLinear j J) := by
  classical
  have hinj : Function.Injective (augmentedLinear j J) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hfree (i : ι) (hi : i ∉ Set.range j) : v i = 0 := by
      exact congrFun (congrArg Prod.snd hv) ⟨i, hi⟩
    have hsel : (J.submatrix id j).mulVec (v ∘ j) = 0 := by
      ext i
      calc
        _ = (J.mulVec v) i := Fintype.sum_of_injective j hj
          (fun k => J i (j k) * v (j k)) (fun k => J i k * v k)
          (fun k hk => by rw [hfree k hk, mul_zero]) (fun _ => rfl)
        _ = 0 := congrFun (congrArg Prod.fst hv) i
    have hm : v ∘ j = 0 := by
      apply (Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr hJ))
      simpa using hsel
    ext i
    by_cases hi : i ∈ Set.range j
    · obtain ⟨k, rfl⟩ := hi
      exact congrFun hm k
    · exact hfree i hi
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  rw [Module.finrank_pi, Module.finrank_prod, Module.finrank_pi, Module.finrank_pi]
  have hc := Fintype.card_congr (Equiv.ofInjective j hj)
  have hd := Fintype.card_congr (Equiv.Set.sumCompl (Set.range j))
  rw [Fintype.card_sum] at hd
  have he : Fintype.card {i : ι // i ∉ Set.range j} =
      Fintype.card ↥(Set.range j)ᶜ := Fintype.card_congr (Equiv.refl _)
  omega

variable {S : Type*} [CommRing S] [Algebra F S]

omit [Fintype ι] [DecidableEq ι] in
                                                                               
theorem submersive_jacobian_at_point
    (P : Algebra.SubmersivePresentation F S ι σ) (ρ : S →ₐ[F] F) :
    IsUnit (Matrix.det (Matrix.of fun i k : σ => MvPolynomial.eval (fun a => ρ (P.val a))
      (MvPolynomial.pderiv (P.map k) (P.relation i)))) := by
  classical
  have h := P.jacobian_isUnit.map ρ.toRingHom
  rw [P.jacobian_eq_jacobiMatrix_det] at h
  have he (f : MvPolynomial ι F) :
      ρ (MvPolynomial.aeval P.val f) =
        MvPolynomial.eval (fun a => ρ (P.val a)) f := by
    change (ρ.comp (MvPolynomial.aeval P.val)) f = _
    rw [MvPolynomial.comp_aeval]
    rfl
  rw [P.algebraMap_apply] at h
  change IsUnit (ρ (MvPolynomial.aeval P.val P.jacobiMatrix.det)) at h
  rw [he, RingHom.map_det] at h
  have heq : (MvPolynomial.eval (fun a => ρ (P.val a))).mapMatrix P.jacobiMatrix =
      (Matrix.of fun i k : σ => MvPolynomial.eval (fun a => ρ (P.val a))
        (MvPolynomial.pderiv (P.map k) (P.relation i)))ᵀ := by
    ext i k
    simp [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, Matrix.transpose_apply]
  rw [heq, Matrix.det_transpose] at h
  exact h

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators Matrix ContDiff
open MvPolynomial
variable {F ι σ S : Type*} [RCLike F] [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra F S]

def augmentedPolynomial (P : Algebra.SubmersivePresentation F S ι σ) (x : ι → F) :
    (σ → F) × ({i : ι // i ∉ Set.range P.map} → F) :=
  ((fun a => eval x (P.relation a)), fun i => x i.val)

def augmentedDerivative (P : Algebra.SubmersivePresentation F S ι σ) (x : ι → F) :
    (ι → F) →L[F] ((σ → F) × ({i : ι // i ∉ Set.range P.map} → F)) :=
  (augmentedLinear P.map (Matrix.of fun i a => eval x (pderiv a (P.relation i)))).toContinuousLinearMap

omit [DecidableEq σ] in
lemma augmentedPolynomial_hasFDerivAt (P : Algebra.SubmersivePresentation F S ι σ)
    (x : ι → F) : HasFDerivAt (augmentedPolynomial P) (augmentedDerivative P x) x := by
  have h₁ := (hasFDerivAt_pi.mpr fun i : σ =>
    hasFDerivAt_polynomialEval (fun a : ι => ContinuousLinearMap.proj (R := F) a)
      (P.relation i) x)
  have h₂ : HasFDerivAt (fun y : ι → F => fun i : {i : ι // i ∉ Set.range P.map} => y i.val)
      (ContinuousLinearMap.pi fun i : {i : ι // i ∉ Set.range P.map} =>
        ContinuousLinearMap.proj (R := F) i.val) x :=
    hasFDerivAt_pi.mpr fun i => (ContinuousLinearMap.proj (R := F) i.val).hasFDerivAt (x := x)
  apply (h₁.prodMk h₂).congr_fderiv
  ext v
  all_goals simp [augmentedDerivative, augmentedLinear, polynomialDifferential,
    Matrix.mulVec, dotProduct]

omit [DecidableEq σ] in
lemma augmentedPolynomial_analyticAt (P : Algebra.SubmersivePresentation F S ι σ)
    (x : ι → F) : AnalyticAt F (augmentedPolynomial P) x := by
  exact (AnalyticAt.pi fun i => analyticAt_polynomial_eval (P.relation i) x).prod
    (AnalyticAt.pi fun i => (ContinuousLinearMap.proj (R := F) i.val).analyticAt x)

def augmentedDerivativeEquiv (P : Algebra.SubmersivePresentation F S ι σ)
    (ρ : S →ₐ[F] F) :
    (ι → F) ≃L[F] ((σ → F) × ({i : ι // i ∉ Set.range P.map} → F)) :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective
    (augmentedLinear P.map (Matrix.of fun i a => eval (fun a => ρ (P.val a))
      (pderiv a (P.relation i))))
    (augmentedLinear_bijective P.map P.map_inj _ (submersive_jacobian_at_point P ρ)))

theorem exists_analytic_augmented_inverse
    (P : Algebra.SubmersivePresentation F S ι σ) (ρ : S →ₐ[F] F) :
    ∃ ψ : ((σ → F) × ({i : ι // i ∉ Set.range P.map} → F)) → (ι → F),
      ψ (augmentedPolynomial P (fun a => ρ (P.val a))) = (fun a => ρ (P.val a)) ∧
      AnalyticAt F ψ (augmentedPolynomial P (fun a => ρ (P.val a))) ∧
      ∀ᶠ y in nhds (augmentedPolynomial P (fun a => ρ (P.val a))),
        augmentedPolynomial P (ψ y) = y := by
  let x : ι → F := fun a => ρ (P.val a)
  let f := augmentedPolynomial P
  let e' := augmentedDerivativeEquiv P ρ
  have hd : HasFDerivAt f (e' : (ι → F) →L[F] _) x := by
    convert! augmentedPolynomial_hasFDerivAt P x using 1
  have hc : ContDiffAt F ω f x := (augmentedPolynomial_analyticAt P x).contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let e := hc.toOpenPartialHomeomorph f hd hn
  let ψ := hc.localInverse hd hn
  refine ⟨ψ, hc.localInverse_apply_image hd hn, (hc.to_localInverse hd hn).analyticAt, ?_⟩
  have hm : f x ∈ e.target := hc.image_mem_toOpenPartialHomeomorph_target hd hn
  filter_upwards [e.open_target.mem_nhds hm] with y hy
  exact e.right_inv hy

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
