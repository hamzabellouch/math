import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticImplicitScalar

namespace OAI

namespace Release061
open Set Filter Topology


theorem IsAffineAlgebraic.zeroLocus_vanishingIdeal
    {n : ℕ} {V : Set (Affine n)} (hV : IsAffineAlgebraic V) :
    MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ V) = V := by
  apply Set.Subset.antisymm _ (MvPolynomial.zeroLocus_vanishingIdeal_le V)
  obtain ⟨P, rfl⟩ := hV
  intro z hz p hp
  exact hz p (fun w hw => hw p hp)

theorem polynomial_normalization_surjective
    {n d : ℕ} {V : Set (Affine n)} (hV : IsAffineAlgebraic V)
    (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ]
      (MvPolynomial (Fin n) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ V))
    (hg : Function.Injective g) (hgi : g.IsIntegral)
    (P : Fin d → MvPolynomial (Fin n) ℂ)
    (hP : ∀ j, (Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ V)) (P j) =
      g (MvPolynomial.X j)) :
    Function.Surjective (fun z : V => fun j => MvPolynomial.eval z.val (P j)) := by
  classical
  let I := MvPolynomial.vanishingIdeal ℂ V
  let A := MvPolynomial (Fin d) ℂ
  let B := MvPolynomial (Fin n) ℂ ⧸ I
  let : Algebra A B := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral A B := ⟨hgi⟩
  intro y
  let m : Ideal A := MvPolynomial.vanishingIdeal ℂ {y}
  have hker : RingHom.ker (algebraMap A B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hg
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := B) m (by rw [hker]; exact bot_le)
  let := hQmax
  let J : Ideal (MvPolynomial (Fin n) ℂ) := Q.comap (Ideal.Quotient.mk I)
  have hJmax : J.IsMaximal := Ideal.comap_isMaximal_of_surjective _
    Ideal.Quotient.mk_surjective
  obtain ⟨z, hz⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hJmax
  have hzV : z ∈ V := by
    rw [← hV.zeroLocus_vanishingIdeal]
    intro p hp
    have hpJ : p ∈ J := by
      change Ideal.Quotient.mk I p ∈ Q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
      exact Q.zero_mem
    rw [hz] at hpJ
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff _ _).mp hpJ
  refine ⟨⟨z, hzV⟩, funext fun j => ?_⟩
  have hmem : g (MvPolynomial.X j - MvPolynomial.C (y j)) ∈ Q := by
    change MvPolynomial.X j - MvPolynomial.C (y j) ∈ Q.under A
    rw [hQ]
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff y _).mpr (by simp)
  have hmemJ : P j - MvPolynomial.C (y j) ∈ J := by
    change (Ideal.Quotient.mkₐ ℂ I) (P j - MvPolynomial.C (y j)) ∈ Q
    have hc : g (MvPolynomial.C (y j)) =
        (Ideal.Quotient.mkₐ ℂ I) (MvPolynomial.C (y j)) := by
      exact (g.commutes (y j)).trans ((Ideal.Quotient.mkₐ ℂ I).commutes (y j)).symm
    rw [map_sub]
    change (Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ V)) (P j) - _ ∈ Q
    rw [hP j, ← hc, ← map_sub]
    exact hmem
  rw [hz] at hmemJ
  have hh := (MvPolynomial.mem_vanishingIdeal_singleton_iff _ _).mp hmemJ
  change MvPolynomial.eval z (P j - MvPolynomial.C (y j)) = 0 at hh
  simpa only [map_sub, MvPolynomial.eval_C, sub_eq_zero] using hh

theorem IsAffineAlgebraic.exists_polynomial_normalization
    {n : ℕ} {V : Set (Affine n)} (hV : IsAffineAlgebraic V) (hne : V.Nonempty) :
    ∃ d ≤ n, ∃ P : Fin d → MvPolynomial (Fin n) ℂ,
      ∃ Q : Fin n → Polynomial (MvPolynomial (Fin d) ℂ),
        (∀ i, (Q i).Monic) ∧
        (∀ z ∈ V, ∀ i,
          Polynomial.eval₂ (MvPolynomial.eval (fun j => MvPolynomial.eval z (P j)))
            (z i) (Q i) = 0) ∧
        Function.Surjective (fun z : V => fun j => MvPolynomial.eval z.val (P j)) := by
  classical
  let I := MvPolynomial.vanishingIdeal ℂ V
  have hI : I ≠ ⊤ := by
    intro heq
    obtain ⟨z, hz⟩ := hne
    have hmem : (1 : MvPolynomial (Fin n) ℂ) ∈ I := by simp [heq]
    have := MvPolynomial.mem_vanishingIdeal_iff.mp hmem z hz
    simp at this
  obtain ⟨d, hd, g, hg, hgi⟩ := exists_integral_inj_algHom_of_quotient I hI
  choose P hP using fun j : Fin d =>
    Ideal.Quotient.mkₐ_surjective ℂ I (g (MvPolynomial.X j))
  choose Q hQ hroot using fun i : Fin n => hgi ((Ideal.Quotient.mkₐ ℂ I) (MvPolynomial.X i))
  refine ⟨d, hd, P, Q, hQ, ?_, polynomial_normalization_surjective hV g hg hgi P hP⟩
  intro z hz i
  let e : (MvPolynomial (Fin n) ℂ ⧸ I) →ₐ[ℂ] ℂ :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval z) (fun p hp =>
      MvPolynomial.mem_vanishingIdeal_iff.mp hp z hz)
  have he (p : MvPolynomial (Fin n) ℂ) : e ((Ideal.Quotient.mkₐ ℂ I) p) =
      MvPolynomial.eval z p := rfl
  have heg : e.comp g = MvPolynomial.aeval (fun j => MvPolynomial.eval z (P j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rw [← hP j, he]
  have hx := congrArg e.toRingHom (hroot i)
  rw [map_zero, Polynomial.hom_eval₂] at hx
  have hegr : e.toRingHom.comp g.toRingHom =
      MvPolynomial.eval (fun j => MvPolynomial.eval z (P j)) := by
    exact congrArg AlgHom.toRingHom heg
  rw [hegr] at hx
  change Polynomial.eval₂ _ (e ((Ideal.Quotient.mkₐ ℂ I) (MvPolynomial.X i))) (Q i) = 0 at hx
  simpa only [he, MvPolynomial.eval_X] using hx

theorem polynomial_analytic_root {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (a : Fin d → ℂ) (b : ℂ)
    (hroot : Polynomial.eval₂ (MvPolynomial.eval a) b P = 0)
    (hsimple : Polynomial.eval₂ (MvPolynomial.eval a) b P.derivative ≠ 0) :
    ∃ g : (Fin d → ℂ) → ℂ, AnalyticAt ℂ g a ∧ g a = b ∧
      (∀ᶠ y in 𝓝 a, Polynomial.eval₂ (MvPolynomial.eval y) (g y) P = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P = 0 →
        p.2 = g p.1) := by
  let F : ((Fin d → ℂ) × ℂ) → ℂ := fun p =>
    Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P
  have hF : AnalyticAt ℂ F (a, b) := by
    have hpoly : ∀ j : ℕ, AnalyticAt ℂ
        (fun p : ((Fin d → ℂ) × ℂ) => MvPolynomial.eval p.1 (P.coeff j)) (a, b) := by
      intro j
      exact (AnalyticOnNhd.eval_mvPolynomial (P.coeff j) _ (Set.mem_univ _)).comp
        ((ContinuousLinearMap.fst ℂ (Fin d → ℂ) ℂ).analyticAt _)
    simp only [F, Polynomial.eval₂_eq_sum_range]
    exact
      Finset.analyticAt_fun_sum (Finset.range (P.natDegree + 1)) (fun j _ =>
        (hpoly j).mul (((ContinuousLinearMap.snd ℂ (Fin d → ℂ) ℂ).analyticAt _).pow j))
  let L := fderiv ℂ F (a,b)
  have hL : HasFDerivAt F L (a,b) := hF.differentiableAt.hasFDerivAt
  have hv : L (0,1) = Polynomial.eval₂ (MvPolynomial.eval a) b P.derivative := by
    have h1 : HasDerivAt (fun z => F (a,z)) (L (0,1)) b :=
      hL.comp_hasDerivAt b ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))
    have h2 := (P.map (MvPolynomial.eval a)).hasDerivAt b
    simp only [Polynomial.derivative_map, Polynomial.eval_map] at h2
    exact h1.unique h2
  exact analytic_implicit_scalar hF hroot L hL (hv ▸ hsimple)

open Set Filter Metric MeasureTheory
open scoped Topology

theorem differentiableAt_intervalIntegral_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {x : E} {r a b : ℝ} (hr : 0 < r)
    (F : E → ℝ → ℂ) (F' : E → ℝ → E →L[ℂ] ℂ)
    (hc : ContinuousOn (Function.uncurry F) (closedBall x r ×ˢ uIcc a b))
    (hc' : ContinuousOn (Function.uncurry F') (closedBall x r ×ˢ uIcc a b))
    (hd : ∀ y ∈ closedBall x r, ∀ t ∈ uIcc a b, HasFDerivAt (F · t) (F' y t) y) :
    DifferentiableAt ℂ (fun y => ∫ t in a..b, F y t) x := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x r).prod isCompact_uIcc).exists_bound_of_continuousOn hc'
  have hsec : ∀ y ∈ closedBall x r, ContinuousOn (F y) (uIcc a b) := by
    intro y hy
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hy, ht⟩)
  have hsec' : ContinuousOn (F' x) (uIcc a b) :=
    hc'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨mem_closedBall_self hr.le, ht⟩)
  have hfint : IntervalIntegrable (F x) volume a b :=
    (hsec x (mem_closedBall_self hr.le)).intervalIntegrable
  have hfmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) (volume.restrict (uIoc a b)) := by
    filter_upwards [closedBall_mem_nhds x hr] with y hy
    exact (hsec y hy).intervalIntegrable.aestronglyMeasurable_restrict_uIoc
  have hbound : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc a b →
      ∀ y ∈ closedBall x r, ‖F' y t‖ ≤ C :=
    Filter.Eventually.of_forall fun t ht y hy => hC (y, t) ⟨hy, uIoc_subset_uIcc ht⟩
  have hdiff : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc a b →
      ∀ y ∈ closedBall x r, HasFDerivAt (F · t) (F' y t) y :=
    Filter.Eventually.of_forall fun t ht y hy => hd y hy t (uIoc_subset_uIcc ht)
  have hderiv : HasFDerivAt (fun y => ∫ t in a..b, F y t)
      (∫ t in a..b, F' x t) x :=
    intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (closedBall_mem_nhds x hr) hfmeas hfint
      hsec'.intervalIntegrable.aestronglyMeasurable_restrict_uIoc hbound
      (intervalIntegrable_const (c := C)) hdiff
  exact hderiv.differentiableAt

theorem differentiableAt_circleIntegral_of_analyticOnNhd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {x : E} {r R : ℝ} {c : ℂ} (hr : 0 < r) (hR : 0 ≤ R)
    (f : E × ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall x r ×ˢ sphere c R)) :
    DifferentiableAt ℂ (fun y => ∮ z in C(c, R), f (y, z)) x := by
  let ι : E →L[ℂ] E × ℂ := ContinuousLinearMap.inl ℂ E ℂ
  let F : E → ℝ → ℂ := fun y t => deriv (circleMap c R) t * f (y, circleMap c R t)
  let F' : E → ℝ → E →L[ℂ] ℂ := fun y t =>
    deriv (circleMap c R) t • (fderiv ℂ f (y, circleMap c R t)).comp ι
  have hcont : ContinuousOn f (closedBall x r ×ˢ sphere c R) := hf.continuousOn
  have hdercont : ContinuousOn (fderiv ℂ f) (closedBall x r ×ˢ sphere c R) := by
    intro p hp
    exact ((hf p hp).contDiffAt (n := 1)).continuousAt_fderiv (by decide) |>.continuousWithinAt
  have hparam : Continuous (fun p : E × ℝ => (p.1, circleMap c R p.2)) :=
    continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd)
  have hmap : MapsTo (fun p : E × ℝ => (p.1, circleMap c R p.2))
      (closedBall x r ×ˢ uIcc 0 (2 * Real.pi)) (closedBall x r ×ˢ sphere c R) :=
    fun p hp => ⟨hp.1, circleMap_mem_sphere c hR p.2⟩
  have hdc : Continuous (fun p : E × ℝ => deriv (circleMap c R) p.2) := by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
  have hc : ContinuousOn (Function.uncurry F) (closedBall x r ×ˢ uIcc 0 (2 * Real.pi)) :=
    hdc.continuousOn.mul (hcont.comp hparam.continuousOn hmap)
  have hc' : ContinuousOn (Function.uncurry F') (closedBall x r ×ˢ uIcc 0 (2 * Real.pi)) :=
    hdc.continuousOn.smul ((hdercont.comp hparam.continuousOn hmap).clm_comp continuousOn_const)
  have hd : ∀ y ∈ closedBall x r, ∀ t ∈ uIcc 0 (2 * Real.pi),
      HasFDerivAt (F · t) (F' y t) y := by
    intro y hy t _
    have hp := (hf (y, circleMap c R t) ⟨hy, circleMap_mem_sphere c hR t⟩).differentiableAt.hasFDerivAt
    have hi : HasFDerivAt (fun y : E => (y, circleMap c R t)) ι y :=
      (hasFDerivAt_id y).prodMk (hasFDerivAt_const _ _)
    exact (hp.comp y hi).const_mul _
  change DifferentiableAt ℂ (fun y => ∫ t in 0..2 * Real.pi, F y t) x
  exact differentiableAt_intervalIntegral_of_continuousOn hr F F' hc hc' hd

theorem differentiableOn_cauchyTransform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {A : Set E} (hA : IsOpen A) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (f : E × ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (A ×ˢ sphere c R)) :
    DifferentiableOn ℂ (fun p : E × ℂ =>
      (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(c, R), (w - p.2)⁻¹ * f (p.1, w))
      (A ×ˢ ball c R) := by
  intro p hp
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hA.prod isOpen_ball).mem_nhds hp)
  let F : (E × ℂ) × ℂ → ℂ := fun q => (q.2 - q.1.2)⁻¹ * f (q.1.1, q.2)
  have hF : AnalyticOnNhd ℂ F (closedBall p r ×ˢ sphere c R) := by
    intro q hq
    have hqq := hsub hq.1
    have hne : q.2 - q.1.2 ≠ 0 := sub_ne_zero.mpr
      (Metric.sphere_disjoint_ball.ne_of_mem hq.2 hqq.2)
    let π₁ : (E × ℂ) × ℂ →L[ℂ] E :=
      (ContinuousLinearMap.fst ℂ E ℂ).comp (ContinuousLinearMap.fst ℂ (E × ℂ) ℂ)
    let π₂ : (E × ℂ) × ℂ →L[ℂ] ℂ :=
      (ContinuousLinearMap.snd ℂ E ℂ).comp (ContinuousLinearMap.fst ℂ (E × ℂ) ℂ)
    let π₃ : (E × ℂ) × ℂ →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ (E × ℂ) ℂ
    have ha : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ => q.2 - q.1.2) q :=
      (π₃.analyticAt q).sub (π₂.analyticAt q)
    have hb : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ => f (q.1.1, q.2)) q :=
      (hf (q.1.1, q.2) ⟨hqq.1, hq.2⟩).comp (f := (π₁.prod π₃))
        ((π₁.prod π₃).analyticAt q)
    exact (ha.inv hne).mul hb
  exact ((differentiableAt_circleIntegral_of_analyticOnNhd hr hR.le F hF).const_mul
    (2 * Real.pi * Complex.I)⁻¹).differentiableWithinAt

end Release061

end OAI
