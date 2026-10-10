import OAI.GroupTheory.Kervaire.MixingOperators

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology

namespace KervaireHaarFlow

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

omit [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S] [NormedSpace ℝ E] in
lemma hasCompactSupport_of_compact (f : S → E) : HasCompactSupport f :=
  (isClosed_closure : IsClosed (tsupport f)).isCompact

omit [SecondCountableTopology S] [NormedSpace ℝ E] in
lemma continuous_integrable {f : S → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (hasCompactSupport_of_compact f)

/-- Compactness supplies the domination needed for differentiation with respect to a real
parameter. This lemma only assumes actual joint continuity and actual pointwise derivatives. -/
lemma hasDerivAt_integral_compact {f df : ℝ → S → E}
    (hf : Continuous (Function.uncurry f)) (hd : Continuous (Function.uncurry df))
    (hfd : ∀ t x, HasDerivAt (fun u ↦ f u x) (df t x) t) (t : ℝ) :
    HasDerivAt (fun u ↦ ∫ x, f u x ∂μ) (∫ x, df t x ∂μ) t := by
  have htc : IsCompact (Icc (t-1) (t+1) ×ˢ (univ : Set S)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := (htc.image hd).isBounded.exists_norm_le
  have hmeas (u : ℝ) : AEStronglyMeasurable (f u) μ :=
    (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (df t) μ :=
    (hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Icc (t-1) (t+1)) (bound := fun _ ↦ C)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall hmeas)
    (continuous_integrable (hf.comp (continuous_const.prodMk continuous_id))) hDmeas
    (Eventually.of_forall fun x u hu ↦ hC _ ⟨(u,x), ⟨hu, mem_univ _⟩, rfl⟩)
    (integrable_const C)
    (Eventually.of_forall fun x u _ ↦ hfd u x)).2

/-- The infinitesimal form of invariance under a measure-preserving flow. -/
lemma integral_deriv_eq_zero_of_invariant {f df : ℝ → S → E}
    (hf : Continuous (Function.uncurry f)) (hd : Continuous (Function.uncurry df))
    (hfd : ∀ t x, HasDerivAt (fun u ↦ f u x) (df t x) t)
    (hinv : ∀ t, (∫ x, f t x ∂μ) = ∫ x, f 0 x ∂μ) (t : ℝ) :
    (∫ x, df t x ∂μ) = 0 := by
  have hfun : (fun u ↦ ∫ x, f u x ∂μ) = fun _ : ℝ ↦ ∫ x, f 0 x ∂μ := funext hinv
  have h := hasDerivAt_integral_compact (μ := μ) hf hd hfd t
  rw [hfun] at h
  exact h.unique (hasDerivAt_const t _)

end KervaireHaarFlow

open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff

namespace KervaireClosedCurrent

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smoothness of simultaneous evaluation, including a varying multilinear map. -/
lemma contDiff_multilinear_eval {n : ℕ}
    {f : E → ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F}
    {V : Fin n → E → E} (hf : ContDiff ℝ ∞ f) (hV : ∀ i, ContDiff ℝ ∞ (V i)) :
    ContDiff ℝ ∞ (fun x ↦ f x (V · x)) := by
  induction n with
  | zero =>
    let ev : ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ E) F →L[ℝ] F :=
      { toFun := fun T ↦ T 0
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        cont := by fun_prop }
    convert ev.contDiff.comp hf using 1
    funext x
    exact congrArg (f x) (Subsingleton.elim _ _)
  | succ n ih =>
    have hc : ContDiff ℝ ∞ (fun x ↦ (f x).curryLeft (V 0 x)) :=
      by
        let L : ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) ↦ E) F ≃L[ℝ]
            E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F :=
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) ↦ E) F).toContinuousLinearEquiv
        exact (L.contDiff.comp hf).clm_apply (hV 0)
    convert ih hc (fun i ↦ hV i.succ) using 1
    funext x
    change f x (fun i ↦ V i x) = f x (Fin.cons (V 0 x) (fun i ↦ V i.succ x))
    congr 1
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i

/-- Evaluation of a smooth form on smooth vector fields is smooth. -/
lemma contDiff_eval_fields {n : ℕ} {form : E → E [⋀^Fin n]→L[ℝ] F}
    {V : Fin n → E → E} (hf : ContDiff ℝ ∞ form) (hV : ∀ i, ContDiff ℝ ∞ (V i)) :
    ContDiff ℝ ∞ (fun x ↦ form x (V · x)) := by
  exact contDiff_multilinear_eval
    ((toContinuousMultilinearMapCLM ℝ : (E [⋀^Fin n]→L[ℝ] F) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F).contDiff.comp hf) hV

end KervaireClosedCurrent

namespace KervaireCurrentHomotopy
open KervaireClosedCurrent KervaireHaarFlow VectorField ContinuousAlternatingMap
open scoped ContDiff

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

/-- A moving-frame homotopy formula for a closed current, proved from the actual exterior
 derivative identity and differentiation under a compact-parameter integral. -/
lemma integral_eval_constant {n : ℕ} {e : S → E} (he : Continuous e)
    {form : (ℝ × E) → (ℝ × E) [⋀^Fin (n+1)]→L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ form)
    {V : Fin (n+2) → (ℝ × E) → (ℝ × E)} (hV : ∀ i, ContDiff ℝ ∞ (V i))
    (hVzero : ∀ p, V 0 p = (1, 0))
    (hdiv : ∀ (t : ℝ) (i : Fin (n+2)), i ≠ 0 → ∀ (g : (ℝ × E) → ℝ),
      ContDiff ℝ ∞ g →
      (∫ x, fderiv ℝ g (t,e x) (V i (t,e x)) ∂μ) = 0)
    (hbracket : ∀ (t : ℝ) (x : S) (i j : Fin (n+1)), i ≤ j →
      form (t,e x) (Matrix.vecCons (lieBracket ℝ (V i.castSucc) (V j.succ) (t,e x))
        (j.removeNth (i.castSucc.removeNth (fun l ↦ V l (t,e x))))) = 0)
    (hclosed : ∀ (t : ℝ) (x : S),
      extDeriv form (t,e x) (fun l ↦ V l (t,e x)) = 0) (t₀ t₁ : ℝ) :
    (∫ x, form (t₀,e x) ((0 : Fin (n+2)).removeNth (fun l ↦ V l (t₀,e x))) ∂μ) =
    (∫ x, form (t₁,e x) ((0 : Fin (n+2)).removeNth (fun l ↦ V l (t₁,e x))) ∂μ) := by
  let g (i : Fin (n+2)) (p : ℝ × E) := form p (i.removeNth (V · p))
  have hg (i) : ContDiff ℝ ∞ (g i) := contDiff_eval_fields hf (fun _ ↦ hV _)
  let f (t : ℝ) (x : S) := g 0 (t,e x)
  let df (t : ℝ) (x : S) := fderiv ℝ (g 0) (t,e x) (1,0)
  have hc : Continuous (fun p : ℝ × S ↦ (p.1,e p.2)) :=
    continuous_fst.prodMk (he.comp continuous_snd)
  have hfc : Continuous (Function.uncurry f) := (hg 0).continuous.comp hc
  have hdc : Continuous (Function.uncurry df) :=
    ((hg 0).continuous_fderiv (by simp)).comp hc |>.clm_apply continuous_const
  have hfd (t : ℝ) (x : S) : HasDerivAt (fun u ↦ f u x) (df t x) t := by
    exact ((hg 0).differentiable (by simp) (t,e x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t (e x)))
  have formula (t : ℝ) (x : S) :
      (∑ i : Fin (n+2), (-1 : ℝ)^i.val * fderiv ℝ (g i) (t,e x) (V i (t,e x))) = 0 := by
    have hb : (∑ i : Fin (n+1), ∑ j ≥ i, (-1 : ℤ)^(i+j : ℕ) •
        form (t,e x) (Matrix.vecCons (lieBracket ℝ (V i.castSucc) (V j.succ) (t,e x))
          (j.removeNth (i.castSucc.removeNth (fun l ↦ V l (t,e x)))))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j hj
      rw [hbracket t x i j (Finset.mem_Ici.mp hj), smul_zero]
    have h := extDeriv_apply_vectorField (hf.differentiable (by simp) (t,e x))
      (fun i ↦ (hV i).differentiable (by simp) (t,e x))
    rw [hclosed t x, hb, sub_zero] at h
    simpa only [g, ← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one,
      smul_eq_mul] using h.symm
  have hdi (t : ℝ) : (∫ x, df t x ∂μ) = 0 := by
    have hint (i : Fin (n+2)) : Integrable
        (fun x ↦ (-1 : ℝ)^i.val * fderiv ℝ (g i) (t,e x) (V i (t,e x))) μ :=
      continuous_integrable (continuous_const.mul
        ((((hg i).continuous_fderiv (by simp)).comp (continuous_const.prodMk he)).clm_apply
          ((hV i).continuous.comp (continuous_const.prodMk he))))
    have hsum := congrArg (fun a : S → ℝ ↦ ∫ x, a x ∂μ) (funext (formula t))
    rw [integral_zero, integral_finsetSum _ (fun i _ ↦ hint i), Fin.sum_univ_succ] at hsum
    have hz (i : Fin (n+1)) : (∫ x, (-1 : ℝ)^i.succ.val *
         fderiv ℝ (g i.succ) (t,e x) (V i.succ (t,e x)) ∂μ) = 0 := by
      rw [integral_const_mul, hdiv t i.succ (Fin.succ_ne_zero _) _ (hg _), mul_zero]
    simpa only [Fin.val_zero, pow_zero, one_mul, hz, Finset.sum_const_zero,
      add_zero, hVzero, df] using hsum
  have hd (t : ℝ) : HasDerivAt (fun u ↦ ∫ x, f u x ∂μ) 0 t := by
    simpa only [hdi] using hasDerivAt_integral_compact (μ := μ) hfc hdc hfd t
  exact is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt) (fun t ↦ (hd t).deriv) t₀ t₁

end KervaireCurrentHomotopy

namespace KervaireHaarFlow

open NormedSpace
open scoped ContDiff

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  [StarRing B] [ContinuousStar B] [StarModule ℝ B]

local instance : NormedAlgebra ℚ B := .restrictScalars ℚ ℝ B

/-- The genuine exponential flow in the unitary group. -/
def expFlow (a : skewAdjoint.submodule ℝ B) (t : ℝ) : unitary B :=
  ⟨exp (t • (a : B)), exp_mem_unitary_of_mem_skewAdjoint (by
    change star (t • (a : B)) = -(t • (a : B))
    rw [star_smul, star_trivial, a.property, smul_neg])⟩

variable [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

/-- Right-invariant vector fields on a compact unitary group have zero Haar divergence.
The derivative is the ambient Fréchet derivative. -/
lemma integral_unitary_fderiv_mul_eq_zero {g : B → ℝ} (hg : ContDiff ℝ ∞ g)
    (a : skewAdjoint.submodule ℝ B) :
    (∫ x : unitary B, fderiv ℝ g (x : B) ((x : B) * a) ∂μ) = 0 := by
  let h : ℝ → unitary B → B := fun t x ↦ (x : B) * exp (t • (a : B))
  have hh : Continuous (Function.uncurry h) := by
    exact (continuous_subtype_val.comp continuous_snd).mul
      ((exp_continuous).comp (continuous_fst.smul continuous_const))
  have hf : Continuous (Function.uncurry fun t x ↦ g (h t x)) := hg.continuous.comp hh
  have hd : Continuous (Function.uncurry fun t x ↦ fderiv ℝ g (h t x) (h t x * a)) :=
    ((hg.continuous_fderiv (by simp)).comp hh).clm_apply (hh.mul continuous_const)
  have hfd (t : ℝ) (x : unitary B) : HasDerivAt (fun u ↦ g (h u x))
      (fderiv ℝ g (h t x) (h t x * a)) t := by
    apply (hg.differentiable (by simp) (h t x)).hasFDerivAt.comp_hasDerivAt
    convert (hasDerivAt_const t (x : B)).mul
      (hasDerivAt_exp_smul_const (a : B) t) using 1
    first | rfl | simp [h, mul_assoc]
  have hinv (t : ℝ) : (∫ x, g (h t x) ∂μ) = ∫ x, g (h 0 x) ∂μ := by
    simpa [h, expFlow] using integral_mul_right_eq_self (μ := μ)
      (fun x : unitary B ↦ g (x : B)) (expFlow a t)
  simpa [h] using integral_deriv_eq_zero_of_invariant (μ := μ) hf hd hfd hinv 0

end KervaireHaarFlow

namespace KervaireUnitaryHaarCurrent
open MeasureTheory VectorField
open scoped ContDiff
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- The autonomous lift of a right-translation field to the time cylinder. -/
def liftField (a : B) : (ℝ × B) →L[ℝ] (ℝ × B) :=
  (ContinuousLinearMap.inr ℝ ℝ B).comp
    (((ContinuousLinearMap.mul ℝ B).flip a).comp (ContinuousLinearMap.snd ℝ ℝ B))

@[simp] lemma liftField_apply (a : B) (p : ℝ × B) : liftField a p = (0,p.2*a) := rfl

lemma bracket_lift (a b : B) (p : ℝ × B) :
    lieBracket ℝ (liftField a) (liftField b) p = liftField (a*b-b*a) p := by
  simp only [lieBracket, ContinuousLinearMap.fderiv, liftField_apply, Prod.sub_def, sub_self]
  congr 1
  noncomm_ring

lemma bracket_time_lift (a : B) (p : ℝ × B) :
    lieBracket ℝ (fun _ : ℝ × B ↦ (1,0)) (liftField a) p = 0 := by
  simp [lieBracket]

lemma bracket_lift_time (a : B) (p : ℝ × B) :
    lieBracket ℝ (liftField a) (fun _ : ℝ × B ↦ (1,0)) p = 0 := by
  rw [lieBracket_swap, bracket_time_lift, neg_zero]

variable [CompleteSpace B] [StarRing B] [ContinuousStar B] [StarModule ℝ B]
  [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

lemma integral_liftField_eq_zero (t : ℝ) {g : (ℝ × B) → ℝ} (hg : ContDiff ℝ ∞ g)
    (a : skewAdjoint.submodule ℝ B) :
    (∫ x : unitary B, fderiv ℝ g (t,(x : B)) (liftField (a : B) (t,(x : B))) ∂μ) = 0 := by
  let f : B → ℝ × B := fun x ↦ (t,x)
  have hf : ContDiff ℝ ∞ f := contDiff_const.prodMk contDiff_id
  have heq (x : B) :
      fderiv ℝ (g ∘ f) x (x*(a : B)) = fderiv ℝ g (t,x) (0,x*(a : B)) := by
    rw [fderiv_comp x (hg.differentiable (by simp) _) (hf.differentiable (by simp) _)]
    have hdf : HasFDerivAt f (ContinuousLinearMap.inr ℝ ℝ B) x :=
      (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
    rw [hdf.fderiv]
    rfl
  simpa only [liftField_apply, heq] using
    KervaireHaarFlow.integral_unitary_fderiv_mul_eq_zero (μ := μ) (hg.comp hf) a

end KervaireUnitaryHaarCurrent

namespace KervaireCompactUnitary
variable {B : Type*} [CStarAlgebra B] [FiniteDimensional ℂ B]

lemma isCompact_unitary : IsCompact (unitary B : Set B) := by
  apply (isCompact_closedBall (0 : B) 1).of_isClosed_subset isClosed_unitary
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  nontriviality B
  exact (CStarRing.norm_of_mem_unitary hu).le

/-- The unitary group of a finite-dimensional complex C⋆-algebra is compact. -/
lemma compactSpace : CompactSpace (unitary B) :=
  isCompact_iff_compactSpace.mp isCompact_unitary

end KervaireCompactUnitary

end

end OAI
