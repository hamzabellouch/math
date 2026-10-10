import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ClusterShift
import OAI.Probability.LatticeSurface.Dynamics.JacobianIdentity
import OAI.Probability.LatticeSurface.Dynamics.LogDet
import OAI.Probability.LatticeSurface.Dynamics.MatrixJacobi
import OAI.Probability.LatticeSurface.Dynamics.ShiftData

namespace OAI

open Set MeasureTheory intervalIntegral

open Matrix Polynomial

open scoped Topology

open Set MeasureTheory Filter

open scoped Topology

namespace TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma opNorm_le_of_row_sum (A : (V → ℝ) →L[ℝ] (V → ℝ)) (K : ℝ) (hK : 0 ≤ K)
    (hrow : ∀ i, ∑ j, |asMatrix A i j| ≤ K) : ‖A‖ ≤ K := by
  apply A.opNorm_le_bound hK
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg v))).mpr
  intro i
  have he : A v i = ∑ j, asMatrix A i j * v j := by
    exact congrFun (LinearMap.toMatrix'_mulVec A.toLinearMap v).symm i
  rw [Real.norm_eq_abs, he]
  calc
    _ ≤ ∑ j, |asMatrix A i j| * |v j| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => asMatrix A i j * v j) Finset.univ
    _ ≤ ∑ j, |asMatrix A i j| * ‖v‖ := by
      apply Finset.sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j, |asMatrix A i j|) * ‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ K * ‖v‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)

end TangentialJacobian

namespace FeasibleShift

open TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma freeShift_derivative_row (G : SimpleGraph V) (ground pins : Finset V)
    (β f : V → ℝ) (h : FreeSites pins → ℝ)
    (s₀ s₁ s₂ L : ℝ) (D : ℕ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hD : ∀ x, (neighbors G x).card ≤ D)
    (A : (FreeSites pins → ℝ) →L[ℝ] (FreeSites pins → ℝ))
    (hu : HasFDerivAt (freeShift G ground pins β f s₀ s₁) A h) (x : FreeSites pins) :
    ∑ j, |asMatrix A x j| ≤ ((s₁ - s₀)⁻¹ * (4 * D * L)) *
      ((component (contactGraph G (extendHeight pins β h) s₂) x).card : ℝ)^2 := by
  classical
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  let C := component (contactGraph G (extendHeight pins β h) s₂) x
  let F : Finset (FreeSites pins) := Finset.univ.filter fun j => (j : V) ∈ C
  have hFc : F.card ≤ C.card := by
    apply Finset.card_le_card_of_injOn (fun j : FreeSites pins => (j : V))
    · intro j hj; exact (Finset.mem_filter.mp hj).2
    · intro j hj k hk hjk; exact Subtype.ext hjk
  have hsum : ∑ j, |asMatrix A x j| = ∑ j ∈ F, |asMatrix A x j| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hj' : (j : V) ∉ C := by simpa [F] using hj
    rw [asMatrix_apply, freeShift_derivative_entry_zero G ground pins β f h s₀ s₁ s₂ L
      hs hss hL hfground hfl A hu x j hj', abs_zero]
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ F, ((s₁ - s₀)⁻¹ * (4 * D * L)) * C.card := by
      apply Finset.sum_le_sum; intro j _
      exact freeShift_derivative_entry G ground pins β f h s₀ s₁ s₂ L D hs hss hL hfground hfl hD A hu x j
    _ ≤ C.card * (((s₁ - s₀)⁻¹ * (4 * D * L)) * C.card) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hFc) (by positivity)
    _ = _ := by dsimp [C]; ring

lemma freeShift_derivative_column (G : SimpleGraph V) (ground pins : Finset V)
    (β f : V → ℝ) (h : FreeSites pins → ℝ)
    (s₀ s₁ s₂ L : ℝ) (D : ℕ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hD : ∀ x, (neighbors G x).card ≤ D)
    (A : (FreeSites pins → ℝ) →L[ℝ] (FreeSites pins → ℝ))
    (hu : HasFDerivAt (freeShift G ground pins β f s₀ s₁) A h) (j : FreeSites pins) :
    ‖A (Pi.single j 1)‖ ≤ ((s₁ - s₀)⁻¹ * (4 * D * L)) *
      (component (contactGraph G (extendHeight pins β h) s₂) j).card := by
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro x
  rw [Real.norm_eq_abs]
  by_cases hj : (j : V) ∈ component (contactGraph G (extendHeight pins β h) s₂) x
  · have he := component_eq_of_reachable ((mem_component _ _ _).mp hj)
    rw [← he]
    exact freeShift_derivative_entry G ground pins β f h s₀ s₁ s₂ L D hs hss hL hfground hfl hD A hu x j
  · rw [freeShift_derivative_entry_zero G ground pins β f h s₀ s₁ s₂ L
      hs hss hL hfground hfl A hu x j hj, abs_zero]
    positivity

lemma freeShift_derivative_cost (G : SimpleGraph V) (ground pins : Finset V)
    (β f : V → ℝ) (h : FreeSites pins → ℝ)
    (s₀ s₁ s₂ L : ℝ) (D : ℕ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hD : ∀ x, (neighbors G x).card ≤ D)
    (A : (FreeSites pins → ℝ) →L[ℝ] (FreeSites pins → ℝ))
    (hu : HasFDerivAt (freeShift G ground pins β f s₀ s₁) A h) :
    jacobianCost A ≤ ((s₁ - s₀)⁻¹ * (4 * D * L)) ^ 2 *
        ∑ x : FreeSites pins, if (x : V) ∈ ground then 0 else
          ((component (contactGraph G (extendHeight pins β h) s₂) x).card : ℝ) ^ 3 := by
  classical
  rw [jacobianCost, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  by_cases hx : (x : V) ∈ ground
  · simp only [ite_eq_left hx, mul_zero, asMatrix_apply,
      freeShift_derivative_ground G ground pins β f h s₀ s₁ A hu x _ hx,
      abs_zero, Finset.sum_const_zero, zero_mul, le_refl]
  rw [ite_eq_right hx]
  calc
    _ ≤ (((s₁ - s₀)⁻¹ * (4 * D * L)) *
        ((component (contactGraph G (extendHeight pins β h) s₂) x).card : ℝ)^2) *
        (((s₁ - s₀)⁻¹ * (4 * D * L)) *
        (component (contactGraph G (extendHeight pins β h) s₂) x).card) :=
      mul_le_mul (freeShift_derivative_row G ground pins β f h s₀ s₁ s₂ L D hs hss hL hfground hfl hD A hu x)
        (freeShift_derivative_column G ground pins β f h s₀ s₁ s₂ L D hs hss hL hfground hfl hD A hu x)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma freeShift_derivative_opNorm (G : SimpleGraph V) (ground pins : Finset V)
    (β f : V → ℝ) (h : FreeSites pins → ℝ)
    (s₀ s₁ s₂ L B : ℝ) (D : ℕ) (hs : s₀ < s₁) (hss : s₁ < s₂)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hfground : ∀ x ∈ ground, f x = 0)
    (hfl : ∀ x y, G.Adj x y → |f x - f y| ≤ L)
    (hD : ∀ x, (neighbors G x).card ≤ D)
    (hgood : ∀ x, ((component (contactGraph G (extendHeight pins β h) s₂) x).card : ℝ) ≤ B)
    (A : (FreeSites pins → ℝ) →L[ℝ] (FreeSites pins → ℝ))
    (hu : HasFDerivAt (freeShift G ground pins β f s₀ s₁) A h) :
    ‖A‖ ≤ ((s₁ - s₀)⁻¹ * (4 * D * L)) * B ^ 2 := by
  have hd : 0 < s₁ - s₀ := sub_pos.mpr hs
  apply opNorm_le_of_row_sum A _ (by positivity)
  intro x
  exact (freeShift_derivative_row G ground pins β f h s₀ s₁ s₂ L D hs hss hL hfground hfl hD A hu x).trans
    (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by positivity) hB).mpr (hgood x)) (by positivity))

end FeasibleShift

namespace FeasibleShift

open TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma freeShift_det_identity (G₀ G : SimpleGraph V) (ground pins walls : Finset V)
    (hp : pins ⊆ ground) (hw : walls ⊆ ground)
    (hG : ∀ x y, G₀.Adj x y → G.Adj x y ∨ (x ∈ ground ∧ y ∈ ground))
    (β f : V → ℝ) (I : V → Set ℝ) (s₀ s₁ M : ℝ) (hs : s₀ < s₁) (hs₀ : 0 < s₀)
    (hM : 0 ≤ M) (hfb : ∀ x, |f x| ≤ M)
    (hP : MeasurableSet (heightPolytope G₀ pins walls β I)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo (-δ) δ,
      ∫ h in heightPolytope G₀ pins walls β I,
        (1 + t • fderiv ℝ (freeShift G ground pins β f s₀ s₁) h).det =
        (volume (heightPolytope G₀ pins walls β I)).toReal := by
  have hdiff : 0 < s₁ - s₀ := sub_pos.mpr hs
  let K : NNReal := ⟨(s₁ - s₀)⁻¹ * (4 * M * Fintype.card (V × V)), by positivity⟩
  let δ : ℝ := min (s₀ / (2 * M + 1)) (1 / (K + 1))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have ht' : |t| < δ := abs_lt.mpr ht
  have htM : |t| * (2 * M) ≤ s₀ := by
    have hh := (lt_div_iff₀ (show 0 < 2 * M + 1 by positivity)).mp
      (ht'.trans_le (min_le_left _ _))
    nlinarith [abs_nonneg t]
  have htK : |t| * K < 1 := by
    have hh := (lt_div_iff₀ (show 0 < (K : ℝ) + 1 by positivity)).mp
      (ht'.trans_le (min_le_right _ _))
    nlinarith [abs_nonneg t]
  have hu : LipschitzWith K (freeShift G ground pins β f s₀ s₁) :=
    freeShift_lipschitz G ground pins β f s₀ s₁ M hs hM hfb
  exact det_integral_of_invariant _ K hu _ hP t htK
    (identity_add_bijective _ K hu t htK).injective.injOn
    (freeShift_small_polytope_onto G₀ G ground pins walls hp hw hG β f I s₀ s₁ M t
      hs hs₀.le hM hfb htM htK)

lemma freeShift_divergence_identities (G₀ G : SimpleGraph V) (ground pins walls : Finset V)
    (hp : pins ⊆ ground) (hw : walls ⊆ ground)
    (hG : ∀ x y, G₀.Adj x y → G.Adj x y ∨ (x ∈ ground ∧ y ∈ ground))
    (β f : V → ℝ) (I : V → Set ℝ) (s₀ s₁ M : ℝ) (hs : s₀ < s₁) (hs₀ : 0 < s₀)
    (hM : 0 ≤ M) (hfb : ∀ x, |f x| ≤ M)
    (hP : MeasurableSet (heightPolytope G₀ pins walls β I))
    (hPfin : volume (heightPolytope G₀ pins walls β I) ≠ ⊤) :
    (∫ h in heightPolytope G₀ pins walls β I,
      (asMatrix (fderiv ℝ (freeShift G ground pins β f s₀ s₁) h)).trace) = 0 ∧
    (∫ h in heightPolytope G₀ pins walls β I,
      (asMatrix (fderiv ℝ (freeShift G ground pins β f s₀ s₁) h)).trace ^ 2) =
    (∫ h in heightPolytope G₀ pins walls β I,
      (asMatrix (fderiv ℝ (freeShift G ground pins β f s₀ s₁) h *
        fderiv ℝ (freeShift G ground pins β f s₀ s₁) h)).trace) := by
  let P := heightPolytope G₀ pins walls β I
  let u := freeShift G ground pins β f s₀ s₁
  have hdiff : 0 < s₁ - s₀ := sub_pos.mpr hs
  let K : NNReal := ⟨(s₁ - s₀)⁻¹ * (4 * M * Fintype.card (V × V)), by positivity⟩
  have hu : LipschitzWith K u := freeShift_lipschitz G ground pins β f s₀ s₁ M hs hM hfb
  let : IsFiniteMeasure (volume.restrict P) := ⟨by simpa [P] using hPfin.lt_top⟩
  obtain ⟨δ, hδ, hid⟩ := freeShift_det_identity G₀ G ground pins walls hp hw hG β f I s₀ s₁ M
    hs hs₀ hM hfb hP
  have hid' : ∀ t ∈ Set.Ioo (-δ) δ, ∫ h, (1 + t • fderiv ℝ u h).det ∂(volume.restrict P) =
      ((volume.restrict P) Set.univ).toReal := by simpa [P, u] using hid
  refine ⟨trace_integral_zero_of_det_identity (volume.restrict P) (fderiv ℝ u)
      (measurable_fderiv ℝ u) K (fun h => norm_fderiv_le_of_lipschitz ℝ hu) δ hδ hid',
    trace_square_integral_of_det_identity (volume.restrict P) (fderiv ℝ u)
      (measurable_fderiv ℝ u) K (fun h => norm_fderiv_le_of_lipschitz ℝ hu) δ hδ hid'⟩

end FeasibleShift

namespace TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma continuous_trace : Continuous (fun A : (V → ℝ) →L[ℝ] (V → ℝ) => (asMatrix A).trace) := by
  simp_rw [← traceCLM_apply]
  exact (traceCLM (V := V)).continuous

lemma continuous_jacobianCost : Continuous (jacobianCost : ((V → ℝ) →L[ℝ] (V → ℝ)) → ℝ) := by
  unfold jacobianCost
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul
  · apply continuous_finsetSum
    intro j _
    simp only [asMatrix_apply]
    fun_prop
  · fun_prop

omit [DecidableEq V] in
lemma uniform_image_area (P S : Set (V → ℝ)) (hP : MeasurableSet P) (hS : MeasurableSet S)
    (hSP : S ⊆ P) (T : (V → ℝ) → (V → ℝ)) (K : NNReal) (hT : LipschitzWith K T)
    (hinj : Set.InjOn T S) (hTP : T '' S ⊆ P) :
    (ProbabilityTheory.cond volume P).real (T '' S) =
      ∫ x in S, |(fderiv ℝ T x).det| ∂(ProbabilityTheory.cond volume P) := by
  have harea := lipschitz_area hT hS hinj
  have he : P ∩ (T '' S) = T '' S := Set.inter_eq_right.mpr hTP
  rw [measureReal_def, ProbabilityTheory.cond_apply hP, he, ENNReal.toReal_mul,
    ProbabilityTheory.cond, Measure.restrict_smul, Measure.restrict_restrict hS,
    Set.inter_eq_left.mpr hSP, MeasureTheory.integral_smul_measure]
  congr 1
  symm
  calc
    _ = (∫⁻ x in S, ENNReal.ofReal |(fderiv ℝ T x).det|).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => abs_nonneg _)
        ((ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ T)).abs.aestronglyMeasurable)
    _ = _ := congrArg ENNReal.toReal harea

omit [DecidableEq V] in
lemma jacobian_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (B : Ω → (V → ℝ) →L[ℝ] (V → ℝ)) (hB : Measurable B) (K : ℝ)
    (hK : ∀ x, ‖B x‖ ≤ K) : Integrable (fun x => |(B x).det|) μ :=
  continuous_integrable_of_bounded μ B hB K hK _ (ContinuousLinearMap.continuous_det.abs)

omit [DecidableEq V] in
lemma uniform_image_lower_bound (P S : Set (V → ℝ)) (hP : MeasurableSet P) (hS : MeasurableSet S)
    (hSP : S ⊆ P) (hPzero : volume P ≠ 0) (hPfin : volume P ≠ ⊤)
    (T : (V → ℝ) → (V → ℝ)) (K : NNReal) (hT : LipschitzWith K T)
    (hinj : Set.InjOn T S) (hTP : T '' S ⊆ P) (c : ℝ)
    (hdet : ∀ᵐ x ∂(volume.restrict S), c ≤ |(fderiv ℝ T x).det|) :
    c * (ProbabilityTheory.cond volume P).real S ≤
      (ProbabilityTheory.cond volume P).real (T '' S) := by
  let μ := ProbabilityTheory.cond volume P
  let : IsProbabilityMeasure μ := ProbabilityTheory.cond_isProbabilityMeasure_of_finite hPzero hPfin
  rw [uniform_image_area P S hP hS hSP T K hT hinj hTP]
  have hdet' : ∀ᵐ x ∂(μ.restrict S), c ≤ |(fderiv ℝ T x).det| := by
    have hab : μ.restrict S ≪ volume.restrict S :=
      (show μ ≪ volume from ProbabilityTheory.cond_absolutelyContinuous).restrict S
    exact hab.ae_le hdet
  have hi := jacobian_integrable μ (fderiv ℝ T) (measurable_fderiv ℝ T) K
    (fun x => norm_fderiv_le_of_lipschitz ℝ hT)
  have hh := integral_mono_ae (integrable_const c : Integrable (fun _ : V → ℝ => c) (μ.restrict S))
    hi.integrableOn hdet'
  simpa only [MeasureTheory.integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_comm,
    measureReal_def] using hh

end TangentialJacobian

namespace TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma markov_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Ω → ℝ) (hF : Integrable F μ) (hn : ∀ x, 0 ≤ F x) (K : ℝ) (hK : 0 < K) :
    μ.real {x | K < F x} ≤ (∫ x, F x ∂μ) / K := by
  apply (le_div_iff₀ hK).mpr
  have hh := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hn) hF K
  have hm : μ.real {x | K < F x} ≤ μ.real {x | K ≤ F x} :=
    measureReal_mono (fun x (hx : K < F x) => le_of_lt hx)
  nlinarith

lemma event_volume_of_moments (P G : Set (V → ℝ)) (hP : MeasurableSet P)
    (hG : MeasurableSet G) (hPzero : volume P ≠ 0) (hPfin : volume P ≠ ⊤)
    (u : (V → ℝ) → (V → ℝ)) (Klip : NNReal) (hu : LipschitzWith Klip u)
    (hinj : Set.InjOn (fun x => x + u x) G)
    (hfeas : ∀ x ∈ P ∩ G, x + u x ∈ P)
    (hnorm : ∀ x ∈ G, ‖fderiv ℝ u x‖ ≤ 1/2)
    (C p K : ℝ) (_hp : 0 < p) (hK : 1 ≤ K)
    (hmoment : (∫ x, (asMatrix (fderiv ℝ u x)).trace ^ 2 + jacobianCost (fderiv ℝ u x)
      ∂(ProbabilityTheory.cond volume P)) ≤ C)
    (hCK : C / K ≤ p/4)
    (hbad : (ProbabilityTheory.cond volume P).real Gᶜ ≤ p/4)
    (E : Set (V → ℝ)) (hE : MeasurableSet E)
    (hEp : p ≤ (ProbabilityTheory.cond volume P).real E) :
    ∃ S : Set (V → ℝ), MeasurableSet S ∧ S ⊆ E ∩ P ∩ G ∧
      p/2 ≤ (ProbabilityTheory.cond volume P).real S ∧
      Set.InjOn (fun x => x + u x) S ∧ (fun x => x + u x) '' S ⊆ P ∧
      MeasurableSet ((fun x => x + u x) '' S) ∧
      Real.exp (-2*K) * p/2 ≤ (ProbabilityTheory.cond volume P).real ((fun x => x + u x) '' S) := by
  let μ := ProbabilityTheory.cond volume P
  let : IsProbabilityMeasure μ := ProbabilityTheory.cond_isProbabilityMeasure_of_finite hPzero hPfin
  let A := fderiv ℝ u
  let F := fun x => (asMatrix (A x)).trace ^ 2 + jacobianCost (A x)
  have hFc : Continuous (fun B : (V → ℝ) →L[ℝ] (V → ℝ) => (asMatrix B).trace ^ 2 + jacobianCost B) :=
    (continuous_trace.pow 2).add continuous_jacobianCost
  have hFm : Measurable F := hFc.measurable.comp (measurable_fderiv ℝ u)
  have hFi : Integrable F μ := continuous_integrable_of_bounded μ A (measurable_fderiv ℝ u) Klip
    (fun x => norm_fderiv_le_of_lipschitz ℝ hu) _ hFc
  have hFn (x) : 0 ≤ F x := add_nonneg (sq_nonneg _) (jacobianCost_nonneg _)
  let B := Gᶜ ∪ {x | K < F x}
  have hBm : MeasurableSet B := hG.compl.union (measurableSet_lt measurable_const hFm)
  have hBm_bound : μ.real B ≤ p/2 := by
    have hmark := markov_real μ F hFi hFn K (by linarith)
    have hquot : (∫ x, F x ∂μ) / K ≤ C / K := div_le_div_of_nonneg_right hmoment (by linarith)
    have hh := measureReal_union_le (μ := μ) Gᶜ {x | K < F x}
    dsimp [B]
    linarith
  let S := (E ∩ P) \ B
  have hSm : MeasurableSet S := (hE.inter hP).diff hBm
  have hSsub : S ⊆ E ∩ P ∩ G := by
    intro x hx
    exact ⟨hx.1, by by_contra hg; exact hx.2 (Or.inl hg)⟩
  have hSmass : p/2 ≤ μ.real S := by
    have heq : μ.real (E ∩ P) = μ.real E := by
      unfold Measure.real
      congr 1
      rw [Set.inter_comm, ProbabilityTheory.cond_inter_self hP]
    have hh := le_measureReal_sdiff (μ := μ) (s₁ := E ∩ P) (s₂ := B)
    rw [heq] at hh
    linarith
  have hSinj : Set.InjOn (fun x => x + u x) S := hinj.mono (fun x hx => (hSsub hx).2)
  have hSP : S ⊆ P := fun x hx => (hSsub hx).1.2
  have hSTP : (fun x => x + u x) '' S ⊆ P := by
    rintro y ⟨x, hx, rfl⟩
    exact hfeas x ⟨hSP hx, (hSsub hx).2⟩
  have hSTm : MeasurableSet ((fun x => x + u x) '' S) :=
    hSm.image_of_continuousOn_injOn (continuous_id.add hu.continuous).continuousOn hSinj
  have hdet : ∀ᵐ x ∂(volume.restrict S), Real.exp (-2*K) ≤ |(fderiv ℝ (fun x => x + u x) x).det| := by
    filter_upwards [ae_restrict_mem hSm, ae_restrict_of_ae (ae_fderiv_id_add_smul hu 1)] with x hx hdx
    have hdx' : fderiv ℝ (fun x => x + u x) x = 1 + A x := by simpa [A] using hdx
    rw [hdx']
    have hAx := hnorm x ((hSsub hx).2)
    have hFK : F x ≤ K := le_of_not_gt (fun h => hx.2 (Or.inr h))
    have ht : |(asMatrix (A x)).trace| ≤ K := by
      have hcost := jacobianCost_nonneg (A x)
      have habsq := sq_abs (asMatrix (A x)).trace
      have hab := abs_nonneg (asMatrix (A x)).trace
      dsimp [F] at hFK
      nlinarith
    have hc : jacobianCost (A x) ≤ K := by
      dsimp [F] at hFK
      nlinarith [sq_nonneg (asMatrix (A x)).trace]
    have hlog := logdet_lower_bound (A x) hAx
    have hpos := det_one_add_pos (A x) (hAx.trans_lt (by norm_num))
    rw [abs_of_pos hpos, ← Real.exp_log hpos]
    apply Real.exp_le_exp.mpr
    have htt := (abs_le.mp ht).1
    linarith
  have harea := uniform_image_lower_bound P S hP hSm hSP hPzero hPfin
    (fun x => x + u x) (1 + Klip) (by simpa using lipschitz_id_add_smul hu 1)
    hSinj hSTP (Real.exp (-2*K)) hdet
  refine ⟨S, hSm, hSsub, hSmass, hSinj, hSTP, hSTm, ?_⟩
  have hexp : 0 ≤ Real.exp (-2*K) := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left hSmass hexp]

end TangentialJacobian

end OAI
