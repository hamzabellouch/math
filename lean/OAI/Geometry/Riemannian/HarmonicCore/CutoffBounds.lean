import OAI.Geometry.Riemannian.HarmonicCore.InteriorDerivative

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3
lemma continuous_compact_bound {V : Type*} [NormedAddCommGroup V]
    (f : E3 → V) (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ K : ℝ, ∀ x, ‖f x‖ ≤ K := by
  obtain ⟨K,hK⟩ := (hs.image hf).isBounded.exists_norm_le
  refine ⟨max K 0,fun x ↦ ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact (hK (f x) (mem_image_of_mem f hx)).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    exact le_max_right _ _

theorem weak_cutoff_H2 (R S T : ℝ) (hRS : R < S)
    (A : E3 → E3 →L[ℝ] E3) (C L c : ℝ) (hc : 0 < c) (hL0 : 0 ≤ L)
    (hA : Continuous A) (hC : ∀ x, ‖A x‖ ≤ C) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = 0)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a : E3) :
    ∃ w : ZeroSobolev R, sobolevValue R w = componentL2 a
      (sobolevDerivative R (cutoffSobolev R T χ hχ hsupp K D hK hD u)) := by
  obtain ⟨w1,_,hw1⟩ := weak_interior_derivative_sobolev R S T hRS A C L c hc hL0 hA hC hL hpos
    u hu χ hχ hsupp K D hK hD a
  let θ : E3 → ℝ := fun x ↦ fderiv ℝ χ x a
  have hθ : ContDiff ℝ ∞ θ := (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hsθ : tsupport θ ⊆ Metric.ball 0 R := (tsupport_fderiv_apply_subset ℝ a).trans hsupp
  have hcompact : HasCompactSupport θ :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport θ,Metric.isBounded_ball.subset hsθ⟩
  obtain ⟨Kθ,hKθ⟩ := continuous_compact_bound θ hθ.continuous hcompact
  obtain ⟨Dθ,hDθ⟩ := continuous_compact_bound (gradient θ) (gradient_continuous hθ) (gradient_compact hcompact)
  let w2 := cutoffSobolev R T θ hθ hsθ Kθ Dθ hKθ hDθ u
  refine ⟨w1+w2,?_⟩
  rw [map_add,hw1]
  change scalarFieldCLM χ hχ.continuous K hK (componentL2 a (sobolevDerivative T u)) +
    scalarFieldCLM θ hθ.continuous Kθ hKθ (sobolevValue T u) =
    componentL2 a (scalarFieldCLM χ hχ.continuous K hK (sobolevDerivative T u) +
      gradientFieldCLM χ hχ D hD (sobolevValue T u))
  rw [map_add,componentL2_scalar]
  congr 1
  apply Lp.ext
  filter_upwards [scalarFieldCLM_coe θ hθ.continuous Kθ hKθ (sobolevValue T u),
    componentL2_coe a (gradientFieldCLM χ hχ D hD (sobolevValue T u)),
    gradientFieldCLM_coe χ hχ D hD (sobolevValue T u)] with x h1 h2 h3
  rw [h1,h2,h3,inner_smul_right,inner_gradient_right]
  simp only [conj_trivial,smul_eq_mul,θ,mul_comm]

lemma sobolev_gradient_norm_le (R : ℝ) (u : ZeroSobolev R) :
    ‖sobolevDerivative R u‖ ≤ ‖u‖ := WithLp.norm_snd_le ValueL2 u.val

lemma cutoff_gradient_bound (R T : ℝ) (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ Metric.ball 0 R) (K D : ℝ)
    (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D) (u : ZeroSobolev T) :
    ‖sobolevDerivative R (cutoffSobolev R T χ hχ hsupp K D hK hD u)‖ ≤
      K*‖sobolevDerivative T u‖+D*‖sobolevValue T u‖ := by
  change ‖scalarFieldCLM χ hχ.continuous K hK (sobolevDerivative T u) +
    gradientFieldCLM χ hχ D hD (sobolevValue T u)‖ ≤ _
  exact (norm_add_le _ _).trans (add_le_add (scalarFieldCLM_norm χ hχ.continuous K hK _)
    (gradientFieldCLM_norm χ hχ D hD _))

lemma component_gradientField (χ θ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hθ : Continuous θ) (D Kθ : ℝ) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (hKθ : ∀ x, ‖θ x‖ ≤ Kθ) (a : E3) (ha : ∀ x, θ x = fderiv ℝ χ x a)
    (u : ValueL2) :
    componentL2 a (gradientFieldCLM χ hχ D hD u) = scalarFieldCLM θ hθ Kθ hKθ u := by
  apply Lp.ext
  filter_upwards [componentL2_coe a (gradientFieldCLM χ hχ D hD u),
    gradientFieldCLM_coe χ hχ D hD u,scalarFieldCLM_coe θ hθ Kθ hKθ u] with x h1 h2 h3
  rw [h1,h2,h3,inner_smul_right,inner_gradient_right,ha x]
  simp only [conj_trivial,smul_eq_mul]
  exact mul_comm _ _

theorem weak_cutoff_H2_bound (R S T : ℝ) (hRS : R < S)
    (C L c : ℝ) (hc : 0 < c) (hL0 : 0 ≤ L)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a : E3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (A : E3 → E3 →L[ℝ] E3) (hA : Continuous A)
      (hC : ∀ x, ‖A x‖ ≤ C) (_hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖),
      (∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ) → ∀ u : ZeroSobolev T,
      (∀ v : ZeroSobolev S,
        ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = 0) →
      ∃ w : ZeroSobolev R,
        sobolevValue R w = componentL2 a (sobolevDerivative R (cutoffSobolev R T χ hχ hsupp K D hK hD u)) ∧
        ‖sobolevDerivative R w‖ ≤ B*(‖sobolevValue T u‖+‖sobolevDerivative T u‖) := by
  let θ : E3 → ℝ := fun x ↦ fderiv ℝ χ x a
  have hθ : ContDiff ℝ ∞ θ := (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hsθ : tsupport θ ⊆ Metric.ball 0 R := (tsupport_fderiv_apply_subset ℝ a).trans hsupp
  have hcompact : HasCompactSupport θ :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport θ,Metric.isBounded_ball.subset hsθ⟩
  obtain ⟨Kθ,hKθ⟩ := continuous_compact_bound θ hθ.continuous hcompact
  obtain ⟨Dθ,hDθ⟩ := continuous_compact_bound (gradient θ) (gradient_continuous hθ) (gradient_compact hcompact)
  let B1 : ℝ := (poincareConstant R+1)*(((((2*C+2)/c+1)*(D+K*L))+D)*‖a‖)
  have hKθ0 : 0 ≤ Kθ := (norm_nonneg (θ 0)).trans (hKθ 0)
  have hDθ0 : 0 ≤ Dθ := (norm_nonneg (gradient θ 0)).trans (hDθ 0)
  refine ⟨max B1 0+Kθ+Dθ,by positivity,fun A hA hC hL hpos u hu ↦ ?_⟩
  obtain ⟨w1,hn1,hw1⟩ := weak_interior_derivative_sobolev R S T hRS A C L c hc hL0 hA hC hL hpos
    u hu χ hχ hsupp K D hK hD a
  let w2 := cutoffSobolev R T θ hθ hsθ Kθ Dθ hKθ hDθ u
  refine ⟨w1+w2,?_,?_⟩
  · rw [map_add,hw1]
    change scalarFieldCLM χ hχ.continuous K hK (componentL2 a (sobolevDerivative T u)) +
      scalarFieldCLM θ hθ.continuous Kθ hKθ (sobolevValue T u) =
      componentL2 a (scalarFieldCLM χ hχ.continuous K hK (sobolevDerivative T u) +
        gradientFieldCLM χ hχ D hD (sobolevValue T u))
    rw [map_add,componentL2_scalar,component_gradientField χ θ hχ hθ.continuous D Kθ hD hKθ a (fun _ ↦ rfl)]
  · have hw1n : ‖sobolevDerivative R w1‖ ≤ max B1 0*‖sobolevDerivative T u‖ := by
      apply (sobolev_gradient_norm_le R w1).trans
      apply hn1.trans
      simpa only [B1,←mul_assoc] using mul_le_mul_of_nonneg_right (le_max_left B1 0)
        (norm_nonneg (sobolevDerivative T u))
    have hw2n := cutoff_gradient_bound R T θ hθ hsθ Kθ Dθ hKθ hDθ u
    rw [map_add]
    apply (norm_add_le _ _).trans
    change ‖sobolevDerivative R w1‖+‖sobolevDerivative R w2‖ ≤ _
    change ‖sobolevDerivative R w2‖ ≤ Kθ*‖sobolevDerivative T u‖+Dθ*‖sobolevValue T u‖ at hw2n
    calc
      _ ≤ (max B1 0+Kθ)*‖sobolevDerivative T u‖+Dθ*‖sobolevValue T u‖ := by
        simpa only [add_mul,add_assoc] using add_le_add hw1n hw2n
      _ ≤ (max B1 0+Kθ)*(‖sobolevValue T u‖+‖sobolevDerivative T u‖)+
          Dθ*(‖sobolevValue T u‖+‖sobolevDerivative T u‖) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _))
            (add_nonneg (le_max_right B1 0) hKθ0))
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) hDθ0)
      _ = _ := (add_mul _ _ _).symm

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
