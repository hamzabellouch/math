import OAI.Geometry.Immersion.ClosedSurface.SmallRealization
import OAI.Geometry.Immersion.ClosedSurface.PhaseDecomposition
import OAI.Geometry.Immersion.ClosedSurface.AtlasDenominators

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Bundle Manifold Filter


theorem space_inner_eq_sum (v w : Space) :
    inner ℝ v w = ∑ i : Fin 4, v i * w i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]



theorem IsSmoothIsometricImmersion.mfderiv_injective {g : SmoothMetric M}
    {F : M → Space} (h : IsSmoothIsometricImmersion M g F) (p : M) :
    Function.Injective (mfderiv planeModel spaceModel F p) := by
  intro v w hvw
  apply sub_eq_zero.mp
  by_contra hne
  have hv : mfderiv planeModel spaceModel F p (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hinner := h.2 p (v - w) (v - w)
  rw [hv, inner_zero_left] at hinner
  exact (ne_of_gt (g.pos p (v - w) hne)) hinner.symm



theorem PhaseGeometry.positive_tensor_has_basis {H : PhaseMean.Tensor}
    (h₀ : 0 < H 0) (hdet : 0 < H 0 * H 2 - (H 1)^2) :
    ∃ P : PhaseBasis, ∀ j, 0 < P.Q j H := by
  obtain ⟨β,r,hr,h₁,h₂⟩ := positive_center_parameters h₀ hdet
  let t₀ := β + r * (-(5/2) : ℝ)
  let t₁ := β + r * (0 : ℝ)
  let t₂ := β + r * (5/2 : ℝ)
  have h01 : t₀ < t₁ := by dsimp [t₀,t₁]; linarith
  have h12 : t₁ < t₂ := by dsimp [t₁,t₂]; linarith
  have hp := shifted_basis_positive h₀ hr h₁ h₂
    (show (-(5/2) : ℝ) ∈ Ioo (-3 : ℝ) (-2) by norm_num)
    (show (0 : ℝ) ∈ Ioo (-(1/4) : ℝ) (1/4) by norm_num)
    (show (5/2 : ℝ) ∈ Ioo (2 : ℝ) 3 by norm_num)
  let ξ : Fin 3 → Base := ![(1,t₀),(1,t₁),(1,t₂)]
  let Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ :=
    ![basisCoefficient t₀ t₁ t₂, basisCoefficient t₁ t₀ t₂, basisCoefficient t₂ t₀ t₁]
  have hd : ∀ A, ∑ j, Q j A • covectorSquare (ξ j) = A := by
    intro A
    simpa only [Fin.sum_univ_three,ξ,Q,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
      Fin.succ_zero_eq_one] using
      three_slope_decomposition h01.ne (h01.trans h12).ne h12.ne A
  have hn : ∀ j, ξ j ≠ 0 := by
    intro j
    fin_cases j <;> simp [ξ]
  refine ⟨⟨ξ,Q,hd,hn⟩,?_⟩
  intro j
  fin_cases j
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2



theorem exists_positive_metric_phase_neighborhood (g : SmoothMetric M) (p : M) :
    ∃ (P : PhaseBasis) (U : Set M), IsOpen U ∧ p ∈ U ∧
      U ⊆ (coordinateChart p).source ∧
      ∀ q ∈ U, ∀ j, 0 < P.Q j (coordinateMetric g p (coordinateChart p q)) := by
  obtain ⟨P,hP⟩ := PhaseGeometry.positive_tensor_has_basis
    (coordinateMetric_positive_center g p).1 (coordinateMetric_positive_center g p).2
  let V : Set PhaseMean.Tensor := ⋂ j : Fin 3, {A | 0 < P.Q j A}
  have hV : IsOpen V := isOpen_iInter_of_finite (fun j => isOpen_lt continuous_const (P.Q j).continuous)
  have hpV : coordinateMetric g p (coordinateCenter p) ∈ V := mem_iInter.mpr hP
  have hn := (coordinateMetric_continuousAt_center g p).preimage_mem_nhds (hV.mem_nhds hpV)
  obtain ⟨W,hWV,hW,hpW⟩ := mem_nhds_iff.mp hn
  let U : Set M := (coordinateChart p).source ∩ (coordinateChart p) ⁻¹' W
  refine ⟨P,U,(coordinateChart p).isOpen_inter_preimage hW,?_,fun _ h => h.1,?_⟩
  · refine ⟨?_,?_⟩
    · rw [coordinateChart_source]
      exact mem_chart_source Plane p
    · change coordinateChart p p ∈ W
      simpa [coordinateChart_apply,chartCoordinates,coordinateCenter,planeModel] using hpW
  · intro q hq j
    exact mem_iInter.mp (hWV hq.2) j

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]





omit [SecondCountableTopology M] in
theorem exists_finite_tangent_metric_decomposition (g : SmoothMetric M) :
    ∃ (t : Finset M) (P : t → PhaseBasis) (b : t → Fin 3 → M → ℝ),
      (∀ (i : t) j, ContMDiff planeModel 𝓘(ℝ) ∞ (b i j)) ∧
      (∀ (i : t) j, HasCompactSupport (b i j)) ∧
      (∀ (i : t) j, tsupport (b i j) ⊆ (coordinateChart (i : M)).source) ∧
      (∀ (i : t) j q, 0 ≤ b i j q) ∧
      (∀ (i : t) j, ContMDiffOn planeModel 𝓘(ℝ) ∞ (atlasPhase (i : M) ((P i).ξ j))
        (coordinateChart (i : M)).source) ∧
      ∀ (q : M) (v u : TangentSpace planeModel q),
        ∑ i, ∑ j, (b i j q)^2 *
          (scalarDifferential (atlasPhase (i : M) ((P i).ξ j)) q v : ℝ) *
          (scalarDifferential (atlasPhase (i : M) ((P i).ξ j)) q u : ℝ) = g.inner q v u := by
  classical
  choose P U hU hpU hsource hpos using exists_positive_metric_phase_neighborhood g
  obtain ⟨t,χ,hχ,hsupp,hcompact,hnonneg,hsquare⟩ :=
    exists_finite_smooth_square_partition (E := Plane) U hU hpU
  have hsource' (i : t) : tsupport (χ i) ⊆ (coordinateChart (i : M)).source :=
    (hsupp i).trans (hsource i)
  have hpos' (i : t) (q : M) (hq : q ∈ tsupport (χ i)) (j) :
      0 < (P i).Q j (coordinateMetric g (i : M) (coordinateChart (i : M) q)) :=
    hpos i q (hsupp i hq) j
  let b : t → Fin 3 → M → ℝ := fun i j => metricPhaseAmplitude g (i : M) ((P i).Q j) (χ i) 1
  obtain ⟨hbsmooth,hbcompact,hdecomp⟩ := global_metric_phase_decomposition g
    (fun i : t => (i : M)) (fun i : t => P i) χ (fun _ _ => 1)
    hχ hcompact hsource' hsquare (fun _ _ => one_ne_zero) hpos'
  refine ⟨t,(fun i : t => P i),b,hbsmooth,hbcompact,?_,?_,?_,?_⟩
  · intro i j
    exact (metricPhaseAmplitude_tsupport g (i : M) ((P i).Q j) (χ i) 1).trans (hsource' i)
  · intro i j q
    exact mul_nonneg (hnonneg i q) (div_nonneg (Real.sqrt_nonneg _) zero_le_one)
  · intro i j
    exact atlasPhase_smoothOn (i : M) ((P i).ξ j)
  · intro q v u
    simpa only [one_smul] using hdecomp q v u

end ClosedSurfaceR4

end

end OAI
