import Mathlib

namespace OAI

noncomputable section

open scoped ComplexConjugate InnerProductSpace BoundedContinuousFunction

namespace UniversalStrongKK

section OperatorMean

variable {G H : Type*} [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure ScalarMean (G : Type*) [TopologicalSpace G] where
  map : (G →ᵇ ℂ) →L[ℂ] ℂ
  norm_map_le : ‖map‖ ≤ 1
  map_one : map 1 = 1
  map_star : ∀ f, map (star f) = star (map f)
  positive : ∀ f, (∀ g, 0 ≤ (f g).re) → 0 ≤ (map f).re

variable (m : ScalarMean G)

noncomputable def operatorCoefficient (T : G →ᵇ (H →L[ℂ] H)) (x y : H) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun g => ⟪T g x, y⟫_ℂ)
    (by fun_prop)
    (‖T‖ * ‖x‖ * ‖y‖)
    (fun g => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        ((T g).le_opNorm x |>.trans
          (mul_le_mul_of_nonneg_right (T.norm_coe_le_norm g) (norm_nonneg x)))
        (norm_nonneg y)))

@[simp] theorem operatorCoefficient_apply (T : G →ᵇ (H →L[ℂ] H)) (x y : H) (g : G) :
    operatorCoefficient T x y g = ⟪T g x, y⟫_ℂ := rfl

theorem norm_operatorCoefficient_le (T : G →ᵇ (H →L[ℂ] H)) (x y : H) :
    ‖operatorCoefficient T x y‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
  apply BoundedContinuousFunction.norm_le (by positivity) |>.mpr
  intro g
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      ((T g).le_opNorm x |>.trans
        (mul_le_mul_of_nonneg_right (T.norm_coe_le_norm g) (norm_nonneg x)))
      (norm_nonneg y))

noncomputable def meanBilinear (T : G →ᵇ (H →L[ℂ] H)) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    { toFun := fun x =>
        { toFun := fun y => m.map (operatorCoefficient T x y)
          map_add' := fun y z => by
            rw [show operatorCoefficient T x (y + z) =
              operatorCoefficient T x y + operatorCoefficient T x z by ext; simp]
            exact map_add m.map _ _
          map_smul' := fun c y => by
            rw [show operatorCoefficient T x (c • y) = c • operatorCoefficient T x y by
              ext; simp]
            exact map_smul m.map c _ }
      map_add' := fun x z => by
        ext y
        change m.map (operatorCoefficient T (x + z) y) = _
        rw [show operatorCoefficient T (x + z) y =
          operatorCoefficient T x y + operatorCoefficient T z y by
          ext; simp]
        exact map_add m.map _ _
      map_smul' := fun c x => by
        ext y
        change m.map (operatorCoefficient T (c • x) y) = _
        rw [show operatorCoefficient T (c • x) y = star c • operatorCoefficient T x y by
          ext; simp [mul_comm]]
        exact map_smul m.map (star c) _ }
    ‖T‖ (fun x y => by
      calc
        _ ≤ ‖m.map‖ * ‖operatorCoefficient T x y‖ := m.map.le_opNorm _
        _ ≤ ‖operatorCoefficient T x y‖ := by
          nlinarith [m.norm_map_le, norm_nonneg (operatorCoefficient T x y)]
        _ ≤ _ := norm_operatorCoefficient_le T x y)

variable [CompleteSpace H]

noncomputable def operatorMean (T : G →ᵇ (H →L[ℂ] H)) : H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin (meanBilinear m T)

@[simp] theorem inner_operatorMean (T : G →ᵇ (H →L[ℂ] H)) (x y : H) :
    ⟪operatorMean m T x, y⟫_ℂ = m.map (operatorCoefficient T x y) :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _

theorem norm_operatorMean_le (T : G →ᵇ (H →L[ℂ] H)) : ‖operatorMean m T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hb (y : H) : ‖⟪operatorMean m T x, y⟫_ℂ‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
    rw [inner_operatorMean]
    calc
      _ ≤ ‖m.map‖ * ‖operatorCoefficient T x y‖ := m.map.le_opNorm _
      _ ≤ ‖operatorCoefficient T x y‖ := by
        nlinarith [m.norm_map_le, norm_nonneg (operatorCoefficient T x y)]
      _ ≤ _ := norm_operatorCoefficient_le T x y
  have hs := hb (operatorMean m T x)
  rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq] at hs
  have hn := norm_nonneg (operatorMean m T x)
  have ht : 0 ≤ ‖T‖ * ‖x‖ := by positivity
  nlinarith

end OperatorMean

end UniversalStrongKK

open scoped Topology

namespace UniversalStrongKK

section UltraMean

variable {I : Type*} [TopologicalSpace I]

theorem exists_ultrafilter_mean (u : Ultrafilter I) :
    ∃ m : ScalarMean I, ∀ f : I →ᵇ ℂ,
      Filter.Tendsto (fun i => f i) (u : Filter I) (𝓝 (m.map f)) := by
  let q (i : I) : WeakDual ℂ (I →ᵇ ℂ) :=
    StrongDual.toWeakDual (BoundedContinuousFunction.evalCLM ℂ i : StrongDual ℂ (I →ᵇ ℂ))
  have hqn (i : I) : ‖(BoundedContinuousFunction.evalCLM ℂ i : StrongDual ℂ (I →ᵇ ℂ))‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    simpa using f.norm_coe_le_norm i
  obtain ⟨m, hm, ht⟩ := (WeakDual.isCompact_closedBall
    (0 : StrongDual ℂ (I →ᵇ ℂ)) 1).ultrafilter_le_nhds (u.map q) (by
      rw [Ultrafilter.coe_map, Filter.map_le_iff_le_comap, Filter.comap_principal]
      apply Filter.le_principal_iff.mpr
      exact Filter.Eventually.of_forall (fun i => by
        simpa [q, Metric.mem_closedBall, dist_zero_right] using hqn i))
  have hlim (f : I →ᵇ ℂ) : Filter.Tendsto (fun i => f i) ↑u (𝓝 (m f)) :=
    (WeakDual.eval_continuous f).continuousAt.tendsto.comp
      (show Filter.Tendsto q ↑u (𝓝 m) from ht)
  refine ⟨⟨m.toStrongDual, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa [Metric.mem_closedBall, dist_zero_right] using hm
  · exact tendsto_nhds_unique (hlim 1) tendsto_const_nhds
  · intro f
    exact tendsto_nhds_unique (hlim (star f)) (by
      simpa only [WeakDual.toStrongDual_apply, BoundedContinuousFunction.star_apply] using (hlim f).star)
  · intro f hf
    exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp (hlim f))
      (Filter.Eventually.of_forall hf)
  · exact hlim

noncomputable def ultrafilterMean (u : Ultrafilter I) : ScalarMean I :=
  (exists_ultrafilter_mean u).choose

theorem tendsto_ultrafilterMean (u : Ultrafilter I) (f : I →ᵇ ℂ) :
    Filter.Tendsto (fun i => f i) (u : Filter I) (𝓝 ((ultrafilterMean u).map f)) :=
  (exists_ultrafilter_mean u).choose_spec f

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tendsto_operatorMean (u : Ultrafilter I) (T : I →ᵇ (H →L[ℂ] H)) :
    Filter.Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (T i)) (u : Filter I)
      (𝓝 (ContinuousLinearMapWOT.ofCLM (operatorMean (ultrafilterMean u) T))) := by
  apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
  intro x y
  have h := (tendsto_ultrafilterMean u (operatorCoefficient T x y)).star
  simpa only [operatorCoefficient_apply, ← inner_operatorMean, Complex.star_def, inner_conj_symm, ContinuousLinearMapWOT.ofCLM_apply] using h

theorem norm_le_of_wot_tendsto {J : Type*} {l : Filter J} [l.NeBot]
    {T : J → (H →L[ℂ] H)} {A : H →L[ℂ] H} {r : ℝ} (hr : 0 ≤ r)
    (hT : Filter.Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (T i)) l (𝓝 (ContinuousLinearMapWOT.ofCLM A)))
    (hb : ∀ᶠ i in l, ‖T i‖ ≤ r) : ‖A‖ ≤ r := by
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro x
  have hh (y : H) : ‖⟪y, A x⟫_ℂ‖ ≤ r * ‖x‖ * ‖y‖ := by
    apply le_of_tendsto
      ((ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp hT x y).norm)
    filter_upwards [hb] with i hi
    calc
      _ ≤ ‖y‖ * ‖T i x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (r * ‖x‖) := by
        gcongr
        exact ((T i).le_opNorm x).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg x))
      _ = _ := by ring
  have h := hh (A x)
  rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq] at h
  have hx : 0 ≤ r * ‖x‖ := by positivity
  nlinarith [norm_nonneg (A x)]

theorem mem_of_wot_tendsto (M : VonNeumannAlgebra H) {J : Type*} {l : Filter J} [l.NeBot]
    {T : J → (H →L[ℂ] H)} {A : H →L[ℂ] H}
    (hT : Filter.Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (T i)) l (𝓝 (ContinuousLinearMapWOT.ofCLM A)))
    (hb : ∀ᶠ i in l, T i ∈ M) : A ∈ M := by
  rw [← M.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro B hB
  ext x
  apply ext_inner_left ℂ
  intro y
  have hl := ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp hT (B x) y
  have hr := ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp hT x (star B y)
  have he : (fun i => ⟪y, T i (B x)⟫_ℂ) =ᶠ[l]
      (fun i => ⟪star B y, T i x⟫_ℂ) := by
    filter_upwards [hb] with i hi
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp hB (T i) hi
    exact congrArg (fun C : H →L[ℂ] H => ⟪y, C x⟫_ℂ) hc
  have hh := tendsto_nhds_unique hl (hr.congr' he.symm)
  simpa only [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left, mul_apply_eq_comp,
    ContinuousLinearMapWOT.ofCLM_apply] using hh.symm

end UltraMean

end UniversalStrongKK

namespace UniversalStrongKK

open scoped InnerProductSpace

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positive_of_wot_tendsto {I : Type*} {l : Filter I} [l.NeBot]
    {T : I → (H →L[ℂ] H)} {A : H →L[ℂ] H}
    (hT : Filter.Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (T i)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM A)))
    (hp : ∀ᶠ i in l, (T i).IsPositive) : A.IsPositive := by
  have hh := ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp hT
  constructor
  · intro x y
    have hl := (hh x y).star
    simp only [Complex.star_def, inner_conj_symm] at hl
    have he : (fun i => ⟪T i x, y⟫_ℂ) =ᶠ[l] (fun i => ⟪x, T i y⟫_ℂ) := by
      filter_upwards [hp] with i hi
      exact hi.inner_left_eq_inner_right x y
    exact tendsto_nhds_unique hl ((hh y x).congr' he.symm)
  · intro x
    change 0 ≤ RCLike.re (⟪A x, x⟫_ℂ)
    rw [inner_re_symm]
    apply ge_of_tendsto ((Complex.continuous_re.tendsto _).comp (hh x x))
    filter_upwards [hp] with i hi
    exact hi.re_inner_nonneg_right x

end UniversalStrongKK
end

end OAI
