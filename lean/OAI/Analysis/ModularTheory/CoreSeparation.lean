import OAI.Analysis.ModularTheory.ScalarCompression
import OAI.Analysis.ModularRecovery.ErgodicAverages
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

namespace OAI

/-! Constant operators from the original commutant commute with the full
modular core. Their cyclic orbit separates core operators on the scalar
subspace. This is the faithfulness step for the later weight construction;
no trace or semifinite weight is assumed. -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace ENNReal

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ) [Measure.IsAddRightInvariant μ]
  (S : BoundedRecovery.StandardModularData H)

omit [Measure.IsAddRightInvariant μ] in
lemma pointwise_commutant_coefficient (b : H →L[ℂ] H) (hb : b ∈ S.M.commutant)
    (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    Commute (pointwiseLpRepresentation μ b) (modularLpRepresentation μ S.D a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [b.coeFn_compLpL (p := 2) (μ := μ) (modularLpRepresentation μ S.D a f),
    modularLpRepresentation_ae μ S.D a f,
    modularLpRepresentation_ae μ S.D a (pointwiseLpRepresentation μ b f),
    b.coeFn_compLpL (p := 2) (μ := μ) f] with t h₁ h₂ h₃ h₄
  change (b.compLpL 2 μ (modularLpRepresentation μ S.D a f)) t =
    (modularLpRepresentation μ S.D a (b.compLpL 2 μ f)) t
  change (modularLpRepresentation μ S.D a (b.compLpL 2 μ f)) t =
    S.D.unitary (-t) (a (S.D.unitary t ((b.compLpL 2 μ f) t))) at h₃
  rw [h₁, h₂, h₃, h₄]
  have h := (VonNeumannAlgebra.mem_commutant_iff.mp hb)
    (S.sigma (-t) a) (S.sigma_mem (-t) ha)
  have hh := congrArg (fun R : H →L[ℂ] H => R (f t)) h.symm
  simpa only [BoundedRecovery.StandardModularData.sigma, neg_neg, mul_apply_eq_comp] using hh

lemma pointwise_commutant_translate (b : H →L[ℂ] H) (s : ℝ) :
    Commute (pointwiseLpRepresentation μ b)
      (modularLpTranslateEquiv (H := H) μ s : Lp H 2 μ →L[ℂ] Lp H 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [b.coeFn_compLpL (p := 2) (μ := μ) (modularLpTranslate μ s f),
    modularLpTranslate_ae μ s f,
    modularLpTranslate_ae μ s (pointwiseLpRepresentation μ b f),
    (measurePreserving_sub_right μ s).quasiMeasurePreserving.ae
      (b.coeFn_compLpL (p := 2) (μ := μ) f)] with t h₁ h₂ h₃ h₄
  change (b.compLpL 2 μ (modularLpTranslate μ s f)) t =
    (modularLpTranslate μ s (b.compLpL 2 μ f)) t
  change (modularLpTranslate μ s (b.compLpL 2 μ f)) t =
    (b.compLpL 2 μ f) (t - s) at h₃
  rw [h₁, h₂, h₃, h₄]

lemma pointwise_commutant_mem_core_commutant (b : H →L[ℂ] H)
    (hb : b ∈ S.M.commutant) :
    pointwiseLpRepresentation μ b ∈ (modularCrossedProduct μ S).commutant := by
  let R := pointwiseLpRepresentation μ b
  let N : StarSubalgebra ℂ (Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
    StarSubalgebra.centralizer ℂ {R}
  have hgen : modularCoreGenerators μ S ⊆ N := by
    intro T hT
    have h : Commute R T ∧ Commute R (star T) := by
      rcases hT with ⟨a, rfl⟩ | ⟨s, rfl⟩
      · refine ⟨pointwise_commutant_coefficient μ S b hb a a.property, ?_⟩
        rw [← map_star]
        exact pointwise_commutant_coefficient μ S b hb _ (star_mem a.property)
      · refine ⟨pointwise_commutant_translate μ b s, ?_⟩
        rw [LinearIsometryEquiv.star_eq_symm]
        exact pointwise_commutant_translate μ b (-s)
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro g hg
    have hg' : g = R := Set.mem_singleton_iff.mp hg
    subst g
    exact ⟨h.1.eq, by simpa only [star_star] using h.2.star_star.eq⟩
  have halg : algebraicModularCore μ S ≤ N := StarAlgebra.adjoin_le hgen
  rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_commutant,
    modularCrossedProduct_carrier, Set.centralizer_centralizer_centralizer]
  intro T hT
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (halg hT) R (Set.mem_singleton R)).1.symm

/-- A fixed finite-measure indicator as a continuous linear function of its
vector coefficient. -/
def indicatorVectorLinear {s : Set ℝ} (hs : MeasurableSet s) (hμ : μ s ≠ ⊤) :
    H →ₗ[ℂ] Lp H 2 μ where
  toFun := indicatorConstLp 2 hs hμ
  map_add' x y := indicatorConstLp_add.symm
  map_smul' c x := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := c • x),
      indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := x),
      Lp.coeFn_smul c (indicatorConstLp 2 hs hμ x)] with t h₁ h₂ h₃
    change (indicatorConstLp 2 hs hμ (c • x)) t = (c • indicatorConstLp 2 hs hμ x) t
    rw [h₁, h₃]
    change s.indicator (fun _ => c • x) t = c • ((indicatorConstLp 2 hs hμ x) t)
    rw [h₂]
    by_cases ht : t ∈ s <;> simp [ht]

def indicatorVectorCLM {s : Set ℝ} (hs : MeasurableSet s) (hμ : μ s ≠ ⊤) :
    H →L[ℂ] Lp H 2 μ :=
  (indicatorVectorLinear μ hs hμ).mkContinuous (μ.real s ^ (1 / (2 : ℝ))) (fun x => by
    change ‖indicatorConstLp 2 hs hμ x‖ ≤ _
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    exact le_of_eq (mul_comm _ _))

omit [Measure.IsAddRightInvariant μ] in
lemma pointwise_indicatorVector (b : H →L[ℂ] H) {s : Set ℝ}
    (hs : MeasurableSet s) (hμ : μ s ≠ ⊤) (x : H) :
    pointwiseLpRepresentation μ b (indicatorConstLp 2 hs hμ x) =
      indicatorConstLp 2 hs hμ (b x) := by
  apply Lp.ext
  filter_upwards [b.coeFn_compLpL (p := 2) (μ := μ) (indicatorConstLp 2 hs hμ x),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := x),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := b x)] with t h₁ h₂ h₃
  change (b.compLpL 2 μ (indicatorConstLp 2 hs hμ x)) t = _
  rw [h₁, h₂, h₃]
  by_cases ht : t ∈ s <;> simp [ht]

omit [Measure.IsAddRightInvariant μ] in
lemma scalarInclusion_indicator {s : Set ℝ} (hs : MeasurableSet s) (hμ : μ s ≠ ⊤) :
    modularScalarInclusion μ S (indicatorConstLp 2 hs hμ (1 : ℂ)) =
      indicatorConstLp 2 hs hμ S.xi := by
  apply Lp.ext
  filter_upwards [modularScalarInclusion_ae μ S (indicatorConstLp 2 hs hμ (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := S.xi)] with t h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  by_cases ht : t ∈ s <;> simp [ht]

/-- Vanishing on the scalar subspace detects an operator in the actual core. -/
theorem modularCore_eq_zero_of_scalarInclusion
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (hT : T ∈ modularCrossedProduct μ S)
    (hz : ∀ f : Lp ℂ 2 μ, T (modularScalarInclusion μ S f) = 0) : T = 0 := by
  have hind {s : Set ℝ} (hs : MeasurableSet s) (hμ : μ s ≠ ⊤) (x : H) :
      T (indicatorConstLp 2 hs hμ x) = 0 := by
    have hc := BoundedRecovery.commutant_cyclic S.M S.xi S.separating
    refine hc.induction ?_ ?_ x
    · rintro x ⟨b, hb, rfl⟩
      have hcomm := (VonNeumannAlgebra.mem_commutant_iff.mp
        (pointwise_commutant_mem_core_commutant μ S b hb)) T hT
      have h := congrArg (fun R : Lp H 2 μ →L[ℂ] Lp H 2 μ =>
        R (indicatorConstLp 2 hs hμ S.xi)) hcomm
      rw [mul_apply_eq_comp, mul_apply_eq_comp, pointwise_indicatorVector] at h
      rw [h, ← scalarInclusion_indicator μ S hs hμ, hz, map_zero]
    · exact isClosed_eq (T.continuous.comp (indicatorVectorCLM μ hs hμ).continuous)
        continuous_const
  apply ContinuousLinearMap.ext
  intro f
  change T f = 0
  refine (Lp.simpleFunc.dense (E := H) (μ := μ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).induction
    ?_ (isClosed_eq T.continuous continuous_const) f
  intro g hg
  lift g to Lp.simpleFunc H 2 μ using hg
  induction g using Lp.simpleFunc.induction (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) with
  | indicatorConst x hs hμ => exact hind hs hμ.ne x
  | add hf hg hfg h₁ h₂ =>
      change T (_ + _) = 0
      rw [map_add, h₁, h₂, add_zero]

/-- The scalar compression detects squares of elements of the core. -/
theorem modularScalarCompression_faithful_square
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (hT : T ∈ modularCrossedProduct μ S)
    (hz : modularScalarCompression μ S (star T * T) = 0) : T = 0 := by
  apply modularCore_eq_zero_of_scalarInclusion μ S T hT
  intro f
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have h := congrArg (fun R : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ => inner ℂ f (R f)) hz
  change inner ℂ f (modularScalarExtraction μ S
    (star T (T (modularScalarInclusion μ S f)))) = inner ℂ f 0 at h
  rw [modularScalarExtraction_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_zero_right] at h
  exact h

end WeakPureInfiniteness

end

end OAI
