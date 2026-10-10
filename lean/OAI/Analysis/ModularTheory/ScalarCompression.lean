import OAI.Analysis.ModularTheory.RightTranslation
import OAI.Analysis.ModularRecovery.TomitaResolvent
import OAI.Analysis.OperatorAlgebra.FiniteHilbertCompression

namespace OAI

/-! Compression of the concrete modular representation to scalar functions
times the distinguished vector. This constructs the compression and its
generator formulas. A trace on the core is not assumed here. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ) (S : BoundedRecovery.StandardModularData H)

def modularScalarInclusion : Lp ℂ 2 μ →L[ℂ] Lp H 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℂ S.xi).compLpL 2 μ

def modularScalarExtraction : Lp H 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (innerSL ℂ S.xi).compLpL 2 μ

lemma modularScalarInclusion_ae (f : Lp ℂ 2 μ) :
    modularScalarInclusion μ S f =ᵐ[μ] fun t => f t • S.xi :=
  (ContinuousLinearMap.toSpanSingleton ℂ S.xi).coeFn_compLpL f

lemma modularScalarExtraction_ae (f : Lp H 2 μ) :
    modularScalarExtraction μ S f =ᵐ[μ] fun t => inner ℂ S.xi (f t) :=
  (innerSL ℂ S.xi).coeFn_compLpL f

lemma modularScalarInclusion_norm (f : Lp ℂ 2 μ) :
    ‖modularScalarInclusion μ S f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
    (Lp.aestronglyMeasurable _)
  filter_upwards [modularScalarInclusion_ae μ S f] with t ht
  rw [ht, norm_smul, S.norm_xi, mul_one]

def modularScalarIsometry : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp H 2 μ where
  toLinearMap := (modularScalarInclusion μ S).toLinearMap
  norm_map' := modularScalarInclusion_norm μ S

lemma modularScalarExtraction_adjoint :
    modularScalarExtraction μ S = (modularScalarInclusion μ S).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  simp only [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [modularScalarExtraction_ae μ S f,
    modularScalarInclusion_ae μ S g] with t hf hg
  rw [hf, hg]
  simp only [inner_smul_right, RCLike.inner_apply, inner_conj_symm, mul_comm]

lemma modularScalarExtraction_inclusion (f : Lp ℂ 2 μ) :
    modularScalarExtraction μ S (modularScalarInclusion μ S f) = f := by
  apply Lp.ext
  filter_upwards [modularScalarExtraction_ae μ S (modularScalarInclusion μ S f),
    modularScalarInclusion_ae μ S f] with t he hi
  rw [he, hi, inner_smul_right, inner_self_eq_norm_sq_to_K, S.norm_xi]
  simp

def modularScalarCompression (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (modularScalarExtraction μ S).comp (T.comp (modularScalarInclusion μ S))

@[simp] lemma modularScalarCompression_one :
    modularScalarCompression μ S 1 = 1 := by
  apply ContinuousLinearMap.ext
  exact modularScalarExtraction_inclusion μ S

def modularScalarCompressionMap : (Lp H 2 μ →L[ℂ] Lp H 2 μ) →L[ℂ]
    (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  hilbertCompression (NonUnitalStarAlgHom.id ℂ (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (modularScalarInclusion μ S)

@[simp] lemma modularScalarCompressionMap_apply (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) :
    modularScalarCompressionMap μ S T = modularScalarCompression μ S T := by
  change (modularScalarInclusion μ S).adjoint.comp (T.comp (modularScalarInclusion μ S)) = _
  rw [← modularScalarExtraction_adjoint]
  rfl

theorem modularScalarCompressionMap_cp : CompletelyPositive (modularScalarCompressionMap μ S) :=
  hilbertCompression_cp _ _

theorem modularScalarCompressionMap_contractive : ‖modularScalarCompressionMap μ S‖ ≤ 1 := by
  have hJ : ‖modularScalarInclusion μ S‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
      rw [modularScalarInclusion_norm, one_mul])
  exact (hilbertCompression_norm_le _ _).trans
    ((mul_le_mul hJ hJ (norm_nonneg (modularScalarInclusion μ S)) zero_le_one).trans_eq (one_mul 1))

lemma modularScalarCompression_coefficient (T : H →L[ℂ] H) :
    modularScalarCompression μ S (modularLpRepresentation μ S.D T) =
      inner ℂ S.xi (T S.xi) • (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [modularScalarExtraction_ae μ S
      (modularLpRepresentation μ S.D T (modularScalarInclusion μ S f)),
    modularLpRepresentation_ae μ S.D T (modularScalarInclusion μ S f),
    modularScalarInclusion_ae μ S f,
    Lp.coeFn_smul (inner ℂ S.xi (T S.xi)) f] with t he hT hi hc
  change (modularScalarExtraction μ S
    (modularLpRepresentation μ S.D T (modularScalarInclusion μ S f))) t =
      ((inner ℂ S.xi (T S.xi)) • f) t
  rw [he, hT, hi, map_smul, S.fixes_xi, map_smul, map_smul, hc]
  rw [inner_smul_right, ← ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.star_eq_adjoint, S.D.unitary_star, neg_neg, S.fixes_xi]
  exact mul_comm _ _

variable [Measure.IsAddRightInvariant μ]

lemma modularScalarInclusion_translate (s : ℝ) (f : Lp ℂ 2 μ) :
    modularScalarInclusion μ S (modularLpTranslate μ s f) =
      modularLpTranslate μ s (modularScalarInclusion μ S f) := by
  apply Lp.ext
  filter_upwards [modularScalarInclusion_ae μ S (modularLpTranslate μ s f),
    modularLpTranslate_ae μ s f,
    modularLpTranslate_ae μ s (modularScalarInclusion μ S f),
    (measurePreserving_sub_right μ s).quasiMeasurePreserving.ae
      (modularScalarInclusion_ae μ S f)] with t hi ht ht' hi'
  rw [hi, ht, ht', hi']

lemma modularScalarInclusion_right (s : ℝ) (f : Lp ℂ 2 μ) :
    modularRightTranslation μ S.D s (modularScalarInclusion μ S f) =
      modularScalarInclusion μ S (modularLpTranslate μ (-s) f) := by
  apply Lp.ext
  filter_upwards [modularRightTranslation_ae μ S.D s (modularScalarInclusion μ S f),
    (measurePreserving_add_right μ s).quasiMeasurePreserving.ae
      (modularScalarInclusion_ae μ S f),
    modularScalarInclusion_ae μ S (modularLpTranslate μ (-s) f),
    modularLpTranslate_ae μ (-s) f] with t hr hi hi' ht
  rw [hr, hi, hi', ht, sub_neg_eq_add, map_smul, S.fixes_xi]

lemma modularScalarCompression_translate (s : ℝ) :
    modularScalarCompression μ S
      (modularLpTranslateEquiv (H := H) μ s : Lp H 2 μ →L[ℂ] Lp H 2 μ) =
      (modularLpTranslateEquiv (H := ℂ) μ s : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  change modularScalarExtraction μ S
    (modularLpTranslate μ s (modularScalarInclusion μ S f)) = _
  rw [← modularScalarInclusion_translate, modularScalarExtraction_inclusion]
  rfl

private lemma scalarExtraction_right (s : ℝ) (f : Lp H 2 μ) :
    modularScalarExtraction μ S (modularRightTranslation μ S.D (-s) f) =
      modularLpTranslate μ s (modularScalarExtraction μ S f) := by
  have h : (modularRightTranslation μ S.D s).comp (modularScalarInclusion μ S) =
      (modularScalarInclusion μ S).comp
        (modularLpTranslateEquiv (H := ℂ) μ (-s) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
    apply ContinuousLinearMap.ext
    exact modularScalarInclusion_right μ S s
  have ha := congrArg ContinuousLinearMap.adjoint h
  have ht : (modularLpTranslateEquiv (H := ℂ) μ (-s) :
      Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ).adjoint =
        (modularLpTranslateEquiv (H := ℂ) μ s : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
    rw [LinearIsometryEquiv.adjoint_eq_symm]
    apply ContinuousLinearMap.ext
    intro g
    change modularLpTranslate μ (- -s) g = modularLpTranslate μ s g
    rw [neg_neg]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ← modularScalarExtraction_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
    modularRightTranslation_star, ht] at ha
  exact congrArg (fun F : Lp H 2 μ →L[ℂ] Lp ℂ 2 μ => F f) ha

/-- Compression of every core operator commutes with the scalar regular
representation. This is a statement about the whole von Neumann closure. -/
theorem modularScalarCompression_commutes (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : T ∈ modularCrossedProduct μ S) (s : ℝ) :
    Commute (modularScalarCompression μ S T)
      (modularLpTranslateEquiv (H := ℂ) μ s : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp
    (modularRightTranslation_mem_commutant μ S (-s)) T hT
  apply ContinuousLinearMap.ext
  intro f
  have hJ : modularScalarInclusion μ S (modularLpTranslate μ s f) =
      modularRightTranslation μ S.D (-s) (modularScalarInclusion μ S f) := by
    simpa only [neg_neg] using (modularScalarInclusion_right μ S (-s) f).symm
  change modularScalarExtraction μ S
      (T (modularScalarInclusion μ S (modularLpTranslate μ s f))) =
    modularLpTranslate μ s (modularScalarExtraction μ S (T (modularScalarInclusion μ S f)))
  rw [hJ]
  have he := congrArg (fun F : Lp H 2 μ →L[ℂ] Lp H 2 μ => F (modularScalarInclusion μ S f)) hc
  change T (modularRightTranslation μ S.D (-s) (modularScalarInclusion μ S f)) =
    modularRightTranslation μ S.D (-s) (T (modularScalarInclusion μ S f)) at he
  rw [he, scalarExtraction_right]

end WeakPureInfiniteness

end

end OAI
