import OAI.Analysis.TracialSplitting.StateExtension
import OAI.Analysis.FactorGeneration.TraceTransport
import OAI.Analysis.KadisonKastler.InjectivityTransport

namespace OAI

/-! # An ambient extension of the finite factor trace representation

Extend the scalar trace state by Hahn–Banach, form its GNS representation,
and compress to the original trace Hilbert space. This supplies the
contractive ambient map required to transport finite tracial injectivity.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance traceExtensionOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance traceExtensionPreorder : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance traceExtensionLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance traceExtensionStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

variable (hfactor : ∀ c : Algebra M,
  (∀ a : Algebra M, a * c = c * a) → ∃ z : ℂ, c = z • (1 : Algebra M))
  (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
    ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hfinite : ∀ a : Algebra M, star a * a = 1 → a * star a = 1)
  (hunit : (1 : Algebra M) ≠ 0)

local notation "τ" => traceFreeTrace hfactor hdiff hfinite hunit
local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

local instance traceExtensionPreNorm : NormedAddCommGroup E :=
  traceFreePreHilbertNormedAddCommGroup hfactor hdiff hfinite hunit
local instance traceExtensionPreInner : InnerProductSpace ℂ E :=
  traceFreePreHilbertInnerProductSpace hfactor hdiff hfinite hunit
local instance traceExtensionHilbertNorm : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion E))
local instance traceExtensionHilbertInner : InnerProductSpace ℂ K :=
  inferInstanceAs (InnerProductSpace ℂ (UniformSpace.Completion E))

/-- The constructed trace as a positive linear functional. -/
def traceFreePositiveFunctional : Algebra M →ₚ[ℂ] ℂ where
  toLinearMap := (τ).toLinearMap
  monotone' := by
    intro a b hab
    have hp := (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.1
      (b - a) (sub_nonneg.mpr hab)
    have hs := (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.1 (b - a)
    rw [(sub_nonneg.mpr hab).isSelfAdjoint.star_eq] at hs
    have hi := congrArg Complex.im hs
    simp only [Complex.star_def, Complex.conj_im] at hi
    have hn : 0 ≤ τ (b - a) := Complex.nonneg_iff.mpr ⟨hp, by linarith⟩
    change τ a ≤ τ b
    exact sub_nonneg.mp (by simpa only [map_sub] using hn)

/-- Only the scalar state extension is used; it carries no operator-algebra conclusion. -/
theorem exists_traceFree_state_extension :
    ∃ σ : (H →L[ℂ] H) →ₚ[ℂ] ℂ, σ 1 = 1 ∧
      ∀ a : Algebra M, σ a.val = τ a := by
  obtain ⟨σ,hσ,hσa⟩ := CurrentMain.state_extension M.toStarSubalgebra.subtype
    Subtype.val_injective (traceFreePositiveFunctional hfactor hdiff hfinite hunit)
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.1
  exact ⟨σ,hσ,hσa⟩

variable (σ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

/-- The algebraic trace Hilbert space embeds in the extended state's GNS space. -/
def traceStatePreEmbedding : E →ₗ[ℂ] σ.GNS where
  toFun x := (σ.toPreGNS (((copy).symm x).val) : σ.GNS)
  map_add' x y := by simp only [map_add, AddMemClass.coe_add, UniformSpace.Completion.coe_add]
  map_smul' c x := by
    simp only [map_smul, SetLike.val_smul, UniformSpace.Completion.coe_smul, RingHom.id_apply]

theorem traceStatePreEmbedding_norm
    (hσ : ∀ a : Algebra M, σ a.val =
      traceFreeTrace (M := M) hfactor hdiff hfinite hunit a) (x : E) :
    ‖traceStatePreEmbedding hfactor hdiff hfinite hunit σ x‖ = ‖ι x‖ := by
  change ‖(σ.toPreGNS (((copy).symm x).val) : σ.GNS)‖ = ‖ι x‖
  rw [UniformSpace.Completion.norm_coe, PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.ofPreGNS_toPreGNS]
  change Real.sqrt (σ ((star ((copy).symm x) * (copy).symm x).val)).re = ‖ι x‖
  have htrace := congrArg (fun z : ℂ => Real.sqrt z.re)
    (hσ (star ((copy).symm x) * (copy).symm x))
  have hnorm : ‖x‖ = Real.sqrt (τ (star ((copy).symm x) * (copy).symm x)).re :=
    norm_eq_sqrt_re_inner (𝕜 := ℂ) x
  exact htrace.trans (hnorm.symm.trans ((ι).norm_map x).symm)

/-- Completion of the trace-state isometry. -/
def traceStateEmbedding (hσ : ∀ a : Algebra M, σ a.val =
      traceFreeTrace (M := M) hfactor hdiff hfinite hunit a) : K →ₗᵢ[ℂ] σ.GNS :=
  (traceStatePreEmbedding hfactor hdiff hfinite hunit σ).extendOfIsometry
    (e := (ι).toLinearMap) (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit)
    (traceStatePreEmbedding_norm hfactor hdiff hfinite hunit σ hσ)

@[simp] theorem traceStateEmbedding_inclusion
    (hσ : ∀ a : Algebra M, σ a.val =
      traceFreeTrace (M := M) hfactor hdiff hfinite hunit a) (x : E) :
    traceStateEmbedding hfactor hdiff hfinite hunit σ hσ (ι x) =
      (σ.toPreGNS (((copy).symm x).val) : σ.GNS) :=
  LinearMap.extendOfIsometry_eq _ _ _ x

/-- The extended state's representation agrees with the trace representation on its subspace. -/
theorem traceStateEmbedding_intertwines
    (hσ : ∀ a : Algebra M, σ a.val =
      traceFreeTrace (M := M) hfactor hdiff hfinite hunit a) (a : Algebra M) (x : K) :
    σ.gnsStarAlgHom a.val (traceStateEmbedding hfactor hdiff hfinite hunit σ hσ x) =
      traceStateEmbedding hfactor hdiff hfinite hunit σ hσ (π a x) := by
  let J := traceStateEmbedding hfactor hdiff hfinite hunit σ hσ
  refine (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit).induction_on x
    (isClosed_eq ((σ.gnsStarAlgHom a.val).continuous.comp J.continuous)
      (J.continuous.comp (π a).continuous)) ?_
  intro y
  obtain ⟨y,rfl⟩ := (copy).surjective y
  have hl := traceFreeHilbertAction_inclusion hfactor hdiff hfinite hunit a y
  change σ.gnsStarAlgHom a.val
    (traceStateEmbedding hfactor hdiff hfinite hunit σ hσ (ι (copy y))) =
    traceStateEmbedding hfactor hdiff hfinite hunit σ hσ (π a (ι (copy y)))
  rw [hl, traceStateEmbedding_inclusion, traceStateEmbedding_inclusion]
  change σ.gnsNonUnitalStarAlgHom a.val (σ.toPreGNS (((copy).symm y).val) : σ.GNS) = _
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  rfl

/-- Compress the ambient GNS representation to the canonical trace space. -/
def traceFreeAmbientExtension (hσ : ∀ a : Algebra M, σ a.val =
      traceFreeTrace (M := M) hfactor hdiff hfinite hunit a) : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K) := by
  let j : K →L[ℂ] σ.GNS := (traceStateEmbedding hfactor hdiff hfinite hunit σ hσ).toContinuousLinearMap
  exact {
    toFun T := j.adjoint.comp ((σ.gnsStarAlgHom T).comp j)
    map_add' S T := by
      ext x
      simp only [map_add, ContinuousLinearMap.comp_apply, add_apply]
    map_smul' c T := by
      ext x
      change j.adjoint ((σ.gnsStarAlgHom (c • T)) (j x)) =
        c • j.adjoint ((σ.gnsStarAlgHom T) (j x))
      rw [map_smul, smul_apply, map_smul] }

theorem traceFreeAmbientExtension_norm
    (hσ : ∀ a : Algebra M, σ a.val =
      traceFreeTrace (M := M) hfactor hdiff hfinite hunit a) (T : H →L[ℂ] H) :
    ‖traceFreeAmbientExtension hfactor hdiff hfinite hunit σ hσ T‖ ≤ ‖T‖ := by
  let J := traceStateEmbedding hfactor hdiff hfinite hunit σ hσ
  let j := J.toContinuousLinearMap
  have hj : ‖j‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp only [j, LinearIsometry.coe_toContinuousLinearMap, J.norm_map, one_mul]
    exact le_rfl
  have hj' : ‖j.adjoint‖ ≤ 1 := by simpa only [LinearIsometryEquiv.norm_map] using hj
  have hπ : ‖σ.gnsStarAlgHom T‖ ≤ ‖T‖ := NonUnitalStarAlgHom.norm_apply_le σ.gnsStarAlgHom T
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  change ‖j.adjoint (σ.gnsStarAlgHom T (J x))‖ ≤ ‖T‖ * ‖x‖
  calc
    _ ≤ ‖σ.gnsStarAlgHom T (J x)‖ := by
      simpa only [one_mul] using j.adjoint.le_of_opNorm_le hj' _
    _ ≤ ‖σ.gnsStarAlgHom T‖ * ‖J x‖ := (σ.gnsStarAlgHom T).le_opNorm _
    _ ≤ ‖T‖ * ‖x‖ := by
      rw [J.norm_map]
      exact mul_le_mul_of_nonneg_right hπ (norm_nonneg x)

theorem traceFreeAmbientExtension_agrees
    (hσ : ∀ a : Algebra M, σ a.val =
      traceFreeTrace (M := M) hfactor hdiff hfinite hunit a) (a : Algebra M) :
    traceFreeAmbientExtension hfactor hdiff hfinite hunit σ hσ a.val = π a := by
  ext x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((traceStateEmbedding hfactor hdiff hfinite hunit σ hσ).toContinuousLinearMap.adjoint
    (σ.gnsStarAlgHom a.val (traceStateEmbedding hfactor hdiff hfinite hunit σ hσ x))) = _
  rw [ContinuousLinearMap.adjoint_inner_right,
    traceStateEmbedding_intertwines hfactor hdiff hfinite hunit σ hσ]
  exact (traceStateEmbedding hfactor hdiff hfinite hunit σ hσ).inner_map_map y (π a x)

/-- An actual contractive ambient extension of the trace representation. -/
theorem exists_traceFreeAmbientExtension :
    ∃ R : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K),
      (∀ T, ‖R T‖ ≤ ‖T‖) ∧ ∀ a : Algebra M, R a.val = π a := by
  obtain ⟨σ,_hσ1,hσ⟩ := exists_traceFree_state_extension hfactor hdiff hfinite hunit
  exact ⟨traceFreeAmbientExtension hfactor hdiff hfinite hunit σ hσ,
    traceFreeAmbientExtension_norm hfactor hdiff hfinite hunit σ hσ,
    traceFreeAmbientExtension_agrees hfactor hdiff hfinite hunit σ hσ⟩

end

end KadisonKastler

end OAI
