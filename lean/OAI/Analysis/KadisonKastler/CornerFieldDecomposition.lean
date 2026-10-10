import OAI.Analysis.KadisonKastler.FieldCoordinateCenters
import OAI.Analysis.KadisonKastler.FieldReconstruction

namespace OAI

/-! # Field decomposition on each reducing Hilbert-sum corner -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))

local notation "L" => fun n => Lp (K n) 2 (μ n)

theorem hilbertSumCompression_isometricExtension (n : ℕ) (T : L n →L[ℂ] L n) :
    hilbertSumCompression n (isometricExtension (hilbertSumInclusion (E := L) n) T) = T := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [hilbertSumCompression_apply, hilbertSumInclusion_extension_apply,
    lp.single_apply_self]

theorem cornerOperatorFieldDecomposition
    (A : VonNeumannAlgebra (lp L 2)) (P : ∀ n, X n → VonNeumannAlgebra (K n))
    (hdec : ∀ T ∈ A, ∃ F : ∀ n, X n → K n →L[ℂ] K n,
      (∀ n v, AEStronglyMeasurable (fun x => F n x v) (μ n)) ∧
      (∀ n, ∀ᵐ x ∂μ n, ‖F n x‖ ≤ ‖T‖) ∧ (∀ n, ∀ᵐ x ∂μ n, F n x ∈ P n x) ∧
      ∀ (f : lp L 2) n, T f n =ᵐ[μ n] fun x => F n x (f n x))
    (hcomm : ∀ S ∈ A.commutant, ∃ G : ∀ n, X n → K n →L[ℂ] K n,
      (∀ n, ∀ᵐ x ∂μ n, G n x ∈ (P n x).commutant) ∧
      ∀ (f : lp L 2) n, S f n =ᵐ[μ n] fun x => G n x (f n x))
    (n : ℕ) :
    OperatorFieldDecomposition (μ n) (P n)
      (isometricCornerAlgebra (hilbertSumInclusion (E := L) n) A
        (hilbertSumProjection_mem_of_commutant_fields μ A
          (fun S hS => let ⟨G, _, hG⟩ := hcomm S hS; ⟨G, hG⟩) n)) := by
  let hn := hilbertSumProjection_mem_of_commutant_fields μ A
    (fun S hS => let ⟨G, _, hG⟩ := hcomm S hS; ⟨G, hG⟩) n
  constructor
  · intro T hT
    have hExt : isometricExtension (hilbertSumInclusion (E := L) n) T ∈ A :=
      (mem_isometricCornerAlgebra_iff _ A hn T).mp hT
    obtain ⟨F, hm, hb, hF, ha⟩ := hdec _ hExt
    refine ⟨F n, hm n, ?_, hF n, ?_⟩
    · simpa only [isometricExtension_norm] using hb n
    · have h := hilbertSumCompression_field_action μ _ F ha n
      rwa [hilbertSumCompression_isometricExtension] at h
  · intro F C _ hm hb hF
    let T := l2LinearFieldMap (μ n) F hm C hb
    have hTa : RepresentsOperatorField (μ n) F T :=
      fun f => l2LinearFieldApply_ae (μ n) F hm C hb f
    refine ⟨T, ?_, hTa⟩
    change T ∈ starSubalgebraCommutant
      (rangeCompressionStarHom (hilbertSumInclusion (E := L) n) A.commutant.toStarSubalgebra
        (rangeProjection_commutes_commutant _ A hn)).range
    rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
    rintro _ ⟨S, rfl⟩
    change hilbertSumCompression n S.val * T = T * hilbertSumCompression n S.val
    obtain ⟨G, hG, hSG⟩ := hcomm S.val S.property
    have hSa := hilbertSumCompression_field_action μ S.val G hSG n
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [hSa (T f), hTa f, hTa (hilbertSumCompression n S.val f),
      hSa f, hG n, hF] with x hsf htf hts hsf' hg hf
    change (hilbertSumCompression n S.val (T f)) x = (T (hilbertSumCompression n S.val f)) x
    rw [hsf, htf, hts, hsf']
    exact congrArg (fun R : K n →L[ℂ] K n => R (f x))
      (VonNeumannAlgebra.mem_commutant_iff.mp hg (F x) hf).symm

end

end KadisonKastler

end OAI
