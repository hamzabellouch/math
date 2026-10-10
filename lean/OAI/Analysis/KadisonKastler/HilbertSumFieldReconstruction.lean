import OAI.Analysis.KadisonKastler.FieldReconstruction
import OAI.Analysis.KadisonKastler.HilbertSumFieldAction

namespace OAI

/-! # Simultaneous bounded-field reconstruction on the rank strata

The commutant test works directly on the Hilbert sum. In particular it does
not assume, in advance, that the coordinate projections belong to the algebra.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

section Norm

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem l2LinearFieldMap_norm_le (μ : Measure X) (F : X → H →L[ℂ] H)
    (hm : ∀ v, AEStronglyMeasurable (fun x => F x v) μ)
    (C : ℝ) (hC : 0 ≤ C) (hn : ∀ᵐ x ∂μ, ‖F x‖ ≤ C) :
    ‖l2LinearFieldMap μ F hm C hn‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [l2LinearFieldApply_ae μ F hm C hn f, hn] with x hx hb
  change ‖l2LinearFieldApply μ F hm C hn f x‖ ≤ _
  rw [hx]
  exact ((F x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

end Norm

variable {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))

local notation "L" => fun n => Lp (K n) 2 (μ n)

theorem reconstruct_hilbertSum_field_of_commutant_fields
    (P : ∀ n, X n → VonNeumannAlgebra (K n))
    (A : VonNeumannAlgebra (lp L 2))
    (hcomm : ∀ S ∈ A.commutant, ∃ G : ∀ n, X n → K n →L[ℂ] K n,
      (∀ n, ∀ᵐ x ∂μ n, G n x ∈ (P n x).commutant) ∧
      ∀ (f : lp L 2) n, S f n =ᵐ[μ n] fun x => G n x (f n x))
    (F : ∀ n, X n → K n →L[ℂ] K n) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ n v, AEStronglyMeasurable (fun x => F n x v) (μ n))
    (hn : ∀ n, ∀ᵐ x ∂μ n, ‖F n x‖ ≤ C)
    (hF : ∀ n, ∀ᵐ x ∂μ n, F n x ∈ P n x) :
    ∃ T ∈ A, ∀ (f : lp L 2) n, T f n =ᵐ[μ n] fun x => F n x (f n x) := by
  let Fn (n : ℕ) := l2LinearFieldMap (μ n) (F n) (hm n) C (hn n)
  have hFn (n : ℕ) : ‖Fn n‖ ≤ C := l2LinearFieldMap_norm_le _ _ _ C hC _
  let T := hilbertSumOperator Fn C hC hFn
  have hTf (f : lp L 2) (n : ℕ) : T f n = Fn n (f n) :=
    hilbertSumOperator_apply Fn C hC hFn f n
  have hFa (n : ℕ) : RepresentsOperatorField (μ n) (F n) (Fn n) :=
    fun f => l2LinearFieldApply_ae (μ n) (F n) (hm n) C (hn n) f
  refine ⟨T, ?_, fun f n => by rw [hTf]; exact hFa n (f n)⟩
  rw [← A.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro S hS
  obtain ⟨G, hG, hSG⟩ := hcomm S hS
  have hSd := hilbertSum_field_diagonal μ S G hSG
  have hSF (n : ℕ) (v : L n) :
      hilbertSumCompression n S (Fn n v) = Fn n (hilbertSumCompression n S v) := by
    have hSa := hilbertSumCompression_field_action μ S G hSG n
    apply Lp.ext
    filter_upwards [hSa (Fn n v), hFa n v, hFa n (hilbertSumCompression n S v),
      hSa v, hG n, hF n] with x hsf hfv hfs hsv hg hf
    rw [hsf, hfv, hfs, hsv]
    exact congrArg (fun R : K n →L[ℂ] K n => R (v x))
      (VonNeumannAlgebra.mem_commutant_iff.mp hg (F n x) hf).symm
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  change S (T f) n = T (S f) n
  rw [hSd, hTf, hTf, hSd]
  exact hSF n (f n)

end

end KadisonKastler

end OAI
