import OAI.Analysis.KadisonKastler.ContractiveWeakLimit
import OAI.Analysis.KadisonKastler.TomiyamaDenseProjections
import OAI.Analysis.KadisonKastler.ProjectionModuleMaps

namespace OAI

/-! # State-preserving weak limits of matrix retractions

The limiting map retains the vector state on the larger algebra. Its
restriction is a bimodular expectation onto the smaller algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H}

/-- Retain both the range and the state when passing to a weak ultralimit. -/
theorem exists_state_preserving_weak_retraction
    (hNM : N ≤ M) (τ : TracialRepresentation N)
    (F : ℕ → (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hF : ∀ n, ‖F n‖ ≤ 1) (hmem : ∀ n T, F n T ∈ N)
    (hfix : ∀ a : Algebra N, Tendsto (fun n => F n a.val τ.vector) atTop
      (𝓝 (a.val τ.vector)))
    (hstate : ∀ n (a : Algebra M),
      inner ℂ τ.vector (F n a.val τ.vector) = inner ℂ τ.vector (a.val τ.vector)) :
    ∃ P : Algebra M →L[ℂ] Algebra N,
      ‖P‖ ≤ 1 ∧
      (∀ a : Algebra N, P (coordinateInclusion hNM a) = a) ∧
      (∀ a : Algebra M,
        inner ℂ τ.vector ((P a).val τ.vector) = inner ℂ τ.vector (a.val τ.vector)) := by
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨E,hE,ht⟩ := exists_contractive_weak_ultralimit ω F hF
  have hEM (T : H →L[ℂ] H) : E T ∈ N :=
    weak_operator_limit_mem N (fun n => ⟨F n T,hmem n T⟩) (E T) (ht T)
  have hET (T : H →L[ℂ] H) (hT : T ∈ N) : E T = T := by
    let a : Algebra N := ⟨T,hT⟩
    have hvec : E T τ.vector = T τ.vector := by
      apply ext_inner_left ℂ
      intro y
      apply tendsto_nhds_unique (ht T τ.vector y)
      exact ((continuous_const.inner continuous_id).tendsto _).comp
        ((hfix a).mono_left (Ultrafilter.of_le atTop))
    have hz : (⟨E T,hEM T⟩ : Algebra N) - a = 0 := τ.separating _ (by
      change E T τ.vector - T τ.vector = 0
      exact sub_eq_zero.mpr hvec)
    exact congrArg Subtype.val (sub_eq_zero.mp hz)
  let P : Algebra M →L[ℂ] Algebra N :=
    (E.comp M.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL).codRestrict
      N.toStarSubalgebra.toSubalgebra.toSubmodule (fun a => hEM a.val)
  refine ⟨P, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    exact E.le_of_opNorm_le hE a.val
  · intro a
    apply Subtype.ext
    exact hET a.val a.property
  · intro a
    apply tendsto_nhds_unique (ht a.val τ.vector τ.vector)
    have hs : (fun n => inner ℂ τ.vector (F n a.val τ.vector)) =
        fun _ => inner ℂ τ.vector (a.val τ.vector) := funext (fun n => hstate n a)
    rw [hs]
    exact tendsto_const_nhds

/-- A contractive retraction onto a von Neumann algebra is bimodular. -/
theorem retraction_bimodule (hNM : N ≤ M) (P : Algebra M →L[ℂ] Algebra N)
    (hP : ‖P‖ ≤ 1) (hfix : ∀ a : Algebra N, P (coordinateInclusion hNM a) = a) :
    (∀ (a : Algebra N) (x : Algebra M),
      P (coordinateInclusion hNM a * x) = a * P x) ∧
    (∀ (a : Algebra N) (x : Algebra M),
      P (x * coordinateInclusion hNM a) = P x * a) := by
  have h := tomiyama_map_mul_of_dense_projections
    (algebra_closed_projection_span_eq_top N) (coordinateInclusion hNM) P
    (fun x => by simpa only [one_mul] using P.le_of_opNorm_le hP x) hfix
  exact ⟨h.1,fun a x => h.2 x a⟩

end

end KadisonKastler

end OAI
