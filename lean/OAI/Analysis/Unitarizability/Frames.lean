import OAI.Analysis.Unitarizability.FrameSelection
import OAI.Analysis.Unitarizability.ComplexFrames

namespace OAI

/-! Frame existence with prescribed dimensions and bounds for all small subfamilies. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J L K : Type*} [Fintype I] [Fintype J] [Fintype L] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq J := Classical.decEq J
local instance : DecidableEq L := Classical.decEq L
local instance : DecidableEq K := Classical.decEq K

def extendVector (e : J ↪ L) (z : EuclideanSpace ℝ J) : EuclideanSpace ℝ L :=
  WithLp.toLp 2 (extend e z)

theorem extendVector_norm (e : J ↪ L) (z : EuclideanSpace ℝ J) : ‖extendVector e z‖ = ‖z‖ := by
  have h : ‖extendVector e z‖^2 = ‖z‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, extendVector, Real.norm_eq_abs, sq_abs]
    exact sum_extend_sq e z
  nlinarith [norm_nonneg (extendVector e z), norm_nonneg z]

omit [Fintype I] in
theorem synthesis_extendVector (σ : K × I → Bool) (e : L ↪ I) (f : J ↪ L)
    (z : EuclideanSpace ℝ J) : synthesis σ e (extendVector f z) = synthesis σ (f.trans e) z := by
  simp only [synthesis_apply, extendVector]
  rw [sum_on_embedding f _ (fun i hi => by rw [extend_off f z i hi]; simp)]
  simp only [extend_apply, Function.Embedding.trans_apply]

omit [Fintype I] in
theorem synthesis_restrict_norm (σ : K × I → Bool) (e : L ↪ I) (f : J ↪ L) :
    ‖synthesis σ (f.trans e)‖ ≤ ‖synthesis σ e‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  rw [← synthesis_extendVector]
  exact ((synthesis σ e).le_opNorm _).trans_eq (by rw [extendVector_norm])

/-- Extend each smaller subset to size p, then restrict a coordinate synthesis operator. -/
theorem all_subfamilies {k p : ℕ} (hp : p ≤ Fintype.card I) (σ : Fin k × I → Bool)
    (hσ : ∀ e : Fin p ↪ I, ‖synthesis σ e‖ ≤ 10) :
    ∀ J : Finset I, J.card ≤ p →
      ‖FiniteSynthesis.synthesis (fun i => ComplexFrames.ofReal (vector σ i)) J‖ ≤ 10 := by
  classical
  intro J hJ
  obtain ⟨L, hJL, hLu, hLc⟩ := Finset.exists_subsuperset_card_eq (s := J) (t := univ)
    (Finset.subset_univ _) hJ (by simpa using hp)
  let eL : L ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  let q : L ≃ Fin p := L.equivFinOfCardEq hLc
  let e : Fin p ↪ I := q.symm.toEmbedding.trans eL
  have he : q.toEmbedding.trans e = eL := by ext i; simp [e]
  have hL : ‖synthesis σ eL‖ ≤ 10 := by
    have h := synthesis_restrict_norm σ e q.toEmbedding
    rw [he] at h
    exact h.trans (hσ e)
  let f : J ↪ L := ⟨fun i => ⟨i.1, hJL i.2⟩, by intro a b h; exact Subtype.ext (congrArg (fun x : L => (x : I)) h)⟩
  let eJ : J ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have hf : f.trans eL = eJ := by ext i; rfl
  have hJnorm : ‖synthesis σ eJ‖ ≤ 10 := by
    have h := synthesis_restrict_norm σ eL f
    rw [hf] at h
    exact h.trans hL
  apply ComplexFrames.synthesis_bound _ J (by norm_num : (0 : ℝ) ≤ 10)
  intro z
  have h := (synthesis σ eJ).le_of_opNorm_le hJnorm z
  simpa only [synthesis_apply, eJ, Function.Embedding.coeFn_mk] using h

/-- Frames with k=ceil(2r log(2n)), p=min(2r,n), and bound 10. -/
theorem frames {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    ∃ v : Fin n → EuclideanSpace ℂ (Fin (FrameParameters.dimension n r)),
      (∀ i, ‖v i‖ = 1) ∧
      FiniteSynthesis.FrameBound v (FrameParameters.subfamilySize n r) 10 := by
  have hk : 0 < FrameParameters.dimension n r := (FrameParameters.bounds hn hr).1
  let : Nonempty (Fin (FrameParameters.dimension n r)) := Fin.pos_iff_nonempty.mp hk
  obtain ⟨σ, hσ⟩ := exists_sign_matrix hk (FrameParameters.exact_failure_bound hn hr)
  refine ⟨fun i => ComplexFrames.ofReal (vector σ i), ?_, ?_⟩
  · intro i
    rw [ComplexFrames.ofReal_norm, vector_norm]
  · exact all_subfamilies (by simpa only [FrameParameters.subfamilySize, Fintype.card_fin] using Nat.min_le_right (2*r) n) σ hσ


/-- The frame lemma for arbitrary finite label types. -/
theorem frames_for_fintype {r : ℕ} (hn : 2 ≤ Fintype.card I) (hr : 1 ≤ r) :
    ∃ v : I → EuclideanSpace ℂ (Fin (FrameParameters.dimension (Fintype.card I) r)),
      (∀ i, ‖v i‖ = 1) ∧
      FiniteSynthesis.FrameBound v (FrameParameters.subfamilySize (Fintype.card I) r) 10 := by
  have hk : 0 < FrameParameters.dimension (Fintype.card I) r := (FrameParameters.bounds hn hr).1
  let : Nonempty (Fin (FrameParameters.dimension (Fintype.card I) r)) := Fin.pos_iff_nonempty.mp hk
  obtain ⟨σ, hσ⟩ := exists_sign_matrix hk (FrameParameters.exact_failure_bound hn hr)
  let q := Fintype.equivFin I
  let σ' : Fin (FrameParameters.dimension (Fintype.card I) r) × I → Bool := fun ai => σ (ai.1, q ai.2)
  have hσ' (e : Fin (FrameParameters.subfamilySize (Fintype.card I) r) ↪ I) : ‖synthesis σ' e‖ ≤ 10 := by
    have hid : synthesis σ' e = synthesis σ (e.trans q.toEmbedding) := rfl
    rw [hid]
    exact hσ _
  refine ⟨fun i => ComplexFrames.ofReal (vector σ' i), ?_, ?_⟩
  · intro i
    rw [ComplexFrames.ofReal_norm, vector_norm]
  · exact all_subfamilies (Nat.min_le_right _ _) σ' hσ'


end SignMatrix
end Dixmier

end

end OAI
