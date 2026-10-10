import OAI.Analysis.PureInfiniteness.RelativeOneStep

namespace OAI

/-! Finite sums and output compressions of relatively approximately inner
maps. These are the coefficient operations required by the local cone proof. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {B D : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]

lemma approximatelyInnerAlong_innerHomCompression (φ : B →⋆ₙₐ[ℂ] D) (v : D) :
    ApproximatelyInnerAlong φ (innerHomCompression φ v) := by
  intro F ε hε
  refine ⟨1, fun _ => v, ?_⟩
  intro b _
  simpa only [Fin.sum_univ_one, innerHomCompression_apply, sub_self, norm_zero] using hε

lemma ApproximatelyInnerAlong.add (φ : B →⋆ₙₐ[ℂ] D) {S T : B → D}
    (hS : ApproximatelyInnerAlong φ S) (hT : ApproximatelyInnerAlong φ T) :
    ApproximatelyInnerAlong φ (fun b => S b + T b) := by
  intro F ε hε
  obtain ⟨n, v, hv⟩ := hS F (ε / 2) (by positivity)
  obtain ⟨m, w, hw⟩ := hT F (ε / 2) (by positivity)
  refine ⟨n + m, Fin.append v w, ?_⟩
  intro b hb
  have he : (∑ j, star (Fin.append v w j) * φ b * Fin.append v w j) =
      (∑ j, star (v j) * φ b * v j) + (∑ j, star (w j) * φ b * w j) := by
    simp [Fin.sum_univ_add]
  rw [he]
  have hd : S b + T b - ((∑ j, star (v j) * φ b * v j) +
      (∑ j, star (w j) * φ b * w j)) =
      (S b - ∑ j, star (v j) * φ b * v j) + (T b - ∑ j, star (w j) * φ b * w j) := by abel
  rw [hd]
  exact (norm_add_le _ _).trans_lt (by linarith [hv b hb, hw b hb])

lemma ApproximatelyInnerAlong.outputCompression (φ : B →⋆ₙₐ[ℂ] D) {T : B → D}
    (hT : ApproximatelyInnerAlong φ T) (a : D) :
    ApproximatelyInnerAlong φ (fun b => star a * T b * a) := by
  intro F ε hε
  let K := ‖a‖ * ‖a‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ := ε / K
  have hδ : 0 < δ := div_pos hε hK
  obtain ⟨n, v, hv⟩ := hT F δ hδ
  refine ⟨n, fun j => v j * a, ?_⟩
  intro b hb
  have he : star a * T b * a - (∑ j, star (v j * a) * φ b * (v j * a)) =
      star a * (T b - ∑ j, star (v j) * φ b * v j) * a := by
    simp only [star_mul, mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_sub, sub_mul]
  rw [he]
  calc
    _ ≤ (‖star a‖ * ‖T b - ∑ j, star (v j) * φ b * v j‖) * ‖a‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖a‖ * δ) * ‖a‖ := by rw [norm_star]; gcongr; exact (hv b hb).le
    _ < ε := by
      have hk : δ * K = ε := div_mul_cancel₀ ε hK.ne'
      dsimp [K] at hk
      nlinarith

lemma ApproximatelyInnerAlong.finset_sum {I : Type*} (φ : B →⋆ₙₐ[ℂ] D)
    (s : Finset I) (T : I → B → D) (hT : ∀ i ∈ s, ApproximatelyInnerAlong φ (T i)) :
    ApproximatelyInnerAlong φ (fun b => ∑ i ∈ s, T i b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro F ε hε
    refine ⟨0, Fin.elim0, ?_⟩
    intro b _
    simpa using hε
  | @insert i s hi ih =>
    have h := (hT i (Finset.mem_insert_self _ _)).add φ
      (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

end WeakPureInfiniteness

end

end OAI
