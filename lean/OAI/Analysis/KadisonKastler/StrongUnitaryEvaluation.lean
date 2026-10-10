import OAI.Analysis.KadisonKastler.StrongUnitaryCoordinates

namespace OAI

/-! # Evaluation on the strong-star Polish unitary model -/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def encodeStrongUnitary (ξ : ℕ → H) (u : unitary (H →L[ℂ] H)) : StrongUnitarySpace ξ :=
  ⟨unitaryCoordinates ξ u, ⟨u, rfl⟩⟩

def decodeStrongUnitary (ξ : ℕ → H) (p : StrongUnitarySpace ξ) :
    unitary (H →L[ℂ] H) := Classical.choose p.property

theorem unitaryCoordinates_decode (ξ : ℕ → H) (p : StrongUnitarySpace ξ) :
    unitaryCoordinates ξ (decodeStrongUnitary ξ p) = p.val :=
  Classical.choose_spec p.property

@[simp] theorem decodeStrongUnitary_apply_test (ξ : ℕ → H) (p : StrongUnitarySpace ξ) (j : ℕ) :
    (decodeStrongUnitary ξ p : H →L[ℂ] H) (ξ j) = p.val.1 j :=
  congrFun (congrArg Prod.fst (unitaryCoordinates_decode ξ p)) j

@[simp] theorem star_decodeStrongUnitary_apply_test (ξ : ℕ → H)
    (p : StrongUnitarySpace ξ) (j : ℕ) :
    (star (decodeStrongUnitary ξ p) : H →L[ℂ] H) (ξ j) = p.val.2 j :=
  congrFun (congrArg Prod.snd (unitaryCoordinates_decode ξ p)) j

theorem decode_encodeStrongUnitary (ξ : ℕ → H) (hξ : DenseRange ξ)
    (u : unitary (H →L[ℂ] H)) :
    decodeStrongUnitary ξ (encodeStrongUnitary ξ u) = u :=
  unitaryCoordinates_injective ξ hξ (unitaryCoordinates_decode ξ _)

theorem encode_decodeStrongUnitary (ξ : ℕ → H) (p : StrongUnitarySpace ξ) :
    encodeStrongUnitary ξ (decodeStrongUnitary ξ p) = p :=
  Subtype.ext (unitaryCoordinates_decode ξ p)

private theorem decode_norm_le_one (ξ : ℕ → H) (p : StrongUnitarySpace ξ) :
    ‖(decodeStrongUnitary ξ p : H →L[ℂ] H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [Unitary.norm_map, one_mul, le_refl]

private theorem star_decode_norm_le_one (ξ : ℕ → H) (p : StrongUnitarySpace ξ) :
    ‖(star (decodeStrongUnitary ξ p) : H →L[ℂ] H)‖ ≤ 1 := by
  rw [norm_star]
  exact decode_norm_le_one ξ p

theorem continuous_decodeStrongUnitary_apply (ξ : ℕ → H) (hξ : DenseRange ξ) (x : H) :
    Continuous (fun p : StrongUnitarySpace ξ => (decodeStrongUnitary ξ p : H →L[ℂ] H) x) := by
  apply SeqContinuous.continuous
  intro p q hp
  apply tendsto_apply_of_dense_contractions ξ hξ
    (fun n => (decodeStrongUnitary ξ (p n) : H →L[ℂ] H))
    (decodeStrongUnitary ξ q : H →L[ℂ] H)
    (fun n => decode_norm_le_one ξ (p n)) (decode_norm_le_one ξ q)
  intro j
  have hc : Continuous (fun p : StrongUnitarySpace ξ => p.val.1 j) :=
    (continuous_apply j).comp (continuous_fst.comp continuous_subtype_val)
  have ht := (hc.tendsto q).comp hp
  convert ht using 1
  · funext n
    exact decodeStrongUnitary_apply_test ξ (p n) j
  · rw [decodeStrongUnitary_apply_test]

theorem continuous_star_decodeStrongUnitary_apply (ξ : ℕ → H) (hξ : DenseRange ξ) (x : H) :
    Continuous (fun p : StrongUnitarySpace ξ =>
      (star (decodeStrongUnitary ξ p) : H →L[ℂ] H) x) := by
  apply SeqContinuous.continuous
  intro p q hp
  apply tendsto_apply_of_dense_contractions ξ hξ
    (fun n => (star (decodeStrongUnitary ξ (p n)) : H →L[ℂ] H))
    (star (decodeStrongUnitary ξ q) : H →L[ℂ] H)
    (fun n => star_decode_norm_le_one ξ (p n)) (star_decode_norm_le_one ξ q)
  intro j
  have hc : Continuous (fun p : StrongUnitarySpace ξ => p.val.2 j) :=
    (continuous_apply j).comp (continuous_snd.comp continuous_subtype_val)
  have ht := (hc.tendsto q).comp hp
  convert ht using 1
  · funext n
    exact star_decodeStrongUnitary_apply_test ξ (p n) j
  · rw [star_decodeStrongUnitary_apply_test]

theorem continuous_decodeStrongUnitary_apply_joint (ξ : ℕ → H) (hξ : DenseRange ξ) :
    Continuous (fun p : StrongUnitarySpace ξ × H =>
      (decodeStrongUnitary ξ p.1 : H →L[ℂ] H) p.2) := by
  apply SeqContinuous.continuous
  intro p q hp
  apply tendsto_apply_contractions
    (fun n => (decodeStrongUnitary ξ (p n).1 : H →L[ℂ] H))
    (decodeStrongUnitary ξ q.1 : H →L[ℂ] H)
    (fun n => decode_norm_le_one ξ (p n).1)
    (fun x => ((continuous_decodeStrongUnitary_apply ξ hξ x).tendsto q.1).comp
      ((continuous_fst.tendsto q).comp hp))
  exact (continuous_snd.tendsto q).comp hp

theorem continuous_star_decodeStrongUnitary_apply_joint (ξ : ℕ → H) (hξ : DenseRange ξ) :
    Continuous (fun p : StrongUnitarySpace ξ × H =>
      (star (decodeStrongUnitary ξ p.1) : H →L[ℂ] H) p.2) := by
  apply SeqContinuous.continuous
  intro p q hp
  apply tendsto_apply_contractions
    (fun n => (star (decodeStrongUnitary ξ (p n).1) : H →L[ℂ] H))
    (star (decodeStrongUnitary ξ q.1) : H →L[ℂ] H)
    (fun n => star_decode_norm_le_one ξ (p n).1)
    (fun x => ((continuous_star_decodeStrongUnitary_apply ξ hξ x).tendsto q.1).comp
      ((continuous_fst.tendsto q).comp hp))
  exact (continuous_snd.tendsto q).comp hp

end

end KadisonKastler

end OAI
