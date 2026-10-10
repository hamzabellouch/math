import OAI.Analysis.Triangular.Schwartz.SpectralCLM
import OAI.Analysis.Triangular.Envelope.JetEnvelopeAnalytic
import OAI.Analysis.Triangular.Construction.TailEnumeration
import OAI.Analysis.Triangular.Envelope.EnvelopeSumsBase

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma frequencyDecay_pos (q v : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    0 < frequencyDecay (damping q) (damping v) t := by
  have hx := Xwave_antitone (damping_pos q) (abs_nonneg t) ht
  have he : Xwave (damping q) |t|=Xwave (damping q) t := by simp [Xwave,waveDen,sq_abs]
  rw [he] at hx
  have hb : damping v < damping q * Xwave (damping q) (5/6) := by
    fin_cases q <;> fin_cases v <;> norm_num [damping,h,H,Xwave,waveDen]
  unfold frequencyDecay
  exact mul_pos Real.pi_pos (sub_pos.mpr (hb.trans_le (mul_le_mul_of_nonneg_left hx (damping_pos q).le)))
lemma normJetEnvelope_enumerateTail (a : Fin 15) (l : ℕ) (k v t : ℝ) :
    normJetEnvelope k v (enumerateTail (a,l)).val.val t =
      normJetEnvelope k v (tailBase a) t * (Real.exp (-frequencyDecay k v t*36))^l := by
  unfold normJetEnvelope
  rw [Q_enumerateTail,D_enumerateTail]
  change _ * Real.exp (-frequencyDecay k v t * ((tailBase a + 36*(l:ℤ):ℤ):ℝ)) = _
  rw [show -frequencyDecay k v t * ((tailBase a + 36*(l:ℤ):ℤ):ℝ) =
    -frequencyDecay k v t*(tailBase a:ℝ) + (l:ℝ)*(-frequencyDecay k v t*36) by push_cast; ring,
    Real.exp_add,Real.exp_nat_mul]
  ring
lemma summable_envelope_period (q v : Fin 2) (a : Fin 15) {t : ℝ} (ht : |t|≤5/6) :
    Summable (fun l : ℕ => normJetEnvelope (damping q) (damping v) (enumerateTail (a,l)).val.val t) := by
  simp_rw [normJetEnvelope_enumerateTail]
  apply Summable.mul_left
  apply summable_geometric_of_norm_lt_one
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
  have hh := frequencyDecay_pos q v ht
  nlinarith
lemma tsum_envelope_period (q v : Fin 2) (a : Fin 15) {t : ℝ} (ht : |t|≤5/6) :
    (∑' l : ℕ, normJetEnvelope (damping q) (damping v) (enumerateTail (a,l)).val.val t) =
    normJetEnvelope (damping q) (damping v) (tailBase a) t *
      (1-Real.exp (-frequencyDecay (damping q) (damping v) t*36))⁻¹ := by
  simp_rw [normJetEnvelope_enumerateTail]
  rw [tsum_mul_left,tsum_geometric_of_norm_lt_one]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
  have hh := frequencyDecay_pos q v ht
  nlinarith
lemma summable_tailEnvelope (q v : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    Summable (fun n : TailNode => normJetEnvelope (damping q) (damping v) n.val.val t) := by
  apply (tailEnumeration.summable_iff).mp
  apply (summable_prod_of_nonneg (fun p => normJetEnvelope_nonneg _ _ _ _ (by
    have hh := FiniteCertificate.Q_node_bounds (enumerateTail p).val.val (enumerateTail p).val.property.2
    change 0 < Q (enumerateTail p).val.val
    linarith [hh.1]))).mpr
  exact ⟨fun a => summable_envelope_period q v a ht, (hasSum_fintype _).summable⟩
lemma tsum_tailEnvelope (q v : Fin 2) (j : Fin 31) :
    (∑' n : TailNode, normJetEnvelope (damping q) (damping v) n.val.val (frequency j)) =
    tailEnvelopeSum q v j := by
  have ht : |frequency j|≤5/6 := abs_le.mpr (frequency_mem j)
  rw [←tailEnumeration.tsum_eq]
  have hs := tailEnumeration.summable_iff.mpr (summable_tailEnvelope q v ht)
  change Summable (fun p : Fin 15 × ℕ => normJetEnvelope (damping q) (damping v) (enumerateTail p).val.val (frequency j)) at hs
  change (∑' p : Fin 15 × ℕ, normJetEnvelope (damping q) (damping v) (enumerateTail p).val.val (frequency j)) = _
  rw [hs.tsum_prod]
  simp_rw [tsum_envelope_period q v _ ht]
  rw [tsum_fintype,←Finset.sum_mul]
  rfl
end AtomicTriangular.Construction
end

end OAI
