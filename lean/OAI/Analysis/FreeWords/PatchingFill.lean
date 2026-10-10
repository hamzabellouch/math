import Mathlib
import OAI.Analysis.FreeWords.ColoredSplit
import OAI.Analysis.FreeWords.PatchTraceBounds
import OAI.Analysis.FreeWords.PatchingTermTrace

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKMatrixQuantization

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

theorem trace_colored_first (v w : PartialUnitary (ConcreteAlgebra M))
    (p : List (ConcreteAlgebra M × ℤ)) (z : ConcreteAlgebra M × ℤ)
    (r : List (Colored.Cell (ConcreteAlgebra M))) (right : ConcreteAlgebra M) :
    τ.map (Colored.value v.power w.power (Colored.old p++(z,true)::r)*right)=
      τ.map (w.power z.2*(Colored.value v.power w.power r*right*PatchingWord.tailValue v.power p*z.1)) := by
  simp only [Colored.value_append,Colored.value_cons,ite_true,Colored.value_old]
  change τ.map ((PatchingWord.tailValue v.power p*(z.1*w.power z.2*Colored.value v.power w.power r))*right)=_
  rw [show (PatchingWord.tailValue v.power p*(z.1*w.power z.2*Colored.value v.power w.power r))*right=
    (PatchingWord.tailValue v.power p*z.1)*(w.power z.2*(Colored.value v.power w.power r*right)) by noncomm_ring]
  rw [τ.tracial]
  congr 1

theorem trace_changed_le (v w : PartialUnitary (ConcreteAlgebra M))
    (A : PatchingWord (ConcreteAlgebra M)) (c : List (Colored.Cell (ConcreteAlgebra M)))
    (hc : c∈Colored.changes A.raw)
    (hnorm : ∀ z∈A.raw, ‖z.1‖≤1) (hright : ‖A.right‖≤1) :
    ‖τ.map (Colored.value v.power w.power c*A.right)‖≤(τ.map w.support).re := by
  have hall : ∀ z∈c, ‖z.1.1‖≤1 := by
    intro z hz
    apply hnorm z.1
    rw [← Colored.erase_of_mem_changes hc]
    exact List.mem_map_of_mem hz
  obtain ⟨p,z,r,he⟩ := Colored.first_true_split c (Colored.true_of_mem_changes hc)
  rw [he,trace_colored_first]
  have hall' := he ▸ hall
  have hz : ‖z.1‖≤1 := hall' (z,true) (List.mem_append_right _ List.mem_cons_self)
  have hp : ‖PatchingWord.tailValue v.power p‖≤1 := by
    have hh := norm_colored_value_le_one v w (Colored.old p)
      (fun a ha => hall' a (List.mem_append_left _ ha))
    simpa only [Colored.value_old,PatchingWord.tailValue] using hh
  have hr : ‖Colored.value v.power w.power r‖≤1 := by
    apply norm_colored_value_le_one v w r
    intro a ha
    exact hall' a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
  let Z := Colored.value v.power w.power r*A.right*PatchingWord.tailValue v.power p*z.1
  have hZ : ‖Z‖≤1 := norm_mul_le_one (norm_mul_le_one (norm_mul_le_one hr hright) hp) hz
  have hA : w.support*(w.power z.2*Z)=w.power z.2*Z := by rw [← mul_assoc,w.support_mul]
  have hb := trace_supported_le τ w.support (w.power z.2*Z) w.projection hA
  rw [traceNorm_projection_sq τ w.projection] at hb
  have ht : 0≤(τ.map w.support).re := by
    rw [← traceNorm_projection_sq τ w.projection]; exact sq_nonneg _
  exact hb.trans ((mul_le_mul_of_nonneg_left (norm_mul_le_one (w.norm_power_le_one _) hZ) ht).trans_eq (mul_one _))

def projectionUnitary (p : ConcreteAlgebra M) (hp : IsStarProjection p) : PartialUnitary (ConcreteAlgebra M) where
  power _ := p
  add _ _ := hp.isIdempotentElem.eq.symm
  power_star _ := hp.isSelfAdjoint.star_eq

theorem fill_partial_bound (v : PartialUnitary (ConcreteAlgebra M))
    {X : Set (ConcreteAlgebra M)} {K : Set ℤ} {N : ℕ}
    (hX : ∀ x∈X, ‖x‖≤1) {b η : ℝ}
    (ht : (τ.map v.support).re=1-η)
    (hv : ∀ A, PatchingWord.Admissible X K N A → ‖τ.map (A.value v.power)‖≤b) :
    ∃ u : unitary (ConcreteAlgebra M), ∀ A, PatchingWord.Admissible X K N A →
      ‖τ.map (A.value (fun k => (u^k).val))‖≤b+2^N*η := by
  let w := projectionUnitary (1-v.support) v.projection.one_sub
  have ho : v.support*w.support=0 := by
    change v.support*(1-v.support)=0
    rw [mul_sub,mul_one,v.projection.isIdempotentElem.eq,sub_self]
  let z := v.sum w ho
  have hz : z.support=1 := by
    change v.support+(1-v.support)=1
    abel
  have htrace : (τ.map w.support).re=η := by
    change (τ.map (1-v.support)).re=η
    rw [map_sub,τ.normalized,Complex.sub_re,Complex.one_re,ht]
    ring
  have hη : 0≤η := by
    rw [← htrace,← traceNorm_projection_sq τ w.projection]
    exact sq_nonneg _
  refine ⟨z.toUnitary hz,fun A hA => ?_⟩
  simp only [z.toUnitary_power]
  have hnorm := norm_raw_coefficients hX hA
  have hterms : ∀ c∈Colored.changes A.raw,
      ‖τ.map (Colored.value v.power w.power c*A.right)‖≤η := by
    intro c hc
    simpa only [htrace] using trace_changed_le τ v w A c hc hnorm.1 hnorm.2
  have hb := expanded_trace_bound τ A v.power w.power hη hterms
  have hpow : (2:ℝ)^A.length≤2^N := pow_le_pow_right₀ (by norm_num) hA.2.2.2.2
  exact hb.trans (add_le_add (hv A hA) (mul_le_mul_of_nonneg_right hpow hη))

end

end KKLocalPatching
end

end OAI
