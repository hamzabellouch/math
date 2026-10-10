import Mathlib
import OAI.Analysis.FreeWords.HaarEndpointLimits
import OAI.Analysis.FreeWords.HaarLeftEndpointDefinitions

namespace OAI

noncomputable section

namespace KKHaarEndpoints

noncomputable section

open Filter

open scoped Topology

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

theorem haar_left_endpoint_limits : HaarLeftEndpointLimits (A := A) := by
  intro ι L τ B u h1 htr hH hC w hne hw a ha
  have hO := haar_endpoint_limits ι L τ B u h1 htr hH hC
  induction w using List.reverseRecOn with
  | nil => exact (hne rfl).elim
  | append_singleton v z unused =>
    have hv : CenteredPowerWord τ B v := by
      intro b hb
      exact hw b (List.mem_append_left _ hb)
    have hz := hw z (List.mem_append_right _ (List.mem_singleton_self _))
    let d := z.2*a
    let d₀ := d-(τ d) • (1:A)
    have hd₀ : d₀∈B ∧ τ d₀=0 := by
      refine ⟨B.sub_mem (B.mul_mem hz.2.1 ha) (B.smul_mem B.one_mem _),?_⟩
      simp [d₀,map_sub,map_smul,h1]
    have hvc : CenteredPowerWord τ B (v++[(z.1,d₀)]) := by
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hv b hb
      · have he := List.mem_singleton.mp hb
        subst b
        exact ⟨hz.1,hd₀⟩
    have hc0 := hC (v++[(z.1,d₀)]) (by simp) hvc
    have ho0 := hO v hv z.1 hz.1
    have hr (j : ι) : τ (a*powerWord (u j) (v++[z]))=
        τ (powerWord (u j) v*(u j^z.1).val*d) := by
      rw [htr,powerWord_append,powerWord_cons,powerWord_nil,mul_one]
      congr 1
      dsimp [d]
      simp only [mul_assoc]
    simp_rw [hr]
    have he (j : ι) : powerWord (u j) v*(u j^z.1).val*d=
        powerWord (u j) (v++[(z.1,d₀)])+(τ d) • (powerWord (u j) v*(u j^z.1).val) := by
      simp only [powerWord_append,powerWord_cons,powerWord_nil,mul_one,d₀,
        mul_sub,mul_smul_comm,mul_assoc]
      abel
    simp_rw [he,map_add,map_smul,smul_eq_mul]
    simpa using hc0.add (ho0.const_mul (τ d))

end

end KKHaarEndpoints
end

end OAI
