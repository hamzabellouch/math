import Mathlib
import OAI.Analysis.FreeWords.HaarEndpointLimitsDefinitions
import OAI.Analysis.FreeWords.HaarEndpoints

namespace OAI

noncomputable section

namespace KKHaarEndpoints

noncomputable section

open Filter

open scoped Topology

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

theorem haar_endpoint_limits : HaarEndpointLimits (A := A) := by
  intro ι L τ B u h1 htr hH hC
  have hp (j : ι) (k l : ℤ) : (u j^k).val*(u j^l).val=(u j^(k+l)).val := by simp [zpow_add]
  have aux : ∀n:ℕ, ∀w:List (ℤ×A), w.length=n → CenteredPowerWord τ B w →
      ∀k:ℤ,k≠0 → Tendsto (fun j => τ (powerWord (u j) w*(u j^k).val)) L (𝓝 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hlen hc k hk
      cases w with
      | nil => simpa only [powerWord_nil,one_mul] using hH k hk
      | cons z t =>
        have hz := hc z List.mem_cons_self
        have ht : CenteredPowerWord τ B t := fun a ha => hc a (List.mem_cons_of_mem _ ha)
        have hrot (j : ι) : τ (powerWord (u j) (z::t)*(u j^k).val)=
            τ ((u j^(k+z.1)).val*z.2*powerWord (u j) t) := by
          rw [powerWord_cons,htr]
          congr 1
          rw [← hp]
          simp only [mul_assoc]
        simp_rw [hrot]
        by_cases hsum : k+z.1=0
        · simp only [hsum,zpow_zero,OneMemClass.coe_one,one_mul]
          induction t using List.reverseRecOn with
          | nil => simpa only [powerWord_nil,mul_one,hz.2.2] using
              (tendsto_const_nhds : Tendsto (fun _ : ι => (0:ℂ)) L (𝓝 0))
          | append_singleton v a unused =>
            have hv : CenteredPowerWord τ B v := by
              intro b hb
              exact ht b (List.mem_append_left _ hb)
            have ha := ht a (List.mem_append_right _ (List.mem_singleton_self _))
            let d := a.2*z.2
            let d₀ := d-(τ d) • (1:A)
            have hd₀ : d₀∈B ∧ τ d₀=0 := by
              refine ⟨B.sub_mem (B.mul_mem ha.2.1 hz.2.1) (B.smul_mem B.one_mem _),?_⟩
              simp [d₀,map_sub,map_smul,h1]
            have hvc : CenteredPowerWord τ B (v++[(a.1,d₀)]) := by
              intro b hb
              rcases List.mem_append.mp hb with hb | hb
              · exact hv b hb
              · have he := List.mem_singleton.mp hb
                subst b
                exact ⟨ha.1,hd₀⟩
            have hc0 := hC (v++[(a.1,d₀)]) (by simp) hvc
            have hlenv : v.length<n := by simp only [List.length_cons,List.length_append] at hlen; omega
            have ho0 := ih v.length hlenv v rfl hv a.1 ha.1
            have hr (j : ι) : τ (z.2*powerWord (u j) (v++[a]))=
                τ (powerWord (u j) v*(u j^a.1).val*d) := by
              rw [htr,powerWord_append,powerWord_cons,powerWord_nil,mul_one]
              congr 1
              dsimp [d]
              simp only [mul_assoc]
            simp_rw [hr]
            have he (j : ι) : powerWord (u j) v*(u j^a.1).val*d=
                powerWord (u j) (v++[(a.1,d₀)])+(τ d) • (powerWord (u j) v*(u j^a.1).val) := by
              simp only [powerWord_append,powerWord_cons,powerWord_nil,mul_one,d₀,
                mul_sub,mul_smul_comm,mul_assoc]
              abel
            simp_rw [he,map_add,map_smul,smul_eq_mul]
            simpa using hc0.add (ho0.const_mul (τ d))
        · exact hC ((k+z.1,z.2)::t) (by simp) (by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact ⟨hsum,hz.2⟩
            · exact ht a ha)
  intro w hw k hk
  exact aux w.length w rfl hw k hk

end

end KKHaarEndpoints
end

end OAI
