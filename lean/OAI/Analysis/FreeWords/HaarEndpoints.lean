import Mathlib
import OAI.Analysis.FreeWords.HaarEndpointsDefinitions

namespace OAI

noncomputable section

namespace KKHaarEndpoints

noncomputable section

variable {A : Type*} [Ring A] [StarRing A]

@[simp] theorem powerWord_nil (u : unitary A) : powerWord u []=1 := rfl

@[simp] theorem powerWord_cons (u : unitary A) (z : ℤ×A) (w : List (ℤ×A)) :
    powerWord u (z::w)=(u^z.1).val*z.2*powerWord u w := rfl

@[simp] theorem powerWord_append (u : unitary A) (v w : List (ℤ×A)) :
    powerWord u (v++w)=powerWord u v*powerWord u w := by simp [powerWord]

variable [Algebra ℂ A]

theorem haar_endpoint_completion : HaarEndpointCompletion (A := A) := by
  intro τ B u h1 htr hH hC
  have hp (k l : ℤ) : (u^k).val*(u^l).val=(u^(k+l)).val := by simp [zpow_add]
  have aux : ∀n:ℕ, ∀w:List (ℤ×A), w.length=n → CenteredPowerWord τ B w →
      ∀k:ℤ,k≠0 → τ (powerWord u w*(u^k).val)=0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hlen hc k hk
      cases w with
      | nil => simpa only [powerWord_nil,one_mul] using hH k hk
      | cons z t =>
        have hz := hc z List.mem_cons_self
        have ht : CenteredPowerWord τ B t := fun a ha => hc a (List.mem_cons_of_mem _ ha)
        have hrot : τ (powerWord u (z::t)*(u^k).val)=
            τ ((u^(k+z.1)).val*z.2*powerWord u t) := by
          rw [powerWord_cons,htr]
          congr 1
          rw [← hp]
          simp only [mul_assoc]
        rw [hrot]
        by_cases hsum : k+z.1=0
        · simp only [hsum,zpow_zero,OneMemClass.coe_one,one_mul]
          induction t using List.reverseRecOn with
          | nil => simpa only [powerWord_nil,mul_one] using hz.2.2
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
            have hlenv : v.length<n := by
              simp only [List.length_cons,List.length_append] at hlen
              omega
            have ho0 := ih v.length hlenv v rfl hv a.1 ha.1
            have hr : τ (z.2*powerWord u (v++[a]))=
                τ (powerWord u v*(u^a.1).val*d) := by
              rw [htr,powerWord_append,powerWord_cons,powerWord_nil,mul_one]
              congr 1
              dsimp [d]
              simp only [mul_assoc]
            rw [hr]
            have he : powerWord u v*(u^a.1).val*d=
                powerWord u (v++[(a.1,d₀)])+(τ d) • (powerWord u v*(u^a.1).val) := by
              simp only [powerWord_append,powerWord_cons,powerWord_nil,mul_one,d₀,
                mul_sub,mul_smul_comm]
              simp only [mul_assoc]; abel
            rw [he,map_add,map_smul,hc0,ho0,smul_zero,add_zero]
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
