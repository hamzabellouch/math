import Mathlib
import OAI.Analysis.FreeWords.AsymptoticProduct

namespace OAI

noncomputable section

namespace KKAsymptoticTransport

noncomputable section

open Filter

open scoped Topology

variable {I A:Type*} [NormedRing A] [NormedAlgebra ℂ A]

omit [NormedAlgebra ℂ A] in
@[simp] theorem netPair_nil (j:I) : netPair ([]:List ((I → A)×A)) j=1 := rfl

omit [NormedAlgebra ℂ A] in
@[simp] theorem netPair_cons (z:(I → A)×A) (w:List ((I → A)×A)) (j:I) :
    netPair (z::w) j=z.1 j*z.2*netPair w j := rfl

omit [NormedAlgebra ℂ A] in
@[simp] theorem netPair_append (w v:List ((I → A)×A)) (j:I) :
    netPair (w++v) j=netPair w j*netPair v j := by
  simp [netPair,List.map_append,List.prod_append]

theorem raw_relative_limits (L:Filter I) (E:A →L[ℂ] A) (S:Set (I → A))
    (hbound:∀c∈S,NetBound c)
    (hzero:∀c∈S,Tendsto (fun j => E (c j)) L (𝓝 0))
    (hrel:RelativeBlockLimits L E S)
    (w:List ((I → A)×A)) (hw:∀z∈w,z.1∈S ∧ E z.2=0) :
    (w≠[] → Tendsto (fun j => E (netPair w j)) L (𝓝 0)) ∧
    (∀c∈S,Tendsto (fun j => E (netPair w j*c j)) L (𝓝 0)) := by
  have hb := fun z hz => hbound z.1 (hw z hz).1
  have hz := fun z hz => hzero z.1 (hw z hz).1
  have hd := pair_center_difference E w hb hz
  have hr := hrel w hw
  refine ⟨fun hn => tendsto_E_of_difference E hd (hr.1 hn),?_⟩
  intro c hc
  have hbc : NetBound (netPair (centeredWord E w)) := by
    apply NetBound.netPair
    intro z hz
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    exact (hb a ha).center E
  exact tendsto_E_of_difference E
    (asymp_mul hd (asymp_center E (hzero c hc)) hbc (hbound c hc)) (hr.2 c hc)

theorem asymptotic_block_transport : AsymptoticBlockTransport (I := I) (A := A) := by
  intro L E S T hid hright hbound hzero hjoin hrelative
  have hrelative' := raw_relative_limits L E S hbound hzero hrelative
  have hxzero (x:A) : E (x-E x)=0 := by rw [map_sub,hid,sub_self]
  have haux : ∀w:List ((I → A)×A),
      (∀z∈w,z.1∈S ∧ z.2∈T) →
      ∀p:List ((I → A)×A),
      (∀z∈p,z.1∈S ∧ E z.2=0) →
      ∀c∈S,∀x∈T,
        Tendsto (fun j => E (netPair p j*c j*x*netPair w j)) L (𝓝 0) := by
    intro w
    induction w with
    | nil =>
      intro _ p hp c hc x hx
      have hp' : ∀z∈p++[(c,x-E x)],z.1∈S ∧ E z.2=0 := by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hp z hz
        · have he := List.mem_singleton.mp hz
          subst z
          exact ⟨hc,hxzero x⟩
      have h₀ := (hrelative' (p++[(c,x-E x)]) hp').1 (by simp)
      have hB := null_mul ((hrelative' p hp).2 c hc) (NetBound.const (E x))
      have hsum := h₀.add hB
      have he (j:I) : E (netPair p j*c j*x*netPair [] j)=
          E (netPair (p++[(c,x-E x)]) j)+E (netPair p j*c j)*E x := by
        rw [← hright]
        rw [← map_add]
        congr 1
        simp only [netPair_nil,netPair_append,netPair_cons,mul_one]
        noncomm_ring
      simpa only [← he,add_zero] using hsum
    | cons z w ih =>
      intro hw p hp c hc x hx
      have hz := hw z List.mem_cons_self
      have hw' := fun a ha => hw a (List.mem_cons_of_mem _ ha)
      have hp' : ∀a∈p++[(c,x-E x)],a.1∈S ∧ E a.2=0 := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hp a ha
        · have he := List.mem_singleton.mp ha
          subst a
          exact ⟨hc,hxzero x⟩
      have hnew : (fun j => c j*E x*z.1 j)∈S := hjoin c hc z.1 hz.1 x hx
      have h₀ := ih hw' (p++[(c,x-E x)]) hp' z.1 hz.1 z.2 hz.2
      have hB := ih hw' p hp (fun j => c j*E x*z.1 j) hnew z.2 hz.2
      have hsum := h₀.add hB
      have he (j:I) : E (netPair p j*c j*x*netPair (z::w) j)=
          E (netPair (p++[(c,x-E x)]) j*z.1 j*z.2*netPair w j)+
          E (netPair p j*(c j*E x*z.1 j)*z.2*netPair w j) := by
        rw [← map_add]
        congr 1
        simp only [netPair_append,netPair_cons,netPair_nil,mul_one]
        noncomm_ring
      simpa only [← he,add_zero] using hsum
  intro w hne hw
  cases w with
  | nil => exact (hne rfl).elim
  | cons z w =>
    have hz := hw z List.mem_cons_self
    have hh := haux w (fun a ha => hw a (List.mem_cons_of_mem _ ha)) [] (by simp)
      z.1 hz.1 z.2 hz.2
    simpa only [netPair_nil,one_mul,netPair_cons] using hh

end

end KKAsymptoticTransport
end

end OAI
