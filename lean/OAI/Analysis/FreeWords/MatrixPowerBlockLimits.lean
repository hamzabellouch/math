import Mathlib
import OAI.Analysis.FreeWords.HaarEndpointLimits
import OAI.Analysis.FreeWords.MatrixPowerBlockLimitsDefinitions
import OAI.Analysis.FreeWords.MatrixTraceCyclic

namespace OAI

noncomputable section

namespace KKMatrixExpectation

noncomputable section

open Filter KKHaarEndpoints

open scoped Topology

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem matrix_power_block_limits : MatrixPowerBlockLimits (A := A) := by
  intro ι L τ h1 htr n hn u hH hC w hw k hk a b
  let τn := matrixTraceMap τ n
  let B := (numericalHom (A := A) n).range.toSubalgebra
  have hn1 : τn 1=1 := matrixTraceMap_one τ h1 hn
  have hc := matrixTraceMap_cyclic τ htr n
  have hO := haar_endpoint_limits (A := Matrix (Fin n) (Fin n) A) ι L τn B u hn1 hc hH hC
  let e := numericalHom (A := A) n (Matrix.single b a 1)
  let e₀ := e-(τn e) • 1
  have he : e∈B := ⟨Matrix.single b a 1,rfl⟩
  have he₀ : e₀∈B ∧ τn e₀=0 := by
    refine ⟨B.sub_mem he (B.smul_mem B.one_mem _),?_⟩
    simp [e₀,map_sub,map_smul,hn1]
  have hw' : CenteredPowerWord τn B (w++[(k,e₀)]) := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hw z hz
    · have hze := List.mem_singleton.mp hz
      subst z
      exact ⟨hk,he₀⟩
  have hclosed := hC (w++[(k,e₀)]) (by simp) hw'
  have hopen := hO w hw k hk
  have htest : Tendsto (fun j => τn (powerWord (u j) w*(u j^k).val*e)) L (𝓝 0) := by
    have hsum := hclosed.add (hopen.const_mul (τn e))
    have hid (j : ι) : τn (powerWord (u j) w*(u j^k).val*e)=
        τn (powerWord (u j) (w++[(k,e₀)]))+(τn e)*τn (powerWord (u j) w*(u j^k).val) := by
      simp only [powerWord_append,powerWord_cons,powerWord_nil,mul_one,e₀,mul_sub,
        mul_smul_comm,map_sub,map_smul,smul_eq_mul,mul_assoc]
      ring
    simp_rw [hid]
    simpa only [τn,zero_add,mul_zero] using hsum
  have hentry (j:ι) : τ ((powerWord (u j) w*(u j^k).val) a b)=
      (n:ℂ)*τn (powerWord (u j) w*(u j^k).val*e) := matrixTraceMap_test_entry τ hn _ a b
  simp_rw [hentry]
  simpa using htest.const_mul (n:ℂ)

end

end KKMatrixExpectation
end

end OAI
