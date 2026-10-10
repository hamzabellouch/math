import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.GuardedNodeOriginal

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A Ω : Type*} [Fintype A] [Fintype Ω]

noncomputable def ambientTest : Option (Finset A)→Finset A
  | none => Finset.univ
  | some Y => Y

lemma not_mem_ambientTest (a : A) (Y : Option (Finset A)) :
    a∉ambientTest Y ↔ Excludes a Y := by cases Y <;> simp [ambientTest,Excludes]

lemma evictionFraction_ambient (X : Finset A) (Y : Option (Finset A)) :
    evictionFraction X (ambientTest Y)=∑a,uniformWeight X a*(if Excludes a Y then (1:ℝ) else 0) := by
  have hs : X\ambientTest Y=(Finset.univ.filter fun a=>Excludes a Y)∩X := by
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,
      true_and,not_mem_ambientTest,and_comm]
  unfold evictionFraction
  rw [hs,←sum_uniformWeight]
  simp only [Finset.sum_filter,mul_ite,mul_one,mul_zero]

lemma expected_ambient_eviction (p : Law Ω) (X : Finset A) (C : Ω→Option (Finset A)) :
    (∑ω,p ω*evictionFraction X (ambientTest (C ω)))=
      ∑a,uniformWeight X a*eventMass p (Finset.univ.filter fun ω=>Excludes a (C ω)) := by
  simp_rw [evictionFraction_ambient]
  simp only [eventMass,Finset.sum_filter,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> ring

theorem adaptive_ambient_eviction {B ι κ Θ Ξ : Type*}
    [Fintype B] [Fintype ι] [Fintype κ] [Fintype Θ] [Fintype Ξ]
    (R : A→B→Prop) (p : Law A) (r : Law B)
    (μ : Law ι) (ν : Law κ) (X : ι→Finset A) (Y : κ→Finset B)
    (prior : ι→κ→Law Θ) (tests : ι→κ→Θ→Law Ξ) (cap : Ξ→Option (Finset B))
    (B₀ L : ℝ) (hB₀ : 0≤B₀) (hL : 0≤L)
    (hX : ∀a,(∑i,μ i*uniformWeight (X i) a)≤L*p a)
    (hY : ∀b,(∑j,ν j*uniformWeight (Y j) b)≤L*r b)
    (hlocal : ∀i j θ b,eventMass (tests i j θ) (Finset.univ.filter fun ξ=>Excludes b (cap ξ))≤
      B₀*((((Finset.univ.filter fun a=>R a b)∩X i).card:ℝ)/(X i).card)) :
    (∑i,∑j,μ i*ν j*(∑θ,prior i j θ*(∑ξ,tests i j θ ξ*
      evictionFraction (Y j) (ambientTest (cap ξ)))))≤B₀*L^2*relationMass R p r := by
  simp_rw [expected_ambient_eviction]
  exact adaptive_rejection_average R p r μ ν X Y prior _ B₀ L hB₀ hL hX hY hlocal
end SharpRamseyFive.ReverseCap

end OAI
