import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.Leak
import OAI.Probability.CriticalPercolation.Criticality.SharpnessPhi

namespace OAI

section
section CurrentModule7
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

lemma finite_sum_connection_le [Fintype E] {p : ℝ} (hp : p ∈ Icc 0 1)
    (A : Finset V) (S : Set V) (hS : S.Finite) (o : V) (ho : o ∈ S)
    (M : ℝ) (hM : ∀ y : V, ∑ v ∈ A,
      probability p (fun ω => (G.openGraph ω).Reachable y v) ≤ M) :
    ∑ v ∈ A, probability p (fun ω => (G.openGraph ω).Reachable o v) ≤
      S.ncard + boundaryFlux G p o Sᶜ * M := by
  let f := fun x y => probability p (fun ω => (G.openGraph ω).Reachable x y)
  let c := fun e => p * probability p (fun ω =>
    boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e)
  have hc : ∀ e, 0 ≤ c e := fun e => mul_nonneg hp.1 (probability_nonneg hp _)
  have hout (v) (hv : v ∉ S) : f o v ≤ ∑ e, c e * f (cutOutside G S e) v :=
    simon_lieb G hp S o ho v hv
  calc
    _ ≤ ∑ v ∈ A, ((if v ∈ S then (1:ℝ) else 0) +
        ∑ e, c e * f (cutOutside G S e) v) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : v ∈ S
      · simp only [ite_eq_left hv]
        exact (probability_le_one hp _).trans (le_add_of_nonneg_right
          (Finset.sum_nonneg fun e _ => mul_nonneg (hc e) (probability_nonneg hp _)))
      · simpa only [ite_eq_right hv,zero_add] using hout v hv
    _ = (A.filter (· ∈ S)).card + ∑ e, c e * ∑ v ∈ A, f (cutOutside G S e) v := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [← Finset.mul_sum]
      congr 1
      simp
    _ ≤ S.ncard + (∑ e, c e) * M := by
      apply add_le_add
      · exact_mod_cast Set.ncard_le_ncard
          (show (↑(A.filter (· ∈ S)) : Set V) ⊆ S from fun v hv => (Finset.mem_filter.mp hv).2) hS
      · rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hM _) (hc e)
    _ = _ := by
      rw [boundaryFlux_eq_sum,Finset.mul_sum]

lemma restricted_boundaryFlux_le_phi (hl : G.LocallyFinite) (p : unitInterval)
    (S : Set V) (hS : S.Finite) (o : V) (K : Set E) (hK : K.Finite) :
    letI := hK.fintype
    boundaryFlux (G.restrictEdges K) (p : ℝ) o Sᶜ ≤ phi G p o S := by
  let := hK.fintype
  let F := fun e => (G.law p).real {ω | boundaryReach G Sᶜ
    (delete (G.openGraph ω) Sᶜ) o e}
  have hF : Summable F := summable_of_hasFiniteSupport
    ((finite_incident G hl hS).subset (boundary_measure_support G p o S))
  rw [boundaryFlux_eq_sum,phi]
  apply mul_le_mul_of_nonneg_left _ p.property.1
  calc
    _ ≤ ∑ e : K, F e.val := by
      apply Finset.sum_le_sum
      intro e _
      rw [finite_probability_restrict G p K hK]
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      change boundaryReach (G.restrictEdges K) Sᶜ
        (delete ((G.restrictEdges K).openGraph (Subtype.val ⁻¹' ω)) Sᶜ) o e at hω
      rw [G.restrictEdges_openGraph] at hω
      have hh : boundaryReach G Sᶜ (delete (G.openGraph (K ∩ ω)) Sᶜ) o e.val := hω
      obtain ⟨x,y,he,hx,hy,hr⟩ := hh
      have hdel : delete (G.openGraph (K ∩ ω)) Sᶜ ≤ delete (G.openGraph ω) Sᶜ :=
        fun _ _ hab => ⟨G.openGraph_mono inter_subset_right hab.1,hab.2⟩
      exact ⟨x,y,he,hx,hy,hr.mono hdel⟩
    _ ≤ ∑' e, F e := by
      simpa only [tsum_fintype,Function.comp_def] using
        (tsum_comp_le_tsum_of_inj hF (fun e => measureReal_nonneg)
          (Subtype.val_injective : Function.Injective (Subtype.val : K → E)))

end CriticalPercolation.Sharpness
end
end CurrentModule7

end

end OAI
