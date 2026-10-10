import Mathlib
import OAI.Probability.CriticalPercolation.Modular.CappedDiscrepancy

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma incident_card_le (S : Set V) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card ≤ D) :
    (G.incidentEdges S).toFinset.card ≤ S.toFinset.card * D := by
  have he : (G.incidentEdges S).toFinset =
      S.toFinset.biUnion (fun v => (G.incidentEdges {v}).toFinset) := by
    ext e
    constructor
    · intro hh
      obtain ⟨v,hv,hev⟩ := Set.mem_toFinset.mp hh
      exact Finset.mem_biUnion.mpr ⟨v,Set.mem_toFinset.mpr hv,
        Set.mem_toFinset.mpr ⟨v,Set.mem_singleton v,hev⟩⟩
    · intro hh
      obtain ⟨v,hv,hev⟩ := Finset.mem_biUnion.mp hh
      obtain ⟨z,hz,he⟩ := Set.mem_toFinset.mp hev
      have hzv : z=v := Set.mem_singleton_iff.mp hz
      subst z
      exact Set.mem_toFinset.mpr ⟨v,Set.mem_toFinset.mp hv,he⟩
  rw [he]
  calc _ ≤ ∑ v ∈ S.toFinset, (G.incidentEdges {v}).toFinset.card := Finset.card_biUnion_le
       _ ≤ ∑ _v ∈ S.toFinset, D := Finset.sum_le_sum (fun v _ => hD v)
       _ = _ := by simp

omit [Fintype E] in
lemma rootMass_capped_eq (s : ℕ) (hs : 0<s) (ω : Set E) (v : V) :
    G.rootMass (cappedMass s) ω v = min (1/(s:ℝ)) (1/(G.clusterSize ω v : ℝ)) := by
  have hm : (0:ℝ)<G.clusterSize ω v := Nat.cast_pos.mpr (G.clusterSize_pos ω v)
  have hs' : (0:ℝ)<s := Nat.cast_pos.mpr hs
  unfold rootMass cappedMass
  by_cases hms : (G.clusterSize ω v : ℝ)/s ≤ 1
  · rw [min_eq_left hms,min_eq_left]
    · field_simp
    · apply (div_le_div_iff₀ hs' hm).mpr
      have hh := (div_le_one hs').mp hms
      simpa only [one_mul] using hh
  · have hh : (s:ℝ) ≤ G.clusterSize ω v := by
      have hh := le_of_lt (lt_of_not_ge hms)
      exact (one_le_div hs').mp hh
    rw [min_eq_right (le_of_lt (lt_of_not_ge hms)),min_eq_right]
    apply (div_le_div_iff₀ hm hs').mpr
    simpa only [one_mul] using hh

omit [Fintype E] in
lemma capped_root_le_normalized (s T D : ℕ) (hs : 0<s) (hT : 0<T) (hD : 1≤D)
    (ω : Set E) (v : V) (hTD : T ≤ D*G.clusterSize ω v) :
    G.rootMass (cappedMass s) ω v ≤ (D:ℝ)*min (1/(s:ℝ)) (1/(T:ℝ)) := by
  rw [G.rootMass_capped_eq s hs ω v,mul_min_of_nonneg _ _ (Nat.cast_nonneg D)]
  apply le_min
  · calc min (1/(s:ℝ)) (1/(G.clusterSize ω v : ℝ)) ≤ 1/(s:ℝ) := min_le_left _ _
         _ ≤ (D:ℝ)*(1/(s:ℝ)) := by
           exact le_mul_of_one_le_left (by positivity) (Nat.one_le_cast.mpr hD)
  · calc min (1/(s:ℝ)) (1/(G.clusterSize ω v : ℝ)) ≤ 1/(G.clusterSize ω v : ℝ) := min_le_right _ _
         _ ≤ (D:ℝ)*(1/(T:ℝ)) := by
           rw [mul_one_div]
           apply (div_le_div_iff₀ (Nat.cast_pos.mpr (G.clusterSize_pos ω v)) (Nat.cast_pos.mpr hT)).mpr
           simpa only [one_mul,Nat.cast_mul] using (Nat.cast_le.mpr hTD : (T:ℝ)≤ (D*G.clusterSize ω v : ℕ))

end CriticalPercolation.BondGraph
end
end
end

end OAI
