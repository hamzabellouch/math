import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.QueryBand
import OAI.Probability.CriticalPercolation.Exploration.IncidenceIdentity
import OAI.Probability.CriticalPercolation.Exploration.QueryNormalized
import OAI.Probability.CriticalPercolation.Modular.ClusterMassInfinite

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.FiniteClusters
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

lemma size_pos {ω : Set E} {v : V} (hC : (G.cluster ω v).Finite) :
    0 < size G ω v := (Set.ncard_pos hC).mpr ⟨v,SimpleGraph.Reachable.refl v⟩

lemma mass_eq_min (s : ℕ) (hs : 0<s) (ω : Set E) (v : V)
    (hC : (G.cluster ω v).Finite) :
    mass G s ω v = min (1/(s:ℝ)) (1/(size G ω v : ℝ)) := by
  have hm : (0:ℝ)<size G ω v := Nat.cast_pos.mpr (size_pos G hC)
  have hs' : (0:ℝ)<s := Nat.cast_pos.mpr hs
  unfold mass cappedMass
  by_cases hms : (size G ω v : ℝ)/s ≤ 1
  · rw [min_eq_left hms,min_eq_left]
    · field_simp
    · apply (div_le_div_iff₀ hs' hm).mpr
      have hh := (div_le_one hs').mp hms
      simpa only [one_mul] using hh
  · have hh : (s:ℝ) ≤ size G ω v := (one_le_div hs').mp (le_of_lt (lt_of_not_ge hms))
    rw [min_eq_right (le_of_lt (lt_of_not_ge hms)),min_eq_right]
    apply (div_le_div_iff₀ hm hs').mpr
    simpa only [one_mul] using hh

lemma mass_le_normalized (s T D : ℕ) (hs : 0<s) (hT : 0<T) (hD : 1≤D)
    (ω : Set E) (v : V) (hC : (G.cluster ω v).Finite) (hTD : T ≤ D*size G ω v) :
    mass G s ω v ≤ (D:ℝ)*min (1/(s:ℝ)) (1/(T:ℝ)) := by
  rw [mass_eq_min G s hs ω v hC,mul_min_of_nonneg _ _ (Nat.cast_nonneg D)]
  apply le_min
  · exact (min_le_left _ _).trans
      (le_mul_of_one_le_left (by positivity) (Nat.one_le_cast.mpr hD))
  · apply (min_le_right _ _).trans
    rw [mul_one_div]
    apply (div_le_div_iff₀ (Nat.cast_pos.mpr (size_pos G hC)) (Nat.cast_pos.mpr hT)).mpr
    simpa only [one_mul,Nat.cast_mul] using (Nat.cast_le.mpr hTD : (T:ℝ)≤(D*size G ω v : ℕ))

variable [Fintype E]

lemma rootSum_eq_centered (p : ℝ) (hp : p≠0) (ω : Set E) (v : V) :
    rootSum G p ω v = -(IncidenceSearch.tree G v).centeredSum p ω / p := by
  rw [IncidenceSearch.tree_centered,rootSum,tsum_fintype,← Finset.sum_neg_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e∈G.incidentEdges (G.cluster ω v)
  · by_cases hω : e∈ω <;> simp [he,hω,hp,coefficient]
  · simp [he]

lemma finite_rootAbsolute_expect (p : ℝ) (hp : p ∈ Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p ∅) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D) (K : ℕ) (v : V) :
    expect w (fun ω => rootAbsolute G (4^K) p ω v) ≤ (D:ℝ)/p*(6/(2:ℝ)^K) := by
  let t := IncidenceSearch.tree G v
  have hwel (ω : Set E) : rootAbsolute G (4^K) p ω v ≤
      (D:ℝ)/p * (|t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) := by
    rw [rootAbsolute,rootSum_eq_centered G p hp.1.ne' ω v,abs_div,abs_neg,abs_of_pos hp.1]
    by_cases hT : t.queryCount ω = 0
    · rw [t.centeredSum_eq_zero_of_count ω hT p]
      simp
    · have hC := G.finite_cluster_of_finite_bonds (Set.toFinite ω) v
      have hTD : t.queryCount ω ≤ D*size G ω v := by
        rw [IncidenceSearch.tree_count,← Set.ncard_eq_toFinset_card']
        simpa only [size,mul_comm] using G.incident_ncard_le _ hC D (fun w _ => hD w)
      have hh := mass_le_normalized G (4^K) (t.queryCount ω) D
        (by positivity) (Nat.pos_of_ne_zero hT) hDpos ω v hC hTD
      have hh' : mass G (4^K) ω v ≤ (D:ℝ)*min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ)) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
      calc
        _ ≤ ((D:ℝ)*min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) *
            (|t.centeredSum p ω|/p) := mul_le_mul_of_nonneg_right hh'
              (div_nonneg (abs_nonneg _) hp.1.le)
        _ = _ := by ring
  calc
    _ ≤ expect w (fun ω => (D:ℝ)/p *
        (|t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ)))) := expect_mono hn hwel
    _ = (D:ℝ)/p * expect w (fun ω =>
        |t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) := expect_const_mul _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (t.normalized_centered_bound ∅ (IncidenceSearch.tree_valid G v) p
        ⟨hp.1.le,hp.2.le⟩ w hw hn hf K) (div_nonneg (Nat.cast_nonneg D) hp.1.le)

lemma finite_rootAbsolute_integral (p : unitInterval) (hp : (p:ℝ) ∈ Ioo 0 1)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D) (K : ℕ) (v : V) :
    (∫ ω, rootAbsolute G (4^K) p ω v ∂G.law p) ≤ (D:ℝ)/p*(6/(2:ℝ)^K) := by
  rw [BondGraph.law,← BernoulliProduct.law_const,BernoulliProduct.integral_law_eq_expect]
  exact finite_rootAbsolute_expect G p hp _
    (fun _ => BernoulliProduct.bitWeight_sum p) (fun _ => BernoulliProduct.bitWeight_nonneg p)
    (fun _ _ => ⟨by simp [BernoulliProduct.bitWeight],by simp [BernoulliProduct.bitWeight]⟩)
    D hDpos hD K v

end CriticalPercolation.FiniteClusters
end
end

end OAI
