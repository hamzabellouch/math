import Mathlib
import OAI.Probability.CriticalPercolation.Modular.RandomTiltedTransport
import OAI.Probability.CriticalPercolation.Modular.ModularClusterCount
import OAI.Probability.CriticalPercolation.Modular.ModularIncidence

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.mem_ends_iff (φ : G.Aut) (e : E) (v : V) :
    φ.vertex v∈G.ends (φ.edge e) ↔ v∈G.ends e := by
  rw [φ.preserves]
  simp only [Sym2.mem_map,φ.vertex.injective.eq_iff,exists_eq_right]

lemma Aut.incident_cluster_iff (φ : G.Aut) (ω : Set E) (x : V) (e : E) :
    φ.edge e∈G.incidentEdges (G.cluster (φ.edge '' ω) (φ.vertex x)) ↔
      e∈G.incidentEdges (G.cluster ω x) := by
  rw [←φ.cluster_image]
  constructor
  · rintro ⟨v,⟨w,hw,rfl⟩,hwe⟩
    exact ⟨w,hw,(Aut.mem_ends_iff G φ e w).mp hwe⟩
  · rintro ⟨v,hv,hve⟩
    exact ⟨φ.vertex v,⟨v,hv,rfl⟩,(Aut.mem_ends_iff G φ e v).mpr hve⟩

lemma measurable_incidentCluster [Countable V] [Countable E] (x : V) (e : E) :
    Measurable (fun ω : Set E => e∈G.incidentEdges (G.cluster ω x)) :=
  Measurable.exists (fun v => (G.measurable_reachable x v).and measurable_const)

def normalizedSelectedIncidence (H : (Set E) → E → ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  (∑' e, if e∈G.incidentEdges (G.cluster ω x) then H ω e*G.bondWeight x e else 0)*
    G.reciprocalClusterMass ω x

def normalizedIncidenceTransport (H : (Set E) → E → ℝ≥0∞) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  ∑' e, if e∈G.incidentEdges (G.cluster ω x) ∧ y∈G.ends e then
    H ω e*G.stabilizerWeight x y*G.reciprocalClusterMass ω x else 0

lemma measurable_normalizedSelectedIncidence [Countable V] [Countable E]
    (H : (Set E) → E → ℝ≥0∞) (hm : ∀ e, Measurable (fun ω => H ω e)) (x : V) :
    Measurable (fun ω : Set E => G.normalizedSelectedIncidence H ω x) := by
  apply Measurable.mul _ (G.measurable_reciprocalClusterMass x)
  exact Measurable.tsum (fun e => ((hm e).mul_const _).ite
    (G.measurable_incidentCluster x e).setOf measurable_const)

lemma measurable_normalizedIncidenceTransport [Countable V] [Countable E]
    (H : (Set E) → E → ℝ≥0∞) (hm : ∀ e, Measurable (fun ω => H ω e)) (x y : V) :
    Measurable (fun ω : Set E => G.normalizedIncidenceTransport H ω x y) := by
  apply Measurable.tsum
  intro e
  exact (((hm e).mul_const _).mul (G.measurable_reciprocalClusterMass x)).ite
    ((G.measurable_incidentCluster x e).and measurable_const).setOf measurable_const

lemma Aut.normalizedIncidenceTransport (H : (Set E) → E → ℝ≥0∞)
    (ha : ∀ (φ : G.Aut) ω e, H (φ.edge '' ω) (φ.edge e)=H ω e)
    (φ : G.Aut) (ω : Set E) (x y : V) :
    G.normalizedIncidenceTransport H (φ.edge '' ω) (φ.vertex x) (φ.vertex y)=
      G.normalizedIncidenceTransport H ω x y := by
  unfold CriticalPercolation.BondGraph.normalizedIncidenceTransport
  rw [←φ.edge.tsum_eq]
  simp only [φ.incident_cluster_iff,φ.mem_ends_iff,ha,φ.stabilizerWeight,φ.reciprocalClusterMass]

lemma normalizedIncidenceTransport_out (H : (Set E) → E → ℝ≥0∞) (ω : Set E) (x : V) :
    (∑' y, G.normalizedIncidenceTransport H ω x y)=G.normalizedSelectedIncidence H ω x := by
  unfold normalizedIncidenceTransport normalizedSelectedIncidence
  rw [ENNReal.tsum_comm,←ENNReal.tsum_mul_right]
  apply tsum_congr
  intro e
  by_cases he : e∈G.incidentEdges (G.cluster ω x)
  · simp only [he,true_and,ite_true]
    rw [tsum_eq_sum (s := (G.ends e).toFinset) (fun y hy => by
      simpa only [Sym2.mem_toFinset] using (ite_eq_right (by simpa only [Sym2.mem_toFinset] using hy) :
        (if y∈G.ends e then H ω e*G.stabilizerWeight x y*G.reciprocalClusterMass ω x else 0)=0))]
    have heq : (∑ y∈(G.ends e).toFinset, if y∈G.ends e then
        H ω e*G.stabilizerWeight x y*G.reciprocalClusterMass ω x else 0) =
      ∑ y∈(G.ends e).toFinset, H ω e*G.stabilizerWeight x y*G.reciprocalClusterMass ω x := by
      apply Finset.sum_congr rfl
      intro y hy
      exact ite_eq_left (Sym2.mem_toFinset.mp hy)
    rw [heq,←Finset.sum_mul,←Finset.mul_sum]
    rfl
  · simp only [he,false_and,ite_false,tsum_zero,zero_mul]

lemma normalizedIncidenceTransport_in (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (H : (Set E) → E → ℝ≥0∞) (ω : Set E) (y : V) :
    (∑' x, G.normalizedIncidenceTransport H ω x y*G.stabilizerWeight y x)=
      ∑' e, if y∈G.ends e then H ω e*G.incidentClusterCount ω e else 0 := by
  unfold normalizedIncidenceTransport
  simp only [←ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro e
  by_cases hy : y∈G.ends e
  · simp only [hy,and_true,ite_true,incidentClusterCount,←ENNReal.tsum_mul_left]
    apply tsum_congr
    intro x
    by_cases he : e∈G.incidentEdges (G.cluster ω x)
    · simp only [ite_eq_left he]
      calc _ = (H ω e*G.reciprocalClusterMass ω x)*
          (G.stabilizerWeight x y*G.stabilizerWeight y x) := by ac_rfl
           _ = _ := by rw [G.stabilizerWeight_mul_reverse hc hl,mul_one]
    · simp only [ite_eq_right he,zero_mul,mul_zero]
  · simp only [hy,and_false,ite_false,zero_mul,tsum_zero]

lemma normalizedSelectedIncidence_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (H : (Set E) → E → ℝ≥0∞) (hH : ∀ ω e, H ω e≤1) (ω : Set E) (x : V) :
    G.normalizedSelectedIncidence H ω x≤(D*(2*K) : ℕ) := by
  unfold normalizedSelectedIncidence
  by_cases hm : G.modularMass x (G.cluster ω x)=∞
  · simp [reciprocalClusterMass,hm]
  · calc
      _ ≤ ((D*(2*K) : ℕ)*G.modularMass x (G.cluster ω x))*G.reciprocalClusterMass ω x := by
        apply mul_le_mul_left
        apply le_trans _ (G.weighted_incidence_le hc hl D K hD hK x _)
        apply ENNReal.tsum_le_tsum
        intro e
        split_ifs
        · exact mul_le_of_le_one_left zero_le (hH ω e)
        · rfl
      _ = _ := by
        rw [reciprocalClusterMass,mul_assoc,ENNReal.mul_inv_cancel
          (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm,mul_one]

theorem expected_normalizedSelectedIncidence [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (H : (Set E) → E → ℝ≥0∞)
    (hm : ∀ e, Measurable (fun ω => H ω e))
    (ha : ∀ (φ : G.Aut) ω e, H (φ.edge '' ω) (φ.edge e)=H ω e) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, G.normalizedSelectedIncidence H ω x ∂G.law p)=
      ∑ y∈(G.orbitRepresentatives hq).roots, ∫⁻ ω,
        ∑' e, if y∈G.ends e then H ω e*G.incidentClusterCount ω e else 0 ∂G.law p := by
  simpa only [G.normalizedIncidenceTransport_out,G.normalizedIncidenceTransport_in hc hl] using
    OrbitRepresentatives.random_tilted_transport G (G.orbitRepresentatives hq) hc hl p
      (G.normalizedIncidenceTransport H) (G.measurable_normalizedIncidenceTransport H hm)
      (fun φ => Aut.normalizedIncidenceTransport G H ha φ)

end CriticalPercolation.BondGraph
end
end

end OAI
