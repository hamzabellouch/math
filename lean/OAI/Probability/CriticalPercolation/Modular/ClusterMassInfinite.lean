import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelContactMeasurability
import OAI.Probability.CriticalPercolation.Modular.CappedDiscrepancy

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

def size (ω : Set E) (v : V) : ℕ := (G.cluster ω v).ncard

def mass (s : ℕ) (ω : Set E) (v : V) : ℝ := cappedMass s (size G ω v) / size G ω v

def coefficient (p : ℝ) (ω : Set E) (e : E) : ℝ := if e ∈ ω then -(1-p)/p else 1

def rootSum (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  ∑' e, if e ∈ G.incidentEdges (G.cluster ω v) then coefficient p ω e else 0

def rootDiscrepancy (s : ℕ) (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  mass G s ω v * rootSum G p ω v

def rootAbsolute (s : ℕ) (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  mass G s ω v * |rootSum G p ω v|

def edgeMass (s : ℕ) (ω : Set E) (e : E) : ℝ :=
  cappedMass s (size G ω (G.ends e).out.1) +
    if (G.openGraph ω).Reachable (G.ends e).out.1 (G.ends e).out.2 then 0
    else cappedMass s (size G ω (G.ends e).out.2)

def edgeDiscrepancy (s : ℕ) (p : ℝ) (ω : Set E) (e : E) : ℝ :=
  coefficient p ω e * edgeMass G s ω e

lemma size_eq_of_reachable {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : size G ω u = size G ω v := by
  unfold size
  rw [G.cluster_eq_of_reachable h]

lemma mass_eq_of_reachable (s : ℕ) {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : mass G s ω u = mass G s ω v := by
  unfold mass
  rw [size_eq_of_reachable G h]

lemma mass_nonneg (s : ℕ) (ω : Set E) (v : V) : 0 ≤ mass G s ω v :=
  div_nonneg (cappedMass_nonneg _ _) (Nat.cast_nonneg _)

lemma cappedMass_le_one (s n : ℕ) : cappedMass s n ≤ 1 := min_le_right _ _

lemma mass_mul_size_le_one (s : ℕ) (ω : Set E) (v : V) :
    mass G s ω v * size G ω v ≤ 1 := by
  by_cases h : size G ω v = 0
  · simp [mass,h]
  · rw [mass,div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr h)]
    exact cappedMass_le_one _ _

lemma mass_eq_zero_of_infinite (s : ℕ) {ω : Set E} {v : V}
    (h : (G.cluster ω v).Infinite) : mass G s ω v = 0 := by
  simp [mass,size,h.ncard]

lemma coefficient_abs_le {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) (ω : Set E) (e : E) :
    |coefficient p ω e| ≤ 1/p := by
  unfold coefficient
  split_ifs
  · rw [abs_div,abs_neg,abs_of_nonneg (sub_nonneg.mpr hp.2.le),abs_of_pos hp.1]
    exact div_le_div_of_nonneg_right (by linarith [hp.1]) hp.1.le
  · rw [abs_one]
    exact (le_div_iff₀ hp.1).mpr (by linarith [hp.2])

lemma rootAbsolute_nonneg (s : ℕ) (p : ℝ) (ω : Set E) (v : V) :
    0 ≤ rootAbsolute G s p ω v := mul_nonneg (mass_nonneg G s ω v) (abs_nonneg _)

lemma abs_rootDiscrepancy (s : ℕ) (p : ℝ) (ω : Set E) (v : V) :
    |rootDiscrepancy G s p ω v| = rootAbsolute G s p ω v := by
  rw [rootDiscrepancy,abs_mul,abs_of_nonneg (mass_nonneg G s ω v)]
  rfl

lemma rootAbsolute_bound (hl : G.LocallyFinite) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (s : ℕ) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) (ω : Set E) (v : V) :
    rootAbsolute G s p ω v ≤ D/p := by
  by_cases hC : (G.cluster ω v).Finite
  · have hI := G.finite_incident hl hC
    have hsum : |rootSum G p ω v| ≤ (G.incidentEdges (G.cluster ω v)).ncard / p := by
      rw [rootSum,tsum_eq_sum (s := hI.toFinset) (fun e he => by
        simp only [hI.mem_toFinset] at he
        simp only [he,ite_false])]
      calc
        _ ≤ ∑ e∈hI.toFinset, |if e ∈ G.incidentEdges (G.cluster ω v) then coefficient p ω e else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ e∈hI.toFinset, |coefficient p ω e| := by
          apply Finset.sum_congr rfl
          intro e he
          rw [ite_eq_left (hI.mem_toFinset.mp he)]
        _ ≤ ∑ _e∈hI.toFinset, 1/p := Finset.sum_le_sum (fun e _ => coefficient_abs_le hp ω e)
        _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,Set.ncard_eq_toFinset_card _ hI]; ring
    calc
      _ ≤ mass G s ω v * ((G.incidentEdges (G.cluster ω v)).ncard / p) :=
        mul_le_mul_of_nonneg_left hsum (mass_nonneg G s ω v)
      _ ≤ mass G s ω v * ((size G ω v : ℝ)*D/p) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (by exact_mod_cast G.incident_ncard_le _ hC D (fun w _ => hD w)) hp.1.le)
          (mass_nonneg G s ω v)
      _ = (mass G s ω v * size G ω v)*(D/p) := by ring
      _ ≤ 1*(D/p) := mul_le_mul_of_nonneg_right (mass_mul_size_le_one G s ω v) (div_nonneg (Nat.cast_nonneg _) hp.1.le)
      _ = _ := one_mul _
  · rw [rootAbsolute,mass_eq_zero_of_infinite G s hC,zero_mul]
    exact div_nonneg (Nat.cast_nonneg _) hp.1.le

lemma edgeMass_nonneg (s : ℕ) (ω : Set E) (e : E) : 0 ≤ edgeMass G s ω e := by
  unfold edgeMass
  split_ifs
  · simpa using cappedMass_nonneg s (size G ω (G.ends e).out.1)
  · exact add_nonneg (cappedMass_nonneg _ _) (cappedMass_nonneg _ _)

lemma edgeMass_le_two (s : ℕ) (ω : Set E) (e : E) : edgeMass G s ω e ≤ 2 := by
  unfold edgeMass
  have h1 := cappedMass_le_one s (size G ω (G.ends e).out.1)
  have h2 := cappedMass_le_one s (size G ω (G.ends e).out.2)
  split_ifs <;> linarith

lemma edgeDiscrepancy_abs_le (s : ℕ) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1)
    (ω : Set E) (e : E) : |edgeDiscrepancy G s p ω e| ≤ 2/p := by
  rw [edgeDiscrepancy,abs_mul,abs_of_nonneg (edgeMass_nonneg G s ω e)]
  calc
    _ ≤ (1/p)*2 := mul_le_mul (coefficient_abs_le hp ω e) (edgeMass_le_two G s ω e)
      (edgeMass_nonneg G s ω e) (div_nonneg zero_le_one hp.1.le)
    _ = _ := by ring

variable [Countable V] [Countable E]

lemma measurable_size (v : V) : Measurable (fun ω => size G ω v) :=
  measurable_ncard.comp (G.measurable_cluster v)

lemma measurable_mass (s : ℕ) (v : V) : Measurable (fun ω => mass G s ω v) := by
  exact ((measurable_of_countable (fun n : ℕ => cappedMass s n / (n:ℝ))).comp
    (measurable_size G v))

omit [Countable E] in
lemma measurable_coefficient (p : ℝ) (e : E) : Measurable (fun ω => coefficient p ω e) :=
  measurable_const.ite (measurable_set_mem e).setOf measurable_const

lemma measurable_incidentCluster (v : V) (e : E) :
    MeasurableSet {ω : Set E | e ∈ G.incidentEdges (G.cluster ω v)} := by
  apply (Measurable.exists (fun w => (G.measurable_reachable v w).and measurable_const)).setOf

lemma measurable_rootSum (p : ℝ) (v : V) : Measurable (fun ω => rootSum G p ω v) := by
  exact Measurable.tsum (fun e => (measurable_coefficient p e).ite
    (measurable_incidentCluster G v e) measurable_const)

lemma measurable_rootAbsolute (s : ℕ) (p : ℝ) (v : V) :
    Measurable (fun ω => rootAbsolute G s p ω v) :=
  (measurable_mass G s v).mul (measurable_rootSum G p v).abs

lemma measurable_rootDiscrepancy (s : ℕ) (p : ℝ) (v : V) :
    Measurable (fun ω => rootDiscrepancy G s p ω v) :=
  (measurable_mass G s v).mul (measurable_rootSum G p v)

lemma measurable_edgeMass (s : ℕ) (e : E) : Measurable (fun ω => edgeMass G s ω e) := by
  have hm (v : V) := (measurable_of_countable (cappedMass s)).comp (measurable_size G v)
  exact (hm _).add (measurable_const.ite (G.measurable_reachable _ _).setOf (hm _))

lemma measurable_edgeDiscrepancy (s : ℕ) (p : ℝ) (e : E) :
    Measurable (fun ω => edgeDiscrepancy G s p ω e) :=
  (measurable_coefficient p e).mul (measurable_edgeMass G s e)

end CriticalPercolation.FiniteClusters
end
end

end OAI
