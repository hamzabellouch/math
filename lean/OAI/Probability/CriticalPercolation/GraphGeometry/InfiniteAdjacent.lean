import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.BallIncidence
import OAI.Probability.CriticalPercolation.Criticality.SubexponentialVolumes
import OAI.Probability.CriticalPercolation.Criticality.WitnessEvents
import OAI.Probability.CriticalPercolation.GraphGeometry.UniformGeometry
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteAdjacentMeasure

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma adjacent_bound_of_geometry (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (hg : G.SubexponentialGrowth)
    (C M D : ℕ) (hM : ∀ v, (G.vertexBall v C).ncard≤M)
    (hDpos : 1≤D) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hdense : ∀ u v, ∃ φ : G.Aut, φ.vertex u ∈ G.vertexBall v C)
    (p : unitInterval) (hp : (p:ℝ)∈Set.Ioo 0 1) (e : E) (K : ℕ) :
    (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)) ≤
      8*(M:ℝ)*((D:ℝ)/(p:ℝ)*(6/(2:ℝ)^K)) := by
  let a := (G.ends e).out.1
  let b := (G.ends e).out.2
  let δ := (G.law p).real (G.twoClusterEvent a b (4^K))
  let Q := (D:ℝ)/(p:ℝ)*(6/(2:ℝ)^K)
  have hQ : 0≤Q := by
    dsimp [Q]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hp.1.le) (by positivity)
  change δ ≤ 8*(M:ℝ)*Q
  by_cases hδ : 0<δ
  swap
  · exact (not_lt.mp hδ).trans (by positivity)
  obtain ⟨J,hJ,hJmass⟩ := G.exists_finite_witnessedTwoCluster p a b (4^K) hδ
  obtain ⟨W,hW⟩ := G.finite_bonds_in_ball hconnected a (hJ.insert e)
  have hJW : J⊆G.inducedEdges (G.vertexBall a W) := fun f hf => hW (Or.inr hf)
  have heW : e∈G.inducedEdges (G.vertexBall a W) := hW (Or.inl rfl)
  choose φ hφ using hdense a
  obtain ⟨n,_,hn⟩ := G.subexponential_ball_enlargement hlocal hg a (C+W) 0
  let B := G.vertexBall a n
  let S := G.vertexBall a (n+C+W)
  have hBf : B.Finite := G.vertexBall_finite hlocal a n
  have hSf : S.Finite := G.vertexBall_finite hlocal a _
  have hEf := G.finite_inducedEdges hlocal hSf
  let q (f : E) := (G.law p).real {ω | G.inducedEdges S∩ω ∈
    G.twoClusterEvent (G.ends f).out.1 (G.ends f).out.2 (4^K)}
  have hq : ∀ f, 0≤q f := fun _ => measureReal_nonneg
  have hmap : ∀ v∈hBf.toFinset, (φ v).edge e∈hEf.toFinset := by
    intro v hv
    apply hEf.mem_toFinset.mpr
    exact G.translated_bonds_in_ball a a v n C W (φ v) (hBf.mem_toFinset.mp hv)
      (hφ v) (Set.singleton_subset_iff.mpr heW) ⟨e,rfl,rfl⟩
  have hvbound : ∀ v∈hBf.toFinset, δ/2≤q ((φ v).edge e) := by
    intro v hv
    have hsub := G.translated_bonds_in_ball a a v n C W (φ v)
      (hBf.mem_toFinset.mp hv) (hφ v) hJW
    have hm := measureReal_mono (G.witnessedTwoCluster_subset_restrict hsub
      ((φ v).vertex a) ((φ v).vertex b) (4^K)) (μ := G.law p)
    rw [Aut.witnessedTwoCluster_real G (φ v) p J hJ a b (4^K)] at hm
    have hend : s((φ v).vertex a,(φ v).vertex b) =
        s((G.ends ((φ v).edge e)).out.1,(G.ends ((φ v).edge e)).out.2) := by
      calc
        _ = G.ends ((φ v).edge e) := by
          rw [(φ v).preserves,(G.ends e).out_eq.symm,Sym2.map_mk]
        _ = _ := (G.ends ((φ v).edge e)).out_eq.symm
    rw [G.twoClusterEvent_sym2 hend (4^K)] at hm
    exact hJmass.trans hm
  have hfib := G.orbit_edge_fibre_bound hlocal C M hM a e (Sym2.out_fst_mem _)
    φ hφ hBf.toFinset
  have havg := G.induced_averaged_adjacent hlocal p hp D hDpos hD S hSf K
  change (∑ f∈hEf.toFinset, q f) ≤ (S.ncard:ℝ)*Q at havg
  have hratio : S.ncard≤2*B.ncard := by simpa only [S,B,Nat.add_assoc] using hn
  have hsum : (B.ncard:ℝ)*(δ/2) ≤ (B.ncard:ℝ)*(4*(M:ℝ)*Q) := by
    calc
      _ = ∑ v∈hBf.toFinset, δ/2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Set.ncard_eq_toFinset_card B hBf]
      _ ≤ ∑ v∈hBf.toFinset, q ((φ v).edge e) := Finset.sum_le_sum hvbound
      _ ≤ (2*M:ℕ)*∑ f∈hEf.toFinset, q f :=
        sum_comp_le_fibre_bound hBf.toFinset hEf.toFinset (fun v => (φ v).edge e) q
          (2*M) hq hmap hfib
      _ ≤ (2*M:ℕ)*((S.ncard:ℝ)*Q) :=
        mul_le_mul_of_nonneg_left havg (Nat.cast_nonneg _)
      _ ≤ (2*M:ℕ)*(((2*B.ncard:ℕ):ℝ)*Q) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hratio) hQ) (Nat.cast_nonneg _)
      _ = _ := by push_cast; ring
  have hBpos : (0:ℝ)<B.ncard := Nat.cast_pos.mpr (G.vertexBall_ncard_pos hlocal a n)
  have hh := (mul_le_mul_iff_right₀ hBpos).mp hsum
  linarith

theorem subexponential_adjacent_bound (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) :
    ∃ A : ℝ, 0<A ∧ ∀ (p : unitInterval), (p:ℝ)∈Set.Ioo 0 1 → ∀ (e : E) (K : ℕ),
      (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)) ≤
        A/((p:ℝ)*(2:ℝ)^K) := by
  obtain ⟨C,hC⟩ := G.uniform_orbit_density_radius hconnected hquasi
  obtain ⟨M,hMpos,hM⟩ := G.uniform_positive_ball_bound hquasi C
  obtain ⟨D,hDpos,hD⟩ := G.uniform_incident_bound hquasi
  have hm : (0:ℝ)<M := by exact_mod_cast hMpos
  have hd : (0:ℝ)<D := by exact_mod_cast hDpos
  refine ⟨48*(M:ℝ)*D, by positivity, ?_⟩
  intro p hp e K
  have hh := G.adjacent_bound_of_geometry hconnected hlocal hg C M D hM hDpos hD hC p hp e K
  convert hh using 1
  ring

end CriticalPercolation.BondGraph
end
end
end

end OAI
