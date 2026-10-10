import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def bondWeight (o : V) (e : E) : ℝ≥0∞ := ∑ v ∈ (G.ends e).toFinset, G.stabilizerWeight o v

lemma bondWeight_ne_top (o : V) (e : E) : G.bondWeight o e ≠ ∞ := by
  apply ENNReal.sum_ne_top.mpr
  intro v hv
  exact G.stabilizerWeight_ne_top o v

lemma bondWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (e : E) : G.bondWeight o e = G.stabilizerWeight o a * G.bondWeight a e := by
  unfold bondWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact G.stabilizerWeight_change_base hc hl o a v

lemma Aut.bondWeight (φ : G.Aut) (o : V) (e : E) :
    G.bondWeight (φ.vertex o) (φ.edge e) = G.bondWeight o e := by
  unfold CriticalPercolation.BondGraph.bondWeight
  rw [φ.preserves]
  have himg : (Sym2.map φ.vertex (G.ends e)).toFinset = (G.ends e).toFinset.image φ.vertex := by
    ext v
    simp only [Sym2.mem_toFinset,Sym2.mem_map,Finset.mem_image]
  rw [himg,Finset.sum_image]
  · simp only [Aut.stabilizerWeight]
  · exact fun _ _ _ _ h => φ.vertex.injective h

lemma incidence_stabilizerOrbit_subset_ball (v w : V) (n : ℕ) (hw : w∈G.vertexBall v n) :
    G.stabilizerOrbit v w ⊆ G.vertexBall v n := by
  intro z hz
  obtain ⟨φ,hv,hwz⟩ := G.mem_stabilizerOrbit.mp hz
  have h := (Aut.vertexBall_mem G φ v w n).mpr hw
  simpa only [hv,hwz] using h

lemma stabilizerWeight_le_ball_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) {v w : V}
    (_hw : w∈G.vertexBall v 1) (hv : v∈G.vertexBall w 1) :
    G.stabilizerWeight v w ≤ K := by
  unfold stabilizerWeight modularRatio
  apply ENNReal.ofReal_le_of_le_toReal
  simp only [ENNReal.toReal_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl v w))).mpr
  have hnum : G.suborbitCard w v ≤ K :=
    (Set.ncard_le_ncard (G.incidence_stabilizerOrbit_subset_ball w v 1 hv)
      (G.vertexBall_finite hl w 1)).trans (hK w)
  have hden : (1:ℝ)≤G.suborbitCard v w := by exact_mod_cast G.suborbitCard_pos hc hl v w
  exact (Nat.cast_le.mpr hnum).trans (by nlinarith [show (0:ℝ)≤K by positivity])

lemma common_bond_ball_one {v w : V} {e : E} (hv : v∈G.ends e) (hw : w∈G.ends e) :
    w∈G.vertexBall v 1 := by
  by_cases he : v=w
  · subst w
    exact G.mem_vertexBall_self v 1
  · apply G.vertexBall_step (G.mem_vertexBall_self v 0)
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨?_,he⟩
    refine ⟨e,Set.mem_univ e,?_⟩
    exact (Sym2.mem_and_mem_iff he).mp ⟨hv,hw⟩

lemma bondWeight_le_at_end (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (o v : V) (e : E)
    (hv : v∈G.ends e) : G.bondWeight o e ≤ (2*K : ℕ)*G.stabilizerWeight o v := by
  rw [G.bondWeight_change_base hc hl o v]
  have hsum : G.bondWeight v e ≤ (2*K : ℕ) := by
    calc
      _ ≤ ∑ w∈(G.ends e).toFinset, (K : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro w hw
        have hw' : w∈G.ends e := Sym2.mem_toFinset.mp hw
        exact G.stabilizerWeight_le_ball_bound hc hl K hK
          (G.common_bond_ball_one hv hw') (G.common_bond_ball_one hw' hv)
      _ = ((G.ends e).toFinset.card * K : ℕ) := by simp [nsmul_eq_mul]
      _ ≤ (2*K : ℕ) := by
        have hh : (G.ends e).toFinset.card≤2 := by
          rw [Sym2.card_toFinset]
          split_ifs <;> omega
        exact_mod_cast Nat.mul_le_mul_right K hh
  calc _ ≤ G.stabilizerWeight o v * (2*K : ℕ) := by gcongr
       _ = _ := mul_comm _ _

lemma weighted_incidence_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (o : V) (S : Set V) :
    (∑' e : E, if e∈G.incidentEdges S then G.bondWeight o e else 0) ≤
      (D*(2*K) : ℕ)*G.modularMass o S := by
  calc
    _ ≤ ∑' e : E, ∑' v : V, if v∈S ∧ v∈G.ends e then G.bondWeight o e else 0 := by
      apply ENNReal.tsum_le_tsum
      intro e
      by_cases he : e∈G.incidentEdges S
      · rw [ite_eq_left he]
        obtain ⟨v,hv,hve⟩ := he
        simpa only [ite_eq_left (show v∈S ∧ v∈G.ends e from ⟨hv,hve⟩)] using
          (ENNReal.le_tsum v (f := fun v => if v∈S ∧ v∈G.ends e then G.bondWeight o e else 0))
      · simp only [ite_eq_right he]; exact zero_le
    _ = ∑' v : V, ∑' e : E, if v∈S ∧ v∈G.ends e then G.bondWeight o e else 0 :=
      ENNReal.tsum_comm
    _ ≤ ∑' v : V, if v∈S then (D*(2*K) : ℕ)*G.stabilizerWeight o v else 0 := by
      apply ENNReal.tsum_le_tsum
      intro v
      by_cases hv : v∈S
      · simp only [hv,true_and,ite_true]
        have hf : (G.incidentEdges {v}).Finite := by simpa [incidentEdges] using hl v
        have hm (e : E) : e∈G.incidentEdges {v} ↔ v∈G.ends e := by
          simp [incidentEdges]
        have ht : (∑' e : E, if v∈G.ends e then G.bondWeight o e else 0) =
            ∑ e∈hf.toFinset, G.bondWeight o e := by
          rw [tsum_eq_sum (s := hf.toFinset) (fun e he => by
            simp only [hf.mem_toFinset,hm] at he
            exact ite_eq_right he)]
          apply Finset.sum_congr rfl
          intro e he
          exact ite_eq_left ((hm e).mp (hf.mem_toFinset.mp he))
        rw [ht]
        calc
          _ ≤ ∑ e∈hf.toFinset, (2*K : ℕ)*G.stabilizerWeight o v := by
            apply Finset.sum_le_sum
            intro e he
            exact G.bondWeight_le_at_end hc hl K hK o v e ((hm e).mp (hf.mem_toFinset.mp he))
          _ = ((G.incidentEdges {v}).ncard : ℝ≥0∞)*((2*K : ℕ)*G.stabilizerWeight o v) := by
            simp only [Finset.sum_const,nsmul_eq_mul,←Set.ncard_eq_toFinset_card _ hf]
          _ ≤ (D : ℝ≥0∞)*((2*K : ℕ)*G.stabilizerWeight o v) := by
            gcongr
            exact_mod_cast hD v
          _ = _ := by simp only [Nat.cast_mul,mul_assoc]
      · simp only [hv,false_and,ite_false,tsum_zero,le_refl]
    _ = _ := by
      unfold modularMass
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      split_ifs <;> simp

end CriticalPercolation.BondGraph
end
end

end OAI
