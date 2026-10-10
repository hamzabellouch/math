import OAI.Probability.BenjaminiSchramm.GhostTiltedTransport
import OAI.Probability.CriticalPercolation.Modular.ModularIncidence

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ghostBondWeight (o : V) (e : E) : ℝ≥0∞ :=
  ∑ v ∈ (G.ends e).toFinset, G.stabilizerWeight o v ^ (3 / 8 : ℝ)

def threeEighthMass (o : V) (S : Set V) : ℝ≥0∞ :=
  ∑' v, if v ∈ S then G.stabilizerWeight o v ^ (3 / 8 : ℝ) else 0

lemma ghostBondWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o v : V) (e : E) : G.ghostBondWeight o e =
      G.stabilizerWeight o v ^ (3 / 8 : ℝ) * G.ghostBondWeight v e := by
  unfold ghostBondWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [G.stabilizerWeight_change_base hc hl o v y,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

lemma ghostBondWeight_le_at_end (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard ≤ K) (o v : V) (e : E)
    (hv : v ∈ G.ends e) :
    G.ghostBondWeight o e ≤ (2 * (K : ℝ≥0∞) ^ (3 / 8 : ℝ)) *
      G.stabilizerWeight o v ^ (3 / 8 : ℝ) := by
  rw [G.ghostBondWeight_change_base hc hl o v e]
  have hsum : G.ghostBondWeight v e ≤ 2 * (K : ℝ≥0∞) ^ (3 / 8 : ℝ) := by
    calc
      _ ≤ ∑ y ∈ (G.ends e).toFinset, (K : ℝ≥0∞) ^ (3 / 8 : ℝ) := by
        apply Finset.sum_le_sum
        intro y hy
        have hy' := Sym2.mem_toFinset.mp hy
        exact ENNReal.rpow_le_rpow
          (G.stabilizerWeight_le_ball_bound hc hl K hK
            (G.common_bond_ball_one hv hy') (G.common_bond_ball_one hy' hv)) (by norm_num)
      _ = (G.ends e).toFinset.card * (K : ℝ≥0∞) ^ (3 / 8 : ℝ) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul' _ le_rfl
        exact_mod_cast (show (G.ends e).toFinset.card ≤ 2 by
          rw [Sym2.card_toFinset]; split_ifs <;> omega)
  exact (mul_le_mul' le_rfl hsum).trans_eq (mul_comm _ _)

lemma weighted_ghost_incidence_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hK : ∀ v, (G.vertexBall v 1).ncard ≤ K) (o : V) (S : Set V) :
    (∑' e, if e ∈ G.incidentEdges S then G.ghostBondWeight o e else 0) ≤
      ((D : ℝ≥0∞) * (2 * (K : ℝ≥0∞) ^ (3 / 8 : ℝ))) * G.threeEighthMass o S := by
  let B := (2 : ℝ≥0∞) * (K : ℝ≥0∞) ^ (3 / 8 : ℝ)
  calc
    _ ≤ ∑' e : E, ∑' v : V, if v ∈ S ∧ v ∈ G.ends e then G.ghostBondWeight o e else 0 := by
      apply ENNReal.tsum_le_tsum
      intro e
      by_cases he : e ∈ G.incidentEdges S
      · rw [ite_eq_left he]
        obtain ⟨v,hv,hve⟩ := he
        simpa only [ite_eq_left (show v ∈ S ∧ v ∈ G.ends e from ⟨hv,hve⟩)] using
          ENNReal.le_tsum v (f := fun v => if v ∈ S ∧ v ∈ G.ends e then G.ghostBondWeight o e else 0)
      · rw [ite_eq_right he]
        exact bot_le
    _ = ∑' v : V, ∑' e : E, if v ∈ S ∧ v ∈ G.ends e then G.ghostBondWeight o e else 0 :=
      ENNReal.tsum_comm
    _ ≤ ∑' v : V, if v ∈ S then (D : ℝ≥0∞) * B * G.stabilizerWeight o v ^ (3 / 8 : ℝ) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro v
      by_cases hv : v ∈ S
      · simp only [hv,true_and,ite_true]
        have hf : (G.incidentEdges {v}).Finite := by simpa [incidentEdges] using hl v
        have hm (e : E) : e ∈ G.incidentEdges {v} ↔ v ∈ G.ends e := by simp [incidentEdges]
        rw [tsum_eq_sum (s := hf.toFinset) (fun e he => by
          simp only [hf.mem_toFinset,hm] at he
          exact ite_eq_right he)]
        calc
          _ ≤ ∑ e ∈ hf.toFinset, B * G.stabilizerWeight o v ^ (3 / 8 : ℝ) := by
            apply Finset.sum_le_sum
            intro e he
            rw [ite_eq_left ((hm e).mp (hf.mem_toFinset.mp he))]
            exact G.ghostBondWeight_le_at_end hc hl K hK o v e
              ((hm e).mp (hf.mem_toFinset.mp he))
          _ = ((G.incidentEdges {v}).ncard : ℝ≥0∞) *
              (B * G.stabilizerWeight o v ^ (3 / 8 : ℝ)) := by
            simp only [Finset.sum_const,nsmul_eq_mul,← Set.ncard_eq_toFinset_card _ hf]
          _ ≤ (D : ℝ≥0∞) * (B * G.stabilizerWeight o v ^ (3 / 8 : ℝ)) := by
            apply mul_le_mul' _ le_rfl
            exact_mod_cast hD v
          _ = _ := (mul_assoc _ _ _).symm
      · simp only [hv,false_and,ite_false,tsum_zero,le_refl]
    _ = _ := by
      unfold threeEighthMass
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      split_ifs <;> simp [B]

lemma ghostWeightedCount_eq (h : ℝ) (ω : Set E) (x : V) :
    G.ghostWeightedCount h ω x =
      Percolation.BenjaminiSchramm.ghostAvoid h (G.quarterTiltedMass ω x) *
        G.threeEighthMass x (G.cluster ω x) := by
  unfold ghostWeightedCount threeEighthMass
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro v
  split_ifs <;> simp_all [cluster]

theorem expected_ghost_boundary_weight_le [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) {h : ℝ} (hh : 0 ≤ h)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hK : ∀ v, (G.vertexBall v 1).ncard ≤ K) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots, ∫⁻ ω,
      Percolation.BenjaminiSchramm.ghostAvoid h (G.quarterTiltedMass ω x) *
        (∑' e, if e ∈ G.incidentEdges (G.cluster ω x) then G.ghostBondWeight x e else 0)
      ∂G.law p) ≤
      ((D : ℝ≥0∞) * (2 * (K : ℝ≥0∞) ^ (3 / 8 : ℝ))) *
        (2 * ∑ x ∈ (G.orbitRepresentatives hq).roots, ∫⁻ ω,
          Percolation.BenjaminiSchramm.ghostAvoid h (G.quarterTiltedMass ω x) *
            G.quarterTiltedMass ω x ∂G.law p) := by
  let B := (D : ℝ≥0∞) * (2 * (K : ℝ≥0∞) ^ (3 / 8 : ℝ))
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top))
  calc
    _ ≤ ∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, B * G.ghostWeightedCount h ω x ∂G.law p := by
      apply Finset.sum_le_sum
      intro x _
      apply lintegral_mono
      intro ω
      dsimp only
      rw [G.ghostWeightedCount_eq]
      exact (mul_le_mul' le_rfl
        (G.weighted_ghost_incidence_le hc hl D K hD hK x (G.cluster ω x))).trans_eq
          (by dsimp [B]; ac_rfl)
    _ = B * ∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, G.ghostWeightedCount h ω x ∂G.law p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      exact lintegral_const_mul' _ _ hB
    _ ≤ _ := mul_le_mul' le_rfl (G.expected_ghostWeightedCount_le hc hl hq p hh)

end CriticalPercolation.BondGraph

end

end OAI
