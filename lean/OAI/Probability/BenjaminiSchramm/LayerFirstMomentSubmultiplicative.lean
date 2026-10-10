import OAI.Probability.BenjaminiSchramm.LayerFirstMoments
import OAI.Probability.BenjaminiSchramm.IntegerLayerFirstVisit

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma adjustedUpLayerMoment_first_visit (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (m n : ℕ) (hm : 0 < m) (x : V) (u : ℝ) :
    G.adjustedUpLayerMoment a R p (m+n) x u ≤
      G.adjustedUpLayerMoment a R p m x u * G.supAdjustedUpLayerMoment a R p n := by
  let f := G.adjustedLayerIndex a R u x
  let I := Percolation.internalEdges G.ends {v | f v ≤ (m+n : ℕ)}
  let A := {v | f v = (m+n : ℕ)}
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → f w ≤ f v+1 ∧ f v ≤ f w+1 := by
    intro e v w hv hw
    have hh := G.adjustedLayerIndex_edge_jump hc hl a R u hR hjump x v w e hv hw
    change f v-1 ≤ f w ∧ f w ≤ f v+1 at hh
    exact ⟨hh.2,by omega⟩
  have hx : f x < (m : ℤ) := by simp only [f,G.adjustedLayerIndex_self]; exact_mod_cast hm
  have hA : ∀ y ∈ A, (m : ℤ) ≤ f y := by
    intro y hy
    change f y = (m+n : ℕ) at hy
    rw [hy]
    exact_mod_cast Nat.le_add_right m n
  have hfirst := integer_first_layer_moment_bound G.ends f hj I A p x m hx hA
  have hI : I ∩ Percolation.internalEdges G.ends {v | f v ≤ (m : ℤ)} =
      Percolation.internalEdges G.ends {v | f v ≤ (m : ℤ)} := by
    apply Set.inter_eq_right.mpr
    apply Percolation.internalEdges_mono G.ends
    intro v hv
    change f v ≤ (m : ℤ) at hv
    change f v ≤ (m+n : ℕ)
    exact hv.trans (by exact_mod_cast Nat.le_add_right m n)
  rw [hI] at hfirst
  have hcont (z : V) (hz : f z=(m : ℤ)) :
      (∫⁻ ω, restrictedLayerCount G.ends I A ω z ∂G.law p) ≤ G.supAdjustedUpLayerMoment a R p n := by
    let v := G.orbitAdjustedHeight a x z/R+u
    have hidx (y : V) : f y = (m : ℤ)+G.adjustedLayerIndex a R v z y := by
      simpa only [f,hz] using G.adjustedLayerIndex_change_base hc hl a R u x z y
    have hDom : {y : V | f y ≤ (m+n : ℕ)} =
        {y | G.adjustedLayerIndex a R v z y ≤ (n : ℤ)} := by
      ext y
      change f y ≤ (m+n : ℕ) ↔ G.adjustedLayerIndex a R v z y ≤ (n : ℤ)
      rw [hidx]
      push_cast
      omega
    have hTar : A = {y | G.adjustedLayerIndex a R v z y=(n : ℤ)} := by
      ext y
      change f y = (m+n : ℕ) ↔ G.adjustedLayerIndex a R v z y=(n : ℤ)
      rw [hidx]
      push_cast
      omega
    change (∫⁻ ω, restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {y | f y ≤ (m+n : ℕ)}) A ω z ∂G.law p) ≤ _
    rw [hDom,hTar]
    exact G.adjustedUpLayerMoment_le_sup a R p n z v
  calc
    _ ≤ ∑' z, (if f z=(m : ℤ) then G.law p
        {ω | Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends {v | f v ≤ (m : ℤ)}) x z} else 0) *
          (∫⁻ ω, restrictedLayerCount G.ends I A ω z ∂G.law p) := hfirst
    _ ≤ ∑' z, (if f z=(m : ℤ) then G.law p
        {ω | Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends {v | f v ≤ (m : ℤ)}) x z} else 0) *
          G.supAdjustedUpLayerMoment a R p n := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : f z=(m : ℤ)
      · exact mul_le_mul' le_rfl (hcont z hz)
      · simp only [ite_eq_right hz,zero_mul,le_refl]
    _ = _ := by
      rw [ENNReal.tsum_mul_right]
      congr 1
      rw [adjustedUpLayerMoment]
      change _ = ∫⁻ ω, restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | f v ≤ (m : ℤ)}) {v | f v=(m : ℤ)} ω x ∂Percolation.law p
      rw [lintegral_restrictedLayerCount]
      apply tsum_congr
      intro z
      by_cases hz : f z=(m : ℤ) <;>
        simp only [Set.mem_ofPred_eq,hz,ite_true,ite_false,law,Percolation.law]

theorem supAdjustedUpLayerMoment_submultiplicative [Nonempty V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (m n : ℕ) :
    G.supAdjustedUpLayerMoment a R p (m+n) ≤
      G.supAdjustedUpLayerMoment a R p m*G.supAdjustedUpLayerMoment a R p n := by
  have hzero : (1 : ℝ≥0∞) ≤ G.supAdjustedUpLayerMoment a R p 0 :=
    (G.adjustedUpLayerMoment_zero_ge_one a R p (Classical.arbitrary V) 0).trans
      (G.adjustedUpLayerMoment_le_sup a R p 0 _ 0)
  by_cases hm : m=0
  · rw [hm,zero_add]
    exact (one_mul _).symm.le.trans (mul_le_mul' hzero le_rfl)
  · apply iSup_le
    intro x
    apply iSup_le
    intro u
    exact (G.adjustedUpLayerMoment_first_visit hc hl a R hR hjump p m n
      (Nat.pos_of_ne_zero hm) x u).trans (mul_le_mul' (G.adjustedUpLayerMoment_le_sup a R p m x u) le_rfl)

theorem subcritical_supAdjustedUpLayerMoment_bound [Nonempty V]
    (hl : Percolation.LocallyFinite G.ends) (hq : Percolation.QuasiTransitive G.ends)
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (hp : p < Percolation.pc G.ends) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, G.supAdjustedUpLayerMoment a R p n ≤ C := by
  obtain ⟨C,_hC,hrow⟩ := Percolation.subcritical_ennreal_row_bound G.ends hl hq p hp
  refine ⟨ENNReal.ofReal C,ENNReal.ofReal_lt_top,fun n => ?_⟩
  apply iSup_le
  intro x
  apply iSup_le
  intro u
  apply le_trans _ (hrow x)
  rw [adjustedUpLayerMoment]
  change (∫⁻ ω, restrictedLayerCount G.ends _ _ ω x ∂Percolation.law p) ≤ _
  rw [lintegral_restrictedLayerCount]
  apply ENNReal.tsum_le_tsum
  intro y
  split_ifs
  · exact measure_mono (fun ω hω => Percolation.conn_mono G.ends Set.inter_subset_left hω)
  · exact bot_le

end CriticalPercolation.BondGraph

end

end OAI
