import OAI.Probability.BenjaminiSchramm.FullLayerProfile
import OAI.Probability.BenjaminiSchramm.BandMomentSummability

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma fullLayerCount_le_bandCount (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (i : ℤ) (x : V) (u : ℝ) (ω : Set E) :
    restrictedLayerCount G.ends Set.univ {y | G.adjustedLayerIndex a R u x y=i} ω x ≤
      G.adjustedBandCount a (R*((i : ℝ)-1)) (R*((i : ℝ)+1)) ω x := by
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : G.adjustedLayerIndex a R u x y=i ∧ Percolation.Conn G.ends (ω ∩ Set.univ) x y
  · have hh := G.adjustedLayerIndex_height_bounds a R u hR x y
    rw [hy.1] at hh
    have hc : y ∈ G.cluster ω x := by
      change y ∈ (criticalModel G.ends).cluster ω x
      rw [criticalModel_cluster]
      exact Percolation.conn_mono G.ends Set.inter_subset_left hy.2
    have ht : y ∈ G.cluster ω x ∧
        R*((i : ℝ)-1) ≤ G.orbitAdjustedHeight a x y ∧
          G.orbitAdjustedHeight a x y ≤ R*((i : ℝ)+1) :=
      ⟨hc,hh.1.le,hh.2.le⟩
    simp only [Set.mem_ofPred_eq,ite_eq_left hy,adjustedBandTransport,ite_eq_left ht,le_refl]
  · simp only [Set.mem_ofPred_eq,ite_eq_right hy]
    exact bot_le

variable [Countable V] [Countable E]

lemma expected_bandCount_le_intermediate_upLayerMoment
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (n : ℕ) (hn : 0 < n) (x : V) (l u : ℝ) (hlower : R*n ≤ l) :
    (∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p) ≤ G.adjustedUpLayerMoment a R p n x 0*C := by
  have he (ω : Set E) : G.adjustedBandCount a l u ω x =
      restrictedLayerCount G.ends Set.univ
        {y | l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u} ω x := by
    apply tsum_congr
    intro y
    have hc : y ∈ G.cluster ω x ↔ Percolation.Conn G.ends ω x y := by
      change y ∈ (criticalModel G.ends).cluster ω x ↔ _
      rw [criticalModel_cluster]
      rfl
    simp only [adjustedBandTransport,Set.inter_univ,Set.mem_ofPred_eq,hc]
    congr 1
    apply propext
    tauto
  simp_rw [he]
  let f := G.adjustedLayerIndex a R 0 x
  have hj : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → f w ≤ f v+1 ∧ f v ≤ f w+1 := by
    intro e v w hv hw
    have hh := G.adjustedLayerIndex_edge_jump hc hl a R 0 hR hjump x v w e hv hw
    change f v-1 ≤ f w ∧ f w ≤ f v+1 at hh
    exact ⟨hh.2,by omega⟩
  have hx : f x < (n : ℤ) := by simp only [f,G.adjustedLayerIndex_self]; exact_mod_cast hn
  have hA : ∀ y ∈ {v | l ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ u},
      (n : ℤ) ≤ f y := by
    intro y hy
    simp only [f,adjustedLayerIndex,add_zero,Int.floor_zero,sub_zero]
    apply Int.le_floor.mpr
    apply (le_div_iff₀ hR).mpr
    push_cast
    nlinarith [hy.1]
  exact first_layer_moment_bound_with_row G.ends p C hrow f hj Set.univ _ x n hx hA

theorem adjustedFullLayerMoment_negative_bound
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x) (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (m : ℝ) (hm : 0 < m) (ham : ∀ x, m ≤ a x)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (C : ℝ≥0∞)
    (hrow : ∀ z, (∑' y, G.law p {ω | Percolation.Conn G.ends ω z y}) ≤ C)
    (n : ℕ) (hn : 3 ≤ n) (x : V) (u : ℝ) :
    G.adjustedFullLayerMoment a R p (-(n : ℤ)) x u ≤
      ((ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r)))*
        ENNReal.ofReal (Real.exp (R*((n : ℝ)+1)))*(G.supAdjustedUpLayerMoment a R p (n-2)*C) := by
  let l := -(R*((n : ℝ)+1))
  let v := -(R*((n : ℝ)-1))
  have hmin : R*(n-2 : ℕ) ≤ -v := by
    dsimp [v]
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast
    nlinarith
  have hroot (r : V) : (∫⁻ ω, G.adjustedBandCount a (-v) (-l) ω r ∂G.law p) ≤
      G.supAdjustedUpLayerMoment a R p (n-2)*C :=
    (G.expected_bandCount_le_intermediate_upLayerMoment hc hl a R hR hjump p C hrow
      (n-2) (by omega) r (-v) (-l) hmin).trans
        (mul_le_mul' (G.adjustedUpLayerMoment_le_sup a R p (n-2) r 0) le_rfl)
  have hsum : (∑ r ∈ O.roots, ENNReal.ofReal (a r)*
      (∫⁻ ω, G.adjustedBandCount a (-v) (-l) ω r ∂G.law p)) ≤
        (∑ r ∈ O.roots, ENNReal.ofReal (a r))*(G.supAdjustedUpLayerMoment a R p (n-2)*C) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun r _ => mul_le_mul' le_rfl (hroot r)
  calc
    _ ≤ ∫⁻ ω, G.adjustedBandCount a l v ω x ∂G.law p := by
      have hleft : R*(((-(n : ℤ)) : ℝ)-1)=l := by
        dsimp [l]
        push_cast
        ring
      have hright : R*(((-(n : ℤ)) : ℝ)+1)=v := by
        dsimp [v]
        push_cast
        ring
      unfold adjustedFullLayerMoment
      apply lintegral_mono
      intro ω
      have hh := G.fullLayerCount_le_bandCount a R hR (-(n : ℤ)) x u ω
      simp only [Int.cast_neg] at hh
      rw [hleft,hright] at hh
      exact hh
    _ ≤ (ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r)*
        (∫⁻ ω, G.adjustedBandCount a l v ω r ∂G.law p)) :=
      G.expected_band_le_weighted_roots O a ha m hm ham p l v x
    _ ≤ (ENNReal.ofReal m)⁻¹*(ENNReal.ofReal (Real.exp (-l))*
        ((∑ r ∈ O.roots, ENNReal.ofReal (a r))*(G.supAdjustedUpLayerMoment a R p (n-2)*C))) :=
      mul_le_mul' le_rfl (((G.expected_adjustedBandCount_reciprocity O hc hl a hapos ha p l v).2).trans
        (mul_le_mul' le_rfl hsum))
    _ = _ := by dsimp only [l]; rw [neg_neg]; ring

end CriticalPercolation.BondGraph

end

end OAI
