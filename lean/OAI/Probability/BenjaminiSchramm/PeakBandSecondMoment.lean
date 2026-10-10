import OAI.Probability.BenjaminiSchramm.PeakBandTransport
import OAI.Probability.BenjaminiSchramm.LayerProfileAtRate

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma peakDownBandCount_le_four_layers (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (n : ℕ) (ω : Set E) (x : V) :
    G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x ≤
      ∑ j ∈ Finset.range 4, restrictedLayerCount G.ends Set.univ
        {y | G.adjustedLayerIndex a R 0 x y = -((n+j+1 : ℕ) : ℤ)} ω x := by
  unfold peakDownBandCount restrictedLayerCount
  simp only [Set.mem_ofPred_eq]
  rw [←Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases h : R*((n : ℝ)+1) < G.orbitAdjustedHeight a y x ∧
      G.orbitAdjustedHeight a y x ≤ R*((n : ℝ)+4) ∧
      ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a y) y x
  · have hhlo : -R*((n : ℝ)+4) ≤ G.orbitAdjustedHeight a x y := by
      rw [G.orbitAdjustedHeight_reverse hc hl a y x]
      linarith [h.2.1]
    have hhhi : G.orbitAdjustedHeight a x y < -R*((n : ℝ)+1) := by
      rw [G.orbitAdjustedHeight_reverse hc hl a y x]
      linarith [h.1]
    have hidx : -((n : ℤ)+4) ≤ G.adjustedLayerIndex a R 0 x y ∧
        G.adjustedLayerIndex a R 0 x y < -((n : ℤ)+1) := by
      simp only [adjustedLayerIndex,add_zero,Int.floor_zero,sub_zero]
      constructor
      · apply Int.le_floor.mpr
        apply (le_div_iff₀ hR).mpr
        push_cast
        nlinarith
      · apply Int.floor_lt.mpr
        apply (div_lt_iff₀ hR).mpr
        push_cast
        nlinarith
    let j : ℕ := (-G.adjustedLayerIndex a R 0 x y-(n : ℤ)-1).toNat
    have hj : j ∈ Finset.range 4 := by
      simp only [Finset.mem_range,j]
      omega
    have he : G.adjustedLayerIndex a R 0 x y = -((n+j+1 : ℕ) : ℤ) := by
      dsimp [j]
      omega
    have hconn : Percolation.Conn G.ends (ω ∩ Set.univ) x y := by
      simpa only [Set.inter_univ] using Percolation.conn_symm G.ends ω h.2.2.1
    unfold peakUpBandTransport
    rw [ite_eq_left h]
    have hb := Finset.single_le_sum (s := Finset.range 4) (a := j)
      (f := fun k => if G.adjustedLayerIndex a R 0 x y = -((n+k+1 : ℕ) : ℤ) ∧
        Percolation.Conn G.ends (ω ∩ Set.univ) x y then (1 : ℝ≥0∞) else 0)
      (fun _ _ => bot_le) hj
    rw [ite_eq_left (show G.adjustedLayerIndex a R 0 x y = -((n+j+1 : ℕ) : ℤ) ∧
      Percolation.Conn G.ends (ω ∩ Set.univ) x y from ⟨he,hconn⟩)] at hb
    apply hb.trans_eq
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hh : G.adjustedLayerIndex a R 0 x y = -((n+k+1 : ℕ) : ℤ) ∧
      Percolation.Conn G.ends (ω ∩ Set.univ) x y
    · simp only [ite_eq_left hh]
    · simp only [ite_eq_right hh]
  · rw [peakUpBandTransport,ite_eq_right h]
    exact bot_le

variable [Countable V] [Countable E]

theorem peakDownBandCount_second_moment_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (p : unitInterval) (β : ℝ) (hβ : R < β)
    (K : ℝ≥0∞)
    (hsecond : ∀ (k l : ℕ) (x : V),
      (∫⁻ ω, restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y = -(k : ℤ)} ω x *
        restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y = -(l : ℤ)} ω x ∂G.law p) ≤
      K*ENNReal.ofReal (Real.exp (-(β-R)*((max k l : ℕ) : ℝ)))) (n : ℕ) (x : V) :
    (∫⁻ ω, (G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x)^2 ∂G.law p) ≤
      16*K*ENNReal.ofReal (Real.exp (-(β-R)*n)) := by
  let N (j : ℕ) (ω : Set E) := restrictedLayerCount G.ends Set.univ
    {y | G.adjustedLayerIndex a R 0 x y = -((n+j+1 : ℕ) : ℤ)} ω x
  have hmeas (j : ℕ) : Measurable (N j) := measurable_restrictedLayerCount G.ends _ _ x
  calc
    _ ≤ ∫⁻ ω, (∑ j ∈ Finset.range 4, N j ω)^2 ∂G.law p :=
      lintegral_mono fun ω => pow_le_pow_left' (G.peakDownBandCount_le_four_layers hc hl a R hR n ω x) 2
    _ = ∑ j ∈ Finset.range 4, ∑ k ∈ Finset.range 4, ∫⁻ ω, N j ω*N k ω ∂G.law p := by
      simp_rw [pow_two,Finset.sum_mul,Finset.mul_sum]
      rw [lintegral_finsetSum (f := fun j ω => ∑ k ∈ Finset.range 4, N j ω*N k ω)
        (Finset.range 4) (fun j _ => Finset.measurable_sum _ (fun k _ => (hmeas j).mul (hmeas k)))]
      apply Finset.sum_congr rfl
      intro j _
      exact lintegral_finsetSum (f := fun k ω => N j ω*N k ω) _ (fun k _ => (hmeas j).mul (hmeas k))
    _ ≤ ∑ _j ∈ Finset.range 4, ∑ _k ∈ Finset.range 4,
        K*ENNReal.ofReal (Real.exp (-(β-R)*n)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply (hsecond (n+j+1) (n+k+1) x).trans
      apply mul_le_mul' le_rfl
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hm : (n : ℝ) ≤ ((max (n+j+1) (n+k+1) : ℕ) : ℝ) := by
        exact_mod_cast (show n ≤ max (n+j+1) (n+k+1) by omega)
      nlinarith
    _ = _ := by norm_num [Finset.sum_const,nsmul_eq_mul]; ring

end CriticalPercolation.BondGraph

end

end OAI
