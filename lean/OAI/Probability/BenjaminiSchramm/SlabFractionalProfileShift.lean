import OAI.Probability.BenjaminiSchramm.SlabRootShift
import OAI.Probability.BenjaminiSchramm.FractionalSlabGeometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma finite_energy_cancel_length (X Y : ℝ≥0∞) (δ A B c : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlen : (N : ℝ) ≤ A*c+B)
    (hXY : ENNReal.ofReal (δ^N)*X ≤ Y) :
    X ≤ ENNReal.ofReal (Real.exp (-Real.log δ*(A*c+B)))*Y := by
  have he : Real.exp (-Real.log δ*(N : ℝ))*δ^N=1 := by
    rw [←Real.exp_log hδ,←Real.exp_nat_mul,←Real.exp_add,Real.log_exp]
    rw [show -Real.log δ*(N : ℝ)+(N : ℝ)*Real.log δ=0 by ring,Real.exp_zero]
  have hc : ENNReal.ofReal (Real.exp (-Real.log δ*(N : ℝ)))*ENNReal.ofReal (δ^N)=1 := by
    rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),he,ENNReal.ofReal_one]
  have hs : 0 ≤ -Real.log δ := neg_nonneg.mpr (Real.log_nonpos hδ.le hδ1)
  calc
    _ = ENNReal.ofReal (Real.exp (-Real.log δ*(N : ℝ)))*(ENNReal.ofReal (δ^N)*X) := by
      rw [←mul_assoc,hc,one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-Real.log δ*(N : ℝ)))*Y := mul_le_mul' le_rfl hXY
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hlen hs))) le_rfl

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def lowerSlabFractionalProfile (a : V → ℝ) (p : unitInterval) (R L : ℝ) : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ x : V,
      (∫⁻ ω, (G.adjustedSlabBandCount a (-k-r) 0 (-k-R) (-k+R) ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp (ζ*k+L*r))

theorem finite_ceiling_fractional_profile [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
    (L : ℝ) (hprofile : G.lowerSlabFractionalProfile (G.stationaryOrbitWeight μ) p R L) :
    ∃ T : ℝ, 0 < T ∧ ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ c : ℝ, 0 ≤ c → ∀ x : V,
        (∫⁻ ω, (G.adjustedSlabBandCount (G.stationaryOrbitWeight μ) (-k-r) c (-k-R) (-k+R) ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp (ζ*k+L*r+T*c)) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,hA,hB,hpaths⟩ := G.stationaryOrbitHeight_bounded_ascent_to_level
    hc hl hq μ hμ hstat hu R hR.le hjump
  let δ := min (p : ℝ) (1-p)
  have hδ : 0 < δ := lt_min hp0 (sub_pos.mpr hp1)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans p.2.2
  let s := -Real.log δ
  have hs : 0 ≤ s := neg_nonneg.mpr (Real.log_nonpos hδ.le hδ1)
  let T := s*A+1
  refine ⟨T,by dsimp [T]; positivity,fun q hq0 hq1 ζ hζ hζ1 => ?_⟩
  obtain ⟨C,hC,hbound⟩ := hprofile q hq0 hq1 ζ hζ
  refine ⟨C*ENNReal.ofReal (Real.exp (s*B+R)),ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top,
    fun k hk r hr c hc0 x => ?_⟩
  obtain ⟨y,w,hlen,hcy,hyc,hw⟩ := hpaths c hc0 x
  have hXY := G.fractional_slab_root_ascent hc hl a p k r c R hk hr w hcy hw hq0.le
  simp_rw [←G.adjustedSlabBandCount_eq_restricted] at hXY
  have hh := finite_energy_cancel_length _ _ δ A B c w.length hδ hδ1 hlen hXY
  have hlevel : 0 ≤ k+G.orbitAdjustedHeight a x y := add_nonneg hk (hc0.trans hcy)
  have hb := hbound (k+G.orbitAdjustedHeight a x y) hlevel r hr y
  apply hh.trans ((mul_le_mul' le_rfl hb).trans ?_)
  have he : -Real.log δ*(A*c+B)+(ζ*(k+G.orbitAdjustedHeight a x y)+L*r) ≤
      (s*B+R)+(ζ*k+L*r+T*c) := by
    have hζh : ζ*G.orbitAdjustedHeight a x y ≤ G.orbitAdjustedHeight a x y :=
      mul_le_of_le_one_left (hc0.trans hcy) hζ1
    dsimp [s,T]
    nlinarith
  calc
    _ = C*ENNReal.ofReal (Real.exp (-Real.log δ*(A*c+B)+(ζ*(k+G.orbitAdjustedHeight a x y)+L*r))) := by
      simp only [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
    _ ≤ C*ENNReal.ofReal (Real.exp ((s*B+R)+(ζ*k+L*r+T*c))) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))
    _ = _ := by
      rw [Real.exp_add (s*B+R) (ζ*k+L*r+T*c),
        ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl

end CriticalPercolation.BondGraph

end

end OAI
