import OAI.Probability.BenjaminiSchramm.SlabExtensionGeometry
import OAI.Probability.BenjaminiSchramm.GeometricIncrement

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem ceiling_zero_band_from_profiles
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (d : ℕ) (hd : ∀ u, (Percolation.finite_neighbors hl u).toFinset.card ≤ d)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e → |G.orbitAdjustedHeight a u v| ≤ R)
    (p : unitInterval) (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
    (T U : ℝ) (hT : 0 < T) (hU : 0 < U)
    (hdown : ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ c : ℝ, 0 ≤ c → ∀ x : V,
        (∫⁻ ω, (G.adjustedSlabBandCount a (-k) c (-k-R) (-k+R) ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp (ζ*k+T*c)))
    (hup : ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ x : V,
        (∫⁻ ω, (G.adjustedSlabBandCount a (-r) (k+r) (k-R) (k+R) ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp ((-1+ζ)*k+U*r))) :
    ∀ q : ℝ, 0 < q → q < 1 → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ c : ℝ, 0 ≤ c → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ c})
        {v | -R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ R} ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp ((T+U+1)*c)) := by
  intro q hq0 hq1
  let b := (q+1)/2
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hqb : q ≤ b*b := by dsimp [b]; nlinarith [sq_nonneg (q-1)]
  obtain ⟨D,hD,hdb⟩ := hdown b hb hb1 (b/4) (by positivity) (by linarith)
  obtain ⟨A,hA,hab⟩ := hup b hb hb1 (1/2) (by norm_num)
  obtain ⟨B,hB,hbb⟩ := hup (b*b) (mul_pos hb hb) (by nlinarith) (1/2) (by norm_num)
  let A' := A*ENNReal.ofReal (Real.exp (U*R))
  have hA' : A' < ⊤ := ENNReal.mul_lt_top hA ENNReal.ofReal_lt_top
  let K := (d : ℝ≥0∞)^b*D*(A')^b
  have hK : K < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hb.le (ENNReal.natCast_ne_top d)) hD)
    (ENNReal.rpow_lt_top_of_nonneg hb.le hA'.ne)
  let s := b*R/4
  have hs : 0 < s := by dsimp [s]; positivity
  let S : ℝ≥0∞ := ∑' n : ℕ, ENNReal.ofReal (Real.exp (-s*n))
  have hS : S < ⊤ := by
    apply Summable.tsum_ofReal_lt_top
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hs)
  refine ⟨B+K*S,ENNReal.add_lt_top.mpr ⟨hB,ENNReal.mul_lt_top hK hS⟩,fun c hc0 x => ?_⟩
  let F (n : ℕ) := ∫⁻ ω, (G.adjustedSlabBandCount a (-(n : ℝ)*R) c (-R) R ω x)^(b*b) ∂G.law p
  let W := ENNReal.ofReal (Real.exp ((T+U+1)*c))
  have h0 : F 0 ≤ B*W := by
    simp only [F,Nat.cast_zero,neg_zero,zero_mul]
    have hh := hbb 0 (by norm_num) c hc0 x
    simp only [zero_sub,zero_add,mul_zero] at hh
    apply le_trans _ (hh.trans ?_)
    · apply lintegral_mono
      intro ω
      apply ENNReal.rpow_le_rpow _ (mul_nonneg hb.le hb.le)
      simp only [G.adjustedSlabBandCount_eq_restricted]
      apply restrictedLayerCount_mono_edges G.ends
      apply Percolation.internalEdges_mono G.ends
      intro v hv
      exact ⟨by linarith [hv.1],hv.2⟩
    · exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
        have hh := mul_nonneg (by linarith : 0 ≤ T+1) hc0
        nlinarith)))
  have hstep (n : ℕ) : F (n+1) ≤ F n+K*W*ENNReal.ofReal (Real.exp (-s*n)) := by
    let L := A'*ENNReal.ofReal (Real.exp (-(n : ℝ)*R/2+U*c))
    have hL (z : V) (hzlo : -((n : ℝ)+1)*R ≤ G.orbitAdjustedHeight a x z)
        (hzhi : G.orbitAdjustedHeight a x z < -(n : ℝ)*R) :
        (∫⁻ ω, (restrictedLayerCount G.ends
          (Percolation.internalEdges G.ends {v | -((n : ℝ)+1)*R ≤ G.orbitAdjustedHeight a x v ∧
            G.orbitAdjustedHeight a x v ≤ c})
          {v | -R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ R} ω z)^b ∂G.law p) ≤ L := by
      have hnn : (0 : ℝ) ≤ (n : ℝ)*R := mul_nonneg (Nat.cast_nonneg _) hR.le
      have hh := hab (-G.orbitAdjustedHeight a x z) (by linarith) (c+R) (by positivity) z
      apply le_trans _ (hh.trans ?_)
      · apply lintegral_mono
        intro ω
        apply ENNReal.rpow_le_rpow _ hb.le
        apply G.lower_extension_frontier_count_bound hc hl a R c hc0 n x z
        · simpa only [Nat.cast_add,Nat.cast_one] using hzlo
        · exact hzhi
      · dsimp [L,A']
        rw [mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
        apply mul_le_mul' le_rfl
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        linarith
    have hh := G.lower_extension_fractional_recurrence hc hl a d hd R c hR.le hc0 hjump
      p hfin n x hb hb1.le hb hb1.le L hL
    have hdownn := hdb ((n : ℝ)*R) (by positivity) c hc0 x
    simp only [←neg_mul] at hdownn
    have hcast : ((n+1 : ℕ) : ℝ)=(n : ℝ)+1 := by norm_cast
    simp only [F,hcast]
    apply hh.trans
    apply add_le_add le_rfl
    apply (mul_le_mul' (mul_le_mul' le_rfl hdownn) le_rfl).trans
    have hprod := fractional_two_profile_product D A' (b/4) T (-1/2) U
      ((n : ℝ)*R) c 1 b (by norm_num) hb.le
    simp only [ENNReal.rpow_one] at hprod
    calc
      _ = (d : ℝ≥0∞)^b*((D*ENNReal.ofReal (Real.exp (b/4*((n : ℝ)*R)+T*c)))*L^b) := by ac_rfl
      _ = K*ENNReal.ofReal (Real.exp ((b/4+b*(-1/2))*((n : ℝ)*R)+(T+b*U)*c)) := by
        dsimp [L,K]
        rw [show -(n : ℝ)*R/2+U*c=(-1/2)*((n : ℝ)*R)+U*c by ring,hprod]
        ac_rfl
      _ ≤ K*ENNReal.ofReal (Real.exp ((T+U+1)*c+(-s*(n : ℝ)))) := by
        apply mul_le_mul' le_rfl
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hU.le hb1.le) hc0
        dsimp [s]
        nlinarith
      _ = _ := by
        dsimp [W,K]
        rw [Real.exp_add ((T+U+1)*c) (-s*(n : ℝ)),ENNReal.ofReal_mul (Real.exp_nonneg _),mul_assoc]
        ac_rfl
  have hF := geometric_increment_factored F B K W s h0 hstep
  have hlimit : (∫⁻ ω, (restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ c})
      {v | -R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ R} ω x)^(b*b) ∂G.law p) ≤
        (B+K*S)*W := by
    have hh := restrictedLayerMoment_iUnion G.ends
      (fun n : ℕ => Percolation.internalEdges G.ends
        {v | -(n : ℝ)*R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ c})
      (internalEdges_lowerSlabs_monotone G.ends _ R c hR.le)
      {v | -R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ R} x p (mul_pos hb hb)
    rw [internalEdges_lowerSlabs_iUnion G.ends _ R c hR] at hh
    simp only [CriticalPercolation.BondGraph.law,Percolation.law] at hh ⊢
    rw [hh]
    apply iSup_le
    intro n
    simpa only [F,G.adjustedSlabBandCount_eq_restricted,CriticalPercolation.BondGraph.law,Percolation.law] using hF n
  apply le_trans _ hlimit
  apply lintegral_mono
  intro ω
  dsimp only
  rcases restrictedLayerCount_zero_or_one_le G.ends
    (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ c})
    {v | -R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ R} ω x with hz | ho
  · rw [hz,ENNReal.zero_rpow_of_pos hq0,ENNReal.zero_rpow_of_pos (mul_pos hb hb)]
  · exact ENNReal.rpow_le_rpow_of_exponent_le ho hqb

end CriticalPercolation.BondGraph

end

end OAI
