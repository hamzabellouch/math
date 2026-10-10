import OAI.Probability.BenjaminiSchramm.UpwardHalfspaceFromContinuation
import OAI.Probability.BenjaminiSchramm.DownwardHalfspaceFromContinuation
import OAI.Probability.BenjaminiSchramm.HalfspaceFiniteShiftProfile
import OAI.Probability.BenjaminiSchramm.FractionalInterpolation
import OAI.Probability.BenjaminiSchramm.FractionalExponentBootstrap

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def downwardHalfspaceFractionalProfile (a : V → ℝ) (p : unitInterval) (R q : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
    (∫⁻ ω, (restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ 0})
      {v | -k-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ -k+R} ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp (ζ*k))

def upwardHalfspaceFractionalProfile (a : V → ℝ) (p : unitInterval) (R q : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
    (∫⁻ ω, (restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | 0 ≤ G.orbitAdjustedHeight a x v})
      {v | k-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ k+R} ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp ((-1+ζ)*k))

theorem halfspace_fractional_profile_bootstrap [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular)
    (d : ℕ) (hd : ∀ u, (Percolation.finite_neighbors hl u).toFinset.card ≤ d)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e u v, u ∈ G.ends e → v ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) u v| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
    (L U B : ℝ) (hB : 0 < B)
    (hdown : G.lowerSlabFractionalProfile (G.stationaryOrbitWeight μ) p R L)
    (hup : ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ x : V,
        (∫⁻ ω, (G.adjustedSlabBandCount (G.stationaryOrbitWeight μ) (-r) (k+r) (k-R) (k+R) ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp ((-1+ζ)*k+U*r)))
    (hcrude : ∀ q : ℝ, 0 < q → q < 1 → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0})
        {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp (B*k))) :
    ∀ q : ℝ, 0 < q → q < 1 →
      G.downwardHalfspaceFractionalProfile (G.stationaryOrbitWeight μ) p R q ∧
      G.upwardHalfspaceFractionalProfile (G.stationaryOrbitWeight μ) p R q := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨Tlow,_hTlow,hshiftlow⟩ := G.halfspace_ceiling_shift_profile_fixed hc hl hq μ hμ hstat hu
    R hR.le hjump p hp0 hp1 (1/8)
  obtain ⟨Thigh,_hThigh,hshifthigh⟩ := G.halfspace_ceiling_shift_profile hc hl hq μ hμ hstat hu
    R hR.le hjump p hp0 hp1 B hcrude
  obtain ⟨Tup,_hTup,hshiftup⟩ := G.halfspace_floor_shift_profile_fixed hc hl hq μ hμ hstat hu
    R hR.le hjump p hp0 hp1 (-1/2)
  let η := min (1/4) (1/(16*(B+1)))
  have hη : 0 < η := lt_min (by norm_num) (div_pos (by norm_num) (by positivity))
  have hη4 : η ≤ 1/4 := min_le_left _ _
  have hη1 : η < 1 := by linarith
  have hηB : (2*η)*B ≤ 1/8 := by
    have hh := (le_div_iff₀ (show 0 < 16*(B+1) by positivity)).mp
      (min_le_right (1/4) (1/(16*(B+1))))
    change η*(16*(B+1)) ≤ 1 at hh
    nlinarith
  have hD0 : G.downwardHalfspaceFractionalProfile a p R 0 := by
    intro ζ hζ
    refine ⟨1,by simp,fun k hk x => ?_⟩
    simp only [ENNReal.rpow_zero,lintegral_const,measure_univ,mul_one,one_mul]
    exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hζ.le hk))
  apply fractional_exponent_bootstrap
    (G.downwardHalfspaceFractionalProfile a p R) (G.upwardHalfspaceFractionalProfile a p R)
    η hη hη1 hD0
  · intro q hq0 hq1 hDq q' hq'0 hq'lim
    let b := (q+1)/2
    have hb0 : 0 < b := by dsimp [b]; positivity
    have hb1 : b < 1 := by dsimp [b]; linarith
    let θ := 2*η
    have hθ0 : 0 < θ := by dsimp [θ]; positivity
    have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
    let m := q+η*(1-q)
    have hm : 0 < m := add_pos_of_nonneg_of_pos hq0 (mul_pos hη (sub_pos.mpr hq1))
    have hm1 : m < 1 := by
      have hh := mul_pos (sub_pos.mpr hη1) (sub_pos.mpr hq1)
      dsimp [m]
      nlinarith
    let t := q'/m
    have ht : 0 < t := div_pos hq'0 hm
    have ht1 : t < 1 := (div_lt_one hm).mpr hq'lim
    have hmt : m*t=q' := by dsimp [t]; field_simp
    obtain ⟨D,hD,hdb⟩ := hshiftlow q hq0 (hDq (1/8) (by norm_num))
    obtain ⟨A,hA,hab⟩ := hshifthigh b hb0 hb1
    let D' := D*ENNReal.ofReal (Real.exp (Tlow*R))
    let A' := A*ENNReal.ofReal (Real.exp (Thigh*R))
    have hD' : D' < ⊤ := ENNReal.mul_lt_top hD ENNReal.ofReal_lt_top
    have hA' : A' < ⊤ := ENNReal.mul_lt_top hA ENNReal.ofReal_lt_top
    let C := D'^(1-θ)*A'^θ
    have hC : C < ⊤ := ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hθ1) hD'.ne)
      (ENNReal.rpow_lt_top_of_nonneg hθ0.le hA'.ne)
    let ρ := (1-θ)*(1/8)+θ*B
    have hρ : 0 ≤ ρ := add_nonneg (mul_nonneg (sub_nonneg.mpr hθ1) (by norm_num))
      (mul_nonneg hθ0.le hB.le)
    have hρ1 : ρ ≤ 3/4 := by dsimp [ρ,θ]; nlinarith
    have hcont (s : ℝ) (hs : 0 ≤ s) (x : V) :
        (∫⁻ ω, (restrictedLayerCount G.ends
          (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ R})
          {v | -s-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ -s+R} ω x)^m ∂G.law p) ≤
            C*ENNReal.ofReal (Real.exp (ρ*s)) := by
      let X := fun ω => restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ R})
        {v | -s-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ -s+R} ω x
      have hX : Measurable X := measurable_restrictedLayerCount G.ends _ _ x
      have hlo : (∫⁻ ω, X ω^q ∂G.law p) ≤ D'*ENNReal.ofReal (Real.exp ((1/8)*s)) := by
        apply (hdb s hs R hR.le x).trans_eq
        dsimp [D']
        rw [Real.exp_add ((1/8)*s) (Tlow*R),ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
      have hhi : (∫⁻ ω, X ω^b ∂G.law p) ≤ A'*ENNReal.ofReal (Real.exp (B*s)) := by
        apply (hab s hs R hR.le x).trans_eq
        dsimp [A']
        rw [Real.exp_add (B*s) (Thigh*R),ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
      have hexp : (1-θ)*q+θ*b=m := by dsimp [θ,b,m]; ring
      have hh := lintegral_rpow_interpolation (G.law p) X hX q b θ hq0 hb0.le hθ0.le hθ1
      rw [hexp] at hh
      apply hh.trans ((mul_le_mul' (ENNReal.rpow_le_rpow hlo (sub_nonneg.mpr hθ1))
        (ENNReal.rpow_le_rpow hhi hθ0.le)).trans_eq ?_)
      have he := fractional_two_profile_product D' A' (1/8) 0 B 0 s 0 (1-θ) θ
        (sub_nonneg.mpr hθ1) hθ0.le
      simpa only [mul_zero,add_zero] using he
    have hh := G.upward_halfspace_from_continuation hc hl a d hd R hR hjump p hfin U hup
      m t ρ hm hm1.le ht ht1 hρ hρ1 C hC hcont
    simpa only [hmt,upwardHalfspaceFractionalProfile] using hh
  · intro q hq0 hq1 hUq q' hq'0 hq'q
    by_cases hq'zero : q'=0
    · simpa only [hq'zero] using hD0
    have hq'pos : 0 < q' := lt_of_le_of_ne hq'0 (Ne.symm hq'zero)
    let t := q'/q
    have ht : 0 < t := div_pos hq'pos hq0
    have ht1 : t < 1 := (div_lt_one hq0).mpr hq'q
    have hqt : q*t=q' := by dsimp [t]; field_simp
    have hbase := hUq (1/2) (by norm_num)
    have he (k : ℝ) : (-1+(1/2 : ℝ))*k=(-1/2)*k := by ring
    simp only [he] at hbase
    obtain ⟨D,hD,hdb⟩ := hshiftup q hq0.le hbase
    let D' := D*ENNReal.ofReal (Real.exp (Tup*R))
    have hD' : D' < ⊤ := ENNReal.mul_lt_top hD ENNReal.ofReal_lt_top
    have hcont (s : ℝ) (hs : 0 ≤ s) (x : V) :
        (∫⁻ ω, (restrictedLayerCount G.ends
          (Percolation.internalEdges G.ends {v | -R ≤ G.orbitAdjustedHeight a x v})
          {v | s-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ s+R} ω x)^q ∂G.law p) ≤
            D'*ENNReal.ofReal (Real.exp (-s/2)) := by
      apply (hdb s hs R hR.le x).trans_eq
      dsimp [D']
      rw [Real.exp_add ((-1/2)*s) (Tup*R),ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rw [show (-1/2 : ℝ)*s= -s/2 by ring]
      ac_rfl
    have hh := G.downward_halfspace_from_continuation hc hl a d hd R hR hjump p hfin L hdown
      q t hq0 hq1 ht ht1 D' hD' hcont
    simpa only [hqt,downwardHalfspaceFractionalProfile] using hh

end CriticalPercolation.BondGraph

end

end OAI
