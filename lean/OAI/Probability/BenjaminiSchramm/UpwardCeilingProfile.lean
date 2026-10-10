import OAI.Probability.BenjaminiSchramm.HalfspaceFiniteShiftProfile
import OAI.Probability.BenjaminiSchramm.UpwardFractionalSlabProfile
import OAI.Probability.BenjaminiSchramm.FractionalBandEstimate
import OAI.Probability.BenjaminiSchramm.BoundedLayerShift

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma adjustedCeilingBandCount_rpow_mono_exponent (a : V → ℝ) (c l u : ℝ)
    (ω : Set E) (x : V) {q q' : ℝ} (hq : 0 < q) (hqq' : q ≤ q') :
    (G.adjustedCeilingBandCount a c l u ω x)^q ≤
      (G.adjustedCeilingBandCount a c l u ω x)^q' := by
  simp only [G.adjustedCeilingBandCount_eq_restrictedLayerCount]
  rcases restrictedLayerCount_zero_or_one_le G.ends _ _ ω x with hz | ho
  · rw [hz,ENNReal.zero_rpow_of_pos hq,ENNReal.zero_rpow_of_pos (hq.trans_le hqq')]
  · exact ENNReal.rpow_le_rpow_of_exponent_le ho hqq'

omit [Countable V] [Countable E] in
lemma one_le_adjustedCeilingZeroBandCount (a : V → ℝ) (c B : ℝ)
    (hB : 0 ≤ B) (ω : Set E) (x : V) :
    1 ≤ G.adjustedCeilingBandCount a c (-B) B ω x := by
  apply le_trans _ (ENNReal.le_tsum x)
  unfold adjustedCeilingBandTransport
  rw [ite_eq_left]
  exact ⟨Percolation.conn_refl G.ends _ x,by simpa using neg_nonpos.mpr hB,by simpa using hB⟩

theorem upward_ceiling_profile [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
    (Vcoef : ℝ) (hV : 0 < Vcoef)
    (hdown : ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0})
        {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
        D*ENNReal.ofReal (Real.exp (ζ*k)))
    (hzero : ∀ q : ℝ, 0 < q → q < 1 → ∃ Z : ℝ≥0∞, Z < ⊤ ∧
      ∀ c : ℝ, 0 ≤ c → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ c})
        {v | -(2*R) ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 2*R} ω x)^q ∂G.law p) ≤
        Z*ENNReal.ofReal (Real.exp (Vcoef*c))) :
    ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k})
        {v | k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k+R} ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp ((-1+ζ)*k)) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨m,M,hm,hbounds⟩ := G.stationaryOrbitWeight_uniform_bounds hc hl μ hμ
  let O := G.orbitRepresentatives hq
  let D := (ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r))*ENNReal.ofReal (Real.exp R)
  have hD : D < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hm))
      (ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top
  intro q hq0 hq1 ζ hζ
  let η := min ((1-q)/2) (min (ζ/4) (1/4))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hηq : η ≤ (1-q)/2 := min_le_left _ _
  have hηζ : η ≤ ζ/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η ≤ 1/4 := (min_le_right _ _).trans (min_le_right _ _)
  let q' := 1-η
  have hq'0 : 0 < q' := by dsimp [q']; linarith
  have hq'1 : q' < 1 := by dsimp [q']; linarith
  have hqq' : q ≤ q' := by dsimp [q']; linarith
  let δ := min ((1-q')/2) (ζ/(4*(Vcoef+1)))
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hζ (by positivity))
  have hδq' : δ ≤ 1-q' := (min_le_left _ _).trans (by linarith)
  have hδ1 : δ < 1 := by linarith
  have hδV : δ*Vcoef ≤ ζ/4 := by
    have hh := (le_div_iff₀ (show 0 < 4*(Vcoef+1) by positivity)).mp
      (min_le_right ((1-q')/2) (ζ/(4*(Vcoef+1))))
    change δ*(4*(Vcoef+1)) ≤ ζ at hh
    nlinarith
  let ε := min (ζ/4) (1/2)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεζ : ε ≤ ζ/4 := min_le_left _ _
  obtain ⟨T,hT,hshift⟩ := G.halfspace_ceiling_shift_profile_fixed hc hl hq μ hμ hstat hu R hR.le hjump p hp0 hp1 ε
  obtain ⟨C₁,hC₁,hbound₁⟩ := hshift (1-δ) (by linarith)
    (hdown (1-δ) (by linarith) (by linarith) ε hε)
  obtain ⟨C₂,hC₂,hbound₂⟩ := hzero q' hq'0 hq'1
  let Q := C₁*ENNReal.ofReal (Real.exp (T*R))
  let Z := C₂*ENNReal.ofReal (Real.exp (Vcoef*(2*R)))
  have hQ : Q < ⊤ := ENNReal.mul_lt_top hC₁ ENNReal.ofReal_lt_top
  have hZ : Z < ⊤ := ENNReal.mul_lt_top hC₂ ENNReal.ofReal_lt_top
  let A := D*Q
  have hA : A < ⊤ := ENNReal.mul_lt_top hD hQ
  let C := A^q'*Z^δ
  have hC : C < ⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hq'0.le hA.ne) (ENNReal.rpow_lt_top_of_nonneg hδ.le hZ.ne)
  refine ⟨C,hC,fun k hk x => ?_⟩
  have hzero' : (∫⁻ ω, (G.adjustedCeilingBandCount a (k+2*R) (-(2*R)) (2*R) ω x)^q' ∂G.law p) ≤
      Z*ENNReal.ofReal (Real.exp (Vcoef*k)) := by
    have hh := hbound₂ (k+2*R) (by positivity) x
    simp_rw [G.adjustedCeilingBandCount_eq_restrictedLayerCount]
    apply hh.trans_eq
    dsimp [Z]
    rw [mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
    rw [show Vcoef*(k+2*R)=Vcoef*(2*R)+Vcoef*k by ring]
  have hdown' (y : V) : (∫⁻ ω, (G.adjustedCeilingBandCount a R (-k-R) (-k+R) ω y)^(1-δ) ∂G.law p) ≤
      Q*ENNReal.ofReal (Real.exp (ε*k)) := by
    have hh := hbound₁ k hk R hR.le y
    simp_rw [G.adjustedCeilingBandCount_eq_restrictedLayerCount]
    apply hh.trans_eq
    dsimp [Q]
    rw [mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
    rw [show ε*k+T*R=T*R+ε*k by ring]
  have hZfin : ∀ᵐ ω ∂G.law p,
      1 ≤ G.adjustedCeilingBandCount a (k+2*R) (-(2*R)) (2*R) ω x ∧
      G.adjustedCeilingBandCount a (k+2*R) (-(2*R)) (2*R) ω x ≠ ⊤ := by
    filter_upwards [hfin x] with ω hω
    refine ⟨G.one_le_adjustedCeilingZeroBandCount a _ _ (by positivity) ω x,?_⟩
    rw [G.adjustedCeilingBandCount_eq_restrictedLayerCount]
    exact (restrictedLayerCount_lt_top_of_finite G.ends _ _ ω x hω).ne
  have hwidth : (k+R)-(k-R)=2*R := by ring
  have hminus : (k-R)-(k+R)= -(2*R) := by ring
  have hnegl : -(k-R)= -k+R := by ring
  have hnegu : -(k+R)= -k-R := by ring
  have hreverse : k+2*R-(k+R)=R := by ring
  have hforward : k+2*R-2*R=k := by ring
  have hh := G.fractional_ceiling_band_estimate O hc hl a (G.stationaryOrbitWeight_pos hc hl μ hμ)
    (G.stationaryOrbitWeight_aut μ) m hm (fun z => (hbounds z).1) p (k+2*R) (k-R) (k+R) x
    hq'0 hq'1 hδ.le hδq'
    (by simpa only [hminus,hwidth] using hZfin)
    (Z*ENNReal.ofReal (Real.exp (Vcoef*k))) (Q*ENNReal.ofReal (Real.exp (ε*k)))
    (by simpa only [hminus,hwidth] using hzero')
    (fun y _ => by simpa only [hreverse,hnegu,hnegl] using hdown' y)
  simp only [hwidth,hforward] at hh
  have hfactor : (((ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp (-(k-R)))*
      (∑ r ∈ O.roots, ENNReal.ofReal (a r)))*(Q*ENNReal.ofReal (Real.exp (ε*k)))) =
        A*ENNReal.ofReal (Real.exp ((ε-1)*k)) := by
    dsimp [A,D]
    have he : Real.exp (-(k-R))*Real.exp (ε*k)=Real.exp R*Real.exp ((ε-1)*k) := by
      rw [←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    calc
      _ = ((ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r))*Q)*
          (ENNReal.ofReal (Real.exp (-(k-R)))*ENNReal.ofReal (Real.exp (ε*k))) := by ac_rfl
      _ = _ := by
        rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),he,ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
  rw [hfactor] at hh
  have heq : (A*ENNReal.ofReal (Real.exp ((ε-1)*k)))^q'*
      (Z*ENNReal.ofReal (Real.exp (Vcoef*k)))^δ =
      C*ENNReal.ofReal (Real.exp ((q'*(ε-1)+δ*Vcoef)*k)) := by
    simpa only [mul_zero,add_zero] using
      fractional_two_profile_product A Z (ε-1) 0 Vcoef 0 k 0 q' δ hq'0.le hδ.le
  have hmono : (∫⁻ ω, (G.adjustedCeilingBandCount a k (k-R) (k+R) ω x)^q ∂G.law p) ≤
      ∫⁻ ω, (G.adjustedCeilingBandCount a k (k-R) (k+R) ω x)^q' ∂G.law p :=
    lintegral_mono (fun ω => G.adjustedCeilingBandCount_rpow_mono_exponent a _ _ _ ω x hq0 hqq')
  simp_rw [←G.adjustedCeilingBandCount_eq_restrictedLayerCount]
  apply (hmono.trans hh).trans
  rw [heq]
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hqε : q'*ε ≤ ε := mul_le_of_le_one_left hε.le hq'1.le
  have hrate : q'*(ε-1)+δ*Vcoef ≤ -1+ζ := by dsimp [q'] at hqε ⊢; nlinarith
  exact mul_le_mul_of_nonneg_right hrate hk

end CriticalPercolation.BondGraph

end

end OAI
