import OAI.Probability.BenjaminiSchramm.HalfspaceFiniteShiftProfile
import OAI.Probability.BenjaminiSchramm.UpwardFractionalSlabProfile
import OAI.Probability.BenjaminiSchramm.LayerMonotoneLimit

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma adjustedSlabBandCount_le_floor_count (a : V → ℝ) (d c l u : ℝ)
    (ω : Set E) (x : V) :
    G.adjustedSlabBandCount a d c l u ω x ≤ restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {v | d ≤ G.orbitAdjustedHeight a x v})
      {v | l ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ u} ω x := by
  rw [G.adjustedSlabBandCount_eq_restricted]
  apply restrictedLayerCount_mono_edges G.ends
  exact Percolation.internalEdges_mono G.ends (fun _ h => h.1)

theorem floor_down_profile_of_zero_band [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
    (Vcoef : ℝ) (hV : 0 < Vcoef)
    (hup : ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v})
        {v | k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k+R} ω x)^q ∂G.law p) ≤
        D*ENNReal.ofReal (Real.exp ((-1+ζ)*k)))
    (hzero : ∀ q : ℝ, 0 < q → q < 1 → ∃ Z : ℝ≥0∞, Z < ⊤ ∧
      ∀ c : ℝ, 0 ≤ c → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | -c ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v})
        {v | -(2*R) ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 2*R} ω x)^q ∂G.law p) ≤
        Z*ENNReal.ofReal (Real.exp (Vcoef*c))) :
    ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | -k ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v})
        {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp (ζ*k)) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨m,M,hm,hbounds⟩ := G.stationaryOrbitWeight_uniform_bounds hc hl μ hμ
  let O := G.orbitRepresentatives hq
  let D := (ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r))*ENNReal.ofReal (Real.exp R)
  have hD : D < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hm))
      (ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top
  intro q hq0 hq1 ζ hζ
  let δ := min ((1-q)/2) (ζ/(4*(Vcoef+1)))
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hζ (by positivity))
  have hδq : δ ≤ 1-q := (min_le_left _ _).trans (by linarith)
  have hδ1 : δ < 1 := by linarith
  have hδV : δ*Vcoef ≤ ζ/4 := by
    have hh := (le_div_iff₀ (show 0 < 4*(Vcoef+1) by positivity)).mp
      (min_le_right ((1-q)/2) (ζ/(4*(Vcoef+1))))
    change δ*(4*(Vcoef+1)) ≤ ζ at hh
    nlinarith
  let ε := ζ/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨T,hT,hshift⟩ := G.halfspace_floor_shift_profile_fixed hc hl hq μ hμ hstat hu R hR.le hjump p hp0 hp1 (-1+ε)
  obtain ⟨C₁,hC₁,hbound₁⟩ := hshift (1-δ) (by linarith)
    (hup (1-δ) (by linarith) (by linarith) ε hε)
  obtain ⟨C₂,hC₂,hbound₂⟩ := hzero q hq0 hq1
  let Q := C₁*ENNReal.ofReal (Real.exp (T*R))
  let Z := C₂*ENNReal.ofReal (Real.exp (Vcoef*(2*R)))
  have hQ : Q < ⊤ := ENNReal.mul_lt_top hC₁ ENNReal.ofReal_lt_top
  have hZ : Z < ⊤ := ENNReal.mul_lt_top hC₂ ENNReal.ofReal_lt_top
  let A := D*Q
  have hA : A < ⊤ := ENNReal.mul_lt_top hD hQ
  let C := A^q*Z^δ
  have hC : C < ⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hq0.le hA.ne) (ENNReal.rpow_lt_top_of_nonneg hδ.le hZ.ne)
  refine ⟨C,hC,fun k hk x => ?_⟩
  have hslab (r : ℝ) (hr : 0 ≤ r) :
      (∫⁻ ω, (G.adjustedSlabBandCount a (-k) r (-k-R) (-k+R) ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp (ζ*k)) := by
    have hzero' : (∫⁻ ω, (G.adjustedSlabBandCount a (-k-2*R) (r+2*R) (-(2*R)) (2*R) ω x)^q ∂G.law p) ≤
        Z*ENNReal.ofReal (Real.exp (Vcoef*k)) := by
      have hh := hbound₂ (k+2*R) (by positivity) x
      have hmon : (∫⁻ ω, (G.adjustedSlabBandCount a (-k-2*R) (r+2*R) (-(2*R)) (2*R) ω x)^q ∂G.law p) ≤
          ∫⁻ ω, (restrictedLayerCount G.ends
            (Percolation.internalEdges G.ends {v | -(k+2*R) ≤ G.orbitAdjustedHeight a x v})
            {v | -(2*R) ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ 2*R} ω x)^q ∂G.law p := by
        apply lintegral_mono
        intro ω
        rw [show -(k+2*R)= -k-2*R by ring]
        exact ENNReal.rpow_le_rpow (G.adjustedSlabBandCount_le_floor_count a _ _ _ _ ω x) hq0.le
      apply (hmon.trans hh).trans_eq
      dsimp [Z]
      rw [mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
      rw [show Vcoef*(k+2*R)=Vcoef*(2*R)+Vcoef*k by ring]
    have hup' (y : V) : (∫⁻ ω, (G.adjustedSlabBandCount a (-R) (r+k+R) (k-R) (k+R) ω y)^(1-δ) ∂G.law p) ≤
        Q*ENNReal.ofReal (Real.exp ((-1+ε)*k)) := by
      have hh := hbound₁ k hk R hR.le y
      apply ((lintegral_mono (μ := G.law p) (fun ω => ENNReal.rpow_le_rpow
        (G.adjustedSlabBandCount_le_floor_count a (-R) (r+k+R) (k-R) (k+R) ω y)
        (show 0 ≤ 1-δ by linarith))).trans hh).trans_eq
      dsimp [Q]
      rw [mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
      rw [show (-1+ε)*k+T*R=T*R+(-1+ε)*k by ring]
    have hZfin : ∀ᵐ ω ∂G.law p,
        1 ≤ G.adjustedSlabBandCount a (-k-2*R) (r+2*R) (-(2*R)) (2*R) ω x ∧
        G.adjustedSlabBandCount a (-k-2*R) (r+2*R) (-(2*R)) (2*R) ω x ≠ ⊤ := by
      filter_upwards [hfin x] with ω hω
      exact ⟨G.one_le_adjustedSlabZeroBandCount a _ _ _ (by positivity) ω x,
        (G.adjustedSlabBandCount_lt_top_of_finite a _ _ _ _ ω x hω).ne⟩
    have hwidth : (-k+R)-(-k-R)=2*R := by ring
    have hminus : (-k-R)-(-k+R)= -(2*R) := by ring
    have hnegl : -(-k-R)=k+R := by ring
    have hnegu : -(-k+R)=k-R := by ring
    have hreverseLo : -k-2*R-(-k-R)= -R := by ring
    have hreverseHi : r+2*R-(-k+R)=r+k+R := by ring
    have hforwardLo : -k-2*R+2*R= -k := by ring
    have hforwardHi : r+2*R-2*R=r := by ring
    have hh := G.fractional_slab_band_estimate O hc hl a (G.stationaryOrbitWeight_pos hc hl μ hμ)
      (G.stationaryOrbitWeight_aut μ) m hm (fun z => (hbounds z).1) p (-k-2*R) (r+2*R) (-k-R) (-k+R) x
      hq0 hq1 hδ.le hδq
      (by simpa only [hminus,hwidth] using hZfin)
      (Z*ENNReal.ofReal (Real.exp (Vcoef*k))) (Q*ENNReal.ofReal (Real.exp ((-1+ε)*k)))
      (by simpa only [hminus,hwidth] using hzero')
      (fun y _ => by simpa only [hreverseLo,hreverseHi,hnegu,hnegl] using hup' y)
    simp only [hwidth,hforwardLo,hforwardHi] at hh
    have hfactor : (((ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp (-(-k-R)))*
        (∑ r ∈ O.roots, ENNReal.ofReal (a r)))*(Q*ENNReal.ofReal (Real.exp ((-1+ε)*k)))) =
          A*ENNReal.ofReal (Real.exp (ε*k)) := by
      dsimp [A,D]
      have he : Real.exp (-(-k-R))*Real.exp ((-1+ε)*k)=Real.exp R*Real.exp (ε*k) := by
        rw [←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      calc
        _ = ((ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r))*Q)*
            (ENNReal.ofReal (Real.exp (-(-k-R)))*ENNReal.ofReal (Real.exp ((-1+ε)*k))) := by ac_rfl
        _ = _ := by
          rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),he,ENNReal.ofReal_mul (Real.exp_nonneg _)]
          ac_rfl
    rw [hfactor] at hh
    have heq : (A*ENNReal.ofReal (Real.exp (ε*k)))^q*
        (Z*ENNReal.ofReal (Real.exp (Vcoef*k)))^δ =
        C*ENNReal.ofReal (Real.exp ((q*ε+δ*Vcoef)*k)) := by
      simpa only [mul_zero,add_zero] using
        fractional_two_profile_product A Z ε 0 Vcoef 0 k 0 q δ hq0.le hδ.le
    apply hh.trans
    rw [heq]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hqε : q*ε ≤ ε := mul_le_of_le_one_left hε.le hq1.le
    have hrate : q*ε+δ*Vcoef ≤ ζ := by dsimp [ε] at hqε ⊢; linarith
    exact mul_le_mul_of_nonneg_right hrate hk
  have hh := restrictedLayerMoment_iUnion G.ends
    (fun n : ℕ => Percolation.internalEdges G.ends
      {v | -k ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ 0+(n : ℝ)*R})
    (internalEdges_upperSlabs_monotone G.ends _ R (-k) 0 hR.le)
    {v | -k-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ -k+R} x p hq0
  rw [internalEdges_upperSlabs_iUnion G.ends _ R (-k) 0 hR] at hh
  simp only [CriticalPercolation.BondGraph.law,Percolation.law] at hh ⊢
  rw [hh]
  apply iSup_le
  intro n
  simpa only [G.adjustedSlabBandCount_eq_restricted,zero_add,
    CriticalPercolation.BondGraph.law,Percolation.law] using hslab ((n : ℝ)*R) (by positivity)

theorem floor_down_profile [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
    (hup : ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v})
        {v | k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k+R} ω x)^q ∂G.law p) ≤
        D*ENNReal.ofReal (Real.exp ((-1+ζ)*k)))
    (hup₂ : ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v})
        {v | k-2*R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k+2*R} ω x)^q ∂G.law p) ≤
        D*ENNReal.ofReal (Real.exp ((-1+ζ)*k))) :
    ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | -k ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v})
        {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp (ζ*k)) := by
  let a := G.stationaryOrbitWeight μ
  have hjump₂ : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ 2*R := by
    intro e v w hv hw
    exact (hjump e v w hv hw).trans (by linarith)
  obtain ⟨T,hT,hshift⟩ := G.halfspace_floor_shift_profile hc hl hq μ hμ hstat hu (2*R)
    (by positivity) hjump₂ p hp0 hp1 (-1+(1/2 : ℝ))
    (fun q hq0 hq1 => hup₂ q hq0 hq1 (1/2) (by norm_num))
  apply G.floor_down_profile_of_zero_band hc hl hq μ hμ hstat hu R hR hjump p hp0 hp1 hfin T hT hup
  intro q hq0 hq1
  obtain ⟨C,hC,hbound⟩ := hshift q hq0 hq1
  refine ⟨C,hC,fun c hc0 x => ?_⟩
  simpa only [zero_sub,sub_zero,zero_add,mul_zero,add_zero] using hbound 0 (by norm_num) c hc0 x

end CriticalPercolation.BondGraph

end

end OAI
