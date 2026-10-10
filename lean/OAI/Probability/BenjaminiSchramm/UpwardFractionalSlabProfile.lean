import OAI.Probability.BenjaminiSchramm.SlabFractionalProfileShift
import OAI.Probability.BenjaminiSchramm.SlabCountBasic
import OAI.Probability.BenjaminiSchramm.FractionalSlabEstimate
import OAI.Probability.BenjaminiSchramm.CriticalFractionalSlab

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
lemma fractional_two_profile_product (A B : ℝ≥0∞) (t u v w k r a δ : ℝ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    (A*ENNReal.ofReal (Real.exp (t*k+u*r)))^a*
      (B*ENNReal.ofReal (Real.exp (v*k+w*r)))^δ =
      (A^a*B^δ)*ENNReal.ofReal (Real.exp ((a*t+δ*v)*k+(a*u+δ*w)*r)) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha,ENNReal.mul_rpow_of_nonneg _ _ hδ,
    ennreal_exp_rpow _ _ ha,ennreal_exp_rpow _ _ hδ]
  calc
    _ = (A^a*B^δ)*(ENNReal.ofReal (Real.exp ((t*k+u*r)*a))*
        ENNReal.ofReal (Real.exp ((v*k+w*r)*δ))) := by ac_rfl
    _ = _ := by
      rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
      rw [show (t*k+u*r)*a+(v*k+w*r)*δ=(a*t+δ*v)*k+(a*u+δ*w)*r by ring]

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem upward_fractional_slab_profile [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
    (L₁ L₂ : ℝ)
    (hprofile₁ : G.lowerSlabFractionalProfile (G.stationaryOrbitWeight μ) p R L₁)
    (hprofile₂ : G.lowerSlabFractionalProfile (G.stationaryOrbitWeight μ) p (2*R) L₂) :
    ∃ U : ℝ, 0 < U ∧ ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ x : V,
        (∫⁻ ω, (G.adjustedSlabBandCount (G.stationaryOrbitWeight μ) (-r) (k+r) (k-R) (k+R) ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp ((-1+ζ)*k+U*r)) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨T₁,hT₁,hshift₁⟩ := G.finite_ceiling_fractional_profile hc hl hq μ hμ hstat hu R hR hjump
    p hp0 hp1 L₁ hprofile₁
  have hjump₂ : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ 2*R := by
    intro e v w hv hw
    exact (hjump e v w hv hw).trans (by linarith)
  obtain ⟨T₂,hT₂,hshift₂⟩ := G.finite_ceiling_fractional_profile hc hl hq μ hμ hstat hu
    (2*R) (by positivity) hjump₂ p hp0 hp1 L₂ hprofile₂
  obtain ⟨m,M,hm,hbounds⟩ := G.stationaryOrbitWeight_uniform_bounds hc hl μ hμ
  let O := G.orbitRepresentatives hq
  let D := (ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r))*ENNReal.ofReal (Real.exp R)
  have hD : D < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hm))
      (ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top
  let U := |L₁|+T₁+|L₂|+T₂+1
  refine ⟨U,by dsimp [U]; positivity,?_⟩
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
  let δ := min ((1-q')/2) (ζ/(4*(T₂+1)))
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hζ (by positivity))
  have hδq' : δ ≤ 1-q' := (min_le_left _ _).trans (by linarith)
  have hδ1 : δ < 1 := by linarith
  have hδT : δ*T₂ ≤ ζ/4 := by
    have hh := (le_div_iff₀ (show 0 < 4*(T₂+1) by positivity)).mp (min_le_right ((1-q')/2) (ζ/(4*(T₂+1))))
    change δ*(4*(T₂+1)) ≤ ζ at hh
    nlinarith
  let ε := min (ζ/4) (1/2)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hεζ : ε ≤ ζ/4 := min_le_left _ _
  obtain ⟨C₁,hC₁,hbound₁⟩ := hshift₁ (1-δ) (by linarith) (by linarith) ε hε hε1
  obtain ⟨C₂,hC₂,hbound₂⟩ := hshift₂ q' hq'0 hq'1 ε hε hε1
  let Q := C₁*ENNReal.ofReal (Real.exp (L₁*R+T₁*R))
  let Z := C₂*ENNReal.ofReal (Real.exp (L₂*(2*R)+T₂*(2*R)))
  have hQ : Q < ⊤ := ENNReal.mul_lt_top hC₁ ENNReal.ofReal_lt_top
  have hZ : Z < ⊤ := ENNReal.mul_lt_top hC₂ ENNReal.ofReal_lt_top
  let A := D*Q
  have hA : A < ⊤ := ENNReal.mul_lt_top hD hQ
  let C := A^q'*Z^δ
  have hC : C < ⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hq'0.le hA.ne) (ENNReal.rpow_lt_top_of_nonneg hδ.le hZ.ne)
  refine ⟨C,hC,fun k hk r hr x => ?_⟩
  have hzero : (∫⁻ ω, (G.adjustedSlabBandCount a (-r-2*R) (k+r+2*R) (-2*R) (2*R) ω x)^q' ∂G.law p) ≤
      Z*ENNReal.ofReal (Real.exp (T₂*k+(L₂+T₂)*r)) := by
    have hh := hbound₂ 0 (by norm_num) (r+2*R) (by positivity) (k+r+2*R) (by positivity) x
    simp only [neg_zero,zero_sub,zero_add,mul_zero] at hh
    rw [←neg_mul] at hh
    rw [show -(r+2*R)= -r-2*R by ring] at hh
    apply hh.trans_eq
    dsimp [Z]
    rw [mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
    rw [show L₂*(r+2*R)+T₂*(k+r+2*R)=(L₂*(2*R)+T₂*(2*R))+(T₂*k+(L₂+T₂)*r) by ring]
  have hdown (y : V) : (∫⁻ ω, (G.adjustedSlabBandCount a (-k-r-R) (r+R) (-k-R) (-k+R) ω y)^(1-δ) ∂G.law p) ≤
      Q*ENNReal.ofReal (Real.exp (ε*k+(L₁+T₁)*r)) := by
    have hh := hbound₁ k hk (r+R) (by positivity) (r+R) (by positivity) y
    rw [show -k-(r+R)= -k-r-R by ring] at hh
    apply hh.trans_eq
    dsimp [Q]
    rw [mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
    rw [show ε*k+L₁*(r+R)+T₁*(r+R)=(L₁*R+T₁*R)+(ε*k+(L₁+T₁)*r) by ring]
  have hZfin : ∀ᵐ ω ∂G.law p,
      1 ≤ G.adjustedSlabBandCount a (-r-2*R) (k+r+2*R) (-2*R) (2*R) ω x ∧
      G.adjustedSlabBandCount a (-r-2*R) (k+r+2*R) (-2*R) (2*R) ω x ≠ ⊤ := by
    filter_upwards [hfin x] with ω hω
    exact ⟨by simpa only [neg_mul] using
      G.one_le_adjustedSlabZeroBandCount a (-r-2*R) (k+r+2*R) (2*R) (by positivity) ω x,
      (G.adjustedSlabBandCount_lt_top_of_finite a _ _ _ _ ω x hω).ne⟩
  have hwidth : (k+R)-(k-R)=2*R := by ring
  have hnegl : -(k-R)= -k+R := by ring
  have hnegu : -(k+R)= -k-R := by ring
  have hlow : -r-2*R- (k-R)= -k-r-R := by ring
  have hhigh : k+r+2*R-(k+R)=r+R := by ring
  have hfwlo : -r-2*R+2*R= -r := by ring
  have hfwup : k+r+2*R-2*R=k+r := by ring
  have hminus : (k-R)-(k+R)= -2*R := by ring
  have hh := G.fractional_slab_band_estimate O hc hl a (G.stationaryOrbitWeight_pos hc hl μ hμ)
    (G.stationaryOrbitWeight_aut μ) m hm (fun z => (hbounds z).1) p (-r-2*R) (k+r+2*R) (k-R) (k+R) x
    hq'0 hq'1 hδ.le hδq'
    (by simpa only [hminus,hwidth] using hZfin)
    (Z*ENNReal.ofReal (Real.exp (T₂*k+(L₂+T₂)*r))) (Q*ENNReal.ofReal (Real.exp (ε*k+(L₁+T₁)*r)))
    (by simpa only [hminus,hwidth] using hzero)
    (fun y _ => by simpa only [hlow,hhigh,hnegu,hnegl] using hdown y)
  simp only [hwidth,hfwlo,hfwup] at hh
  have hfactor : (((ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp (-(k-R)))*
      (∑ r ∈ O.roots, ENNReal.ofReal (a r)))*(Q*ENNReal.ofReal (Real.exp (ε*k+(L₁+T₁)*r)))) =
        A*ENNReal.ofReal (Real.exp ((ε-1)*k+(L₁+T₁)*r)) := by
    dsimp [A,D]
    have he : Real.exp (-(k-R))*Real.exp (ε*k+(L₁+T₁)*r)=Real.exp R*Real.exp ((ε-1)*k+(L₁+T₁)*r) := by
      rw [←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    calc
      _ = ((ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r))*Q)*
          (ENNReal.ofReal (Real.exp (-(k-R)))*ENNReal.ofReal (Real.exp (ε*k+(L₁+T₁)*r))) := by ac_rfl
      _ = _ := by
        rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),he,ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
  rw [hfactor] at hh
  have heq : (A*ENNReal.ofReal (Real.exp ((ε-1)*k+(L₁+T₁)*r)))^q'*
      (Z*ENNReal.ofReal (Real.exp (T₂*k+(L₂+T₂)*r)))^δ =
      C*ENNReal.ofReal (Real.exp ((q'*(ε-1)+δ*T₂)*k+(q'*(L₁+T₁)+δ*(L₂+T₂))*r)) :=
    fractional_two_profile_product A Z (ε-1) (L₁+T₁) T₂ (L₂+T₂) k r q' δ hq'0.le hδ.le
  have hmono : (∫⁻ ω, (G.adjustedSlabBandCount a (-r) (k+r) (k-R) (k+R) ω x)^q ∂G.law p) ≤
      ∫⁻ ω, (G.adjustedSlabBandCount a (-r) (k+r) (k-R) (k+R) ω x)^q' ∂G.law p :=
    lintegral_mono (fun ω => G.adjustedSlabBandCount_rpow_mono_exponent a _ _ _ _ ω x hq0 hqq')
  apply (hmono.trans hh).trans
  rw [heq]
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hqε : q'*ε ≤ ε := mul_le_of_le_one_left hε.le hq'1.le
  have hrate : q'*(ε-1)+δ*T₂ ≤ -1+ζ := by dsimp [q'] at hqε ⊢; nlinarith
  have hcoef₁ : q'*(L₁+T₁) ≤ |L₁|+T₁ :=
    (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) le_rfl) hq'0.le).trans
      (mul_le_of_le_one_left (by positivity) hq'1.le)
  have hcoef₂ : δ*(L₂+T₂) ≤ |L₂|+T₂ :=
    (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) le_rfl) hδ.le).trans
      (mul_le_of_le_one_left (by positivity) hδ1.le)
  have hcoeff : q'*(L₁+T₁)+δ*(L₂+T₂) ≤ U := by dsimp [U]; linarith
  exact add_le_add (mul_le_mul_of_nonneg_right hrate hk) (mul_le_mul_of_nonneg_right hcoeff hr)

end CriticalPercolation.BondGraph

end

end OAI
