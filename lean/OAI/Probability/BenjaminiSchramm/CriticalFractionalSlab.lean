import OAI.Probability.BenjaminiSchramm.FractionalSlabFromTruncation
import OAI.Probability.BenjaminiSchramm.PeakRateCancellation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma fractional_exponential_product (A B Z : ℝ≥0∞) (t u k r a δ : ℝ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    (A*ENNReal.ofReal (Real.exp (t*r)))^a*
      (B*ENNReal.ofReal (Real.exp (u*(k+r))))^δ*Z =
    (A^a*B^δ*Z)*ENNReal.ofReal (Real.exp (δ*u*k+(a*t+δ*u)*r)) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha,ENNReal.mul_rpow_of_nonneg _ _ hδ,
    ennreal_exp_rpow _ _ ha,ennreal_exp_rpow _ _ hδ]
  calc
    _ = (A^a*B^δ*Z)*(ENNReal.ofReal (Real.exp (t*r*a))*
        ENNReal.ofReal (Real.exp (u*(k+r)*δ))) := by ac_rfl
    _ = _ := by
      rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
      rw [show t*r*a+u*(k+r)*δ=δ*u*k+(a*t+δ*u)*r by ring]

variable {V E : Type*} [Encodable V] [Countable E] [Infinite V]
    (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem critical_slab_fractional_of_peak_survival
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hpc1 : pc G < 1) (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (α : ℝ) (hα : 1 ≤ α) (hcross : ∀ t : ℝ, 0 ≤ t →
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t))
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (hsurv : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ ell : ℝ, 0 < ell →
      ENNReal.ofReal (c*Real.exp (-((α-1)+ε)*ell)) ≤
        (criticalModel G).fullPeakDownProbability
          ((criticalModel G).orbitRepresentatives (criticalModel_quasiTransitive G hq))
          ((criticalModel G).stationaryOrbitWeight μ) (pc G) ell) :
    ∃ L : ℝ, 0 < L ∧ ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ x : V,
        (∫⁻ ω, (restrictedLayerCount G
          (internalEdges G {z | -k-r ≤ (criticalModel G).orbitAdjustedHeight
            ((criticalModel G).stationaryOrbitWeight μ) x z ∧
              (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ≤ 0})
          {z | -k-R ≤ (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ∧
            (criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) x z ≤ -k+R}
          ω x)^q ∂law (pc G)) ≤ C*ENNReal.ofReal (Real.exp (ζ*k+L*r)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  let O := H.orbitRepresentatives (criticalModel_quasiTransitive G hq)
  obtain ⟨M,hM,K,hK,L₁,hL₁,hcmp⟩ := critical_peak_comparison_at_rate G hc hl hq hpc1 hu
    μ hμ hstat α hcross R hR hjump
  obtain ⟨C₀,L₀,hC₀,hL₀,hup⟩ := critical_normalized_halfspace_exp_bound G hc hl hq hu μ hμ hstat
  refine ⟨L₁+L₀,by positivity,fun q hq0 hq1 ζ hζ => ?_⟩
  let δ := min ((1-q)/2) (ζ/(L₀+1))
  have hδpos : 0 < δ := lt_min (by positivity) (div_pos hζ (by positivity))
  have hδq : δ ≤ 1-q := (min_le_left _ _).trans (by linarith)
  have hδ1 : δ ≤ 1 := by linarith
  have hδL : δ*L₀ ≤ ζ := by
    have hle : δ ≤ ζ/(L₀+1) := min_le_right _ _
    have hm := (le_div_iff₀ (show 0 < L₀+1 by positivity)).mp hle
    nlinarith
  let ε := δ/(2*q)
  have hε : 0 < ε := div_pos hδpos (by positivity)
  have heq : ε*q=δ/2 := by dsimp [ε]; field_simp
  obtain ⟨c,hcpos,hden⟩ := hsurv ε hε
  let A := ENNReal.ofReal c⁻¹*K*ENNReal.ofReal (Real.exp ε)
  let B := ENNReal.ofReal (C₀*Real.exp (L₀*(2*M+2*R)))
  let Z := ∑' n : ℕ, ENNReal.ofReal (Real.exp ((ε*q-δ)*n))
  have hA : A < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK) ENNReal.ofReal_lt_top
  have hB : B < ⊤ := ENNReal.ofReal_lt_top
  have hZ : Z < ⊤ := by
    simpa only [one_mul] using fractional_height_geometric_sum_lt_top (t := ε) (s := 1)
      (a := q) (δ := δ) (by rw [heq]; linarith)
  let C := A^q*B^δ*Z
  have hC : C < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0.le hA.ne)
      (ENNReal.rpow_lt_top_of_nonneg hδpos.le hB.ne)) hZ
  refine ⟨C,hC,fun k hk r hr x => ?_⟩
  let f := fun z => H.orbitAdjustedHeight a x z
  let D := internalEdges G {z | -k-r-2*M-2*R ≤ f z}
  let I := internalEdges G {z | -k-r ≤ f z ∧ f z ≤ 0}
  let W : Set V := {z | -k-R ≤ f z ∧ f z ≤ -k+R}
  have htrunc (n : ℕ) : (∫⁻ ω,
      (restrictedHit G D x {z | 1*((n : ℝ)+1) ≤ f z})ᶜ.indicator
        (fun ω => restrictedLayerCount G I W ω x) ω ∂law (pc G)) ≤
      (A*ENNReal.ofReal (Real.exp (L₁*r)))*ENNReal.ofReal (Real.exp (ε*n)) := by
    have hn : (0 : ℝ) < (n : ℝ)+1 := by positivity
    have hh := peak_rate_cancellation
      (H.fullPeakDownProbability O a (pc G) ((n : ℝ)+1))
      (H.mixedHeightLayerMoment a (pc G) (-k-r) 0 (-k-R) (-k+R)
        (-k-r-2*M-2*R) ((n : ℝ)+1) x) K c (α-1) ε ((n : ℝ)+1) k L₁ r hcpos
      (hden _ hn) (hcmp k hk r hr _ hn x)
    rw [H.mixedHeightLayerMoment_eq_lintegral] at hh
    change (∫⁻ ω,
      (restrictedHit G D x {z | (n : ℝ)+1 ≤ f z})ᶜ.indicator
        (fun ω => restrictedLayerCount G I W ω x) ω ∂law (pc G)) ≤ _ at hh
    simp only [one_mul]
    apply hh.trans
    have he : L₁*r+ε*((n : ℝ)+1)-(α-1)*k ≤ ε+L₁*r+ε*n := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hα) hk]
    calc
      _ ≤ ENNReal.ofReal c⁻¹*K*ENNReal.ofReal (Real.exp (ε+L₁*r+ε*n)) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))
      _ = _ := by
        dsimp [A]
        rw [Real.exp_add,Real.exp_add,
          ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp ε*Real.exp (L₁*r)),ENNReal.ofReal_mul (Real.exp_nonneg ε)]
        ac_rfl
  have hhit (n : ℕ) : law (pc G) (restrictedHit G D x {z | 1*n ≤ f z}) ≤
      (B*ENNReal.ofReal (Real.exp (L₀*(k+r))))*ENNReal.ofReal (Real.exp (-1*n)) := by
    have hh := hup (k+r+2*M+2*R) (by positivity) x n (Nat.cast_nonneg n)
    have he : -(k+r+2*M+2*R)= -k-r-2*M-2*R := by ring
    change law (pc G) (H.adjustedHalfspaceHit a x _ _) ≤ _ at hh
    unfold CriticalPercolation.BondGraph.adjustedHalfspaceHit at hh
    rw [he] at hh
    change law (pc G) (restrictedHit G D x {z | (n : ℝ) ≤ f z}) ≤ _ at hh
    simp only [one_mul,neg_mul,one_mul]
    apply hh.trans_eq
    have he : C₀*Real.exp (L₀*(k+r+2*M+2*R)-(n : ℝ)) =
      (C₀*Real.exp (L₀*(2*M+2*R)))*Real.exp (L₀*(k+r))*Real.exp (-(n : ℝ)) := by
      rw [mul_assoc,mul_assoc,←Real.exp_add,←Real.exp_add]
      congr 2
      ring
    rw [he,ENNReal.ofReal_mul (by positivity : 0 ≤ C₀*Real.exp (L₀*(2*M+2*R))*Real.exp (L₀*(k+r))),
      ENNReal.ofReal_mul (by positivity : 0 ≤ C₀*Real.exp (L₀*(2*M+2*R)))]
  have hfin : ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite :=
    critical_finite_general G hc hl hq hpc1 x
  have hh := layer_fractional_of_truncated_moments G (pc G) D I W f 1 zero_lt_one x
    (by exact H.orbitAdjustedHeight_self a x) hfin
    (A*ENNReal.ofReal (Real.exp (L₁*r))) (B*ENNReal.ofReal (Real.exp (L₀*(k+r))))
    ε htrunc hhit hq0 hq1 hδpos.le hδq
  change (∫⁻ ω, (restrictedLayerCount G I W ω x)^q ∂law (pc G)) ≤ _
  apply hh.trans
  simp only [one_mul] at hh ⊢
  change (A*ENNReal.ofReal (Real.exp (L₁*r)))^q*
      (B*ENNReal.ofReal (Real.exp (L₀*(k+r))))^δ*Z ≤ _
  rw [fractional_exponential_product A B Z L₁ L₀ k r q δ hq0.le hδpos.le]
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hqL : q*L₁ ≤ L₁ := mul_le_of_le_one_left hL₁.le hq1.le
  have hδL₀ : δ*L₀ ≤ L₀ := mul_le_of_le_one_left hL₀.le hδ1
  have hkk := mul_le_mul_of_nonneg_right hδL hk
  have hrr := mul_le_mul_of_nonneg_right (add_le_add hqL hδL₀) hr
  linarith

end Percolation.BenjaminiSchramm

end

end OAI
