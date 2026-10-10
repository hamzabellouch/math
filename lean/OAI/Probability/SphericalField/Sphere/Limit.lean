import Mathlib
import OAI.Probability.SphericalField.Sphere.Shell

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

lemma normalizedCoordinateSphereLog_measurable (n k : ℕ) (σ : ℕ → ℝ) :
    Measurable (normalizedCoordinateSphereLog n k σ) := by
  have hm := (coordinateAngularLog_measurable n k σ (Real.sqrt (n+1:ℕ))).comp
    (show Measurable (fun p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k =>
      ((fun (i : Fin (n+1)) (_ : ℕ) => p.1 i),p.2)) from by fun_prop)
  exact hm.div_const _

lemma normalizedCoordinateSphereLog_integrable (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ}
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b k z) (r : ℝ≥0) :
    Integrable (normalizedCoordinateSphereLog n k σ) (coordinateCascadeLaw (n+1) k z r) :=
  (coordinateAngularLog_integrable n k σ (Real.sqrt (n+1:ℕ)) z hz hz0 hz1 hp r).div_const _

lemma normalizedCoordinateSphereLog_nonneg (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ}
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b k z) (r : ℝ≥0) :
    0 ≤ᵐ[coordinateCascadeLaw (n+1) k z r] normalizedCoordinateSphereLog n k σ := by
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  filter_upwards [canonicalCoordinateBase_pos (n+1) k σ z hz hz0 hz1 r,
    canonicalCoordinateTotal_pos (n+1) k σ b z hz hz0 hz1 hp r] with p h0 hc
  exact div_nonneg (coordinateAngularLog_regular n k σ _ hb _ h0 hc).2.1 (by positivity)

lemma expectedCoordinateSphereLog_upper (n k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b k z) (r : ℝ≥0)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hm : 0 < (canonicalRadialMass n b).real (normSquareBand n ε)) :
    expectedCoordinateSphereLog n k σ z r ≤
      (1+ε)*canonicalGaussianFreeValue σ k z r b-
        Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1:ℕ):ℝ)+
          ε*(Real.log b/2+2*b) := by
  let μ := coordinateCascadeLaw (n+1) k z r
  let C := fun p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k =>
    canonicalCoordinateLog (n+1) k σ b ((fun i _ => p.1 i),p.2)
  let M := Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))
  let d : ℝ := n+1
  have hd : 0 < d := by dsimp [d]; positivity
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  have hi : Integrable C μ := (canonical_coordinate_joint_mean (n+1) σ b k z hz hz0 hz1 hp r).1
  have he : (∫ p, C p ∂μ) = d*canonicalGaussianFreeValue σ k z r b := by
    simpa [d,C,μ,coordinateCascadeLaw] using (canonical_coordinate_joint_mean (n+1) σ b k z hz hz0 hz1 hp r).2
  have hni := normalizedCoordinateSphereLog_integrable n k σ z hz hz0 hz1 hp r
  have hbi : Integrable (fun p => (1+ε)*C p/d-M/d+ε*(Real.log b/2+2*b)) μ :=
    (((hi.const_mul (1+ε)).div_const d).sub (integrable_const _)).add (integrable_const _)
  have hlo : ∀ᵐ p ∂μ, normalizedCoordinateSphereLog n k σ p ≤
      (1+ε)*C p/d-M/d+ε*(Real.log b/2+2*b) := by
    filter_upwards [canonicalCoordinateBase_pos (n+1) k σ z hz hz0 hz1 r,
      canonicalCoordinateTotal_pos (n+1) k σ b z hz hz0 hz1 hp r] with p h0 hc
    have hraw := canonicalCoordinate_unitSphere_upper n k σ hb hε hε1 _ h0 hc hm
    have hh := div_le_div_of_nonneg_right hraw hd.le
    have heq : ((1+ε)*C p-M+ε*((n+1:ℕ):ℝ)*(Real.log b/2+2*b))/d =
        (1+ε)*C p/d-M/d+ε*(Real.log b/2+2*b) := by
      dsimp only [d]
      push_cast
      field_simp
    change coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) ((fun i _ => p.1 i),p.2)/d ≤
      ((1+ε)*C p-M+ε*((n+1:ℕ):ℝ)*(Real.log b/2+2*b))/d at hh
    rw [heq] at hh
    simpa only [normalizedCoordinateSphereLog,d,Nat.cast_add,Nat.cast_one] using hh
  have hh := integral_mono_ae hni hbi hlo
  have hcalc : (∫ p, (1+ε)*C p/d-M/d+ε*(Real.log b/2+2*b) ∂μ) =
      (1+ε)*canonicalGaussianFreeValue σ k z r b-M/d+ε*(Real.log b/2+2*b) := by
    rw [integral_add (f := fun p => (1+ε)*C p/d-M/d)
      (g := fun _ => ε*(Real.log b/2+2*b))
      (((hi.const_mul (1+ε)).div_const d).sub (integrable_const (M/d)))
      (integrable_const (ε*(Real.log b/2+2*b))),
      integral_sub (f := fun p => (1+ε)*C p/d) (g := fun _ => M/d)
        ((hi.const_mul (1+ε)).div_const d) (integrable_const (M/d)),
      integral_div,integral_const_mul,he]
    simp only [integral_const,probReal_univ,one_smul]
    field_simp
  rw [hcalc] at hh
  simpa [expectedCoordinateSphereLog,M,d] using hh

lemma expectedCoordinateSphereLog_upper_eventually (k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b k z) (r : ℝ≥0) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, expectedCoordinateSphereLog n k σ z r ≤
      canonicalGaussianFreeValue σ k z r b+(b-1)/2+
        ε*(canonicalGaussianFreeValue σ k z r b+Real.log b/2+2*b+|1-b|/2)+
          Real.log 2/((n+1:ℕ):ℝ) := by
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  filter_upwards [canonicalRadial_band_eventually_half hε hε1] with n hn
  have hm := (canonicalRadial_band_mass_bounds n hb hn).1
  have hmp : 0 < (canonicalRadialMass n b).real (normSquareBand n ε) :=
    (by positivity : 0 < Real.exp (((n+1:ℕ):ℝ)*((1-b)/2-|1-b| * ε/2))/2).trans_le hm
  have hu := expectedCoordinateSphereLog_upper n k σ z hz hz0 hz1 hp r hε.le hε1.le hmp
  have hl := (canonicalRadial_band_log_bounds n hb hn).1
  linarith

lemma normalizedCoordinateSphereLog_lower_probability (k : ℕ) (σ : ℕ → ℝ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (r : ℝ≥0) (b : ℝ) (hp : 0 < quadraticCascadePrecision σ b k z)
    (hstat : -1/(2*b)+quadraticCascadeReciprocalSlope σ b k z-
      (r:ℝ)/(2*(quadraticCascadePrecision σ b k z)^2) = -1/2)
    {ε a : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (ha : a < canonicalGaussianFreeValue σ k z r b+(b-1)/2-
      ε*(canonicalGaussianFreeValue σ k z r b+Real.log b/2+2*b+|1-b|/2)) :
    Tendsto (fun n : ℕ => (coordinateCascadeLaw (n+1) k z r).real
      {p | a ≤ normalizedCoordinateSphereLog n k σ p}) atTop (𝓝 1) := by
  let C := canonicalGaussianFreeValue σ k z r b
  let K := Real.log b/2+2*b
  let L := C+(b-1)/2-ε*(C+K+|1-b|/2)
  let δ := L-a
  have hδ : 0 < δ := by
    apply sub_pos.mpr
    simpa [L,C,K,add_assoc] using ha
  let μ := fun n => coordinateCascadeLaw (n+1) k z r
  let F := fun n (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) =>
    canonicalCoordinateLog (n+1) k σ b ((fun i _ => p.1 i),p.2)
  let B := fun n => {p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k |
    (canonicalCoordinateBandTotalE n k σ b ε ((fun i _ => p.1 i),p.2)).toReal <
      decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ)
        (canonicalCoordinatePotential (n+1) b) k ((fun i _ => p.1 i),p.2)/2}
  let D := fun n => {p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k |
    (δ/2)*((n+1:ℕ):ℝ) ≤ |F n p-((n+1:ℕ):ℝ)*C|}
  have hB : Tendsto (fun n => μ n (B n)) atTop (𝓝 0) :=
    canonicalCoordinate_bad_half_band_tendsto_zero k σ z hz hz0 hz1 r b hp hstat hε
  have hD : Tendsto (fun n => μ n (D n)) atTop (𝓝 0) :=
    (canonical_coordinate_converges σ b k z hz hz0 hz1 hp r (half_pos hδ)).comp
      (tendsto_add_atTop_nat 1)
  have hsum := hB.add hD
  simp only [add_zero] at hsum
  have ht : Tendsto (fun n : ℕ => Real.log 2/((n+1:ℕ):ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hev : ∀ᶠ n : ℕ in atTop, Real.log 2/((n+1:ℕ):ℝ) < δ/2 :=
    ht.eventually (gt_mem_nhds (half_pos hδ))
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  have hbad : Tendsto (fun n => μ n {p | normalizedCoordinateSphereLog n k σ p < a}) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall (fun _ => bot_le))
    filter_upwards [hev,canonicalRadial_band_eventually_half hε hε1] with n hn hhalf
    apply le_trans (measure_mono_ae (t := B n ∪ D n) ?_) (measure_union_le _ _)
    filter_upwards [canonicalCoordinateBase_pos (n+1) k σ z hz hz0 hz1 r,
      canonicalCoordinateTotal_pos (n+1) k σ b z hz hz0 hz1 hp r] with p h0 hc
    intro hbad
    by_cases hpB : p ∈ B n
    · exact Or.inl hpB
    · right
      by_contra hpD
      have hm := (canonicalRadial_band_mass_bounds n hb hhalf).1
      have hmp : 0 < (canonicalRadialMass n b).real (normSquareBand n ε) :=
        (by positivity : 0 < Real.exp (((n+1:ℕ):ℝ)*((1-b)/2-|1-b| * ε/2))/2).trans_le hm
      have hu := (canonicalRadial_band_log_bounds n hb hhalf).2
      have hraw := canonicalCoordinate_unitSphere_lower n k σ hb hε.le hε1.le _ h0 hc hmp
        (le_of_not_gt hpB)
      have hd : 0 < ((n+1:ℕ):ℝ) := by positivity
      have hlow := (div_le_div_of_nonneg_right hraw hd.le)
      have herr : |F n p-((n+1:ℕ):ℝ)*C| < (δ/2)*((n+1:ℕ):ℝ) := not_le.mp hpD
      have herr' : C-δ/2 < F n p/((n+1:ℕ):ℝ) := by
        apply (lt_div_iff₀ hd).mpr
        have hh := (abs_lt.mp herr).1
        nlinarith
      have he : ((1-ε)*F n p-Real.log 2-
          Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))-
          ε*((n+1:ℕ):ℝ)*K)/((n+1:ℕ):ℝ) =
          (1-ε)*(F n p/((n+1:ℕ):ℝ))-Real.log 2/((n+1:ℕ):ℝ)-
          Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1:ℕ):ℝ)-ε*K := by
        field_simp
      change ((1-ε)*F n p-Real.log 2-
          Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))-
          ε*((n+1:ℕ):ℝ)*K)/((n+1:ℕ):ℝ) ≤ normalizedCoordinateSphereLog n k σ p at hlow
      rw [he] at hlow
      have hmule := mul_lt_mul_of_pos_left herr' (sub_pos.mpr hε1)
      have haeq : a = L-δ := by dsimp [δ]; ring
      change normalizedCoordinateSphereLog n k σ p < a at hbad
      dsimp only [L] at haeq
      nlinarith [mul_nonneg hε.le hδ.le]
  have hreal : Tendsto (fun n => (μ n).real {p | normalizedCoordinateSphereLog n k σ p < a}) atTop (𝓝 0) := by
    exact (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ⊤)).comp hbad
  have hone : Tendsto (fun n => 1-(μ n).real {p | normalizedCoordinateSphereLog n k σ p < a}) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hreal
  convert hone using 1
  ext n
  have hmeas : MeasurableSet {p | normalizedCoordinateSphereLog n k σ p < a} :=
    measurableSet_lt (normalizedCoordinateSphereLog_measurable n k σ) measurable_const
  rw [← probReal_compl_eq_one_sub hmeas]
  congr 1
  ext p
  simp only [mem_compl_iff,mem_ofPred_eq,not_lt]

lemma expectedCoordinateSphereLog_lower_eventually (k : ℕ) (σ : ℕ → ℝ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (r : ℝ≥0) (b : ℝ) (hp : 0 < quadraticCascadePrecision σ b k z)
    (hstat : -1/(2*b)+quadraticCascadeReciprocalSlope σ b k z-
      (r:ℝ)/(2*(quadraticCascadePrecision σ b k z)^2) = -1/2)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ a : ℝ, a < canonicalGaussianFreeValue σ k z r b+(b-1)/2-
      ε*(canonicalGaussianFreeValue σ k z r b+Real.log b/2+2*b+|1-b|/2) →
    ∀ᶠ n : ℕ in atTop, a < expectedCoordinateSphereLog n k σ z r := by
  apply expected_eventually_gt_of_probability_lower
    (fun n => coordinateCascadeLaw (n+1) k z r) (fun n => normalizedCoordinateSphereLog n k σ)
    (fun n => normalizedCoordinateSphereLog_integrable n k σ z hz hz0 hz1 hp r)
    (fun n => normalizedCoordinateSphereLog_nonneg n k σ z hz hz0 hz1 hp r)
  exact fun a ha => normalizedCoordinateSphereLog_lower_probability k σ z hz hz0 hz1 r b hp hstat hε hε1 ha

theorem expectedCoordinateSphereLog_tendsto (k : ℕ) (σ : ℕ → ℝ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (r : ℝ≥0) (b : ℝ) (hp : 0 < quadraticCascadePrecision σ b k z)
    (hstat : -1/(2*b)+quadraticCascadeReciprocalSlope σ b k z-
      (r:ℝ)/(2*(quadraticCascadePrecision σ b k z)^2) = -1/2) :
    Tendsto (fun n : ℕ => expectedCoordinateSphereLog n k σ z r) atTop
      (𝓝 (canonicalGaussianFreeValue σ k z r b+(b-1)/2)) := by
  let T := canonicalGaussianFreeValue σ k z r b+(b-1)/2
  let A := canonicalGaussianFreeValue σ k z r b+Real.log b/2+2*b+|1-b|/2
  let e := fun j : ℕ => 1/((j+1:ℕ):ℝ)
  have he : Tendsto e atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have he0 : ∀ j, 0 < e j := by intro j; dsimp [e]; positivity
  have he1 : ∀ᶠ j in atTop, e j < 1 := he.eventually (gt_mem_nhds zero_lt_one)
  have hl : Tendsto (fun j => T-e j*A) atTop (𝓝 T) := by
    simpa using tendsto_const_nhds.sub (he.mul_const A)
  have hu : Tendsto (fun j => T+e j*A) atTop (𝓝 T) := by
    simpa using tendsto_const_nhds.add (he.mul_const A)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨j,hj1,hja⟩ := (he1.and (hl.eventually (lt_mem_nhds ha))).exists
    exact expectedCoordinateSphereLog_lower_eventually k σ z hz hz0 hz1 r b hp hstat (he0 j) hj1 a hja
  · intro a ha
    obtain ⟨j,hj1,hja⟩ := (he1.and (hu.eventually (gt_mem_nhds ha))).exists
    have ht : Tendsto (fun n : ℕ => T+e j*A+Real.log 2/((n+1:ℕ):ℝ)) atTop (𝓝 (T+e j*A)) := by
      have hh : Tendsto (fun n : ℕ => Real.log 2/((n+1:ℕ):ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      simpa using tendsto_const_nhds.add hh
    filter_upwards [expectedCoordinateSphereLog_upper_eventually k σ z hz hz0 hz1 hp r (he0 j) hj1,
      ht.eventually (gt_mem_nhds hja)] with n hn hn'
    exact hn.trans_lt hn'

end SphericalPerceptron
end
end

end OAI
