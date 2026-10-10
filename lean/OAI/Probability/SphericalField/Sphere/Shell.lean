import Mathlib
import OAI.Probability.SphericalField.Sphere.WeightedBands
import OAI.Probability.SphericalField.Sphere.Bridge

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

lemma canonicalWeighted_compl_band_le (n : ℕ) (F : RadialSpace n → ℝ≥0∞)
    (hF : Measurable F) (b ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫⁻ x in (normSquareBand n ε)ᶜ, F x ∂canonicalRadialMass n b) ≤
      ENNReal.ofReal (Real.exp (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)) *
        (∫⁻ x, F x ∂canonicalRadialMass n (b-δ)) +
      ENNReal.ofReal (Real.exp (δ*((n+1:ℕ):ℝ)*(1-ε)/2)) *
        (∫⁻ x, F x ∂canonicalRadialMass n (b+δ)) := by
  have hs : (normSquareBand n ε)ᶜ ⊆
      {x : RadialSpace n | ((n+1:ℕ):ℝ)*(1+ε) ≤ ‖x‖^2} ∪
      {x : RadialSpace n | ‖x‖^2 ≤ ((n+1:ℕ):ℝ)*(1-ε)} := by
    intro x hx
    simp only [normSquareBand,mem_compl_iff,mem_ofPred_eq,not_and_or,not_le] at hx
    rcases hx with hx | hx
    · exact Or.inr hx.le
    · exact Or.inl hx.le
  exact (lintegral_mono_set hs).trans ((lintegral_union_le _ _ _).trans
    (add_le_add (canonicalWeighted_upper_tail n F hF b ε hδ)
      (canonicalWeighted_lower_tail n F hF b ε hδ)))

lemma exp_log_quotient_mul {x y u : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hu : 0 < u) (c : ℝ) :
    Real.exp (Real.log (y/u)-Real.log (x/u)+c)*x = Real.exp c*y := by
  rw [Real.exp_add,Real.exp_sub,Real.exp_log (div_pos hy hu),
    Real.exp_log (div_pos hx hu)]
  field_simp

def canonicalCoordinateBandTotalE (n k : ℕ) (σ : ℕ → ℝ) (b ε : ℝ)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) : ℝ≥0∞ :=
  ∫⁻ x in normSquareBand n ε,
    decoratedFieldFactor (n+1) (canonicalCoordinateStep (n+1) σ)
      (coordinateLeafField (n+1)) k p x ∂canonicalRadialMass n b

lemma canonicalCoordinateBandTotalE_le (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ}
    (hb : 0 < b) (ε : ℝ)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) :
    canonicalCoordinateBandTotalE n k σ b ε p ≤
      decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ)
        (canonicalCoordinatePotential (n+1) b) k p := by
  rw [canonicalCoordinateTotalE_eq_radial n k σ hb]
  exact setLIntegral_le_lintegral _ _

lemma canonicalCoordinate_half_band (n k : ℕ) (σ : ℕ → ℝ) {b δ : ℝ}
    (hb : 0 < b) (hδ : 0 ≤ δ) (hbm : 0 < b-δ) (ε : ℝ)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p)
    (hm : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) (b-δ)) k p)
    (hp : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) (b+δ)) k p)
    (hrm : Real.exp (canonicalCoordinateLog (n+1) k σ (b-δ) p -
      canonicalCoordinateLog (n+1) k σ b p - ((n+1:ℕ):ℝ)*(δ*(1+ε)/2)) ≤ 1/4)
    (hrp : Real.exp (canonicalCoordinateLog (n+1) k σ (b+δ) p -
      canonicalCoordinateLog (n+1) k σ b p - ((n+1:ℕ):ℝ)*(-δ*(1-ε)/2)) ≤ 1/4) :
    decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ)
        (canonicalCoordinatePotential (n+1) b) k p / 2 ≤
      (canonicalCoordinateBandTotalE n k σ b ε p).toReal := by
  let F := decoratedFieldFactor (n+1) (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p
  have hF : Measurable F := decoratedFieldFactor_measurable (n+1) _
    (canonicalCoordinateStep_measurable (n+1) σ) _ (coordinateLeafField_measurable (n+1)) k p
  let T := fun a => decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ)
    (canonicalCoordinatePotential (n+1) a) k p
  let B := canonicalCoordinateBandTotalE n k σ b ε p
  have ht : T b ≠ ∞ := (ENNReal.toReal_pos_iff.mp hc).2.ne
  have hmt : T (b-δ) ≠ ∞ := (ENNReal.toReal_pos_iff.mp hm).2.ne
  have hpt : T (b+δ) ≠ ∞ := (ENNReal.toReal_pos_iff.mp hp).2.ne
  have hBt : B ≠ ∞ := ne_top_of_le_ne_top ht (canonicalCoordinateBandTotalE_le n k σ hb ε p)
  have he := lintegral_add_compl F (μ := canonicalRadialMass n b) (normSquareBand_measurable n ε)
  have hu := canonicalWeighted_compl_band_le n F hF b ε hδ
  have hbp : 0 < b+δ := add_pos_of_pos_of_nonneg hb hδ
  have hid (a : ℝ) (ha : 0 < a) : (∫⁻ x, F x ∂canonicalRadialMass n a) = T a :=
    (canonicalCoordinateTotalE_eq_radial n k σ ha p).symm
  rw [hid b hb] at he
  rw [hid (b-δ) hbm,hid (b+δ) hbp] at hu
  have hbnd : T b ≤ B + (ENNReal.ofReal (Real.exp (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)) * T (b-δ) +
      ENNReal.ofReal (Real.exp (δ*((n+1:ℕ):ℝ)*(1-ε)/2)) * T (b+δ)) := by
    rw [← he]
    exact add_le_add le_rfl hu
  have hre := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hBt,
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpt⟩⟩) hbnd
  rw [ENNReal.toReal_add hBt (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpt⟩),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpt),ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,ENNReal.toReal_ofReal (Real.exp_pos _).le] at hre
  have hem := exp_log_quotient_mul hc hm h0 (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)
  have hep := exp_log_quotient_mul hc hp h0 (δ*((n+1:ℕ):ℝ)*(1-ε)/2)
  change Real.exp (canonicalCoordinateLog (n+1) k σ (b-δ) p-
    canonicalCoordinateLog (n+1) k σ b p + _) * (T b).toReal =
      Real.exp (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)*(T (b-δ)).toReal at hem
  change Real.exp (canonicalCoordinateLog (n+1) k σ (b+δ) p-
    canonicalCoordinateLog (n+1) k σ b p + _) * (T b).toReal =
      Real.exp (δ*((n+1:ℕ):ℝ)*(1-ε)/2)*(T (b+δ)).toReal at hep
  change 0 < (T b).toReal at hc
  have hm' : Real.exp (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)*(T (b-δ)).toReal ≤ (T b).toReal/4 := by
    rw [← hem]
    convert mul_le_mul_of_nonneg_right hrm hc.le using 1 <;> congr 1 <;> ring_nf
  have hp' : Real.exp (δ*((n+1:ℕ):ℝ)*(1-ε)/2)*(T (b+δ)).toReal ≤ (T b).toReal/4 := by
    rw [← hep]
    convert mul_le_mul_of_nonneg_right hrp hc.le using 1 <;> congr 1 <;> ring_nf
  change (T b).toReal/2 ≤ B.toReal
  linarith

theorem canonicalCoordinate_bad_half_band_tendsto_zero (k : ℕ) (σ : ℕ → ℝ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (r : ℝ≥0) (b : ℝ) (hp : 0 < quadraticCascadePrecision σ b k z)
    (hstat : -1/(2*b)+quadraticCascadeReciprocalSlope σ b k z-
      (r:ℝ)/(2*(quadraticCascadePrecision σ b k z)^2) = -1/2)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => coordinateCascadeLaw (n+1) k z r
      {p | (canonicalCoordinateBandTotalE n k σ b ε ((fun i _ => p.1 i),p.2)).toReal <
        decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ)
          (canonicalCoordinatePotential (n+1) b) k ((fun i _ => p.1 i),p.2)/2}) atTop (𝓝 0) := by
  obtain ⟨δ,hδ,hpm,hpp,hrm,hrp⟩ := canonical_stationary_tail_rates σ k z
    (fun i => (hz0 i).le) r b hp hstat hε
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  have hbm : 0 < b-δ := hpm.trans_le (quadraticCascadePrecision_le σ (b-δ) k z (fun i => (hz0 i).le))
  let Xm := fun n (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) =>
    Real.exp (canonicalCoordinateLog (n+1) k σ (b-δ) ((fun i _ => p.1 i),p.2)-
      canonicalCoordinateLog (n+1) k σ b ((fun i _ => p.1 i),p.2)-((n+1:ℕ):ℝ)*(δ*(1+ε)/2))
  let Xp := fun n (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) =>
    Real.exp (canonicalCoordinateLog (n+1) k σ (b+δ) ((fun i _ => p.1 i),p.2)-
      canonicalCoordinateLog (n+1) k σ b ((fun i _ => p.1 i),p.2)-((n+1:ℕ):ℝ)*(-δ*(1-ε)/2))
  have htm : Tendsto (fun n => coordinateCascadeLaw (n+1) k z r {p | 1/4 ≤ Xm n p}) atTop (𝓝 0) :=
    (canonical_ratio_converges σ b (b-δ) (δ*(1+ε)/2) k z hz hz0 hz1 hp hpm r hrm
      (by norm_num : (0:ℝ)<1/4)).comp (tendsto_add_atTop_nat 1)
  have htp : Tendsto (fun n => coordinateCascadeLaw (n+1) k z r {p | 1/4 ≤ Xp n p}) atTop (𝓝 0) :=
    (canonical_ratio_converges σ b (b+δ) (-δ*(1-ε)/2) k z hz hz0 hz1 hp hpp r hrp
      (by norm_num : (0:ℝ)<1/4)).comp (tendsto_add_atTop_nat 1)
  have he := htm.add htp
  simp only [add_zero] at he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    (Eventually.of_forall (fun _ => bot_le))
  apply Eventually.of_forall
  intro n
  apply le_trans (measure_mono_ae (t := {p | 1/4 ≤ Xm n p} ∪ {p | 1/4 ≤ Xp n p}) ?_)
    (measure_union_le _ _)
  filter_upwards [canonicalCoordinateBase_pos (n+1) k σ z hz hz0 hz1 r,
    canonicalCoordinateTotal_pos (n+1) k σ b z hz hz0 hz1 hp r,
    canonicalCoordinateTotal_pos (n+1) k σ (b-δ) z hz hz0 hz1 hpm r,
    canonicalCoordinateTotal_pos (n+1) k σ (b+δ) z hz hz0 hz1 hpp r] with p h0 hc hm hp'
  intro hbad
  by_cases hm' : 1/4 ≤ Xm n p
  · exact Or.inl hm'
  · right
    by_contra hp''
    have hhalf := canonicalCoordinate_half_band n k σ hb hδ.le hbm ε _ h0 hc hm hp'
      (not_le.mp hm').le (not_le.mp hp'').le
    exact (not_le.mpr hbad) hhalf

lemma canonicalCoordinate_shell_log_upper (n k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p)
    (hm : 0 < (canonicalRadialMass n b).real (normSquareBand n ε)) :
    coordinateAngularLog n k σ (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε))) p ≤
      canonicalCoordinateLog (n+1) k σ b p -
        Real.log ((canonicalRadialMass n b).real (normSquareBand n ε)) := by
  let A := decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε)))
  let T := decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ)
    (canonicalCoordinatePotential (n+1) b) k p
  let M := canonicalRadialMass n b (normSquareBand n ε)
  have hA : 0 < A.toReal := (coordinateAngularLog_regular n k σ _ hb p h0 hc).1
  change 0 < T.toReal at hc
  change 0 < M.toReal at hm
  have hle : A*M ≤ T := (decoratedCanonical_band_bounds n _
    (canonicalCoordinateStep_measurable (n+1) σ) _ (coordinateLeafField_measurable (n+1)) k p b ε).1.trans
      (canonicalCoordinateBandTotalE_le n k σ hb ε p)
  have hr := ENNReal.toReal_mono (ENNReal.toReal_pos_iff.mp hc).2.ne hle
  rw [ENNReal.toReal_mul] at hr
  change A.toReal*M.toReal ≤ T.toReal at hr
  have hlog := Real.log_le_log (mul_pos hA hm) hr
  rw [Real.log_mul hA.ne' hm.ne'] at hlog
  change Real.log (A.toReal / _) ≤ Real.log (T.toReal / _) - Real.log M.toReal
  rw [Real.log_div hA.ne' h0.ne',Real.log_div hc.ne' h0.ne']
  linarith

lemma canonicalCoordinate_shell_log_lower (n k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p)
    (hm : 0 < (canonicalRadialMass n b).real (normSquareBand n ε))
    (hh : decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ)
        (canonicalCoordinatePotential (n+1) b) k p / 2 ≤
      (canonicalCoordinateBandTotalE n k σ b ε p).toReal) :
    canonicalCoordinateLog (n+1) k σ b p - Real.log 2 -
        Real.log ((canonicalRadialMass n b).real (normSquareBand n ε)) ≤
      coordinateAngularLog n k σ (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε))) p := by
  let A := decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε)))
  let T := decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ)
    (canonicalCoordinatePotential (n+1) b) k p
  let M := canonicalRadialMass n b (normSquareBand n ε)
  have hA : 0 < A.toReal := (coordinateAngularLog_regular n k σ _ hb p h0 hc).1
  change 0 < T.toReal at hc
  change 0 < M.toReal at hm
  have hle : canonicalCoordinateBandTotalE n k σ b ε p ≤ A*M :=
    (decoratedCanonical_band_bounds n _ (canonicalCoordinateStep_measurable (n+1) σ) _
      (coordinateLeafField_measurable (n+1)) k p b ε).2
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.toReal_pos_iff.mp hA).2.ne (ENNReal.toReal_pos_iff.mp hm).2.ne) hle
  rw [ENNReal.toReal_mul] at hr
  change T.toReal/2 ≤ _ at hh
  have hlog := Real.log_le_log (div_pos hc (by norm_num : (0:ℝ)<2)) (hh.trans hr)
  rw [Real.log_mul hA.ne' hm.ne',Real.log_div hc.ne' (by norm_num : (2:ℝ)≠0)] at hlog
  change Real.log (T.toReal / _) - Real.log 2 - Real.log M.toReal ≤ Real.log (A.toReal / _)
  rw [Real.log_div hc.ne' h0.ne',Real.log_div hA.ne' h0.ne']
  linarith

lemma convex_nonneg_radius_transfer {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (hn : ∀ r, 0 ≤ f r) {R r s ε : ℝ} (hR : 0 < R)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hr : (1-ε)*R ≤ r) (hrR : r ≤ R)
    (hs : R ≤ s) (hsR : s ≤ (1+ε)*R) :
    f R ≤ f r + ε*f (2*R) ∧ f s ≤ f R + ε*f (2*R) := by
  have hr2 : 0 < 2*R-r := by linarith
  let c := (R-r)/(2*R-r)
  have hc0 : 0 ≤ c := div_nonneg (by linarith) hr2.le
  have hcε : c ≤ ε := (div_le_iff₀ hr2).mpr (by nlinarith)
  have hc1 : c ≤ 1 := hcε.trans hε1
  have hcEq : c*(2*R-r)=R-r := div_mul_cancel₀ _ hr2.ne'
  have he : (1-c)*r+c*(2*R) = R := by nlinarith [hcEq]
  have hl := hf.2 (mem_univ r) (mem_univ (2*R)) (sub_nonneg.mpr hc1) hc0 (by ring : 1-c+c=1)
  simp only [smul_eq_mul,he] at hl
  have hmix : (1-c)*f r+c*f (2*R) ≤ f r+ε*f (2*R) := by
    nlinarith [mul_nonneg hc0 (hn r),mul_le_mul_of_nonneg_right hcε (hn (2*R))]
  refine ⟨hl.trans hmix,?_⟩
  let d := (s-R)/R
  have hd0 : 0 ≤ d := div_nonneg (sub_nonneg.mpr hs) hR.le
  have hdε : d ≤ ε := (div_le_iff₀ hR).mpr (by nlinarith)
  have hd1 : d ≤ 1 := hdε.trans hε1
  have hdEq : d*R=s-R := div_mul_cancel₀ _ hR.ne'
  have he' : (1-d)*R+d*(2*R) = s := by nlinarith [hdEq]
  have hu := hf.2 (mem_univ R) (mem_univ (2*R)) (sub_nonneg.mpr hd1) hd0 (by ring : 1-d+d=1)
  simp only [smul_eq_mul,he'] at hu
  apply hu.trans
  nlinarith [mul_nonneg hd0 (hn R),mul_le_mul_of_nonneg_right hdε (hn (2*R))]

lemma sqrt_radius_band {d ε : ℝ} (hd : 0 < d) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1-ε)*Real.sqrt d ≤ Real.sqrt (d*(1-ε)) ∧
    Real.sqrt (d*(1-ε)) ≤ Real.sqrt d ∧
    Real.sqrt d ≤ Real.sqrt (d*(1+ε)) ∧
    Real.sqrt (d*(1+ε)) ≤ (1+ε)*Real.sqrt d := by
  have hs := Real.sq_sqrt hd.le
  constructor
  · apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    rw [mul_pow,hs]
    nlinarith [mul_nonneg (mul_nonneg hd.le hε) (sub_nonneg.mpr hε1)]
  constructor
  · exact Real.sqrt_le_sqrt (by nlinarith)
  constructor
  · exact Real.sqrt_le_sqrt (by nlinarith)
  · apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow,hs]
    nlinarith [mul_nonneg hd.le (sq_nonneg ε)]

lemma coordinateAngularLog_unit_radius_bounds (n k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (hb : 0 < b) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p) :
    coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) p ≤
      coordinateAngularLog n k σ (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε))) p +
        ε*(canonicalCoordinateLog (n+1) k σ b p+((n+1:ℕ):ℝ)*(Real.log b/2+2*b)) ∧
    coordinateAngularLog n k σ (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε))) p ≤
      coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) p +
        ε*(canonicalCoordinateLog (n+1) k σ b p+((n+1:ℕ):ℝ)*(Real.log b/2+2*b)) := by
  have hd : 0 < ((n+1:ℕ):ℝ) := by positivity
  have hr := sqrt_radius_band hd hε hε1
  have hconv := convex_nonneg_radius_transfer (coordinateAngularLog_convex n k σ hb p h0 hc)
    (fun r => (coordinateAngularLog_regular n k σ r hb p h0 hc).2.1)
    (Real.sqrt_pos.mpr hd) hε hε1 hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  have hbig := (coordinateAngularLog_regular n k σ (2*Real.sqrt (n+1:ℕ)) hb p h0 hc).2.2
  have he : ((n+1:ℕ):ℝ)*Real.log b/2+b*(2*Real.sqrt (n+1:ℕ))^2/2 =
      ((n+1:ℕ):ℝ)*(Real.log b/2+2*b) := by
    rw [mul_pow,Real.sq_sqrt hd.le]
    ring
  have hbige : coordinateAngularLog n k σ (2*Real.sqrt (n+1:ℕ)) p ≤
      canonicalCoordinateLog (n+1) k σ b p+((n+1:ℕ):ℝ)*(Real.log b/2+2*b) := by
    linarith [he]
  exact ⟨hconv.1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbige hε)),
    hconv.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbige hε))⟩

lemma canonicalCoordinate_unitSphere_upper (n k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (hb : 0 < b) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p)
    (hm : 0 < (canonicalRadialMass n b).real (normSquareBand n ε)) :
    coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) p ≤
      (1+ε)*canonicalCoordinateLog (n+1) k σ b p-
        Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))+
          ε*((n+1:ℕ):ℝ)*(Real.log b/2+2*b) := by
  have h₁ := canonicalCoordinate_shell_log_upper n k σ hb p h0 hc hm
  have h₂ := (coordinateAngularLog_unit_radius_bounds n k σ hb hε hε1 p h0 hc).1
  linarith

lemma canonicalCoordinate_unitSphere_lower (n k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (hb : 0 < b) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p)
    (hm : 0 < (canonicalRadialMass n b).real (normSquareBand n ε))
    (hh : decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ)
        (canonicalCoordinatePotential (n+1) b) k p / 2 ≤
      (canonicalCoordinateBandTotalE n k σ b ε p).toReal) :
    (1-ε)*canonicalCoordinateLog (n+1) k σ b p-Real.log 2-
        Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))-
          ε*((n+1:ℕ):ℝ)*(Real.log b/2+2*b) ≤
      coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) p := by
  have h₁ := canonicalCoordinate_shell_log_lower n k σ hb p h0 hc hm hh
  have h₂ := (coordinateAngularLog_unit_radius_bounds n k σ hb hε hε1 p h0 hc).2
  linarith

end SphericalPerceptron
end
end

end OAI
