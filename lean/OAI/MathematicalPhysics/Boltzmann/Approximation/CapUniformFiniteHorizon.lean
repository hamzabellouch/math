import OAI.MathematicalPhysics.Boltzmann.Approximation.CapAnnularMassGrowth
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotTransportBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.AccessAngularFubini
import OAI.MathematicalPhysics.Boltzmann.Branching.AeWindowPatching
import OAI.MathematicalPhysics.Boltzmann.Branching.DiagonalVanishingCap
import OAI.MathematicalPhysics.Boltzmann.Branching.HotFullVanishingContradiction
import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxAccessMeasure

namespace OAI

section

/-! # Patching actual annular growth into a common set of late time pairs -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.unbounded_horizon_box_growth
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {d κ : ℝ} (hd : 0 < d) (hdsmall : d ≤ 1/32) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) (hH : E.horizon = ⊤) :
    ∃ A₀ ε γ₀ R : ℝ, 0 < A₀ ∧ 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧ 0 < R ∧
      (η ≤ Real.log (1+ε/20) → α ≤ ε → γ ≤ γ₀ → 480*(8*A₀) ≤ ε*K →
      let δ := 8*κ*A₀/K;
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, R < s →
        t ∈ Ioo ((1+δ)*s) ((1+2*δ)*s) →
        (6:ℝ≥0∞)*hotLateBoxMass E.hotLimit κ d s ≤ hotLateBoxMass E.hotLimit κ d t) := by
  obtain ⟨A₀,ε,γ₀,hA₀,hε,hεsmall,hγ₀,hgrowth⟩ := E.annular_mass_growth hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hd hdsmall hκ hκsmall hg
  let R := max 1 (4*(Real.exp η*E.fraction)/κ)
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨A₀,ε,γ₀,R,hA₀,hε,hεsmall,hγ₀,hR,?_⟩
  intro hηsmall hαsmall hγsmall hKlarge
  dsimp only
  let δ := 8*κ*A₀/K
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbase : 15360*A₀ ≤ K := by
    have hh := mul_le_mul_of_nonneg_right hεsmall hK.le
    nlinarith
  have hδsmall : 2*δ < κ/200 := by
    rw [show 2*δ = 16*κ*A₀/K by dsimp [δ]; ring]
    apply (div_lt_iff₀ hK).mpr
    have hh := mul_le_mul_of_nonneg_left hbase hκ.le
    nlinarith [mul_pos hκ hK]
  have hlocal : ∀ b : ℚ, ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      R < (b:ℝ) → s ∈ Ioo (b:ℝ) ((1+κ/200)*(b:ℝ)) →
      t ∈ Ioo (b:ℝ) ((1+κ/200)*(b:ℝ)) →
      (δ*s ≤ t-s → t-s ≤ 2*δ*s →
        (6:ℝ≥0∞)*hotLateBoxMass E.hotLimit κ d s ≤ hotLateBoxMass E.hotLimit κ d t) := by
    intro b
    by_cases hbR : R < (b:ℝ)
    · have hb : 0 < (b:ℝ) := hR.trans hbR
      let W := κ*(b:ℝ)/200
      have hW : 0 < W := by dsimp [W]; positivity
      have heq : (b:ℝ)+W = (1+κ/200)*(b:ℝ) := by dsimp [W]; ring
      have hcut : Real.exp η*E.fraction+6*W < κ*(b:ℝ)/2 := by
        have hh : 4*(Real.exp η*E.fraction)/κ < (b:ℝ) :=
          (le_max_right _ _).trans_lt hbR
        have hh' := (div_lt_iff₀ hκ).mp hh
        dsimp [W]
        nlinarith [mul_pos hκ hb]
      have hB : (b:ℝ)+W < 2*((b:ℝ)+W) := by linarith
      have htop : ENNReal.ofReal (2*((b:ℝ)+W)) < E.horizon := by
        rw [hH]
        exact ENNReal.ofReal_lt_top
      have hh := hgrowth hηsmall hαsmall hγsmall hKlarge hb hW le_rfl hB htop hcut
      filter_upwards [hh] with s hs
      filter_upwards [hs] with t ht
      intro _ hsw htw hlo hhi
      rw [← heq] at hsw htw
      apply ht hsw htw hlo
      simpa only [show 2*δ = 16*κ*A₀/K by dsimp [δ]; ring] using hhi
    · exact ae_of_all _ (fun _ => ae_of_all _ (fun _ h => False.elim (hbR h)))
  have hp := ae_patch_multiplicative_windows (div_pos hκ (by norm_num)) hlocal
  filter_upwards [hp] with s hs
  filter_upwards [hs] with t ht
  intro hRs htime
  have hspos : 0 < s := hR.trans hRs
  have hst : s < t := by nlinarith [mul_pos hδ hspos,htime.1]
  have htu : t < (1+κ/200)*s :=
    htime.2.trans (mul_lt_mul_of_pos_right (by linarith) hspos)
  apply ht hRs hst htu <;> nlinarith [htime.1,htime.2]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual nonzero hot limit has positive mass in all sufficiently late growth boxes -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.unbounded_horizon_lateBox_positive
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters) (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hH : E.horizon = ⊤)
    {κ ρ ε d : ℝ} (hκ : 0 < κ) (hκmax : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε : 0 < ε) (hεmax : ε ≤ 1/12) (hαε : α ≤ ε/2) (hερ : 6*ε ≤ ρ)
    (haccess : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (hd : 0 < d) (hρd : ρ ≤ d*κ/4) (hρ₅ : κ+ρ ≤ 5) :
    ∃ T : ℝ, 0 < T ∧ ∀ᵐ t ∂volume, T ≤ t → 0 < hotLateBoxMass E.hotLimit κ d t := by
  obtain ⟨s,_hs,n,hpersist⟩ := E.persisting_entry hDP hcarleman hGLPS hMityagin
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hH
    hκ.le hκmax hρ hε hεmax hαε hερ haccess
  exact positive_entryPortion_eventually_lateBox hκ hd hρd hρ₅ n s
    (hotPhaseSlice E.hotLimit) hpersist

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # An unbounded limiting horizon would force every sufficiently late hot box to vanish -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.unbounded_horizon_lateBox_zero
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {d κ : ℝ} (hd : 0 < d) (hdsmall : d ≤ 1/32) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) (hH : E.horizon = ⊤) :
    ∃ A₀ ε γ₀ R : ℝ, 0 < A₀ ∧ 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧ 0 < R ∧
      (η ≤ Real.log (1+ε/20) → α ≤ ε → γ ≤ γ₀ → 480*(8*A₀) ≤ ε*K →
      ∀ᵐ t ∂volume, R < t → hotLateBoxMass E.hotLimit κ d t = 0) := by
  obtain ⟨A₀,ε,γ₀,R,hA₀,hε,hεsmall,hγ₀,hR,hgrow⟩ := E.unbounded_horizon_box_growth
    hDP hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    hd hdsmall hκ hκsmall hg hH
  refine ⟨A₀,ε,γ₀,R,hA₀,hε,hεsmall,hγ₀,hR,?_⟩
  intro hηsmall hαsmall hγsmall hKlarge
  let δ := 8*κ*A₀/K
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbase : 15360*A₀ ≤ K := by
    have hh := mul_le_mul_of_nonneg_right hεsmall hK.le
    nlinarith
  have hδsmall : δ ≤ κ/1920 := by
    dsimp [δ]
    apply (div_le_iff₀ hK).mpr
    have hh := mul_le_mul_of_nonneg_left hbase hκ.le
    nlinarith
  have hr : (1+2*δ)^4 < 3 := by
    have hh : 1+2*δ ≤ (11/10:ℝ) := by nlinarith
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+2*δ) hh 4
    norm_num at hp
    linarith
  let m : ℝ → ℝ := fun t => (hotLateBoxMass E.hotLimit κ d t).toReal
  have hcap := E.toHotLimitExtraction.hotLateBoxMass_real_cap hκ.le hd.le hq₂
  have hfinite := E.toHotLimitExtraction.hotLateBoxMass_finite hκ.le hd.le hq₂
  have hstep : ∀ᵐ s ∂volume, R < s → ∀ᵐ t ∂volume,
      t ∈ Ioo ((1+δ)*s) ((1+2*δ)*s) → 3*m s ≤ m t := by
    filter_upwards [hgrow hηsmall hαsmall hγsmall hKlarge] with s hs
    intro hRs
    filter_upwards [hs,hfinite] with t ht htf
    intro hit
    have hspos := hR.trans hRs
    have htpos : 0 < t := (mul_pos (by positivity : (0:ℝ)<1+δ) hspos).trans hit.1
    have hh := ENNReal.toReal_mono (htf htpos.le) (ht hRs hit)
    rw [ENNReal.toReal_mul] at hh
    norm_num at hh
    exact (mul_le_mul_of_nonneg_right (by norm_num : (3:ℝ)≤6) ENNReal.toReal_nonneg).trans hh
  have hlatecap : ∀ᵐ t ∂volume, R < t → m t ≤ lateBoxCapConstant q κ d*(1+t)^4 := by
    filter_upwards [hcap] with t ht
    intro hRt
    exact ht (hR.trans hRt).le
  have hz : ∀ᵐ t ∂volume, R < t → m t = 0 :=
    GrowthContradiction.ae_zero_of_late_growth_cap (r₀ := 1+δ) (r₁ := 1+2*δ)
      hR.le (by linarith) (by linarith) hr
      (lateBoxCapConstant_nonneg hκ.le hd.le) (fun _ => ENNReal.toReal_nonneg)
      hlatecap hstep
  filter_upwards [hz,hfinite] with t ht hf
  intro hRt
  have hm0 := ht hRt
  exact (ENNReal.toReal_eq_toReal_iff' (hf (hR.trans hRt).le) (by simp)).mp
    (by simpa only [ENNReal.toReal_zero] using hm0)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # An actual cap limit separates from the dormant solution -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_separated_cap_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321) (hDPhot : Published.DunfordPettis1940HotWindows)
    (hDPpair : Published.DunfordPettis1940HotPairWindows)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {s₀ η K α γ d₀ q : ℝ} {B : DormantFamily s₀ η K α γ d₀ q} (D : DormantLimit B)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    (hfinite : ∀ (F : ShrinkingCapFamily s₀ η K α γ d₀ q) (S : AttainedCapSequence F)
      (E : AttainedCapSequence.HotPairExtraction S), E.horizon < ⊤) :
    ∃ (A : TightCapFamily s₀ η K α γ d₀ q) (L : CapLocalLimit A), A.time ≤ B.time ∧
      ∃ t ∈ Icc 0 A.time,
        ¬ (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀)
            L.density t =ᵐ[volume]
          MildCollisionSolution.positiveEvolution B.time (JetPeriodicDatum.datum s₀ η K α γ d₀)
            D.density t) := by
  obtain ⟨τ₀,hτ₀,hτ₀max,hfamilies⟩ := exists_tight_cap_family_at hcarleman hs₀ hsmax hη hηmax
    hK.le hα hαmax hγ hd₀ hd₀max hwidth hsmall hq₁ hq₂
  let τ := min τ₀ B.time
  have hτ : 0 < τ := lt_min hτ₀ B.time_pos
  have hτmax : τ ≤ 1/32 := (min_le_left _ _).trans hτ₀max
  have hex (n : ℕ) : ∃ A : TightCapFamily s₀ η K α γ d₀ q, A.time = shrinkingHorizon τ n :=
    hfamilies _ (shrinkingHorizon_pos hτ n) ((shrinkingHorizon_le hτ n).trans (min_le_left _ _))
  choose A htime using hex
  have hL (n) : Nonempty (CapLocalLimit (A n)) :=
    (A n).exists_limit hcarleman hGLPS hDP hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hwidth hsmall hq₁ hq₂
  let L := fun n => Classical.choice (hL n)
  have hT (n) : (A n).time ≤ B.time := by
    rw [htime n]
    exact (shrinkingHorizon_le hτ n).trans (min_le_right _ _)
  by_contra hno
  have hagree (n) (t) (ht : t ∈ Icc 0 (A n).time) :
      MildCollisionSolution.positiveEvolution (A n).time (JetPeriodicDatum.datum s₀ η K α γ d₀)
          (L n).density t =ᵐ[volume]
        MildCollisionSolution.positiveEvolution B.time (JetPeriodicDatum.datum s₀ η K α γ d₀)
          D.density t := by
    by_contra hh
    exact hno ⟨A n,L n,hT n,t,ht,hh⟩
  have he (n) := (L n).density_eq_dormant D (hT n) (hagree n)
  obtain ⟨F,hF,hvan⟩ := exists_vanishing_cap_family D hs₀ hsmax hη hηmax hK.le hα.le
    (hαmax.trans (by norm_num)) hγ.le hd₀ hd₀max hsmall (by linarith) hq₂ hτ hτmax A htime L he
  have hvan' : ∀ j, Tendsto (fun n => scaledBoxMass (shrinkingHorizon F.horizonScale n)
      (EuclideanFlight.density q (F.approximation n).solution.value) j) atTop (𝓝 0) := by
    simpa only [hF] using hvan
  obtain ⟨S⟩ := exists_attained_cap_sequence F hs₀ hsmax hη hηmax hK.le hd₀.le hq₂
  obtain ⟨E₀⟩ := S.exists_hot_limit_extraction hDPhot hs₀ hsmax hη hηmax hK.le hd₀.le hq₂
  obtain ⟨E⟩ := S.exists_hot_pair_limit hDPpair E₀ hs₀ hsmax hη hηmax hK.le hd₀.le hq₂
  exact E.toHotLimitExtraction.full_vanishing_impossible hcarleman hMityagin hs₀ hsmax hη hηmax
    hK.le hα (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₁ hq₂ (hfinite F S E) hvan'

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Fixed geometric parameters force every actual extracted dilated horizon to be finite -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

theorem uniform_finite_horizon_parameters :
    ∃ κ d A₀ ε γ₀ : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < d ∧ d ≤ 1/32 ∧
      0 < A₀ ∧ 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
        {S : AttainedCapSequence F},
      Published.DunfordPettis1940HotPairWindows → Published.GPV2009CarlemanInput →
      Published.GLPS1988Proposition3 → Published.Mityagin2020FiveGainParameters →
      ∀ E : HotPairExtraction S,
      0 < s₀ → s₀ ≤ 1/8 → 0 < η → η ≤ Real.log 2 →
      0 < K → 0 < α → α ≤ 1/4 → 0 < γ → 0 < d₀ → d₀ ≤ 1 →
      JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1 → 1 < q → q < 2 →
      η ≤ Real.log (1+ε/20) → α ≤ ε → γ ≤ γ₀ → 480*(8*A₀) ≤ ε*K →
      E.horizon < ⊤ := by
  obtain ⟨κ,hκ,hκmax,hgrowth,haccess⟩ := exists_access_growth_parameters
  let d : ℝ := 1/64
  have hd : 0 < d := by norm_num [d]
  have hdsmall : d ≤ 1/32 := by norm_num [d]
  obtain ⟨εa,hεa,hεamax,hεar,ha⟩ := haccess d hd (by norm_num [d])
  obtain ⟨A₀,εg,γ₀,hA₀,hεg,hεgmax,hγ₀,hzero⟩ :=
    uniform_late_zero_parameters hd hdsmall hκ hκmax hgrowth
  let ε := min εg (εa/2)
  have hε : 0 < ε := lt_min hεg (by positivity)
  have hεg' : ε ≤ εg := min_le_left _ _
  have hεa' : ε ≤ εa/2 := min_le_right _ _
  refine ⟨κ,d,A₀,ε,γ₀,hκ,hκmax,hd,hdsmall,hA₀,hε,hεg'.trans hεgmax,hγ₀,?_⟩
  intro s₀ η K α γ d₀ q F S hDP hcarleman hGLPS hMityagin E
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    hηsmall hαsmall hγsmall hKlarge
  apply lt_top_iff_ne_top.mpr
  intro hH
  have hηg : η ≤ Real.log (1+εg/20) := hηsmall.trans
    (Real.log_le_log (by positivity) (by linarith))
  have hKg : 480*(8*A₀) ≤ εg*K := hKlarge.trans
    (mul_le_mul_of_nonneg_right hεg' hK.le)
  obtain ⟨R,hR,hz⟩ := hzero hDP hcarleman hGLPS E hs₀ hsmax hη hηmax hK hα hαmax
    hγ hd₀ hd₀max hsmall hq₁ hq₂ hηg (hαsmall.trans hεg') hγsmall hKg hH
  have hρ : d*κ/4 ≤ 1 := by nlinarith
  have hρ₅ : κ+d*κ/4 ≤ 5 := by nlinarith
  obtain ⟨T,hT,hp⟩ := E.unbounded_horizon_lateBox_positive hDP hcarleman hGLPS hMityagin
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hH
    hκ hκmax.le hρ hεa hεamax (hαsmall.trans hεa') hεar
    (by simpa only [div_div, show (4:ℝ)*2=8 by norm_num] using ha) hd le_rfl hρ₅
  have hpos : (volume : Measure ℝ) (Ioo (max R T+1) (max R T+2)) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  obtain ⟨t,ht,htz,htp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae (hz.and hp))
  have hr : R < t := by linarith [le_max_left R T,ht.1]
  have ht' : T ≤ t := by linarith [le_max_right R T,ht.1]
  have hh := htp ht'
  rw [htz hr] at hh
  exact (lt_irrefl _ hh)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
