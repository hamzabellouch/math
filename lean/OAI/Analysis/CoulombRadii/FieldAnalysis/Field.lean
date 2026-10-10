import Mathlib
import OAI.Analysis.CoulombRadii.LimitTheory.UniformGroundStateCountControl
import OAI.Analysis.CoulombRadii.Variational.RetainedAnalyticSequence

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

def RetainedAnalyticSequence.field (d : RetainedAnalyticSequence) : ℕ → Position → ℝ :=
  fun n => screenedField (d.lam n) (d.σ n)

def RetainedAnalyticSequence.reindex (d : RetainedAnalyticSequence) (u : ℕ → ℕ)
    (hu : Tendsto u atTop atTop) : RetainedAnalyticSequence where
  σ := d.σ ∘ u
  U := d.U ∘ u
  p := d.p ∘ u
  lam := d.lam ∘ u
  a := d.a ∘ u
  q := d.q ∘ u
  Aσ := d.Aσ ∘ u
  Ap := d.Ap ∘ u
  B := d.B
  Ccap := d.Ccap
  Cinv := d.Cinv
  Bpos := d.Bpos
  Cpos := d.Cpos
  σi := fun n => d.σi (u n)
  σp := fun n => d.σp (u n)
  σb := fun n => d.σb (u n)
  σmass := fun n => d.σmass (u n)
  pi := fun n => d.pi (u n)
  pp := fun n => d.pp (u n)
  pb := fun n => d.pb (u n)
  ps := fun n => d.ps (u n)
  pm := d.pm.comp hu
  apos := fun n => d.apos (u n)
  alim := d.alim.comp hu
  qlim := d.qlim.comp hu
  aq := hu.eventually d.aq
  Ucont := fun n => d.Ucont (u n)
  Ulower := fun n => d.Ulower (u n)
  Uupper := fun n => d.Uupper (u n)
  Uweak := fun n => d.Uweak (u n)
  cap := fun n => d.cap (u n)
  err := fun n => d.err (u n)

def sommerfeldProfile (x : Position) : ℝ := aTF/‖x‖^4

def sommerfeldDensity (x : Position) : ℝ := kTF*aTF^(3/2 : ℝ)/‖x‖^6

theorem sommerfeldProfile_continuousOn : ContinuousOn sommerfeldProfile {x | x ≠ 0} := by
  apply continuousOn_const.div (continuous_norm.pow 4).continuousOn
  intro x hx
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr hx)

theorem sommerfeldProfile_density (x : Position) : tfDensityScalar (sommerfeldProfile x) = sommerfeldDensity x := by
  have hn : 0 ≤ ‖x‖ := norm_nonneg x
  have hf : 0 ≤ aTF/‖x‖^4 := div_nonneg aTF_pos.le (pow_nonneg hn 4)
  unfold tfDensityScalar sommerfeldProfile sommerfeldDensity
  rw [max_eq_left hf, Real.div_rpow aTF_pos.le (pow_nonneg hn 4), ← Real.rpow_natCast_mul hn]
  norm_num
  ring

theorem RetainedAnalyticSequence.limit_eq_profile (d : RetainedAnalyticSequence)
    {F : Position → ℝ} (hF : ContinuousOn F {x | x ≠ 0})
    (hu : TendstoLocallyUniformlyOn d.field F atTop {x | x ≠ 0}) :
    ∀ x ≠ 0, F x = sommerfeldProfile x := by
  have herr := expanding_annular_error_locallyUniform d.alim d.qlim d.err
  have hw := screened_semilinear_limit d.σi d.σp d.σb hF hu herr
  have hcap := expanding_annular_cap_limit d.alim d.qlim d.cap hu
  have hL : ∀ a b : ℝ, 0 < a → (∫ x in closedNormAnnulus a b, ‖F x‖) ≤
      2*(d.Ccap/a^4)*(volume (closedNormAnnulus a b)).toReal := by
    intro a b ha
    apply neutral_screened_limit_annular_lone d.Cpos ha d.σi d.σp d.σb d.σmass hF hu
    exact (expanding_annular_cap_eventually (r := b) ha d.alim d.qlim d.cap).mono
      (fun n hn x hx => hn x hx.1 hx.2)
  obtain ⟨K,hK,habs⟩ := semilinear_absolute_bound d.Cpos hF hw hcap hL
  have hpos := screened_limit_positive d.σi d.σp d.σb d.pi d.pp d.pb d.ps d.pm
    d.apos d.alim d.qlim d.aq d.Ucont d.Ulower d.Uupper d.Uweak d.err hu hK.le habs
  have hw' : HasWeakLaplacian F punctured (fun x => 4*Real.pi*kTF*F x^(3/2 : ℝ)) := by
    intro φ hφ hc ht
    rw [hw φ hφ hc ht]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hfx : 0 ≤ F x := (div_nonneg d.Bpos.le (pow_nonneg (norm_nonneg x) 4)).trans (hpos x (ht hx))
      simp only [tfReaction, max_eq_left hfx]
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  intro x hx
  have he := weak_sommerfeld_rigidity_exact d.Bpos hF hw' (fun x hx => ⟨hpos x hx, hcap x hx⟩) x hx
  simpa only [sommerfeldProfile, aTF_value] using he

theorem RetainedAnalyticSequence.precompact (d : RetainedAnalyticSequence) :
    ∃ (F : Position → ℝ) (u : ℕ → ℕ), StrictMono u ∧ ContinuousOn F {x | x ≠ 0} ∧
      TendstoLocallyUniformlyOn (fun n => d.field (u n)) F atTop {x | x ≠ 0} := by
  have hb : ∀ a b : ℝ, 0 < a → a < b → ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ n in atTop, ∀ x : Position, a ≤ ‖x‖ → ‖x‖ ≤ b →
        screenedField (d.lam n) (d.σ n) x ≤ d.Ccap/‖x‖^4 ∧ d.σ n x ≤ A := by
    intro a b ha _
    exact expanding_annular_density_bound tfDensityScalar_monotone tfDensityScalar_nonneg
      d.Cpos ha d.alim d.qlim d.cap d.err
  obtain ⟨F,u,hu,hF,hconv,_⟩ := neutral_screened_precompact_sequence d.σi d.σp d.σb d.σmass d.Cpos hb
  exact ⟨F,u,hu,hF,hconv⟩

theorem RetainedAnalyticSequence.converges (d : RetainedAnalyticSequence) :
    TendstoLocallyUniformlyOn d.field sommerfeldProfile atTop {x | x ≠ 0} ∧
    TendstoLocallyUniformlyOn d.σ sommerfeldDensity atTop {x | x ≠ 0} := by
  have hu : TendstoLocallyUniformlyOn d.field sommerfeldProfile atTop {x | x ≠ 0} := by
    apply locallyUniform_of_subsequence isOpen_ne
      (fun n => screenedField_continuousOn (d.σi n) (d.σp n) (d.σb n)) sommerfeldProfile_continuousOn
    intro u hu
    let e := d.reindex u hu
    obtain ⟨F,v,hv,hF,hconv⟩ := e.precompact
    have hEq := (e.reindex v hv.tendsto_atTop).limit_eq_profile hF hconv
    refine ⟨v, hconv.congr_right ?_⟩
    exact hEq
  refine ⟨hu, ?_⟩
  have hh := density_locallyUniform_of_vanishing_error hu sommerfeldProfile_continuousOn
    (expanding_annular_error_locallyUniform d.alim d.qlim d.err)
  exact hh.congr_right (fun x _ => sommerfeldProfile_density x)

theorem uniformOn_of_selected_locallyUniformly
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {Θ : ℕ → Type*} {P : ∀ n, Θ n → Prop} {f : ∀ n, Θ n → X → Y}
    {g : X → Y} {U K : Set X} (hK : IsCompact K) (hKU : K ⊆ U)
    (hsel : ∀ u : ℕ → ℕ, StrictMono u → ∀ θ : ∀ n, Θ (u n),
      (∀ n, P (u n) (θ n)) →
      TendstoLocallyUniformlyOn (fun n => f (u n) (θ n)) g atTop U) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ θ, P n θ → ∀ x ∈ K, dist (f n θ x) (g x) < ε := by
  classical
  intro ε hε
  by_contra hh
  have hf := frequently_atTop.mp (not_eventually.mp hh)
  obtain ⟨u,hu,hbad⟩ := Nat.exists_strictMono_subsequence (by
    intro N
    obtain ⟨n,hn,hfail⟩ := hf (N+1)
    exact ⟨n, by omega, hfail⟩)
  have hchoices : ∀ n, ∃ θ : Θ (u n), P (u n) θ ∧
      ∃ x ∈ K, ε ≤ dist (f (u n) θ x) (g x) := by
    intro n
    simpa only [not_forall, Classical.not_imp, not_lt, exists_prop] using hbad n
  choose θ hθ x hx hεx using hchoices
  have ht := hsel u hu θ hθ
  have ht' := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (ht.mono hKU)
  obtain ⟨n,hn⟩ := ((Metric.tendstoUniformlyOn_iff.mp ht') ε hε).exists
  exact (not_lt_of_ge (hεx n)) (by simpa only [dist_comm] using hn (x n) (hx n))

structure RetainedAnalyticFamily (Θ : ℕ → Type*) where
  σ : ∀ n, Θ n → Position → ℝ
  U : ∀ n, Θ n → Position → ℝ
  p : ∀ n, Θ n → Position → ℝ
  lam : ℕ → ℝ
  a : ℕ → ℝ
  q : ℕ → ℝ
  ε : ℕ → ℝ
  Aσ : ∀ n, Θ n → ℝ
  Ap : ∀ n, Θ n → ℝ
  B : ℝ
  Ccap : ℝ
  Cinv : ℝ
  Bpos : 0 < B
  Cpos : 0 ≤ Ccap
  σi : ∀ n θ, Integrable (σ n θ)
  σp : ∀ n θ x, 0 ≤ σ n θ x
  σb : ∀ n θ x, σ n θ x ≤ Aσ n θ
  σmass : ∀ n θ, (∫ x, σ n θ x) = lam n
  pi : ∀ n θ, Integrable (p n θ)
  pp : ∀ n θ x, 0 ≤ p n θ x
  pb : ∀ n θ x, p n θ x ≤ Ap n θ
  ps : ∀ n θ x, a n < ‖x‖ → p n θ x = 0
  pm : ∀ n θ, (∫ x, p n θ x) ≤ ε n
  εlim : Tendsto ε atTop (𝓝 0)
  apos : ∀ n, 0 < a n
  alim : Tendsto a atTop (𝓝 0)
  qlim : Tendsto q atTop atTop
  aq : ∀ᶠ n in atTop, 1/(2*q n) ≤ a n
  Ucont : ∀ n θ, Continuous (fun x => U n θ x-lam n*coulombKernel x)
  Ulower : ∀ n θ x, a n ≤ ‖x‖ → B/‖x‖^4*(1-a n/(8*‖x‖)) ≤ U n θ x
  Uupper : ∀ n θ x, a n ≤ ‖x‖ → U n θ x ≤ Cinv/‖x‖^4
  Uweak : ∀ n θ, WeakNuclearSubsolution (U n θ) (lam n) Set.univ
    (barrierSource (a n) (U n θ) (σ n θ) (p n θ))
  cap : ∀ n θ x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → screenedField (lam n) (σ n θ) x ≤ Ccap/‖x‖^4
  err : ∀ n θ x, a n ≤ ‖x‖ → ‖x‖ ≤ q n →
    |σ n θ x-tfDensityScalar (screenedField (lam n) (σ n θ) x)| ≤ ((q n)^8)⁻¹*(‖x‖^6)⁻¹

def RetainedAnalyticFamily.select {Θ : ℕ → Type*} (d : RetainedAnalyticFamily Θ)
    (u : ℕ → ℕ) (hu : Tendsto u atTop atTop) (θ : ∀ n, Θ (u n)) : RetainedAnalyticSequence where
  σ := fun n => d.σ (u n) (θ n)
  U := fun n => d.U (u n) (θ n)
  p := fun n => d.p (u n) (θ n)
  lam := d.lam ∘ u
  a := d.a ∘ u
  q := d.q ∘ u
  Aσ := fun n => d.Aσ (u n) (θ n)
  Ap := fun n => d.Ap (u n) (θ n)
  B := d.B
  Ccap := d.Ccap
  Cinv := d.Cinv
  Bpos := d.Bpos
  Cpos := d.Cpos
  σi := fun n => d.σi (u n) (θ n)
  σp := fun n => d.σp (u n) (θ n)
  σb := fun n => d.σb (u n) (θ n)
  σmass := fun n => d.σmass (u n) (θ n)
  pi := fun n => d.pi (u n) (θ n)
  pp := fun n => d.pp (u n) (θ n)
  pb := fun n => d.pb (u n) (θ n)
  ps := fun n => d.ps (u n) (θ n)
  pm := squeeze_zero (fun n => integral_nonneg (d.pp (u n) (θ n)))
    (fun n => d.pm (u n) (θ n)) (d.εlim.comp hu)
  apos := fun n => d.apos (u n)
  alim := d.alim.comp hu
  qlim := d.qlim.comp hu
  aq := hu.eventually d.aq
  Ucont := fun n => d.Ucont (u n) (θ n)
  Ulower := fun n => d.Ulower (u n) (θ n)
  Uupper := fun n => d.Uupper (u n) (θ n)
  Uweak := fun n => d.Uweak (u n) (θ n)
  cap := fun n => d.cap (u n) (θ n)
  err := fun n => d.err (u n) (θ n)

theorem RetainedAnalyticFamily.uniform {Θ : ℕ → Type*} (d : RetainedAnalyticFamily Θ)
    {K : Set Position} (hK : IsCompact K) (hK0 : (0 : Position) ∉ K) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ θ : Θ n, ∀ x ∈ K,
      |screenedField (d.lam n) (d.σ n θ) x-sommerfeldProfile x| < ε ∧
      |d.σ n θ x-sommerfeldDensity x| < ε := by
  have hKU : K ⊆ {x : Position | x ≠ 0} := fun x hx h => hK0 (h ▸ hx)
  have hfield := uniformOn_of_selected_locallyUniformly (P := fun _ _ => True)
    (f := fun n θ => screenedField (d.lam n) (d.σ n θ)) hK hKU
    (fun u hu θ _ => (d.select u hu.tendsto_atTop θ).converges.1)
  have hdensity := uniformOn_of_selected_locallyUniformly (P := fun _ _ => True)
    (f := d.σ) hK hKU
    (fun u hu θ _ => (d.select u hu.tendsto_atTop θ).converges.2)
  intro ε hε
  filter_upwards [hfield ε hε, hdensity ε hε] with n hn hn' θ x hx
  exact ⟨by simpa only [Real.dist_eq] using hn θ trivial x hx,
    by simpa only [Real.dist_eq] using hn' θ trivial x hx⟩

theorem sommerfeldDensity_continuousOn : ContinuousOn sommerfeldDensity {x | x ≠ 0} := by
  apply continuousOn_const.div (continuous_norm.pow 6).continuousOn
  intro x hx
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr hx)

theorem RetainedAnalyticFamily.uniform_integral {Θ : ℕ → Type*} (d : RetainedAnalyticFamily Θ)
    {S K : Set Position} (hK : IsCompact K) (hK0 : (0 : Position) ∉ K) (hSK : S ⊆ K) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ θ : Θ n,
      |(∫ x in S, d.σ n θ x)-(∫ x in S, sommerfeldDensity x)| < ε := by
  have hKU : K ⊆ {x : Position | x ≠ 0} := fun x hx h => hK0 (h ▸ hx)
  have hi : IntegrableOn sommerfeldDensity S :=
    ((sommerfeldDensity_continuousOn.mono hKU).integrableOn_compact hK).mono_set hSK
  have hSfin : volume S < ⊤ := (measure_mono hSK).trans_lt hK.measure_lt_top
  intro ε hε
  have hV : 0 < volume.real S+1 := by positivity
  have hδ : 0 < ε/(volume.real S+1) := div_pos hε hV
  filter_upwards [d.uniform hK hK0 _ hδ] with n hn θ
  rw [← integral_sub (d.σi n θ).integrableOn hi]
  have hb := norm_setIntegral_le_of_norm_le_const (f := fun x => d.σ n θ x-sommerfeldDensity x)
    (C := ε/(volume.real S+1)) hSfin (fun x hx => by
      simpa only [Real.norm_eq_abs] using (hn θ x (hSK hx)).2.le)
  calc
    _ ≤ (ε/(volume.real S+1))*volume.real S := by simpa only [Real.norm_eq_abs] using hb
    _ < (ε/(volume.real S+1))*(volume.real S+1) :=
      mul_lt_mul_of_pos_left (by linarith) hδ
    _ = ε := div_mul_cancel₀ ε hV.ne'

theorem expectation_tendsto_of_eventual_uniform {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (Y : ∀ n, Ω n → ℝ)
    (G : ∀ n, Set (Ω n)) {C L : ℝ}
    (hY : ∀ n, MemLp (Y n) 2 (μ n)) (hY0 : ∀ n, 0 ≤ᵐ[μ n] Y n)
    (hG : ∀ n, MeasurableSet (G n))
    (hgood : ∀ δ > 0, ∀ᶠ n in atTop, ∀ z ∈ G n, |Y n z-L| < δ)
    (hL2 : ∀ᶠ n in atTop, Real.sqrt (∫ z, Y n z ^ 2 ∂μ n) ≤ C)
    (hbad : Tendsto (fun n => (μ n).real (G n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, Y n z ∂μ n) atTop (𝓝 L) := by
  have hs : Tendsto (fun n => Real.sqrt ((μ n).real (G n)ᶜ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hbad
  have he : Tendsto (fun n => C*Real.sqrt ((μ n).real (G n)ᶜ)+|L| *(μ n).real (G n)ᶜ)
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hs.const_mul C).add (hbad.const_mul |L|)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε2 : 0 < ε/2 := by positivity
  filter_upwards [hgood (ε/2) hε2, hL2, he.eventually (gt_mem_nhds hε2)] with n hn hL hn'
  rw [Real.dist_eq]
  have hh := expectation_error_bound (hY n) (hY0 n) (hG n) hε2.le
    (fun z hz => (hn z hz).le) hL
  linarith

theorem integrable_sommerfeldDensity_exterior {a : ℝ} (ha : 0 < a) :
    IntegrableOn sommerfeldDensity {x | a < ‖x‖} := by
  change Integrable (fun x : Position => kTF*aTF^(3/2 : ℝ) / ‖x‖^6)
    (volume.restrict {x | a < ‖x‖})
  exact (integrable_exterior_inverse_sixth ha).const_mul (kTF*aTF^(3/2 : ℝ))

theorem sommerfeldDensity_exteriorMass {a : ℝ} (ha : 0 < a) :
    (∫ x : Position in {x | a < ‖x‖}, sommerfeldDensity x) =
      (81*Real.pi^2/2) / a^3 := by
  change (∫ x : Position in {x | a < ‖x‖},
    kTF*aTF^(3/2 : ℝ)*(‖x‖^6)⁻¹) = _
  rw [integral_const_mul, integral_exterior_inverse_sixth ha, profile_coefficient,
    aTF_value]
  field_simp
  ring

theorem sommerfeldDensity_annularMass {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : Position in {x | a < ‖x‖ ∧ ‖x‖ < b}, sommerfeldDensity x) =
      (81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3 := by
  rw [← sommerfeldDensity_exteriorMass ha, ← sommerfeldDensity_exteriorMass (ha.trans_le hab),
    ← setIntegral_sdiff (isOpen_lt continuous_const continuous_norm).measurableSet
      (integrable_sommerfeldDensity_exterior ha) (by intro x hx; exact hab.trans_lt hx)]
  symm
  apply setIntegral_congr_set
  have hsphere : ∀ᵐ x : Position, x ∉ Metric.sphere (0 : Position) b := by
    rw [ae_iff]
    convert Measure.addHaar_sphere volume (0 : Position) b using 1
    congr 1
    ext x
    simp
  filter_upwards [hsphere] with x hx
  simp only [Metric.mem_sphere, dist_zero_right] at hx
  apply propext
  change (a < ‖x‖ ∧ ¬ b < ‖x‖) ↔ (a < ‖x‖ ∧ ‖x‖ < b)
  constructor
  · rintro ⟨hr,hR⟩
    exact ⟨hr, lt_of_le_of_ne (le_of_not_gt hR) hx⟩
  · exact fun h => ⟨h.1, not_lt_of_ge h.2.le⟩

theorem RetainedAnalyticFamily.expected_integral {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {G : ∀ n, Set (Ω n)}
    (d : RetainedAnalyticFamily (fun n => G n))
    (σ : ∀ n, Ω n → Position → ℝ)
    (hσ : ∀ n (θ : G n), σ n θ = d.σ n θ)
    {S K : Set Position} (hK : IsCompact K) (hK0 : (0 : Position) ∉ K) (hSK : S ⊆ K)
    (hY : ∀ n, MemLp (fun z => ∫ x in S, σ n z x) 2 (μ n))
    (hY0 : ∀ n, 0 ≤ᵐ[μ n] (fun z => ∫ x in S, σ n z x))
    (hG : ∀ n, MeasurableSet (G n)) {C : ℝ}
    (hL2 : ∀ᶠ n in atTop, Real.sqrt (∫ z, (∫ x in S, σ n z x)^2 ∂μ n) ≤ C)
    (hbad : Tendsto (fun n => (μ n).real (G n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, (∫ x in S, σ n z x) ∂μ n) atTop
      (𝓝 (∫ x in S, sommerfeldDensity x)) := by
  apply expectation_tendsto_of_eventual_uniform μ (fun n z => ∫ x in S, σ n z x) G
    hY hY0 hG ?_ hL2 hbad
  intro ε hε
  filter_upwards [d.uniform_integral hK hK0 hSK ε hε] with n hn z hz
  have hh := hn ⟨z,hz⟩
  simpa only [← hσ n ⟨z,hz⟩] using hh

theorem RetainedAnalyticFamily.expected_annulus {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {G : ∀ n, Set (Ω n)}
    (d : RetainedAnalyticFamily (fun n => G n))
    (σ : ∀ n, Ω n → Position → ℝ) (hσ : ∀ n (θ : G n), σ n θ = d.σ n θ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hY : ∀ n, MemLp (fun z => ∫ x in {x | a < ‖x‖ ∧ ‖x‖ < b}, σ n z x) 2 (μ n))
    (hY0 : ∀ n, 0 ≤ᵐ[μ n] (fun z => ∫ x in {x | a < ‖x‖ ∧ ‖x‖ < b}, σ n z x))
    (hG : ∀ n, MeasurableSet (G n)) {C : ℝ}
    (hL2 : ∀ᶠ n in atTop, Real.sqrt (∫ z,
      (∫ x in {x | a < ‖x‖ ∧ ‖x‖ < b}, σ n z x)^2 ∂μ n) ≤ C)
    (hbad : Tendsto (fun n => (μ n).real (G n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, (∫ x in {x | a < ‖x‖ ∧ ‖x‖ < b}, σ n z x) ∂μ n)
      atTop (𝓝 ((81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3)) := by
  rw [← sommerfeldDensity_annularMass ha hab.le]
  apply d.expected_integral μ σ hσ (isCompact_closedNormAnnulus a b) ?_
    (fun x hx => ⟨hx.1.le,hx.2.le⟩) hY hY0 hG hL2 hbad
  intro hh
  exact (not_le_of_gt ha) (by simpa using hh.1)

end NeutralAtom
end

end

end OAI
