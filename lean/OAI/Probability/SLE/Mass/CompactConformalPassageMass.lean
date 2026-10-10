import OAI.Probability.SLE.Gauge.ConformalCompactSausage
import OAI.Probability.SLE.Gauge.RibbonPassageMass
import OAI.Probability.SLE.SausageCharge
import OAI.Probability.SLE.Gauge.RetainedPassageExtraction

namespace OAI

/-! The compact-retention and sausage part of the uniform ribbon step,
assembled for actual locally convergent conformal maps and actual SLE.
Only the passage event and its retained intervals are supplied by geometry. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

theorem compact_conformal_ribbon_mass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hne : ∀ z ∈ upperHalfPlane, deriv F z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (K : Set ℂ) (hK : IsCompact K) (hKn : K.Nonempty) (hKH : K ⊆ upperHalfPlane)
    (R : Set ℂ) (hR : IsOpen R) (himage : F '' K ⊆ R)
    (I : Finset (ℝ≥0 × ℝ≥0)) (hI : ∀ J ∈ I, J.1 < J.2)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P (G n))
    (hretain : ∀ᶠ n in atTop, ∀ ω, ω ∈ G n →
      ∃ J ∈ I, γ ω '' Icc J.1 J.2 ⊆ K) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 2) ≤ P {ω | ω ∈ G n ∧ ENNReal.ofReal a ≤
        wholeSausageCharge κ (fun t => Fₙ n (γ ω t)) (v n) R} := by
  obtain ⟨c, ell, v₀, hc, hell, hv₀, htransfer⟩ := eventually_compact_sausage_transfer
    κ Fₙ F hFn hinj hF hne hconv K hK hKn hKH R hR himage
  have hcoeff : 0 < c ^ 2 * ell ^ codimension κ :=
    mul_pos (sq_pos_of_pos hc) (Real.rpow_pos_of_pos hell _)
  have hsmall : ∀ᶠ n in atTop, v n < v₀ := hlim.eventually (gt_mem_nhds hv₀)
  have hlim' : Tendsto (fun n => ell * v n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlim
  have htrans : ∀ᶠ n in atTop, ∀ ω, ω ∈ G n → True ∧
      ∃ J ∈ I, ENNReal.ofReal (c ^ 2 * ell ^ codimension κ) *
        sourceSausageMass κ (γ ω) J.1 J.2 (ell * v n) ≤
        wholeSausageCharge κ (fun t => Fₙ n (γ ω t)) (v n) R := by
    filter_upwards [htransfer, hretain, hsmall] with n hn hr hs
    intro ω hω
    obtain ⟨J, hJI, hJK⟩ := hr ω hω
    refine ⟨trivial, J, hJI, (hn (γ ω) J.1 J.2 hJK (v n) (hv n) hs).trans ?_⟩
    apply mul_le_mul' le_rfl (measure_mono (inter_subset_inter_right R ?_))
    rintro z ⟨t, _, hdist⟩
    exact ⟨t, by simpa only [dist_comm] using hdist⟩
  obtain ⟨a, ha, hmass⟩ := ribbon_passage_mass_of_eventually_finite_intervals
    P κ hκ hκ8 γ hSLE I hI (fun n => ell * v n)
    (fun n => mul_pos hell (hv n)) hlim' G q hq hG
    (fun n ω => wholeSausageCharge κ (fun t => Fₙ n (γ ω t)) (v n) R)
    (fun _ _ => True) (c ^ 2 * ell ^ codimension κ) hcoeff htrans
  exact ⟨a, ha, by simpa only [true_and] using hmass⟩

/-- A countable family of actual retained compact intervals is enough.
The finite extraction, common mesh, derivative constants, and unconditional
small-sausage subtraction are all performed here. -/
theorem countable_compact_conformal_ribbon_mass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hne : ∀ z ∈ upperHalfPlane, deriv F z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (K : ℕ → Set ℂ) (hK : ∀ i, IsCompact (K i))
    (hKH : ∀ i, K i ⊆ upperHalfPlane)
    (R : Set ℂ) (hR : IsOpen R) (himage : ∀ i, F '' K i ⊆ R)
    (J : ℕ → ℝ≥0 × ℝ≥0) (hJ : ∀ i, (J i).1 < (J i).2)
    (E : Set Ω) (D : ℕ → Set Ω)
    (hE : MeasurableSet E) (hD : ∀ i, MeasurableSet (D i))
    (hcover : P (E \ ⋃ i, D i) = 0)
    (hretain : ∀ i ω, ω ∈ D i → γ ω '' Icc (J i).1 (J i).2 ⊆ K i)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ n, ENNReal.ofReal q ≤ P (G n ∩ E)) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 4) ≤ P {ω | ω ∈ G n ∩ E ∧ ENNReal.ofReal a ≤
        wholeSausageCharge κ (fun t => Fₙ n (γ ω t)) (v n) R} := by
  classical
  obtain ⟨N, hN⟩ := varying_events_after_finite_retention P E D G hE hD hcover q hq hG
  let A := ⋃ i ∈ Finset.range N, D i
  let Q := ⋃ i ∈ Finset.range N, K i
  let H : ℕ → Set Ω := fun n => G n ∩ E ∩ A
  have hQ : IsCompact Q := (Finset.range N).isCompact_biUnion (fun i _ => hK i)
  have hQH : Q ⊆ upperHalfPlane := iUnion₂_subset (fun i _ => hKH i)
  have hQR : F '' Q ⊆ R := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hz
    exact himage i (mem_image_of_mem F hi)
  have hQn : Q.Nonempty := by
    have hHpos : 0 < P (H 0) := (ENNReal.ofReal_pos.mpr (by positivity : 0 < q / 2)).trans_le (hN 0)
    obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero hHpos.ne'
    obtain ⟨i, hi, hDi⟩ := mem_iUnion₂.mp hω.2
    refine ⟨γ ω (J i).1, mem_iUnion₂.mpr ⟨i, hi, ?_⟩⟩
    exact hretain i ω hDi (mem_image_of_mem (γ ω) ⟨le_rfl, (hJ i).le⟩)
  let I := (Finset.range N).image J
  have hI : ∀ L ∈ I, L.1 < L.2 := by
    intro L hL
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hL
    exact hJ i
  have hr : ∀ n ω, ω ∈ H n → ∃ L ∈ I, γ ω '' Icc L.1 L.2 ⊆ Q := by
    intro n ω hω
    obtain ⟨i, hi, hDi⟩ := mem_iUnion₂.mp hω.2
    exact ⟨J i, Finset.mem_image.mpr ⟨i, hi, rfl⟩,
      (hretain i ω hDi).trans (subset_iUnion₂_of_subset i hi Subset.rfl)⟩
  obtain ⟨a, ha, hmass⟩ := compact_conformal_ribbon_mass P κ hκ hκ8 γ hSLE
    Fₙ F hFn hinj hF hne hconv Q hQ hQn hQH R hR hQR I hI
    v hv hlim H (q / 2) (by positivity) (Eventually.of_forall hN)
    (Eventually.of_forall hr)
  refine ⟨a, ha, ?_⟩
  filter_upwards [hmass] with n hn
  have hqq : q / 2 / 2 = q / 4 := by ring
  rw [hqq] at hn
  exact hn.trans (measure_mono (fun _ hω => ⟨hω.1.1, hω.2⟩))

end SLEExactGauge

end

end OAI
