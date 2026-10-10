import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-!
# Invariant observables on asymptotic pairs

This is the measurable part of the stable-leaf argument. The two
coordinates of a family of pairs have uniformly dominated marginals. If
the coordinates become asymptotic, every integrable observable which is
unchanged along both coordinate sequences has equal values on the pair.

The proof uses compactly supported continuous approximation in L¹ and
dominated convergence. It requires no ergodicity or pointwise ergodic
theorem.
-/

open MeasureTheory Filter Set
open scoped Topology Uniformity

namespace DukePrimeDegree

variable {α Z : Type*} [UniformSpace α] [T2Space α] [NormalSpace α]
  [WeaklyLocallyCompactSpace α] [MeasurableSpace α] [BorelSpace α]
  [MeasurableSpace Z]

omit [T2Space α] [NormalSpace α] [WeaklyLocallyCompactSpace α] in
/-- Compactly supported continuous observables have vanishing mean
oscillation on a finite measure of asymptotic pairs. -/
theorem integral_compact_observable_difference_tendsto_zero
    (nu : Measure Z) [IsFiniteMeasure nu]
    (p q : ℕ → Z → α)
    (hp : ∀ n, Measurable (p n))
    (hq : ∀ n, Measurable (q n))
    (hasymptotic : ∀ᵐ z ∂nu,
      Tendsto (fun n => (p n z, q n z)) atTop (𝓤 α))
    (g : α → ℝ) (hg : Continuous g) (hcompact : HasCompactSupport g) :
    Tendsto (fun n => ∫ z, |g (p n z) - g (q n z)| ∂nu) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hg
  have hlim : ∀ᵐ z ∂nu,
      Tendsto (fun n => |g (p n z) - g (q n z)|) atTop (𝓝 0) := by
    filter_upwards [hasymptotic] with z hz
    have hu : Tendsto (fun n => (g (p n z), g (q n z))) atTop (𝓤 ℝ) :=
      (show Tendsto (fun z : α × α => (g z.1, g z.2)) (𝓤 α) (𝓤 ℝ) from
        hcompact.uniformContinuous_of_continuous hg).comp hz
    simpa only [Real.dist_eq] using tendsto_uniformity_iff_dist_tendsto_zero.mp hu
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun z => |g (p n z) - g (q n z)|) nu := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Function.comp_apply] using
      ((hg.measurable.comp (hp n)).sub
        (hg.measurable.comp (hq n))).norm.aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ z ∂nu, ‖|g (p n z) - g (q n z)|‖ ≤ 2 * C := by
    apply ae_of_all
    intro z
    rw [Real.norm_eq_abs, abs_abs]
    calc
      |g (p n z) - g (q n z)| ≤ |g (p n z)| + |g (q n z)| := abs_sub _ _
      _ ≤ C + C := add_le_add (hC _) (hC _)
      _ = 2 * C := by ring
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (fun _ : Z => 2 * C) hm
      (integrable_const _) hb hlim

/-- An integrable invariant observable is equal on any asymptotic pair
family with dominated marginals. This is the Hopf stable-pair principle in
the form used for neutral diagonal actions on leaf measures. -/
theorem ae_eq_of_compact_observable_dominated_pairs
    (μ : Measure α) [μ.Regular] (nu : Measure Z) [IsFiniteMeasure nu]
    (p q : ℕ → Z → α)
    (hp : ∀ n, Measurable (p n))
    (hq : ∀ n, Measurable (q n))
    (hpμ : ∀ n, nu.map (p n) ≤ μ)
    (hqμ : ∀ n, nu.map (q n) ≤ μ)
    (hcompactlim : ∀ g : α → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun n => ∫ z, |g (p n z) - g (q n z)| ∂nu) atTop (𝓝 0))
    (f : α → ℝ) (hf : Integrable f μ)
    (hfp : ∀ n, (fun z => f (p n z)) =ᵐ[nu] fun z => f (p 0 z))
    (hfq : ∀ n, (fun z => f (q n z)) =ᵐ[nu] fun z => f (q 0 z)) :
    (fun z => f (p 0 z)) =ᵐ[nu] fun z => f (q 0 z) := by
  let D := ∫ z, |f (p 0 z) - f (q 0 z)| ∂nu
  have hfint (n : ℕ) : Integrable (fun z => f (p n z)) nu :=
    (hf.mono_measure (hpμ n)).comp_measurable (hp n)
  have hfqint (n : ℕ) : Integrable (fun z => f (q n z)) nu :=
    (hf.mono_measure (hqμ n)).comp_measurable (hq n)
  have hsmall (ε : ℝ) (hε : 0 < ε) : D ≤ 2 * ε := by
    obtain ⟨g, hcompact, herror, hg, hgint⟩ :=
      hf.exists_hasCompactSupport_integral_sub_le hε
    have herrint : Integrable (fun x => |f x - g x|) μ := (hf.sub hgint).abs
    have herrmap (r : Z → α) (hr : Measurable r) (hrμ : nu.map r ≤ μ) :
        (∫ z, |f (r z) - g (r z)| ∂nu) ≤ ∫ x, |f x - g x| ∂μ := by
      rw [← integral_map hr.aemeasurable (herrint.mono_measure hrμ).aestronglyMeasurable]
      exact integral_mono_measure hrμ (Eventually.of_forall (fun x => abs_nonneg _)) herrint
    have hlim := hcompactlim g hg hcompact
    have hineq (n : ℕ) : D ≤ 2 * ε + ∫ z, |g (p n z) - g (q n z)| ∂nu := by
      have hpgi : Integrable (fun z => g (p n z)) nu :=
        (hgint.mono_measure (hpμ n)).comp_measurable (hp n)
      have hqgi : Integrable (fun z => g (q n z)) nu :=
        (hgint.mono_measure (hqμ n)).comp_measurable (hq n)
      have hpoint : ∀ᵐ z ∂nu, |f (p 0 z) - f (q 0 z)| ≤
          |f (p n z) - g (p n z)| + |g (p n z) - g (q n z)| +
            |f (q n z) - g (q n z)| := by
        filter_upwards [hfp n, hfq n] with z hpz hqz
        rw [← hpz, ← hqz]
        calc
          |f (p n z) - f (q n z)| =
              |(f (p n z) - g (p n z)) + (g (p n z) - g (q n z)) +
                (g (q n z) - f (q n z))| := by congr 1; ring
          _ ≤ |f (p n z) - g (p n z)| + |g (p n z) - g (q n z)| +
              |g (q n z) - f (q n z)| := (abs_add_le _ _).trans
                (add_le_add (abs_add_le _ _) le_rfl)
          _ = _ := by rw [abs_sub_comm (g (q n z))]
      have hi := integral_mono_ae ((hfint 0).sub (hfqint 0)).abs
        ((((hfint n).sub hpgi).abs.add (hpgi.sub hqgi).abs).add
          ((hfqint n).sub hqgi).abs) hpoint
      simp only [Pi.add_apply, Pi.sub_apply] at hi
      have hadd := integral_add (((hfint n).sub hpgi).abs.add (hpgi.sub hqgi).abs)
        ((hfqint n).sub hqgi).abs
      have hadd' := integral_add ((hfint n).sub hpgi).abs (hpgi.sub hqgi).abs
      simp only [Pi.add_apply, Pi.sub_apply] at hadd hadd'
      rw [hadd, hadd'] at hi
      have herrp := herrmap (p n) (hp n) (hpμ n)
      have herrq := herrmap (q n) (hq n) (hqμ n)
      have herr : (∫ x, |f x - g x| ∂μ) ≤ ε := by
        simpa only [Real.norm_eq_abs] using herror
      dsimp only [D]
      linarith
    have hh := ge_of_tendsto (tendsto_const_nhds.add hlim)
      (Filter.Eventually.of_forall hineq)
    simpa only [add_zero] using hh
  have hDnonneg : 0 ≤ D := integral_nonneg (fun z => abs_nonneg _)
  have hDzero : D = 0 := by
    by_contra hD
    have hDpos : 0 < D := lt_of_le_of_ne hDnonneg (Ne.symm hD)
    have h := hsmall (D / 4) (by positivity)
    linarith
  have heq : (fun z => |f (p 0 z) - f (q 0 z)|) =ᵐ[nu] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => abs_nonneg _)
      ((hfint 0).sub (hfqint 0)).abs).mp hDzero
  filter_upwards [heq] with z hz
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

/-- Asymptotic pairs give the compact-observable condition by uniform
continuity and dominated convergence. -/
theorem ae_eq_of_asymptotic_dominated_pairs
    (μ : Measure α) [μ.Regular] (nu : Measure Z) [IsFiniteMeasure nu]
    (p q : ℕ → Z → α)
    (hp : ∀ n, Measurable (p n))
    (hq : ∀ n, Measurable (q n))
    (hpμ : ∀ n, nu.map (p n) ≤ μ)
    (hqμ : ∀ n, nu.map (q n) ≤ μ)
    (hasymptotic : ∀ᵐ z ∂nu,
      Tendsto (fun n => (p n z, q n z)) atTop (𝓤 α))
    (f : α → ℝ) (hf : Integrable f μ)
    (hfp : ∀ n, (fun z => f (p n z)) =ᵐ[nu] fun z => f (p 0 z))
    (hfq : ∀ n, (fun z => f (q n z)) =ᵐ[nu] fun z => f (q 0 z)) :
    (fun z => f (p 0 z)) =ᵐ[nu] fun z => f (q 0 z) :=
  ae_eq_of_compact_observable_dominated_pairs μ nu p q hp hq hpμ hqμ
    (fun g hg hc => integral_compact_observable_difference_tendsto_zero
      nu p q hp hq hasymptotic g hg hc) f hf hfp hfq

/-- Equal marginals are a useful special case of the dominated-pair
principle. No invariance of the joint pair measure is required. -/
theorem ae_eq_of_asymptotic_preserving_pairs
    (μ : Measure α) [μ.Regular] (nu : Measure Z) [IsFiniteMeasure nu]
    (p q : ℕ → Z → α)
    (hp : ∀ n, MeasurePreserving (p n) nu μ)
    (hq : ∀ n, MeasurePreserving (q n) nu μ)
    (hasymptotic : ∀ᵐ z ∂nu,
      Tendsto (fun n => (p n z, q n z)) atTop (𝓤 α))
    (f : α → ℝ) (hf : Integrable f μ)
    (hfp : ∀ n, (fun z => f (p n z)) =ᵐ[nu] fun z => f (p 0 z))
    (hfq : ∀ n, (fun z => f (q n z)) =ᵐ[nu] fun z => f (q 0 z)) :
    (fun z => f (p 0 z)) =ᵐ[nu] fun z => f (q 0 z) :=
  ae_eq_of_asymptotic_dominated_pairs μ nu p q (fun n => (hp n).measurable)
    (fun n => (hq n).measurable) (fun n => (hp n).map_eq.le)
    (fun n => (hq n).map_eq.le) hasymptotic f hf hfp hfq

/-- The dynamical form: invariant observables agree on pairs whose
forward orbits become asymptotic. The pair marginals need only be
dominated by the invariant measure, as happens for a foliation chart. -/
theorem ae_eq_of_asymptotic_pair_orbits
    (μ : Measure α) [μ.Regular] (nu : Measure Z) [IsFiniteMeasure nu]
    (r s : Z → α) (hr : Measurable r) (hs : Measurable s)
    (hrμ : nu.map r ≤ μ) (hsμ : nu.map s ≤ μ)
    (T : α → α) (hT : MeasurePreserving T μ μ)
    (hasymptotic : ∀ᵐ z ∂nu,
      Tendsto (fun n => (T^[n] (r z), T^[n] (s z))) atTop (𝓤 α))
    (f : α → ℝ) (hf : Integrable f μ)
    (hfinv : (fun x => f (T x)) =ᵐ[μ] f) :
    (fun z => f (r z)) =ᵐ[nu] fun z => f (s z) := by
  have hi (n : ℕ) : (fun x => f (T^[n] x)) =ᵐ[μ] f := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh : ∀ᵐ x ∂μ, f (T^[n] (T x)) = f (T x) := by
        exact ae_of_ae_map hT.measurable.aemeasurable
          (p := fun x => f (T^[n] x) = f x) (by rwa [hT.map_eq])
      filter_upwards [hh, hfinv] with x hx h0
      simpa only [Function.iterate_succ_apply] using hx.trans h0
  have hmap (r : Z → α) (hr : Measurable r) (hrμ : nu.map r ≤ μ) (n : ℕ) :
      nu.map (fun z => T^[n] (r z)) ≤ μ := by
    change nu.map (T^[n] ∘ r) ≤ μ
    rw [← Measure.map_map (hT.iterate n).measurable hr]
    exact (Measure.map_mono hrμ (hT.iterate n).measurable).trans_eq (hT.iterate n).map_eq
  have hfix (r : Z → α) (hr : Measurable r) (hrμ : nu.map r ≤ μ) (n : ℕ) :
      (fun z => f (T^[n] (r z))) =ᵐ[nu] fun z => f (T^[0] (r z)) := by
    exact ae_of_ae_map hr.aemeasurable
      (p := fun x => f (T^[n] x) = f x) (ae_mono hrμ (hi n))
  have h := ae_eq_of_asymptotic_dominated_pairs μ nu
    (fun n z => T^[n] (r z)) (fun n z => T^[n] (s z))
    (fun n => (hT.iterate n).measurable.comp hr)
    (fun n => (hT.iterate n).measurable.comp hs)
    (hmap r hr hrμ) (hmap s hs hsμ) hasymptotic f hf
    (hfix r hr hrμ) (hfix s hs hsμ)
  simpa only [Function.iterate_zero, id_eq] using h

end DukePrimeDegree

end OAI
