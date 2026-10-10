import OAI.NumberTheory.DukePrimeDegree.Geometry.DiscreteMaximal
import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitCoboundary

namespace OAI

/-!
# Uniform generic sets for bounded observables

The maximal estimate is applied to the small L1 residual of a single
finite orbit average. The complementary part is an explicit bounded
coboundary. Consequently one fixed set controls every sufficiently
large averaging length, including lengths chosen from a nearby pair.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

lemma measurable_orbit_average (T : X → X) (hT : Measurable T)
    (f : X → ℝ) (hf : Measurable f) (N : ℕ) :
    Measurable (birkhoffAverage ℝ T f N) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ (fun k _ => hf.comp (hT.iterate k))

lemma integrable_orbit_average (μ : Measure X) (T : X → X)
    (hT : MeasurePreserving T μ μ) (f : X → ℝ) (hf : Integrable f μ) (N : ℕ) :
    Integrable (birkhoffAverage ℝ T f N) μ := by
  apply Integrable.const_mul
  exact integrable_finsetSum _ (fun k _ => (hT.iterate k).integrable_comp_of_integrable hf)

omit [MeasurableSpace X] in
lemma abs_orbit_average_le_of_abs_sum_le (T : X → X) (r : X → ℝ)
    (η : ℝ) (N : ℕ) (hN : N ≠ 0) (x : X)
    (hsum : birkhoffSum T (fun y => |r y|) N x ≤ η * N) :
    |birkhoffAverage ℝ T r N x| ≤ η := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  rw [birkhoffAverage, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ (N : ℝ)⁻¹ * birkhoffSum T (fun y => |r y|) N x :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (N : ℝ)⁻¹ * (η * N) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = η := by field_simp

/-- Quantitative good set from one finite-average residual. -/
theorem exists_uniform_average_set_from_residual
    (μ : Measure X) [IsFiniteMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ)
    (f : X → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C)
    (c η : ℝ) (hη : 0 < η) (M : ℕ) (hM : M ≠ 0) :
    ∃ G : Set X, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal
        ((∫ x, |birkhoffAverage ℝ T f M x - c| ∂μ) / η) ∧
      ∀ x ∈ G, ∀ N : ℕ, N ≠ 0 →
        |birkhoffAverage ℝ T f N x - c| ≤ (N : ℝ)⁻¹ * (2 * (M * C)) + η := by
  let r : X → ℝ := fun x => birkhoffAverage ℝ T f M x - c
  have hrm : Measurable r := (measurable_orbit_average T hT.measurable f hfm M).sub measurable_const
  have hri : Integrable r μ := (integrable_orbit_average μ T hT f hfi M).sub (integrable_const c)
  obtain ⟨G, hG, hGμ, hGsum⟩ := exists_discrete_average_good_set μ hT hri.norm
    (by simpa only [Real.norm_eq_abs] using hrm.norm) (fun x => abs_nonneg (r x)) η hη
  refine ⟨G, hG, hGμ, ?_⟩
  intro x hx N hN
  have hrbound : |birkhoffAverage ℝ T r N x| ≤ η :=
    abs_orbit_average_le_of_abs_sum_le T r η N hN x (hGsum x hx N)
  have hcob := orbit_average_coboundary_bound T (orbitAveragePotential T f M)
    (M * C) (orbitAveragePotential_abs_le T f C hC0 hC M) N x
  have hfun : (fun y => orbitAveragePotential T f M y -
      orbitAveragePotential T f M (T y)) = fun y => f y - birkhoffAverage ℝ T f M y := by
    funext y
    exact (sub_orbit_average_eq_coboundary T f M hM y).symm
  rw [hfun] at hcob
  have hc : birkhoffAverage ℝ T (fun _ => c) N x = c := by
    exact birkhoffAverage_apply_of_comp_eq ℝ rfl (Nat.cast_ne_zero.mpr hN) x
  have hdecomp : birkhoffAverage ℝ T f N x - c =
      birkhoffAverage ℝ T (fun y => f y - birkhoffAverage ℝ T f M y) N x +
        birkhoffAverage ℝ T r N x := by
    change _ = birkhoffAverage ℝ T (f - birkhoffAverage ℝ T f M) N x +
      birkhoffAverage ℝ T (birkhoffAverage ℝ T f M - fun _ => c) N x
    rw [birkhoffAverage_sub_apply, birkhoffAverage_sub_apply, hc]
    ring
  rw [hdecomp]
  exact (abs_add_le _ _).trans (add_le_add hcob hrbound)

/-- L1 convergence of bounded orbit averages yields a single measurable
set of arbitrarily large measure with uniform eventual convergence.
The convergence premise is stated separately so it can be supplied by
an ergodic real flow after smoothing over one unit of time. -/
theorem exists_uniform_generic_set_of_L1_convergence
    (μ : Measure X) [IsFiniteMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ)
    (f : X → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C)
    (c : ℝ)
    (hmean : Tendsto (fun M => ∫ x, |birkhoffAverage ℝ T f M x - c| ∂μ) atTop (𝓝 0))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set X, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ N₀ : ℕ, ∀ x ∈ G, ∀ N ≥ N₀, |birkhoffAverage ℝ T f N x - c| ≤ ε := by
  have hsmall := hmean.eventually (gt_mem_nhds (show (0 : ℝ) < δ * (ε / 2) by positivity))
  obtain ⟨M, hM, hres⟩ := (eventually_gt_atTop (0 : ℕ)).and hsmall |>.exists
  obtain ⟨G, hG, hGμ, hGbound⟩ := exists_uniform_average_set_from_residual μ T hT
    f hfm hfi C hC0 hC c (ε / 2) (by positivity) M (Nat.ne_of_gt hM)
  refine ⟨G, hG, hGμ.trans ?_, ?_⟩
  · apply ENNReal.ofReal_le_ofReal
    exact (div_le_iff₀ (by positivity : 0 < ε / 2)).mpr hres.le
  · have hlim : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (2 * (M * C))) atTop (𝓝 0) := by
      simpa only [div_eq_inv_mul] using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
          Tendsto (fun N : ℕ => (2 * (M * C)) / (N : ℝ)) atTop (𝓝 0))
    have htail := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_gt_atTop (0 : ℕ)).and htail)
    refine ⟨N₀, ?_⟩
    intro x hx N hN
    have hs := hGbound x hx N (Nat.ne_of_gt (hN₀ N hN).1)
    linarith [(hN₀ N hN).2]

end DukePrimeDegree

end

end OAI
