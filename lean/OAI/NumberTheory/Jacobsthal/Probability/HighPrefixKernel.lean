import Mathlib.Probability.Kernel.Composition.Prod
import OAI.NumberTheory.Jacobsthal.Paths.HighPrefixState

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.HighPrefixKernel

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open WeightedKernelMass HarmonicPrefixKernel HarmonicPrefixTilt HarmonicLongPrefixes HighPrefixState

noncomputable def kernel (ell S : ℝ) : Kernel State State :=
  ((Kernel.id : Kernel State State).prod
    ((HarmonicPrefixKernel.kernel ell).comap (fun z : State => z.1) measurable_fst)).map
      (Function.uncurry (update S))

instance kernel_isSFinite (ell S : ℝ) : IsSFiniteKernel (kernel ell S) := by
  unfold kernel
  infer_instance

lemma update_at_measurable (S : ℝ) (z : State) : Measurable (update S z) :=
  (update_measurable S).of_uncurry_left

theorem kernel_eq_map (ell S : ℝ) (z : State) :
    kernel ell S z = (HarmonicPrefixKernel.kernel ell z.1).map (update S z) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [kernel,Kernel.map_apply _ (update_measurable S),lintegral_map hf (update_measurable S)]
  have hg : Measurable (fun p : State × ℝ => f (update S p.1 p.2)) := hf.comp (update_measurable S)
  calc
    _ = ∫⁻ t, f (update S z t) ∂HarmonicPrefixKernel.kernel ell z.1 :=
      Kernel.lintegral_id_prod (f := fun p : State × ℝ => f (update S p.1 p.2)) hg _ z
    _ = _ := (lintegral_map hf (update_at_measurable S z)).symm

lemma harmonic_ae_interval (ell B : ℝ) :
    ∀ᵐ t ∂HarmonicPrefixKernel.kernel ell B, t ∈ Ioc ell B := by
  rw [HarmonicPrefixKernel.kernel_eq_restrict,
    ae_withDensity_iff (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (t⁻¹)))]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
  intro _
  exact ht

theorem ae_update (ell S : ℝ) (z : State) {P : State → Prop}
    (hP : MeasurableSet {w | P w}) (h : ∀ t ∈ Ioc ell z.1, P (update S z t)) :
    ∀ᵐ w ∂kernel ell S z, P w := by
  rw [kernel_eq_map]
  apply (ae_map_iff (update_at_measurable S z).aemeasurable hP).mpr
  exact (harmonic_ae_interval ell z.1).mono (fun t ht => h t ht)

lemma state_schur_one {ell : ℝ} (hell : 0<ell) (S : ℝ) (z : State) :
    1+(∫⁻ w, boundE ell w.1 ∂kernel ell S z) = boundE ell z.1 := by
  rw [kernel_eq_map]
  have hf : Measurable (fun w : State => boundE ell w.1) := (boundE_measurable ell).comp measurable_fst
  rw [lintegral_map (f := fun w : State => boundE ell w.1) hf (update_at_measurable S z)]
  exact schur_one hell z.1

lemma state_schur_two {ell : ℝ} (hell : 0<ell) (S : ℝ) (z : State) :
    1+2*(∫⁻ w, squareBoundE ell w.1 ∂kernel ell S z) = squareBoundE ell z.1 := by
  rw [kernel_eq_map]
  have hf : Measurable (fun w : State => squareBoundE ell w.1) := (squareBoundE_measurable ell).comp measurable_fst
  rw [lintegral_map (f := fun w : State => squareBoundE ell w.1) hf (update_at_measurable S z)]
  exact schur_two hell z.1

theorem total_mass {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) (S R : ℝ) :
    (∑' n : ℕ, mass (kernel ell S) n (initial S B R)) ≤ ENNReal.ofReal (B/ell) := by
  have h := weighted_total_bound (kernel ell S) 1 (fun z : State => boundE ell z.1)
    (fun z => by simpa only [one_mul] using (state_schur_one hell S z).le) (initial S B R)
  simpa only [one_pow,one_mul,initial,boundE,bound_on hell hB] using h

theorem weighted_mass {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) (S R : ℝ) :
    (∑' n : ℕ, (2:ℝ≥0∞)^n*mass (kernel ell S) n (initial S B R)) ≤ ENNReal.ofReal ((B/ell)^2) := by
  have h := weighted_total_bound (kernel ell S) 2 (fun z : State => squareBoundE ell z.1)
    (fun z => (state_schur_two hell S z).le) (initial S B R)
  simpa only [initial,squareBoundE,bound_on hell hB] using h

theorem ae_invariant {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) (S R : ℝ) :
    ∀ n : ℕ, (n:ℝ)≤S →
      ∀ᵐ z ∂(kernel ell S ^ n) (initial S B R), Invariant ell S n z := by
  intro n
  induction n with
  | zero =>
    intro _
    change ∀ᵐ z ∂Measure.dirac (initial S B R), Invariant ell S 0 z
    exact (ae_dirac_iff (invariant_measurable ell S 0)).mpr (initial_invariant hell hB)
  | succ n ih =>
    intro hn
    have hn' : (n:ℝ)≤S := by push_cast at hn; linarith
    rw [pow_succ']
    apply Kernel.ae_comp_of_ae_ae (invariant_measurable ell S (n+1))
    filter_upwards [ih hn'] with z hz
    exact ae_update ell S z (invariant_measurable ell S (n+1))
      (fun t ht => update_invariant hell n z t hz ht hn')

end ErdosPrimeInputs.HighPrefixKernel

end

end Erdos970

end OAI
