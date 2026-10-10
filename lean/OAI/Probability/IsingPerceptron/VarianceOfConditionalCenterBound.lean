import Mathlib
import OAI.Probability.IsingPerceptron.MemLpOfAbsBound

namespace OAI

/-! Variance Of Conditional Center Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

theorem variance_of_conditional_center_bound {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} {X : A → ℝ} (hF : Measurable F) (hX : MemLp X 2 μ)
    (hi : ∀ a, Integrable (fun b => (F (a,b)-X a)^2) ν)
    (hc : ∀ a, ∫ b, F (a,b) ∂ν = X a) {C : A → ℝ} (hC : Integrable C μ)
    (hb : ∀ a, (∫ b, (F (a,b)-X a)^2 ∂ν) ≤ C a) :
    MemLp F 2 (μ.prod ν) ∧ Var[F; μ.prod ν] ≤ (∫ a, C a ∂μ)+Var[X; μ] := by
  let D : A × B → ℝ := fun p => F p-X p.1
  have hd : AEStronglyMeasurable D (μ.prod ν) :=
    hF.aestronglyMeasurable.sub (hX.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_fst (μ := μ) (ν := ν)))
  have hdi : Integrable (fun p => (D p)^2) (μ.prod ν) := by
    apply (integrable_prod_iff (hd.pow 2)).mpr
    refine ⟨ae_of_all _ hi, ?_⟩
    have hnorm : (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) =
        fun a => ∫ b, (D (a,b))^2 ∂ν := by
      ext a
      apply integral_congr_ae
      apply ae_of_all
      intro b
      exact Real.norm_of_nonneg (sq_nonneg _)
    change Integrable (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) μ
    rw [hnorm]
    apply hC.mono' (hd.pow 2).integral_prod_right'
    apply ae_of_all
    intro a
    change ‖∫ b, (D (a,b))^2 ∂ν‖ ≤ C a
    rw [Real.norm_of_nonneg (integral_nonneg (fun b => sq_nonneg (D (a,b))))]
    exact hb a
  have hDLp : MemLp D 2 (μ.prod ν) := (memLp_two_iff_integrable_sq hd).mpr hdi
  have hfLp : MemLp F 2 (μ.prod ν) := by
    convert hDLp.add (hX.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ν))) using 1
    ext p
    simp [D]
  refine ⟨hfLp, ?_⟩
  have hsecLp (a : A) : MemLp (fun b => F (a,b)) 2 ν := by
    have hdm : Measurable (fun b => F (a,b)-X a) :=
      (hF.comp (measurable_const.prodMk measurable_id)).sub measurable_const
    have hL := (memLp_two_iff_integrable_sq hdm.aestronglyMeasurable).mpr (hi a)
    convert hL.add (memLp_const (X a)) using 1
    ext b
    simp
  have hsec (a : A) : (∫ b, F (a,b)^2 ∂ν) ≤ C a+(X a)^2 := by
    have hv := hb a
    have he := variance_eq_integral (hsecLp a).aemeasurable
    rw [hc a] at he
    rw [← he, variance_eq_sub (hsecLp a)] at hv
    simp only [Pi.pow_apply,hc a] at hv
    linarith
  have hh := integral_mono hfLp.integrable_sq.integral_prod_left
    (hC.add hX.integrable_sq) hsec
  simp only [Pi.add_apply] at hh
  rw [integral_add hC hX.integrable_sq] at hh
  rw [variance_eq_sub hfLp,variance_eq_sub hX]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hfLp.integrable_sq,
    integral_prod _ (hfLp.integrable (by norm_num))]
  simp_rw [hc]
  linarith

theorem poisson_count_variance {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (r : ℝ≥0) {F : ℕ × Ω → ℝ} (hF : Measurable F)
    (hL : ∀ m, MemLp (fun ω => F (m,ω)) 2 Q) {C D K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ m, Var[(fun ω => F (m,ω)); Q] ≤ C+D*m)
    (hs : ∀ m, |(∫ ω, F (m+1,ω) ∂Q)-(∫ ω, F (m,ω) ∂Q)| ≤ K) :
    MemLp F 2 ((poissonMeasure r).prod Q) ∧
      Var[F; (poissonMeasure r).prod Q] ≤ C+D*r+K^2*r := by
  let X := fun m => ∫ ω, F (m,ω) ∂Q
  have hx : MemLp X 2 (poissonMeasure r) := nat_step_memLp (poisson_cast_memLp r) hs
  have hc : Integrable (fun m : ℕ => C+D*m) (poissonMeasure r) :=
    (integrable_const C).add (((poisson_cast_memLp r).integrable (by norm_num)).const_mul D)
  have hh := variance_of_conditional_center_bound (poissonMeasure r) Q hF hx
    (fun m => ((hL m).sub (memLp_const (X m))).integrable_sq) (fun _ => rfl) hc
    (fun m => by
      rw [← variance_eq_integral (hL m).aemeasurable]
      exact hv m)
  refine ⟨hh.1, ?_⟩
  have hhx := variance_of_distance_bound (poissonMeasure r) hx (poisson_cast_memLp r) hK
    (nat_abs_step_bound hs)
  rw [poisson_cast_variance] at hhx
  have hmean : (∫ m : ℕ, C+D*m ∂poissonMeasure r) = C+D*r := by
    rw [integral_add (integrable_const C)
      (((poisson_cast_memLp r).integrable (by norm_num)).const_mul D),
      integral_const,probReal_univ,one_smul,integral_const_mul,poisson_cast_mean]
  rw [hmean] at hh
  linarith [hh.2]

lemma infinite_prefix_preserving {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (M : ℕ) :
    MeasurePreserving (fun y : ℕ → A => fun i : Fin M => y i)
      (Measure.infinitePi (fun _ : ℕ => P)) (Measure.pi (fun _ : Fin M => P)) := by
  refine ⟨Measurable.of_eval (fun index => measurable_pi_apply (index : ℕ)), ?_⟩
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]

abbrev InfiniteRootData (m : ℕ) (A : Type*) := (Fin m → ℝ) × (ℕ → A)

def rootPrefix {m : ℕ} {A : Type*} (M : ℕ) (p : InfiniteRootData m A) :
    (Fin m → ℝ) × (Fin M → A) := (p.1,fun i => p.2 i)

lemma rootPrefix_preserving {m : ℕ} {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (M : ℕ) :
    MeasurePreserving (rootPrefix (m := m) (A := A) M)
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.infinitePi (fun _ : ℕ => P)))
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.pi (fun _ : Fin M => P))) :=
  (MeasurePreserving.id _).prod (infinite_prefix_preserving P M)

lemma patternBase_prefix_succ {I A : Type*} [Fintype I] (φ : A → I → ℝ)
    (y : ℕ → A) (M : ℕ) :
    patternBase φ (fun i : Fin (M+1) => y i) = patternBase φ (fun i : Fin M => y i)+φ (y M) := by
  ext x
  simp only [patternBase,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,Pi.add_apply]

lemma rootEnergy_prefix_step {I A : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (a : I → Fin m → ℝ) {φ : A → I → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (p : InfiniteRootData m A) (M : ℕ) :
    |rootEnergy n b μ ν (patternBase φ (fun i : Fin (M+1) => p.2 i)) a p.1-
      rootEnergy n b μ ν (patternBase φ (fun i : Fin M => p.2 i)) a p.1| ≤ K := by
  apply (rootEnergy_base_lipschitz n b μ ν hμ hb _ _ a p.1).trans
  rw [patternBase_prefix_succ,add_sub_cancel_left]
  exact (pi_norm_le_iff_of_nonneg hK).mpr (fun x => by simpa only [Real.norm_eq_abs] using hφ (p.2 M) x)

lemma integral_difference_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)
    {K : ℝ} (h : ∀ ω, |X ω-Y ω| ≤ K) : |(∫ ω, X ω ∂P)-(∫ ω, Y ω ∂P)| ≤ K := by
  rw [← integral_sub hX hY,← Real.norm_eq_abs]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => X ω-Y ω) (C := K)
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using h ω))

lemma cascadeEnergyLog_total_mean {Ω : Type*} {I : Type} [MeasurableSpace Ω] [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    {H : Ω → I → ℝ} (hH : Measurable H) (hL : MemLp (fun ω => energyRecursion n b μ ν (H ω)) 2 P) :
    (∫ p : Ω × NoiseTree (I → ℝ) n, cascadeEnergyLog n b μ ν (H p.1) p.2
      ∂P.prod (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))) =
      ∫ ω, energyRecursion n b μ ν (H ω) ∂P := by
  have hi := (cascadeEnergyLog_variance P n b hb μ ν hμ hH hL).1.integrable (by norm_num)
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => (cascadeEnergyLog_conditional n b hb μ ν hμ (H ω)).2.1)

variable {I A : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable [MeasurableSpace A]

def infinitePatternRoot (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) {m : ℕ} (a : I → Fin m → ℝ) (φ : A → I → ℝ)
    (p : ℕ × InfiniteRootData m A) : ℝ :=
  rootEnergy n b μ ν (patternBase φ (fun i : Fin p.1 => p.2.2 i)) a p.2.1

lemma measurable_infinitePatternRoot (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) {m : ℕ} (a : I → Fin m → ℝ) {φ : A → I → ℝ} (hm : Measurable φ) :
    Measurable (infinitePatternRoot n b μ ν a φ) := by
  apply measurable_from_prod_countable_right
  intro M
  apply (measurable_energyRecursion n b μ ν).comp
  apply Measurable.of_eval
  intro x
  exact (Finset.measurable_sum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) =>
    ((measurable_pi_apply x).comp hm).comp
    ((measurable_pi_apply (i : ℕ)).comp measurable_snd))).add
    (by fun_prop : Measurable (fun p : InfiniteRootData m A => ∑ j, a x j*p.1 j))

lemma infinitePatternRoot_fixed_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (ha : ∀ x j, |a x j| ≤ c j) (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → I → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (M : ℕ) :
    let Q := (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.infinitePi (fun _ : ℕ => P))
    MemLp (fun p => infinitePatternRoot n b μ ν a φ (M,p)) 2 Q ∧
      Var[(fun p => infinitePatternRoot n b μ ν a φ (M,p));Q] ≤ (∑ j, (c j)^2)+M*(2*K)^2 := by
  have hL := pattern_root_energy_memLp n b μ ν hμ hb a c hc ha P hm hK hφ (M := M)
  have hv := pattern_root_energy_variance n b μ ν hμ hb a c hc ha P hm hK hφ (M := M)
  have hp := rootPrefix_preserving (m := m) P M
  constructor
  · simpa only [infinitePatternRoot, Function.comp_def, rootPrefix] using
      hL.comp_measurePreserving hp
  · simpa only [infinitePatternRoot, Function.comp_def, rootPrefix] using
      (hp.variance_fun_comp hL.aemeasurable).le.trans hv

theorem infinitePatternRoot_poisson_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (ha : ∀ x j, |a x j| ≤ c j) (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → I → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (r : ℝ≥0) :
    let Q := (poissonMeasure r).prod ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))
    MemLp (infinitePatternRoot n b μ ν a φ) 2 Q ∧
      Var[infinitePatternRoot n b μ ν a φ;Q] ≤ (∑ j, (c j)^2)+(2*K)^2*r+K^2*r := by
  have hh := infinitePatternRoot_fixed_variance n b μ ν hμ hb a c hc ha P hm hK hφ
  apply poisson_count_variance _ r (measurable_infinitePatternRoot n b μ ν a hm)
    (fun M => (hh M).1) hK
  · intro M
    simpa only [mul_comm (M : ℝ)] using (hh M).2
  · intro M
    apply integral_difference_bound _ ((hh (M+1)).1.integrable (by norm_num))
      ((hh M).1.integrable (by norm_num))
    exact fun p => rootEnergy_prefix_step n b μ ν hμ hb a hK hφ p M

end IsingPerceptron

namespace IsingPerceptron

lemma enriched_poisson_root_variance {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : ∀ i < n, 0 < b i) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := (poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))
    let X := infinitePatternRoot n b μ ν (enrichedCoefficientsFin N n h u 0) φ
    MemLp X 2 Q ∧ Var[X;Q] ≤ N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := by
  let x₀ : Spin N := fun _ => 0
  let c := fun j => |enrichedCoefficientsFin N n h u 0 x₀ j|
  have H := infinitePatternRoot_poisson_variance n b
    (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1)) hb
    (enrichedCoefficientsFin N n h u 0) c (fun _ => abs_nonneg _)
    (fun x j => (enrichedLevelCoefficient_abs n h u 0 x x₀ _).le) P hm hK hφ r
  have hc : (∑ j, (c j)^2) ≤ N*h 0+4*N*(perturbationScale N)^2 := by
    have he := (Fintype.equivFin (EnrichedBlock N)).symm.sum_comp
      (fun j => |enrichedLevelCoefficient n h u 0 x₀ j|^2)
    change (∑ j, |enrichedLevelCoefficient n h u 0 x₀ ((Fintype.equivFin _).symm j)|^2) ≤ _
    rw [he]
    exact enrichedRoot_envelope_sq hN n hh h0 u hu x₀
  refine ⟨H.1, ?_⟩
  linarith [H.2]

abbrev EnrichedPoissonRoot (N : ℕ) (A : Type*) := ℕ × InfiniteRootData (EnrichedRootSize N) A

def enrichedPoissonBase {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (φ : A → Spin N → ℝ) (p : EnrichedPoissonRoot N A) : Spin N → ℝ :=
  enrichedBaseEnergy n h u φ (rootPrefix p.1 p.2)

lemma measurable_enrichedPoissonBase {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    Measurable (enrichedPoissonBase n h u φ) := by
  apply measurable_from_prod_countable_right
  intro M
  exact (measurable_enrichedBaseEnergy n h u hm).comp
    (measurable_fst.prodMk (Measurable.of_eval (fun index : Fin M =>
      (measurable_pi_apply (index : ℕ)).comp measurable_snd)))

def enrichedPoissonLog {N : ℕ} {A : Type*} (n : ℕ) (b h : ℕ → ℝ) (u : Fin N → ℝ)
    (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (p : EnrichedPoissonRoot N A × NoiseTree (Spin N → ℝ) n) : ℝ :=
  cascadeEnergyLog n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (enrichedPoissonBase n h u φ p.1) p.2 - N*h n/2

lemma enriched_poisson_unshifted {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := ((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))).prod
        (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
    let X := fun p : EnrichedPoissonRoot N A × NoiseTree (Spin N → ℝ) n =>
      cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1) p.2
    MemLp X 2 Q ∧ Var[X;Q] ≤
      4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := by
  have hr := enriched_poisson_root_variance hN n b (fun i hi => (hb.1 i hi).1) hh h0 u hu ν P hm hK hφ r
  have hv := cascadeEnergyLog_variance _ n b hb
    (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1))
    (measurable_enrichedPoissonBase n h u hm) hr.1
  refine ⟨hv.1, ?_⟩
  have hrv : Var[(fun p => energyRecursion n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (enrichedPoissonBase n h u φ p)); _] ≤ N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := hr.2
  linarith [hv.2,hrv]

theorem enriched_poisson_variance {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := ((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))).prod
        (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
    MemLp (enrichedPoissonLog n b h u ν φ) 2 Q ∧ Var[enrichedPoissonLog n b h u ν φ;Q] ≤
      4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := by
  exact memLp_variance_shift _
    (enriched_poisson_unshifted hN n b hb hh h0 u hu ν P hm hK hφ r) (N*h n/2)

lemma perturbationScale_le_one {N : ℕ} (hN : 0 < N) : perturbationScale N ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast hN
  · norm_num

lemma perturbationScale_nonneg (N : ℕ) : 0 ≤ perturbationScale N :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma field_cap_arithmetic {N : ℕ} (hN : 0 < N) {C H h₀ e K r α : ℝ}
    (hC : 0 ≤ C) (he : 0 ≤ e) (he1 : e ≤ 1) (hh : h₀ ≤ H)
    (hr : r ≤ α*N) :
    (C+N*h₀+4*N*e^2+5*K^2*r) / (N:ℝ)^2 ≤ (C+H+4+5*K^2*α)/N := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hc : C ≤ N*C := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hh hn.le
  have he' : 4*N*e^2 ≤ 4*N := by
    have : e^2 ≤ 1 := by nlinarith
    nlinarith
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ 5*K^2 by positivity)
  apply (div_le_iff₀ (sq_pos_of_pos hn)).2
  have hid : (C+H+4+5*K^2*α)/N*(N:ℝ)^2 = (C+H+4+5*K^2*α)*N := by
    field_simp
  rw [hid]
  nlinarith

lemma l1_center_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ ω, |X ω-∫ t, X t ∂P| ∂P) ≤ Real.sqrt (Var[X;P]) := by
  have hL := (hX.sub (memLp_const (∫ t, X t ∂P))).norm
  have hv := variance_nonneg (fun ω => |X ω-∫ t, X t ∂P|) P
  rw [variance_eq_sub (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using hL)] at hv
  have he : (∫ ω, |X ω-∫ t, X t ∂P|^2 ∂P) = Var[X;P] := by
    rw [variance_eq_integral hX.aemeasurable]
    simp only [sq_abs]
  simp only [Pi.pow_apply] at hv
  rw [he] at hv
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _)) (variance_nonneg X P)).2
    (by linarith)

theorem enriched_field_cap_variance {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := ((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))).prod
        (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
    let C := 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
    let X := fun p => enrichedPoissonLog n b h u ν φ p / N
    MemLp X 2 Q ∧ Var[X;Q] ≤ (C+H+4+5*K^2*α)/N := by
  have hv := enriched_poisson_variance hN n b hb hh h0 u hu ν P hm hK hφ r
  refine ⟨by simpa only [div_eq_mul_inv] using hv.1.mul_const ((N:ℝ)⁻¹), ?_⟩
  simp only [div_eq_mul_inv, variance_mul_const]
  have hh' : h 0 ≤ H := (hh (Nat.zero_le n)).trans hH
  have hc : 0 ≤ 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
    positivity
  have ha := field_cap_arithmetic hN hc (perturbationScale_nonneg N)
    (perturbationScale_le_one hN) hh' hr (K := K)
  have ha' : (4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +N*h 0+4*N*(perturbationScale N)^2+5*K^2*r)*(N:ℝ)⁻¹^2 ≤
      (4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +H+4+5*K^2*α)*(N:ℝ)⁻¹ := by
    simpa only [div_eq_mul_inv, inv_pow] using ha
  exact (mul_le_mul_of_nonneg_right hv.2 (sq_nonneg _)).trans ha'

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma labeled_terminal_integral (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z)))
    (ht : 0 < noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) ∧
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) < ∞)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    (∫ γ, Real.exp (noiseLeafTerminal n X u s (labeledNoiseLeaf A n (ω,z) γ))
      ∂labeledLeafLaw n ω) =
    ∫ v, Real.exp (noiseLeafTerminal n X u s v)
      ∂noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  rw [← labeledLeafLaw_noiseMap A n ω z hgood ht]
  exact (integral_map (measurable_of_countable _).aemeasurable
    (((measurable_noiseLeafTerminal n hX hu).comp
      (measurable_const.prodMk measurable_id)).exp.aestronglyMeasurable)).symm

lemma cascadeEnergyLog_eq_leaf_integral (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) (H : I → ℝ) :
    ∀ᵐ T ∂(noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)),
      cascadeEnergyLog n b μ ν H T =
      Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => finiteLogIntegral ν)
        (fun _ p => p.1 + p.2) H v) ∂noiseLeafKernel (I → ℝ) n T) := by
  have hfac := noiseTreeFactor_leafIntegral n b hb μ
    (X := fun _ => finiteLogIntegral ν) (u := fun _ p => p.1+p.2)
    (fun _ => measurable_finiteLogIntegral ν) (fun _ => measurable_fst.add measurable_snd) H
  have htot : ∀ᵐ T ∂(noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)),
      0 < noiseTreeTotal (I → ℝ) n T ∧ noiseTreeTotal (I → ℝ) n T < ∞ := by
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget (I → ℝ) n).aemeasurable
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  filter_upwards [hfac,htot] with T hfac ht
  simp only [noiseTreeFactor_terminal] at hfac
  unfold cascadeEnergyLog
  rw [hfac, ENNReal.toReal_mul]
  have ht0 : (noiseTreeTotal (I → ℝ) n T).toReal ≠ 0 :=
    (ENNReal.toReal_pos ht.1.ne' ht.2.ne).ne'
  rw [mul_div_cancel_left₀ _ ht0]
  congr 1
  exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun v => (Real.exp_pos _).le))
    (((measurable_noiseLeafTerminal n (fun _ => measurable_finiteLogIntegral ν)
      (fun _ => measurable_fst.add measurable_snd)).comp
        (measurable_const.prodMk measurable_id)).exp.aestronglyMeasurable)).symm

def labeledEnergy : (n : ℕ) → MarkForest (I → ℝ) n → LabeledLeaf n → (I → ℝ) → (I → ℝ)
  | 0, _, _, H => H
  | n+1, z, γ, H => labeledEnergy n (z γ.1.1 γ.1.2).2 γ.2 (H + (z γ.1.1 γ.1.2).1)

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma labeledEnergy_terminal (n : ℕ) (ω : LabeledTree n) (z : MarkForest (I → ℝ) n)
    (γ : LabeledLeaf n) (F : (I → ℝ) → ℝ) (H : I → ℝ) :
    noiseLeafTerminal n (fun _ => F) (fun _ p => p.1 + p.2) H
      (labeledNoiseLeaf (I → ℝ) n (ω,z) γ) = F (labeledEnergy n z γ H) := by
  induction n generalizing H with
  | zero => rfl
  | succ n ih => exact ih _ _ _ _

def labeledSpinReference (n : ℕ) (ν : Measure I) (ω : LabeledTree n) :
    Measure (I × LabeledLeaf n) := ν.prod (labeledLeafLaw n ω)

instance labeledSpinReference_probability (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν]
    (ω : LabeledTree n) : IsProbabilityMeasure (labeledSpinReference n ν ω) := by
  unfold labeledSpinReference
  infer_instance

def labeledEnergyLog (n : ℕ) (ν : Measure I) (H : I → ℝ)
    (p : LabeledTree n × MarkForest (I → ℝ) n) : ℝ :=
  Real.log (∫ s, Real.exp (labeledEnergy n p.2 s.2 H s.1)
    ∂labeledSpinReference n ν p.1)

lemma labeledEnergyLog_eq_leaf (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν]
    (H : I → ℝ) (p : LabeledTree n × MarkForest (I → ℝ) n) :
    labeledEnergyLog n ν H p = Real.log (∫ γ,
      Real.exp (finiteLogIntegral ν (labeledEnergy n p.2 γ H)) ∂labeledLeafLaw n p.1) := by
  have hE : Measurable (fun s : I × LabeledLeaf n => Real.exp (labeledEnergy n p.2 s.2 H s.1)) :=
    measurable_of_countable _
  have hF : Measurable (fun γ : LabeledLeaf n => Real.exp (finiteLogIntegral ν (labeledEnergy n p.2 γ H))) :=
    measurable_of_countable _
  unfold labeledEnergyLog labeledSpinReference
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => (Real.exp_pos _).le)) hE.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => (Real.exp_pos _).le)) hF.aestronglyMeasurable]
  congr 1
  rw [lintegral_prod _ hE.ennreal_ofReal.aemeasurable,
    lintegral_lintegral_swap hE.ennreal_ofReal.aemeasurable]
  apply lintegral_congr
  intro γ
  rw [finiteLogIntegral, Real.exp_log (MeasureTheory.integral_exp_pos Integrable.of_finite)]
  exact (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite (ae_of_all _ (fun _ => (Real.exp_pos _).le))).symm

theorem labeledEnergyLog_eq_cascade (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) [IsProbabilityMeasure ν] (H : I → ℝ) :
    ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (I → ℝ) n μ)),
      labeledEnergyLog n ν H p =
        cascadeEnergyLog n b μ ν H (labeledNoiseJoin (I → ℝ) n p) := by
  have hgood : ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw (I → ℝ) n μ)), GoodNoiseTree (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) := by
    apply ae_of_ae_map (measurable_labeledNoiseJoin (I → ℝ) n).aemeasurable
    rw [labeledNoiseJoin_law]
    exact noiseCascade_good (I → ℝ) n b hb μ
  have htot : ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw (I → ℝ) n μ)),
      0 < noiseTreeTotal (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) ∧
      noiseTreeTotal (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) < ∞ := by
    apply ae_of_ae_map (p := fun T : NoiseTree (I → ℝ) n =>
      0 < noiseTreeTotal (I → ℝ) n T ∧ noiseTreeTotal (I → ℝ) n T < ∞)
      (measurable_labeledNoiseJoin (I → ℝ) n).aemeasurable
    rw [labeledNoiseJoin_law]
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget (I → ℝ) n).aemeasurable
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  have he : ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw (I → ℝ) n μ)),
      cascadeEnergyLog n b μ ν H (labeledNoiseJoin (I → ℝ) n p) =
      Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => finiteLogIntegral ν)
        (fun _ p => p.1+p.2) H v) ∂noiseLeafKernel (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p)) := by
    apply ae_of_ae_map (p := fun T : NoiseTree (I → ℝ) n =>
      cascadeEnergyLog n b μ ν H T = Real.log (∫ v, Real.exp (noiseLeafTerminal n
        (fun _ => finiteLogIntegral ν) (fun _ p => p.1+p.2) H v) ∂noiseLeafKernel (I → ℝ) n T))
      (measurable_labeledNoiseJoin (I → ℝ) n).aemeasurable
    rw [labeledNoiseJoin_law]
    exact cascadeEnergyLog_eq_leaf_integral n b hb μ ν H
  filter_upwards [hgood,htot,he] with p hg ht he
  rw [he,labeledEnergyLog_eq_leaf]
  congr 1
  have hm := labeled_terminal_integral n p.1 p.2 hg ht
    (X := fun _ => finiteLogIntegral ν) (u := fun _ p => p.1+p.2)
    (fun _ => measurable_finiteLogIntegral ν) (fun _ => measurable_fst.add measurable_snd) H
  simpa only [labeledEnergy_terminal] using hm

end IsingPerceptron

namespace IsingPerceptron

def enrichedForestCoordinates (N n : ℕ) : Measure (ForestVertex n → Fin (EnrichedRootSize N) → ℝ) :=
  Measure.infinitePi (fun _ : ForestVertex n =>
    Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))

instance enrichedForestCoordinates_probability (N n : ℕ) :
    IsProbabilityMeasure (enrichedForestCoordinates N n) := by
  unfold enrichedForestCoordinates
  infer_instance

def enrichedForest (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (g : ForestVertex n → Fin (EnrichedRootSize N) → ℝ) : MarkForest (Spin N → ℝ) n :=
  markForestOfCoords (Spin N → ℝ) n
    (fun v => enrichedIncrement N n h u (forestVertexDepth n v+1) (g v))

lemma measurable_enrichedForest (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) :
    Measurable (enrichedForest N n h u) := by
  apply (measurable_markForestOfCoords (Spin N → ℝ) n).comp
  exact Measurable.of_eval (fun vertex =>
    (measurable_enrichedIncrement N n h u (forestVertexDepth n vertex+1)).comp (measurable_pi_apply vertex))

theorem enrichedForest_law (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) :
    (enrichedForestCoordinates N n).map (enrichedForest N n h u) =
      markForestLaw (Spin N → ℝ) n (fun i => enrichedIncrementLaw N n h u (i+1)) := by
  change (enrichedForestCoordinates N n).map
    ((markForestOfCoords (Spin N → ℝ) n) ∘
      (fun g v => enrichedIncrement N n h u (forestVertexDepth n v+1) (g v))) = _
  have hm : Measurable (fun g : ForestVertex n → Fin (EnrichedRootSize N) → ℝ =>
      fun v => enrichedIncrement N n h u (forestVertexDepth n v+1) (g v)) := by
    exact Measurable.of_eval (fun vertex =>
      (measurable_enrichedIncrement N n h u (forestVertexDepth n vertex+1)).comp (measurable_pi_apply vertex))
  rw [← Measure.map_map (measurable_markForestOfCoords (Spin N → ℝ) n) hm]
  unfold enrichedForestCoordinates
  rw [Measure.infinitePi_map_pi _ (fun v => measurable_enrichedIncrement N n h u (forestVertexDepth n v+1))]
  exact markForestOfCoords_law (Spin N → ℝ) n (fun i => enrichedIncrementLaw N n h u (i+1))

theorem labeledEnrichedCoordinates_law (N n : ℕ) (b h : ℕ → ℝ) (u : Fin N → ℝ) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (enrichedForestCoordinates N n)).map
      (fun p => labeledNoiseJoin (Spin N → ℝ) n (p.1,enrichedForest N n h u p.2)) =
      noiseCascadeLaw (Spin N → ℝ) n b (fun i => enrichedIncrementLaw N n h u (i+1)) := by
  have hp := (MeasurePreserving.id (labeledCascadeLaw n b : Measure (LabeledTree n))).prod
    (show MeasurePreserving (enrichedForest N n h u) (enrichedForestCoordinates N n)
      (markForestLaw (Spin N → ℝ) n (fun i => enrichedIncrementLaw N n h u (i+1))) from
        ⟨measurable_enrichedForest N n h u, enrichedForest_law N n h u⟩)
  change _ = _
  rw [show (fun p => labeledNoiseJoin (Spin N → ℝ) n (p.1,enrichedForest N n h u p.2)) =
    (labeledNoiseJoin (Spin N → ℝ) n) ∘ Prod.map id (enrichedForest N n h u) from rfl,
    ← Measure.map_map (measurable_labeledNoiseJoin (Spin N → ℝ) n) hp.measurable,
    hp.map_eq, labeledNoiseJoin_law]

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_labeledEnergy (n : ℕ) (γ : LabeledLeaf n) :
    Measurable (fun p : MarkForest (I → ℝ) n × (I → ℝ) => labeledEnergy n p.1 γ p.2) := by
  induction n with
  | zero => exact measurable_snd
  | succ n ih =>
    exact (ih γ.2).comp (show Measurable (fun p : MarkForest (I → ℝ) (n+1) × (I → ℝ) =>
      ((p.1 γ.1.1 γ.1.2).2,p.2+(p.1 γ.1.1 γ.1.2).1)) from by fun_prop)

lemma measurable_labeledEnergyLog (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν] :
    Measurable (fun p : (I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n) =>
      labeledEnergyLog n ν p.1 p.2) := by
  let κ : Kernel ((I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n)) (LabeledLeaf n) :=
    ⟨fun p => labeledLeafLaw n p.2.1,(measurable_labeledLeafLaw n).comp (by fun_prop)⟩
  have : IsMarkovKernel κ := ⟨fun _ => labeledLeafLaw_probability _ _⟩
  have hm : Measurable (fun p : ((I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n)) × LabeledLeaf n =>
      Real.exp (finiteLogIntegral ν (labeledEnergy n p.1.2.2 p.2 p.1.1))) := by
    apply measurable_swap_iff.mp
    apply measurable_from_prod_countable_right
    intro γ
    exact ((measurable_finiteLogIntegral ν).comp
      ((measurable_labeledEnergy n γ).comp
        (show Measurable (fun p : (I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n) =>
          (p.2.2,p.1)) from by fun_prop))).exp
  simpa only [labeledEnergyLog_eq_leaf, κ, Kernel.coe_mk] using
    (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.log

theorem labeledEnergyLog_eq_cascade_random {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    {H : Ω → I → ℝ} (hmH : Measurable H) :
    ∀ᵐ p ∂P.prod ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw (I → ℝ) n μ)),
      labeledEnergyLog n ν (H p.1) p.2 =
        cascadeEnergyLog n b μ ν (H p.1) (labeledNoiseJoin (I → ℝ) n p.2) := by
  have hbase : Measurable (fun p : Ω × (LabeledTree n × MarkForest (I → ℝ) n) =>
      (H p.1,p.2)) := (hmH.comp measurable_fst).prodMk measurable_snd
  have hjoin : Measurable (fun p : Ω × (LabeledTree n × MarkForest (I → ℝ) n) =>
      (H p.1,labeledNoiseJoin (I → ℝ) n p.2)) :=
    (hmH.comp measurable_fst).prodMk ((measurable_labeledNoiseJoin (I → ℝ) n).comp measurable_snd)
  have hl := (measurable_labeledEnergyLog n ν).comp hbase
  have hr := (measurable_cascadeEnergyLog n b μ ν).comp hjoin
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hl hr)).mpr
    (ae_of_all _ (fun ω => labeledEnergyLog_eq_cascade n b hb μ ν (H ω)))

end IsingPerceptron

end

end OAI
