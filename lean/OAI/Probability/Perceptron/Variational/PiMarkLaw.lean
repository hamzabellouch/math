import Mathlib
import OAI.Probability.Perceptron.Variational.ProductMarkLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy

def piMarkLaw {ι S : Type} [Fintype ι] [MeasurableSpace S]
    (ν : ι → ProbabilityMeasure S) : ProbabilityMeasure (ι → S) :=
  ⟨Measure.pi (fun i => (ν i : Measure S)),inferInstance⟩

lemma fractional_log_moment_sum_pi {ι S : Type} [Fintype ι] [MeasurableSpace S]
    (ν : ι → ProbabilityMeasure S) (b : ℝ) (f : ι → S → ℝ)
    (hI : ∀ i, Integrable (fun s => Real.exp (b*f i s)) (ν i)) :
    (Integrable (fun s : ι → S => Real.exp (b*∑ i, f i (s i))) (piMarkLaw ν)) ∧
    Real.log (∫ s, Real.exp (b*∑ i, f i (s i)) ∂(piMarkLaw ν : Measure (ι → S)))/b =
      ∑ i, Real.log (∫ s, Real.exp (b*f i s) ∂(ν i : Measure S))/b := by
  simp_rw [Finset.mul_sum,Real.exp_sum]
  constructor
  · exact Integrable.fintype_prod hI
  · change Real.log (∫ s, ∏ i, Real.exp (b*f i (s i)) ∂Measure.pi (fun i => (ν i : Measure S)))/b = _
    rw [integral_fintype_prod_eq_prod (fun i s => Real.exp (b*f i s)),Real.log_prod (fun i _ => (integral_exp_pos (hI i)).ne'),Finset.sum_div]

theorem finiteCascade_sum_pi {ι X S : Type} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace S]
    (ν : ι → ProbabilityMeasure S) (step : ι → X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (H : ι → X → ℝ)
    (hI : ∀ i, finiteCascadeFractionalIntegrable (ν i) (step i) (H i) n z) :
    (∀ x, finiteCascadeLogRecursion (piMarkLaw ν)
      (fun p : (ι → X)×(ι → S) => fun i => step i (p.1 i,p.2 i)) n z
        (fun x => ∑ i, H i (x i)) x =
      ∑ i, finiteCascadeLogRecursion (ν i) (step i) n z (H i) (x i)) ∧
    finiteCascadeFractionalIntegrable (piMarkLaw ν)
      (fun p : (ι → X)×(ι → S) => fun i => step i (p.1 i,p.2 i))
        (fun x => ∑ i, H i (x i)) n z := by
  induction n with
  | zero => exact ⟨fun _ => rfl,trivial⟩
  | succ n ih =>
    obtain ⟨heq,htail⟩ := ih (fun j => z j.succ) (fun i => (hI i).2)
    constructor
    · intro x
      conv_lhs => rw [finiteCascadeLogRecursion]
      unfold fractionalLogMoment
      simp_rw [heq]
      exact (fractional_log_moment_sum_pi ν (z 0)
        (fun i s => finiteCascadeLogRecursion (ν i) (step i) n (fun j => z j.succ) (H i) (step i (x i,s)))
        (fun i => (hI i).1 (x i))).2
    · refine ⟨?_,htail⟩
      intro x
      simp_rw [heq]
      exact (fractional_log_moment_sum_pi ν (z 0)
        (fun i s => finiteCascadeLogRecursion (ν i) (step i) n (fun j => z j.succ) (H i) (step i (x i,s)))
        (fun i => (hI i).1 (x i))).1

theorem finiteCascade_quadratic_coordinates (d : ℕ) (σ : ℕ → ℝ) (b : ℝ) (c : Fin d → ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    (hp : 0 < quadraticCascadePrecision σ b n z) :
    (∀ x, finiteCascadeLogRecursion (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (fun p : (Fin d → ℕ → ℝ)×(Fin d → ℝ) => fun i => gaussianShiftStep σ (p.1 i,p.2 i)) n z
        (fun x => ∑ i, (c i+(x i 0)^2/(2*b))) x =
      (∑ i, c i) + d*quadraticCascadeOffset σ b n z+
        (∑ i, (x i n)^2)/(2*quadraticCascadePrecision σ b n z)) ∧
    finiteCascadeFractionalIntegrable (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (fun p : (Fin d → ℕ → ℝ)×(Fin d → ℝ) => fun i => gaussianShiftStep σ (p.1 i,p.2 i))
        (fun x => ∑ i, (c i+(x i 0)^2/(2*b))) n z := by
  have hq := finiteCascade_sum_pi (fun _ : Fin d => standardGaussianMark)
    (fun _ => gaussianShiftStep σ) n z (fun i x => c i+(x 0)^2/(2*b))
    (fun i => (finiteCascade_quadratic_recursion σ b (c i) n z hz hp).2)
  refine ⟨?_,hq.2⟩
  intro x
  rw [hq.1]
  simp_rw [(finiteCascade_quadratic_recursion σ b _ n z hz hp).1]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_div]

def canonicalCoordinateStep (d : ℕ) (σ : ℕ → ℝ) :
    (Fin d → ℕ → ℝ)×(Fin d → ℝ) → (Fin d → ℕ → ℝ) :=
  fun p i => gaussianShiftStep σ (p.1 i,p.2 i)

lemma canonicalCoordinateStep_measurable (d : ℕ) (σ : ℕ → ℝ) :
    Measurable (canonicalCoordinateStep d σ) := by
  apply Measurable.of_eval
  intro i
  exact (gaussianShiftStep_measurable σ).comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))

def canonicalCoordinatePotential (d : ℕ) (b : ℝ) (x : Fin d → ℕ → ℝ) : ℝ :=
  ∑ i, (-Real.log b/2+(x i 0)^2/(2*b))

lemma canonicalCoordinatePotential_measurable (d : ℕ) (b : ℝ) :
    Measurable (canonicalCoordinatePotential d b) := by unfold canonicalCoordinatePotential; fun_prop

lemma canonical_coordinate_spin_log (d : ℕ) {b : ℝ} (hb : 0 < b) (u : Fin d → ℝ) :
    Real.log (∫ y : Fin d → ℝ, Real.exp ((1-b)*(∑ i, (y i)^2)/2+∑ i, u i*y i)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
        ∑ i, (-Real.log b/2+(u i)^2/(2*b)) := by
  have he : (fun y : Fin d → ℝ => Real.exp ((1-b)*(∑ i, (y i)^2)/2+∑ i, u i*y i)) =
      (fun y => ∏ i, Real.exp ((1-b)*(y i)^2/2+u i*y i)) := by
    funext y
    rw [← Real.exp_sum]
    congr 1
    simp only [Finset.sum_add_distrib,Finset.sum_div,Finset.mul_sum]
  rw [he,integral_fintype_prod_eq_prod (fun i y => Real.exp ((1-b)*y^2/2+u i*y))]
  rw [Real.log_prod (fun i _ => (integral_exp_pos (canonical_scalar_integrable hb (u i))).ne')]
  simp_rw [canonical_scalar_log hb]

def canonicalCoordinateLog (d n : ℕ) (σ : ℕ → ℝ) (b : ℝ)
    (p : (Fin d → ℕ → ℝ)×DecoratedCascade (Fin d → ℝ) n) : ℝ :=
  Real.log (decoratedTerminalTotal (canonicalCoordinateStep d σ) (canonicalCoordinatePotential d b) n p /
    decoratedTerminalTotal (canonicalCoordinateStep d σ) (fun _ => 0) n p)

lemma canonical_coordinate_recursion (d : ℕ) (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    (hp : 0 < quadraticCascadePrecision σ b n z) :
    (∀ x, finiteCascadeLogRecursion (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (canonicalCoordinateStep d σ) n z (canonicalCoordinatePotential d b) x =
      d*(-Real.log b/2+quadraticCascadeOffset σ b n z)+
        (∑ i, (x i n)^2)/(2*quadraticCascadePrecision σ b n z)) ∧
    finiteCascadeFractionalIntegrable (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (canonicalCoordinateStep d σ) (canonicalCoordinatePotential d b) n z := by
  have he := finiteCascade_quadratic_coordinates d σ b (fun _ => -Real.log b/2) n z hz hp
  refine ⟨?_,he.2⟩
  intro x
  unfold canonicalCoordinateStep canonicalCoordinatePotential
  rw [he.1]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_add]

theorem canonical_coordinate_log_mean (d : ℕ) (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (x : Fin d → ℕ → ℝ) :
    (∫ η, canonicalCoordinateLog d n σ b (x,η)
      ∂decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z) =
      d*(-Real.log b/2+quadraticCascadeOffset σ b n z)+
        (∑ i, (x i n)^2)/(2*quadraticCascadePrecision σ b n z) := by
  unfold canonicalCoordinateLog
  rw [finiteCascade_terminal_log_recursion_of_fractional _ _ (canonicalCoordinateStep_measurable d σ)
    n z hz hz0 hz1 (canonicalCoordinatePotential_measurable d b)
    (canonical_coordinate_recursion d σ b n z hz0 hp).2]
  exact (canonical_coordinate_recursion d σ b n z hz0 hp).1 x

lemma canonical_coordinate_log_deviation_le (d : ℕ) (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (x : Fin d → ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
      Measure (DecoratedCascade (Fin d → ℝ) n))
      {η | ε ≤ |canonicalCoordinateLog d n σ b (x,η)-
        (d*(-Real.log b/2+quadraticCascadeOffset σ b n z)+
          (∑ i, (x i n)^2)/(2*quadraticCascadePrecision σ b n z))|} ≤
      ENNReal.ofReal (cascadeLogFluctuationConstant n z/ε^2) := by
  have he := finiteCascade_terminal_log_deviation_le _ _ (canonicalCoordinateStep_measurable d σ)
    n z hz hz0 hz1 (canonicalCoordinatePotential_measurable d b)
    (canonical_coordinate_recursion d σ b n z hz0 hp).2 x hε
  rw [(canonical_coordinate_recursion d σ b n z hz0 hp).1 x] at he
  exact he

lemma gaussian_square_memLp_two (r : ℝ≥0) : MemLp (fun y : ℝ => y^2) 2 (gaussianReal 0 r) := by
  have : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
    apply (ENNReal.holderTriple_coe_iff (p := 4) (q := 4) (r := 2) (by norm_num)).mpr
    norm_num [NNReal.holderTriple_iff]
  have h4 : MemLp (fun y : ℝ => y) (4 : ℝ≥0∞) (gaussianReal 0 r) := memLp_id_gaussianReal 4
  have hm : MemLp (fun y : ℝ => y*y) 2 (gaussianReal 0 r) :=
    h4.mul h4
  simpa [pow_two] using hm

lemma gaussian_square_mean (r : ℝ≥0) : (∫ y, y^2 ∂gaussianReal 0 r) = r := by
  have he := variance_fun_id_gaussianReal (μ := 0) (v := r)
  rw [variance_eq_integral (by fun_prop : AEMeasurable (fun x : ℝ => x) (gaussianReal 0 r))] at he
  simpa only [integral_id_gaussianReal,sub_zero] using he

lemma gaussian_square_sum_memLp_two (d : ℕ) (r : ℝ≥0) :
    MemLp (fun y : Fin d → ℝ => ∑ i, (y i)^2) 2 (Measure.pi (fun _ => gaussianReal 0 r)) := by
  exact memLp_finsetSum _ (fun i _ => (gaussian_square_memLp_two r).comp_measurePreserving (measurePreserving_eval _ i))

lemma gaussian_square_sum_mean (d : ℕ) (r : ℝ≥0) :
    (∫ y : Fin d → ℝ, ∑ i, (y i)^2 ∂Measure.pi (fun _ => gaussianReal 0 r)) = d*r := by
  have hi : ∀ i : Fin d, Integrable (fun y : Fin d → ℝ => (y i)^2) (Measure.pi (fun _ => gaussianReal 0 r)) :=
    fun i => ((gaussian_square_memLp_two r).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 r) i)).integrable (by norm_num)
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  have hj : ∀ i : Fin d, (∫ y : Fin d → ℝ, (y i)^2 ∂Measure.pi (fun _ => gaussianReal 0 r)) = r := by
    intro i
    rw [integral_comp_eval (μ := fun _ : Fin d => gaussianReal 0 r) (i := i) (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y^2) (gaussianReal 0 r))]
    exact gaussian_square_mean r
  simp_rw [hj]
  simp

lemma gaussian_square_sum_variance (d : ℕ) (r : ℝ≥0) :
    variance (fun y : Fin d → ℝ => ∑ i, (y i)^2) (Measure.pi (fun _ => gaussianReal 0 r)) =
      d*variance (fun y : ℝ => y^2) (gaussianReal 0 r) := by
  have he := variance_sum_pi (μ := fun _ : Fin d => gaussianReal 0 r) (fun _ => gaussian_square_memLp_two r)
  have hs : (∑ i : Fin d, fun ω : Fin d → ℝ => (ω i)^2) = (fun ω => ∑ i, (ω i)^2) := by ext ω; simp
  rw [hs] at he
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using he

lemma gaussian_square_average_deviation_le (d : ℕ) (hd : 0 < d) (r : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 r))
      {y | ε ≤ |(∑ i, (y i)^2)/(d : ℝ)-r|} ≤
      ENNReal.ofReal (variance (fun y : ℝ => y^2) (gaussianReal 0 r)/(d*ε^2)) := by
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hc := meas_ge_le_variance_div_sq (gaussian_square_sum_memLp_two d r) (mul_pos hε hd')
  rw [gaussian_square_sum_mean,gaussian_square_sum_variance] at hc
  have hset : {y : Fin d → ℝ | ε ≤ |(∑ i, (y i)^2)/(d : ℝ)-r|} =
      {y | ε*(d : ℝ) ≤ |(∑ i, (y i)^2)-(d : ℝ)*r|} := by
    ext y
    have he : (∑ i, (y i)^2)/(d : ℝ)-r = ((∑ i, (y i)^2)-(d : ℝ)*r)/(d : ℝ) := by field_simp
    simp only [Set.mem_ofPred_eq,he,abs_div,abs_of_pos hd']
    exact le_div_iff₀ hd'
  rw [hset]
  convert hc using 2
  field_simp [hd'.ne',hε.ne']

lemma decoratedTerminalTotal_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step) {H : X → ℝ}
    (hH : Measurable H) (n : ℕ) (z : Fin n → ℝ) : Measurable (decoratedTerminalTotal step H n) := by
  have he : decoratedTerminalTotal step H n = fun p =>
      Real.exp (finiteCascadeLogRecursion ν step n z H p.1) *
        decoratedWeightedTotal step n (finiteCascadeShifts ν step n z H) p := by
    funext p
    exact decoratedTerminalTotal_telescoping ν step H n z p
  rw [he]
  exact (((finiteCascadeLogRecursion_measurable ν step hs n z hH).comp measurable_fst).exp).mul
    (decoratedWeightedTotalE_measurable step hs n _ (finiteCascadeShifts_measurable ν step hs n z hH)).ennreal_toReal

lemma canonicalCoordinateLog_measurable (d n : ℕ) (σ : ℕ → ℝ) (b : ℝ) (z : Fin n → ℝ) :
    Measurable (canonicalCoordinateLog d n σ b) := by
  exact ((decoratedTerminalTotal_measurable (piMarkLaw (fun _ : Fin d => standardGaussianMark)) _
    (canonicalCoordinateStep_measurable d σ) (canonicalCoordinatePotential_measurable d b) n z).div
    (decoratedTerminalTotal_measurable (piMarkLaw (fun _ : Fin d => standardGaussianMark)) _
      (canonicalCoordinateStep_measurable d σ) measurable_const n z)).log

lemma product_deviation_le {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : X×Y → ℝ} {G : X → ℝ} (hF : Measurable F) (hG : Measurable G)
    (c ε : ℝ) (A : ℝ≥0∞)
    (hbound : ∀ x, ν {y | ε/2 ≤ |F (x,y)-G x|} ≤ A) :
    μ.prod ν {p | ε ≤ |F p-c|} ≤ A+μ {x | ε/2 ≤ |G x-c|} := by
  have hsub : {p : X×Y | ε ≤ |F p-c|} ⊆
      {p | ε/2 ≤ |F p-G p.1|} ∪ {p | ε/2 ≤ |G p.1-c|} := by
    intro p hp
    by_contra hh
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_le] at hh
    have ht := abs_sub_le (F p) (G p.1) c
    dsimp only [Set.mem_ofPred_eq] at hp
    linarith
  have hA : μ.prod ν {p : X×Y | ε/2 ≤ |F p-G p.1|} ≤ A := by
    rw [Measure.prod_apply (by measurability)]
    calc
      _ ≤ ∫⁻ _ : X, A ∂μ := lintegral_mono hbound
      _ = A := by simp
  have hB : μ.prod ν {p : X×Y | ε/2 ≤ |G p.1-c|} = μ {x | ε/2 ≤ |G x-c|} := by
    have hs : {p : X×Y | ε/2 ≤ |G p.1-c|} = {x | ε/2 ≤ |G x-c|} ×ˢ Set.univ := by ext p; simp
    rw [hs,Measure.prod_prod]
    simp
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (by rw [hB]; exact add_le_add hA le_rfl))

theorem canonical_coordinate_joint_deviation_le (d : ℕ) (hd : 0 < d) (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (r : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ((Measure.pi (fun _ : Fin d => gaussianReal 0 r)).prod
      (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
        Measure (DecoratedCascade (Fin d → ℝ) n)))
      {p | ε*(d : ℝ) ≤ |canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)-
        d*canonicalGaussianFreeValue σ n z r b|} ≤
      ENNReal.ofReal (cascadeLogFluctuationConstant n z/(ε*d/2)^2)+
        ENNReal.ofReal (variance (fun y : ℝ => y^2) (gaussianReal 0 r)/
          (d*(ε*quadraticCascadePrecision σ b n z)^2)) := by
  let P := quadraticCascadePrecision σ b n z
  let a := -Real.log b/2+quadraticCascadeOffset σ b n z
  let G := fun y : Fin d → ℝ => (d : ℝ)*a+(∑ i, (y i)^2)/(2*P)
  let F := fun p : (Fin d → ℝ)×DecoratedCascade (Fin d → ℝ) n =>
    canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)
  have hP : 0 < P := hp
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hF : Measurable F := (canonicalCoordinateLog_measurable d n σ b z).comp (by fun_prop)
  have hG : Measurable G := by dsimp [G]; fun_prop
  have hc := product_deviation_le (Measure.pi (fun _ : Fin d => gaussianReal 0 r))
    (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
        Measure (DecoratedCascade (Fin d → ℝ) n)) hF hG
    (d*canonicalGaussianFreeValue σ n z r b) (ε*d)
    (ENNReal.ofReal (cascadeLogFluctuationConstant n z/(ε*d/2)^2))
    (fun y => canonical_coordinate_log_deviation_le d σ b n z hz hz0 hz1 hp
      (fun i _ => y i) (half_pos (mul_pos hε hd')))
  apply hc.trans
  apply add_le_add le_rfl
  have hset : {y : Fin d → ℝ | ε*(d : ℝ)/2 ≤ |G y-d*canonicalGaussianFreeValue σ n z r b|} =
      {y | ε*P ≤ |(∑ i, (y i)^2)/(d : ℝ)-r|} := by
    ext y
    have he : G y-d*canonicalGaussianFreeValue σ n z r b =
        ((d : ℝ)/(2*P))*((∑ i, (y i)^2)/(d : ℝ)-r) := by
      dsimp [G,a,canonicalGaussianFreeValue]
      change (d : ℝ)*(-Real.log b/2+quadraticCascadeOffset σ b n z)+
        (∑ i, (y i)^2)/(2*P)-d*(-Real.log b/2+quadraticCascadeOffset σ b n z+r/(2*P)) = _
      field_simp [hd'.ne',hP.ne']
      ring
    have hf : 0 < (d : ℝ)/(2*P) := by positivity
    simp only [Set.mem_ofPred_eq,he,abs_mul,abs_of_pos hf]
    rw [mul_comm ((d : ℝ)/(2*P)),←div_le_iff₀ hf]
    field_simp [hd'.ne',hP.ne']
  rw [hset]
  exact gaussian_square_average_deviation_le d hd r (mul_pos hε hP)

theorem canonical_coordinate_converges (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (r : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun d : ℕ =>
      ((Measure.pi (fun _ : Fin d => gaussianReal 0 r)).prod
        (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
          Measure (DecoratedCascade (Fin d → ℝ) n)))
        {p | ε*(d : ℝ) ≤ |canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)-
          d*canonicalGaussianFreeValue σ n z r b|}) atTop (𝓝 0) := by
  have hd : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun d : ℕ => (ε*(d : ℝ)/2)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      ((hd.const_mul_atTop hε).atTop_div_const (by norm_num))
  have hu : Tendsto (fun d : ℕ => (d : ℝ)*(ε*quadraticCascadePrecision σ b n z)^2) atTop atTop :=
    hd.atTop_mul_const (sq_pos_of_pos (mul_pos hε hp))
  have ht0 : Tendsto (fun d : ℕ => cascadeLogFluctuationConstant n z/(ε*(d : ℝ)/2)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  have hu0 : Tendsto (fun d : ℕ => variance (fun y : ℝ => y^2) (gaussianReal 0 r)/
      ((d : ℝ)*(ε*quadraticCascadePrecision σ b n z)^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hu
  have hsum : Tendsto (fun d : ℕ => ENNReal.ofReal (cascadeLogFluctuationConstant n z/(ε*(d : ℝ)/2)^2)+
      ENNReal.ofReal (variance (fun y : ℝ => y^2) (gaussianReal 0 r)/
        ((d : ℝ)*(ε*quadraticCascadePrecision σ b n z)^2))) atTop (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal ht0).add (ENNReal.tendsto_ofReal hu0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [eventually_gt_atTop 0] with d hdpos
    exact canonical_coordinate_joint_deviation_le d hdpos σ b n z hz hz0 hz1 hp r hε

lemma exponential_ratio_converges {Ω : ℕ → Type} [∀ d, MeasurableSpace (Ω d)] (μ : ∀ d, Measure (Ω d))
    (X Y : ∀ d, Ω d → ℝ) (x y a : ℝ) (hrate : y-x < a)
    (hX : ∀ ε > 0, Tendsto (fun d => μ d {p | ε*(d : ℝ) ≤ |X d p-d*x|}) atTop (𝓝 0))
    (hY : ∀ ε > 0, Tendsto (fun d => μ d {p | ε*(d : ℝ) ≤ |Y d p-d*y|}) atTop (𝓝 0))
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun d => μ d {p | ρ ≤ Real.exp (Y d p-X d p-(d : ℝ)*a)}) atTop (𝓝 0) := by
  let ε := (a-(y-x))/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have ht : Tendsto (fun d : ℕ => ε*(d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hε
  have he : ∀ᶠ d : ℕ in atTop, -Real.log ρ < ε*(d : ℝ) := ht.eventually (eventually_gt_atTop _)
  have hb : ∀ᶠ d : ℕ in atTop,
      μ d {p | ρ ≤ Real.exp (Y d p-X d p-(d : ℝ)*a)} ≤
        μ d {p | ε*(d : ℝ) ≤ |X d p-d*x|}+μ d {p | ε*(d : ℝ) ≤ |Y d p-d*y|} := by
    filter_upwards [he,eventually_gt_atTop 0] with d hd hdpos
    apply le_trans (measure_mono (t :=
      {p | ε*(d : ℝ) ≤ |X d p-d*x|} ∪ {p | ε*(d : ℝ) ≤ |Y d p-d*y|}) ?_) (measure_union_le _ _)
    intro p hp
    by_contra hh
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_le] at hh
    have hx := (abs_lt.mp hh.1).1
    have hy := (abs_lt.mp hh.2).2
    have hp' : Real.log ρ ≤ Y d p-X d p-(d : ℝ)*a := by
      simpa only [Real.log_exp] using Real.log_le_log hρ hp
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
    have ha : a = y-x+4*ε := by dsimp [ε]; ring
    rw [ha] at hp'
    nlinarith
  have hs := (hX ε hε).add (hY ε hε)
  simp only [add_zero] at hs
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
    (Eventually.of_forall (fun _ => bot_le)) hb

theorem canonical_ratio_converges (σ : ℕ → ℝ) (b b' a : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z)
    (hp' : 0 < quadraticCascadePrecision σ b' n z) (r : ℝ≥0)
    (hrate : canonicalGaussianFreeValue σ n z r b'-canonicalGaussianFreeValue σ n z r b < a)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun d : ℕ =>
      ((Measure.pi (fun _ : Fin d => gaussianReal 0 r)).prod
        (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
          Measure (DecoratedCascade (Fin d → ℝ) n)))
        {p | ρ ≤ Real.exp
          (canonicalCoordinateLog d n σ b' ((fun i _ => p.1 i),p.2)-
            canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)-(d : ℝ)*a)}) atTop (𝓝 0) := by
  apply exponential_ratio_converges _ _ _ _ _ _ hrate
  · exact fun ε hε => canonical_coordinate_converges σ b n z hz hz0 hz1 hp r hε
  · exact fun ε hε => canonical_coordinate_converges σ b' n z hz hz0 hz1 hp' r hε
  · exact hρ

lemma canonical_stationary_tail_rates (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (r b : ℝ) (hp : 0 < quadraticCascadePrecision σ b n z)
    (hstat : -1/(2*b)+quadraticCascadeReciprocalSlope σ b n z-
      r/(2*(quadraticCascadePrecision σ b n z)^2) = -1/2)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧
      0 < quadraticCascadePrecision σ (b-δ) n z ∧
      0 < quadraticCascadePrecision σ (b+δ) n z ∧
      canonicalGaussianFreeValue σ n z r (b-δ)-canonicalGaussianFreeValue σ n z r b < δ*(1+ε)/2 ∧
      canonicalGaussianFreeValue σ n z r (b+δ)-canonicalGaussianFreeValue σ n z r b < -δ*(1-ε)/2 := by
  let C := canonicalGaussianFreeValue σ n z r
  have hf : HasDerivAt C (-1/2) b := by
    simpa only [hstat] using canonicalGaussianFreeValue_hasDerivAt σ n z hz r hp
  have hlin := hf.isLittleO.def (by positivity : 0 < ε/4)
  have hpos : ∀ᶠ t in 𝓝 b, 0 < quadraticCascadePrecision σ t n z :=
    (quadraticCascadePrecision_hasDerivAt σ n z b).continuousAt.eventually (eventually_gt_nhds hp)
  obtain ⟨η,hη,hboth⟩ := Metric.eventually_nhds_iff.mp (hlin.and hpos)
  let δ := η/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdη : δ < η := by dsimp [δ]; linarith
  have hleft : dist (b-δ) b < η := by simpa [Real.dist_eq,abs_of_nonneg hδ.le] using hdη
  have hright : dist (b+δ) b < η := by simpa [Real.dist_eq,abs_of_nonneg hδ.le] using hdη
  obtain ⟨hl,hlp⟩ := hboth hleft
  obtain ⟨hr,hrp⟩ := hboth hright
  simp only [Real.norm_eq_abs,smul_eq_mul] at hl hr
  have hdl : b-δ-b = -δ := by ring
  have hdr : b+δ-b = δ := by ring
  rw [hdl,abs_neg,abs_of_pos hδ] at hl
  rw [hdr,abs_of_pos hδ] at hr
  refine ⟨δ,hδ,hlp,hrp,?_,?_⟩
  · have := (abs_le.mp hl).2
    dsimp only [C] at this
    nlinarith [mul_pos hε hδ]
  · have := (abs_le.mp hr).2
    dsimp only [C] at this
    nlinarith [mul_pos hε hδ]

end SphericalPerceptronFreeEnergy

end

end OAI
