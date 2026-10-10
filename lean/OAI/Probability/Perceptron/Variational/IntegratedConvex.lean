import Mathlib
import OAI.Probability.Perceptron.Interpolation.KernelReplicaGibbs
import OAI.Probability.Perceptron.Pressure.GaussianPressureDerivative

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma convex_derivative_monotone {A a : ℝ→ℝ} (hc : ConvexOn ℝ univ A)
    (hd : ∀ u, HasDerivAt A (a u) u) : Monotone a := by
  intro x y hxy
  simpa only [(hd x).deriv,(hd y).deriv] using
    hc.monotoneOn_deriv (fun x _ => (hd x).differentiableAt) (mem_univ x) (mem_univ y) hxy

lemma integral_convex_derivative_fluctuation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Ω→ℝ→ℝ} {A a : ℝ→ℝ}
    {D : Ω→ℝ} {u s δ : ℝ} (hs : 0<s)
    (hD : AEStronglyMeasurable D P)
    (hF : ∀ᵐ ω ∂P, ConvexOn ℝ univ (F ω) ∧ HasDerivAt (F ω) (D ω) u)
    (hA : ConvexOn ℝ univ A) (ha : ∀ x, HasDerivAt A (a x) x)
    (hi : ∀ x ∈ Icc (u-s) (u+s), Integrable (fun ω => F ω x) P)
    (hb : ∀ x ∈ Icc (u-s) (u+s), (∫ ω, |F ω x-A x| ∂P)≤ δ) :
    (∫ ω, |D ω-a u| ∂P) ≤ a (u+s)-a (u-s)+4*δ/s := by
  have hm := convex_derivative_monotone hA ha
  have hp := hA.slope_le_of_hasDerivAt (mem_univ u) (mem_univ (u+s))
    (by linarith : u<u+s) (ha (u+s))
  have hn := hA.le_slope_of_hasDerivAt (mem_univ (u-s)) (mem_univ u)
    (by linarith : u-s<u) (ha (u-s))
  have he1 : u+s-u=s := by ring
  have he2 : u-(u-s)=s := by ring
  simp only [slope,he1,he2,smul_eq_mul,vsub_eq_sub] at hp hn
  have hp' : A (u+s)-A u≤ s*a (u+s) := by
    have := (div_le_iff₀ hs).mp (show (A (u+s)-A u)/s≤ a (u+s) by simpa [div_eq_mul_inv,mul_comm] using hp)
    linarith
  have hn' : s*a (u-s)≤A u-A (u-s) := by
    have := (le_div_iff₀ hs).mp (show a (u-s)≤(A u-A (u-s))/s by simpa [div_eq_mul_inv,mul_comm] using hn)
    linarith
  have he : ((a (u+s)-a (u-s))/s)*s^2=(a (u+s)-a (u-s))*s := by field_simp [ne_of_gt hs]
  have hp'' : A (u+s)-A u-s*a u≤((a (u+s)-a (u-s))/s)*s^2 := by
    rw [he]; nlinarith [hm (show u-s≤u by linarith)]
  have hn'' : A (u-s)-A u+s*a u≤((a (u+s)-a (u-s))/s)*s^2 := by
    rw [he]; nlinarith [hm (show u≤u+s by linarith)]
  have hh := integral_convex_contact_bound P hs hD hF hp'' hn''
    (hi (u+s) (by constructor <;> linarith)) (hi u (by constructor <;> linarith))
    (hi (u-s) (by constructor <;> linarith))
    (hb (u+s) (by constructor <;> linarith)) (hb u (by constructor <;> linarith))
    (hb (u-s) (by constructor <;> linarith))
  simpa only [div_mul_cancel₀ _ (ne_of_gt hs)] using hh

lemma convex_integrated_derivative_shift {A a : ℝ→ℝ}
    (hc : ConvexOn ℝ univ A) (hd : ∀ u, HasDerivAt A (a u) u)
    {s K : ℝ} (hs : 0≤ s) (hK : ∀ u ∈ Icc (1-s) (2+s), |a u|≤ K) :
    (∫ u in (1:ℝ)..2, a (u+s)-a (u-s)) ≤ 4*K*s := by
  have hm := convex_derivative_monotone hc hd
  have hp : Monotone (fun u => a (u+s)) := hm.comp (fun _ _ h => by linarith)
  have hn : Monotone (fun u => a (u-s)) := hm.comp (fun _ _ h => sub_le_sub_right h s)
  rw [intervalIntegral.integral_sub hp.intervalIntegrable hn.intervalIntegrable,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => (hd (u+s)).comp_add_const u s) hp.intervalIntegrable,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => (hd (u-s)).comp_sub_const u s) hn.intervalIntegrable]
  have ht (t : ℝ) (ht : t∈Icc (1:ℝ) 2) : |A (t+s)-A (t-s)|≤ 2*K*s := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hm.intervalIntegrable]
    have hh : ‖∫ u in (t-s)..(t+s), a u‖≤ K*|(t+s)-(t-s)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => by
        rw [uIoc_of_le (by linarith : t-s≤t+s)] at hu
        exact hK u ⟨by linarith [ht.1,hu.1],by linarith [ht.2,hu.2]⟩)
    have he : (t+s)-(t-s)=2*s := by ring
    rw [he,abs_of_nonneg (by positivity)] at hh
    simpa only [Real.norm_eq_abs] using hh.trans_eq (by ring)
  have h1 := ht 1 (by norm_num)
  have h2 := ht 2 (by norm_num)
  linarith [le_abs_self (A (2+s)-A (2-s)),neg_abs_le (A (1+s)-A (1-s))]

lemma integrated_convex_fluctuation_bound {H A a : ℝ→ℝ}
    (hc : ConvexOn ℝ univ A) (hd : ∀ u, HasDerivAt A (a u) u)
    {s K δ : ℝ} (hs : 0<s)
    (hK : ∀ u ∈ Icc (1-s) (2+s), |a u|≤ K)
    (hH : IntervalIntegrable H volume 1 2)
    (hb : ∀ u ∈ Icc (1:ℝ) 2, H u≤ a (u+s)-a (u-s)+4*δ/s) :
    (∫ u in (1:ℝ)..2, H u) ≤ 4*K*s+4*δ/s := by
  have hm := convex_derivative_monotone hc hd
  have hp : Monotone (fun u => a (u+s)) := hm.comp (fun _ _ h => by linarith)
  have hn : Monotone (fun u => a (u-s)) := hm.comp (fun _ _ h => sub_le_sub_right h s)
  calc
    _ ≤ ∫ u in (1:ℝ)..2, a (u+s)-a (u-s)+4*δ/s :=
      intervalIntegral.integral_mono_on (by norm_num) hH
        ((hp.intervalIntegrable.sub hn.intervalIntegrable).add intervalIntegrable_const) hb
    _ = (∫ u in (1:ℝ)..2, a (u+s)-a (u-s))+4*δ/s := by
      rw [intervalIntegral.integral_add (hp.intervalIntegrable.sub hn.intervalIntegrable) intervalIntegrable_const]
      norm_num
    _ ≤ _ := by linarith [convex_integrated_derivative_shift hc hd hs.le hK]

variable {I : Type} [Fintype I]

def countableGaussianVector (g : ℕ→ℝ) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun i => g (countableCoordinate i))

lemma countableGaussianVector_measurable : Measurable (countableGaussianVector (I:=I)) := by
  unfold countableGaussianVector
  fun_prop

lemma countableGaussianVector_law :
    countableGaussianLaw.map (countableGaussianVector (I:=I))=stdGaussian (EuclideanSpace ℝ I) := by
  let c : (ℕ→ℝ)→I→ℝ := fun g i => g (countableCoordinate i)
  have hc : Measurable c := by fun_prop
  have hl : countableGaussianLaw.map c=Measure.infinitePi (fun _ : I => gaussianReal 0 1) :=
    Measure.map_infinitePi_infinitePi_of_inj countableCoordinate_injective
  change countableGaussianLaw.map ((WithLp.toLp 2) ∘ c)=_
  rw [← Measure.map_map (PiLp.continuous_toLp 2 _).measurable hc,hl,
    Measure.infinitePi_eq_pi,map_pi_eq_stdGaussian]

lemma countableGaussianVector_preserving :
    MeasurePreserving (countableGaussianVector (I:=I)) countableGaussianLaw (stdGaussian (EuclideanSpace ℝ I)) :=
  ⟨countableGaussianVector_measurable,countableGaussianVector_law⟩

def vectorGaussianRow {S : Type*} (V : S→EuclideanSpace ℝ I) (i : ℕ) (x : S) : ℝ :=
  finiteGaussianRow countableCoordinate (fun j => V x j) i

def vectorGaussianLength (I : Type) [Fintype I] : ℕ :=
  finiteGaussianRowLength (countableCoordinate (ι:=I))

lemma vectorGaussianRow_measurable {S : Type*} [MeasurableSpace S]
    {V : S→EuclideanSpace ℝ I} (hV : Measurable V) (i : ℕ) : Measurable (vectorGaussianRow V i) := by
  classical
  unfold vectorGaussianRow finiteGaussianRow
  apply Finset.measurable_sum
  intro j _
  split_ifs
  · exact (EuclideanSpace.proj j).continuous.measurable.comp hV
  · exact measurable_const

lemma vectorGaussianRow_field {S : Type*} (V : S→EuclideanSpace ℝ I) (g : ℕ→ℝ) (x : S) :
    countableGaussianField (vectorGaussianRow V) (fun _ => vectorGaussianLength I) g x=
      inner ℝ (V x) (countableGaussianVector g) := by
  unfold countableGaussianField gaussianPrefixField vectorGaussianRow vectorGaussianLength
  rw [finiteGaussianRow_field countableCoordinate_injective]
  rfl

lemma vectorGaussianRow_norm {S : Type*} (V : S→EuclideanSpace ℝ I) (x : S) :
    (∑ i : Fin (vectorGaussianLength I), vectorGaussianRow V i.val x^2)=‖V x‖^2 := by
  unfold vectorGaussianRow vectorGaussianLength
  rw [finiteGaussianRow_norm countableCoordinate_injective,← real_inner_self_eq_norm_sq]
  change (∑ i, V x i^2)=∑ i, V x i*V x i
  simp only [pow_two]

lemma vectorGaussianRow_covariance {S : Type*} (V W : S→EuclideanSpace ℝ I) (x y : S) :
    countableGaussianCovariance (vectorGaussianRow V) (vectorGaussianRow W)
      (fun _ => vectorGaussianLength I) x y = inner ℝ (W x) (V y) := by
  unfold countableGaussianCovariance gaussianPrefixCovariance maskedGaussianCoefficient
  simp only [Fin.is_lt,ite_true]
  change (∑ i : Fin (vectorGaussianLength I),
    finiteGaussianRow countableCoordinate (fun j => W x j) i.val *
    finiteGaussianRow countableCoordinate (fun j => V y j) i.val)=_
  calc
    _ = ∑ j, W x j*finiteGaussianRow countableCoordinate (fun k => V y k) (countableCoordinate j) :=
      finiteGaussianRow_sum countableCoordinate_injective (fun j => W x j)
        (fun i a => a*finiteGaussianRow countableCoordinate (fun j => V y j) i) (by simp)
    _ = ∑ j, W x j*V y j := by simp_rw [finiteGaussianRow_key countableCoordinate_injective]
    _ = _ := by
      change (∑ i, W x i*V y i)=∑ i, V y i*W x i
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma euclideanGaussian_tiltMean_ibp {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H : S→ℝ} {V W : S→EuclideanSpace ℝ I}
    (hH : Measurable H) (hV : Measurable V) (hW : Measurable W)
    {A D E : ℝ} (hA : ∀ x, |H x|≤A) (hD : ∀ x, ‖V x‖^2≤D) (hE : ∀ x, ‖W x‖^2≤E) :
    (∫ g, tiltMean μ (fun x => H x+inner ℝ (V x) g) (fun x => inner ℝ (W x) g) 1
      ∂stdGaussian (EuclideanSpace ℝ I)) =
    ∫ g, tiltMean μ (fun x => H x+inner ℝ (V x) g) (fun x => inner ℝ (W x) (V x)) 1 -
      gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) 2
        (fun x => inner ℝ (W (x 1)) (V (x 0))) ∂stdGaussian (EuclideanSpace ℝ I) := by
  have h1 : Measurable (fun a : EuclideanSpace ℝ I × S => H a.2+inner ℝ (V a.2) a.1) :=
    (hH.comp measurable_snd).add ((hV.comp measurable_snd).inner measurable_fst)
  have h2 : Measurable (fun a : EuclideanSpace ℝ I × S => inner ℝ (W a.2) a.1) :=
    (hW.comp measurable_snd).inner measurable_fst
  have h3 : Measurable (fun x => inner ℝ (W x) (V x)) := hW.inner hV
  have h4 : Measurable (fun x : Fin 2→S => inner ℝ (W (x 1)) (V (x 0))) :=
    (hW.comp (measurable_pi_apply 1)).inner (hV.comp (measurable_pi_apply 0))
  have hleft := kernel_tiltMean_measurable (Kernel.const (EuclideanSpace ℝ I) μ)
    (H := fun g x => H x+inner ℝ (V x) g) (Y := fun g x => inner ℝ (W x) g) h1 h2
  have hright := (kernel_tiltMean_measurable (Kernel.const (EuclideanSpace ℝ I) μ)
    (H := fun g x => H x+inner ℝ (V x) g) (Y := fun _ x => inner ℝ (W x) (V x)) h1
    (h3.comp measurable_snd)).sub (kernel_replicaMean_measurable (Kernel.const (EuclideanSpace ℝ I) μ)
    (H := fun g x => H x+inner ℝ (V x) g)
    (G := fun _ x => inner ℝ (W (x 1)) (V (x 0))) h1 (h4.comp measurable_snd))
  have he := annealedGaussianTiltMean_ibp μ hH (vectorGaussianRow_measurable hV)
    (vectorGaussianRow_measurable hW) measurable_const hA
    (fun x => (vectorGaussianRow_norm V x).trans_le (hD x))
    (fun x => (vectorGaussianRow_norm W x).trans_le (hE x))
  have hham (g) : countableGaussianHamiltonian H (vectorGaussianRow V)
      (fun _ => vectorGaussianLength I) g = fun x => H x+inner ℝ (V x) (countableGaussianVector g) := by
    funext x
    exact congrArg (fun y => H x+y) (vectorGaussianRow_field V g x)
  have hfield (g) : countableGaussianField (vectorGaussianRow W)
      (fun _ => vectorGaussianLength I) g = fun x => inner ℝ (W x) (countableGaussianVector g) :=
    funext (vectorGaussianRow_field W g)
  simp_rw [hham,hfield,vectorGaussianRow_covariance] at he
  simp only [Kernel.const_apply] at hleft hright
  change Measurable (fun g => tiltMean μ (fun x => H x+inner ℝ (V x) g)
    (fun x => inner ℝ (W x) (V x)) 1 - gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) 2
      (fun x => inner ℝ (W (x 1)) (V (x 0)))) at hright
  rw [← countableGaussianVector_law (I:=I),
    integral_map countableGaussianVector_measurable.aemeasurable hleft.aestronglyMeasurable,
    integral_map countableGaussianVector_measurable.aemeasurable hright.aestronglyMeasurable]
  exact he

end SphericalPerceptronFreeEnergy
end

end OAI
