import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

variable {ι : Type*} [Fintype ι]

def normalLogConst (d s : ℝ) : ℝ := -log (sqrt (2*Real.pi*s))-d^2/(2*s)

def normalLogDensity (d s x : ℝ) : ℝ := normalLogConst d s+d/s*x-x^2/(2*s)

lemma exp_normalLogDensity (d : ℝ) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    exp (normalLogDensity d s x) = gaussianPDFReal d s.toNNReal x := by
  have hsp : 0 < sqrt (2*Real.pi*s) := sqrt_pos.mpr (by positivity)
  have he : normalLogDensity d s x = -log (sqrt (2*Real.pi*s)) - (x-d)^2/(2*s) := by
    unfold normalLogDensity normalLogConst
    field_simp
    ring
  rw [he, sub_eq_add_neg, exp_add, exp_neg, exp_log hsp]
  simp only [gaussianPDFReal, Real.coe_toNNReal s hs.le]
  congr 1
  congr 1
  ring

lemma continuousOn_normalLogConst : ContinuousOn (fun p : ℝ×ℝ => normalLogConst p.1 p.2)
    {p | 0 < p.2} := by
  unfold normalLogConst
  apply ContinuousOn.sub
  · apply ContinuousOn.neg
    apply ContinuousOn.log
    · fun_prop
    · intro p hp
      have hp' : 0 < p.2 := hp
      exact (sqrt_pos.mpr (by positivity : 0 < 2*Real.pi*p.2)).ne'
  · exact (continuous_fst.pow 2).continuousOn.div (continuous_const.mul continuous_snd).continuousOn
      (fun p hp => mul_ne_zero (by norm_num) (ne_of_gt hp))

lemma normalLogDensity_sub_le (d' s' d s x : ℝ) :
    normalLogDensity d' s' x-normalLogDensity d s x ≤
      |normalLogConst d' s'-normalLogConst d s| + |d'/s'-d/s| *|x| +
        |1/(2*s')-1/(2*s)| *x^2 := by
  have hx := le_abs_self ((d'/s'-d/s)*x)
  rw [abs_mul] at hx
  have hq := neg_le_abs (1/(2*s')-1/(2*s))
  have hm := mul_le_mul_of_nonneg_right hq (sq_nonneg x)
  have hc := le_abs_self (normalLogConst d' s'-normalLogConst d s)
  have he : normalLogDensity d' s' x-normalLogDensity d s x =
      (normalLogConst d' s'-normalLogConst d s)+(d'/s'-d/s)*x -
        (1/(2*s')-1/(2*s))*x^2 := by
    unfold normalLogDensity
    ring
  rw [he]
  linarith

lemma normalLogDensity_sum_sub_le {y : ι → ℝ} {R : ℝ}
    (hy : ∑ i, (y i)^2 ≤ (Fintype.card ι : ℝ)*R) (d' s' d s : ℝ) :
    (∑ i, normalLogDensity d' s' (y i))-(∑ i, normalLogDensity d s (y i)) ≤
      (Fintype.card ι : ℝ) * (|normalLogConst d' s'-normalLogConst d s| +
        |d'/s'-d/s| *(1+R)+|1/(2*s')-1/(2*s)| *R) := by
  have hl : ∑ i, |y i| ≤ (Fintype.card ι : ℝ)*(1+R) := by
    calc
      _ ≤ ∑ i, (1+(y i)^2) := Finset.sum_le_sum (fun i _ => by
        nlinarith [sq_abs (y i), sq_nonneg (|y i|-1)])
      _ = (Fintype.card ι : ℝ) + ∑ i, (y i)^2 := by simp [Finset.sum_add_distrib]
      _ ≤ _ := by nlinarith
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => normalLogDensity_sub_le d' s' d s (y i))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] at hh
  have h1 := mul_le_mul_of_nonneg_left hl (abs_nonneg (d'/s'-d/s))
  have h2 := mul_le_mul_of_nonneg_left hy (abs_nonneg (1/(2*s')-1/(2*s)))
  calc
    _ ≤ _ := hh
    _ ≤ _ := by nlinarith

def productNormal (d s : ℝ) (y : ι → ℝ) : ℝ := ∏ i, gaussianPDFReal d s.toNNReal (y i)

lemma productNormal_eq_exp (d : ℝ) {s : ℝ} (hs : 0 < s) (y : ι → ℝ) :
    productNormal d s y = exp (∑ i, normalLogDensity d s (y i)) := by
  rw [exp_sum]
  unfold productNormal
  apply Finset.prod_congr rfl
  intro i hi
  exact (exp_normalLogDensity d hs (y i)).symm

lemma productNormal_nonneg (d s : ℝ) (y : ι → ℝ) : 0 ≤ productNormal d s y :=
  Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg d s.toNNReal (y i))

lemma integrable_tiltedNormal (f : ℝ →ᵇ ℝ) (d : ℝ) (s : ℝ≥0) :
    Integrable (fun x => exp (f x)*gaussianPDFReal d s x) := by
  have h := (integrable_gaussianPDFReal d s).bdd_mul
    (continuous_exp.comp f.continuous).aestronglyMeasurable
    (c := exp ‖f‖) (ae_of_all _ (fun x => by
      dsimp only [Function.comp_def]
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x))))
  exact h

lemma integral_tiltedNormal (f : ℝ →ᵇ ℝ) (d : ℝ) {s : ℝ≥0} (hs : s ≠ 0) :
    (∫ x, exp (f x)*gaussianPDFReal d s x) = ∫ x, exp (f x) ∂gaussianReal d s := by
  rw [integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul, mul_comm]

lemma tiltedNormal_mass_pos (f : ℝ →ᵇ ℝ) (d : ℝ) (s : ℝ≥0) :
    0 < ∫ x, exp (f x) ∂gaussianReal d s := by
  have hi : Integrable (fun x => exp (f x)) (gaussianReal d s) := Integrable.of_bound
    (by fun_prop) (exp ‖f‖) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x))))
  exact integral_pos_iff_support_of_nonneg (fun _ => (exp_pos _).le) hi |>.mpr
    (by simp [Function.support, (exp_pos _).ne'])

lemma product_tiltedNormal_integral (f : ℝ →ᵇ ℝ) (d : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ y : ι → ℝ, exp (∑ i, f (y i))*productNormal d s y) =
      exp ((Fintype.card ι : ℝ)*log (∫ x, exp (f x) ∂gaussianReal d s.toNNReal)) := by
  have hs' : s.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hs)
  have he (y : ι → ℝ) : exp (∑ i, f (y i))*productNormal d s y =
      ∏ i, (exp (f (y i))*gaussianPDFReal d s.toNNReal (y i)) := by
    rw [exp_sum, productNormal, Finset.prod_mul_distrib]
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_pow (fun x : ℝ => exp (f x)*gaussianPDFReal d s.toNNReal x), integral_tiltedNormal f d hs',
    exp_nat_mul, exp_log (tiltedNormal_mass_pos f d s.toNNReal)]

lemma product_tiltedNormal_integrable (f : ℝ →ᵇ ℝ) (d s : ℝ) :
    Integrable (fun y : ι → ℝ => exp (∑ i, f (y i))*productNormal d s y) := by
  have h := Integrable.fintype_prod (fun _ : ι => integrable_tiltedNormal f d s.toNNReal)
  simpa only [exp_sum, productNormal, Finset.prod_mul_distrib, volume_pi] using h

end SKGap

namespace SKGap

def normalDensityError (R d s d₀ s₀ : ℝ) : ℝ :=
  |normalLogConst d s-normalLogConst d₀ s₀| + |d/s-d₀/s₀| * (1+R) +
    |1/(2*s)-1/(2*s₀)| * R

lemma normalDensityError_self (R d s : ℝ) : normalDensityError R d s d s = 0 := by
  simp [normalDensityError]

lemma continuous_normalDensityError {X : Type*} [TopologicalSpace X]
    {d s : X → ℝ} (hd : Continuous d) (hs : Continuous s) (hspos : ∀ x, 0 < s x)
    (R d₀ s₀ : ℝ) : Continuous (fun x => normalDensityError R (d x) (s x) d₀ s₀) := by
  have hlog : Continuous (fun x => normalLogConst (d x) (s x)) :=
    continuousOn_normalLogConst.comp_continuous (hd.prodMk hs) (fun x => hspos x)
  have hdiv := hd.div hs (fun x => (hspos x).ne')
  have hinv : Continuous (fun x => (1 : ℝ)/(2*s x)) := continuous_const.div (continuous_const.mul hs) (fun x => mul_ne_zero (by norm_num) (hspos x).ne')
  exact ((hlog.sub continuous_const).abs.add ((hdiv.sub continuous_const).abs.mul continuous_const)).add
    ((hinv.sub continuous_const).abs.mul continuous_const)

theorem finite_gaussian_test_cover {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {P : X → ProbabilityMeasure ℝ} {d s ψ : X → ℝ}
    (hP : ContinuousOn P K) (hd : ContinuousOn d K) (hs : ContinuousOn s K)
    (hψ : ContinuousOn ψ K) (hpos : ∀ x ∈ K, 0 < s x) (R r : ℝ)
    (hW : ∀ x ∈ K, ∃ f : ℝ →ᵇ ℝ, ψ x-(∫ y, f y ∂P x)+
      log (∫ y, exp (f y) ∂gaussianReal (d x) (s x).toNNReal) < r) :
    ∃ (C : Finset K) (f : K → ℝ →ᵇ ℝ), ∀ z ∈ K, ∃ x ∈ C,
      ψ z-(∫ y, f x y ∂P z)+normalDensityError R (d z) (s z) (d x) (s x)+
      log (∫ y, exp (f x y) ∂gaussianReal (d x) (s x).toNNReal) < r := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  choose f hf using (fun x : K => hW x.1 x.2)
  let U (x : K) : Set K := {z | ψ z-(∫ y, f x y ∂P z)+
    normalDensityError R (d z) (s z) (d x) (s x)+
      log (∫ y, exp (f x y) ∂gaussianReal (d x) (s x).toNNReal) < r}
  have hU (x : K) : IsOpen (U x) := by
    apply isOpen_lt _ continuous_const
    have hint : Continuous (fun z : K => ∫ y, f x y ∂P z) :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (f x)).comp hP.domRestrict
    exact ((hψ.domRestrict.sub hint).add
      (continuous_normalDensityError hd.domRestrict hs.domRestrict
        (fun z : K => hpos z.1 z.2) R (d x) (s x))).add continuous_const
  have hcov : (univ : Set K) ⊆ ⋃ x : K, U x := by
    intro z _
    refine mem_iUnion.mpr ⟨z, ?_⟩
    change ψ z-(∫ y, f z y ∂P z)+normalDensityError R (d z) (s z) (d z) (s z)+
      log (∫ y, exp (f z y) ∂gaussianReal (d z) (s z).toNNReal) < r
    simpa only [normalDensityError_self, add_zero] using hf z
  obtain ⟨C,hC⟩ := isCompact_univ.elim_finite_subcover U hU hcov
  refine ⟨C,f,?_⟩
  intro z hz
  have hh := hC (mem_univ (⟨z,hz⟩ : K))
  obtain ⟨x,hx⟩ := mem_iUnion.mp hh
  obtain ⟨hxC,hxU⟩ := mem_iUnion.mp hx
  exact ⟨x,hxC,hxU⟩

end SKGap
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

end
end
end
end
end
end
end

end OAI
