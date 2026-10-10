import Mathlib
import OAI.Computability.MinUncut.Estimates.ExpectResampleRow
import OAI.Computability.MinUncut.Analysis.LowGradient

namespace OAI

section
noncomputable section
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] query pullQuery thirdFailure
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  {m n : ℕ}

lemma spatialEnergy_eq_expect (v : Point m n → ℝ) :
    spatialEnergy v = 𝔼 x : Point m n, (v x)^2 := by
  simp [spatialEnergy,Fintype.expect_eq_sum_div_card,Point,div_eq_mul_inv,mul_comm]

lemma spatial_young (v w : Point m n → ℝ) {a : ℝ} (ha : 0<a) :
    (𝔼 x : Point m n, v x*w x) ≤ a*spatialEnergy v+(4*a)⁻¹*spatialEnergy w := by
  rw [spatialEnergy_eq_expect,spatialEnergy_eq_expect]
  simp only [Finset.mul_expect,← Finset.expect_add_distrib]
  apply Finset.expect_le_expect
  intro x _
  have he : (4*a)*((4*a)⁻¹) = 1 := mul_inv_cancel₀ (by positivity)
  nlinarith [sq_nonneg (2*a*v x-w x)]

lemma gradient_correlation_truncate (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0<n) {σ η T a : ℝ} (hσ : σ≠0) (hη : 0<η) (hT : 0<T) (ha : 0<a)
    (c : Point m n → ℝ) (v : Point m n → ℝ) :
    (𝔼 x : Point m n, v x*gradient f B σ η c x) ≤
      T*faceCorrelation v+a*spatialEnergy v+
      (σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η)*thirdRejection f B σ η c := by
  have hE : 0 ≤ spatialEnergy v := by rw [spatialEnergy_eq_expect]; positivity
  have hW := tableMass_le_thirdRejection f B σ hη c
  have hcoeff : 0 ≤ σ⁻¹^2/(4*a*T) := by positivity
  have hsmall : 0 ≤ (σ⁻¹^2/(4*a*T))*tableMass f B σ η c :=
    mul_nonneg hcoeff (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hmid : (𝔼 x : Point m n, v x*gradient f B σ η c x) ≤
      T*faceCorrelation v+a*spatialEnergy v+(σ⁻¹^2/(4*a*T))*tableMass f B σ η c := by
    by_cases h : tableMass f B σ η c ≤ T
    · have hz := (le_abs_self _).trans (gradient_convex_correlation f B hn hσ hη.ne' c v)
      have hm := mul_le_mul_of_nonneg_right h (faceCorrelation_nonneg v)
      nlinarith [mul_nonneg ha.le hE]
    · have hy := spatial_young v (gradient f B σ η c) ha
      have hg := mul_le_mul_of_nonneg_left (gradient_spatialEnergy_le f B hn hσ η c)
        (show 0≤(4*a)⁻¹ by positivity)
      have hw := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) hcoeff
      have he : (σ⁻¹^2/(4*a*T))*T = (4*a)⁻¹*σ⁻¹^2 := by field_simp
      rw [he] at hw
      nlinarith [mul_nonneg hT.le (faceCorrelation_nonneg v)]
  exact hmid.trans (by nlinarith [mul_le_mul_of_nonneg_left hW hcoeff])

omit [Fintype A] in
lemma thirdRejection_measurable (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) :
    Measurable (thirdRejection f B σ η) := by
  have hh (z : Code m n) : Measurable
      (fun p : ((Point m n → ℝ) × (Point m n → ℝ)) × (Code m n → ℝ) =>
        thirdFailure f B η (p.1.1+σ•p.1.2) p.2 z) :=
    (measurable_thirdFailure f B η z).comp (show Measurable
      (fun p : ((Point m n → ℝ) × (Point m n → ℝ)) × (Code m n → ℝ) =>
        (p.1.1+σ•p.1.2,p.2)) by fun_prop)
  have hi (z : Code m n) : Measurable (fun c : Point m n → ℝ =>
      ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
        thirdFailure f B η (c+σ•g) l z ∂gauss (Code m n) ∂gauss (Point m n)) :=
    (hh z).stronglyMeasurable.integral_prod_right.measurable.stronglyMeasurable.integral_prod_right.measurable
  unfold thirdRejection
  simp only [Fintype.expect_eq_sum_div_card]
  exact (Finset.measurable_sum _ (fun z _ => hi z)).div_const _

omit [Fintype A] in
lemma thirdRejection_nonneg (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : 0 ≤ thirdRejection f B σ η c := by
  apply Finset.expect_nonneg
  intro z _
  exact integral_nonneg (fun g => integral_nonneg (fun l => thirdFailure_nonneg f B η _ l z))

omit [Fintype A] in
lemma thirdRejection_abs_le (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : |thirdRejection f B σ η c| ≤ 1 := by
  have he (z : Code m n) (g : Point m n → ℝ) :
      |∫ l, thirdFailure f B η (c+σ•g) l z ∂gauss (Code m n)| ≤ 1 := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := gauss (Code m n))
        (f := fun l => thirdFailure f B η (c+σ•g) l z) (C := 1)
        (ae_of_all _ (fun l => by simpa only [Real.norm_eq_abs] using thirdFailure_abs_le f B η _ l z))
  have hb (z : Code m n) :
      |∫ g, ∫ l, thirdFailure f B η (c+σ•g) l z ∂gauss (Code m n) ∂gauss (Point m n)| ≤ 1 := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := gauss (Point m n))
        (f := fun g => ∫ l, thirdFailure f B η (c+σ•g) l z ∂gauss (Code m n)) (C := 1)
        (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using he z g))
  exact (Finset.abs_expect_le _ _).trans (by
    simpa using Finset.expect_le_expect (s := Finset.univ) (fun z _ => hb z))

omit [Fintype A] in
lemma thirdRejection_integrable (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) :
    Integrable (thirdRejection f B σ η) (gauss (Point m n)) :=
  Integrable.of_bound (thirdRejection_measurable f B σ η).aestronglyMeasurable 1
    (ae_of_all _ (fun c => by simpa only [Real.norm_eq_abs] using thirdRejection_abs_le f B σ η c))

lemma lowGradient_continuous (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) (x : Point m n) :
    Continuous (fun c => lowGradient D s f σ η B c x) :=
  selectedProject_continuous _ _ _

lemma lowGradient_correlation_continuous (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) :
    Continuous (fun c => faceCorrelation (lowGradient D s f σ η B c)) := by
  apply Continuous.finset_sup'_apply
  intro z _
  simp only [Fintype.expect_eq_sum_div_card]
  exact ((continuous_finsetSum _ (fun x _ =>
    (lowGradient_continuous D s f σ η B x).mul continuous_const)).div_const _).abs

lemma lowGradient_correlation_integrable (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) :
    Integrable (fun c => faceCorrelation (lowGradient D s f σ η B c)) (gauss (Point m n)) := by
  have hi : Integrable (fun c => 𝔼 x : Point m n, |lowGradient D s f σ η B c x|)
      (gauss (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun x _ =>
      ((lowGradient_memLp D s f σ η B x).integrable (by norm_num)).abs)).div_const _
  exact hi.mono' (lowGradient_correlation_continuous D s f σ η B).aestronglyMeasurable
    (ae_of_all _ (fun c => by
      rw [Real.norm_eq_abs,abs_of_nonneg (faceCorrelation_nonneg _)]
      exact faceCorrelation_le_l1 _))

def averagedCorrelation (u : FaceArray A m n → (Point m n → ℝ) → Point m n → ℝ) : ℝ :=
  𝔼 B, ∫ c, faceCorrelation (u B c) ∂gauss (Point m n)

def thirdError (f : FoldedProof A) (σ η : ℝ) : ℝ :=
  𝔼 B : FaceArray A m n, ∫ c, thirdRejection f B σ η c ∂gauss (Point m n)

lemma lowGradient_inner_identity (D s : ℕ) (f : FoldedProof A)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    (𝔼 B : FaceArray A m n, ∫ c, (𝔼 x : Point m n,
      lowGradient D s f σ η B c x*gradient f B σ η c x) ∂gauss (Point m n)) =
      averagedEnergy (lowGradient (m := m) (n := n) D s f σ η) := by
  have hi (B : FaceArray A m n) :
      (∫ c, (𝔼 x : Point m n, lowGradient D s f σ η B c x*gradient f B σ η c x)
        ∂gauss (Point m n)) =
      (𝔼 x : Point m n, ∫ c, lowGradient D s f σ η B c x*gradient f B σ η c x
        ∂gauss (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card,integral_div]
    rw [integral_finsetSum (f := fun x c => lowGradient D s f σ η B c x*gradient f B σ η c x) _ (fun x _ =>
      (lowGradient_memLp D s f σ η B x).integrable_mul (gradient_memLp f B hσ η x))]
  simp_rw [hi]
  rw [Finset.expect_comm]
  have he (x : Point m n) :
      (𝔼 B : FaceArray A m n, ∫ c,
        lowGradient D s f σ η B c x*gradient f B σ η c x ∂gauss (Point m n)) =
      jointEnergy (fun B c => lowGradient D s f σ η B c x) := by
    change jointInner (selectedProject (rectangle D s) (fun B c => gradient f B σ η c x))
      (fun B c => gradient f B σ η c x) = _
    rw [jointInner_symm,selectedProject_source_inner _ _ (fun B => gradient_memLp f B hσ η x),
      ← selectedProject_energy]
    rfl
  simp_rw [he]
  rw [averagedEnergy_eq_jointEnergy _ (lowGradient_memLp D s f σ η)]
  simp [Point,Fintype.expect_eq_sum_div_card,div_eq_mul_inv,mul_comm]

lemma lowGradient_correlation_truncated (D s : ℕ) (f : FoldedProof A)
    (hn : 0<n) {σ η T a : ℝ} (hσ : σ≠0) (hη : 0<η) (hT : 0<T) (ha : 0<a) :
    averagedEnergy (lowGradient (m := m) (n := n) D s f σ η) ≤
      T*averagedCorrelation (lowGradient (m := m) (n := n) D s f σ η)+
      a*averagedEnergy (lowGradient (m := m) (n := n) D s f σ η)+
      (σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η)*thirdError (m := m) (n := n) f σ η := by
  have hi (B : FaceArray A m n) :
      Integrable (fun c => 𝔼 x : Point m n,
        lowGradient D s f σ η B c x*gradient f B σ η c x) (gauss (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun x _ =>
      (lowGradient_memLp D s f σ η B x).integrable_mul (gradient_memLp f B hσ η x))).div_const _
  have he (B : FaceArray A m n) :
      Integrable (fun c => spatialEnergy (lowGradient D s f σ η B c)) (gauss (Point m n)) := by
    simp only [spatialEnergy]
    exact (integrable_finsetSum _ (fun x _ => (lowGradient_memLp D s f σ η B x).integrable_sq)).const_mul _
  have hp (B : FaceArray A m n) := integral_mono (hi B)
    (((lowGradient_correlation_integrable D s f σ η B).const_mul T).add ((he B).const_mul a) |>.add
      ((thirdRejection_integrable f B σ η).const_mul ((σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η))))
    (fun c => gradient_correlation_truncate f B hn hσ hη hT ha c (lowGradient D s f σ η B c))
  have hp' (B : FaceArray A m n) :
      (∫ c, (𝔼 x : Point m n, lowGradient D s f σ η B c x*gradient f B σ η c x)
        ∂gauss (Point m n)) ≤
      T*(∫ c, faceCorrelation (lowGradient D s f σ η B c) ∂gauss (Point m n))+
      a*(∫ c, spatialEnergy (lowGradient D s f σ η B c) ∂gauss (Point m n))+
      (σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η)*
        (∫ c, thirdRejection f B σ η c ∂gauss (Point m n)) := by
    have hh := hp B
    change _ ≤ ∫ c, (T*faceCorrelation (lowGradient D s f σ η B c)+
      a*spatialEnergy (lowGradient D s f σ η B c)+
      (σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η)*thirdRejection f B σ η c)
        ∂gauss (Point m n) at hh
    rw [integral_add (f := fun c => T*faceCorrelation (lowGradient D s f σ η B c)+a*spatialEnergy (lowGradient D s f σ η B c))
      (g := fun c => (σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η)*thirdRejection f B σ η c)
      ((lowGradient_correlation_integrable D s f σ η B).const_mul T |>.add ((he B).const_mul a))
      ((thirdRejection_integrable f B σ η).const_mul _),
      integral_add ((lowGradient_correlation_integrable D s f σ η B).const_mul T) ((he B).const_mul a)] at hh
    simpa only [integral_const_mul] using hh
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun B _ => hp' B)
  rw [lowGradient_inner_identity D s f hσ η] at hh
  simpa only [Finset.expect_add_distrib,← Finset.mul_expect,averagedCorrelation,averagedEnergy,thirdError]
    using hh
end MinUncut.Inner

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)] {m n : ℕ}

lemma lowGradient_correlation_truncated_weighted (D s : ℕ)
    (w : Ξ → ℝ) (hw : ∀ ξ,0≤w ξ) (f : ∀ ξ, FoldedProof (A ξ))
    (hn : 0<n) {σ η T a : ℝ} (hσ : σ≠0) (hη : 0<η) (hT : 0<T) (ha : 0<a) :
    (∑ ξ, w ξ*averagedEnergy (lowGradient (m := m) (n := n) D s (f ξ) σ η)) ≤
      T*(∑ ξ, w ξ*averagedCorrelation (lowGradient (m := m) (n := n) D s (f ξ) σ η))+
      a*(∑ ξ, w ξ*averagedEnergy (lowGradient (m := m) (n := n) D s (f ξ) σ η))+
      (σ⁻¹^2/(4*a*T))*((Fintype.card (Code m n):ℝ)/η)*
        (∑ ξ, w ξ*thirdError (m := m) (n := n) (f ξ) σ η) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ξ _ => mul_le_mul_of_nonneg_left
    (lowGradient_correlation_truncated (m := m) D s (f ξ) hn hσ hη hT ha) (hw ξ))
  convert hh using 1
  simp only [mul_add,Finset.sum_add_distrib]
  congr 2 <;> rw [Finset.mul_sum] <;> apply Finset.sum_congr rfl <;> intro ξ _ <;> ring
end MinUncut.Inner

end
end

end OAI
