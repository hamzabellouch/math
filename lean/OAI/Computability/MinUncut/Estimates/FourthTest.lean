import Mathlib
import OAI.Computability.MinUncut.Analysis.LowGradient
import OAI.Computability.MinUncut.Encoding.LocalDecoder

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
attribute [local instance] Classical.propDecidable
attribute [local irreducible] query pullQuery
variable {V A V' A' : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A'] [Fintype A'] {m n : ℕ}

def comparisonFailure (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) : ℝ :=
  if f.answer (pullQuery B (c+σ•p.1) (η•p.2)) =
    g.answer (pullQuery C (c+σ•p.1) (η•p.2)) then 0 else 1

def comparisonRejection (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ)
    (c : Point m n → ℝ) : ℝ :=
  ∫ p, comparisonFailure f g B C σ η c p ∂(gauss (Point m n)).prod (gauss (Code m n))

omit [Fintype A] [Fintype A'] in
lemma comparisonFailure_eq (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) :
    (coupledAnswer f B σ η c p-coupledAnswer g C σ η c p)^2 =
      4*comparisonFailure f g B C σ η c p := by
  unfold coupledAnswer comparisonFailure
  cases f.answer (pullQuery B (c+σ•p.1) (η•p.2)) <;>
    cases g.answer (pullQuery C (c+σ•p.1) (η•p.2)) <;> norm_num [bitSign]

theorem gradient_comparison (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n)
    (hn : 0 < n) {σ : ℝ} (hσ : σ≠0) (η : ℝ) (c : Point m n → ℝ) :
    spatialEnergy (fun x => gradient f B σ η c x-gradient g C σ η c x) ≤
      4*σ⁻¹^2*comparisonRejection f g B C σ η c := by
  let μ := (gauss (Point m n)).prod (gauss (Code m n))
  let D := fun p => coupledAnswer f B σ η c p-coupledAnswer g C σ η c p
  have hD : MemLp D 2 μ := (coupledAnswer_memLp f B σ η c).sub (coupledAnswer_memLp g C σ η c)
  have hX (x : Point m n) : MemLp (fun p => p.1 x) 2 μ :=
    (GaussianSmoothing.coordinate_memLp_two x).comp_fst (gauss (Code m n))
  have hXX (x y : Point m n) : (∫ p, p.1 x*p.1 y ∂μ)=if x=y then 1 else 0 := by
    have hi : Integrable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => p.1 x*p.1 y) μ :=
      (hX x).integrable_mul (hX y)
    change (∫ p, p.1 x*p.1 y ∂(gauss (Point m n)).prod (gauss (Code m n)))=_
    rw [integral_prod _ hi]
    simpa only [integral_const,MeasureTheory.probReal_univ,one_smul,gauss,GaussianSmoothing.gamma] using GaussianSmoothing.coordinate_second_moment x y
  have hS := GaussianSmoothing.integral_bessel hX hXX hD
  have hN : (0 : ℝ)<(n^m:ℕ) := by exact_mod_cast pow_pos hn m
  have hd (x : Point m n) :
      gradient f B σ η c x-gradient g C σ η c x =
      Real.sqrt (n^m:ℕ)/σ*(∫ p, p.1 x*D p ∂μ) := by
    rw [gradient_coupled_score f B hσ,gradient_coupled_score g C hσ]
    simp only [D,mul_sub]
    rw [integral_sub (coupled_score_integrable f B σ η c x) (coupled_score_integrable g C σ η c x)]
    ring
  have he : spatialEnergy (fun x => gradient f B σ η c x-gradient g C σ η c x) =
      σ⁻¹^2*∑ x, (∫ p, p.1 x*D p ∂μ)^2 := by
    simp only [spatialEnergy,hd,mul_pow,div_pow,Real.sq_sqrt hN.le,← Finset.mul_sum]
    field_simp
  rw [he]
  calc
    _ ≤ σ⁻¹^2*(∫ p, (D p)^2 ∂μ) := mul_le_mul_of_nonneg_left hS (sq_nonneg _)
    _ = _ := by
      simp_rw [D,comparisonFailure_eq]
      rw [integral_const_mul]
      change σ⁻¹^2*(4*comparisonRejection f g B C σ η c)=_
      ring

def pullbackFaces (π : A →ᵃ[F₂] A') (C : FaceArray A' m n) : FaceArray A m n :=
  fun r => formPullback π (C r)

omit [Fintype A] [Fintype A'] in
@[simp] lemma labelCode_pullbackFaces (π : A →ᵃ[F₂] A') (C : FaceArray A' m n) (a : A) :
    labelCode (pullbackFaces π C) a = labelCode C (π a) := rfl

omit [Fintype A] [Fintype A'] in
@[simp] lemma pullQuery_pullbackFaces (π : A →ᵃ[F₂] A') (C : FaceArray A' m n)
    (u : Point m n → ℝ) (d : Code m n → ℝ) :
    pullQuery (pullbackFaces π C) u d = (pullQuery C u d) ∘ π := by
  funext a
  unfold pullQuery
  rw [labelCode_pullbackFaces]
  rfl

omit [Fintype A] [Fintype A'] in
lemma pullbackFaces_joinRow (π : A →ᵃ[F₂] A') (r : Row m n) (b : Forms A')
    (D : Rest (W := Forms A') r) :
    pullbackFaces π (joinRow r b D) =
      joinRow r (formPullback π b) (fun t => formPullback π (D t)) := by
  funext t
  by_cases ht : t=r
  · subst t
    simp [pullbackFaces]
  · simp only [pullbackFaces, joinRow_other r b D ⟨t,ht⟩,
      joinRow_other r (formPullback π b) (fun s => formPullback π (D s)) ⟨t,ht⟩]

def comparisonRow (f : FoldedProof A) (σ η : ℝ) (c : Point m n → ℝ)
    (x : Point m n) (r : Row m n) (D : Rest (W := Forms A) r) (b : Forms A) : ℝ :=
  gradient f (joinRow r b D) σ η c x

omit [Fintype A] [Fintype A'] in
lemma comparisonRow_pullback (π : A →ᵃ[F₂] A') (f : FoldedProof A)
    (σ η : ℝ) (c : Point m n → ℝ) (x : Point m n) (r : Row m n)
    (D : Rest (W := Forms A') r) (b : Forms A') :
    comparisonRow f σ η c x r (fun t => formPullback π (D t)) (formPullback π b) =
      gradient f (pullbackFaces π (joinRow r b D)) σ η c x := by
  rw [pullbackFaces_joinRow]
  rfl

omit [Fintype A] in
lemma comparisonRow_average (π : A →ᵃ[F₂] A') (f : FoldedProof A) (g : FoldedProof A')
    (σ η : ℝ) (c : Point m n → ℝ) (x : Point m n) (r : Row m n) :
    (𝔼 D : Rest (W := Forms A') r, 𝔼 b : Forms A',
      (comparisonRow f σ η c x r (fun t => formPullback π (D t)) (formPullback π b) -
        comparisonRow g σ η c x r D b)^2) =
    𝔼 C : FaceArray A' m n,
      (gradient f (pullbackFaces π C) σ η c x-gradient g C σ η c x)^2 := by
  simp_rw [comparisonRow_pullback]
  rw [Finset.expect_comm, expect_splitRow r]
  rfl

omit [Fintype A] [Fintype A'] in
lemma comparisonFailure_indicator (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) :
    comparisonFailure f g B C σ η c p =
      (coupledAnswer f B σ η c p-coupledAnswer g C σ η c p)^2/4 := by
  have h := comparisonFailure_eq f g B C σ η c p
  linarith

lemma comparisonRejection_measurable (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ) :
    Measurable (comparisonRejection f g B C σ η) := by
  have hf : Measurable
      (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
        coupledAnswer f B σ η u.1 u.2) := by
    have hm : Measurable (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
        (u.1+σ•u.2.1,u.2.2)) := by fun_prop
    exact (measurable_answer f B η).comp hm
  have hg : Measurable
      (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
        coupledAnswer g C σ η u.1 u.2) := by
    have hm : Measurable (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
        (u.1+σ•u.2.1,u.2.2)) := by fun_prop
    exact (measurable_answer g C η).comp hm
  have hm : Measurable (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
      comparisonFailure f g B C σ η u.1 u.2) := by
    simp_rw [comparisonFailure_indicator]
    exact (hf.sub hg).pow_const 2 |>.div_const 4
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma comparisonRejection_range (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ)
    (c : Point m n → ℝ) :
    0≤ comparisonRejection f g B C σ η c ∧ comparisonRejection f g B C σ η c≤1 := by
  have hm : Measurable (comparisonFailure f g B C σ η c) := by
    change Measurable (fun p => comparisonFailure f g B C σ η c p)
    simp_rw [comparisonFailure_indicator]
    exact ((coupledAnswer_measurable f B σ η c).sub
      (coupledAnswer_measurable g C σ η c)).pow_const 2 |>.div_const 4
  have hb (p : (Point m n → ℝ) × (Code m n → ℝ)) :
      0≤ comparisonFailure f g B C σ η c p ∧ comparisonFailure f g B C σ η c p≤1 := by
    unfold comparisonFailure; split_ifs <;> norm_num
  have hi : Integrable (comparisonFailure f g B C σ η c)
      ((gauss (Point m n)).prod (gauss (Code m n))) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hb p).1]; exact (hb p).2))
  constructor
  · exact integral_nonneg (fun p => (hb p).1)
  · unfold comparisonRejection
    simpa only [integral_const,MeasureTheory.probReal_univ,one_smul] using
      integral_mono hi (integrable_const 1) (fun p => (hb p).2)

lemma comparisonRejection_integrable (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ) :
    Integrable (comparisonRejection f g B C σ η) (gauss (Point m n)) :=
  Integrable.of_bound (comparisonRejection_measurable f g B C σ η).aestronglyMeasurable 1
    (ae_of_all _ (fun c => by
      rw [Real.norm_eq_abs,abs_of_nonneg (comparisonRejection_range f g B C σ η c).1]
      exact (comparisonRejection_range f g B C σ η c).2))

def fourthError (π : A →ᵃ[F₂] A') (f : FoldedProof A) (g : FoldedProof A')
    (σ η : ℝ) : ℝ :=
  𝔼 C : FaceArray A' m n, ∫ c,
    comparisonRejection f g (pullbackFaces π C) C σ η c ∂gauss (Point m n)

lemma averaged_comparison (π : A →ᵃ[F₂] A') (f : FoldedProof A) (g : FoldedProof A')
    (hn : 0<n) {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    averagedEnergy (m := m) (n := n) (fun C c x => gradient f (pullbackFaces π C) σ η c x-
      gradient g C σ η c x) ≤ 4*σ⁻¹^2*fourthError (m := m) (n := n) π f g σ η := by
  have he (C : FaceArray A' m n) :
      (∫ c, spatialEnergy (fun x => gradient f (pullbackFaces π C) σ η c x-
          gradient g C σ η c x) ∂gauss (Point m n)) ≤
        4*σ⁻¹^2*(∫ c, comparisonRejection f g (pullbackFaces π C) C σ η c ∂gauss (Point m n)) := by
    have hi : Integrable (fun c => spatialEnergy (fun x =>
        gradient f (pullbackFaces π C) σ η c x-gradient g C σ η c x)) (gauss (Point m n)) := by
      apply Integrable.const_mul
      apply integrable_finsetSum
      intro x _
      exact ((gradient_memLp f (pullbackFaces π C) hσ η x).sub
        (gradient_memLp g C hσ η x)).integrable_sq
    rw [← integral_const_mul]
    exact integral_mono hi ((comparisonRejection_integrable f g _ _ σ η).const_mul _)
      (fun c => gradient_comparison f g _ _ hn hσ η c)
  simpa only [averagedEnergy,fourthError,← Finset.mul_expect] using
    Finset.expect_le_expect (s := Finset.univ) (fun C _ => he C)

omit [Fintype A] in
lemma comparisonRow_spatial_average (π : A →ᵃ[F₂] A') (f : FoldedProof A)
    (g : FoldedProof A') (σ η : ℝ) (c : Point m n → ℝ)
    (r : Point m n → Row m n) :
    (𝔼 x : Point m n, 𝔼 D : Rest (W := Forms A') (r x), 𝔼 b : Forms A',
      (comparisonRow f σ η c x (r x) (fun t => formPullback π (D t)) (formPullback π b)-
        comparisonRow g σ η c x (r x) D b)^2) =
    𝔼 C : FaceArray A' m n, spatialEnergy (fun x =>
      gradient f (pullbackFaces π C) σ η c x-gradient g C σ η c x) := by
  simp_rw [comparisonRow_average]
  rw [Finset.expect_comm]
  congr 1
  funext C
  simp only [Fintype.expect_eq_sum_div_card,spatialEnergy,Fintype.card_fun,Fintype.card_fin,
    div_eq_mul_inv,mul_comm]

end MinUncut.Inner

open scoped BigOperators
namespace MinUncut.Composition
open BinaryFourier hiding F₂
open MinUncut.Inner RowNoise
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {V W A B : Type*}
  [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup W] [Module F₂ W] [AddTorsor W B] [Fintype B]

def listMatch (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (g : Forms B → ℝ) (u θ : ℝ) : Prop :=
  ∃ a ∈ labelList f u, ∃ b ∈ labelList g θ, π a=b

def rowDistance (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (g : Forms B → ℝ) : ℝ :=
  𝔼 z : Forms B, (g z-f (formPullback π z))^2

def restrictedFourth (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (u : ℝ) : ℝ :=
  ∑ β : Module.Dual F₂ (Forms B), coefficient (fun z => remainder f u (formPullback π z)) β ^4

omit [Fintype A] in
lemma rowDistance_nonneg (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (g : Forms B → ℝ) :
    0≤rowDistance π f g := Finset.expect_nonneg (fun _ _ => sq_nonneg _)

lemma restrictedFourth_nonneg (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (u : ℝ) :
    0≤restrictedFourth π f u := Finset.sum_nonneg (fun _ _ => by positivity)

lemma coefficient_fourth_le (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (u : ℝ)
    (β : Module.Dual F₂ (Forms B)) :
    coefficient (fun z => remainder f u (formPullback π z)) β ^4 ≤ restrictedFourth π f u :=
  by
    unfold restrictedFourth
    exact Finset.single_le_sum (f := fun γ : Module.Dual F₂ (Forms B) =>
      coefficient (fun z => remainder f u (formPullback π z)) γ ^4)
      (fun _ _ => by positivity) (Finset.mem_univ β)

theorem atom_le_matching_charge (π : A →ᵃ[F₂] B) (f : Forms A → ℝ)
    (g : Forms B → ℝ) (u : ℝ) {θ : ℝ} (hθ : 0<θ) :
    (if (labelList g θ).Nonempty then (1 : ℝ) else 0) ≤
      (if listMatch π f g u θ then 1 else 0) +
      16/θ^2*rowDistance π f g + 256/θ^4*restrictedFourth π f u := by
  have hd := rowDistance_nonneg π f g
  have hr := restrictedFourth_nonneg π f u
  have hd0 : 0≤16/θ^2*rowDistance π f g := by positivity
  have hr0 : 0≤256/θ^4*restrictedFourth π f u := by positivity
  by_cases ha : (labelList g θ).Nonempty
  · rw [ite_eq_left ha]
    by_cases hm : listMatch π f g u θ
    · rw [ite_eq_left hm]; linarith
    rw [ite_eq_right hm,zero_add]
    obtain ⟨b,hb⟩ := ha
    by_cases hc : rowDistance π f g < (θ/4)^2
    · have hrem : θ/4 ≤ |coefficient (fun z => remainder f u (formPullback π z))
          (labelFrequency b)| := by
        by_contra hn
        obtain ⟨a,ha,hab⟩ := local_matching π f g hθ b hb hc (lt_of_not_ge hn)
        exact hm ⟨a,ha,b,hb,hab⟩
      have hpow := pow_le_pow_left₀ (by positivity : 0≤θ/4) hrem 4
      rw [pow_abs,abs_of_nonneg (by positivity)] at hpow
      have hfour := coefficient_fourth_le π f u (labelFrequency b)
      have hlow : θ^4 ≤ 256*restrictedFourth π f u := by nlinarith
      have hcharge : 1≤256/θ^4*restrictedFourth π f u := by
        rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hθ 4),one_mul]
        exact hlow
      linarith
    · have hlow : θ^2≤16*rowDistance π f g := by
        have hh := le_of_not_gt hc
        nlinarith
      have hcharge : 1≤16/θ^2*rowDistance π f g := by
        rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hθ 2),one_mul]
        exact hlow
      linarith
  · rw [ite_eq_right ha]
    have hm0 : (0 : ℝ) ≤ (if listMatch π f g u θ then 1 else 0) := by split_ifs <;> norm_num
    linarith

end MinUncut.Composition

end

end OAI
