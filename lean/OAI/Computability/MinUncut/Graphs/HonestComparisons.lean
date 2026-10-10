import Mathlib
import OAI.Computability.MinUncut.Estimates.FirstError
import OAI.Computability.MinUncut.Analysis.FreshCorrelation
import OAI.Computability.MinUncut.Graphs.HonestRows
import OAI.Computability.MinUncut.Analysis.GaussianPacking

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.Inner
open GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma score_query (z : Code m n) (u : Point m n → ℝ) (d : Code m n → ℝ) :
    query u d z=decide (0 ≤ score (codeVector z) u+d z) := by
  rw [score_codeVector]
  rfl

lemma score_add_noise (v c g : Point m n → ℝ) (σ : ℝ) :
    score v (c+σ•g)=score v c+σ*score v g := by
  simp only [score,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype A] in
lemma firstFailure_evaluation (a : A) (B : FaceArray A m n) (σ η : ℝ)
    (c g : Point m n → ℝ) (l : Code m n → ℝ) :
    firstFailure (evaluationProof a) B σ η c g l =
      signFailure (score (codeVector (labelCode B a)) c)
        (score (codeVector (labelCode B a)) c+σ*score (codeVector (labelCode B a)) g+η*l (labelCode B a)) := by
  simp only [firstFailure,evaluationProof,pullQuery,score_query,Pi.zero_apply,add_zero,
    score_add_noise,Pi.smul_apply,smul_eq_mul,decide_eq_decide,signFailure]

omit [Fintype A] in
lemma firstRejection_evaluation_le (a : A) (B : FaceArray A m n) (hn : 0<n)
    {σ η : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) :
    (∫ c, firstRejection (evaluationProof a) B σ η c ∂gauss (Point m n))  ≤  4*(σ+η) := by
  simp only [firstRejection,firstFailure_evaluation,gauss]
  exact first_triple_bound (codeVector_norm hn _) hσ hη _

lemma firstError_evaluation_le (a : A) (hn : 0<n) {σ η : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) :
    firstError (m := m) (n := n) (evaluationProof a) σ η  ≤  4*(σ+η) := by
  exact (Finset.expect_le_expect (fun B _ => firstRejection_evaluation_le a B hn hσ hη)).trans_eq
    (Fintype.expect_const _)

omit [Fintype A] in
lemma secondFailure_evaluation (a : A) (B C : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) :
    secondFailure (evaluationProof a) B C σ η c p =
      signFailure (score (codeVector (labelCode B a)) c+σ*score (codeVector (labelCode B a)) p.1+η*p.2 (labelCode B a))
        (score (codeVector (labelCode C a)) c+σ*score (codeVector (labelCode C a)) p.1+η*p.2 (labelCode C a)) := by
  simp only [secondFailure,evaluationProof,pullQuery,score_query,score_add_noise,
    Pi.smul_apply,smul_eq_mul,decide_eq_decide,signFailure]

omit [Fintype A] in
lemma secondRejection_evaluation_le (a : A) (B C : FaceArray A m n) (hn : 0<n)
    {σ η : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hη : 0 ≤ η) :
    (∫ c, secondRejection (evaluationProof a) B C σ η c ∂gauss (Point m n))  ≤
      4*‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖+4*η := by
  unfold secondRejection
  simp only [secondFailure_evaluation,gauss]
  have he (c : Point m n → ℝ) :
      (∫ p : (Point m n → ℝ) × (Code m n → ℝ),
        signFailure (score (codeVector (labelCode B a)) c+σ*score (codeVector (labelCode B a)) p.1+η*p.2 (labelCode B a))
          (score (codeVector (labelCode C a)) c+σ*score (codeVector (labelCode C a)) p.1+η*p.2 (labelCode C a))
        ∂(Measure.pi (fun _ : Point m n => gaussianReal 0 1)).prod (Measure.pi (fun _ : Code m n => gaussianReal 0 1))) =
      ∫ g, ∫ l,
        signFailure (score (codeVector (labelCode B a)) c+σ*score (codeVector (labelCode B a)) g+η*l (labelCode B a))
          (score (codeVector (labelCode C a)) c+σ*score (codeVector (labelCode C a)) g+η*l (labelCode C a))
        ∂Measure.pi (fun _ : Code m n => gaussianReal 0 1) ∂Measure.pi (fun _ : Point m n => gaussianReal 0 1) := by
    apply integral_prod
    apply signFailure_integrable <;> unfold score <;> fun_prop
  simp_rw [he]
  exact second_triple_bound (codeVector_norm hn _) (codeVector_norm hn _) hσ hσ1 hη _ _

omit [Fintype A] in
lemma thirdFailure_evaluation (a : A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) (l : Code m n → ℝ) (z : Code m n) :
    thirdFailure (evaluationProof a) B η u l z=if z=labelCode B a then 1 else 0 := by
  unfold thirdFailure evaluationProof
  by_cases h : z=labelCode B a
  · subst z; simp
  · simp [Function.update_of_ne (Ne.symm h),h]

omit [Fintype A] in
lemma thirdRejection_evaluation (a : A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : thirdRejection (evaluationProof a) B σ η c=(Fintype.card (Code m n):ℝ)⁻¹ := by
  simp only [thirdRejection,thirdFailure_evaluation,integral_const,probReal_univ,one_smul,
    Fintype.expect_eq_sum_div_card]
  simp

lemma thirdError_evaluation (a : A) (σ η : ℝ) :
    thirdError (m := m) (n := n) (evaluationProof a) σ η=(Fintype.card (Code m n):ℝ)⁻¹ := by
  simp only [thirdError,thirdRejection_evaluation,integral_const,probReal_univ,one_smul,Fintype.expect_const]
end MinUncut.Inner

end
noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma codeVector_distance_sq (hn : 0<n) (z w : Code m n) :
    ‖vector (codeVector z)-vector (codeVector w)‖^2=
      ((n^m:ℕ):ℝ)⁻¹*∑ x, (BinaryFourier.sign (z.val x)-BinaryFourier.sign (w.val x))^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,PiLp.sub_apply,vector,codeVector,← mul_sub,mul_pow]
  rw [← Finset.mul_sum,inv_pow,Real.sq_sqrt (by positivity)]

lemma noise_vector_sq (a : A) (B : FaceArray A m n) (hn : 0<n) (ρ : ℝ) :
    (𝔼 C : FaceArray A m n, density ρ B C*‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖^2)=
      ((n^m:ℕ):ℝ)⁻¹*∑ x : Point m n, 2*(1-(1-ρ)^degree (labelFunctional a x)) := by
  simp_rw [codeVector_distance_sq hn,← character_label,Finset.mul_sum,mul_left_comm (density ρ B _),
    Finset.expect_sum_comm,← Finset.mul_expect,character_noise_distance]

lemma noise_vector_sq_le (a : A) (B : FaceArray A m n) (hn : 0<n)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (𝔼 C : FaceArray A m n, density ρ B C*‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖^2) ≤ 2*(m:ℝ)*ρ := by
  have hn' : (0:ℝ)<(n^m:ℕ) := by positivity
  rw [noise_vector_sq a B hn]
  calc
    _  ≤  ((n^m:ℕ):ℝ)⁻¹ * ∑ _ : Point m n, 2*(m:ℝ)*ρ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn'.le)
      apply Finset.sum_le_sum
      intro x _
      have hb := character_noise_distance_le hρ1 (labelFunctional a x) B
      rw [character_noise_distance] at hb
      have hd : (degree (labelFunctional a x):ℝ) ≤ m := by exact_mod_cast labelFunctional_degree a x
      exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) hρ)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul]
      rw [← mul_assoc,inv_mul_cancel₀ hn'.ne',one_mul]

lemma weighted_expect_sq {T : Type*} [Fintype T] (w f : T → ℝ)
    (hw : ∀ t, 0 ≤ w t) (hw1 : (𝔼 t, w t)=1) :
    (𝔼 t, w t*f t)^2 ≤ 𝔼 t, w t*(f t)^2 := by
  let M := 𝔼 t, w t*f t
  have hz : 0 ≤ 𝔼 t, w t*(f t-M)^2 :=
    Finset.expect_nonneg (fun t _ => mul_nonneg (hw t) (sq_nonneg _))
  have he (t : T) : w t*(f t-M)^2=w t*(f t)^2-2*M*(w t*f t)+M^2*w t := by ring
  simp_rw [he,Finset.expect_add_distrib,Finset.expect_sub_distrib,← Finset.mul_expect,hw1,mul_one] at hz
  change 0 ≤ (𝔼 t, w t*(f t)^2)-2*M*M+M^2 at hz
  change M^2 ≤ _
  nlinarith only [hz]

lemma noise_vector_le (a : A) (B : FaceArray A m n) (hn : 0<n) (hm : 0 < m)
    {δ : ℝ} (hδ : 0 ≤ δ) (hρ1 : δ^2/(m:ℝ) ≤ 1) :
    (𝔼 C : FaceArray A m n, density (δ^2/(m:ℝ)) B C*
      ‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖) ≤ 2*δ := by
  have hρ : 0 ≤ δ^2/(m:ℝ) := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hs := weighted_expect_sq (density (δ^2/(m:ℝ)) B)
    (fun C => ‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖)
    (density_nonneg hρ hρ1 B) (density_mean _ B)
  have hb := noise_vector_sq_le a B hn hρ hρ1
  have hmp : (0:ℝ)< m := by exact_mod_cast hm
  have he : 2*(m:ℝ)*(δ^2/(m:ℝ))=2*δ^2 := by field_simp
  rw [he] at hb
  have hM : 0 ≤ 𝔼 C : FaceArray A m n, density (δ^2/(m:ℝ)) B C*
      ‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖ :=
    Finset.expect_nonneg (fun C _ => mul_nonneg (density_nonneg hρ hρ1 B C) (norm_nonneg _))
  have hs' := hs.trans hb
  exact (sq_le_sq₀ hM (by positivity)).mp (by nlinarith [sq_nonneg δ])
end MinUncut.Inner

end

end OAI
