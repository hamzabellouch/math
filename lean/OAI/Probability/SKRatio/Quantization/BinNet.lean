import Mathlib
import OAI.Probability.SKRatio.Quantization.BinFunctional

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma norm_of_sum_sq_one {p : Fin n → ℝ} (hp : ∑ i, p i^2=1) :
    ‖WithLp.toLp 2 p‖=1 := by
  have he := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 p)
  simp only [hp] at he
  nlinarith only [he,norm_nonneg (WithLp.toLp 2 p)]

lemma quadratic_vector_difference (M : Matrix (Fin n) (Fin n) ℝ)
    {p q : Fin n → ℝ} (hp : ∑ i, p i^2=1) (hq : ∑ i, q i^2=1) :
    |quadratic M p-quadratic M q| ≤
      2*euclideanOpNorm M*‖WithLp.toLp 2 (fun i => p i-q i)‖ := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) M
  let P : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 p
  let Q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 q
  have hP : ‖P‖=1 := norm_of_sum_sq_one hp
  have hQ : ‖Q‖=1 := norm_of_sum_sq_one hq
  have he : inner ℝ P (A P)-inner ℝ Q (A Q) =
      inner ℝ (P-Q) (A P)+inner ℝ Q (A (P-Q)) := by
    simp only [map_sub,inner_sub_left,inner_sub_right]
    ring
  rw [quadratic_inner,quadratic_inner]
  change |inner ℝ P (A P)-inner ℝ Q (A Q)|≤_
  rw [he]
  have h1 := (abs_real_inner_le_norm (P-Q) (A P)).trans
    (mul_le_mul_of_nonneg_left (A.le_opNorm P) (norm_nonneg _))
  have h2 := (abs_real_inner_le_norm Q (A (P-Q))).trans
    (mul_le_mul_of_nonneg_left (A.le_opNorm (P-Q)) (norm_nonneg _))
  rw [hP] at h1
  rw [hQ] at h2
  have ht := abs_add_le (inner ℝ (P-Q) (A P)) (inner ℝ Q (A (P-Q)))
  change |inner ℝ (P-Q) (A P)+inner ℝ Q (A (P-Q))|≤2*‖A‖*‖P-Q‖
  nlinarith only [ht,h1,h2]

lemma variance_bilinear_difference (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : ∀ i, |v i|≤1)
    {p q : Fin n → ℝ} (hp : ∑ i, p i^2=1) (hq : ∑ i, q i^2=1) :
    |p ⬝ᵥ (M*ᵥ(fun i => v i*p i))-q ⬝ᵥ (M*ᵥ(fun i => v i*q i))|≤
      2*euclideanOpNorm M*‖WithLp.toLp 2 (fun i => p i-q i)‖ := by
  have he (p : Fin n → ℝ) : p ⬝ᵥ (M*ᵥ(fun i => v i*p i))=
      quadratic (M*Matrix.diagonal v) p := by
    simp only [quadratic,Matrix.mul_diagonal,dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,he]
  apply (quadratic_vector_difference _ hp hq).trans
  have hd := matrix_diagonal_opNorm_le v 1 (by norm_num) hv
  have hn : euclideanOpNorm (M*Matrix.diagonal v)≤euclideanOpNorm M := by
    unfold euclideanOpNorm
    rw [map_mul]
    exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans_eq (mul_one _))
  gcongr

abbrev WeightBox (α : Type*) := α → Set.Icc (0:ℝ) 1

lemma binT_le_one [Nonempty (Fin n)] (σ : Fin n → α) (a : α) : binT σ a≤1 := by
  have hs : binT σ a^2≤1 := by
    rw [←binT_unit σ]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (binT σ i)) (Finset.mem_univ a)
  nlinarith only [hs]

def binBox [Nonempty (Fin n)] (σ : Fin n → α) : WeightBox α :=
  fun a => ⟨binT σ a,binT_nonneg σ a,binT_le_one σ a⟩

omit [DecidableEq α] in
lemma finiteA_parameter_tolerance (β : ℝ) (h : α → ℝ) {a : ℝ} (ha : 0<a) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (t : WeightBox α) (z z' : Parameters α),
      ‖z.val-z'.val‖<δ →
      |finiteA β (fun d => t d) h z-finiteA β (fun d => t d) h z'|<a := by
  have hc : Continuous (fun q : WeightBox α × Parameters α =>
      finiteA β (fun d => q.1 d) h q.2) := by
    unfold finiteA moment
    have hb (d : α) := (continuous_paramB d).comp (continuous_snd (X := WeightBox α))
    have hr (d : α) := (continuous_paramR d).comp (continuous_snd (X := WeightBox α))
    have ht (d : α) : Continuous (fun q : WeightBox α × Parameters α => (q.1 d:ℝ)) :=
      continuous_subtype_val.comp ((continuous_apply d).comp continuous_fst)
    fun_prop
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) a ha
  refine ⟨δ,hδ,fun t z z' hh => ?_⟩
  apply hcont (a := (t,z)) (b := (t,z'))
  simp only [Prod.dist_eq,dist_self,Subtype.dist_eq,dist_eq_norm,max_lt_iff]
  exact ⟨hδ,hh⟩

theorem binForm_finite_net (β : ℝ) (h : α → ℝ) {K a : ℝ} (hK : 0≤K) (ha : 0<a) :
    ∃ F : Finset (Parameters α), ∀ {n : ℕ} (_ : 0<n) (σ : Fin n → α),
      (∀ d, 2≤count σ d) → ∀ M : Matrix (Fin n) (Fin n) ℝ,
      euclideanOpNorm M≤K → ∀ (z : Parameters α) (u : Directions σ),
      ∃ z' ∈ F,
        (vectorOf z u) ⬝ᵥ (M*ᵥ(fun i => v (h (σ i))*vectorOf z u i))+
            finiteA β (binT σ) h z ≤
          (vectorOf z' u) ⬝ᵥ (M*ᵥ(fun i => v (h (σ i))*vectorOf z' u i))+
            finiteA β (binT σ) h z'+a := by
  obtain ⟨δ,hδ,hA⟩ := finiteA_parameter_tolerance β h (show 0<a/2 by positivity)
  let η := min δ (a/(4*K+1))
  have hη : 0<η := lt_min hδ (by positivity)
  obtain ⟨F,hF⟩ := parameters_finite_net (α := α) hη
  refine ⟨F,?_⟩
  intro n hn σ hc M hM z u
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hc' : ∀ d, 0<count σ d := fun d => lt_of_lt_of_le (by norm_num) (hc d)
  obtain ⟨z',hz',hnear⟩ := hF z
  refine ⟨z',hz',?_⟩
  have hA' := (le_abs_self _).trans (hA (binBox σ) z z' (hnear.trans_le (min_le_left _ _))).le
  have hdiff := variance_bilinear_difference M (fun i => v (h (σ i)))
    (fun i => by rw [abs_of_nonneg (v_pos _).le]; exact v_le_one _)
    (vectorOf_unit hc' z u) (vectorOf_unit hc' z' u)
  rw [vectorOf_difference hc'] at hdiff
  have hkd := mul_le_mul_of_nonneg_right hM (norm_nonneg (z.val-z'.val))
  have hηd := (lt_div_iff₀ (by positivity : 0<4*K+1)).mp (hnear.trans_le (min_le_right _ _))
  have habs := le_abs_self ((vectorOf z u) ⬝ᵥ (M*ᵥ (fun i => v (h (σ i))*vectorOf z u i))-
    (vectorOf z' u) ⬝ᵥ (M*ᵥ (fun i => v (h (σ i))*vectorOf z' u i)))
  change finiteA β (binT σ) h z-finiteA β (binT σ) h z'≤a/2 at hA'
  nlinarith only [habs,hdiff,hkd,hηd,hA',norm_nonneg (z.val-z'.val)]

end SKRatio.Bins

end

end OAI
