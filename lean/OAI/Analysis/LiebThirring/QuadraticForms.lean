import OAI.Analysis.LiebThirring.Gamma

namespace OAI

universe u166 u167 u168 u169 u170


noncomputable section
open Filter Set
open scoped Topology
namespace SharpLiebThirring.SpectralProof

lemma quadratic_error_bound {ι : Type u166} [Fintype ι] (M : ι → ι → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hM : ∀ i j, |M i j| ≤ ε) (c : ι → ℝ) :
    (∑ i, ∑ j, c i*c j*M i j) ≤ ε*(Fintype.card ι)*∑ i, c i^2 := by
  classical
  calc
    _ ≤ ∑ i, ∑ j, ε*(|c i| *|c j|) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      calc
        _ ≤ |c i*c j*M i j| := le_abs_self _
        _ = |c i| *|c j| *|M i j| := by rw [abs_mul,abs_mul]
        _ ≤ |c i| *|c j| *ε := mul_le_mul_of_nonneg_left (hM i j) (by positivity)
        _ = _ := by ring
    _ = ε*(∑ i, |c i|)^2 := by simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul,pow_two]
    _ ≤ ε*((Fintype.card ι)*∑ i, c i^2) := by
      apply mul_le_mul_of_nonneg_left _ hε
      simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,sq_abs] using
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι ↦ (1 : ℝ)) (fun i ↦ |c i|)
    _ = _ := by ring

/-- A strict negative diagonal is stable under entrywise perturbations. -/
lemma eventually_negative_quadratic {ι : Type u167} [Fintype ι] [DecidableEq ι] (M : ℕ → ι → ι → ℝ)
    (d : ι → ℝ) (hd : ∀ i, d i < 0)
    (hM : ∀ i j, Tendsto (fun n ↦ M n i j) atTop (𝓝 (if i=j then d i else 0))) :
    ∀ᶠ n in atTop, ∀ c : ι → ℝ, (∑ i, ∑ j, c i*c j*M n i j) ≤ 0 := by
  classical
  by_cases hi : IsEmpty ι
  · simp
  let : Nonempty ι := not_isEmpty_iff.mp hi
  obtain ⟨a,ha⟩ := Finite.exists_max d
  let ε := -d a/((Fintype.card ι : ℝ)+1)
  have he : 0 < ε := div_pos (neg_pos.mpr (hd a)) (by positivity)
  have hε : ε*(Fintype.card ι : ℝ) ≤ -d a := by
    have hh : ε*((Fintype.card ι : ℝ)+1) = -d a := by dsimp [ε]; field_simp
    nlinarith
  have hev : ∀ᶠ n in atTop, ∀ i j, |M n i j-(if i=j then d i else 0)| ≤ ε := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    exact ((tendsto_order.1 (((hM i j).sub_const (if i=j then d i else 0)).abs)).2 ε (by simpa using he)).mono
      (fun n hn ↦ le_of_lt (by simpa using hn))
  filter_upwards [hev] with n hn c
  have hb := quadratic_error_bound (fun i j ↦ M n i j-(if i=j then d i else 0)) he.le hn c
  have hid : (∑ i, ∑ j, c i*c j*(if i=j then d i else 0)) = ∑ i, c i^2*d i := by
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_ite,pow_two]
  have hsplit : (∑ i, ∑ j, c i*c j*M n i j) =
      (∑ i, ∑ j, c i*c j*(M n i j-(if i=j then d i else 0))) + ∑ i, c i^2*d i := by
    rw [← hid,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hsplit]
  have hd' : (∑ i, c i^2*d i) ≤ d a*∑ i, c i^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    exact (mul_le_mul_of_nonneg_left (ha i) (sq_nonneg _)).trans_eq (mul_comm _ _)
  have hs : 0 ≤ ∑ i, c i^2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hε hs]

end SharpLiebThirring.SpectralProof

end


noncomputable section
open Module
namespace SharpLiebThirring.SpectralProof

variable {E : Type u168} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Complex orthonormal vectors give twice as many real orthonormal vectors. -/
lemma doubled_orthonormal {ι : Type u169} [DecidableEq ι] (a b : ι → E)
    (hr : ∀ i j, inner ℝ (a i) (a j)+inner ℝ (b i) (b j) = if i=j then 1 else 0)
    (hi : ∀ i j, inner ℝ (a i) (b j)-inner ℝ (b i) (a j) = 0) :
    Orthonormal ℝ (fun z : ι × Bool ↦
      WithLp.toLp 2 (if z.2 then (-b z.1,a z.1) else (a z.1,b z.1))) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i,p⟩ ⟨j,q⟩
  cases p <;> cases q <;>
    simp only [Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,WithLp.prod_inner_apply,
      inner_neg_left,inner_neg_right,neg_neg,
      Prod.mk.injEq,and_true,and_false,ite_false]
  · exact hr i j
  · linarith [hi i j]
  · linarith [hi j i,real_inner_comm (a j) (b i),real_inner_comm (b j) (a i)]
  · simpa only [add_comm] using hr i j

lemma complex_family_card_le_real_dimension {ι : Type u170} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ E] (a b : ι → E)
    (hr : ∀ i j, inner ℝ (a i) (a j)+inner ℝ (b i) (b j) = if i=j then 1 else 0)
    (hi : ∀ i j, inner ℝ (a i) (b j)-inner ℝ (b i) (a j) = 0) :
    Fintype.card ι ≤ finrank ℝ E := by
  have h := (doubled_orthonormal a b hr hi).linearIndependent.fintype_card_le_finrank
  rw [(WithLp.linearEquiv 2 ℝ (E×E)).finrank_eq,finrank_prod] at h
  simp only [Fintype.card_prod,Fintype.card_bool] at h
  omega

end SharpLiebThirring.SpectralProof

end

end OAI
