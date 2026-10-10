import OAI.InformationTheory.Entanglement.HilbertTrace

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
open ContinuousLinearMap
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι κ : Type*}

omit [CompleteSpace H] in
lemma symmetric_bessel_trace (b : HilbertBasis ι ℂ H) (S : H →L[ℂ] H)
    (hS : S.IsSymmetric) (hi : Summable (fun i => ‖S (b i)‖^2))
    (v : κ → H) (s : Finset κ) (hv : ∀ x, ∑ j∈s, ‖inner ℂ (v j) x‖^2≤‖x‖^2) :
    ∑ j∈s, ‖S (v j)‖^2≤∑' i, ‖S (b i)‖^2 := by
  have he (j : κ) : HasSum (fun i => ‖inner ℂ (v j) (S (b i))‖^2) (‖S (v j)‖^2) := by
    convert hilbert_parseval b (S (v j)) using 1
    ext i
    have h := hS (b i) (v j)
    change inner ℂ (S (b i)) (v j)=inner ℂ (b i) (S (v j)) at h
    rw [← h,norm_inner_symm]
  calc
    ∑ j∈s, ‖S (v j)‖^2=∑ j∈s, ∑' i, ‖inner ℂ (v j) (S (b i))‖^2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (he j).tsum_eq.symm
    _ = ∑' i, ∑ j∈s, ‖inner ℂ (v j) (S (b i))‖^2 :=
      ((fun j (_ : j∈s) => (he j).summable) |> Summable.tsum_finsetSum).symm
    _ ≤ ∑' i, ‖S (b i)‖^2 :=
      Summable.tsum_le_tsum (fun i => hv (S (b i)))
        (hasSum_sum (s := s) (fun j _ => he j)).summable hi
lemma positive_contraction_family_trace (b : HilbertBasis ι ℂ H)
    {A : H →L[ℂ] H} (hA : HasFinitePositiveTrace b A)
    (U : H →L[ℂ] H) (hU : U.IsSymmetric) (hn : ‖U‖≤1) (s : Finset ι) :
    ∑ j∈s, (inner ℂ (U (b j)) (A (U (b j)))).re≤hilbertTrace b A := by
  have hi : Summable (fun i => ‖CFC.sqrt A (b i)‖^2) := by
    simpa only [← positive_diagonal_sqrt hA.1] using hA.2
  have hb (x : H) : (∑ j∈s, ‖inner ℂ (U (b j)) x‖^2)≤‖x‖^2 := by
    have he (j : ι) : inner ℂ (U (b j)) x=inner ℂ (b j) (U x) := hU _ _
    simp only [he]
    calc
      (∑ j∈s, ‖inner ℂ (b j) (U x)‖^2)≤‖U x‖^2 := b.orthonormal.sum_inner_products_le _
      _ ≤ ‖x‖^2 := by
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (U.le_opNorm x).trans (by nlinarith [norm_nonneg x])
  have h := symmetric_bessel_trace b (CFC.sqrt A)
    (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg A)).isSymmetric hi (fun i => U (b i)) s hb
  simpa only [← positive_diagonal_sqrt hA.1,hilbertTrace] using h

def positiveSupportApprox (ε : ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (max x 0/(max x 0+ε))
lemma positiveSupportApprox_continuous {ε : ℝ} (hε : 0<ε) :
    Continuous (positiveSupportApprox ε) := by
  exact ((continuous_id.max continuous_const).div
    ((continuous_id.max continuous_const).add continuous_const)
    (fun x => (add_pos_of_nonneg_of_pos (le_max_right x 0) hε).ne')).sqrt
lemma positiveSupportApprox_norm {ε : ℝ} (hε : 0<ε) (x : ℝ) :
    ‖positiveSupportApprox ε x‖≤1 := by
  unfold positiveSupportApprox
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_one.mpr
  exact (div_le_one (add_pos_of_nonneg_of_pos (le_max_right x 0) hε)).mpr (by linarith)
lemma positiveSupportApprox_error {ε : ℝ} (hε : 0<ε) (x : ℝ) :
    ‖max x 0-positiveSupportApprox ε x*x*positiveSupportApprox ε x‖≤ε := by
  have hs : (positiveSupportApprox ε x)^2=max x 0/(max x 0+ε) :=
    Real.sq_sqrt (div_nonneg (le_max_right x 0) (by linarith [le_max_right x 0]))
  have hd : 0 < (max x 0 + ε) := add_pos_of_nonneg_of_pos (le_max_right x 0) hε
  have he : (positiveSupportApprox ε x)^2*(max x 0+ε)=max x 0 :=
    (eq_div_iff hd.ne').mp hs
  have hn := positiveSupportApprox_norm hε x
  rw [Real.norm_eq_abs] at hn ⊢
  have hns := abs_le.mp hn
  by_cases hx : 0≤x
  · rw [max_eq_left hx] at he ⊢
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (positiveSupportApprox ε x)]
  · have hm : max x 0=0 := max_eq_right (le_of_not_ge hx)
    simp [positiveSupportApprox,hm,hε.le]
lemma positiveSupportApprox_operator (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    {ε : ℝ} (hε : 0<ε) :
    let U := cfc (positiveSupportApprox ε) T
    IsSelfAdjoint U ∧ ‖U‖≤1 ∧ ‖posPart T-U*T*U‖≤ε := by
  dsimp only
  refine ⟨cfc_predicate _ _,norm_cfc_le (by norm_num) (fun x _ => positiveSupportApprox_norm hε x),?_⟩
  have hc : ContinuousOn (positiveSupportApprox ε) (spectrum ℝ T) :=
    (positiveSupportApprox_continuous hε).continuousOn
  have hm : cfc (fun x => positiveSupportApprox ε x*x*positiveSupportApprox ε x) T=
      cfc (positiveSupportApprox ε) T*T*cfc (positiveSupportApprox ε) T := by
    rw [cfc_mul (fun x => positiveSupportApprox ε x*x) (positiveSupportApprox ε) T
      ((positiveSupportApprox_continuous hε).mul continuous_id).continuousOn hc,
      cfc_mul (positiveSupportApprox ε) (fun x : ℝ => x) T hc continuous_id.continuousOn]
    change cfc (positiveSupportApprox ε) T * cfc (id : ℝ → ℝ) T *
      cfc (positiveSupportApprox ε) T = _
    rw [cfc_id ℝ T hT]
  have hp : cfc (fun x : ℝ => max x 0) T=posPart T := by
    rw [CFC.posPart_def,cfcₙ_eq_cfc]
    rfl
  have he : posPart T-cfc (positiveSupportApprox ε) T*T*cfc (positiveSupportApprox ε) T=
      cfc (fun x => max x 0-positiveSupportApprox ε x*x*positiveSupportApprox ε x) T := by
    rw [cfc_sub (fun x : ℝ => max x 0)
      (fun x : ℝ => positiveSupportApprox ε x*x*positiveSupportApprox ε x) T
      (continuous_id.max continuous_const).continuousOn
      (((positiveSupportApprox_continuous hε).mul continuous_id).mul
        (positiveSupportApprox_continuous hε)).continuousOn,hp,hm]
  rw [he]
  exact norm_cfc_le hε.le (fun x _ => positiveSupportApprox_error hε x)
end SecretKey

end

end OAI
