import OAI.InformationTheory.Entanglement.HilbertTraceIdeal

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
open ContinuousLinearMap
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}
lemma positive_part_finite_sum_le (b : HilbertBasis ι ℂ H)
    {T A : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (hA : HasFinitePositiveTrace b A) (hTA : T≤A) (s : Finset ι) :
    (∑ j∈s, (inner ℂ (b j) (posPart T (b j))).re)≤hilbertTrace b A := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε/(s.card+1)
  have hd : 0<δ := div_pos hε (by positivity)
  let U := cfc (positiveSupportApprox δ) T
  obtain ⟨hu,hn,he⟩ := positiveSupportApprox_operator T hT hd
  change IsSelfAdjoint U at hu
  change ‖U‖≤1 at hn
  change ‖posPart T-U*T*U‖≤δ at he
  have hus : U.IsSymmetric := isSelfAdjoint_iff_isSymmetric.mp hu
  have hj (j : ι) : (inner ℂ (b j) (posPart T (b j))).re ≤
      (inner ℂ (U (b j)) (A (U (b j)))).re+δ := by
    have hn1 : ‖b j‖=1 := b.orthonormal.norm_eq_one j
    have hb : (inner ℂ (b j) ((posPart T-U*T*U) (b j))).re≤δ := by
      calc
        _ ≤ ‖inner ℂ (b j) ((posPart T-U*T*U) (b j))‖ := Complex.re_le_norm _
        _ ≤ ‖b j‖ * ‖(posPart T-U*T*U) (b j)‖ := norm_inner_le_norm _ _
        _ ≤ ‖b j‖ * (‖posPart T-U*T*U‖ * ‖b j‖) :=
          mul_le_mul_of_nonneg_left ((posPart T-U*T*U).le_opNorm _) (norm_nonneg _)
        _ ≤ δ := by simpa only [hn1,one_mul,mul_one] using he
    have ht : (inner ℂ (U (b j)) (T (U (b j)))).re≤
        (inner ℂ (U (b j)) (A (U (b j)))).re := by
      have hp := (nonneg_iff_isPositive.mp (sub_nonneg.mpr hTA)).re_inner_nonneg_right (U (b j))
      change 0≤(inner ℂ (U (b j)) ((A-T) (U (b j)))).re at hp
      simpa only [sub_apply,inner_sub_right,Complex.sub_re,sub_nonneg] using hp
    have hh : inner ℂ (b j) ((U*T*U) (b j))=inner ℂ (U (b j)) (T (U (b j))) := by
      exact (hus (b j) (T (U (b j)))).symm
    simp only [sub_apply,inner_sub_right,Complex.sub_re,hh] at hb
    linarith
  calc
    (∑ j∈s, (inner ℂ (b j) (posPart T (b j))).re) ≤
        ∑ j∈s, ((inner ℂ (U (b j)) (A (U (b j)))).re+δ) :=
      Finset.sum_le_sum (fun j _ => hj j)
    _ = (∑ j∈s, (inner ℂ (U (b j)) (A (U (b j)))).re)+s.card*δ := by
      rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
    _ ≤ hilbertTrace b A+s.card*δ :=
      add_le_add (positive_contraction_family_trace b hA U hus hn s) le_rfl
    _ ≤ hilbertTrace b A+ε := by
      apply add_le_add le_rfl
      have hfrac : δ*((s.card : ℝ)+1)=ε := (div_mul_cancel₀ ε (by positivity))
      nlinarith
lemma positive_part_finite_of_majorant (b : HilbertBasis ι ℂ H)
    {T A : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (hA : HasFinitePositiveTrace b A) (hTA : T≤A) :
    HasFinitePositiveTrace b (posPart T) ∧ hilbertTrace b (posPart T)≤hilbertTrace b A := by
  have hn (i : ι) : 0≤(inner ℂ (b i) (posPart T (b i))).re :=
    (nonneg_iff_isPositive.mp (CFC.posPart_nonneg T)).re_inner_nonneg_right _
  exact ⟨⟨CFC.posPart_nonneg T,summable_of_sum_le hn
    (positive_part_finite_sum_le b hT hA hTA)⟩,
    Real.tsum_le_of_sum_le hn (positive_part_finite_sum_le b hT hA hTA)⟩

theorem positive_difference_traceClass (b : HilbertBasis ι ℂ H)
    {A B : H →L[ℂ] H} (hA : HasFinitePositiveTrace b A)
    (hB : HasFinitePositiveTrace b B) :
    HermitianTraceClass b (A-B) ∧
      hilbertTraceNorm b (A-B)≤hilbertTrace b A+hilbertTrace b B := by
  have ht : IsSelfAdjoint (A-B) := hA.1.isSelfAdjoint.sub hB.1.isSelfAdjoint
  obtain ⟨hp,hp'⟩ := positive_part_finite_of_majorant b ht hA
    (sub_le_self A hB.1)
  obtain ⟨hn,hn'⟩ := positive_part_finite_of_majorant b ht.neg hB (show -(A-B)≤B by
    rw [neg_sub]; exact sub_le_self B hA.1)
  have he : posPart (-(A-B))=negPart (A-B) := CFC.posPart_neg (A-B)
  rw [he] at hn hn'
  have hab : HasFinitePositiveTrace b (CFC.abs (A-B)) := by
    rw [← CFC.posPart_add_negPart (A-B) ht]
    refine ⟨add_nonneg hp.1 hn.1,?_⟩
    simpa only [add_apply,inner_add_right,Complex.add_re] using hp.2.add hn.2
  refine ⟨⟨ht,hab⟩,?_⟩
  rw [hilbertTraceNorm_jordan b ⟨ht,hab⟩]
  exact add_le_add hp' hn'

end SecretKey

end

end OAI
