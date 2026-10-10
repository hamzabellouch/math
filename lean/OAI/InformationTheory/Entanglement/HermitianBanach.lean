import OAI.InformationTheory.Entanglement.TraceStateBounds

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap Filter
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}
lemma hermitianTraceClass_real_smul (b : HilbertBasis ι ℂ H) (r : ℝ)
    {A : H→L[ℂ]H} (hA : HermitianTraceClass b A) : HermitianTraceClass b (r • A) := by
  refine ⟨(show IsSelfAdjoint r by simp [IsSelfAdjoint]).smul hA.1,?_⟩
  rw [CFC.abs_smul]
  refine ⟨smul_nonneg (norm_nonneg r) hA.2.1,?_⟩
  change Summable (fun i => (inner ℂ (b i) (((‖r‖ : ℝ) : ℂ) • CFC.abs A (b i))).re)
  simpa only [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    using hA.2.2.mul_left ‖r‖
lemma hilbertTraceNorm_real_smul (b : HilbertBasis ι ℂ H) (r : ℝ) (A : H→L[ℂ]H) :
    hilbertTraceNorm b (r • A)=‖r‖*hilbertTraceNorm b A := by
  rw [hilbertTraceNorm,CFC.abs_smul]
  change (∑' i, (inner ℂ (b i) (((‖r‖ : ℝ) : ℂ) • CFC.abs A (b i))).re)=_
  simp only [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact tsum_mul_left
lemma hilbertTraceNorm_nonneg (b : HilbertBasis ι ℂ H) (A : H→L[ℂ]H) :
    0≤hilbertTraceNorm b A := by
  exact tsum_nonneg (fun i => (nonneg_iff_isPositive.mp (CFC.abs_nonneg A)).re_inner_nonneg_right _)
lemma opNorm_le_traceNorm (b : HilbertBasis ι ℂ H) {A : H→L[ℂ]H}
    (hA : HermitianTraceClass b A) : ‖A‖≤hilbertTraceNorm b A := by
  simpa only [CFC.norm_abs,hilbertTraceNorm] using positive_opNorm_le_trace b hA.2

def hermitianTraceSpace (b : HilbertBasis ι ℂ H) : Submodule ℝ (H→L[ℂ]H) where
  carrier := {A | HermitianTraceClass b A}
  zero_mem' := by simp [HermitianTraceClass,HasFinitePositiveTrace]
  add_mem' hA hB := (hilbertTraceNorm_triangle b hA hB).1
  smul_mem' r A hA := hermitianTraceClass_real_smul b r hA

def HermitianTrace (b : HilbertBasis ι ℂ H) : Type _ := ↥(hermitianTraceSpace b)
namespace HermitianTrace
variable (b : HilbertBasis ι ℂ H)
instance hermitianTraceAddCommGroup : AddCommGroup (HermitianTrace b) := inferInstanceAs (AddCommGroup (hermitianTraceSpace b))
instance hermitianTraceModule : Module ℝ (HermitianTrace b) := inferInstanceAs (Module ℝ (hermitianTraceSpace b))
def operator (A : HermitianTrace b) : H→L[ℂ]H := A.val
lemma property (A : HermitianTrace b) : HermitianTraceClass b (operator b A) := Subtype.property A
instance hermitianTraceNorm : Norm (HermitianTrace b) := ⟨fun A => hilbertTraceNorm b (operator b A)⟩
@[simp] lemma operator_add (A B : HermitianTrace b) : operator b (A+B)=operator b A+operator b B := rfl
@[simp] lemma operator_sub (A B : HermitianTrace b) : operator b (A-B)=operator b A-operator b B := rfl
@[simp] lemma operator_smul (r : ℝ) (A : HermitianTrace b) : operator b (r • A)=r • operator b A := rfl
@[simp] lemma operator_zero : operator b 0=0 := rfl
lemma norm_eq (A : HermitianTrace b) : ‖A‖=hilbertTraceNorm b (operator b A) := rfl
lemma core : NormedSpace.Core ℝ (HermitianTrace b) where
  norm_nonneg A := hilbertTraceNorm_nonneg b _
  norm_smul r A := hilbertTraceNorm_real_smul b r _
  norm_triangle A B := (hilbertTraceNorm_triangle b (property b A) (property b B)).2
  norm_eq_zero_iff A := by
    constructor
    · intro h
      apply Subtype.ext
      apply norm_eq_zero.mp
      exact le_antisymm (h ▸ opNorm_le_traceNorm b (property b A)) (norm_nonneg _)
    · intro h; rw [h]; simp [norm_eq,hilbertTraceNorm,hilbertTrace]
instance hermitianTraceNormedAddCommGroup : NormedAddCommGroup (HermitianTrace b) := NormedAddCommGroup.ofCore (core b)
instance hermitianTraceNormedSpace : NormedSpace ℝ (HermitianTrace b) := NormedSpace.ofCore (core b)

def inclusion : HermitianTrace b →L[ℝ] H→L[ℂ]H :=
  ({ toFun := operator b
     map_add' := operator_add b
     map_smul' := fun r A => operator_smul b r A } : HermitianTrace b →ₗ[ℝ] H→L[ℂ]H).mkContinuous 1
    (fun A => by
      change ‖operator b A‖ ≤ 1 * hilbertTraceNorm b (operator b A)
      simpa only [one_mul] using opNorm_le_traceNorm b (property b A))
end HermitianTrace

lemma traceNorm_fatou_bound (b : HilbertBasis ι ℂ H) {A : ℕ→H→L[ℂ]H} {T : H→L[ℂ]H}
    (hlim : Tendsto A atTop (nhds T)) (hA : ∀ n, HermitianTraceClass b (A n))
    {C : ℝ} (hC : ∀ᶠ n in atTop, hilbertTraceNorm b (A n)≤C) :
    HermitianTraceClass b T ∧ hilbertTraceNorm b T≤C := by
  have hself : IsSelfAdjoint T := by
    have hs := hlim.star
    exact tendsto_nhds_unique hs (hlim.congr' (Filter.Eventually.of_forall (fun n => (hA n).1.star_eq.symm)))
  have hnorm : Tendsto (fun n => CFC.abs (A n)) atTop (nhds (CFC.abs T)) :=
    CFC.continuous_abs.continuousAt.tendsto.comp hlim
  have hdiag (i : ι) : Tendsto (fun n => (inner ℂ (b i) (CFC.abs (A n) (b i))).re)
      atTop (nhds (inner ℂ (b i) (CFC.abs T (b i))).re) := by
    exact Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_const_nhds.inner ((ContinuousLinearMap.apply ℂ H (b i)).continuous.continuousAt.tendsto.comp hnorm))
  have hn (i : ι) : 0≤(inner ℂ (b i) (CFC.abs T (b i))).re :=
    (nonneg_iff_isPositive.mp (CFC.abs_nonneg T)).re_inner_nonneg_right _
  have hbound (s : Finset ι) : ∑ i∈s, (inner ℂ (b i) (CFC.abs T (b i))).re≤C := by
    apply le_of_tendsto (tendsto_finsetSum s (fun i hi => hdiag i))
    filter_upwards [hC] with n hn
    exact ((hA n).2.2.sum_le_tsum s (fun i hi =>
      (nonneg_iff_isPositive.mp (CFC.abs_nonneg (A n))).re_inner_nonneg_right _)).trans hn
  exact ⟨⟨hself, CFC.abs_nonneg T, summable_of_sum_le hn hbound⟩,
    Real.tsum_le_of_sum_le hn hbound⟩
namespace HermitianTrace
variable (b : HilbertBasis ι ℂ H)

instance completeSpace : CompleteSpace (HermitianTrace b) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨T,hT⟩ := cauchySeq_tendsto_of_complete ((inclusion b).uniformContinuous.comp_cauchySeq hu)
  change Tendsto (fun n => operator b (u n)) atTop (nhds T) at hT
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hu 1 zero_lt_one
  have hbound : ∀ᶠ n in atTop, hilbertTraceNorm b (operator b (u n)) ≤ ‖u N‖+1 := by
    filter_upwards [eventually_ge_atTop N] with n hn
    change ‖u n‖ ≤ ‖u N‖+1
    have hh := hN n hn N le_rfl
    rw [dist_eq_norm] at hh
    simpa only [sub_add_cancel] using (norm_add_le (u n-u N) (u N)).trans
      (by linarith : ‖u n-u N‖+‖u N‖≤‖u N‖+1)
  have hTC := traceNorm_fatou_bound b hT (fun n => property b (u n)) hbound
  let t : HermitianTrace b := ⟨T,hTC.1⟩
  refine ⟨t,Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨M,hM⟩ := Metric.cauchySeq_iff.mp hu (ε/2) (by positivity)
  refine ⟨M,fun m hm => ?_⟩
  have hdiff : Tendsto (fun n => operator b (u n)-operator b (u m)) atTop
      (nhds (T-operator b (u m))) := hT.sub_const _
  have hsmall : ∀ᶠ n in atTop, hilbertTraceNorm b (operator b (u n)-operator b (u m)) ≤ ε/2 := by
    filter_upwards [eventually_ge_atTop M] with n hn
    change ‖u n-u m‖≤ε/2
    simpa only [dist_eq_norm] using (hM n hn m hm).le
  have hlim := (traceNorm_fatou_bound b hdiff (fun n => property b (u n-u m)) hsmall).2
  have : ‖t-u m‖≤ε/2 := hlim
  rw [dist_comm,dist_eq_norm]
  exact this.trans_lt (by linarith)
end HermitianTrace

end SecretKey

end

end OAI
