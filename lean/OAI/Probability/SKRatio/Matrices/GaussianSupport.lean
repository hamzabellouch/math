import Mathlib
import OAI.Probability.SKRatio.FiniteChain.Mean
import OAI.Probability.SKRatio.Matrices.Spin
import OAI.Probability.SKRatio.Matrices.MatrixCoordinates
import OAI.Probability.SKRatio.Matrices.GaussianCoordinates

namespace OAI

section
section

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKRatioGaussian.GaussianRegression

theorem law_eq_of_mean_covariance {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {P' : Measure Ω'} {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P')
    (hm : ∀ i, (∫ w, X w i ∂P) = ∫ w, Y w i ∂P')
    (hc : ∀ i k, cov[fun w => X w i, fun w => X w k; P] =
      cov[fun w => Y w i, fun w => Y w k; P']) :
    P.map X = P'.map Y := by
  classical
  have := hX.isProbabilityMeasure
  have := hY.isProbabilityMeasure
  apply Measure.ext_of_charFunDual
  ext L
  rw [hX.charFunDual_map_eq,hY.charFunDual_map_eq]
  let c : ι → ℝ := fun i => L (fun k => if i=k then 1 else 0)
  have hL (x : ι → ℝ) : L x = ∑ i, x i * c i := by
    simpa only [c, smul_eq_mul, ContinuousLinearMap.coe_coe] using L.toLinearMap.pi_apply_eq_sum_univ x
  have hLX : L ∘ X = fun w => ∑ i, X w i*c i := funext (fun w => hL (X w))
  have hLY : L ∘ Y = fun w => ∑ i, Y w i*c i := funext (fun w => hL (Y w))
  have hiX (i : ι) := (hX.eval i).memLp_two
  have hiY (i : ι) := (hY.eval i).memLp_two
  have hem : (∫ w, (L ∘ X) w ∂P) = ∫ w, (L ∘ Y) w ∂P' := by
    rw [hLX,hLY]
    rw [integral_finsetSum _ (fun i _ => ((hX.eval i).integrable.mul_const _)),
      integral_finsetSum _ (fun i _ => ((hY.eval i).integrable.mul_const _))]
    simp only [integral_mul_const,hm]
  have hev : Var[L ∘ X; P] = Var[L ∘ Y; P'] := by
    rw [← covariance_self (hX.map L).aemeasurable,
      ← covariance_self (hY.map L).aemeasurable]
    rw [hLX,hLY]
    rw [covariance_fun_sum_fun_sum (fun i => (hiX i).mul_const _) (fun i => (hiX i).mul_const _),
      covariance_fun_sum_fun_sum (fun i => (hiY i).mul_const _) (fun i => (hiY i).mul_const _)]
    simp only [covariance_mul_const_left,covariance_mul_const_right,hc]
  rw [hev,hem]

def matrixCLM {ι κ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) :
    (κ → ℝ) →L[ℝ] (ι → ℝ) := A.mulVecLin.toContinuousLinearMap

@[simp] lemma matrixCLM_apply {ι κ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) (x : κ → ℝ) :
    matrixCLM A x = A *ᵥ x := rfl

theorem residual_independent {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P) (K : Matrix ι κ ℝ)
    (hcov : ∀ i k, cov[fun w => X w i, fun w => Y w k; P] =
      ∑ l, K i l * cov[fun w => Y w l,fun w => Y w k; P]) :
    IndepFun (fun w => X w-K*ᵥ Y w) Y P := by
  have := hXY.isProbabilityMeasure
  have hR : HasGaussianLaw (fun w => (X w-K*ᵥ Y w,Y w)) P := by
    exact hXY.map_fun (((ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ))-
      (matrixCLM K).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ))).prod
      (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ)))
  apply hR.indepFun_of_covariance_eval
  intro i k
  change cov[fun w => X w i-∑ l, K i l*Y w l,fun w => Y w k; P]=0
  have hK : MemLp (fun w => ∑ l, K i l*Y w l) 2 P :=
    ((hXY.snd.map (matrixCLM K)).eval i).memLp_two
  rw [covariance_fun_sub_left (hXY.fst.eval i).memLp_two hK (hXY.snd.eval k).memLp_two]
  rw [covariance_fun_sum_left (fun l => (hXY.snd.eval l).memLp_two.const_mul _)
    (hXY.snd.eval k).memLp_two]
  simp only [covariance_const_mul_left,hcov,sub_self]

end SKRatioGaussian.GaussianRegression
end
end

section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal

lemma coordinate_hasLaw {κ : Type*} [Fintype κ] (i : κ) :
    HasLaw (fun g : κ → ℝ => g i) (gaussianReal 0 1) (gaussianCoordinates κ) :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) i).map_eq⟩

lemma coordinates_gaussian {κ : Type*} [Fintype κ] :
    HasGaussianLaw (fun g : κ → ℝ => g) (gaussianCoordinates κ) :=
  (iIndepFun_pi (fun _ : κ => aemeasurable_id)).hasGaussianLaw
    (fun i => (coordinate_hasLaw i).hasGaussianLaw)

lemma coordinate_covariance {κ : Type*} [Fintype κ] [DecidableEq κ] (i k : κ) :
    cov[fun g : κ → ℝ => g i,fun g : κ → ℝ => g k;gaussianCoordinates κ] =
      if i=k then 1 else 0 := by
  by_cases h : i=k
  · subst k
    rw [ite_eq_left rfl,covariance_self (measurable_pi_apply i).aemeasurable,
      (coordinate_hasLaw i).variance_eq]
    simp
  · rw [ite_eq_right h]
    exact ((iIndepFun_pi (fun _ : κ => aemeasurable_id)).indepFun h).covariance_eq_zero
      (coordinate_hasLaw i).hasGaussianLaw.memLp_two (coordinate_hasLaw k).hasGaussianLaw.memLp_two

lemma linear_gaussian_mean {κ : Type*} [Fintype κ] (a : κ → ℝ) :
    (∫ g, ∑ i, a i*g i ∂gaussianCoordinates κ) = 0 := by
  rw [integral_finsetSum _ (fun i _ => (coordinate_hasLaw i).hasGaussianLaw.integrable.const_mul _)]
  simp [integral_const_mul,(coordinate_hasLaw _).integral_eq]

lemma linear_gaussian_covariance {κ : Type*} [Fintype κ] [DecidableEq κ] (a b : κ → ℝ) :
    cov[fun g => ∑ i, a i*g i,fun g => ∑ i, b i*g i;gaussianCoordinates κ] =
      ∑ i, a i*b i := by
  rw [covariance_fun_sum_fun_sum
    (fun i => (coordinate_hasLaw i).hasGaussianLaw.memLp_two.const_mul _)
    (fun i => (coordinate_hasLaw i).hasGaussianLaw.memLp_two.const_mul _)]
  simp only [covariance_const_mul_left,covariance_const_mul_right,coordinate_covariance]
  simp [mul_comm]

lemma matrix_sample_gaussian {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) :
    HasGaussianLaw (fun g => A*ᵥg) (gaussianCoordinates κ) :=
  coordinates_gaussian.map_fun (GaussianRegression.matrixCLM A)

lemma matrix_sample_covariance {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (i k : ι) :
    cov[fun g => (A*ᵥg) i,fun g => (A*ᵥg) k;gaussianCoordinates κ] = (A*Aᵀ) i k :=
  linear_gaussian_covariance (A i) (A k)

end SKRatioGaussian
end
end

section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goeEntryCoeff (r : ℝ) : Matrix (ι × ι) (MatrixCoordinates ι) ℝ :=
  fun p a => sqrt (2*r)/2 * ((if a=Sum.inl p then 1 else 0)+
    (if a=Sum.inl (p.2,p.1) then 1 else 0))

lemma goeEntryCoeff_sample (r : ℝ) (g : MatrixCoordinates ι → ℝ) (i k : ι) :
    (goeEntryCoeff r*ᵥg) (i,k) = goeMatrix r g i k := by
  simp only [mulVec,dotProduct,goeEntryCoeff,mul_assoc,add_mul]
  rw [← Finset.mul_sum,Finset.sum_add_distrib]
  simp [goeMatrix]

lemma goe_matrix_gaussian (r : ℝ) :
    HasGaussianLaw (fun (g : MatrixCoordinates ι → ℝ) (p : ι × ι) => goeMatrix r g p.1 p.2) (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := matrix_sample_gaussian (goeEntryCoeff (ι := ι) r)
  simpa only [show (fun g => goeEntryCoeff (ι := ι) r*ᵥg) =
    (fun g p => goeMatrix r g p.1 p.2) from funext (fun g => funext (fun p => goeEntryCoeff_sample r g p.1 p.2))] using hh

lemma goe_mean_zero (r : ℝ) (i k : ι) :
    (∫ g, goeMatrix r g i k ∂gaussianCoordinates (MatrixCoordinates ι))=0 := by
  simpa only [← goeEntryCoeff_sample,mulVec,dotProduct] using linear_gaussian_mean (goeEntryCoeff (ι := ι) r (i,k))

lemma goe_entry_cov {r : ℝ} (hr : 0 ≤ r) (i k l m : ι) :
    cov[fun g => goeMatrix r g i k,fun g => goeMatrix r g l m;
      gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then 1 else 0)*(if k=m then 1 else 0)+
       (if i=m then 1 else 0)*(if k=l then 1 else 0)) := by
  let μ := gaussianCoordinates (MatrixCoordinates ι)
  have hm (a : MatrixCoordinates ι) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  change cov[fun g : MatrixCoordinates ι → ℝ => sqrt (2*r)/2*(g (.inl (i,k))+g (.inl (k,i))),
    fun g => sqrt (2*r)/2*(g (.inl (l,m))+g (.inl (m,l))); μ]=_
  rw [covariance_const_mul_left,covariance_const_mul_right]
  change sqrt (2*r)/2*(sqrt (2*r)/2*cov[(fun g => g (.inl (i,k))) + (fun g => g (.inl (k,i))),
    (fun g => g (.inl (l,m))) + (fun g => g (.inl (m,l)));gaussianCoordinates (MatrixCoordinates ι)]) = _
  rw [covariance_add_left (hm _) (hm _) ((hm _).add (hm _)),
    covariance_add_right (hm _) (hm _) (hm _),
    covariance_add_right (hm _) (hm _) (hm _)]
  simp only [coordinate_covariance,Sum.inl.injEq,Prod.mk.injEq]
  have hs : (sqrt (2*r)/2)^2=r/2 := by rw [div_pow,sq_sqrt (by positivity)]; ring
  have hs' : sqrt (2*r)/2*(sqrt (2*r)/2)=r/2 := by nlinarith only [hs]
  rw [← mul_assoc,hs']
  have hind (p q : Prop) [Decidable p] [Decidable q] :
      (if p ∧ q then (1:ℝ) else 0)=(if p then 1 else 0)*(if q then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [hind]
  ring

end SKRatioGaussian
end
end

section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators
variable {n : ℕ}

def goeDisorder (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) : Disorder n :=
  fun e=>goeMatrix r g e.1.1 e.1.2

lemma goeDisorder_gaussian (r : ℝ) :
    HasGaussianLaw (goeDisorder (n:=n) r) (gaussianCoordinates (MatrixCoordinates (Fin n))) :=
  (goe_matrix_gaussian (ι:=Fin n) r).map_fun (ContinuousLinearMap.pi (fun e : Edge n=>ContinuousLinearMap.proj e.1))

lemma goeDisorder_mean (r : ℝ) (e : Edge n) :
    (∫ g,goeDisorder r g e ∂gaussianCoordinates (MatrixCoordinates (Fin n)))=0 :=
  goe_mean_zero r e.1.1 e.1.2

lemma goeDisorder_cov {r : ℝ} (hr : 0 ≤ r) (e f : Edge n) :
    cov[fun g=>goeDisorder r g e,fun g=>goeDisorder r g f;
      gaussianCoordinates (MatrixCoordinates (Fin n))]=if e=f then r else 0 := by
  change cov[fun g=>goeMatrix r g e.1.1 e.1.2,fun g=>goeMatrix r g f.1.1 f.1.2;
    gaussianCoordinates (MatrixCoordinates (Fin n))]=_
  rw [goe_entry_cov hr]
  have heq : e=f ↔ e.1.1=f.1.1 ∧ e.1.2=f.1.2 := by simp only [Subtype.ext_iff,Prod.ext_iff]
  have hcross : ¬(e.1.1=f.1.2 ∧ e.1.2=f.1.1) := by
    rintro ⟨h1,h2⟩
    have he := e.2
    rw [h1,h2] at he
    exact (lt_asymm f.2 he)
  split_ifs <;> simp_all

lemma goeDisorder_hasLaw {r : ℝ} (hr : 0 ≤ r) :
    HasLaw (goeDisorder (n:=n) r) (Measure.pi (fun _ : Edge n=>gaussianReal 0 (Real.toNNReal r)))
      (gaussianCoordinates (MatrixCoordinates (Fin n))) := by
  have hg := goeDisorder_gaussian (n:=n) r
  have hl (e : Edge n) : HasLaw (fun g=>goeDisorder r g e)
      (gaussianReal 0 (Real.toNNReal r)) (gaussianCoordinates (MatrixCoordinates (Fin n))) := by
    refine ⟨(hg.eval e).aemeasurable,?_⟩
    rw [(hg.eval e).map_eq_gaussianReal,goeDisorder_mean,
      ← covariance_self (hg.eval e).aemeasurable,goeDisorder_cov hr,ite_eq_left rfl]
  exact iIndepFun.hasLaw_pi hl (hg.iIndepFun_of_covariance_eq_zero
    (fun e f h=>by rw [goeDisorder_cov hr,ite_eq_right h]))

lemma goe_actual_disorder_hasLaw (β : ℝ) (n : ℕ) :
    HasLaw (goeDisorder (n:=n) (β^2/(n:ℝ))) (disorderLaw β n)
      (gaussianCoordinates (MatrixCoordinates (Fin n))) :=
  goeDisorder_hasLaw (by positivity)

lemma coupling_goeDisorder (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) :
    Matrix.of (coupling (goeDisorder r g))=goeMatrix r g-Matrix.diagonal (fun i=>goeMatrix r g i i) := by
  ext i k
  by_cases hik : i=k
  · subst k
    simp [coupling]
  · rcases lt_or_gt_of_ne hik with h | h
    · simp [coupling,h,hik,goeDisorder]
    · simp [coupling,h,not_lt_of_gt h,hik,goeDisorder,goeMatrix,add_comm]
end SKRatioGaussian

end
end

section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
lemma goe_row_gaussian (r : ℝ) (i : ι) (e : κ→ι) :
    HasGaussianLaw (fun g : MatrixCoordinates ι→ℝ=>fun k=>goeMatrix r g i (e k))
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  exact (goe_matrix_gaussian r).map_fun
    (ContinuousLinearMap.pi (fun k=>ContinuousLinearMap.proj (i,e k)) :
      ((ι × ι)→ℝ) →L[ℝ] (κ→ℝ))

omit [Fintype κ] in
lemma goe_row_cov {r : ℝ} (hr : 0 ≤ r) (i : ι) (e : κ ↪ ι)
    (he : ∀ k,e k≠i) (k l : κ) :
    cov[fun g=>goeMatrix r g i (e k),fun g=>goeMatrix r g i (e l);
      gaussianCoordinates (MatrixCoordinates ι)]=if k=l then r else 0 := by
  classical
  rw [goe_entry_cov hr]
  have hi : ∀ k,¬i=e k := fun k=>Ne.symm (he k)
  simp only [ite_true,hi,he,e.injective.eq_iff]
  simp only [ite_false,mul_zero,add_zero]
  split_ifs <;> simp_all

lemma goe_row_hasLaw {r : ℝ} (hr : 0 ≤ r) (i : ι) (e : κ ↪ ι)
    (he : ∀ k,e k≠i) :
    HasLaw (fun g : MatrixCoordinates ι→ℝ=>fun k=>goeMatrix r g i (e k))
      (Measure.pi (fun _ : κ=>gaussianReal 0 (Real.toNNReal r)))
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  classical
  have hg := goe_row_gaussian r i e
  have hl (k : κ) : HasLaw (fun g=>goeMatrix r g i (e k))
      (gaussianReal 0 (Real.toNNReal r)) (gaussianCoordinates (MatrixCoordinates ι)) := by
    refine ⟨(hg.eval k).aemeasurable,?_⟩
    rw [(hg.eval k).map_eq_gaussianReal,goe_mean_zero,
      ← covariance_self (hg.eval k).aemeasurable,goe_row_cov hr i e he,ite_eq_left rfl]
  exact iIndepFun.hasLaw_pi hl (hg.iIndepFun_of_covariance_eq_zero
    (fun k l h=>by rw [goe_row_cov hr i e he,ite_eq_right h]))
end SKRatioGaussian

end
end

end

end OAI
