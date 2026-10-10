import Mathlib
import OAI.Probability.LogConcave.Sampling.NaturalMomentNorm
import OAI.Probability.LogConcave.JetEstimates.TensorTerm
import OAI.Probability.LogConcave.JetEstimates.Slice

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped ENNReal

lemma integral_sq_le_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hf0 : ∀x,0≤f x)
    {B : ℝ≥0∞} (hB : B≠⊤) (hN : eLpNorm f 2 μ≤B) :
    Integrable (fun x => (f x)^2) μ ∧ (∫x,(f x)^2 ∂μ)≤B.toReal^2 := by
  have hm : MemLp f 2 μ := lt_of_le_of_lt hN (lt_top_iff_ne_top.mpr hB)
  have hi := hm.integrable_sq
  refine ⟨hi,?_⟩
  have hnorm : eLpNorm f (2 : ℝ≥0∞) μ = eLpNorm' f (2 : ℝ) μ := by
    simpa using (eLpNorm_nnreal_eq_eLpNorm' (p := 2) (by norm_num) hf)
  rw [hnorm] at hN
  have hh := (norm_le_iff_natural_moment hf0 (by norm_num : 0<2) B).mp hN
  have he : (∫x,(f x)^2 ∂μ)=(∫⁻x,ENNReal.ofReal (f x)^2 ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => sq_nonneg (f x))) hi.1]
    simp_rw [ENNReal.ofReal_pow (hf0 _)]
  rw [he,←ENNReal.toReal_pow]
  exact ENNReal.toReal_le_toReal (ne_of_lt ((lt_of_le_of_lt hh (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hB)))))
    (ENNReal.pow_ne_top hB) |>.mpr hh
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

lemma allSplit_integral_frobenius {Ω S I : Type} [MeasurableSpace Ω] [Fintype S]
    [Fintype I] [Nonempty I] {μ : Measure Ω} {d : ℕ}
    {T : (S → Fin d) → Ω → ℝ} {b : Ω → ℝ} {B : ℝ≥0∞}
    (hT : ∀c,Integrable (fun y => (T c y)^2) μ)
    (hb : AEStronglyMeasurable b μ) (hb0 : ∀y,0≤b y) (hB : B≠⊤)
    (hN : eLpNorm b 2 μ≤B) (hs : ∀y,TensorEnergy.AllSplitBound (fun c => T c y) (b y))
    (e : S ≃ I ⊕ Unit) :
    (∑c,∫y,(T c y)^2 ∂μ)≤d*B.toReal^2 := by
  obtain ⟨hi,hv⟩ := integral_sq_le_of_eLpNorm hb hb0 hB hN
  calc
    _ = ∫y,∑c,(T c y)^2 ∂μ := (integral_finsetSum Finset.univ (fun c _ => hT c)).symm
    _ ≤ ∫y,(d:ℝ)*(b y)^2 ∂μ := integral_mono
      (integrable_finsetSum Finset.univ (fun c _ => hT c)) (hi.const_mul _) (fun y => (hs y).frobeniusSquared e)
    _ = (d:ℝ)*(∫y,(b y)^2 ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _)

namespace TensorSum

lemma spatialTensor_integrable_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    {S : Type} [Fintype S] (A : TensorSum S) (j : ℕ) (c : Fin j ⊕ S → Fin d) :
    Integrable (fun y => (spatialTensor (A.slice F x r ρ ((lam:ℝ)*r)) (List.finRange j) y c)^2)
      (interpolationLaw F x r ρ) := by
  have hp := spatialTensor_polySmooth (A.slice F x r ρ ((lam:ℝ)*r))
    (A.slice_polySmooth hF x hr hlam hl h0 h1) (List.finRange j) c
  rw [interpolationLaw_eq_gibbs hF x hr.le (by linarith) (by nlinarith)]
  exact integrable_polynomial_gibbs
    (interpolationPotential_smooth hF x hr.le hl h0 h1).continuous
    (interpolationPotential_lowerTail hF x hr.le (by linarith) h0 h1)
    (hp.smooth.continuous.pow 2) (Appell.HasGrowth.pow (hp.growth []) 2)

lemma spatialTensor_l2 {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (hd : 1≤d) (A : TensorSum (Unit ⊕ Unit)) {w : ℕ} (hw : A.weightLE w) (j : ℕ) :
    (∑c,∫y,(spatialTensor (A.slice F x r ρ ((lam:ℝ)*r)) (List.finRange j) y c)^2 ∂interpolationLaw F x r ρ)≤
      d*(A.momentBudget d j 2).toReal^2*((Real.sqrt (1-ρ^2))⁻¹)^(2*(w+j)) := by
  have hR : 0≤(Real.sqrt (1-ρ^2))⁻¹ := by positivity
  have hB : A.momentBudget d j 2*ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)^(w+j)≠⊤ :=
    ENNReal.mul_ne_top (A.momentBudget_ne_top _ _ _) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hh := allSplit_integral_frobenius (A.spatialTensor_integrable_sq hF x hr hlam hl h0 h1 j)
    (A.spatialBound_measurable hF x hr hlam hl h0 h1 j).aestronglyMeasurable
    (A.spatialBound_nonneg _ _ _ _ _ j) hB (A.spatialBound_Lp hF x hr hlam hl h0 h1 hd hw j (by norm_num) (by norm_num))
    (A.spatialBound_allSplit hF x hr hlam hl h0 h1 j) (Equiv.sumAssoc (Fin j) Unit Unit).symm
  convert hh using 1
  · congr 2; exact Subsingleton.elim _ _
  · rw [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hR,mul_pow]
    rw [←pow_mul]
    ring
end TensorSum
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal

def matrixZeroColor (d : ℕ) : (Fin d × Fin d) ≃ (Fin 0 ⊕ (Unit ⊕ Unit) → Fin d) where
  toFun p := Sum.elim Fin.elim0 (Sum.elim (fun _ => p.1) (fun _ => p.2))
  invFun c := (c (Sum.inr (Sum.inl ())),c (Sum.inr (Sum.inr ())))
  left_inv p := rfl
  right_inv c := by
    funext s
    rcases s with s | (s | s)
    · exact Fin.elim0 s
    · cases s; rfl
    · cases s; rfl

def matrixOneColor (d : ℕ) : (Fin d × Fin d × Fin d) ≃ (Fin 1 ⊕ (Unit ⊕ Unit) → Fin d) where
  toFun p := Sum.elim (fun _ => p.2.1) (Sum.elim (fun _ => p.1) (fun _ => p.2.2))
  invFun c := (c (Sum.inr (Sum.inl ())),c (Sum.inl 0),c (Sum.inr (Sum.inr ())))
  left_inv p := rfl
  right_inv c := by
    funext s
    rcases s with s | (s | s)
    · have hs : s=0 := Subsingleton.elim _ _
      subst s; rfl
    · cases s; rfl
    · cases s; rfl

lemma matrix_zero_energy_eq {d : ℕ} (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (μ : Measure (Point d)) :
    (∑c,∫y,(spatialTensor A (List.finRange 0) y c)^2 ∂μ)=
      ∑a : Fin d,∑j : Fin d,∫y,(A (Sum.elim (fun _ => a) (fun _ => j)) y)^2 ∂μ := by
  have he := Equiv.sum_comp (matrixZeroColor d) (fun c => ∫y,(spatialTensor A (List.finRange 0) y c)^2 ∂μ)
  rw [Fintype.sum_prod_type] at he
  exact he.symm

lemma matrix_one_energy_eq {d : ℕ} (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (μ : Measure (Point d)) :
    (∑c,∫y,(spatialTensor A (List.finRange 1) y c)^2 ∂μ)=
      ∑a : Fin d,∑i : Fin d,∑j : Fin d,∫y,(directional (EuclideanSpace.basisFun (Fin d) ℝ i)
        (A (Sum.elim (fun _ => a) (fun _ => j))) y)^2 ∂μ := by
  have he := Equiv.sum_comp (matrixOneColor d) (fun c => ∫y,(spatialTensor A (List.finRange 1) y c)^2 ∂μ)
  simp only [Fintype.sum_prod_type] at he
  exact he.symm

namespace TensorSum
lemma slice_integrable_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum (Unit ⊕ Unit)) (a j : Fin d) :
    Integrable (fun y => (A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => a) (fun _ => j)) y)^2)
      (interpolationLaw F x r ρ) := A.spatialTensor_integrable_sq hF x hr hlam hl h0 h1 0 (matrixZeroColor d (a,j))

lemma slice_directional_integrable_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum (Unit ⊕ Unit)) (a i j : Fin d) :
    Integrable (fun y => (directional (EuclideanSpace.basisFun (Fin d) ℝ i)
      (A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => a) (fun _ => j))) y)^2)
      (interpolationLaw F x r ρ) := A.spatialTensor_integrable_sq hF x hr hlam hl h0 h1 1 (matrixOneColor d (a,i,j))

lemma matrix_zero_energy {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (hd : 1≤d) (A : TensorSum (Unit ⊕ Unit)) {w : ℕ} (hw : A.weightLE w) :
    (∑a : Fin d,∫y,∑j : Fin d,(A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => a) (fun _ => j)) y)^2
       ∂interpolationLaw F x r ρ)≤d*(A.momentBudget d 0 2).toReal^2*((Real.sqrt (1-ρ^2))⁻¹)^(2*w) := by
  simp_rw [integral_finsetSum Finset.univ (fun j _ => A.slice_integrable_sq hF x hr hlam hl h0 h1 _ j)]
  rw [←matrix_zero_energy_eq]
  simpa only [Nat.add_zero] using A.spatialTensor_l2 hF x hr hlam hl h0 h1 hd hw 0

lemma matrix_one_energy {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (hd : 1≤d) (A : TensorSum (Unit ⊕ Unit)) {w : ℕ} (hw : A.weightLE w) :
    (∑a : Fin d,∫y,∑i : Fin d,∑j : Fin d,(directional (EuclideanSpace.basisFun (Fin d) ℝ i)
      (A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => a) (fun _ => j))) y)^2
       ∂interpolationLaw F x r ρ)≤d*(A.momentBudget d 1 2).toReal^2*((Real.sqrt (1-ρ^2))⁻¹)^(2*(w+1)) := by
  simp_rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun j _ => A.slice_directional_integrable_sq hF x hr hlam hl h0 h1 _ i j)),
    integral_finsetSum Finset.univ (fun j _ => A.slice_directional_integrable_sq hF x hr hlam hl h0 h1 _ _ j)]
  rw [←matrix_one_energy_eq]
  exact A.spatialTensor_l2 hF x hr hlam hl h0 h1 hd hw 1
end TensorSum
end LogConcaveSampling

end

end

end

end OAI
