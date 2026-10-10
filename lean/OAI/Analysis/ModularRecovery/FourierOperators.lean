import OAI.Analysis.ModularRecovery.StrongLimits

namespace OAI

/-! Normalized Fourier operators, Schwarz inequalities, and multiplication. -/

universe u uA uB uM

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma exists_fourierKernel_lift (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    ∃ a : H →L[ℂ] H, a ∈ S.M ∧ ‖a‖ ≤ 4*kernelMass*‖b‖ ∧
      a S.xi = kernelFourier t • S.D.unitary t (S.J ((↑(star b):H →L[ℂ] H) S.xi)) := by
  have ht : Tendsto (fun n => (S.kernelAverage n t b:H →L[ℂ] H) S.xi) atTop
      (𝓝 (kernelFourier t • S.D.unitary t (S.J ((↑(star b):H →L[ℂ] H) S.xi)))) := by
    simpa only [S.kernelAverage_xi] using S.D.kernelMultiplier_strong_tendsto t
      (S.J ((↑(star b):H →L[ℂ] H) S.xi))
  exact (isClosed_bounded_orbit S.M S.xi S.separating
    (mul_nonneg (mul_nonneg (by norm_num) kernelMass_pos.le) (norm_nonneg b))).mem_of_tendsto ht
    (Filter.Eventually.of_forall fun n => ⟨S.kernelAverage n t b,(S.kernelAverage n t b).property,
      S.norm_kernelAverage_le n t b,rfl⟩)

def fourierKernel (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : S.M.toStarSubalgebra :=
  ⟨Classical.choose (S.exists_fourierKernel_lift t b),
    (Classical.choose_spec (S.exists_fourierKernel_lift t b)).1⟩

lemma fourierKernel_xi (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    (S.fourierKernel t b:H →L[ℂ] H) S.xi =
      kernelFourier t • S.D.unitary t (S.J ((↑(star b):H →L[ℂ] H) S.xi)) :=
  (Classical.choose_spec (S.exists_fourierKernel_lift t b)).2.2

lemma norm_fourierKernel_le (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : ‖S.fourierKernel t b‖ ≤ 4*kernelMass*‖b‖ :=
  (Classical.choose_spec (S.exists_fourierKernel_lift t b)).2.1

lemma fourierKernel_strong_tendsto (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (h : H) :
    Tendsto (fun n => (S.kernelAverage n t b:H →L[ℂ] H) h) atTop
      (𝓝 ((S.fourierKernel t b:H →L[ℂ] H) h)) := by
  apply S.tendsto_apply_of_tendsto_xi _ _
    (mul_nonneg (mul_nonneg (by norm_num) kernelMass_pos.le) (norm_nonneg b))
    (fun n => S.norm_kernelAverage_le n t b)
  simpa only [S.kernelAverage_xi,S.fourierKernel_xi] using
    S.D.kernelMultiplier_strong_tendsto t (S.J ((↑(star b):H →L[ℂ] H) S.xi))

lemma fourierKernel_add (S : StandardModularData H) (t : ℝ)
    (b c : S.M.commutant.toStarSubalgebra) :
    S.fourierKernel t (b+c) = S.fourierKernel t b + S.fourierKernel t c := by
  apply S.eq_of_xi
  change (S.fourierKernel t (b+c):H →L[ℂ] H) S.xi =
    (S.fourierKernel t b:H →L[ℂ] H) S.xi + (S.fourierKernel t c:H →L[ℂ] H) S.xi
  simp only [S.fourierKernel_xi,star_add]
  change kernelFourier t • S.D.unitary t (S.J ((star (b:H →L[ℂ] H)+star (c:H →L[ℂ] H)) S.xi)) = _
  simp only [add_apply,map_add,smul_add,StarMemClass.coe_star]

lemma fourierKernel_smul (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (z : ℂ) :
    S.fourierKernel t (z • b) = z • S.fourierKernel t b := by
  apply S.eq_of_xi
  change (S.fourierKernel t (z • b):H →L[ℂ] H) S.xi = z • (S.fourierKernel t b:H →L[ℂ] H) S.xi
  simp only [S.fourierKernel_xi,star_smul]
  change kernelFourier t • S.D.unitary t (S.J ((star z • star (b:H →L[ℂ] H)) S.xi)) = _
  simp only [smul_apply,map_smulₛₗ,Complex.star_def,starRingEnd_self_apply,
    RingHom.id_apply,StarMemClass.coe_star]
  exact smul_comm _ _ _

lemma fourierKernel_one (S : StandardModularData H) (t : ℝ) :
    S.fourierKernel t 1 = kernelFourier t • 1 := by
  apply S.eq_of_xi
  rw [S.fourierKernel_xi]
  simp only [star_one,OneMemClass.coe_one,one_apply_eq_self]
  change kernelFourier t • S.D.unitary t (S.J S.xi) = kernelFourier t • S.xi
  rw [S.J_fixes_xi,S.fixes_xi]

lemma fourierKernel_star (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    star (S.fourierKernel t b) = S.fourierKernel t (star b) := by
  apply Subtype.ext
  ext h
  apply ext_inner_left ℂ
  intro k
  rw [StarMemClass.coe_star,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  have hx := (S.fourierKernel_strong_tendsto t b k).inner (𝕜 := ℂ) (tendsto_const_nhds (x := h))
  have hy := (tendsto_const_nhds (x := k)).inner (𝕜 := ℂ) (S.fourierKernel_strong_tendsto t (star b) h)
  simp only [← S.kernelAverage_star,StarMemClass.coe_star,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right] at hy
  exact tendsto_nhds_unique hx hy

lemma fourierKernel_gram_vector_nonneg (S : StandardModularData H)
    {m : Type uM} [Fintype m] (t : ℝ)
    (b : m → S.M.commutant.toStarSubalgebra) (h : m → H) :
    0 ≤ (∑ i,∑ j,inner ℂ (h i) ((S.fourierKernel t (star (b j)*b i):H →L[ℂ] H) (h j))).re := by
  have ht : Tendsto (fun n => ∑ i,∑ j,inner ℂ (h i)
      ((S.kernelAverage n t (star (b j)*b i):H →L[ℂ] H) (h j))) atTop
      (𝓝 (∑ i,∑ j,inner ℂ (h i)
        ((S.fourierKernel t (star (b j)*b i):H →L[ℂ] H) (h j)))) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact tendsto_const_nhds.inner (S.fourierKernel_strong_tendsto t _ _)
  exact ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp ht)
    (Filter.Eventually.of_forall (fun n => S.kernelAverage_gram_vector_nonneg n t b h))

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

def normalizedFourier (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : S.M.toStarSubalgebra :=
  (kernelFourier t)⁻¹ • S.fourierKernel t b

lemma normalizedFourier_add (S : StandardModularData H) (t : ℝ)
    (b c : S.M.commutant.toStarSubalgebra) :
    S.normalizedFourier t (b+c) = S.normalizedFourier t b + S.normalizedFourier t c := by
  simp only [normalizedFourier,S.fourierKernel_add,smul_add]

lemma normalizedFourier_smul (S : StandardModularData H) (t : ℝ)
    (z : ℂ) (b : S.M.commutant.toStarSubalgebra) :
    S.normalizedFourier t (z • b) = z • S.normalizedFourier t b := by
  simp only [normalizedFourier,S.fourierKernel_smul,smul_comm z]

lemma normalizedFourier_star (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    star (S.normalizedFourier t b) = S.normalizedFourier t (star b) := by
  simp only [normalizedFourier,star_smul,star_inv₀,kernelFourier_star,S.fourierKernel_star]

lemma normalizedFourier_one (S : StandardModularData H) (t : ℝ)
    (ht : kernelFourier t ≠ 0) : S.normalizedFourier t 1 = 1 := by
  simp only [normalizedFourier,S.fourierKernel_one,smul_smul,inv_mul_cancel₀ ht,one_smul]

lemma normalizedFourier_xi (S : StandardModularData H) (t : ℝ)
    (ht : kernelFourier t ≠ 0) (b : S.M.commutant.toStarSubalgebra) :
    (S.normalizedFourier t b:H →L[ℂ] H) S.xi =
      S.D.unitary t (S.J ((↑(star b):H →L[ℂ] H) S.xi)) := by
  change (kernelFourier t)⁻¹ • ((S.fourierKernel t b:H →L[ℂ] H) S.xi) = _
  rw [S.fourierKernel_xi,smul_smul,inv_mul_cancel₀ ht,one_smul]

lemma kernelFourier_ne_zero {t : ℝ} (ht : 0 < (kernelFourier t).re) : kernelFourier t ≠ 0 := by
  intro he
  simp only [he,Complex.zero_re] at ht
  exact lt_irrefl _ ht

lemma normalizedFourier_gram_vector_nonneg (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) {m : Type uM} [Fintype m]
    (b : m → S.M.commutant.toStarSubalgebra) (h : m → H) :
    0 ≤ (∑ i,∑ j,inner ℂ (h i) ((S.normalizedFourier t (star (b j)*b i):H →L[ℂ] H) (h j))).re := by
  change 0 ≤ (∑ i,∑ j,inner ℂ (h i)
    ((kernelFourier t)⁻¹ • ((S.fourierKernel t (star (b j)*b i):H →L[ℂ] H) (h j)))).re
  simp only [inner_smul_right,← Finset.mul_sum]
  rw [← kernelFourier_eq_real t,← Complex.ofReal_inv,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg (inv_nonneg.mpr ht.le) (S.fourierKernel_gram_vector_nonneg t b h)

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma normalizedFourier_schwarz (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b : S.M.commutant.toStarSubalgebra) :
    S.normalizedFourier t b * star (S.normalizedFourier t b) ≤
      S.normalizedFourier t (star b*b) := by
  rw [← sub_nonneg]
  change 0 ≤ (S.normalizedFourier t (star b*b):H →L[ℂ] H) -
    (S.normalizedFourier t b:H →L[ℂ] H)*star (S.normalizedFourier t b:H →L[ℂ] H)
  rw [ContinuousLinearMap.nonneg_iff_isPositive,ContinuousLinearMap.isPositive_def']
  refine ⟨?_,fun h => ?_⟩
  · show star _ = _
    simp only [star_sub,star_mul,star_star,← StarMemClass.coe_star,S.normalizedFourier_star]
  · let y : H := (S.normalizedFourier t (star b):H →L[ℂ] H) h
    have hp := S.normalizedFourier_gram_vector_nonneg t ht
      (![1,b] : Fin 2 → S.M.commutant.toStarSubalgebra) (![(-y),h] : Fin 2 → H)
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,star_one,one_mul,mul_one,S.normalizedFourier_one t (kernelFourier_ne_zero ht),
      OneMemClass.coe_one,one_apply_eq_self,map_neg,inner_neg_left,inner_neg_right] at hp
    have hy : inner ℂ h ((S.normalizedFourier t b:H →L[ℂ] H) y) = inner ℂ y y := by
      rw [← star_star b,← S.normalizedFourier_star,StarMemClass.coe_star,
        ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
    change 0 ≤ (inner ℂ (((S.normalizedFourier t (star b*b):H →L[ℂ] H) -
      (S.normalizedFourier t b:H →L[ℂ] H)*star (S.normalizedFourier t b:H →L[ℂ] H)) h) h).re
    rw [← inner_conj_symm,Complex.conj_re]
    simp only [sub_apply,mul_apply_eq_comp,← StarMemClass.coe_star,S.normalizedFourier_star,
      inner_sub_right]
    change 0 ≤ (inner ℂ h ((S.normalizedFourier t (star b*b):H →L[ℂ] H) h) -
      inner ℂ h ((S.normalizedFourier t b:H →L[ℂ] H) y)).re
    rw [hy]
    change 0 ≤ (- -inner ℂ y y + -inner ℂ y y +
      (-inner ℂ h ((S.normalizedFourier t b:H →L[ℂ] H) y) +
      inner ℂ h ((S.normalizedFourier t (star b*b):H →L[ℂ] H) h))).re at hp
    rw [hy] at hp
    simpa only [neg_neg,add_neg_cancel,zero_add,sub_eq_add_neg,add_comm] using hp

lemma phi_normalizedFourier (S : StandardModularData H) (t : ℝ)
    (ht : kernelFourier t ≠ 0) (b : S.M.commutant.toStarSubalgebra) :
    S.phi (S.normalizedFourier t b) = S.commutantData.phi b := by
  change inner ℂ S.xi ((S.normalizedFourier t b:H →L[ℂ] H) S.xi) =
    inner ℂ S.xi ((b:H →L[ℂ] H) S.xi)
  rw [S.normalizedFourier_xi t ht]
  rw [← star_star (S.D.unitary t),ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rw [S.D.unitary_star,S.fixes_xi]
  have he (x : H) : inner ℂ S.xi (S.J x) = inner ℂ x S.xi := by
    have h := S.J_inner_flip S.xi (S.J x)
    rw [S.J_fixes_xi,S.conjugation x] at h
    exact h
  rw [he,StarMemClass.coe_star,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

lemma phi_faithful_nonneg (S : StandardModularData H) (a : S.M.toStarSubalgebra)
    (ha : 0 ≤ a) (hz : (S.phi a).re = 0) : a = 0 := by
  obtain ⟨d,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  rw [S.phi_faithful d hz,star_zero,mul_zero]

lemma normalizedFourier_star_square (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b : S.M.commutant.toStarSubalgebra) :
    S.normalizedFourier t (star b*b) =
      S.normalizedFourier t b * star (S.normalizedFourier t b) := by
  apply sub_eq_zero.mp
  apply S.phi_faithful_nonneg _ (sub_nonneg.mpr (S.normalizedFourier_schwarz t ht b))
  rw [map_sub,Complex.sub_re,S.phi_normalizedFourier t (kernelFourier_ne_zero ht)]
  have hv : (S.commutantData.phi (star b*b)).re = ‖(b:H →L[ℂ] H) S.xi‖^2 :=
    S.commutantData.phi_star_mul b
  rw [hv]
  have he : (S.phi (S.normalizedFourier t b * star (S.normalizedFourier t b))).re =
      ‖(b:H →L[ℂ] H) S.xi‖^2 := by
    nth_rw 1 [← star_star (S.normalizedFourier t b)]
    rw [S.phi_star_mul,S.normalizedFourier_star,S.normalizedFourier_xi t (kernelFourier_ne_zero ht),
      star_star,S.D.norm_unitary_apply,S.J.norm_map]
  rw [he,sub_self]

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

lemma sesq_zero_of_diagonal {A : Type uA} {B : Type uB} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (f : A → A → B)
    (ha : ∀ a b c, f (a+b) c = f a c + f b c)
    (hb : ∀ a b c, f a (b+c) = f a b + f a c)
    (hs : ∀ (z : ℂ) a b, f (z • a) b = star z • f a b)
    (ht : ∀ (z : ℂ) a b, f a (z • b) = z • f a b)
    (hd : ∀ a, f a a = 0) (a b : A) : f a b = 0 := by
  have h1 : f a b + f b a = 0 := by
    have h := hd (a+b)
    simpa only [ha,hb,hd,zero_add,add_zero] using h
  have h2 : Complex.I • f a b + star Complex.I • f b a = 0 := by
    have h := hd (a+Complex.I • b)
    simpa only [ha,hb,hs,ht,hd,smul_zero,zero_add,add_zero] using h
  have hba : f b a = -f a b := eq_neg_of_add_eq_zero_right h1
  rw [hba,Complex.star_def,Complex.conj_I,neg_smul,smul_neg,neg_neg,← two_smul ℂ] at h2
  have hI : Complex.I • f a b = 0 := (smul_eq_zero.mp h2).resolve_left (by norm_num)
  exact (smul_eq_zero.mp hI).resolve_left Complex.I_ne_zero

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma normalizedFourier_star_mul (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b c : S.M.commutant.toStarSubalgebra) :
    S.normalizedFourier t (star b*c) =
      S.normalizedFourier t c * star (S.normalizedFourier t b) := by
  apply sub_eq_zero.mp
  let f : S.M.commutant.toStarSubalgebra → S.M.commutant.toStarSubalgebra → S.M.toStarSubalgebra :=
    fun b c => S.normalizedFourier t (star b*c) - S.normalizedFourier t c * star (S.normalizedFourier t b)
  show f b c = 0
  apply sesq_zero_of_diagonal f
  · intro a b c
    dsimp only [f]
    simp only [star_add,add_mul,S.normalizedFourier_add,mul_add]
    abel
  · intro a b c
    dsimp only [f]
    simp only [mul_add,S.normalizedFourier_add,add_mul]
    abel
  · intro z a b
    dsimp only [f]
    simp only [star_smul,smul_mul_assoc,S.normalizedFourier_smul,mul_smul_comm,smul_sub]
  · intro z a b
    dsimp only [f]
    simp only [mul_smul_comm,S.normalizedFourier_smul,smul_mul_assoc,smul_sub]
  · intro a
    exact sub_eq_zero.mpr (S.normalizedFourier_star_square t ht a)

lemma normalizedFourier_mul (S : StandardModularData H) (t : ℝ)
    (ht : 0 < (kernelFourier t).re) (b c : S.M.commutant.toStarSubalgebra) :
    S.normalizedFourier t (b*c) = S.normalizedFourier t c * S.normalizedFourier t b := by
  simpa only [star_star,S.normalizedFourier_star] using S.normalizedFourier_star_mul t ht (star b) c

end StandardModularData
end BoundedRecovery

end
end
end
end

end OAI
