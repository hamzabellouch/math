import Mathlib
import OAI.Probability.SKRatio.Matrices.GaussianSupport

namespace OAI

section
section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

lemma gaussian_square_exp_integral :
    (∫ x : ℝ,exp (x^2/4) ∂gaussianReal 0 1) ≤ 2 := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero),
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun y=>by simp [gaussianPDF]))]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul]
  have he : (fun x : ℝ=>gaussianPDFReal 0 1 x*exp (x^2/4))=
      (fun x : ℝ=>(1/sqrt (2*Real.pi))*exp (-(1/4:ℝ)*x^2)) := by
    funext x
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    rw [mul_assoc,← exp_add]
    congr 2 <;> ring
  rw [he,integral_const_mul,integral_gaussian]
  have hp := Real.pi_pos
  have h1 := sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have h2 := sq_sqrt (show 0 ≤ Real.pi/(1/4:ℝ) by positivity)
  have h3 := sqrt_nonneg (2*Real.pi)
  have h4 := sqrt_nonneg (Real.pi/(1/4:ℝ))
  rw [one_div,mul_comm,← div_eq_mul_inv]
  apply (div_le_iff₀ (sqrt_pos.mpr (by positivity))).mpr
  nlinarith

lemma gaussian_square_exp_integrable :
    Integrable (fun x : ℝ=>exp (x^2/4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero),integrable_withDensity_iff
    (measurable_gaussianPDF 0 1) (ae_of_all _ (fun y=>by simp [gaussianPDF]))]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  have hi := (integrable_exp_neg_mul_sq (show (0:ℝ) < 1/4 by norm_num)).const_mul (1/sqrt (2*Real.pi))
  have he : (fun g : ℝ=>exp (g^2/4)*gaussianPDFReal 0 1 g)=
      (fun g : ℝ=>(1/sqrt (2*Real.pi))*exp (-(1/4:ℝ)*g^2)) := by
    funext g
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    rw [mul_left_comm,← exp_add]
    congr 2 <;> ring
  rw [he]
  exact hi

lemma product_gaussian_square_exp_integral {ι : Type*} [Fintype ι] :
    (∫ g : ι→ℝ,exp ((∑ i,g i^2)/4) ∂Measure.pi (fun _ : ι=>gaussianReal 0 1)) ≤
      exp ((Fintype.card ι:ℝ)*log 2) := by
  have he (g : ι→ℝ) : exp ((∑ i,g i^2)/4)=∏ i,exp (g i^2/4) := by
    rw [← exp_sum,Finset.sum_div]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (f:=fun _ : ι=>fun x : ℝ=>exp (x^2/4))]
  calc
    _ ≤ ∏ _i : ι,(2:ℝ) := Finset.prod_le_prod₀
      (fun i _=>integral_nonneg (fun x=>(exp_pos _).le))
      (fun i _=>gaussian_square_exp_integral)
    _ = _ := by rw [Finset.prod_const,Finset.card_univ,exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]

lemma product_gaussian_square_exp_integrable {ι : Type*} [Fintype ι] :
    Integrable (fun g : ι→ℝ=>exp ((∑ i,g i^2)/4))
      (Measure.pi (fun _ : ι=>gaussianReal 0 1)) := by
  have hi := Integrable.fintype_prod (fun _ : ι=>gaussian_square_exp_integrable)
  convert hi using 1
  ext g
  rw [← exp_sum,Finset.sum_div]

lemma product_gaussian_square_tail {ι : Type*} [Fintype ι] (t : ℝ) :
    (Measure.pi (fun _ : ι=>gaussianReal 0 1)).real {g | t < ∑ i,g i^2} ≤
      exp (-t/4+(Fintype.card ι:ℝ)*log 2) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (Measure.pi (fun _ : ι=>gaussianReal 0 1))
      (fun g=>(exp_pos ((∑ i,g i^2)/4)).le)) product_gaussian_square_exp_integrable (exp (t/4))
  have hs : {g : ι→ℝ| t < ∑ i,g i^2} ⊆ {g | exp (t/4) ≤ exp ((∑ i,g i^2)/4)} := by
    intro g hg
    exact exp_le_exp.mpr (by linarith only [show t < ∑ i,g i^2 from hg])
  have hb := (mul_le_mul_of_nonneg_left (measureReal_mono hs)
    (exp_pos (t/4)).le).trans (hm.trans product_gaussian_square_exp_integral)
  rw [show -t/4+(Fintype.card ι:ℝ)*log 2=(Fintype.card ι:ℝ)*log 2-t/4 by ring,exp_sub]
  apply (le_div_iff₀ (exp_pos _)).mpr
  simpa only [mul_comm] using hb
end SKRatioGaussian
end
end

section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal
variable {κ : Type*} [Fintype κ]

lemma gaussian_scaled_coordinates_hasLaw {r : ℝ} (hr : 0 ≤ r) :
    HasLaw (fun g : κ→ℝ=>fun k=>sqrt r*g k)
      (Measure.pi (fun _ : κ=>gaussianReal 0 (Real.toNNReal r))) (gaussianCoordinates κ) := by
  have hl (k : κ) : HasLaw (fun g : κ→ℝ=>sqrt r*g k)
      (gaussianReal 0 (Real.toNNReal r)) (gaussianCoordinates κ) := by
    have h := gaussianReal_const_mul (coordinate_hasLaw (κ:=κ) k) (sqrt r)
    have hv : (⟨(sqrt r)^2,sq_nonneg _⟩:ℝ≥0)*1=Real.toNNReal r := by
      apply NNReal.eq
      change (sqrt r)^2*1=↑(Real.toNNReal r)
      rw [mul_one,sq_sqrt hr,Real.coe_toNNReal _ hr]
    rw [mul_zero] at h
    convert h using 1
    exact congrArg (gaussianReal 0) hv.symm
  exact iIndepFun.hasLaw_pi hl ((iIndepFun_pi (fun _ : κ=>aemeasurable_id)).comp
    (fun _=>fun x : ℝ=>sqrt r*x) (fun _=>by fun_prop))

lemma scaled_gaussian_square_tail {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (Measure.pi (fun _ : κ=>gaussianReal 0 (Real.toNNReal r))).real {g | t < ∑ i,g i^2} ≤
      exp (-t/(4*r)+(Fintype.card κ:ℝ)*log 2) := by
  have hm : MeasurableSet {g : κ→ℝ | t < ∑ i,g i^2} := by measurability
  rw [← (gaussian_scaled_coordinates_hasLaw (κ:=κ) hr.le).measureReal_eq hm]
  have he : {g : κ→ℝ | t < ∑ i,(sqrt r*g i)^2}={g | t/r < ∑ i,g i^2} := by
    ext g
    simp only [Set.mem_ofPred_eq,mul_pow,sq_sqrt hr.le,← Finset.mul_sum]
    rw [div_lt_iff₀ hr,mul_comm]
  rw [he]
  convert product_gaussian_square_tail (ι:=κ) (t/r) using 1
  congr 2
  ring_nf
end SKRatioGaussian
end
end

section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

lemma gaussian_real_square_tail {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (gaussianReal 0 (Real.toNNReal r)).real {x : ℝ | t < x^2} ≤ exp (-t/(4*r)+log 2) := by
  have h : HasLaw (fun v : Unit→ℝ=>v ()) (gaussianReal 0 (Real.toNNReal r))
      (Measure.pi (fun _ : Unit=>gaussianReal 0 (Real.toNNReal r))) :=
    ⟨(measurable_pi_apply ()).aemeasurable,(measurePreserving_eval (fun _ : Unit=>gaussianReal 0 (Real.toNNReal r)) ()).map_eq⟩
  rw [← h.measureReal_eq (by measurability : MeasurableSet {x : ℝ | t < x^2})]
  simpa using scaled_gaussian_square_tail (κ:=Unit) hr t

lemma gaussian_real_abs_tail {r : ℝ} (hr : 0 < r) {d : ℝ} (hd : 0 ≤ d) :
    (gaussianReal 0 (Real.toNNReal r)).real {x : ℝ | d < |x|} ≤ 2*exp (-d^2/(4*r)) := by
  have he : {x : ℝ | d < |x|}={x | d^2 < x^2} := by
    ext x
    simpa only [Set.mem_ofPred_eq,sq_abs] using (sq_lt_sq₀ hd (abs_nonneg x)).symm
  rw [he]
  apply (gaussian_real_square_tail hr (d^2)).trans_eq
  rw [exp_add,exp_log (by norm_num : (0:ℝ) < 2),mul_comm]
end SKRatioGaussian
end
end

section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_diagonal_hasLaw {r : ℝ} (hr : 0 ≤ r) (i : ι) :
    HasLaw (fun g : MatrixCoordinates ι→ℝ=>goeMatrix r g i i)
      (gaussianReal 0 (Real.toNNReal (2*r))) (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hg := (goe_matrix_gaussian (ι:=ι) r).eval (i,i)
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal,goe_mean_zero,← covariance_self hg.aemeasurable,goe_entry_cov hr]
  simp only [ite_true,mul_one]
  congr 2
  ring

lemma goe_diagonal_tail {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | ∃ i : ι,d < |goeMatrix r g i i|} ≤
      2*(Fintype.card ι:ℝ)*exp (-d^2/(8*r)) := by
  have hsingle (i : ι) :
      (gaussianCoordinates (MatrixCoordinates ι)).real {g | d < |goeMatrix r g i i|} ≤
      2*exp (-d^2/(8*r)) := by
    rw [(goe_diagonal_hasLaw hr.le i).measureReal_eq
      (by measurability : MeasurableSet {x : ℝ | d < |x|})]
    convert gaussian_real_abs_tail (r:=2*r) (by positivity) hd using 1
    ring_nf
  have he : {g : MatrixCoordinates ι→ℝ | ∃ i : ι,d < |goeMatrix r g i i|}=
      ⋃ i : ι,{g | d < |goeMatrix r g i i|} := by ext g;simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  apply (Finset.sum_le_sum (fun i _=>hsingle i)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

lemma diagonal_norm_le {d : ℝ} (hd : 0 ≤ d) (v : ι→ℝ) (hv : ∀ i,|v i| ≤ d) :
    ‖Matrix.diagonal v‖ ≤ d := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hd).mpr (fun i=>by simpa only [Real.norm_eq_abs] using hv i)
end SKRatioGaussian
end
end

section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators
variable {n : ℕ}

lemma coupling_goe_offdiag (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) (i k : Fin n)
    (hik : i≠k) : coupling (goeDisorder r g) i k=goeMatrix r g i k := by
  have h := congrFun (congrFun (coupling_goeDisorder r g) i) k
  simpa only [of_apply,Matrix.sub_apply,diagonal_apply_ne _ hik,sub_zero] using h

lemma coupling_goe_row_square_sum (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ)
    (i : Fin n) (S : Finset (Fin n)) :
    (∑ k∈S,coupling (goeDisorder r g) i k^2)=∑ k : S.erase i,goeMatrix r g i k^2 := by
  rw [Finset.sum_coe_sort (S.erase i) (fun k : Fin n=>goeMatrix r g i k^2)]
  calc
    _ = ∑ k∈S.erase i,coupling (goeDisorder r g) i k^2 :=
      by
        by_cases hi : i∈S
        · rw [Finset.sum_erase_eq_sub hi]
          simp [coupling]
        · rw [Finset.erase_eq_self.mpr hi]
    _ = _ := Finset.sum_congr rfl (fun k hk=>by rw [coupling_goe_offdiag r g i k (Ne.symm (Finset.ne_of_mem_erase hk))])

lemma coupling_goe_row_tail {r : ℝ} (hr : 0 < r) (i : Fin n) (S : Finset (Fin n)) (t : ℝ) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | t < ∑ k∈S,coupling (goeDisorder r g) i k^2} ≤
      exp (-t/(4*r)+(S.card:ℝ)*log 2) := by
  let e : S.erase i ↪ Fin n := ⟨Subtype.val,Subtype.val_injective⟩
  have havoid (k : S.erase i) : e k≠i := Finset.ne_of_mem_erase k.2
  have hm : MeasurableSet {v : S.erase i→ℝ | t < ∑ k,v k^2} := by measurability
  simp_rw [coupling_goe_row_square_sum]
  have heq := (goe_row_hasLaw hr.le i e havoid).measureReal_eq hm
  change (gaussianCoordinates (MatrixCoordinates (Fin n))).real
    {g | t < ∑ k : S.erase i,goeMatrix r g i k^2} = (Measure.pi (fun _ : S.erase i=>gaussianReal 0 (Real.toNNReal r))).real {v | t < ∑ k,v k^2} at heq
  rw [heq]
  apply (scaled_gaussian_square_tail hr t).trans
  apply exp_le_exp.mpr
  have hcard : (Fintype.card (S.erase i):ℝ) ≤ S.card := by
    rw [Fintype.card_coe]
    exact_mod_cast Finset.card_erase_le
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcard (log_nonneg (show (1:ℝ) ≤ 2 by norm_num)))

end SKRatioGaussian
end
end

section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators
variable {n : ℕ}

lemma coupling_goe_all_rows_tail [NeZero n] {j t : ℝ} (hj : 0 < j) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ∃ i : Fin n,t < ∑ k,coupling (goeDisorder (j/(n:ℝ)) g) i k^2} ≤
      (n:ℝ)*exp (-(n:ℝ)*(t/(4*j)-log 2)) := by
  have hn : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  have he : {g : MatrixCoordinates (Fin n)→ℝ | ∃ i : Fin n,t < ∑ k,coupling (goeDisorder (j/(n:ℝ)) g) i k^2}=
      ⋃ i : Fin n,{g | t < ∑ k,coupling (goeDisorder (j/(n:ℝ)) g) i k^2} := by ext g;simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  have hb (i : Fin n) := coupling_goe_row_tail (div_pos hj hn) i Finset.univ t
  simp only [Finset.card_univ,Fintype.card_fin] at hb
  apply (Finset.sum_le_sum (fun i _=>hb i)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 2
  field_simp
  ring

lemma coupling_goe_max_entry_tail [NeZero n] {j d : ℝ} (hj : 0 < j) (hd : 0 ≤ d) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ∃ i k : Fin n,d < |coupling (goeDisorder (j/(n:ℝ)) g) i k|} ≤
      2*(n:ℝ)^2*exp (-(n:ℝ)*d^2/(4*j)) := by
  have hn : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  have hsingle (i k : Fin n) :
      (gaussianCoordinates (MatrixCoordinates (Fin n))).real
        {g | d < |coupling (goeDisorder (j/(n:ℝ)) g) i k|} ≤
      2*exp (-(n:ℝ)*d^2/(4*j)) := by
    have he : {g : MatrixCoordinates (Fin n)→ℝ | d < |coupling (goeDisorder (j/(n:ℝ)) g) i k|}=
        {g | d^2 < ∑ l∈({k} : Finset (Fin n)),coupling (goeDisorder (j/(n:ℝ)) g) i l^2} := by
      ext g
      simp only [Finset.sum_singleton,Set.mem_ofPred_eq]
      simpa only [sq_abs] using (sq_lt_sq₀ hd (abs_nonneg (coupling (goeDisorder (j/(n:ℝ)) g) i k))).symm
    rw [he]
    apply (coupling_goe_row_tail (div_pos hj hn) i {k} (d^2)).trans_eq
    simp only [Finset.card_singleton,Nat.cast_one,one_mul,exp_add,exp_log (by norm_num : (0:ℝ) < 2)]
    rw [mul_comm]
    congr 2
    field_simp
  have he : {g : MatrixCoordinates (Fin n)→ℝ | ∃ i k : Fin n,d < |coupling (goeDisorder (j/(n:ℝ)) g) i k|}=
      ⋃ i : Fin n,⋃ k : Fin n,{g | d < |coupling (goeDisorder (j/(n:ℝ)) g) i k|} := by ext g;simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  apply (Finset.sum_le_sum (fun i _=>(measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum (fun k _=>hsingle i k)))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring
end SKRatioGaussian

end
end

end

end OAI
