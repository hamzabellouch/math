import Mathlib
import OAI.Analysis.FreeWords.FlipBasic

namespace OAI

noncomputable section

namespace KKFreeLiftDiagnostic

open scoped BigOperators Matrix.Norms.L2Operator Kronecker

noncomputable section

theorem norm_entry_le_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  have hh := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have hc := PiLp.norm_apply_le
    ((EuclideanSpace.equiv ι ℂ).symm (A.mulVec (EuclideanSpace.single j (1:ℂ)).ofLp)) i
  have he : (EuclideanSpace.single j (1:ℂ)).ofLp=Pi.single j 1 := by
    funext k
    simp [Pi.single_apply]
  rw [he,Matrix.mulVec_single_one] at hh hc
  simpa using hc.trans hh

theorem normalizedTrace_norm_le {d : ℕ} (hd : 0 < d) (A : Block d) :
    ‖normalizedTrace A‖ ≤ ‖A‖ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : ‖Matrix.trace A‖ ≤ (d : ℝ)^2*‖A‖ := by
    calc
      _ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin d × Fin d, ‖A‖ := Finset.sum_le_sum (fun i _ => norm_entry_le_opNorm A i i)
      _ = _ := by simp [Fintype.card_prod,pow_two]
  simp only [normalizedTrace,norm_mul,norm_inv,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ ((d : ℝ)^2)⁻¹*((d : ℝ)^2*‖A‖) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = ‖A‖ := by field_simp

@[simp] theorem normalizedTrace_sub {d : ℕ} (A B : Block d) :
    normalizedTrace (A-B)=normalizedTrace A-normalizedTrace B := by
  simp [normalizedTrace,Matrix.trace_sub,mul_sub]

theorem flip_norm {d : ℕ} (hd : 0 < d) : ‖flip d‖=1 := by
  let : NeZero d := ⟨hd.ne'⟩
  exact CStarRing.norm_coe_unitary ⟨flip d,flip_unitary d⟩

theorem left_norm {d : ℕ} (hd : 0 < d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖left (U : Matrix (Fin d) (Fin d) ℂ)‖=1 := by
  let : NeZero d := ⟨hd.ne'⟩
  exact CStarRing.norm_coe_unitary ⟨left (U : Matrix (Fin d) (Fin d) ℂ),left_unitary U⟩

theorem centeredFlip_close {d : ℕ} (hd : 0 < d) :
    ‖centeredFlip d-flip d‖=(d : ℝ)⁻¹ := by
  let : NeZero d := ⟨hd.ne'⟩
  have he : centeredFlip d-flip d = -((d : ℂ)⁻¹ • (1 : Block d)) := by
    dsimp [centeredFlip]; abel
  rw [he,norm_neg,norm_smul,norm_one,mul_one,norm_inv,Complex.norm_natCast]

theorem centeredFlip_norm_le {d : ℕ} (hd : 0 < d) : ‖centeredFlip d‖ ≤ 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hi : (d : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hdR
  have hh := norm_sub_le (centeredFlip d-flip d) (-flip d)
  rw [sub_neg_eq_add,sub_add_cancel,norm_neg,centeredFlip_close hd,flip_norm hd] at hh
  linarith

theorem norm_product_difference {A : Type*} [NormedRing A] (a b c d : A) :
    ‖a*b-c*d‖ ≤ ‖a-c‖*‖b‖+‖c‖*‖b-d‖ := by
  have he : a*b-c*d=(a-c)*b+c*(b-d) := by noncomm_ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

theorem four_product_difference {A : Type*} [NormedRing A]
    (a b c e a' b' c' e' : A) (t : ℝ) (ht : 0 ≤ t)
    (_ : ‖a‖≤2) (hb : ‖b‖≤2) (hc : ‖c‖≤2) (he : ‖e‖≤2)
    (ha' : ‖a'‖≤1) (hb' : ‖b'‖≤1) (hc' : ‖c'‖≤1) (_ : ‖e'‖≤1)
    (had : ‖a-a'‖≤t) (hbd : ‖b-b'‖≤t) (hcd : ‖c-c'‖≤t) (hed : ‖e-e'‖≤t) :
    ‖a*b*c*e-a'*b'*c'*e'‖ ≤ 15*t := by
  have h12 : ‖a*b-a'*b'‖≤3*t := by
    calc
      _ ≤ ‖a-a'‖*‖b‖+‖a'‖*‖b-b'‖ := norm_product_difference _ _ _ _
      _ ≤ t*2+1*t := by gcongr
      _ = _ := by ring
  have hb12 : ‖a'*b'‖≤1 := by
    calc
      _ ≤ ‖a'‖*‖b'‖ := norm_mul_le _ _
      _ ≤ 1*1 := by gcongr
      _ = 1 := by norm_num
  have hb123 : ‖a'*b'*c'‖≤1 := by
    calc
      _ ≤ ‖a'*b'‖*‖c'‖ := norm_mul_le _ _
      _ ≤ 1*1 := by gcongr
      _ = 1 := by norm_num
  have h123 : ‖a*b*c-a'*b'*c'‖≤7*t := by
    calc
      _ ≤ ‖a*b-a'*b'‖*‖c‖+‖a'*b'‖*‖c-c'‖ := norm_product_difference _ _ _ _
      _ ≤ (3*t)*2+1*t := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ‖a*b*c-a'*b'*c'‖*‖e‖+‖a'*b'*c'‖*‖e-e'‖ := norm_product_difference _ _ _ _
    _ ≤ (7*t)*2+1*t := by gcongr
    _ = _ := by ring

end

end KKFreeLiftDiagnostic
end

end OAI
