import OAI.InformationTheory.SecretKey.Discussion

namespace OAI

noncomputable section

namespace ZeroKey

section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

universe v8144_0 v8144_1

variable {ι : Type v8144_0} {κ : Type v8144_1} [inst8144_0 : Fintype ι] [inst8144_1 : Fintype κ] [inst8144_2 : DecidableEq ι] [inst8144_3 : DecidableEq κ]

omit inst8144_2 inst8144_3 in
lemma faithful_input_effects [DecidableEq ι] [DecidableEq κ] (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : U.PosSemidef) (hV : V.PosSemidef) :
    (((Fintype.card ι : ℂ) • Uᵀ).PosSemidef ∧ ((Fintype.card κ : ℂ) • Vᵀ).PosSemidef) :=
  ⟨hU.transpose.smul (Nat.cast_nonneg _),hV.transpose.smul (Nat.cast_nonneg _)⟩

end

section

open scoped MatrixOrder ComplexOrder Kronecker

open Matrix

section

universe v8188_0

variable {ι : Type v8188_0} [inst8188_0 : Fintype ι] [inst8188_1 : DecidableEq ι]

lemma traceNorm_unitary_mul_le (A : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    traceNorm ((U : Matrix ι ι ℂ) * A) ≤ traceNorm A := by
  obtain ⟨W,hW⟩ := exists_unitary_traceNorm ((U : Matrix ι ι ℂ) * A)
  rw [← hW, ← mul_assoc]
  exact re_trace_unitary_mul_le_traceNorm A (W*U)

lemma traceNorm_unitary_mul (A : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    traceNorm ((U : Matrix ι ι ℂ) * A) = traceNorm A := by
  apply le_antisymm (traceNorm_unitary_mul_le A U)
  have h := traceNorm_unitary_mul_le ((U : Matrix ι ι ℂ) * A) (star U)
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose, ← mul_assoc,
    show (U : Matrix ι ι ℂ)ᴴ * U = 1 from U.prop.1, one_mul] using h

lemma traceNorm_mul_unitary_le (A : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    traceNorm (A * (U : Matrix ι ι ℂ)) ≤ traceNorm A := by
  obtain ⟨W,hW⟩ := exists_unitary_traceNorm (A * (U : Matrix ι ι ℂ))
  rw [← hW, ← mul_assoc, Matrix.trace_mul_cycle]
  exact re_trace_unitary_mul_le_traceNorm A (U*W)

lemma traceNorm_mul_unitary (A : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    traceNorm (A * (U : Matrix ι ι ℂ)) = traceNorm A := by
  apply le_antisymm (traceNorm_mul_unitary_le A U)
  have h := traceNorm_mul_unitary_le (A * (U : Matrix ι ι ℂ)) (star U)
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose, mul_assoc,
    show (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 from U.prop.2, mul_one] using h

lemma traceNorm_posSemidef {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    traceNorm A = (trace A).re := by
  simp only [traceNorm, hA.isHermitian.eq, CFC.sqrt_mul_self A hA.nonneg]

lemma re_trace_le_traceNorm (A : Matrix ι ι ℂ) : (trace A).re ≤ traceNorm A := by
  simpa using re_trace_unitary_mul_le_traceNorm A 1

lemma traceNorm_conjTranspose_le (A : Matrix ι ι ℂ) : traceNorm Aᴴ ≤ traceNorm A := by
  obtain ⟨W,hW⟩ := exists_unitary_traceNorm Aᴴ
  have he : (trace ((W : Matrix ι ι ℂ) * Aᴴ)).re =
      (trace ((W : Matrix ι ι ℂ)ᴴ * A)).re := by
    have heq : (W : Matrix ι ι ℂ) * Aᴴ = (A * (W : Matrix ι ι ℂ)ᴴ)ᴴ := by simp
    rw [heq, Matrix.trace_conjTranspose, Matrix.trace_mul_comm]
    rfl
  rw [← hW, he]
  exact re_trace_unitary_mul_le_traceNorm A (star W)

lemma traceNorm_conjTranspose (A : Matrix ι ι ℂ) : traceNorm Aᴴ = traceNorm A := by
  apply le_antisymm (traceNorm_conjTranspose_le A)
  simpa only [Matrix.conjTranspose_conjTranspose] using traceNorm_conjTranspose_le Aᴴ

lemma traceNorm_transpose_le (A : Matrix ι ι ℂ) : traceNorm Aᵀ ≤ traceNorm A := by
  obtain ⟨W,hW⟩ := exists_unitary_traceNorm Aᵀ
  rw [← hW, ← Matrix.trace_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.trace_mul_comm]
  exact re_trace_unitary_mul_le_traceNorm A (Matrix.UnitaryGroup.transpose W)

lemma traceNorm_transpose (A : Matrix ι ι ℂ) : traceNorm Aᵀ = traceNorm A := by
  apply le_antisymm (traceNorm_transpose_le A)
  simpa only [Matrix.transpose_transpose] using traceNorm_transpose_le Aᵀ

def rootFidelity (H J : Matrix ι ι ℂ) : ℝ := traceNorm (CFC.sqrt H * CFC.sqrt J)

lemma polar_fidelity (A B : Matrix ι ι ℂ) :
    rootFidelity (Aᴴ * A) (Bᴴ * B) = traceNorm (A * Bᴴ) := by
  obtain ⟨U,hU⟩ := exists_unitary_polar A
  obtain ⟨V,hV⟩ := exists_unitary_polar B
  have hS : (CFC.sqrt (Bᴴ * B))ᴴ = CFC.sqrt (Bᴴ * B) :=
    (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq
  have he : A * Bᴴ = (U : Matrix ι ι ℂ) *
      (CFC.sqrt (Aᴴ*A) * CFC.sqrt (Bᴴ*B)) * ((star V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) := by
    conv_lhs => rw [hU, hV]
    simp only [Matrix.conjTranspose_mul, hS, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      mul_assoc]
  rw [he, traceNorm_mul_unitary, traceNorm_unitary_mul]
  rfl

end

section

universe v8268_0

variable {ι : Type v8268_0} [inst8268_0 : Fintype ι] [inst8268_1 : DecidableEq ι]

def unitSign (t : ℝ) := if 0 ≤ t then (1 : ℝ) else -1

lemma unitSign_square (t : ℝ) : unitSign t * unitSign t = 1 := by
  by_cases h : 0 ≤ t <;> simp [unitSign, h]

lemma signed_absolute (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    ∃ U : Matrix.unitaryGroup ι ℂ, Commute (U : Matrix ι ι ℂ) H ∧
      ((U : Matrix ι ι ℂ)*H - H).PosSemidef ∧
      ((U : Matrix ι ι ℂ)*H + H).PosSemidef := by
  let S := cfc unitSign H
  have hS : S.IsHermitian := IsSelfAdjoint.cfc
  have hSS : S*S=1 := by
    dsimp [S]
    rw [← matrix_cfc_mul _ _ H hH]
    simp only [unitSign_square, cfc_const_one ℝ H]
  have hSU : S ∈ Matrix.unitaryGroup ι ℂ := by
    constructor <;> simpa only [Matrix.star_eq_conjTranspose, hS.eq] using hSS
  have hc : Commute S H := (Commute.refl H).cfc_real _
  have hSH : S*H = cfc (fun t => unitSign t * t) H := by
    conv_lhs => arg 2; rw [← cfc_id ℝ H]
    rw [matrix_cfc_mul _ _ H hH]
    rfl
  refine ⟨⟨S,hSU⟩,hc,?_,?_⟩
  · change (S*H-H).PosSemidef
    have he : S*H-H = cfc (fun t => unitSign t*t-t) H := by
      rw [cfc_sub _ _ H (matrix_cfc_continuous _ H) (matrix_cfc_continuous _ H),
        show cfc (fun t : ℝ => t) H = H from cfc_id ℝ H, hSH]
    rw [he]
    apply LE.le.posSemidef
    apply cfc_nonneg
    intro t _
    by_cases ht : 0 ≤ t <;> simp [unitSign, ht]
    linarith
  · change (S*H+H).PosSemidef
    have he : S*H+H = cfc (fun t => unitSign t*t+t) H := by
      rw [cfc_add H _ _ (matrix_cfc_continuous _ H) (matrix_cfc_continuous _ H),
        show cfc (fun t : ℝ => t) H = H from cfc_id ℝ H, hSH]
    rw [he]
    apply LE.le.posSemidef
    apply cfc_nonneg
    intro t _
    by_cases ht : 0 ≤ t <;> simp [unitSign, ht]

lemma powers_stormer {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (trace ((A-B)*(A-B))).re ≤ traceNorm (A*A-B*B) := by
  obtain ⟨U,hUZ,hminus,hplus⟩ := signed_absolute (A-B) (hA.isHermitian.sub hB.isHermitian)
  let S : Matrix ι ι ℂ := U
  have h₁ := re_trace_mul_nonneg hminus hA
  have h₂ := re_trace_mul_nonneg hplus hB
  have hd := re_trace_unitary_mul_le_traceNorm (A*A-B*B) U
  have he : trace (S*(A*A-B*B)) = trace (S*(A-B)*(A+B)) := by
    have he₁ : A*A-B*B = (A-B)*A+B*(A-B) := by noncomm_ring
    rw [he₁, mul_add, Matrix.trace_add, ← mul_assoc]
    rw [show trace (S*(B*(A-B))) = trace (S*(A-B)*B) by
      rw [← mul_assoc, Matrix.trace_mul_cycle, ← hUZ.eq]]
    rw [← Matrix.trace_add, ← mul_add]
  have he₂ : (S*(A-B)-(A-B))*A + (S*(A-B)+(A-B))*B =
      S*(A-B)*(A+B) - (A-B)*(A-B) := by noncomm_ring
  have hsum := add_nonneg h₁ h₂
  change 0 ≤ (trace ((S*(A-B)-(A-B))*A)).re +
    (trace ((S*(A-B)+(A-B))*B)).re at hsum
  rw [← Complex.add_re, ← Matrix.trace_add, he₂, Matrix.trace_sub, Complex.sub_re,
    ← he] at hsum
  change (trace (S*(A*A-B*B))).re ≤ _ at hd
  linarith

lemma fidelity_lower {H J : Matrix ι ι ℂ} (hH : H.PosSemidef) (hJ : J.PosSemidef) :
    ((trace H).re + (trace J).re - traceNorm (H-J))/2 ≤ rootFidelity H J := by
  let A := CFC.sqrt H
  let B := CFC.sqrt J
  have hA : A.PosSemidef := (CFC.sqrt_nonneg H).posSemidef
  have hB : B.PosSemidef := (CFC.sqrt_nonneg J).posSemidef
  have hAA : A*A=H := CFC.sqrt_mul_sqrt_self H hH.nonneg
  have hBB : B*B=J := CFC.sqrt_mul_sqrt_self J hJ.nonneg
  have h := powers_stormer hA hB
  rw [hAA,hBB] at h
  have he : trace ((A-B)*(A-B)) = trace H + trace J - 2*trace (A*B) := by
    simp only [sub_mul, mul_sub, Matrix.trace_sub, hAA, hBB, Matrix.trace_mul_comm B A]
    ring
  rw [he, Complex.sub_re, Complex.add_re, Complex.mul_re] at h
  have hb := re_trace_le_traceNorm (A*B)
  change _ ≤ traceNorm (A*B)
  norm_num at h
  linarith

end

section

universe v8360_0

variable {ι : Type v8360_0} [inst8360_0 : Fintype ι] [inst8360_1 : DecidableEq ι]

lemma traceNorm_neg (A : Matrix ι ι ℂ) : traceNorm (-A) = traceNorm A := by
  simp only [traceNorm, Matrix.conjTranspose_neg, neg_mul_neg]

lemma traceNorm_sub_comm (A B : Matrix ι ι ℂ) : traceNorm (A-B) = traceNorm (B-A) := by
  rw [← neg_sub B A, traceNorm_neg]

lemma abs_re_trace_le_traceNorm (A : Matrix ι ι ℂ) : |(trace A).re| ≤ traceNorm A := by
  apply abs_le.mpr
  constructor
  · have h := re_trace_le_traceNorm (-A)
    rw [Matrix.trace_neg, Complex.neg_re, traceNorm_neg] at h
    linarith
  · exact re_trace_le_traceNorm A

lemma traceNorm_smul_nonneg (A : Matrix ι ι ℂ) {r : ℝ} (hr : 0 ≤ r) :
    traceNorm (r • A) = r * traceNorm A := by
  have he (U : Matrix.unitaryGroup ι ℂ) :
      (trace ((U : Matrix ι ι ℂ) * (r • A))).re = r * (trace ((U : Matrix ι ι ℂ)*A)).re := by
    simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply le_antisymm
  · obtain ⟨U,hU⟩ := exists_unitary_traceNorm (r • A)
    rw [← hU, he]
    exact mul_le_mul_of_nonneg_left (re_trace_unitary_mul_le_traceNorm A U) hr
  · obtain ⟨U,hU⟩ := exists_unitary_traceNorm A
    have h := re_trace_unitary_mul_le_traceNorm (r • A) U
    rwa [he, hU] at h

lemma sqrt_transpose {H : Matrix ι ι ℂ} (hH : H.PosSemidef) :
    CFC.sqrt Hᵀ = (CFC.sqrt H)ᵀ := by
  apply CFC.sqrt_unique
  · rw [← Matrix.transpose_mul, CFC.sqrt_mul_sqrt_self H hH.nonneg]
  · exact ((CFC.sqrt_nonneg H).posSemidef.transpose).nonneg

lemma rootFidelity_symm (H J : Matrix ι ι ℂ) : rootFidelity H J = rootFidelity J H := by
  dsimp [rootFidelity]
  rw [← traceNorm_conjTranspose, Matrix.conjTranspose_mul,
    (CFC.sqrt_nonneg H).posSemidef.isHermitian.eq,
    (CFC.sqrt_nonneg J).posSemidef.isHermitian.eq]

lemma rootFidelity_transpose {H J : Matrix ι ι ℂ} (hH : H.PosSemidef) (hJ : J.PosSemidef) :
    rootFidelity Hᵀ Jᵀ = rootFidelity H J := by
  dsimp [rootFidelity]
  rw [sqrt_transpose hH, sqrt_transpose hJ, ← Matrix.transpose_mul, traceNorm_transpose]
  exact rootFidelity_symm J H

lemma eveBlock_positive (R : Matrix ι ι ℂ) {D : Matrix ι ι ℂ} (hD : D.PosSemidef) :
    (eveBlock R D).PosSemidef := by
  apply Matrix.PosSemidef.transpose
  simpa only [(CFC.sqrt_nonneg R).posSemidef.isHermitian.eq] using
    hD.mul_mul_conjTranspose_same (CFC.sqrt R)

lemma trace_eveBlock {R : Matrix ι ι ℂ} (hR : R.PosSemidef) (D : Matrix ι ι ℂ) :
    trace (eveBlock R D) = trace (D*R) := by
  rw [eveBlock, Matrix.trace_transpose, Matrix.trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self R hR.nonneg, Matrix.trace_mul_comm]

lemma fidelity_eveBlock {R D₀ D₁ : Matrix ι ι ℂ} (hR : R.PosSemidef)
    (hD₀ : D₀.PosSemidef) (hD₁ : D₁.PosSemidef) :
    rootFidelity (eveBlock R D₀) (eveBlock R D₁) =
      traceNorm (CFC.sqrt D₀ * R * CFC.sqrt D₁) := by
  let A := CFC.sqrt D₀ * CFC.sqrt R
  let B := CFC.sqrt D₁ * CFC.sqrt R
  have hA : Aᴴ*A = CFC.sqrt R * D₀ * CFC.sqrt R := by
    dsimp [A]
    simp only [Matrix.conjTranspose_mul, (CFC.sqrt_nonneg R).posSemidef.isHermitian.eq,
      (CFC.sqrt_nonneg D₀).posSemidef.isHermitian.eq]
    rw [mul_assoc, ← mul_assoc (CFC.sqrt D₀), CFC.sqrt_mul_sqrt_self D₀ hD₀.nonneg, ← mul_assoc]
  have hB : Bᴴ*B = CFC.sqrt R * D₁ * CFC.sqrt R := by
    dsimp [B]
    simp only [Matrix.conjTranspose_mul, (CFC.sqrt_nonneg R).posSemidef.isHermitian.eq,
      (CFC.sqrt_nonneg D₁).posSemidef.isHermitian.eq]
    rw [mul_assoc, ← mul_assoc (CFC.sqrt D₁), CFC.sqrt_mul_sqrt_self D₁ hD₁.nonneg, ← mul_assoc]
  have hAB : A*Bᴴ = CFC.sqrt D₀ * R * CFC.sqrt D₁ := by
    dsimp [A,B]
    simp only [Matrix.conjTranspose_mul, (CFC.sqrt_nonneg R).posSemidef.isHermitian.eq,
      (CFC.sqrt_nonneg D₁).posSemidef.isHermitian.eq]
    rw [mul_assoc, ← mul_assoc (CFC.sqrt R), CFC.sqrt_mul_sqrt_self R hR.nonneg, ← mul_assoc]
  rw [eveBlock, eveBlock, ← hA, ← hB,
    rootFidelity_transpose (Matrix.posSemidef_conjTranspose_mul_self A)
      (Matrix.posSemidef_conjTranspose_mul_self B), polar_fidelity, hAB]

end

section

open scoped Matrix.Norms.L2Operator

universe v8454_0

variable {ι : Type v8454_0} [inst8454_0 : Fintype ι] [inst8454_1 : DecidableEq ι]

open scoped Matrix.Norms.L2Operator in
lemma continuous_traceNorm : Continuous (traceNorm : Matrix ι ι ℂ → ℝ) := by
  have h : Continuous (CFC.abs : Matrix ι ι ℂ → Matrix ι ι ℂ) := CFC.continuous_abs
  change Continuous (fun A : Matrix ι ι ℂ => (trace (CFC.abs A)).re)
  unfold Matrix.trace Matrix.diag
  fun_prop

universe v8463_0

variable {Ω : Type v8463_0} [inst8463_0 : MeasurableSpace Ω]

lemma measurable_traceNorm {F : Ω → Matrix ι ι ℂ} (hF : Measurable F) :
    Measurable (fun t => traceNorm (F t)) := continuous_traceNorm.measurable.comp hF

open scoped Matrix.Norms.L2Operator in
lemma measurable_sqrt_psd {F : Ω → Matrix ι ι ℂ}
    (hF : Measurable F) (hpos : ∀ t, (F t).PosSemidef) :
    Measurable (fun t => CFC.sqrt (F t)) := by
  let G : Ω → {A : Matrix ι ι ℂ // 0 ≤ A} := fun t => ⟨F t,(hpos t).nonneg⟩
  have hG : Measurable G := hF.subtype_mk
  have hC : Continuous (fun A : {A : Matrix ι ι ℂ // 0 ≤ A} => CFC.sqrt A.1) :=
    continuousOn_iff_continuous_domRestrict.mp CFC.continuousOn_sqrt
  exact hC.measurable.comp hG

lemma measurable_rootFidelity {F G : Ω → Matrix ι ι ℂ}
    (hF : Measurable F) (hG : Measurable G)
    (hFp : ∀ t, (F t).PosSemidef) (hGp : ∀ t, (G t).PosSemidef) :
    Measurable (fun t => rootFidelity (F t) (G t)) := by
  have h₁ := measurable_sqrt_psd hF hFp
  have h₂ := measurable_sqrt_psd hG hGp
  apply measurable_traceNorm
  exact h₁.mul h₂

omit inst8454_1 in
lemma measurable_re_trace [DecidableEq ι] {F : Ω → Matrix ι ι ℂ} (hF : Measurable F) :
    Measurable (fun t => (trace (F t)).re) := by
  have h : Continuous (fun A : Matrix ι ι ℂ => (trace A).re) := by
    unfold Matrix.trace Matrix.diag
    fun_prop
  exact h.measurable.comp hF

lemma traceNorm_sub_le_trace {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    traceNorm (A-B) ≤ (trace A).re + (trace B).re := by
  have h := traceNorm_add_le A (-B)
  rwa [← sub_eq_add_neg, traceNorm_posSemidef hA, traceNorm_neg, traceNorm_posSemidef hB] at h

lemma traceNorm_sub_integrable {μ : MeasureTheory.Measure Ω} {F G : Ω → Matrix ι ι ℂ}
    (hF : Measurable F) (hG : Measurable G)
    (hFp : ∀ t, (F t).PosSemidef) (hGp : ∀ t, (G t).PosSemidef)
    (hFi : MeasureTheory.Integrable (fun t => (trace (F t)).re) μ)
    (hGi : MeasureTheory.Integrable (fun t => (trace (G t)).re) μ) :
    MeasureTheory.Integrable (fun t => traceNorm (F t-G t)) μ := by
  apply (hFi.add hGi).mono' (measurable_traceNorm (hF.sub hG)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_of_nonneg (traceNorm_nonneg _)]
    exact traceNorm_sub_le_trace (hFp t) (hGp t)

end

open MeasureTheory

section

universe v8517_0

variable {Ω : Type v8517_0} [inst8517_0 : MeasurableSpace Ω] {μ : Measure Ω}

lemma memLp_sqrt {p : Ω → ℝ} (hp : Integrable p μ) (hp0 : ∀ t, 0 ≤ p t) :
    MemLp (fun t => Real.sqrt (p t)) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hp.aemeasurable.sqrt.aestronglyMeasurable)).mpr
  simpa only [Real.sq_sqrt (hp0 _)] using hp

lemma sqrt_product_integrable {p q : Ω → ℝ} (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ t, 0 ≤ p t) (hq0 : ∀ t, 0 ≤ q t) :
    Integrable (fun t => Real.sqrt (p t*q t)) μ := by
  have hp₂ := memLp_sqrt hp hp0
  have hq₂ := memLp_sqrt hq hq0
  have h := hp₂.integrable_mul hq₂
  change Integrable (fun t => Real.sqrt (p t) * Real.sqrt (q t)) μ at h
  simpa only [Real.sqrt_mul (hp0 _)] using h

lemma integral_sqrt_product_le {p q : Ω → ℝ} (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ t, 0 ≤ p t) (hq0 : ∀ t, 0 ≤ q t) :
    (∫ t, Real.sqrt (p t*q t) ∂μ) ≤ Real.sqrt ((∫ t, p t ∂μ)*(∫ t, q t ∂μ)) := by
  have hp₂ := memLp_sqrt hp hp0
  have hq₂ := memLp_sqrt hq hq0
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (Real.HolderConjugate.two_two)
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (p t)))
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (q t))) (by simpa using hp₂) (by simpa using hq₂)
  simp only [Real.rpow_two, Real.sq_sqrt (hp0 _), Real.sq_sqrt (hq0 _),
    ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (hp0 _)] at h
  rw [Real.sqrt_mul (integral_nonneg hp0)]
  exact h

end

section

lemma uniform_gap_arithmetic {e η f : ℝ} (_he0 : 0 ≤ e) (heη : e ≤ η/2)
    (hlower : (1-η)/2 ≤ f) (hupper : f ≤ Real.sqrt (e*(1-e))+e) : 1/5 ≤ η := by
  by_contra h
  have hη : η < 1/5 := lt_of_not_ge h
  have he : e < 1/10 := by linarith
  have hprod : e*(1-e) < (3/10 : ℝ)^2 := by
    have h := mul_pos (sub_pos.mpr he) (show 0 < (9/10 : ℝ)-e by linarith)
    nlinarith
  have hs : Real.sqrt (e*(1-e)) < 3/10 := (Real.sqrt_lt' (by norm_num)).mpr hprod
  linarith

lemma two_term_root_cauchy {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a*b)+Real.sqrt (c*d) ≤ Real.sqrt ((a+d)*(b+c)) := by
  have h₁ := Real.mul_self_sqrt (mul_nonneg ha hb)
  have h₂ := Real.mul_self_sqrt (mul_nonneg hc hd)
  have h₃ := Real.mul_self_sqrt (mul_nonneg ha hc)
  have h₄ := Real.mul_self_sqrt (mul_nonneg hb hd)
  have he : Real.sqrt (a*b)*Real.sqrt (c*d) = Real.sqrt (a*c)*Real.sqrt (b*d) := by
    rw [← Real.sqrt_mul (mul_nonneg ha hb), ← Real.sqrt_mul (mul_nonneg ha hc)]
    congr 1
    ring
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  have h := sq_nonneg (Real.sqrt (a*c)-Real.sqrt (b*d))
  nlinarith

lemma root_cross_le_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2*Real.sqrt (a*b) ≤ a+b := by
  have h := sq_nonneg (Real.sqrt a - Real.sqrt b)
  rw [Real.sqrt_mul ha]
  nlinarith [Real.mul_self_sqrt ha, Real.mul_self_sqrt hb]

open scoped Matrix.Norms.L2Operator

universe v8592_0 v8592_1

variable {ι : Type v8592_0} {Ω : Type v8592_1} [inst8592_0 : Fintype ι] [inst8592_1 : DecidableEq ι] [inst8592_2 : MeasurableSpace Ω]

lemma rootFidelity_le_sqrt_trace {H J : Matrix ι ι ℂ}
    (hH : H.PosSemidef) (hJ : J.PosSemidef) :
    rootFidelity H J ≤ Real.sqrt ((trace H).re*(trace J).re) := by
  have h := traceNorm_mul_conjTranspose_le (CFC.sqrt H) (CFC.sqrt J)
  simpa only [(CFC.sqrt_nonneg H).posSemidef.isHermitian.eq,
    (CFC.sqrt_nonneg J).posSemidef.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self H hH.nonneg, CFC.sqrt_mul_sqrt_self J hJ.nonneg,
    rootFidelity] using h

lemma rootFidelity_integrable {μ : Measure Ω} {F G : Ω → Matrix ι ι ℂ}
    (hF : Measurable F) (hG : Measurable G)
    (hFp : ∀ t, (F t).PosSemidef) (hGp : ∀ t, (G t).PosSemidef)
    (hFi : Integrable (fun t => (trace (F t)).re) μ)
    (hGi : Integrable (fun t => (trace (G t)).re) μ) :
    Integrable (fun t => rootFidelity (F t) (G t)) μ := by
  apply (sqrt_product_integrable hFi hGi (fun t => re_trace_nonneg (hFp t))
    (fun t => re_trace_nonneg (hGp t))).mono'
      (measurable_rootFidelity hF hG hFp hGp).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_of_nonneg (show 0 ≤ rootFidelity (F t) (G t) from traceNorm_nonneg _)]
    exact rootFidelity_le_sqrt_trace (hFp t) (hGp t)

lemma traceNorm_sub_triangle (A B C : Matrix ι ι ℂ) :
    traceNorm (A-B) ≤ traceNorm (A-C)+traceNorm (B-C) := by
  have h := traceNorm_add_le (A-C) (C-B)
  rwa [sub_add_sub_cancel, traceNorm_sub_comm C B] at h

lemma trace_difference_le_norm (A B : Matrix ι ι ℂ) :
    (trace B).re-(trace A).re ≤ traceNorm (A-B) := by
  have h := re_trace_le_traceNorm (B-A)
  rwa [Matrix.trace_sub, Complex.sub_re, traceNorm_sub_comm B A] at h

end

section

open scoped Matrix.Norms.L2Operator

universe v8632_0 v8632_1

variable {ι : Type v8632_0} {Ω : Type v8632_1} [inst8632_0 : Fintype ι] [inst8632_1 : DecidableEq ι] [inst8632_2 : MeasurableSpace Ω]

lemma density_uniform_gap {μ : Measure Ω} (τ : BitDensity μ ι)
    (hcoherence : ∀ t, rootFidelity (τ.block false false t) (τ.block true true t) ≤
      Real.sqrt ((trace (τ.block false false t)).re*(trace (τ.block false true t)).re) +
      Real.sqrt ((trace (τ.block true false t)).re*(trace (τ.block true true t)).re) +
      2*Real.sqrt ((trace (τ.block false true t)).re*(trace (τ.block true false t)).re))
    (σ : Ω → Matrix ι ι ℂ) (hσ : Measurable σ) (hσp : ∀ t, (σ t).PosSemidef)
    (hσi : Integrable (fun t => (trace (σ t)).re) μ)
    (hσn : (∫ t, (trace (σ t)).re ∂μ) = 1) :
    1/5 ≤ τ.idealBitError σ := by
  let p := fun i j t => (trace (τ.block i j t)).re
  let P := fun i j => τ.mass i j
  let e := P false true + P true false
  let f := ∫ t, rootFidelity (τ.block false false t) (τ.block true true t) ∂μ
  let S := fun t => (1/2 : ℝ) • σ t
  let q := ∫ t, traceNorm (τ.block false false t-τ.block true true t) ∂μ
  let a₀ := ∫ t, traceNorm (τ.block false false t-S t) ∂μ
  let a₁ := ∫ t, traceNorm (τ.block true true t-S t) ∂μ
  have hp (i j : Bool) (t : Ω) : 0 ≤ p i j t := re_trace_nonneg (τ.positive i j t)
  have hP (i j : Bool) : 0 ≤ P i j := integral_nonneg (hp i j)
  have hPn : P false false + P false true+P true false+P true true=1 := τ.normalized
  have hfi : Integrable (fun t => rootFidelity (τ.block false false t)
      (τ.block true true t)) μ := rootFidelity_integrable (τ.measurable _ _) (τ.measurable _ _)
        (τ.positive _ _) (τ.positive _ _) (τ.integrable _ _) (τ.integrable _ _)
  have h₁ := sqrt_product_integrable (τ.integrable false false) (τ.integrable false true)
    (hp false false) (hp false true)
  have h₂ := sqrt_product_integrable (τ.integrable true false) (τ.integrable true true)
    (hp true false) (hp true true)
  have h₃ := sqrt_product_integrable (τ.integrable false true) (τ.integrable true false)
    (hp false true) (hp true false)
  have hfupper : f ≤ Real.sqrt (P false false*P false true) +
      Real.sqrt (P true false*P true true)+2*Real.sqrt (P false true*P true false) := by
    have h := integral_mono hfi ((h₁.add h₂).add (h₃.const_mul 2)) hcoherence
    rw [integral_add' (h₁.add h₂) (h₃.const_mul 2), integral_add' h₁ h₂,
      integral_const_mul] at h
    have hc₁ := integral_sqrt_product_le (τ.integrable false false) (τ.integrable false true)
      (hp false false) (hp false true)
    have hc₂ := integral_sqrt_product_le (τ.integrable true false) (τ.integrable true true)
      (hp true false) (hp true true)
    have hc₃ := integral_sqrt_product_le (τ.integrable false true) (τ.integrable true false)
      (hp false true) (hp true false)
    change _ ≤ Real.sqrt (P false false*P false true) at hc₁
    change _ ≤ Real.sqrt (P true false*P true true) at hc₂
    change _ ≤ Real.sqrt (P false true*P true false) at hc₃
    dsimp [f]
    linarith
  have hqi : Integrable (fun t => traceNorm (τ.block false false t-τ.block true true t)) μ :=
    traceNorm_sub_integrable (τ.measurable _ _) (τ.measurable _ _) (τ.positive _ _)
      (τ.positive _ _) (τ.integrable _ _) (τ.integrable _ _)
  have hSm : Measurable S := hσ.const_smul (1/2 : ℝ)
  have hSp (t) : (S t).PosSemidef := (hσp t).smul (show (0:ℝ) ≤ 1/2 by norm_num)
  have hSt (t) : (trace (S t)).re = (1/2 : ℝ)*(trace (σ t)).re := by
    simp only [S, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hSi : Integrable (fun t => (trace (S t)).re) μ := by
    simpa only [hSt] using hσi.const_mul (1/2)
  have hSn : (∫ t, (trace (S t)).re ∂μ) = 1/2 := by
    simp only [hSt, integral_const_mul, hσn, mul_one]
  have ha₀i := traceNorm_sub_integrable (τ.measurable false false) hSm
    (τ.positive false false) hSp (τ.integrable false false) hSi
  have ha₁i := traceNorm_sub_integrable (τ.measurable true true) hSm
    (τ.positive true true) hSp (τ.integrable true true) hSi
  have hq : q ≤ a₀+a₁ := by
    have h := integral_mono hqi (ha₀i.add ha₁i) (fun t =>
      traceNorm_sub_triangle (τ.block false false t) (τ.block true true t) (S t))
    rwa [integral_add' ha₀i ha₁i] at h
  have ha₀ : 1/2-P false false ≤ a₀ := by
    have h := integral_mono (hSi.sub (τ.integrable false false)) ha₀i
      (fun t => trace_difference_le_norm (τ.block false false t) (S t))
    rwa [integral_sub' hSi (τ.integrable false false), hSn] at h
  have ha₁ : 1/2-P true true ≤ a₁ := by
    have h := integral_mono (hSi.sub (τ.integrable true true)) ha₁i
      (fun t => trace_difference_le_norm (τ.block true true t) (S t))
    rwa [integral_sub' hSi (τ.integrable true true), hSn] at h
  have hflower : (P false false+P true true-q)/2 ≤ f := by
    have hi := ((τ.integrable false false).add (τ.integrable true true)).sub hqi
    have h := integral_mono (hi.div_const 2) hfi (fun t =>
      fidelity_lower (τ.positive false false t) (τ.positive true true t))
    rwa [integral_div, integral_sub' ((τ.integrable false false).add
      (τ.integrable true true)) hqi, integral_add' (τ.integrable false false)
      (τ.integrable true true)] at h
  have he0 : 0 ≤ e := add_nonneg (hP _ _) (hP _ _)
  have hη : τ.idealBitError σ = e+a₀+a₁ := rfl
  have heη : e ≤ τ.idealBitError σ/2 := by rw [hη]; dsimp [e]; linarith
  have hlow : (1-τ.idealBitError σ)/2 ≤ f := by rw [hη]; dsimp [e]; linarith
  have hup : f ≤ Real.sqrt (e*(1-e))+e := by
    have hc := two_term_root_cauchy (hP false false) (hP false true)
      (hP true false) (hP true true)
    have hx := root_cross_le_sum (hP false true) (hP true false)
    have heq : (P false false+P true true)*(P false true+P true false)=e*(1-e) := by
      have hn : P false false+P true true=1-e := by dsimp [e]; linarith
      rw [hn]
      exact mul_comm _ _
    rw [heq] at hc
    change 2*Real.sqrt (P false true*P true false) ≤ e at hx
    linarith
  exact uniform_gap_arithmetic he0 heη hlow hup

end

open scoped Matrix.Norms.L2Operator

universe v8764_0

theorem class_factor_density_uniform_gap {a b : ℕ} {Ω : Type v8764_0} [MeasurableSpace Ω]
    {μ : Measure Ω} (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : InClass R)
    (τ : BitDensity μ (Fin a × Fin b)) (X : Bool → Ω → Mat a) (Y : Bool → Ω → Mat b)
    (hX : ∀ i t, (X i t).PosSemidef) (hY : ∀ j t, (Y j t).PosSemidef)
    (hblock : ∀ i j t, τ.block i j t = eveBlock R (X i t ⊗ₖ Y j t))
    (σ : Ω → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hσ : Measurable σ) (hσp : ∀ t, (σ t).PosSemidef)
    (hσi : Integrable (fun t => (trace (σ t)).re) μ)
    (hσn : (∫ t, (trace (σ t)).re ∂μ) = 1) :
    1/5 ≤ τ.idealBitError σ := by
  apply density_uniform_gap τ _ σ hσ hσp hσi hσn
  intro t
  have ht (i j) : (trace (τ.block i j t)).re = weight R (X i t) (Y j t) := by
    rw [hblock, trace_eveBlock hR.1.1]
    rfl
  simp only [ht]
  rw [hblock, hblock, fidelity_eveBlock hR.1.1 ((hX false t).kronecker (hY false t))
      ((hX true t).kronecker (hY true t))]
  exact four_effect_inequality R hR (X false t) (X true t) (Y false t) (Y true t)
    (hX false t) (hX true t) (hY false t) (hY true t)

end

section

open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

open Matrix MeasureTheory ProbabilityTheory

universe v8797_0 v8797_1

variable {Ω : Type v8797_0} {ι : Type v8797_1} [inst8797_0 : MeasurableSpace Ω] [inst8797_1 : Fintype ι] [inst8797_2 : DecidableEq ι]

omit inst8797_2 in
lemma real_trace_smul [DecidableEq ι] (r : ℝ) (A : Matrix ι ι ℂ) :
    (trace (r • A)).re = r * (trace A).re := by
  simp [Matrix.trace_smul,Complex.real_smul,Complex.mul_re]

namespace BitDensity

variable {μ ν : Measure Ω} [inst8804_0 : SigmaFinite μ] [inst8804_1 : SigmaFinite ν]

def changeMeasure (τ : BitDensity μ ι) (hμν : μ ≪ ν) : BitDensity ν ι where
  block i j t := (μ.rnDeriv ν t).toReal • τ.block i j t
  positive i j t := (τ.positive i j t).smul ENNReal.toReal_nonneg
  measurable i j := (Measure.measurable_rnDeriv μ ν).ennreal_toReal.smul (τ.measurable i j)
  integrable i j := by
    simp only [real_trace_smul]
    exact (integrable_toReal_rnDeriv_mul_iff hμν).mpr (τ.integrable i j)
  normalized := by
    simp only [real_trace_smul,integral_toReal_rnDeriv_mul hμν]
    exact τ.normalized

lemma changeMeasure_mass (τ : BitDensity μ ι) (hμν : μ ≪ ν) (i j : Bool) :
    (τ.changeMeasure hμν).mass i j = τ.mass i j := by
  simp only [mass,changeMeasure,real_trace_smul,integral_toReal_rnDeriv_mul hμν]

lemma changeMeasure_idealBitError (τ : BitDensity μ ι) (hμν : μ ≪ ν)
    (σ : Ω → Matrix ι ι ℂ) :
    (τ.changeMeasure hμν).idealBitError (fun t => (μ.rnDeriv ν t).toReal • σ t) =
      τ.idealBitError σ := by
  have he (A B : Matrix ι ι ℂ) (r : ℝ) (hr : 0 ≤ r) :
      traceNorm (r • A - (1/2 : ℝ) • (r • B)) = r * traceNorm (A - (1/2 : ℝ) • B) := by
    rw [smul_comm (1/2 : ℝ) r B, ← smul_sub, traceNorm_smul_nonneg _ hr]
  simp only [idealBitError,changeMeasure_mass]
  simp only [changeMeasure,he _ _ _ ENNReal.toReal_nonneg,
    integral_toReal_rnDeriv_mul hμν]

end BitDensity

lemma eveBlock_smul_local {a b : ℕ} (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (X : Mat a) (Y : Mat b) (r : ℝ) :
    eveBlock R ((r • X) ⊗ₖ Y) = r • eveBlock R (X ⊗ₖ Y) := by
  simp only [eveBlock, Matrix.smul_kronecker,Matrix.mul_smul,smul_mul_assoc,
    Matrix.transpose_smul]

theorem class_factor_gap_dominating_measure {a b : ℕ}
    {μ ν : Measure Ω} [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν)
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : InClass R)
    (τ : BitDensity μ (Fin a × Fin b)) (X : Bool → Ω → Mat a) (Y : Bool → Ω → Mat b)
    (hX : ∀ i t, (X i t).PosSemidef) (hY : ∀ j t, (Y j t).PosSemidef)
    (hblock : ∀ i j t, τ.block i j t = eveBlock R (X i t ⊗ₖ Y j t))
    (σ : Ω → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hσ : Measurable σ) (hσp : ∀ t, (σ t).PosSemidef)
    (hσi : Integrable (fun t => (trace (σ t)).re) ν)
    (hσn : (∫ t, (trace (σ t)).re ∂ν) = 1) :
    1/5 ≤ (τ.changeMeasure hμν).idealBitError σ := by
  apply class_factor_density_uniform_gap R hR (τ.changeMeasure hμν)
    (fun i t => (μ.rnDeriv ν t).toReal • X i t) Y
    (fun i t => (hX i t).smul ENNReal.toReal_nonneg) hY
    _ σ hσ hσp hσi hσn
  intro i j t
  change (μ.rnDeriv ν t).toReal • τ.block i j t = _
  rw [hblock,eveBlock_smul_local]

end

section

open Matrix MeasureTheory ProbabilityTheory Function unitInterval Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

open UnrestrictedQuantum

universe v8979_0 v8979_1 v8979_2 v8979_3 v8979_4 v8979_5 v8979_6 v8979_7 v8979_8 v8979_9

variable {O : Type v8979_0} {M : Type v8979_1} {ι : Type v8979_2} {η : Type v8979_3} [inst8979_0 : MeasurableSpace O] [inst8979_1 : MeasurableSpace M]
  [inst8979_2 : StandardBorelSpace O] [inst8979_3 : Nonempty O] [inst8979_4 : StandardBorelSpace M] [inst8979_5 : Nonempty M]
  [inst8979_6 : Fintype ι] [inst8979_7 : Fintype η] [inst8979_8 : DecidableEq ι] [inst8979_9 : DecidableEq η]
  (d : Discussion O M)
  (A : ℕ → Type v8979_4) (B : ℕ → Type v8979_5)
  [inst8979_10 : ∀ n, AddCommGroup (A n)] [inst8979_11 : ∀ n, Module ℂ (A n)] [inst8979_12 : ∀ n, One (A n)] [inst8979_13 : ∀ n, LE (A n)]
  [inst8979_14 : ∀ n, AddCommGroup (B n)] [inst8979_15 : ∀ n, Module ℂ (B n)] [inst8979_16 : ∀ n, One (B n)] [inst8979_17 : ∀ n, LE (B n)]
  (TA : Type v8979_6) (TB : Type v8979_7) (CA : Type v8979_8) (CB : Type v8979_9)
  [inst8979_18 : AddCommGroup TA] [inst8979_19 : Module ℂ TA] [inst8979_20 : One TA] [inst8979_21 : LE TA]
  [inst8979_22 : AddCommGroup TB] [inst8979_23 : Module ℂ TB] [inst8979_24 : One TB] [inst8979_25 : LE TB]
  [inst8979_26 : AddCommGroup CA] [inst8979_27 : Module ℂ CA] [inst8979_28 : One CA] [inst8979_29 : LE CA]
  [inst8979_30 : AddCommGroup CB] [inst8979_31 : Module ℂ CB] [inst8979_32 : One CB] [inst8979_33 : LE CB]

variable {d A B TA TB CA CB}

namespace BitProtocol

variable (p : BitProtocol (ι := ι) (η := η) d A B TA TB CA CB)

lemma canonicalOutput_event (R : Matrix (ι × η) (ι × η) ℂ)
    (i j : Bool) (S : Set (ℕ → M)) (hS : MeasurableSet S) :
    (p.canonicalOutput R i j).value S =
      ∫ x in d.sampler.publicRecord ⁻¹' S,
        preparationFilter R * p.completeReference i j x * (preparationFilter R)ᴴ ∂d.probeLaw := by
  rw [canonicalOutput,PositiveMatrixMeasure.filter_value,p.probeOutput_event i j S hS,
    integral_filter _ (p.completeReference_integrable i j).integrableOn]

end BitProtocol

end

section

open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

open Matrix MeasureTheory ProbabilityTheory Filter

universe v9125_0 v9125_1

variable {ι : Type v9125_0} {Ω : Type v9125_1} [inst9125_0 : Fintype ι] [inst9125_1 : DecidableEq ι] [inst9125_2 : MeasurableSpace Ω]

lemma density_uniform_gap_ae {μ : Measure Ω} (τ : BitDensity μ ι)
    (hcoherence : ∀ᵐ t ∂μ, rootFidelity (τ.block false false t) (τ.block true true t) ≤
      Real.sqrt ((trace (τ.block false false t)).re*(trace (τ.block false true t)).re) +
      Real.sqrt ((trace (τ.block true false t)).re*(trace (τ.block true true t)).re) +
      2*Real.sqrt ((trace (τ.block false true t)).re*(trace (τ.block true false t)).re))
    (σ : Ω → Matrix ι ι ℂ) (hσ : Measurable σ) (hσp : ∀ t, (σ t).PosSemidef)
    (hσi : Integrable (fun t => (trace (σ t)).re) μ)
    (hσn : (∫ t, (trace (σ t)).re ∂μ) = 1) :
    1/5 ≤ τ.idealBitError σ := by
  let p := fun i j t => (trace (τ.block i j t)).re
  let P := fun i j => τ.mass i j
  let e := P false true + P true false
  let f := ∫ t, rootFidelity (τ.block false false t) (τ.block true true t) ∂μ
  let S := fun t => (1/2 : ℝ) • σ t
  let q := ∫ t, traceNorm (τ.block false false t-τ.block true true t) ∂μ
  let a₀ := ∫ t, traceNorm (τ.block false false t-S t) ∂μ
  let a₁ := ∫ t, traceNorm (τ.block true true t-S t) ∂μ
  have hp (i j : Bool) (t : Ω) : 0 ≤ p i j t := re_trace_nonneg (τ.positive i j t)
  have hP (i j : Bool) : 0 ≤ P i j := integral_nonneg (hp i j)
  have hPn : P false false + P false true+P true false+P true true=1 := τ.normalized
  have hfi : Integrable (fun t => rootFidelity (τ.block false false t)
      (τ.block true true t)) μ := rootFidelity_integrable (τ.measurable _ _) (τ.measurable _ _)
        (τ.positive _ _) (τ.positive _ _) (τ.integrable _ _) (τ.integrable _ _)
  have h₁ := sqrt_product_integrable (τ.integrable false false) (τ.integrable false true)
    (hp false false) (hp false true)
  have h₂ := sqrt_product_integrable (τ.integrable true false) (τ.integrable true true)
    (hp true false) (hp true true)
  have h₃ := sqrt_product_integrable (τ.integrable false true) (τ.integrable true false)
    (hp false true) (hp true false)
  have hfupper : f ≤ Real.sqrt (P false false*P false true) +
      Real.sqrt (P true false*P true true)+2*Real.sqrt (P false true*P true false) := by
    have h := integral_mono_ae hfi ((h₁.add h₂).add (h₃.const_mul 2)) hcoherence
    rw [integral_add' (h₁.add h₂) (h₃.const_mul 2), integral_add' h₁ h₂,
      integral_const_mul] at h
    have hc₁ := integral_sqrt_product_le (τ.integrable false false) (τ.integrable false true)
      (hp false false) (hp false true)
    have hc₂ := integral_sqrt_product_le (τ.integrable true false) (τ.integrable true true)
      (hp true false) (hp true true)
    have hc₃ := integral_sqrt_product_le (τ.integrable false true) (τ.integrable true false)
      (hp false true) (hp true false)
    change _ ≤ Real.sqrt (P false false*P false true) at hc₁
    change _ ≤ Real.sqrt (P true false*P true true) at hc₂
    change _ ≤ Real.sqrt (P false true*P true false) at hc₃
    dsimp [f]
    linarith
  have hqi : Integrable (fun t => traceNorm (τ.block false false t-τ.block true true t)) μ :=
    traceNorm_sub_integrable (τ.measurable _ _) (τ.measurable _ _) (τ.positive _ _)
      (τ.positive _ _) (τ.integrable _ _) (τ.integrable _ _)
  have hSm : Measurable S := hσ.const_smul (1/2 : ℝ)
  have hSp (t) : (S t).PosSemidef := (hσp t).smul (show (0:ℝ) ≤ 1/2 by norm_num)
  have hSt (t) : (trace (S t)).re = (1/2 : ℝ)*(trace (σ t)).re := by
    simp only [S, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hSi : Integrable (fun t => (trace (S t)).re) μ := by
    simpa only [hSt] using hσi.const_mul (1/2)
  have hSn : (∫ t, (trace (S t)).re ∂μ) = 1/2 := by
    simp only [hSt, integral_const_mul, hσn, mul_one]
  have ha₀i := traceNorm_sub_integrable (τ.measurable false false) hSm
    (τ.positive false false) hSp (τ.integrable false false) hSi
  have ha₁i := traceNorm_sub_integrable (τ.measurable true true) hSm
    (τ.positive true true) hSp (τ.integrable true true) hSi
  have hq : q ≤ a₀+a₁ := by
    have h := integral_mono hqi (ha₀i.add ha₁i) (fun t =>
      traceNorm_sub_triangle (τ.block false false t) (τ.block true true t) (S t))
    rwa [integral_add' ha₀i ha₁i] at h
  have ha₀ : 1/2-P false false ≤ a₀ := by
    have h := integral_mono (hSi.sub (τ.integrable false false)) ha₀i
      (fun t => trace_difference_le_norm (τ.block false false t) (S t))
    rwa [integral_sub' hSi (τ.integrable false false), hSn] at h
  have ha₁ : 1/2-P true true ≤ a₁ := by
    have h := integral_mono (hSi.sub (τ.integrable true true)) ha₁i
      (fun t => trace_difference_le_norm (τ.block true true t) (S t))
    rwa [integral_sub' hSi (τ.integrable true true), hSn] at h
  have hflower : (P false false+P true true-q)/2 ≤ f := by
    have hi := ((τ.integrable false false).add (τ.integrable true true)).sub hqi
    have h := integral_mono (hi.div_const 2) hfi (fun t =>
      fidelity_lower (τ.positive false false t) (τ.positive true true t))
    rwa [integral_div, integral_sub' ((τ.integrable false false).add
      (τ.integrable true true)) hqi, integral_add' (τ.integrable false false)
      (τ.integrable true true)] at h
  have he0 : 0 ≤ e := add_nonneg (hP _ _) (hP _ _)
  have hη : τ.idealBitError σ = e+a₀+a₁ := rfl
  have heη : e ≤ τ.idealBitError σ/2 := by rw [hη]; dsimp [e]; linarith
  have hlow : (1-τ.idealBitError σ)/2 ≤ f := by rw [hη]; dsimp [e]; linarith
  have hup : f ≤ Real.sqrt (e*(1-e))+e := by
    have hc := two_term_root_cauchy (hP false false) (hP false true)
      (hP true false) (hP true true)
    have hx := root_cross_le_sum (hP false true) (hP true false)
    have heq : (P false false+P true true)*(P false true+P true false)=e*(1-e) := by
      have hn : P false false+P true true=1-e := by dsimp [e]; linarith
      rw [hn]
      exact mul_comm _ _
    rw [heq] at hc
    change 2*Real.sqrt (P false true*P true false) ≤ e at hx
    linarith
  exact uniform_gap_arithmetic he0 heη hlow hup

end

section

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace PositiveMatrixMeasure

universe v9319_0 v9319_1

variable {Ω : Type v9319_0} {ι : Type v9319_1} [inst9319_0 : MeasurableSpace Ω] [inst9319_1 : Fintype ι] [inst9319_2 : DecidableEq ι]
  (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) [inst9319_3 : SigmaFinite μ]

lemma integral_density
    (hAC : ∀ S, MeasurableSet S → μ S = 0 → W.value S = 0)
    (S : Set Ω) (hS : MeasurableSet S) :
    (∫ t in S, W.density μ t ∂μ) = W.value S := by
  ext i j
  let L := (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap
  have he := L.integral_comp_comm ((W.integrable_density μ).integrableOn (s := S))
  exact he.symm.trans (W.integral_density_entry μ hAC S hS i j)

lemma density_eq_ae {F : Ω → Matrix ι ι ℂ} (hF : Integrable F μ)
    (he : ∀ S, MeasurableSet S → W.value S = ∫ t in S, F t ∂μ) :
    W.density μ =ᵐ[μ] F := by
  have hAC : ∀ S, MeasurableSet S → μ S = 0 → W.value S = 0 := by
    intro S hS hz
    rw [he S hS,Measure.restrict_eq_zero.mpr hz,integral_zero_measure]
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (W.integrable_density μ) hF
  intro S hS hfin
  exact (W.integral_density μ hAC S hS).trans (he S hS)

lemma positiveDensity_eq_ae {F : Ω → Matrix ι ι ℂ} (hF : Integrable F μ)
    (he : ∀ S, MeasurableSet S → W.value S = ∫ t in S, F t ∂μ) :
    W.positiveDensity μ =ᵐ[μ] F := by
  have hAC : ∀ S, MeasurableSet S → μ S = 0 → W.value S = 0 := by
    intro S hS hz
    rw [he S hS,Measure.restrict_eq_zero.mpr hz,integral_zero_measure]
  exact (W.positiveDensity_ae μ hAC).trans (W.density_eq_ae μ hF he)

lemma positiveDensity_trace_eq_one (hW : (trace (W.value Set.univ)).re = 1) :
    (∫ t, (trace (W.positiveDensity W.traceMeasure t)).re ∂W.traceMeasure) = 1 := by
  rw [W.integral_positiveDensity_trace _ (W.value_zero_of_traceMeasure_zero)]
  exact hW

lemma positiveDensity_integrable
    (hAC : ∀ S, MeasurableSet S → μ S = 0 → W.value S = 0) :
    Integrable (W.positiveDensity μ) μ :=
  (W.integrable_density μ).congr (W.positiveDensity_ae μ hAC).symm

lemma positiveDensity_integral
    (hAC : ∀ S, MeasurableSet S → μ S = 0 → W.value S = 0)
    (S : Set Ω) (hS : MeasurableSet S) :
    (∫ t in S, W.positiveDensity μ t ∂μ) = W.value S := by
  rw [integral_congr_ae (ae_restrict_of_ae (W.positiveDensity_ae μ hAC))]
  exact W.integral_density μ hAC S hS

lemma positiveDensity_changeMeasure (ν : Measure Ω) [SigmaFinite ν]
    (hμν : μ ≪ ν)
    (hAC : ∀ S, MeasurableSet S → μ S = 0 → W.value S = 0) :
    W.positiveDensity ν =ᵐ[ν] fun t => (μ.rnDeriv ν t).toReal • W.positiveDensity μ t := by
  apply W.positiveDensity_eq_ae ν
    ((integrable_rnDeriv_smul_iff hμν).mpr (W.positiveDensity_integrable μ hAC))
  intro S hS
  rw [setIntegral_rnDeriv_smul hμν hS,W.positiveDensity_integral μ hAC S hS]

end PositiveMatrixMeasure

namespace BitDensity

universe v9378_0 v9378_1

variable {Ω : Type v9378_0} {ι : Type v9378_1} [inst9378_0 : MeasurableSpace Ω] [inst9378_1 : Fintype ι] [inst9378_2 : DecidableEq ι]
  {μ : Measure Ω}

lemma idealBitError_congr (τ υ : BitDensity μ ι) (σ θ : Ω → Matrix ι ι ℂ)
    (hτ : ∀ i j, τ.block i j =ᵐ[μ] υ.block i j) (hσ : σ =ᵐ[μ] θ) :
    τ.idealBitError σ = υ.idealBitError θ := by
  have hm (i j : Bool) : τ.mass i j = υ.mass i j := by
    apply integral_congr_ae
    filter_upwards [hτ i j] with t ht
    rw [ht]
  have hd (i : Bool) :
      (∫ t, traceNorm (τ.block i i t - (1/2 : ℝ) • σ t) ∂μ) =
        ∫ t, traceNorm (υ.block i i t - (1/2 : ℝ) • θ t) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hτ i i,hσ] with t ht hs
    rw [ht,hs]
  simp only [idealBitError,hm,hd]

end BitDensity

end

section

open Matrix MeasureTheory ProbabilityTheory Function unitInterval Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

open UnrestrictedQuantum

universe v9409_0 v9409_1 v9409_2 v9409_3 v9409_4 v9409_5 v9409_6 v9409_7 v9409_8 v9409_9

variable {O : Type v9409_0} {M : Type v9409_1} {ι : Type v9409_2} {η : Type v9409_3} [inst9409_0 : MeasurableSpace O] [inst9409_1 : MeasurableSpace M]
  [inst9409_2 : StandardBorelSpace O] [inst9409_3 : Nonempty O] [inst9409_4 : StandardBorelSpace M] [inst9409_5 : Nonempty M]
  [inst9409_6 : Fintype ι] [inst9409_7 : Fintype η] [inst9409_8 : DecidableEq ι] [inst9409_9 : DecidableEq η]
  [inst9409_10 : Nonempty ι] [inst9409_11 : Nonempty η]
  {d : Discussion O M} {A : ℕ → Type v9409_4} {B : ℕ → Type v9409_5}
  [inst9409_12 : ∀ n, AddCommGroup (A n)] [inst9409_13 : ∀ n, Module ℂ (A n)] [inst9409_14 : ∀ n, One (A n)] [inst9409_15 : ∀ n, LE (A n)]
  [inst9409_16 : ∀ n, AddCommGroup (B n)] [inst9409_17 : ∀ n, Module ℂ (B n)] [inst9409_18 : ∀ n, One (B n)] [inst9409_19 : ∀ n, LE (B n)]
  {TA : Type v9409_6} {TB : Type v9409_7} {CA : Type v9409_8} {CB : Type v9409_9}
  [inst9409_20 : AddCommGroup TA] [inst9409_21 : Module ℂ TA] [inst9409_22 : One TA] [inst9409_23 : LE TA]
  [inst9409_24 : AddCommGroup TB] [inst9409_25 : Module ℂ TB] [inst9409_26 : One TB] [inst9409_27 : LE TB]
  [inst9409_28 : AddCommGroup CA] [inst9409_29 : Module ℂ CA] [inst9409_30 : One CA] [inst9409_31 : LE CA]
  [inst9409_32 : AddCommGroup CB] [inst9409_33 : Module ℂ CB] [inst9409_34 : One CB] [inst9409_35 : LE CB]

namespace BitProtocol

variable (p : BitProtocol (ι := ι) (η := η) d A B TA TB CA CB)
  (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R)

include hR

lemma canonicalOutput_ac (i j : Bool) (S : Set (ℕ → M)) (hS : MeasurableSet S)
    (hnull : d.transcriptLaw S = 0) : (p.canonicalOutput R i j).value S = 0 := by
  obtain ⟨τ,X,Y,hX,hY,hτ,hi,he⟩ := p.canonical_density_representation R hR
  rw [he i j S hS,Measure.restrict_eq_zero.mpr hnull,integral_zero_measure]

def outputDensity (ν : Measure (ℕ → M)) [SigmaFinite ν]
    (hμν : d.transcriptLaw ≪ ν) : BitDensity ν (ι × η) :=
  PositiveMatrixMeasure.toBitDensity (p.canonicalOutput R) ν
    (fun i j S hS hz => p.canonicalOutput_ac R hR i j S hS (hμν hz))
    (p.canonicalOutput_normalized R hR)

lemma outputDensity_eq (ν : Measure (ℕ → M)) [SigmaFinite ν]
    (hμν : d.transcriptLaw ≪ ν)
    (τ : BitDensity d.transcriptLaw (ι × η))
    (hi : ∀ i j, Integrable (τ.block i j) d.transcriptLaw)
    (he : ∀ i j S, MeasurableSet S → (p.canonicalOutput R i j).value S =
        ∫ t in S, τ.block i j t ∂d.transcriptLaw) (i j : Bool) :
    (p.outputDensity R hR ν hμν).block i j =ᵐ[ν] (τ.changeMeasure hμν).block i j := by
  apply (p.canonicalOutput R i j).positiveDensity_eq_ae ν
    ((integrable_rnDeriv_smul_iff hμν).mpr (hi i j))
  intro S hS
  rw [setIntegral_rnDeriv_smul hμν hS,he i j S hS]

def secretBitError (sigma : PositiveMatrixMeasure (ℕ → M) (ι × η)) : ℝ :=
  (p.outputDensity R hR (d.transcriptLaw + sigma.traceMeasure)
    (Measure.AbsolutelyContinuous.rfl.add_right _)).idealBitError
      (sigma.positiveDensity (d.transcriptLaw + sigma.traceMeasure))

end BitProtocol

theorem BitProtocol.uniform_gap {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (p : BitProtocol (ι := Fin a) (η := Fin b) d A B TA TB CA CB)
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : InClass R)
    (sigma : PositiveMatrixMeasure (ℕ → M) (Fin a × Fin b))
    (hsigma : (trace (sigma.value Set.univ)).re = 1) :
    1/5 ≤ p.secretBitError R hR.1 sigma := by
  let ν := d.transcriptLaw + sigma.traceMeasure
  have hμν : d.transcriptLaw ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right _
  have hsν : sigma.traceMeasure ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hsAC (S : Set (ℕ → M)) (hS : MeasurableSet S) (hz : ν S = 0) :
      sigma.value S = 0 := sigma.value_zero_of_traceMeasure_zero S hS (hsν hz)
  obtain ⟨τ,X,Y,hX,hY,hτ,hi,he⟩ := p.canonical_density_representation R hR.1
  have hg := class_factor_gap_dominating_measure hμν R hR τ X Y hX hY hτ
    (sigma.positiveDensity ν) (sigma.measurable_positiveDensity ν)
    (sigma.positiveDensity_pos ν) (sigma.integrable_positiveDensity_trace ν hsAC)
    ((sigma.integral_positiveDensity_trace ν hsAC).trans hsigma)
  have heq := BitDensity.idealBitError_congr (p.outputDensity R hR.1 ν hμν)
    (τ.changeMeasure hμν) (sigma.positiveDensity ν) (sigma.positiveDensity ν)
    (p.outputDensity_eq R hR.1 ν hμν τ hi he) Filter.EventuallyEq.rfl
  change 1/5 ≤ (p.outputDensity R hR.1 ν hμν).idealBitError (sigma.positiveDensity ν)
  rw [heq]
  exact hg

end

section

open Matrix

open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator CFC

universe v9542_0 v9542_1

theorem traceNorm_positive_tracePreserving {ι : Type v9542_0} {κ : Type v9542_1}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (L : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (hpos : ∀ A, A.PosSemidef → (L A).PosSemidef)
    (htr : ∀ A, trace (L A) = trace A)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    traceNorm (L A) ≤ traceNorm A := by
  have hsa : IsSelfAdjoint A := hA
  have hp : A⁺.PosSemidef := (CFC.posPart_nonneg A).posSemidef
  have hn : A⁻.PosSemidef := (CFC.negPart_nonneg A).posSemidef
  have hd := CFC.posPart_sub_negPart A hsa
  have ha := CFC.posPart_add_negPart A hsa
  calc
    traceNorm (L A) = traceNorm (L A⁺ + -(L A⁻)) := by conv_lhs => rw [← hd,map_sub,sub_eq_add_neg]
    _ ≤ traceNorm (L A⁺) + traceNorm (-(L A⁻)) := traceNorm_add_le _ _
    _ = (trace A⁺).re + (trace A⁻).re := by
      rw [traceNorm_neg,traceNorm_posSemidef (hpos _ hp),
        traceNorm_posSemidef (hpos _ hn),htr,htr]
    _ = traceNorm A := by
      rw [← Complex.add_re,← Matrix.trace_add,ha]
      rfl

end

section

open Matrix MeasureTheory

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section

universe v9577_0 v9577_1 v9577_2

variable {ι : Type v9577_0} {α : Type v9577_1} {Λ : Type v9577_2} [inst9577_0 : Fintype ι] [inst9577_1 : DecidableEq ι]

lemma traceNorm_sum_le (s : Finset α) (A : α → Matrix ι ι ℂ) :
    traceNorm (∑ a ∈ s, A a) ≤ ∑ a ∈ s, traceNorm (A a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [traceNorm]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (traceNorm_add_le _ _).trans (add_le_add le_rfl ih)

variable [inst9588_0 : Fintype Λ] [inst9588_1 : DecidableEq Λ]

def firstBitBlocks (W : (Bool × Λ) → (Bool × Λ) → Matrix ι ι ℂ) :
    Bool → Bool → Matrix ι ι ℂ := fun i j => ∑ a, ∑ b, W (i,a) (j,b)

omit inst9588_1 in
theorem firstBit_traceNorm_contracts [DecidableEq Λ]
    (W V : (Bool × Λ) → (Bool × Λ) → Matrix ι ι ℂ) :
    (∑ i, ∑ j, traceNorm (firstBitBlocks W i j - firstBitBlocks V i j)) ≤
      ∑ a, ∑ b, traceNorm (W a b - V a b) := by
  have hb (i j : Bool) :
      traceNorm (firstBitBlocks W i j - firstBitBlocks V i j) ≤
        ∑ a, ∑ b, traceNorm (W (i,a) (j,b) - V (i,a) (j,b)) := by
    unfold firstBitBlocks
    simp_rw [← Finset.sum_sub_distrib]
    exact (traceNorm_sum_le Finset.univ _).trans
      (Finset.sum_le_sum fun a _ => traceNorm_sum_le Finset.univ _)
  calc
    _ ≤ ∑ i : Bool, ∑ j : Bool, ∑ a : Λ, ∑ b : Λ,
        traceNorm (W (i,a) (j,b) - V (i,a) (j,b)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]

def idealKeyBlocks (σ : Matrix ι ι ℂ) : (Bool × Λ) → (Bool × Λ) → Matrix ι ι ℂ :=
  fun a b => if a=b then (1/(2*(Fintype.card Λ : ℝ))) • σ else 0

omit inst9577_0 inst9577_1 in
lemma firstBit_idealKey [Fintype ι] [DecidableEq ι] [Nonempty Λ] (σ : Matrix ι ι ℂ) (i j : Bool) :
    firstBitBlocks (idealKeyBlocks (Λ := Λ) σ) i j =
      if i=j then (1/2 : ℝ) • σ else 0 := by
  classical
  by_cases hij : i=j
  · subst j
    simp only [firstBitBlocks,idealKeyBlocks,Prod.mk.injEq,true_and,ite_true]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
    have hn : (Fintype.card Λ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    congr 1
    field_simp
  · simp [firstBitBlocks,idealKeyBlocks,hij,Prod.mk.injEq]

end

section

universe v9649_0 v9649_1

variable {Ω : Type v9649_0} {ι : Type v9649_1} [inst9649_0 : MeasurableSpace Ω] [inst9649_1 : Fintype ι] [inst9649_2 : DecidableEq ι] {μ : Measure Ω}

def idealBitBlocks (sigma : Matrix ι ι ℂ) (i j : Bool) : Matrix ι ι ℂ :=
  if i = j then (1/2 : ℝ) • sigma else 0

def cqBitError (τ : Bool → Bool → Ω → Matrix ι ι ℂ)
    (sigma : Ω → Matrix ι ι ℂ) (μ : Measure Ω) : ℝ :=
  ∑ i, ∑ j, ∫ t, traceNorm (τ i j t - idealBitBlocks (sigma t) i j) ∂μ

lemma BitDensity.idealBitError_eq_cq (τ : BitDensity μ ι)
    (sigma : Ω → Matrix ι ι ℂ) : τ.idealBitError sigma = cqBitError τ.block sigma μ := by
  simp only [cqBitError,Fintype.sum_bool,idealBitBlocks,Bool.true_eq_false,
    Bool.false_eq_true,ite_false,ite_true,sub_zero]
  simp_rw [traceNorm_posSemidef (τ.positive true false _),
    traceNorm_posSemidef (τ.positive false true _)]
  unfold BitDensity.idealBitError BitDensity.mass
  ring

end

universe v9682_0 v9682_1 v9682_2 v9682_3

variable {Ω : Type v9682_0} {ι : Type v9682_1} {K : Type v9682_2} {Λ : Type v9682_3} [inst9682_0 : MeasurableSpace Ω] [inst9682_1 : Fintype ι] [inst9682_2 : DecidableEq ι]
  [inst9682_3 : Fintype K] [inst9682_4 : DecidableEq K] [inst9682_5 : Fintype Λ] [inst9682_6 : DecidableEq Λ] {μ : Measure Ω}

omit inst9682_1 inst9682_2 in
lemma idealFiniteBlocks_bit [Fintype ι] [DecidableEq ι] (sigma : Matrix ι ι ℂ) :
    idealFiniteBlocks (K := Bool) sigma = idealBitBlocks sigma := by
  funext a b
  simp [idealFiniteBlocks,idealBitBlocks]

omit inst9682_1 inst9682_2 in
lemma idealFiniteBlocks_bitSuffix [Fintype ι] [DecidableEq ι] (sigma : Matrix ι ι ℂ) :
    idealFiniteBlocks (K := Bool × Λ) sigma = idealKeyBlocks sigma := by
  funext a b
  simp [idealFiniteBlocks,idealKeyBlocks,Fintype.card_prod,Nat.cast_mul]

omit inst9682_6 in
theorem cqDistance_firstBit_le [DecidableEq Λ]
    (W V : (Bool × Λ) → (Bool × Λ) → Ω → Matrix ι ι ℂ)
    (hW : ∀ a b, Measurable (W a b)) (hV : ∀ a b, Measurable (V a b))
    (hi : ∀ a b, Integrable (fun t => traceNorm (W a b t - V a b t)) μ) :
    cqDistance (fun i j t => firstBitBlocks (fun a b => W a b t) i j)
      (fun i j t => firstBitBlocks (fun a b => V a b t) i j) μ ≤ cqDistance W V μ := by
  have hp (i j : Bool) (t : Ω) :
      traceNorm (firstBitBlocks (fun a b => W a b t) i j -
        firstBitBlocks (fun a b => V a b t) i j) ≤
        ∑ a : Λ, ∑ b : Λ, traceNorm (W (i,a) (j,b) t - V (i,a) (j,b) t) := by
    unfold firstBitBlocks
    simp_rw [← Finset.sum_sub_distrib]
    exact (traceNorm_sum_le Finset.univ _).trans
      (Finset.sum_le_sum fun a _ => traceNorm_sum_le Finset.univ _)
  have hb (i j : Bool) :
      (∫ t, traceNorm (firstBitBlocks (fun a b => W a b t) i j -
        firstBitBlocks (fun a b => V a b t) i j) ∂μ) ≤
        ∑ a : Λ, ∑ b : Λ, ∫ t, traceNorm (W (i,a) (j,b) t - V (i,a) (j,b) t) ∂μ := by
    have hir := integrable_finsetSum Finset.univ (fun a _ =>
      integrable_finsetSum Finset.univ (fun b _ => hi (i,a) (j,b)))
    have hml : Measurable (fun t => traceNorm
        (firstBitBlocks (fun a b => W a b t) i j - firstBitBlocks (fun a b => V a b t) i j)) := by
      apply measurable_traceNorm
      exact (Finset.measurable_sum Finset.univ (fun a _ =>
        Finset.measurable_sum Finset.univ (fun b _ => hW (i,a) (j,b)))).sub
        (Finset.measurable_sum Finset.univ (fun a _ =>
        Finset.measurable_sum Finset.univ (fun b _ => hV (i,a) (j,b))))
    have hil := hir.mono' hml.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (traceNorm_nonneg _)]
      exact hp i j t))
    calc
      _ ≤ ∫ t, ∑ a : Λ, ∑ b : Λ, traceNorm (W (i,a) (j,b) t - V (i,a) (j,b) t) ∂μ :=
        integral_mono hil hir (hp i j)
      _ = _ := by
        rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi (i,a) (j,b)))]
        apply Finset.sum_congr rfl
        intro a _
        rw [integral_finsetSum _ (fun b _ => hi (i,a) (j,b))]
  calc
    _ ≤ ∑ i : Bool, ∑ j : Bool, ∑ a : Λ, ∑ b : Λ,
        ∫ t, traceNorm (W (i,a) (j,b) t - V (i,a) (j,b) t) ∂μ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = _ := by
      simp only [cqDistance,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]

omit inst9682_2 in
lemma idealFinite_measurable [DecidableEq ι] (sigma : Ω → Matrix ι ι ℂ) (hs : Measurable sigma) (a b : K) :
    Measurable (fun t => idealFiniteBlocks (sigma t) a b) := by
  by_cases h : a = b <;> simp only [idealFiniteBlocks,h,ite_true,ite_false]
  · exact hs.const_smul (1/(Fintype.card K : ℝ))
  · exact measurable_const

omit inst9682_1 inst9682_2 in
lemma idealFinite_positive [Fintype ι] [DecidableEq ι] (sigma : Matrix ι ι ℂ) (hs : sigma.PosSemidef) (a b : K) :
    (idealFiniteBlocks sigma a b).PosSemidef := by
  by_cases h : a = b <;> simp only [idealFiniteBlocks,h,ite_true,ite_false]
  · exact hs.smul (by positivity : (0:ℝ) ≤ 1/(Fintype.card K : ℝ))
  · exact Matrix.PosSemidef.zero

omit inst9682_2 in
lemma idealFinite_trace_integrable [DecidableEq ι] (sigma : Ω → Matrix ι ι ℂ)
    (hi : Integrable (fun t => (trace (sigma t)).re) μ) (a b : K) :
    Integrable (fun t => (trace (idealFiniteBlocks (sigma t) a b)).re) μ := by
  by_cases h : a = b <;> simp only [idealFiniteBlocks,h,ite_true,ite_false]
  · simpa only [Matrix.trace_smul,Complex.smul_re,smul_eq_mul] using hi.const_mul (1/(Fintype.card K : ℝ))
  · simp

theorem cqFirstBit_ideal_le [Nonempty Λ]
    (W : (Bool × Λ) → (Bool × Λ) → Ω → Matrix ι ι ℂ)
    (hW : ∀ a b, Measurable (W a b)) (hWp : ∀ a b t, (W a b t).PosSemidef)
    (hWi : ∀ a b, Integrable (fun t => (trace (W a b t)).re) μ)
    (sigma : Ω → Matrix ι ι ℂ) (hs : Measurable sigma) (hsp : ∀ t, (sigma t).PosSemidef)
    (hsi : Integrable (fun t => (trace (sigma t)).re) μ) :
    cqBitError (fun i j t => firstBitBlocks (fun a b => W a b t) i j) sigma μ ≤
      cqDistance W (fun a b t => idealFiniteBlocks (sigma t) a b) μ := by
  have h := cqDistance_firstBit_le W (fun a b t => idealFiniteBlocks (sigma t) a b) hW
    (idealFinite_measurable sigma hs)
    (fun a b => traceNorm_sub_integrable (hW a b) (idealFinite_measurable sigma hs a b)
      (hWp a b) (fun t => idealFinite_positive (sigma t) (hsp t) a b)
      (hWi a b) (idealFinite_trace_integrable sigma hsi a b))
  simpa only [cqDistance,cqBitError,idealFiniteBlocks_bitSuffix,firstBit_idealKey,
    idealBitBlocks] using h

end

open Matrix MeasureTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe v9802_0 v9802_1 v9802_2

variable {Ω : Type v9802_0} {ι : Type v9802_1} {K : Type v9802_2} [inst9802_0 : MeasurableSpace Ω] [inst9802_1 : Fintype ι] [inst9802_2 : DecidableEq ι]
  [inst9802_3 : Fintype K] [inst9802_4 : DecidableEq K] {μ : Measure Ω}

omit inst9802_4 in
lemma cqDistance_nonneg [DecidableEq K] (W V : K → K → Ω → Matrix ι ι ℂ) : 0 ≤ cqDistance W V μ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => traceNorm_nonneg _

omit inst9802_4 in
lemma cqDistance_triangle [DecidableEq K] (W V Z : K → K → Ω → Matrix ι ι ℂ)
    (hW : ∀ a b, Measurable (W a b)) (hV : ∀ a b, Measurable (V a b))
    (hZ : ∀ a b, Measurable (Z a b))
    (hWp : ∀ a b t, (W a b t).PosSemidef) (hVp : ∀ a b t, (V a b t).PosSemidef)
    (hZp : ∀ a b t, (Z a b t).PosSemidef)
    (hWi : ∀ a b, Integrable (fun t => (trace (W a b t)).re) μ)
    (hVi : ∀ a b, Integrable (fun t => (trace (V a b t)).re) μ)
    (hZi : ∀ a b, Integrable (fun t => (trace (Z a b t)).re) μ) :
    cqDistance W Z μ ≤ cqDistance W V μ + cqDistance V Z μ := by
  have h (a b : K) : (∫ t, traceNorm (W a b t - Z a b t) ∂μ) ≤
      (∫ t, traceNorm (W a b t - V a b t) ∂μ) +
      ∫ t, traceNorm (V a b t - Z a b t) ∂μ := by
    have hwv := traceNorm_sub_integrable (hW a b) (hV a b) (hWp a b) (hVp a b) (hWi a b) (hVi a b)
    have hvz := traceNorm_sub_integrable (hV a b) (hZ a b) (hVp a b) (hZp a b) (hVi a b) (hZi a b)
    have hwz := traceNorm_sub_integrable (hW a b) (hZ a b) (hWp a b) (hZp a b) (hWi a b) (hZi a b)
    rw [← integral_add hwv hvz]
    apply integral_mono hwz (hwv.add hvz)
    intro t
    have he : W a b t - Z a b t = (W a b t - V a b t) + (V a b t - Z a b t) := by abel
    change traceNorm (W a b t - Z a b t) ≤
      traceNorm (W a b t - V a b t) + traceNorm (V a b t - Z a b t)
    rw [he]
    exact traceNorm_add_le _ _
  calc
    _ ≤ ∑ a, ∑ b, ((∫ t, traceNorm (W a b t - V a b t) ∂μ) +
        ∫ t, traceNorm (V a b t - Z a b t) ∂μ) :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h a b
    _ = _ := by simp only [cqDistance,Finset.sum_add_distrib]

lemma BitDensity.error_triangle (τ υ : BitDensity μ ι)
    (sigma : Ω → Matrix ι ι ℂ) (hs : Measurable sigma) (hsp : ∀ t, (sigma t).PosSemidef)
    (hsi : Integrable (fun t => (trace (sigma t)).re) μ) :
    τ.idealBitError sigma ≤ cqDistance τ.block υ.block μ + υ.idealBitError sigma := by
  have h := cqDistance_triangle τ.block υ.block (fun a b t => idealFiniteBlocks (sigma t) a b)
    τ.measurable υ.measurable (idealFinite_measurable sigma hs)
    τ.positive υ.positive (fun a b t => idealFinite_positive (sigma t) (hsp t) a b)
    τ.integrable υ.integrable (idealFinite_trace_integrable sigma hsi)
  simpa only [cqDistance,cqBitError,BitDensity.idealBitError_eq_cq,idealFiniteBlocks_bit] using h

theorem BitDensity.gap_of_traceNorm_limit (τ : ℕ → BitDensity μ ι) (υ : BitDensity μ ι)
    (sigma : Ω → Matrix ι ι ℂ) (hs : Measurable sigma) (hsp : ∀ t, (sigma t).PosSemidef)
    (hsi : Integrable (fun t => (trace (sigma t)).re) μ)
    (hgap : ∀ n, 1/5 ≤ (τ n).idealBitError sigma)
    (hlim : Tendsto (fun n => cqDistance (τ n).block υ.block μ) atTop (nhds 0)) :
    1/5 ≤ υ.idealBitError sigma := by
  have hle (n : ℕ) := (hgap n).trans ((τ n).error_triangle υ sigma hs hsp hsi)
  have ht : Tendsto (fun n => cqDistance (τ n).block υ.block μ + υ.idealBitError sigma)
      atTop (nhds (υ.idealBitError sigma)) := by simpa using hlim.add_const (υ.idealBitError sigma)
  exact ge_of_tendsto ht (Filter.Eventually.of_forall hle)

end ZeroKey

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace ZeroKey

open UnrestrictedQuantum

universe v9877_0 v9877_1 v9877_2 v9877_3 v9877_4 v9877_5 v9877_6 v9877_7

variable {O : Type v9877_0} {M : Type v9877_1} [inst9877_0 : MeasurableSpace O] [inst9877_1 : MeasurableSpace M]
  [inst9877_2 : StandardBorelSpace O] [inst9877_3 : Nonempty O] [inst9877_4 : StandardBorelSpace M] [inst9877_5 : Nonempty M]
  {d : Discussion O M} {A : ℕ → Type v9877_2} {B : ℕ → Type v9877_3}
  [inst9877_6 : ∀ n, AddCommGroup (A n)] [inst9877_7 : ∀ n, Module ℂ (A n)] [inst9877_8 : ∀ n, One (A n)] [inst9877_9 : ∀ n, LE (A n)]
  [inst9877_10 : ∀ n, AddCommGroup (B n)] [inst9877_11 : ∀ n, Module ℂ (B n)] [inst9877_12 : ∀ n, One (B n)] [inst9877_13 : ∀ n, LE (B n)]
  {TA : Type v9877_4} {TB : Type v9877_5} {CA : Type v9877_6} {CB : Type v9877_7}
  [inst9877_14 : AddCommGroup TA] [inst9877_15 : Module ℂ TA] [inst9877_16 : One TA] [inst9877_17 : LE TA]
  [inst9877_18 : AddCommGroup TB] [inst9877_19 : Module ℂ TB] [inst9877_20 : One TB] [inst9877_21 : LE TB]
  [inst9877_22 : AddCommGroup CA] [inst9877_23 : Module ℂ CA] [inst9877_24 : One CA] [inst9877_25 : LE CA]
  [inst9877_26 : AddCommGroup CB] [inst9877_27 : Module ℂ CB] [inst9877_28 : One CB] [inst9877_29 : LE CB]
  {a b : ℕ} [inst9877_30 : Nonempty (Fin a)] [inst9877_31 : Nonempty (Fin b)]

theorem BitProtocol.uniform_gap_dominated
    (p : BitProtocol (ι := Fin a) (η := Fin b) d A B TA TB CA CB)
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : InClass R)
    (ν : Measure (ℕ → M)) [SigmaFinite ν] (hμν : d.transcriptLaw ≪ ν)
    (sigma : (ℕ → M) → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hs : Measurable sigma) (hsp : ∀ t, (sigma t).PosSemidef)
    (hsi : Integrable (fun t => (trace (sigma t)).re) ν)
    (hsn : (∫ t, (trace (sigma t)).re ∂ν) = 1) :
    1/5 ≤ (p.outputDensity R hR.1 ν hμν).idealBitError sigma := by
  obtain ⟨τ,X,Y,hX,hY,hτ,hi,he⟩ := p.canonical_density_representation R hR.1
  have hg := class_factor_gap_dominating_measure hμν R hR τ X Y hX hY hτ
    sigma hs hsp hsi hsn
  rw [BitDensity.idealBitError_congr (p.outputDensity R hR.1 ν hμν)
    (τ.changeMeasure hμν) sigma sigma (p.outputDensity_eq R hR.1 ν hμν τ hi he)
    Filter.EventuallyEq.rfl]
  exact hg

end ZeroKey

end

end OAI
