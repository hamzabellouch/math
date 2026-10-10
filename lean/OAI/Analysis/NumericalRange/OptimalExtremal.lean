import OAI.Analysis.NumericalRange.DualSeparation

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_188 u_189 u_190

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
open Set Filter Metric Topology
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder Pointwise
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section
variable {n : Type u_188} [Fintype n] [DecidableEq n]

lemma pos_trace_zero_mul {B C : Matrix n n ℂ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (h0 : (Matrix.trace (B*C)).re = 0) : B*C = 0 := by
  obtain ⟨R,hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB
  obtain ⟨S,hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC
  change B = Rᴴ * R at hR
  change C = Sᴴ * S at hS
  have hp := (Matrix.nonneg_iff_posSemidef.mp hC).mul_mul_conjTranspose_same R
  have ht : Matrix.trace (R*C*Rᴴ) = 0 := by
    apply Complex.ext
    · rw [Matrix.trace_mul_cycle, ← hR]
      exact h0
    · exact (Complex.nonneg_iff.mp hp.trace_nonneg).2.symm
  have hz : R*C*Rᴴ = 0 := hp.trace_eq_zero_iff.mp ht
  have hrs : R*Sᴴ = 0 := by
    apply Matrix.self_mul_conjTranspose_eq_zero.mp
    simpa only [hS, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using hz
  rw [hR,hS]
  calc
    Rᴴ * R * (Sᴴ * S) = Rᴴ * (R*Sᴴ) * S := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hrs,Matrix.mul_zero,Matrix.zero_mul]

lemma pos_trace_zero_mul_reverse {B C : Matrix n n ℂ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (h0 : (Matrix.trace (B*C)).re = 0) : C*B = 0 := by
  apply pos_trace_zero_mul hC hB
  simpa only [Matrix.trace_mul_comm C B] using h0

lemma upper_slack_support {H X : Matrix n n ℂ} {τ : ℝ}
    (hX : 0 ≤ X) (hH : H ≤ τ • 1)
    (h0 : (Matrix.trace (X*(τ • 1-H))).re = 0) : H*X = τ • X := by
  have hz := pos_trace_zero_mul_reverse hX (sub_nonneg.mpr hH) h0
  have hh : τ • X = H*X := by
    simpa only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] using hz
  exact hh.symm

lemma lower_slack_support {H Y : Matrix n n ℂ}
    (hY : 0 ≤ Y) (hH : 1 ≤ H)
    (h0 : (Matrix.trace (Y*(H-1))).re = 0) : H*Y = Y := by
  have hz := pos_trace_zero_mul_reverse hY (sub_nonneg.mpr hH) h0
  simpa only [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] using hz

lemma endpoint_support_factor {H B X : Matrix n n ℂ} {τ : ℝ}
    (hX : X*Xᴴ = B) (hB : H*B = τ • B) : H*X = τ • X := by
  have hz : (H-τ • 1)*B = 0 := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,hB,sub_self]
  rw [← hX] at hz
  have hh := (Matrix.mul_self_mul_conjTranspose_eq_zero X (H-τ • 1)).mp hz
  simpa only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] using hh

lemma sqrt_endpoint_support {H X : Matrix n n ℂ} {a : ℝ}
    (hH : 0 ≤ H) (ha : 0 < a) (hX : H*X = (a*a) • X) :
    CFC.sqrt H * X = a • X := by
  have hu : IsUnit (a • (1 : Matrix n n ℂ) + CFC.sqrt H) :=
    ((Matrix.PosDef.one.smul ha).add_posSemidef
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H))).isUnit
  apply sub_eq_zero.mp
  apply hu.mul_left_cancel
  rw [Matrix.mul_zero]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, ← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self H hH, hX]
  module

lemma separated_endpoint_orthogonal
    {n : Type u_188} [Fintype n] [DecidableEq n] {S X Y : Matrix n n ℂ} {a : ℝ}
    (hS : S.IsHermitian) (hX : S*X = a • X) (hY : S*Y = Y) (ha : a ≠ 1) :
    Xᴴ*Y = 0 := by
  have hx : Xᴴ*S = a • Xᴴ := by
    have hh := congrArg Matrix.conjTranspose hX
    simpa only [Matrix.conjTranspose_mul, hS.eq, Matrix.conjTranspose_smul,
      star_trivial] using hh
  have he : a • (Xᴴ*Y) = Xᴴ*Y := by
    rw [← Matrix.smul_mul, ← hx, Matrix.mul_assoc, hY]
  have hz : (a-1) • (Xᴴ*Y) = 0 := by rw [sub_smul,one_smul,he,sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

end

section
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : Type u_189} [Fintype n] [DecidableEq n] [Nonempty n]

theorem exists_optimal_metric_and_dual {T : Matrix n n ℂ}
    (hT : spectralRadius ℂ T < 1) :
    ∃ (τ : ℝ) (H X Y Z : HermitianMatrix n),
      MetricFeasible T τ H ∧ (H : Matrix n n ℂ).PosDef ∧
      (∀ s J, MetricFeasible T s J → τ ≤ s) ∧
      0 ≤ (X : Matrix n n ℂ) ∧ 0 ≤ (Y : Matrix n n ℂ) ∧ 0 ≤ (Z : Matrix n n ℂ) ∧
      X-Y = Z-metricPush T Z ∧ hermTrace X 1 = 1 ∧ hermTrace Y 1 = τ ∧
      (H : Matrix n n ℂ)*(X : Matrix n n ℂ) = τ • (X : Matrix n n ℂ) ∧
      (H : Matrix n n ℂ)*(Y : Matrix n n ℂ) = (Y : Matrix n n ℂ) := by
  obtain ⟨τ,H,hf,hp,hm⟩ := exists_optimal_metric hT
  let HH : HermitianMatrix n := ⟨H,hp.isHermitian⟩
  obtain ⟨X,Y,Z,hX,hY,hZ,hb,htX,htY,hcY,hcX,_⟩ :=
    metric_dual_certificate (H := HH) hT hf (fun s J hJ => hm s J hJ)
  refine ⟨τ,HH,X,Y,Z,hf,hp,?_,hX,hY,hZ,hb,htX,htY,?_,?_⟩
  · exact hm
  · apply upper_slack_support hX
    · simpa only [Algebra.algebraMap_eq_smul_one] using hf.2.1
    · exact hcX
  · exact lower_slack_support hY hf.1 hcY

theorem endpoint_dual_factors
    {n : Type u_189} [Fintype n] [DecidableEq n] [Nonempty n]
    {H X₀ Y₀ : Matrix n n ℂ} {τ : ℝ}
    (hH : 0 ≤ H) (hX : 0 ≤ X₀) (hY : 0 ≤ Y₀) (hτ : 1 < τ)
    (hSX : H*X₀ = τ • X₀) (hSY : H*Y₀ = Y₀)
    (htrX : (Matrix.trace X₀).re = 1) (htrY : (Matrix.trace Y₀).re = τ) :
    ∃ X Y : Matrix n n ℂ,
      X*Xᴴ = X₀ ∧ Y*Yᴴ = τ⁻¹ • Y₀ ∧
      (Matrix.trace (X*Xᴴ)).re = 1 ∧ (Matrix.trace (Y*Yᴴ)).re = 1 ∧
      CFC.sqrt H * X = Real.sqrt τ • X ∧ CFC.sqrt H * Y = Y ∧ Xᴴ*Y = 0 := by
  let a := Real.sqrt τ
  have ha : 0 < a := Real.sqrt_pos.mpr (lt_trans zero_lt_one hτ)
  have ha2 : a*a = τ := Real.mul_self_sqrt (le_trans zero_le_one hτ.le)
  let X := CFC.sqrt X₀
  let Y := a⁻¹ • CFC.sqrt Y₀
  have hXh : Xᴴ = X := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X₀)).isHermitian
  have hYh : (CFC.sqrt Y₀)ᴴ = CFC.sqrt Y₀ :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Y₀)).isHermitian
  have hfX : X*Xᴴ = X₀ := by rw [hXh]; exact CFC.sqrt_mul_sqrt_self X₀ hX
  have hfY : Y*Yᴴ = τ⁻¹ • Y₀ := by
    change (a⁻¹ • CFC.sqrt Y₀)*(a⁻¹ • CFC.sqrt Y₀)ᴴ = _
    rw [Matrix.conjTranspose_smul,star_trivial,hYh,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,CFC.sqrt_mul_sqrt_self Y₀ hY,← mul_inv_rev,ha2]
  have hsX : H*X = τ • X := endpoint_support_factor hfX hSX
  have hsY : H*Y = Y := by
    have hs0 : H*CFC.sqrt Y₀ = CFC.sqrt Y₀ := by
      have hf : CFC.sqrt Y₀*(CFC.sqrt Y₀)ᴴ = Y₀ := by
        rw [hYh]; exact CFC.sqrt_mul_sqrt_self Y₀ hY
      simpa only [one_smul] using endpoint_support_factor (τ := 1) hf (by simpa using hSY)
    rw [Matrix.mul_smul,hs0]
  have hsX' : CFC.sqrt H*X = a • X :=
    sqrt_endpoint_support hH ha (by simpa only [ha2] using hsX)
  have hsY' : CFC.sqrt H*Y = Y := by
    simpa using sqrt_endpoint_support hH zero_lt_one (by simpa using hsY)
  refine ⟨X,Y,hfX,hfY,by rw [hfX]; exact htrX,?_,hsX',hsY',?_⟩
  · rw [hfY,Matrix.trace_smul]
    simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,htrY,inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one hτ))]
  · apply separated_endpoint_orthogonal
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian hsX' hsY'
    intro hh
    rw [hh,mul_one] at ha2
    linarith

lemma metric_sqrt_isUnit
    {n : Type u_189} [Fintype n] [DecidableEq n] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.PosDef) : IsUnit (CFC.sqrt H) :=
  (CFC.isUnit_sqrt_iff H hH.posSemidef.nonneg).mpr hH.isUnit

theorem metric_similarity_contraction {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H) (hp : H.PosDef) :
    ‖CFC.sqrt H * T * (CFC.sqrt H)⁻¹‖ ≤ 1 := by
  let S := CFC.sqrt H
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian
  have hs2 : S*S = H := CFC.sqrt_mul_sqrt_self H hp.posSemidef.nonneg
  have hu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp (metric_sqrt_isUnit hp)
  have hi : S⁻¹*S = 1 := Matrix.nonsing_inv_mul S hu
  have hi' : S*S⁻¹ = 1 := Matrix.mul_nonsing_inv S hu
  have hp0 : (H-Tᴴ*H*T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hf.2.2)
  have hpc := hp0.conjTranspose_mul_mul_same S⁻¹
  have hid : S⁻¹ᴴ*(H-Tᴴ*H*T)*S⁻¹ = 1-(S*T*S⁻¹)ᴴ*(S*T*S⁻¹) := by
    rw [hS.inv.eq,Matrix.mul_sub,Matrix.sub_mul]
    have h1 : S⁻¹*H*S⁻¹ = 1 := by
      rw [← hs2,← Matrix.mul_assoc,hi,Matrix.one_mul,hi']
    rw [h1,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hS.inv.eq,hS.eq]
    congr 1
    rw [← hs2]
    noncomm_ring
  rw [hid] at hpc
  have hle : (S*T*S⁻¹)ᴴ*(S*T*S⁻¹) ≤ 1 := hpc
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (Matrix.posSemidef_conjTranspose_mul_self (S*T*S⁻¹)).nonneg).mpr hle
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg (S*T*S⁻¹)]

lemma endpoint_congruence
    {n : Type u_189} [Fintype n] [DecidableEq n] [Nonempty n] {S B : Matrix n n ℂ} {a : ℝ}
    (hS : S.IsHermitian) (hB : B.IsHermitian) (hs : S*B = a • B) :
    S*B*S = (a*a) • B := by
  have hr : B*S = a • B := by
    simpa only [Matrix.conjTranspose_mul,hS.eq,hB.eq,Matrix.conjTranspose_smul,
      star_trivial] using congrArg Matrix.conjTranspose hs
  rw [hs,Matrix.smul_mul,hr,smul_smul]

lemma normalized_dual_balance {S T X₀ Y₀ Z₀ : Matrix n n ℂ} {a : ℝ}
    (hS : S.IsHermitian) (hSu : IsUnit S) (ha : a ≠ 0)
    (hX : X₀.IsHermitian) (hY : Y₀.IsHermitian)
    (hsX : S*X₀ = a • X₀) (hsY : S*Y₀ = Y₀)
    (hb : X₀-Y₀ = Z₀-T*Z₀*Tᴴ) :
    X₀-(a*a)⁻¹ • Y₀ =
      (a*a)⁻¹ • (S*Z₀*S) -
      (S*T*S⁻¹)*((a*a)⁻¹ • (S*Z₀*S))*(S*T*S⁻¹)ᴴ := by
  have hi : S⁻¹*S = 1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hSu)
  have hi' : S*S⁻¹ = 1 := Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hSu)
  have he : (S*T*S⁻¹)*(S*Z₀*S)*(S*T*S⁻¹)ᴴ = S*(T*Z₀*Tᴴ)*S := by
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hS.inv.eq,hS.eq]
    calc
      _ = S*T*(S⁻¹*S)*Z₀*(S*S⁻¹)*Tᴴ*S := by noncomm_ring
      _ = _ := by rw [hi,hi']; simp only [Matrix.mul_one]; noncomm_ring
  rw [Matrix.mul_smul,Matrix.smul_mul,he,← smul_sub,← Matrix.sub_mul,← Matrix.mul_sub,← hb]
  rw [Matrix.mul_sub,Matrix.sub_mul,endpoint_congruence hS hX hsX,
    endpoint_congruence (a := 1) hS hY (by simpa using hsY)]
  simp only [smul_sub,smul_smul,inv_mul_cancel₀ (mul_ne_zero ha ha),one_smul,one_mul]

end

open Filter Topology Set Metric
open scoped Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_190} [Fintype n] [DecidableEq n] [Nonempty n]

lemma spectrum_matrix_similarity
    {n : Type u_190} [Fintype n] [DecidableEq n] [Nonempty n]
    {S : Matrix n n ℂ} (hS : IsUnit S) (T : Matrix n n ℂ) :
    spectrum ℂ (S*T*S⁻¹) = spectrum ℂ T := by
  rw [← hS.unit_spec, ← Matrix.coe_units_inv]
  exact spectrum.units_conjugate

lemma vectorize_norm_one_of_trace
    {n : Type u_190} [Fintype n] [DecidableEq n] [Nonempty n] {X : Matrix n n ℂ}
    (hX : (Matrix.trace (X*Xᴴ)).re = 1) : ‖vectorize X‖ = 1 := by
  have hs : ‖vectorize X‖^2 = 1 := by
    calc
      _ = (inner ℂ (vectorize X) (vectorize X)).re := norm_sq_eq_re_inner (𝕜 := ℂ) (vectorize X)
      _ = (Matrix.trace (Xᴴ*X)).re := congrArg Complex.re (hs_inner X X)
      _ = 1 := by rw [Matrix.trace_mul_comm]; exact hX
  nlinarith [norm_nonneg (vectorize X)]

theorem exists_optimal_analytic_extremal {T : Matrix n n ℂ}
    (hT : spectralRadius ℂ T < 1) :
    ∃ (τ : ℝ) (H : Matrix n n ℂ),
      MetricFeasible T τ H ∧ H.PosDef ∧
      (∀ s J, MetricFeasible T s J → τ ≤ s) ∧
      (1 < τ → ∃ (X Y : Matrix n n ℂ) (F : ℂ → Matrix n n ℂ),
        ‖vectorize X‖ = 1 ∧ ‖vectorize Y‖ = 1 ∧
        CFC.sqrt H*X = Real.sqrt τ • X ∧ CFC.sqrt H*Y = Y ∧ Xᴴ*Y = 0 ∧
        AnalyticOnNhd ℂ F (closedBall 0 1) ∧
        (∀ z ∈ closedBall 0 1, ‖F z‖ ≤ 1) ∧
        Matrix.toEuclideanCLM (n := n × n) (𝕜 := ℂ)
          (completeAnalyticEval (CFC.sqrt H*T*(CFC.sqrt H)⁻¹) F)
          (vectorize X) = vectorize Y) := by
  obtain ⟨τ,H,X₀,Y₀,Z₀,hf,hp,hm,hX₀,hY₀,hZ₀,hb,htX,htY,hHX,hHY⟩ :=
    exists_optimal_metric_and_dual hT
  refine ⟨τ,H,hf,hp,hm,?_⟩
  intro hτ
  have hτ0 : 0 ≤ τ := le_trans zero_le_one hτ.le
  have ha : 0 < Real.sqrt τ := Real.sqrt_pos.mpr (lt_trans zero_lt_one hτ)
  have ha2 : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ0
  have htX' : (Matrix.trace (X₀ : Matrix n n ℂ)).re = 1 := by
    simpa only [hermTrace, selfAdjoint.val_one, Matrix.mul_one] using htX
  have htY' : (Matrix.trace (Y₀ : Matrix n n ℂ)).re = τ := by
    simpa only [hermTrace, selfAdjoint.val_one, Matrix.mul_one] using htY
  obtain ⟨X,Y,hXX,hYY,htrX,htrY,hSX,hSY,hXY⟩ :=
    endpoint_dual_factors hp.posSemidef.nonneg hX₀ hY₀ hτ hHX hHY htX' htY'
  let S := CFC.sqrt (H : Matrix n n ℂ)
  have hS : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (H : Matrix n n ℂ))).isHermitian
  have hSu : IsUnit S := metric_sqrt_isUnit hp
  have hSX₀ : S*(X₀ : Matrix n n ℂ) = Real.sqrt τ • (X₀ : Matrix n n ℂ) :=
    sqrt_endpoint_support hp.posSemidef.nonneg ha (by rwa [ha2])
  have hSY₀ : S*(Y₀ : Matrix n n ℂ) = (Y₀ : Matrix n n ℂ) := by
    simpa only [one_mul, one_smul] using
      sqrt_endpoint_support (X := (Y₀ : Matrix n n ℂ)) hp.posSemidef.nonneg zero_lt_one
        (by simpa only [one_mul, one_smul] using hHY)
  have hb' : (X₀ : Matrix n n ℂ)-(Y₀ : Matrix n n ℂ) =
      (Z₀ : Matrix n n ℂ)-T*(Z₀ : Matrix n n ℂ)*Tᴴ := by
    exact congrArg (fun M : HermitianMatrix n => (M : Matrix n n ℂ)) hb
  let Z : Matrix n n ℂ := τ⁻¹ • (S*(Z₀ : Matrix n n ℂ)*S)
  have hZ : 0 ≤ Z := by
    have hz := (Matrix.nonneg_iff_posSemidef.mp hZ₀).conjTranspose_mul_mul_same S
    rw [hS.eq] at hz
    exact (hz.smul (inv_nonneg.mpr hτ0)).nonneg
  let L := CFC.sqrt Z
  have hLL : L*Lᴴ = Z := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Z)).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self Z hZ
  have hbal : X*Xᴴ-Y*Yᴴ = L*Lᴴ-(S*T*S⁻¹)*(L*Lᴴ)*(S*T*S⁻¹)ᴴ := by
    rw [hLL, hXX, hYY]
    simpa only [ha2] using normalized_dual_balance hS hSu ha.ne' X₀.property Y₀.property hSX₀ hSY₀ hb'
  have hD : spectralRadius ℂ (S*T*S⁻¹) < 1 := by
    simpa only [spectralRadius_eq_of_unital, spectrum_matrix_similarity hSu] using hT
  obtain ⟨F,hFa,hFn,hFe⟩ := exists_analytic_extremal_from_balance hD hbal
  exact ⟨X,Y,F,vectorize_norm_one_of_trace htrX,vectorize_norm_one_of_trace htrY,
    hSX,hSY,hXY,hFa,hFn,hFe⟩


end CompleteCrouzeix

end

end OAI
