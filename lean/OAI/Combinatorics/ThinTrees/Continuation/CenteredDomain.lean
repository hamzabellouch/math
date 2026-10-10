import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.Hierarchy

namespace OAI

/-! Centered domain. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma mul_constant_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD0 : D *ᵥ ones n=0) :
    D*constantProjection n=0 := by
  simp only [constantProjection,mul_smul_comm,mul_vecMulVec,hD0,zero_vecMulVec,smul_zero]

lemma constant_mul_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : constantProjection n*D=0 := by
  have hh := congrArg transpose (mul_constant_of_ones hD0)
  simpa only [transpose_mul,constantProjection_symmetric,
    (isHermitian_iff_isSymm.mp hD).eq,transpose_zero] using hh

lemma mul_centering_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD0 : D *ᵥ ones n=0) :
    D*centering n=D := by
  rw [centering,mul_sub,mul_one,mul_constant_of_ones hD0,sub_zero]

lemma centering_mul_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : centering n*D=D := by
  rw [centering,sub_mul,one_mul,constant_mul_of_ones hD hD0,sub_zero]

lemma centered_eq {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : centered D=D := by
  rw [centered,centering_mul_of_ones hD hD0,mul_centering_of_ones hD0]

lemma centeredPositive_psd (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : CenteredPositive D) : D.PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg hD.1
  intro x
  change 0 ≤ qform D x
  rw [←centered_eq hD.1 hD.2.1,qform_centered]
  by_cases hx : centering n *ᵥ x=0
  · simp [hx,qform]
  · exact (hD.2.2 _ (centering_mulVec_sum hn x) hx).le

lemma regularize_pd (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : CenteredPositive D) : (regularize D).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos (hD.1.add constantProjection_psd.isHermitian)
  intro x hx
  change 0 < qform (regularize D) x
  rw [regularize,qform_add]
  by_cases hp : centering n *ᵥ x=0
  · have hs : (∑i, x i) ≠ 0 := by
      intro hs
      rw [centering_mulVec_of_sum_zero hs] at hp
      exact hx hp
    have hq : 0 < qform (constantProjection n) x := by
      rw [qform_constantProjection]
      exact div_pos (sq_pos_of_ne_zero hs) (Nat.cast_pos.mpr hn)
    exact add_pos_of_nonneg_of_pos (qform_nonneg (centeredPositive_psd hn hD) _) hq
  · have hq : 0 < qform D x := by
      rw [←centered_eq hD.1 hD.2.1,qform_centered]
      exact hD.2.2 _ (centering_mulVec_sum hn x) hp
    exact add_pos_of_pos_of_nonneg hq (qform_nonneg constantProjection_psd _)

lemma centeredPositive_add_psd {D F : Matrix (Fin n) (Fin n) ℝ}
    (hD : CenteredPositive D) (hF : F.PosSemidef) (hF0 : F *ᵥ ones n=0) :
    CenteredPositive (D+F) := by
  refine ⟨hD.1.add hF.isHermitian,?_,?_⟩
  · simp only [add_mulVec,hD.2.1,hF0,add_zero]
  · intro x hx hx0
    rw [qform_add]
    exact add_pos_of_pos_of_nonneg (hD.2.2 x hx hx0) (qform_nonneg hF _)

lemma centered_rankOne {b : Fin n → ℝ} (hb : (∑i, b i)=0) :
    centered (vecMulVec b b)=vecMulVec b b := by
  apply centered_eq
  · simpa only [star_trivial] using (posSemidef_vecMulVec_self_star b).isHermitian
  · rw [vecMulVec_mulVec,dotProduct_comm,ones_dot,hb,IsCentralScalar.op_smul_eq_smul,zero_smul]

lemma centered_regularize {D : Matrix (Fin n) (Fin n) ℝ} (hn : 0 < n)
    (hD : D.IsHermitian) (hD0 : D *ᵥ ones n=0) : centered (regularize D)=D := by
  have hc0 : centering n*constantProjection n=0 := by
    exact mul_constant_of_ones (centering_ones hn)
  simp only [centered,regularize,mul_add,hc0,add_zero,
    centering_mul_of_ones hD hD0,mul_centering_of_ones hD0]

lemma centered_resistance_nonneg (G : MultiGraph n m) (hn : 0 < n)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : CenteredPositive D) (e : Fin m) :
    0 ≤ resistance G D e := qform_nonneg (regularize_pd hn hD).inv.posSemidef _

lemma centered_inverse_antitone (hn : 0 < n) {D X : Matrix (Fin n) (Fin n) ℝ}
    (hD : CenteredPositive D) (hX : CenteredPositive X) (hDX : D ≤ X) (b : Fin n → ℝ) :
    qform (inverseOnZeroSum X) b ≤ qform (inverseOnZeroSum D) b := by
  apply StrongThinTree.resistance_antitone (regularize_pd hn hX) (regularize_pd hn hD)
  have hh : regularize X-regularize D=X-D := by unfold regularize; abel
  rw [hh]
  exact Matrix.le_iff.mp hDX

lemma centered_resistance_order (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : CenteredPositive X) {b : Fin n → ℝ} (hb : (∑i, b i)=0)
    {a : ℝ} (ha : 0 < a) :
    (X-a • vecMulVec b b).PosSemidef ↔ a*qform (inverseOnZeroSum X) b ≤ 1 := by
  have heq : a • (a⁻¹ • regularize X-vecMulVec b b)=regularize X-a • vecMulVec b b := by
    rw [smul_sub,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  have hproblem := StrongThinTree.resistance_order (regularize_pd hn hX) b (inv_pos.mpr ha)
  constructor
  · intro h
    have h' : (regularize X-a • vecMulVec b b).PosSemidef := by
      convert h.add constantProjection_psd using 1
      unfold regularize
      abel
    have hinv := h'.smul (inv_nonneg.mpr ha.le)
    have hi : a⁻¹ • (regularize X-a • vecMulVec b b)=a⁻¹ • regularize X-vecMulVec b b := by
      rw [smul_sub,smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
    rw [hi] at hinv
    have hh := hproblem.mpr hinv
    change qform (inverseOnZeroSum X) b ≤ a⁻¹ at hh
    have hm := mul_le_mul_of_nonneg_left hh ha.le
    rwa [mul_inv_cancel₀ ha.ne'] at hm
  · intro h
    have hh : qform (inverseOnZeroSum X) b ≤ a⁻¹ := by
      rw [←one_div,le_div_iff₀ ha]
      simpa only [mul_comm] using h
    have h' := (hproblem.mp hh).smul ha.le
    rw [heq] at h'
    have hc := centered_psd h'
    have he : centered (regularize X-a • vecMulVec b b)=X-a • vecMulVec b b := by
      simp only [centered,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
      rw [show centering n*regularize X*centering n=X from centered_regularize hn hX.1 hX.2.1]
      rw [show centering n*vecMulVec b b*centering n=vecMulVec b b from centered_rankOne hb]
    rwa [he] at hc

def metricDomain (G : MultiGraph n m) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.IsHermitian ∧ X *ᵥ ones n=0 ∧ G.laplacian univ ≤ X ∧
     ∀Z, CenteredTest Z → (X*Z).trace ≤ 3*(G.laplacian univ*Z).trace}

lemma laplacian_mem_domain (G : MultiGraph n m) : G.laplacian univ ∈ metricDomain G := by
  refine ⟨(G.laplacian_psd univ).isHermitian,laplacian_ones G,le_rfl,?_⟩
  intro Z hZ
  have hh := trace_pairing_nonneg (G.laplacian_psd univ) hZ.1.1
  linarith only [hh]

lemma domain_psd (G : MultiGraph n m) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ metricDomain G) : X.PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp ((Matrix.nonneg_iff_posSemidef.mpr (G.laplacian_psd univ)).trans hX.2.2.1)

lemma domain_positive (G : MultiGraph n m) (hn : 0 < n) (hG : G.Connected univ)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ metricDomain G) : CenteredPositive X := by
  refine ⟨hX.1,hX.2.1,?_⟩
  intro x hx hx0
  exact (laplacian_zeroSum_pos G hn hG x hx hx0).trans_le (qform_mono hX.2.2.1 x)

lemma domain_closed (G : MultiGraph n m) : IsClosed (metricDomain G) := by
  have hc : Continuous (fun X : Matrix (Fin n) (Fin n) ℝ => X *ᵥ ones n) := by
    fun_prop
  have ht : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | ∀Z, CenteredTest Z →
      (X*Z).trace ≤ (3:ℝ)*(G.laplacian univ*Z).trace} := by
    simp only [show {X : Matrix (Fin n) (Fin n) ℝ | ∀Z, CenteredTest Z →
      (X*Z).trace ≤ (3:ℝ)*(G.laplacian univ*Z).trace} =
      ⋂ Z : {Z : Matrix (Fin n) (Fin n) ℝ // CenteredTest Z},
        {X | (X*Z.val).trace ≤ 3*(G.laplacian univ*Z.val).trace} by ext; simp]
    exact isClosed_iInter fun Z => isClosed_le (trace_pairing_continuous _) continuous_const
  exact (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
    ((isClosed_eq hc continuous_const).inter ((isClosed_matrixAbove _).inter ht))

lemma domain_convex (G : MultiGraph n m) : Convex ℝ (metricDomain G) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨(hX.1.smul (isSelfAdjoint_iff.mpr (star_trivial a))).add (hY.1.smul (isSelfAdjoint_iff.mpr (star_trivial b))),?_,?_,?_⟩
  · simp only [add_mulVec,smul_mulVec,hX.2.1,hY.2.1,smul_zero,add_zero]
  · apply Matrix.le_iff.mpr
    have h := ((Matrix.le_iff.mp hX.2.2.1).smul ha).add ((Matrix.le_iff.mp hY.2.2.1).smul hb)
    convert h using 1
    rw [smul_sub,smul_sub]
    have hh : a • G.laplacian univ+b • G.laplacian univ=G.laplacian univ := by
      rw [←add_smul,hab,one_smul]
    nth_rw 1 [←hh]
    abel
  · intro Z hZ
    simp only [add_mul,smul_mul_assoc,trace_add,trace_smul,smul_eq_mul]
    calc
      a*(X*Z).trace+b*(Y*Z).trace ≤ a*(3*(G.laplacian univ*Z).trace)+b*(3*(G.laplacian univ*Z).trace) :=
        add_le_add (mul_le_mul_of_nonneg_left (hX.2.2.2 Z hZ) ha) (mul_le_mul_of_nonneg_left (hY.2.2.2 Z hZ) hb)
      _ = 3*(G.laplacian univ*Z).trace := by rw [←add_mul,hab,one_mul]

lemma difference_sum (u v : Fin n) : (∑i, difference u v i)=0 := by
  simp [difference,point,sum_sub_distrib]

lemma test_centered (hn : 0 < n) {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Test Z) :
    CenteredTest (centered Z) := by
  refine ⟨⟨centered_psd hZ.1,?_⟩,centered_ones hn Z⟩
  intro u v w
  simpa only [qform_centered,centering_mulVec_of_sum_zero (difference_sum _ _)] using hZ.2 u v w

lemma centered_one (hn : 0 < n) : centered (1 : Matrix (Fin n) (Fin n) ℝ)=centering n := by
  rw [centered,mul_one,mul_centering_of_ones (centering_ones hn)]

lemma centering_test (hn : 0 < n) : CenteredTest (centering n) := by
  simpa only [centered_one hn] using test_centered hn (test_one (n:=n))

lemma domain_trace_bound (G : MultiGraph n m) (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ metricDomain G) : X.trace ≤ 3*(G.laplacian univ).trace := by
  have hh := hX.2.2.2 _ (centering_test hn)
  simpa only [mul_centering_of_ones hX.2.1,mul_centering_of_ones (laplacian_ones G)] using hh

lemma domain_bounded (G : MultiGraph n m) (hn : 0 < n) : Bornology.IsBounded (metricDomain G) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨3*(G.laplacian univ).trace,fun X hX => ?_⟩
  have ht := domain_trace_bound G hn hX
  have hp := domain_psd G hX
  have hC : 0 ≤ 3*(G.laplacian univ).trace := mul_nonneg (by norm_num) (G.laplacian_psd univ).trace_nonneg
  have hd (i : Fin n) : X i i ≤ 3*(G.laplacian univ).trace :=
    (single_le_sum (fun j _ => hp.diag_nonneg (i:=j)) (mem_univ i)).trans ht
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  simpa only [Real.norm_eq_abs] using psd_entry_bound hp hC hd i j

lemma domain_compact (G : MultiGraph n m) (hn : 0 < n) : IsCompact (metricDomain G) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨domain_closed G,domain_bounded G hn⟩

lemma shortcut_add_mem_domain {m' : ℕ} (G : MultiGraph n m) (H : MultiGraph n m')
    (hn : 0 < n) (hGH : G.laplacian univ ≤ H.laplacian univ)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : CenteredPositive D)
    (ht : ∀Z, CenteredTest Z → (D*Z).trace ≤ (G.laplacian univ*Z).trace) :
    H.laplacian univ+D ∈ metricDomain H := by
  refine ⟨(H.laplacian_psd univ).isHermitian.add hD.1,?_,?_,?_⟩
  · simp only [add_mulVec,laplacian_ones H,hD.2.1,add_zero]
  · exact le_add_of_nonneg_right (Matrix.nonneg_iff_posSemidef.mpr (centeredPositive_psd hn hD))
  · intro Z hZ
    rw [add_mul,trace_add]
    have h1 := ht Z hZ
    have h2 := trace_pairing_mono hGH hZ.1.1
    have h3 := trace_pairing_nonneg (H.laplacian_psd univ) hZ.1.1
    linarith only [h1,h2,h3]

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
