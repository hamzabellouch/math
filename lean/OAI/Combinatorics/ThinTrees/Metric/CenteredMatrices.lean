import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.MatrixBound

namespace OAI

/-! Centered matrices. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

def ones (n : ℕ) : Fin n → ℝ := fun _ => 1

def constantProjection (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (n : ℝ)⁻¹ • vecMulVec (ones n) (ones n)

def centering (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := 1-constantProjection n

lemma ones_dot (x : Fin n → ℝ) : ones n ⬝ᵥ x=∑i, x i := by
  simp [ones,dotProduct]

lemma constantProjection_psd : (constantProjection n).PosSemidef := by
  apply Matrix.PosSemidef.smul _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  simpa only [star_trivial] using posSemidef_vecMulVec_self_star (ones n)

lemma constantProjection_symmetric : (constantProjection n)ᵀ=constantProjection n :=
  isHermitian_iff_isSymm.mp constantProjection_psd.isHermitian

lemma centering_symmetric : (centering n)ᵀ=centering n := by
  simp only [centering,transpose_sub,transpose_one,constantProjection_symmetric]

lemma constantProjection_mulVec (x : Fin n → ℝ) :
    constantProjection n *ᵥ x=((∑i, x i)/(n:ℝ)) • ones n := by
  ext j
  simp [constantProjection,mulVec,dotProduct,Matrix.smul_apply,vecMulVec,ones,div_eq_mul_inv,Finset.sum_mul,mul_comm]

lemma qform_constantProjection (x : Fin n → ℝ) :
    qform (constantProjection n) x=(∑i, x i)^2/(n:ℝ) := by
  rw [qform,constantProjection_mulVec,dotProduct_smul,dotProduct_comm x,ones_dot]
  simp only [smul_eq_mul]
  ring

lemma centering_mulVec (x : Fin n → ℝ) :
    centering n *ᵥ x=x-((∑i, x i)/(n:ℝ)) • ones n := by
  rw [centering,sub_mulVec,one_mulVec,constantProjection_mulVec]

lemma centering_mulVec_of_sum_zero {x : Fin n → ℝ} (hx : ∑i, x i=0) :
    centering n *ᵥ x=x := by
  simp only [centering_mulVec,hx,zero_div,zero_smul,sub_zero]

lemma centering_mulVec_sum (hn : 0 < n) (x : Fin n → ℝ) :
    ∑i, (centering n *ᵥ x) i=0 := by
  rw [centering_mulVec]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,ones,sum_sub_distrib,mul_one,
    sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  ring

lemma constantProjection_ones (hn : 0 < n) : constantProjection n *ᵥ ones n=ones n := by
  rw [constantProjection_mulVec]
  simp only [ones,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)),one_smul]

lemma centering_ones (hn : 0 < n) : centering n *ᵥ ones n=0 := by
  rw [centering,sub_mulVec,one_mulVec,constantProjection_ones hn,sub_self]

lemma centered_dot (b y : Fin n → ℝ) (hb : ∑i, b i=0) :
    b ⬝ᵥ (centering n *ᵥ y)=b ⬝ᵥ y := by
  rw [dotProduct_mulVec,←mulVec_transpose,centering_symmetric,centering_mulVec_of_sum_zero hb]

def centered (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  centering n*D*centering n

lemma centered_psd {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosSemidef) : (centered D).PosSemidef := by
  have hh := hD.mul_mul_conjTranspose_same (centering n)
  simpa only [centered,conjTranspose_eq_transpose_of_trivial,centering_symmetric] using hh

lemma centered_ones (hn : 0 < n) (D : Matrix (Fin n) (Fin n) ℝ) : centered D *ᵥ ones n=0 := by
  simp only [centered,←mulVec_mulVec,centering_ones hn,mulVec_zero]

lemma qform_centered (D : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qform (centered D) x=qform D (centering n *ᵥ x) := by
  unfold centered qform
  rw [←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec,←mulVec_transpose,centering_symmetric]

def CenteredPositive (D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  D.IsHermitian ∧ D *ᵥ ones n=0 ∧ ∀x : Fin n → ℝ, (∑i, x i)=0 → x ≠ 0 → 0 < qform D x

def regularize (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  D+constantProjection n

def inverseOnZeroSum (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (regularize D)⁻¹

lemma centered_positive (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) :
    CenteredPositive (centered D) := by
  refine ⟨(centered_psd hD.posSemidef).isHermitian,centered_ones hn D,?_⟩
  intro x hx hne
  rw [qform_centered,centering_mulVec_of_sum_zero hx]
  simpa only [qform,star_trivial] using hD.dotProduct_mulVec_pos hne

lemma regularize_centered_pd (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) :
    (regularize (centered D)).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos
    ((centered_psd hD.posSemidef).add constantProjection_psd).isHermitian
  intro x hx
  change 0 < qform (regularize (centered D)) x
  rw [regularize,qform_add,qform_centered]
  by_cases hp : centering n *ᵥ x=0
  · have hs : (∑i, x i) ≠ 0 := by
      intro hs
      rw [centering_mulVec_of_sum_zero hs] at hp
      exact hx hp
    have hq : 0 < qform (constantProjection n) x := by
      rw [qform_constantProjection]
      exact div_pos (sq_pos_of_ne_zero hs) (Nat.cast_pos.mpr hn)
    exact add_pos_of_nonneg_of_pos (qform_nonneg hD.posSemidef _) hq
  · have hq : 0 < qform D (centering n *ᵥ x) := by
      simpa only [qform,star_trivial] using hD.dotProduct_mulVec_pos hp
    exact add_pos_of_pos_of_nonneg hq (qform_nonneg constantProjection_psd _)

lemma inverseOnZeroSum_solves (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD0 : D *ᵥ ones n=0) (hD : (regularize D).PosDef)
    {b : Fin n → ℝ} (hb : (∑i, b i)=0) :
    (∑i, (inverseOnZeroSum D *ᵥ b) i)=0 ∧ D *ᵥ (inverseOnZeroSum D *ᵥ b)=b := by
  let y := inverseOnZeroSum D *ᵥ b
  have hy : regularize D *ᵥ y=b := posDef_solve hD b
  have h1 : regularize D *ᵥ ones n=ones n := by
    rw [regularize,add_mulVec,hD0,constantProjection_ones hn,zero_add]
  have hys : ∑i, y i=0 := by
    have hh := MatrixDual.quadratic_symm hD.isHermitian (ones n) y
    rw [hy,h1,dotProduct_comm y,ones_dot,ones_dot,hb] at hh
    exact hh.symm
  refine ⟨hys,?_⟩
  rw [regularize,add_mulVec,constantProjection_mulVec,hys,zero_div,zero_smul,add_zero] at hy
  exact hy

lemma inverse_centered_le (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : D.PosDef) {b : Fin n → ℝ} (hb : (∑i, b i)=0) :
    qform (inverseOnZeroSum (centered D)) b ≤ qform D⁻¹ b := by
  let A := regularize (centered D)
  have hA : A.PosDef := regularize_centered_pd hn hD
  let y := A⁻¹ *ᵥ b
  have hs : A *ᵥ y=b := posDef_solve hA b
  have hq : qform D (centering n *ᵥ y) ≤ b ⬝ᵥ y := by
    have hh : qform A y=b ⬝ᵥ y := by rw [qform,hs,dotProduct_comm]
    dsimp [A] at hh
    rw [regularize,qform_add,qform_centered] at hh
    linarith only [hh,qform_nonneg (constantProjection_psd (n:=n)) y]
  have hv := MatrixDual.inverse_quadratic_variational hD b (centering n *ᵥ y)
  rw [centered_dot b y hb] at hv
  change 2*(b ⬝ᵥ y)-qform D (centering n *ᵥ y) ≤ qform D⁻¹ b at hv
  change b ⬝ᵥ y ≤ qform D⁻¹ b
  linarith only [hv,hq]

lemma centeredTest_mul_constant {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    Z*constantProjection n=0 := by
  have h0 : Z *ᵥ ones n=0 := hZ.2
  simp only [constantProjection,mul_smul_comm,mul_vecMulVec,h0,zero_vecMulVec,smul_zero]

lemma centeredTest_constant_mul {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    constantProjection n*Z=0 := by
  have hh := congrArg transpose (centeredTest_mul_constant hZ)
  simpa only [transpose_mul,constantProjection_symmetric,
    (isHermitian_iff_isSymm.mp hZ.1.1.isHermitian).eq,transpose_zero] using hh

lemma centeredTest_mul_centering {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    Z*centering n=Z := by
  rw [centering,mul_sub,mul_one,centeredTest_mul_constant hZ,sub_zero]

lemma centeredTest_centering_mul {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    centering n*Z=Z := by
  rw [centering,sub_mul,one_mul,centeredTest_constant_mul hZ,sub_zero]

lemma centered_trace (D : Matrix (Fin n) (Fin n) ℝ)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    (centered D*Z).trace=(D*Z).trace := by
  rw [centered,mul_assoc (centering n*D),centeredTest_centering_mul hZ,
    mul_assoc,trace_mul_comm,mul_assoc,centeredTest_mul_centering hZ]

lemma regularize_trace (D : Matrix (Fin n) (Fin n) ℝ)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : CenteredTest Z) :
    (regularize D*Z).trace=(D*Z).trace := by
  rw [regularize,add_mul,trace_add,centeredTest_constant_mul hZ,trace_zero,add_zero]

lemma laplacian_zeroSum_pos (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ)
    (x : Fin n → ℝ) (hx : (∑i, x i)=0) (hxne : x ≠ 0) :
    0 < qform (G.laplacian univ) x := by
  have hnonneg := qform_nonneg (G.laplacian_psd univ) x
  by_contra hpos
  have hzero : qform (G.laplacian univ) x=0 := le_antisymm (not_lt.mp hpos) hnonneg
  have hedge (e : Fin m) : x (G.left e)-x (G.right e)=0 := by
    rw [G.laplacian_qform] at hzero
    have he := (single_le_sum (fun i _ => sq_nonneg (x (G.left i)-x (G.right i))) (mem_univ e))
    rw [hzero] at he
    exact sq_eq_zero_iff.mp (le_antisymm he (sq_nonneg _))
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => x ⬝ᵥ v
      map_add' := fun v w => dotProduct_add x v w
      map_smul' := fun c v => dotProduct_smul c x v }
  have hf : G.edgeSpan univ ≤ f.ker := by
    apply (Packing.span_le_iff G.incidence).mpr
    intro e _
    change (∑v, x v*G.incidence e v)=0
    rw [G.eval_incidence]
    exact hedge e
  have hxx : x ⬝ᵥ x=0 := hf (by rw [G.connected_span_zeroSum hn hc]; exact (mem_zeroSumSpace x).mpr hx)
  exact hxne (dotProduct_self_eq_zero.mp hxx)

lemma laplacian_ones (G : MultiGraph n m) : G.laplacian univ *ᵥ ones n=0 := by
  simp only [laplacian,sum_mulVec,vecMulVec_mulVec]
  apply Finset.sum_eq_zero
  intro e _
  rw [dotProduct_comm]
  change MulOpposite.op (∑v, ones n v*G.incidence e v) • G.incidence e=0
  rw [G.eval_incidence]
  simp [ones]

lemma laplacian_centered_positive (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ) :
    CenteredPositive (G.laplacian univ) :=
  ⟨(G.laplacian_psd univ).isHermitian,laplacian_ones G,laplacian_zeroSum_pos G hn hc⟩

lemma laplacian_regularize_pd (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ) :
    (regularize (G.laplacian univ)).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos ((G.laplacian_psd univ).add constantProjection_psd).isHermitian
  intro x hx
  change 0 < qform (regularize (G.laplacian univ)) x
  rw [regularize,qform_add]
  by_cases hxs : (∑i, x i)=0
  · exact add_pos_of_pos_of_nonneg (laplacian_zeroSum_pos G hn hc x hxs hx)
      (qform_nonneg constantProjection_psd x)
  · apply add_pos_of_nonneg_of_pos (qform_nonneg (G.laplacian_psd univ) x)
    rw [qform_constantProjection]
    exact div_pos (sq_pos_of_ne_zero hxs) (Nat.cast_pos.mpr hn)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
