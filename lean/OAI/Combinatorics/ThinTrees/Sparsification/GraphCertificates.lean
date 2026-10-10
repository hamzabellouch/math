import Mathlib
import OAI.Combinatorics.ThinTrees.Sparsification.GraphicHalf

namespace OAI

/-! Graph certificates. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests Normalization RationalSigning
open scoped MatrixOrder
variable {n d m : ℕ}

lemma qform_outer (u x : Fin n → ℝ) : qform (vecMulVec u u) x=(u ⬝ᵥ x)^2 := by
  rw [qform,vecMulVec_mulVec,dotProduct_smul,op_smul_eq_smul,smul_eq_mul,dotProduct_comm x u,pow_two]

lemma cut_test (S : Finset (Fin n)) : Test (vecMulVec (cutIndicator S) (cutIndicator S)) := by
  refine ⟨ShortcutDual.outer_posSemidef _,?_⟩
  intro u v w
  simp only [qform_outer,eval_difference]
  rcases cutIndicator_binary S u with hu|hu <;>
    rcases cutIndicator_binary S v with hv|hv <;>
      rcases cutIndicator_binary S w with hw|hw <;> norm_num [hu,hv,hw]

lemma trace_mul_centered (D Z : Matrix (Fin n) (Fin n) ℝ) :
    (D*centered Z).trace=(centered D*Z).trace := by
  simp only [centered]
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc,trace_mul_comm (D*centering n*Z),
    ←Matrix.mul_assoc (centering n)]
  simp only [Matrix.mul_assoc]

lemma centered_laplacian (G : MultiGraph n m) (A : Finset (Fin m)) :
    centered (G.laplacian A)=G.laplacian A := by
  apply centered_eq (G.laplacian_psd A).isHermitian
  simp only [laplacian,Matrix.sum_mulVec]
  apply sum_eq_zero
  intro e _
  rw [vecMulVec_mulVec]
  have he : G.incidence e ⬝ᵥ ones n=0 := by
    simp only [dotProduct,ones,mul_one]
    exact (mem_zeroSumSpace _).mp (G.incidence_zeroSum e)
  simp only [he,op_smul_eq_smul,zero_smul]

lemma centered_cut_trace (G : MultiGraph n m) (A : Finset (Fin m)) (S : Finset (Fin n)) :
    (G.laplacian A*centered (vecMulVec (cutIndicator S) (cutIndicator S))).trace=
      ((G.cut A S).card:ℝ) := by
  rw [trace_mul_centered,centered_laplacian,trace_mul_comm,ShortcutDual.trace_outer_mul]
  exact G.laplacian_cut A S

lemma cut_bound (G : MultiGraph n m) (hn : 0 < n) (A B : Finset (Fin m))
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ metricDomain G)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hL : G.laplacian A ≤ (1/2:ℝ) • G.laplacian B+ε • regularize X)
    (S : Finset (Fin n)) :
    ((G.cut A S).card:ℝ) ≤ (1/2+3*ε)*(G.cut univ S).card := by
  let Z := centered (vecMulVec (cutIndicator S) (cutIndicator S))
  have hZ : CenteredTest Z := test_centered hn (cut_test S)
  have hh := trace_pairing_mono hL hZ.1.1
  simp only [Matrix.add_mul,Matrix.smul_mul,trace_add,trace_smul,smul_eq_mul,
    regularize_trace _ hZ] at hh
  have hx := hX.2.2.2 Z hZ
  have hcut : ((G.cut B S).card:ℝ) ≤ (G.cut univ S).card := by
    exact_mod_cast card_le_card (show G.cut B S ⊆ G.cut univ S from
      fun e he => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2⟩)
  simp only [Z,centered_cut_trace] at hx hh
  have hm := mul_le_mul_of_nonneg_left hx hε
  nlinarith only [hh,hm,hcut]

lemma square_whitening {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.PosDef) :
    ∃M : Matrix (Fin d) (Fin d) ℝ, IsUnit M ∧ Mᵀ=M ∧ M*M=Q⁻¹ ∧ M*Q*M=1 := by
  obtain ⟨S,hS,hunit,hSS⟩ := posDef_sqrt_factors hQ
  have hSi : S⁻¹*S=1 := nonsing_inv_mul S ((isUnit_iff_isUnit_det _).mp hunit)
  have hiS : S*S⁻¹=1 := mul_nonsing_inv S ((isUnit_iff_isUnit_det _).mp hunit)
  refine ⟨S⁻¹,by simpa only [isUnit_nonsing_inv_iff] using hunit,?_,?_,?_⟩
  · rw [transpose_nonsing_inv,(isHermitian_iff_isSymm.mp hS).eq]
  · rw [←hSS,Matrix.mul_inv_rev]
  · rw [←hSS,←Matrix.mul_assoc,hSi,Matrix.one_mul,hiS]

lemma packing_bound (G : MultiGraph (d+1) m) (hn : 2 ≤ d+1)
    (B A : Finset (Fin m)) (hAB : A ⊆ B) (s : Fin m → ℚ)
    (hs : ∀e, 0 < s e)
    (hQ : ((scaledForm G B s).map (fun q : ℚ => (q:ℝ))).PosDef)
    {c h : ℝ} {r : ℕ} (hc : 0 < c) (hh : 0 < h) (hr : (r:ℝ)*h ≤ c)
    (hnorm : ∀e ∈ B, leverage (realColumns (graphColumns G B)) (realWeights s) e ≤ h)
    (hlow : c • ((scaledForm G B s).map (fun q : ℚ => (q:ℝ))) ≤
      StackedSigning.gram (realVec (scaledColumns G B s)) A) : G.TreePackable A r := by
  let Q := (scaledForm G B s).map (fun q : ℚ => (q:ℝ))
  obtain ⟨M,hM,hMt,hMM,hMQ⟩ := square_whitening hQ
  let L₀ := dropRoot d
  let L := L₀.trans (Matrix.toLinearEquiv' M hM.invertible)
  have hv (e : Fin m) (he : e ∈ B) : M*ᵥrealVec (scaledColumns G B s) e=
      (s e:ℝ) • L ⟨G.incidence e,G.incidence_zeroSum e⟩ := by
    rw [scaledColumns_cast,graphColumns_cast,ite_eq_left he,mulVec_smul]
    rfl
  have hvecnorm (e : Fin m) : (M*ᵥrealVec (scaledColumns G B s) e) ⬝ᵥ
      (M*ᵥrealVec (scaledColumns G B s) e)=
        leverage (realColumns (graphColumns G B)) (realWeights s) e := by
    rw [←hMt,GramWhitening.rectangular_norm,hMt,hMM,scaledColumns_leverage]
  have hLo := GramWhitening.congruence_mono hlow M
  rw [hMt,Matrix.mul_smul,Matrix.smul_mul,hMQ] at hLo
  have hGram : M*StackedSigning.gram (realVec (scaledColumns G B s)) A*M=
      ∑e∈A,vecMulVec ((s e:ℝ) • L ⟨G.incidence e,G.incidence_zeroSum e⟩)
        ((s e:ℝ) • L ⟨G.incidence e,G.incidence_zeroSum e⟩) := by
    rw [StackedSigning.gram]
    nth_rw 1 [←hMt]
    rw [←GramWhitening.congruence_sum_outer,hMt]
    apply sum_congr rfl
    intro e he
    rw [hv e (hAB he)]
  rw [hGram] at hLo
  apply G.represented_frame_treePackable hn L (fun e => (s e:ℝ))
    (fun e => by exact_mod_cast hs e) A hc hh hr
  · intro e he
    dsimp only
    rw [←hv e (hAB he),hvecnorm]
    exact hnorm e (hAB he)
  · intro x
    have hx := qform_mono hLo x
    change qform (c • (1 : Matrix (Fin d) (Fin d) ℝ)) x ≤ qform _ x at hx
    rw [qform_smul,qform_covariance] at hx
    simpa only [qform,one_mulVec] using hx

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
