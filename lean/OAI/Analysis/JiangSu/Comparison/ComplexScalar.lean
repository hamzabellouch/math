import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.FiniteScalar

namespace OAI

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma finite_scalar_unbounded {I J : Type*} (Γ : I → TracialState D)
    (hsupply : SpectralProjectionSupply Γ) (x : J → D) (s : Finset J)
    (hx : ∀ j ∈ s, IsSelfAdjoint (x j))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (q : D) (hq : IsStarProjection q) :
    ∃ P : ProjectionPacking q,
      (∀ j ∈ s, ∀ i, ∃ μ : ℝ, ‖P.piece i*x j*P.piece i-μ • P.piece i‖ ≤ ε) ∧
      ∀ i, ((Γ i).functional P.residual).re ≤ δ := by
  classical
  let M : ℝ := 1+∑ j ∈ s, ‖x j‖
  have hM : 0 < M := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ s) => norm_nonneg (x j))
    dsimp [M]; linarith
  have hjM (j : J) (hj : j ∈ s) : ‖x j‖ ≤ M := by
    have := Finset.single_le_sum (fun j (_ : j ∈ s) => norm_nonneg (x j)) hj
    dsimp [M]; linarith
  let y := fun j => M⁻¹ • x j
  have hy (j : J) (hj : j ∈ s) : IsSelfAdjoint (y j) := by
    rw [isSelfAdjoint_iff]
    simp only [y,star_smul,star_trivial,(hx j hj).star_eq]
  have hyn (j : J) (hj : j ∈ s) : ‖y j‖ ≤ 1 := by
    rw [show y j = M⁻¹ • x j from rfl,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hM]
    exact (inv_mul_le_one₀ hM).mpr (hjM j hj)
  obtain ⟨P,hP,hPi⟩ := finite_scalar_family Γ hsupply y s hy hyn (div_pos hε hM) hδ q hq
  refine ⟨P,?_,hPi⟩
  intro j hj i
  obtain ⟨μ,hμ,hbound⟩ := hP j hj i
  refine ⟨M*μ,?_⟩
  have he : P.piece i*x j*P.piece i-(M*μ) • P.piece i =
      M • (P.piece i*y j*P.piece i-μ • P.piece i) := by
    simp only [y,mul_smul_comm,smul_mul_assoc,smul_sub,smul_smul,mul_inv_cancel₀ hM.ne',one_smul]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hM]
  exact (mul_le_mul_of_nonneg_left hbound hM.le).trans_eq (by field_simp)

theorem finite_complex_scalar {I : Type*} (Γ : I → TracialState D)
    (hsupply : SpectralProjectionSupply Γ) (F : Finset D)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (q : D) (hq : IsStarProjection q) :
    ∃ P : ProjectionPacking q,
      (∀ b ∈ F, ∀ i, ∃ α : ℂ, ‖P.piece i*b*P.piece i-α • P.piece i‖ ≤ ε) ∧
      ∀ i, ((Γ i).functional P.residual).re ≤ δ := by
  classical
  let S := F.image realPart ∪ F.image imaginaryPart
  obtain ⟨P,hP,hPi⟩ := finite_scalar_unbounded Γ hsupply
    (fun a : selfAdjoint D => (a:D)) S (fun a _ => a.property) (half_pos hε) hδ q hq
  refine ⟨P,?_,hPi⟩
  intro b hb i
  obtain ⟨α,hα⟩ := hP (realPart b) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb)) i
  obtain ⟨β,hβ⟩ := hP (imaginaryPart b) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb)) i
  have hα' : ‖P.piece i*(realPart b:D)*P.piece i-(α:ℂ) • P.piece i‖ ≤ ε/2 := by
    simpa only [Complex.coe_smul] using hα
  have hβ' : ‖P.piece i*(imaginaryPart b:D)*P.piece i-(β:ℂ) • P.piece i‖ ≤ ε/2 := by
    simpa only [Complex.coe_smul] using hβ
  refine ⟨(α:ℂ)+Complex.I*β,?_⟩
  have he : P.piece i*b*P.piece i-((α:ℂ)+Complex.I*β) • P.piece i =
      (P.piece i*(realPart b:D)*P.piece i-(α:ℂ) • P.piece i)+
      Complex.I • (P.piece i*(imaginaryPart b:D)*P.piece i-(β:ℂ) • P.piece i) := by
    conv_lhs => rw [←realPart_add_I_smul_imaginaryPart b]
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,add_smul,smul_sub,smul_smul]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (by
    rw [norm_smul,Complex.norm_I,one_mul]
    linarith)

end DirectComparison

namespace DirectPacking
open Pureness CurrentMain
open scoped ComplexOrder

example {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]
    (τ : RestrictedTracialState D) (p : D) : 0 ≤ traceTwoNorm τ p := traceTwoNorm_nonneg τ p
end DirectPacking

namespace DirectComparison
open Pureness CurrentMain
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def ProjectionPacking.toPartition {q : D} (P : ProjectionPacking q) :
    ProjectionPartition P.total := by
  classical
  exact {
    Index := {i : P.Index // P.piece i ≠ 0}
    piece := fun i => P.piece i.1
    isProjection := fun i => P.projection i.1
    nonzero := fun i => i.2
    orthogonal := fun i j hij => P.orthogonal (fun h => hij (Subtype.ext h))
    sum_eq := by
      have he := Fintype.sum_subtype_add_sum_subtype (fun i => P.piece i ≠ 0) P.piece
      have hz : (∑ i : {i : P.Index // ¬P.piece i ≠ 0}, P.piece i)=0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact not_ne_iff.mp i.2
      rw [hz,add_zero] at he
      exact he }

end DirectComparison

namespace DirectPacking
open Pureness CurrentMain DirectComparison
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

theorem weighted_family_of_kraus_average {I : Type} [Fintype I]
    (hsupply : DirectComparison.SpectralProjectionSupply
      (fun τ : RestrictedTracialState D => (τ : Pureness.TracialState D))) (v : I → D) (hv : ∑ i, star (v i)*v i = 1)
    (K : Finset (unitary D)) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    {r : D} (hr : IsStarProjection r)
    (hcentral : ∀ r₀ : D, IsStarProjection r₀ → r₀ ≤ r → ∀ P : ProjectionPartition r₀, ∀ x ∈ K, ∀ τ : RestrictedTracialState D,
      ∑ s, traceOneNorm τ (weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s) -
        (x : D) * weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s) * star (x : D)) ≤ η^2) :
    ∃ F : WeightedBlockFamily r,
      (∀ j, ∀ x ∈ K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
        ‖F.range j * (x : D) * F.range j - (F.row j).matrix (F.base j) H‖ < η) ∧
      (∀ τ : RestrictedTracialState D,
        traceOneNorm τ (F.weightedSum - weightedAverage (fun _ : I => (1 : ℝ)) v r) ≤ η ^ 2) ∧
      (∀ x ∈ K, ∀ τ : RestrictedTracialState D,
        ∑ j, F.weight j * traceTwoNorm τ ((x : D) * F.range j - F.range j * (x : D)) ^ 2 ≤
          6 * η) := by
  classical
  obtain ⟨T⟩ := exists_blockControl (Fintype.card I) (Nat.cast_nonneg _) (half_pos hη)
  let K' : Finset D := K.image (fun x : unitary D => (x : D))
  let tests : Finset D := Finset.univ.biUnion fun i : I =>
    Finset.univ.biUnion fun j : I => (insert 1 K').image (fun x => star (v i) * x * v j)
  obtain ⟨P₀,hP₀,hres⟩ := DirectComparison.finite_complex_scalar
    (fun τ : RestrictedTracialState D => (τ : Pureness.TracialState D)) hsupply tests
    (ε := T.tolerance/4) (δ := η^2/2) (div_pos T.tolerance_pos (by norm_num)) (by positivity) r hr
  let P := P₀.toPartition
  have hP (b : D) (hb : b ∈ tests) (s : P.Index) :
      ∃ α : ℂ, ‖P.piece s*b*P.piece s-α • P.piece s‖ < T.tolerance/2 := by
    obtain ⟨α,hα⟩ := hP₀ b hb s.1
    exact ⟨α,hα.trans_lt (by linarith [T.tolerance_pos])⟩
  have hcompression (s : P.Index) (i j : I) (x : D) (hx : x ∈ insert 1 K') :
      ∃ α : ℂ, ‖P.piece s * (star (v i) * x * v j) * P.piece s - α • P.piece s‖ <
        T.tolerance / 2 := by
    apply hP _ _ s
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_image_of_mem _ hx⟩⟩
  have hK' (x : D) (hx : x ∈ K') : ‖x‖ ≤ 1 := by
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    have hu := CStarRing.norm_coe_unitary_mul u (1 : D)
    rw [mul_one] at hu
    exact hu.le.trans (IsStarProjection.one D).norm_le
  choose n hn U c hc hc1 hmono htr hpair using fun s =>
    raw_kraus_spectral_block v hv K' hK' T (P.isProjection s) (P.nonzero s) (hcompression s)
  let J := Σ s : P.Index, {j : Fin (n s) // 0 < orderedLayerWeights (c s) j}
  let F : WeightedBlockFamily r := {
    Index := J
    weight := fun a => orderedLayerWeights (c a.1) a.2
    weight_pos := fun a => a.2.property
    weight_le_one := fun a => (orderedLayerWeights_le (c a.1) (hc a.1) a.2).trans (hc1 a.1 a.2)
    base := fun a => P.piece a.1
    baseProjection := fun a => P.isProjection a.1
    base_nonzero := fun a => P.nonzero a.1
    base_le := fun a => (P.piece_le P₀.total_projection a.1).trans P₀.total_le
    columns := fun a => Fintype.card {i : Fin (n a.1) // a.2.val ≤ i}
    columns_pos := fun a => upperColumn_nonempty a.2.val
    row := fun a => (U a.1).subrow (upperEmbedding a.2.val) }
  have hFsum : F.weightedSum = ∑ s, ∑ i, c s i • (U s).atom i := by
    change (∑ a : J, orderedLayerWeights (c a.1) a.2 •
      ((U a.1).subrow (upperEmbedding a.2.val)).sample (P.piece a.1)) = _
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun s _ => (U s).positive_layer_sum (c s) (hc s) (hmono s)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro j x hx
    obtain ⟨H,hH⟩ := hpair j.1 _ (upperEmbedding j.2.val) (x : D) (Finset.mem_image_of_mem _ hx)
    exact ⟨H,hH.trans (by linarith)⟩
  · intro τ
    have hav : weightedAverage (fun _ : I => (1 : ℝ)) v P₀.total =
        ∑ s, weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s) := by
      calc
        _ = weightedAverage (fun _ : I => (1 : ℝ)) v (∑ s, P.piece s) :=
          congrArg (weightedAverage (fun _ : I => (1 : ℝ)) v) P.sum_eq.symm
        _ = _ := weightedAverage_sum (fun _ : I => (1 : ℝ)) v P.piece
    have hclose : traceOneNorm τ (F.weightedSum-weightedAverage (fun _ : I => (1 : ℝ)) v P₀.total) ≤ (η/2)^2 := by
      rw [hFsum,hav,←Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ s, traceOneNorm τ ((∑ i, c s i • (U s).atom i)-weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s)) :=
          traceOneNorm_sum_le τ _ fun s =>
            (projection_combination_nonneg (U s).atom (U s).atom_projection (c s) (hc s)).isSelfAdjoint.sub
              (weightedAverage_nonneg (fun _ : I => (1 : ℝ)) v (fun _ => zero_le_one) (P.isProjection s).nonneg).isSelfAdjoint
        _ ≤ ∑ s, (η/2)^2*(τ.functional (P.piece s)).re := Finset.sum_le_sum fun s _ => htr s τ
        _ = (η/2)^2*(τ.functional P₀.total).re := by rw [←Finset.mul_sum,←Complex.re_sum,←map_sum,P.sum_eq]
        _ ≤ (η/2)^2 := by
          have ht := trace_projection_le_one (τ : Pureness.TracialState D) P₀.total_projection
          nlinarith [sq_nonneg (η/2)]
    have hdiff : weightedAverage (fun _ : I => (1 : ℝ)) v r-weightedAverage (fun _ : I => (1 : ℝ)) v P₀.total =
        weightedAverage (fun _ : I => (1 : ℝ)) v P₀.residual := by
      simp only [DirectComparison.ProjectionPacking.residual,weightedAverage,one_smul,mul_sub,sub_mul,Finset.sum_sub_distrib]
    have hnon := weightedAverage_nonneg (fun _ : I => (1 : ℝ)) v (fun _ => zero_le_one) (P₀.residual_projection hr).nonneg
    have hsmall : traceOneNorm τ (weightedAverage (fun _ : I => (1 : ℝ)) v r-weightedAverage (fun _ : I => (1 : ℝ)) v P₀.total) ≤ η^2/2 := by
      rw [hdiff,traceOneNorm_of_nonneg τ hnon,kraus_average_trace τ v hv]
      exact hres τ
    have he := traceOneNorm_add_le (τ : Pureness.TracialState D)
      ((F.weightedSum_nonneg).isSelfAdjoint.sub
        (weightedAverage_nonneg (fun _ : I => (1 : ℝ)) v (fun _ => zero_le_one) P₀.total_projection.nonneg).isSelfAdjoint)
      ((weightedAverage_nonneg (fun _ : I => (1 : ℝ)) v (fun _ => zero_le_one) P₀.total_projection.nonneg).isSelfAdjoint.sub
        (weightedAverage_nonneg (fun _ : I => (1 : ℝ)) v (fun _ => zero_le_one) hr.nonneg).isSelfAdjoint)
    rw [sub_add_sub_cancel] at he
    have hrev : traceOneNorm τ (weightedAverage (fun _ : I => (1 : ℝ)) v P₀.total-weightedAverage (fun _ : I => (1 : ℝ)) v r) =
        traceOneNorm τ (weightedAverage (fun _ : I => (1 : ℝ)) v r-weightedAverage (fun _ : I => (1 : ℝ)) v P₀.total) := by
      rw [←neg_sub (weightedAverage (fun _ : I => (1 : ℝ)) v r),traceOneNorm_neg]
    rw [hrev] at he
    exact he.trans ((add_le_add hclose hsmall).trans (by nlinarith [sq_nonneg η]))
  · intro x hx τ
    change (∑ a : J, orderedLayerWeights (c a.1) a.2 * traceTwoNorm τ
      ((x : D) * ((U a.1).subrow (upperEmbedding a.2.val)).sample (P.piece a.1) -
        ((U a.1).subrow (upperEmbedding a.2.val)).sample (P.piece a.1) * (x : D)) ^ 2) ≤ _
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ s, ∑ j, orderedLayerWeights (c s) j * traceTwoNorm τ
          ((x : D) * upperLayerCut (U s).atom j - upperLayerCut (U s).atom j * (x : D)) ^ 2 :=
        Finset.sum_congr rfl fun s _ => (U s).positive_layer_energy (c s) (hc s) (hmono s) τ x
      _ ≤ 6*η := by
        apply layer_energy_global τ n (fun s => (U s).atom)
          (fun s => (U s).atom_projection) (fun s => (U s).atom_orthogonal)
          c hc hmono x (fun s => weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s))
          (fun s => weightedAverage_nonneg (fun _ : I => (1 : ℝ)) v (fun _ => zero_le_one)
            (P.isProjection s).nonneg) hη.le hη1.le
        · calc
            _ ≤ ∑ s, (η/2)^2*(τ.functional (P.piece s)).re := Finset.sum_le_sum fun s _ => htr s τ
            _ = (η/2)^2*(τ.functional P₀.total).re := by
              rw [← Finset.mul_sum,← Complex.re_sum,← map_sum,P.sum_eq]
            _ ≤ η^2 := by
              have ht := trace_projection_le_one (τ : Pureness.TracialState D) P₀.total_projection
              nlinarith [sq_nonneg η]
        · simp only [kraus_average_trace τ v hv]
          rw [← Complex.re_sum,← map_sum,P.sum_eq]
          exact trace_projection_le_one (τ : Pureness.TracialState D) P₀.total_projection
        · exact hcentral P₀.total P₀.total_projection P₀.total_le P x hx τ

end DirectPacking
end

end OAI
