import OAI.Analysis.Naimark.Homogeneity

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped BigOperators InnerProductSpace ComplexOrder
open Filter Topology
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {ι : Type*} [fintypeι : Fintype ι] [decidableEqι : DecidableEq ι]

def matrixRow (r : ι) (x : ι → A) : CStarMatrix ι ι A :=
  CStarMatrix.ofMatrix (fun i j => if i=r then x j else 0)

omit partialOrderA starOrderedRingA fintypeι in
@[simp] lemma matrixRow_apply [PartialOrder A] [StarOrderedRing A] [Fintype ι] (r : ι) (x : ι → A) (i j : ι) :
    matrixRow r x i j = if i=r then x j else 0 := rfl

omit partialOrderA starOrderedRingA in
lemma matrixRow_gram [PartialOrder A] [StarOrderedRing A] (r : ι) (x : ι → A) (i j : ι) :
    (star (matrixRow r x)*matrixRow r x) i j = star (x i)*x j := by
  simp only [CStarMatrix.mul_apply,CStarMatrix.star_apply,matrixRow_apply]
  simp only [apply_ite star,star_zero,ite_mul,mul_ite,zero_mul,mul_zero]
  simp

def matrixConst (a : A) : CStarMatrix ι ι A :=
  matrixDiagonalHom (fun _ => StarAlgHom.id ℂ A) (fun _ => a)

omit partialOrderA starOrderedRingA in
@[simp] lemma matrixConst_apply [PartialOrder A] [StarOrderedRing A] (a : A) (i j : ι) :
    matrixConst (ι:=ι) a i j = if i=j then a else 0 := by simp [matrixConst]

lemma matrixConst_norm (a : A) : ‖matrixConst (ι:=ι) a‖ ≤ ‖a‖ := by
  exact (NonUnitalStarAlgHom.norm_apply_le
    (matrixDiagonalHom (fun _ : ι => StarAlgHom.id ℂ A)) (fun _ => a)).trans (pi_norm_le_iff_of_nonneg (norm_nonneg a) |>.mpr (fun _ => le_rfl))

@[simp] lemma matrixConst_star (a : A) : star (matrixConst (ι:=ι) a) = matrixConst (star a) := by
  ext i j
  simp only [CStarMatrix.star_apply,matrixConst_apply,apply_ite star,star_zero]
  split_ifs <;> simp_all

omit partialOrderA starOrderedRingA in
@[simp] lemma matrixConst_mul [PartialOrder A] [StarOrderedRing A] (a b : A) : matrixConst (ι:=ι) a*matrixConst (ι:=ι) b=matrixConst (ι:=ι) (a*b) := by
  exact (map_mul (matrixDiagonalHom (fun _ : ι => StarAlgHom.id ℂ A)) (fun _ => a) (fun _ => b)).symm

lemma matrixRow_average (r : ι) (x : ι → A) (a : A) :
    (matrixRow r x*matrixConst (ι:=ι) a*star (matrixRow r x)) r r = rowAverage x a := by
  simp only [CStarMatrix.mul_apply,CStarMatrix.star_apply,matrixRow_apply,matrixConst_apply,ite_true]
  simp [rowAverage]

lemma matrixRow_average_norm (r : ι) (x : ι → A) (a : A) :
    ‖rowAverage x a‖ ≤ ‖matrixRow r x‖^2*‖a‖ := by
  rw [← matrixRow_average r x a]
  exact (CStarMatrix.norm_entry_le_norm).trans ((norm_mul_le _ _).trans
    ((mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (matrixConst_norm a) (norm_nonneg _))) (norm_nonneg _)).trans_eq
      (by rw [norm_star]; ring)))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpaceH : CompleteSpace H]

def columnMap (v : ι → H) : EuclideanSpace ℂ ι →L[ℂ] H :=
  ∑ i, (EuclideanSpace.proj i).smulRight (v i)

omit decidableEqι completeSpaceH in
@[simp] lemma columnMap_apply [DecidableEq ι] [CompleteSpace H] (v : ι → H) (z : EuclideanSpace ℂ ι) :
    columnMap v z = ∑ i, z i • v i := by simp [columnMap]

@[simp] lemma columnMap_single (v : ι → H) (i : ι) :
    columnMap v (EuclideanSpace.single i 1) = v i := by
  simp [columnMap_apply,PiLp.single_apply,ite_smul]

lemma columnMap_adjoint_apply (v : ι → H) (y : H) (i : ι) :
    (columnMap v).adjoint y i = ⟪v i,y⟫_ℂ := by
  have h := (columnMap v).adjoint_inner_right (EuclideanSpace.single i 1) y
  simpa only [EuclideanSpace.inner_single_left,map_one,one_mul,columnMap_single] using h

def matrixOperator : CStarMatrix ι ι ℂ ≃⋆ₐ[ℂ]
    (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  CStarMatrix.ofMatrixStarAlgEquiv.symm.trans Matrix.toEuclideanCLM

lemma matrixOperator_apply (M : CStarMatrix ι ι ℂ) (z : EuclideanSpace ℂ ι) (i : ι) :
    matrixOperator M z i = ∑ j, M i j*z j := rfl

def scalarGram (v : ι → H) : CStarMatrix ι ι ℂ :=
  CStarMatrix.ofMatrix (fun i j => ⟪v i,v j⟫_ℂ)

lemma scalarGram_operator (v : ι → H) :
    matrixOperator (scalarGram v) = (columnMap v).adjoint.comp (columnMap v) := by
  ext z i
  rw [matrixOperator_apply,ContinuousLinearMap.comp_apply,columnMap_adjoint_apply,columnMap_apply]
  change (∑ j, ⟪v i, v j⟫_ℂ * z j) = ⟪v i, ∑ j, z j • v j⟫_ℂ
  simp only [inner_sum,inner_smul_right,mul_comm]

lemma scalarGram_norm (v : ι → H) : ‖scalarGram v‖=‖columnMap v‖^2 := by
  rw [← StarAlgEquiv.norm_map (matrixOperator (ι:=ι)) (scalarGram v),scalarGram_operator,
    ContinuousLinearMap.norm_adjoint_comp_self,pow_two]

def matrixScalar : CStarMatrix ι ι ℂ →⋆ₙₐ[ℂ] CStarMatrix ι ι A :=
  CStarMatrix.mapₙₐ (StarAlgHom.ofId ℂ A).toNonUnitalStarAlgHom

omit partialOrderA starOrderedRingA decidableEqι in
@[simp] lemma matrixScalar_apply [PartialOrder A] [StarOrderedRing A] [DecidableEq ι] (M : CStarMatrix ι ι ℂ) (i j : ι) :
    matrixScalar (A:=A) M i j = M i j • (1:A) := by
  change algebraMap ℂ A (M i j) = _
  exact Algebra.algebraMap_eq_smul_one _

omit decidableEqι in
lemma matrixScalar_norm [DecidableEq ι] (M : CStarMatrix ι ι ℂ) :
    ‖matrixScalar (A:=A) M‖ ≤ ‖M‖ := NonUnitalStarAlgHom.norm_apply_le _ _

lemma matrixScalar_mul_const (M : CStarMatrix ι ι ℂ) (a : A) (i j : ι) :
    (matrixScalar (A:=A) M*matrixConst (ι:=ι) a) i j = M i j • a := by
  simp only [CStarMatrix.mul_apply,matrixScalar_apply,matrixConst_apply,mul_ite,mul_zero]
  simp

lemma excision_matrix_gram_tendsto
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (r : ι) (c : ι → A) :
    Tendsto (fun e =>
      star (matrixRow r (fun i => c i*pureExcisionNet π ξ e)) *
        matrixRow r (fun i => c i*pureExcisionNet π ξ e) -
      matrixScalar (scalarGram (fun i => π (c i) ξ)) *
        matrixConst (pureExcisionNet π ξ e*pureExcisionNet π ξ e)) atTop (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hs : ⟪ξ,π (star (c i)*c j) ξ⟫_ℂ = ⟪π (c i) ξ,π (c j) ξ⟫_ℂ := by
    simp only [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  have he := pureExcisionNet_excision π hπ ξ hξ (star (c i)*c j)
  convert he using 1
  · funext e
    simp only [CStarMatrix.sub_apply,matrixRow_gram,matrixScalar_mul_const,scalarGram,
      star_mul,
      (IsSelfAdjoint.of_nonneg (pureExcisionNet_nonneg π ξ e)).star_eq,hs]
    change _ - ⟪π (c i) ξ,π (c j) ξ⟫_ℂ • _ = _
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,mul_assoc]
  · rfl

omit partialOrderA starOrderedRingA in
lemma norm_lt_of_gram_approx [PartialOrder A] [StarOrderedRing A] (R G Q : A) (k δ : ℝ) (hk : 0 ≤ k) (hδ : 0 < δ)
    (hQ : ‖Q‖ ≤ 1) (hG : ‖G‖ ≤ k^2) (he : ‖star R*R-G*Q‖ < δ^2) :
    ‖R‖ < k+δ := by
  have hn : ‖G*Q‖ ≤ k^2 := by
    calc
      _ ≤ ‖G‖*‖Q‖ := norm_mul_le G Q
      _ ≤ ‖G‖*1 := mul_le_mul_of_nonneg_left hQ (norm_nonneg G)
      _ ≤ k^2 := by simpa using hG
  have hs : ‖R‖^2 ≤ ‖star R*R-G*Q‖+k^2 := by
    calc
      _ = ‖star R*R‖ := by rw [CStarRing.norm_star_mul_self,pow_two]
      _ ≤ ‖star R*R-G*Q‖+‖G*Q‖ := by
        simpa only [sub_add_cancel] using norm_add_le (star R*R-G*Q) (G*Q)
      _ ≤ _ := add_le_add le_rfl hn
  nlinarith [norm_nonneg R]

lemma excision_matrix_row_norm
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (r : ι) (c : ι → A) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ e in atTop,
      ‖matrixRow r (fun i => c i*pureExcisionNet π ξ e)‖ <
        ‖columnMap (fun i => π (c i) ξ)‖+δ := by
  have ht := (excision_matrix_gram_tendsto π hπ ξ hξ r c).norm
  have he := ht.eventually (gt_mem_nhds (by simpa using sq_pos_of_pos hδ))
  filter_upwards [he] with e he
  apply norm_lt_of_gram_approx _
    (matrixScalar (A:=A) (scalarGram (fun i => π (c i) ξ)))
    (matrixConst (pureExcisionNet π ξ e*pureExcisionNet π ξ e)) _ δ
    (norm_nonneg _) hδ ?_ ?_ he
  · apply (matrixConst_norm _).trans
    apply (norm_mul_le _ _).trans
    nlinarith [pureExcisionNet_norm π ξ e,norm_nonneg (pureExcisionNet π ξ e)]
  · exact (matrixScalar_norm _).trans_eq (scalarGram_norm _)

end KOS

open scoped InnerProductSpace BigOperators
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpaceH : CompleteSpace H]
variable {ι : Type*} [Fintype ι]

omit completeSpaceH in
lemma norm_sum_sq_of_orthogonal [CompleteSpace H] (v : ι → H)
    (hv : ∀ i j, i ≠ j → ⟪v i,v j⟫_ℂ = 0) :
    ‖∑ i, v i‖^2 = ∑ i, ‖v i‖^2 := by
  classical
  have hi : ⟪∑ i, v i,∑ i, v i⟫_ℂ = ∑ i, ⟪v i,v i⟫_ℂ := by
    simp only [sum_inner,inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_eq_single i (fun j _ hji => hv j i hji) (by simp)
  have hr := congrArg Complex.reCLM hi
  simpa only [map_sum,Complex.reCLM_apply,← RCLike.re_to_complex,inner_self_eq_norm_sq] using hr

lemma projection_inner_zero {P Q : H →L[ℂ] H}
    (hP : IsStarProjection P) (hPQ : P*Q=0) (x y : H) :
    ⟪P x,Q y⟫_ℂ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint,hP.isSelfAdjoint.star_eq,
    ← mul_apply_eq_comp,hPQ,zero_apply,inner_zero_right]

lemma projection_family_sum_norm_sq_le (P : ι → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i))
    (ho : ∀ i j, i ≠ j → P i*P j=0) (x : H) :
    ∑ i, ‖P i x‖^2 ≤ ‖x‖^2 := by
  classical
  let y : H := ∑ i, P i x
  have hp (i : ι) : P i y = P i x := by
    simp only [y,map_sum,← mul_apply_eq_comp]
    rw [Finset.sum_eq_single i]
    · rw [(hP i).isIdempotentElem.eq]
    · intro j _ hji
      rw [ho i j hji.symm,zero_apply]
    · simp
  have horth : ⟪y,x-y⟫_ℂ = 0 := by
    simp only [y,sum_inner]
    apply Finset.sum_eq_zero
    intro i _
    rw [← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint,(hP i).isSelfAdjoint.star_eq,
      map_sub,hp,sub_self,inner_zero_right]
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y (x-y) horth
  have hy : ‖y‖^2 = ∑ i, ‖P i x‖^2 :=
    norm_sum_sq_of_orthogonal _ (fun i j hij => projection_inner_zero (hP i) (ho i j hij) x x)
  rw [add_sub_cancel] at he
  have he' : ‖x‖^2 = ‖y‖^2 + ‖x-y‖^2 := by nlinarith [he]
  rw [hy] at he'
  nlinarith [sq_nonneg ‖x-y‖]

lemma projection_blocks_norm_le (P Q : ι → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ i, IsStarProjection (Q i))
    (hoP : ∀ i j, i ≠ j → P i*P j=0)
    (hoQ : ∀ i j, i ≠ j → Q i*Q j=0) (b : H →L[ℂ] H) :
    ‖∑ i, Q i*b*P i‖ ≤ ‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg b)
  intro x
  have hv : ∀ i, ‖Q i (b (P i x))‖ ≤ ‖b‖*‖P i x‖ := by
    intro i
    exact ((Q i).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (IsStarProjection.norm_le _ (hQ i))
      (norm_nonneg _)).trans (by simpa using b.le_opNorm (P i x)))
  have he : ‖(∑ i, Q i*b*P i) x‖^2 = ∑ i, ‖Q i (b (P i x))‖^2 := by
    simp only [sum_apply,mul_apply_eq_comp]
    exact norm_sum_sq_of_orthogonal _ (fun i j hij =>
      projection_inner_zero (hQ i) (hoQ i j hij) _ _)
  have hs : ‖(∑ i, Q i*b*P i) x‖^2 ≤ (‖b‖*‖x‖)^2 := by
    rw [he]
    calc
      _ ≤ ∑ i, (‖b‖*‖P i x‖)^2 := Finset.sum_le_sum (fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)
      _ = ‖b‖^2 * ∑ i, ‖P i x‖^2 := by simp [mul_pow,Finset.mul_sum]
      _ ≤ ‖b‖^2*‖x‖^2 := mul_le_mul_of_nonneg_left
        (projection_family_sum_norm_sq_le P hP hoP x) (sq_nonneg _)
      _ = _ := (mul_pow _ _ _).symm
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hs

end KOS

open scoped BigOperators
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure ProjectionChain (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  P : ℕ → H →L[ℂ] H
  projection : ∀ n, IsStarProjection (P n)
  increasing : ∀ i j, i ≤ j → P i*P j=P i

namespace ProjectionChain
variable (J : ProjectionChain H)

def block (n : ℕ) : H →L[ℂ] H := J.P (n+1)-J.P n

lemma reverse_increasing (i j : ℕ) (hij : i ≤ j) : J.P j*J.P i=J.P i := by
  have h := congrArg star (J.increasing i j hij)
  simpa only [star_mul,(J.projection i).isSelfAdjoint.star_eq,
    (J.projection j).isSelfAdjoint.star_eq] using h

lemma block_projection (n : ℕ) : IsStarProjection (J.block n) := by
  constructor
  · change (J.P (n+1)-J.P n)*(J.P (n+1)-J.P n) = J.P (n+1)-J.P n
    rw [sub_mul,mul_sub,mul_sub,(J.projection (n+1)).isIdempotentElem.eq,
      (J.projection n).isIdempotentElem.eq,J.increasing n (n+1) (by omega),
      J.reverse_increasing n (n+1) (by omega)]
    abel
  · exact (J.projection (n+1)).isSelfAdjoint.sub (J.projection n).isSelfAdjoint

lemma blocks_orthogonal (i j : ℕ) (hij : i ≠ j) : J.block i*J.block j=0 := by
  have hlt : ∀ i j : ℕ, i < j → J.block i*J.block j=0 := by
    intro i j h
    dsimp [block]
    rw [sub_mul,mul_sub,mul_sub,J.increasing (i+1) (j+1) (by omega),
      J.increasing (i+1) j (by omega),J.increasing i (j+1) (by omega),
      J.increasing i j (by omega)]
    abel
  rcases lt_or_gt_of_ne hij with h|h
  · exact hlt i j h
  · have he := congrArg star (hlt j i h)
    simpa only [star_mul,star_zero,(J.block_projection i).isSelfAdjoint.star_eq,
      (J.block_projection j).isSelfAdjoint.star_eq] using he

lemma upper_block (b : H →L[ℂ] H) (hb : ∀ n, J.P (n+1)*b*J.P n=b*J.P n)
    (n : ℕ) :
    J.block (n+1)*b*J.block n = b*J.P (n+1)-J.P (n+1)*b*J.P (n+1) := by
  have hfar : J.P (n+2)*b*J.P n=b*J.P n := by
    calc
      _ = J.P (n+2)*(J.P (n+1)*(b*J.P n)) := by
        simpa only [mul_assoc] using congrArg (fun T => J.P (n+2)*T) (hb n).symm
      _ = J.P (n+1)*(b*J.P n) := by
        rw [← mul_assoc,J.reverse_increasing (n+1) (n+2) (by omega)]
      _ = _ := by rw [← mul_assoc,hb n]
  dsimp [block]
  simp only [sub_mul,mul_sub]
  rw [hb (n+1),hfar,hb n]
  abel

lemma commutator_block (b : H →L[ℂ] H) (hs : IsSelfAdjoint b)
    (hb : ∀ n, J.P (n+1)*b*J.P n=b*J.P n) (n : ℕ) :
    b*J.P (n+1)-J.P (n+1)*b =
      J.block (n+1)*b*J.block n-star (J.block (n+1)*b*J.block n) := by
  rw [J.upper_block b hb n]
  simp only [star_sub,star_mul,hs.star_eq,(J.projection (n+1)).isSelfAdjoint.star_eq]
  noncomm_ring

def average (N : ℕ) : H →L[ℂ] H := (N:ℝ)⁻¹ • ∑ i : Fin N, J.P (i.val+1)

lemma sum_commutator_norm_le (b : H →L[ℂ] H) (hs : IsSelfAdjoint b)
    (hb : ∀ n, J.P (n+1)*b*J.P n=b*J.P n) (N : ℕ) :
    ‖b*(∑ i : Fin N, J.P (i.val+1))-(∑ i : Fin N, J.P (i.val+1))*b‖ ≤ 2*‖b‖ := by
  have he : b*(∑ i : Fin N, J.P (i.val+1))-(∑ i : Fin N, J.P (i.val+1))*b =
      (∑ i : Fin N, J.block (i.val+1)*b*J.block i.val) -
      star (∑ i : Fin N, J.block (i.val+1)*b*J.block i.val) := by
    simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib,star_sum]
    exact Finset.sum_congr rfl (fun i _ => J.commutator_block b hs hb i.val)
  have hu : ‖∑ i : Fin N, J.block (i.val+1)*b*J.block i.val‖ ≤ ‖b‖ := by
    apply projection_blocks_norm_le <;> try exact fun i => J.block_projection _
    · intro i j hij
      exact J.blocks_orthogonal _ _ (fun he => hij (Fin.ext he))
    · intro i j hij
      exact J.blocks_orthogonal _ _ (fun he => hij (Fin.ext (by omega)))
  rw [he]
  exact (norm_sub_le _ _).trans (by rw [norm_star]; linarith)

lemma average_commutator_norm_le (b : H →L[ℂ] H) (hs : IsSelfAdjoint b)
    (hb : ∀ n, J.P (n+1)*b*J.P n=b*J.P n) (N : ℕ) :
    ‖b*J.average N-J.average N*b‖ ≤ 2*‖b‖/(N:ℝ) := by
  rw [average,mul_smul_comm,smul_mul_assoc,← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  exact (mul_le_mul_of_nonneg_left (J.sum_commutator_norm_le b hs hb N)
    (inv_nonneg.mpr (Nat.cast_nonneg N))).trans_eq (by ring)

end ProjectionChain
end KOS

open scoped BigOperators
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpaceH : CompleteSpace H]

open Classical in
def krylovSet (F : Finset (H →L[ℂ] H)) (ξ : H) : ℕ → Finset H
  | 0 => {ξ}
  | n+1 => krylovSet F ξ n ∪ F.biUnion (fun b => (krylovSet F ξ n).image b)

def krylovSpace (F : Finset (H →L[ℂ] H)) (ξ : H) (n : ℕ) : Submodule ℂ H :=
  Submodule.span ℂ (↑(krylovSet F ξ n) : Set H)

instance krylovSpace_finite (F : Finset (H →L[ℂ] H)) (ξ : H) (n : ℕ) :
    FiniteDimensional ℂ (krylovSpace F ξ n) :=
  FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet _)

omit completeSpaceH in
lemma krylovSpace_mono [CompleteSpace H] (F : Finset (H →L[ℂ] H)) (ξ : H) :
    Monotone (krylovSpace F ξ) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  apply Submodule.span_mono
  exact Finset.coe_subset.mpr (Finset.subset_union_left)

lemma mem_krylovSpace (F : Finset (H →L[ℂ] H)) (ξ : H) (n : ℕ) :
    ξ ∈ krylovSpace F ξ n := by
  exact krylovSpace_mono F ξ (Nat.zero_le n) (Submodule.subset_span (by simp [krylovSet]))

omit completeSpaceH in
lemma map_mem_krylovSpace [CompleteSpace H] (F : Finset (H →L[ℂ] H)) (ξ : H) (n : ℕ)
    (b : H →L[ℂ] H) (hb : b ∈ F) {x : H} (hx : x ∈ krylovSpace F ξ n) :
    b x ∈ krylovSpace F ξ (n+1) := by
  classical
  apply Submodule.span_induction (p := fun x _ => b x ∈ krylovSpace F ξ (n+1)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    apply Submodule.subset_span
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_image.mpr ⟨y,hy,rfl⟩⟩)
  · rw [map_zero]
    exact (krylovSpace F ξ (n+1)).zero_mem
  · intro x y _ _ hx hy
    simpa using (krylovSpace F ξ (n+1)).add_mem hx hy
  · intro a x _ hx
    simpa using (krylovSpace F ξ (n+1)).smul_mem a hx

def krylovChain (F : Finset (H →L[ℂ] H)) (ξ : H) : ProjectionChain H where
  P n := (krylovSpace F ξ n).starProjection
  projection n := isStarProjection_starProjection
  increasing i j hij := by
    exact Submodule.starProjection_comp_starProjection_of_le (krylovSpace_mono F ξ hij)

lemma krylovChain_band (F : Finset (H →L[ℂ] H)) (ξ : H)
    (b : H →L[ℂ] H) (hb : b ∈ F) (n : ℕ) :
    (krylovChain F ξ).P (n+1)*b*(krylovChain F ξ).P n = b*(krylovChain F ξ).P n := by
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  apply map_mem_krylovSpace F ξ n b hb
  exact Submodule.starProjection_apply_mem _ _

lemma krylovChain_fixes (F : Finset (H →L[ℂ] H)) (ξ : H) (n : ℕ) :
    (krylovChain F ξ).P n ξ = ξ :=
  Submodule.starProjection_eq_self_iff.mpr (mem_krylovSpace F ξ n)

lemma krylovAverage_fixes (F : Finset (H →L[ℂ] H)) (ξ : H) (N : ℕ) (hN : 0 < N) :
    (krylovChain F ξ).average N ξ = ξ := by
  simp only [ProjectionChain.average,smul_apply,sum_apply,krylovChain_fixes,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hN),one_smul]

lemma krylovAverage_selfAdjoint (F : Finset (H →L[ℂ] H)) (ξ : H) (N : ℕ) :
    IsSelfAdjoint ((krylovChain F ξ).average N) := by
  change star ((krylovChain F ξ).average N) = _
  simp only [ProjectionChain.average,star_smul,star_trivial,star_sum,
    fun n => ((krylovChain F ξ).projection n).isSelfAdjoint.star_eq]

lemma krylovAverage_norm (F : Finset (H →L[ℂ] H)) (ξ : H) (N : ℕ) :
    ‖(krylovChain F ξ).average N‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl|hN
  · simp [ProjectionChain.average]
  rw [ProjectionChain.average,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  have hs : ‖∑ i : Fin N, (krylovChain F ξ).P (i.val+1)‖ ≤ (N:ℝ) := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ =>
      IsStarProjection.norm_le _ ((krylovChain F ξ).projection _))).trans_eq (by simp))
  exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg N))).trans_eq
    (inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hN))

lemma krylovAverage_mem (F : Finset (H →L[ℂ] H)) (ξ : H) (N : ℕ) (x : H) :
    (krylovChain F ξ).average N x ∈ krylovSpace F ξ N := by
  simp only [ProjectionChain.average,smul_apply,sum_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i _
  exact krylovSpace_mono F ξ (by omega : i.val+1 ≤ N)
    (Submodule.starProjection_apply_mem _ x)

lemma krylovAverage_projection (F : Finset (H →L[ℂ] H)) (ξ : H) (N : ℕ) :
    (krylovChain F ξ).average N*(krylovSpace F ξ N).starProjection =
      (krylovChain F ξ).average N := by
  have he : (krylovSpace F ξ N).starProjection*(krylovChain F ξ).average N =
      (krylovChain F ξ).average N := by
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr (krylovAverage_mem F ξ N x)
  have hs := congrArg star he
  simpa only [star_mul,(krylovAverage_selfAdjoint F ξ N).star_eq,
    (isStarProjection_starProjection (U:=krylovSpace F ξ N)).isSelfAdjoint.star_eq] using hs

end KOS

open scoped BigOperators InnerProductSpace
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [decidableEqι : DecidableEq ι]

lemma columnMap_comp (T : H →L[ℂ] H) (v : ι → H) :
    columnMap (fun i => T (v i)) = T.comp (columnMap v) := by
  ext z
  simp only [columnMap_apply,ContinuousLinearMap.comp_apply,map_sum,map_smul]

lemma columnMap_sub (v w : ι → H) :
    columnMap (fun i => v i-w i) = columnMap v-columnMap w := by
  ext z
  simp only [columnMap_apply,sub_apply,smul_sub,Finset.sum_sub_distrib]

lemma columnMap_matrix (v : ι → H) (B : CStarMatrix ι ι ℂ) :
    columnMap (fun j => ∑ i, B i j • v i) = (columnMap v).comp (matrixOperator B) := by
  ext z
  simp only [columnMap_apply,ContinuousLinearMap.comp_apply,matrixOperator_apply,
    Finset.smul_sum,Finset.sum_smul,smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

variable (M : Submodule ℂ H) [finiteDimensionalM : FiniteDimensional ℂ M] (e : OrthonormalBasis ι ℂ M)

def basisColumn : EuclideanSpace ℂ ι →L[ℂ] H := columnMap (fun i => (e i : H))

omit finiteDimensionalM in
lemma basisColumn_apply [FiniteDimensional ℂ M] (z : EuclideanSpace ℂ ι) : basisColumn M e z = (e.repr.symm z : H) := by
  rw [basisColumn,columnMap_apply]
  have h := congrArg (fun x : M => (x:H)) (e.sum_repr (e.repr.symm z))
  simpa using h

lemma basisColumn_norm : ‖basisColumn M e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [basisColumn_apply]
  change ‖e.repr.symm z‖ ≤ 1*‖z‖
  simp

lemma basisColumn_projection :
    (basisColumn M e).comp (basisColumn M e).adjoint = M.starProjection := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,basisColumn,columnMap_apply,columnMap_adjoint_apply]
  rw [e.starProjection_eq_sum_rankOne]
  simp only [sum_apply,InnerProductSpace.rankOne_apply]

omit decidableEqι finiteDimensionalM in
lemma basisColumn_compression_selfAdjoint [DecidableEq ι] [FiniteDimensional ℂ M] (b : H →L[ℂ] H) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint ((basisColumn M e).adjoint.comp (b.comp (basisColumn M e))) := by
  change star _ = _
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  change (basisColumn M e).adjoint.comp ((star b).comp (basisColumn M e)) = _
  rw [hb.star_eq]

lemma compressedColumn_defect (T b : H →L[ℂ] H) (hTP : T*M.starProjection=T) :
    (b.comp (T.comp (basisColumn M e))) -
      (T.comp (basisColumn M e)).comp ((basisColumn M e).adjoint.comp (b.comp (basisColumn M e))) =
    (b*T-T*b).comp (basisColumn M e) := by
  have hp := basisColumn_projection M e
  have ht : T.comp ((basisColumn M e).comp (basisColumn M e).adjoint)=T := by
    rw [hp]
    exact hTP
  calc
    _ = b.comp (T.comp (basisColumn M e)) -
        (T.comp ((basisColumn M e).comp (basisColumn M e).adjoint)).comp
          (b.comp (basisColumn M e)) := by rfl
    _ = _ := by rw [ht]; rfl

lemma krylov_column_reconstruct (F : Finset (H →L[ℂ] H)) (ξ : H) (N : ℕ) (hN : 0<N)
    (e : OrthonormalBasis ι ℂ (krylovSpace F ξ N)) :
    let W := (krylovChain F ξ).average N |>.comp (basisColumn (krylovSpace F ξ N) e)
    W (W.adjoint ξ) = ξ := by
  dsimp only
  rw [ContinuousLinearMap.adjoint_comp]
  have hs : ((krylovChain F ξ).average N).adjoint=(krylovChain F ξ).average N :=
    (krylovAverage_selfAdjoint F ξ N).star_eq
  rw [hs]
  simp only [ContinuousLinearMap.comp_apply,krylovAverage_fixes F ξ N hN]
  have hp := congrArg (fun T : H →L[ℂ] H => T ξ)
    (basisColumn_projection (krylovSpace F ξ N) e)
  rw [ContinuousLinearMap.comp_apply] at hp
  rw [hp,Submodule.starProjection_eq_self_iff.mpr (mem_krylovSpace F ξ N),
    krylovAverage_fixes F ξ N hN]

end KOS

open scoped BigOperators InnerProductSpace
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_quasicentral_columns (F : Finset (H →L[ℂ] H))
    (hF : ∀ b ∈ F, IsSelfAdjoint b) (ξ : H) (hξ : ‖ξ‖=1)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ (n : ℕ) (_ : 0<n) (w : Fin n → H) (B : (H →L[ℂ] H) → CStarMatrix (Fin n) (Fin n) ℂ),
      ‖columnMap w‖ ≤ 1 ∧ columnMap w ((columnMap w).adjoint ξ)=ξ ∧
      ∀ b ∈ F, IsSelfAdjoint (B b) ∧
        ‖columnMap (fun j => b (w j)-∑ i, B b i j • w i)‖ ≤ δ := by
  classical
  let K : ℝ := ∑ b ∈ F, ‖b‖
  have hK : 0 ≤ K := Finset.sum_nonneg (fun b _ => norm_nonneg b)
  obtain ⟨N,hN⟩ := exists_nat_gt (2*K/δ)
  have hN0 : 0<N := by
    have hn : (0:ℝ)<N := (div_nonneg (by positivity) hδ.le).trans_lt hN
    exact_mod_cast hn
  let M := krylovSpace F ξ N
  let e := stdOrthonormalBasis ℂ M
  let L := basisColumn M e
  let T := (krylovChain F ξ).average N
  have hn0 : 0<Module.finrank ℂ M := by
    have hξ0 : ξ ≠ 0 := by intro hz; simp [hz] at hξ
    let : Nontrivial M := nontrivial_of_ne (⟨ξ,mem_krylovSpace F ξ N⟩:M) 0
      (by intro hz; exact hξ0 (congrArg Subtype.val hz))
    exact Module.finrank_pos
  let w := fun i => T (e i : H)
  let B := fun b : H →L[ℂ] H => matrixOperator.symm (L.adjoint.comp (b.comp L))
  have hw : columnMap w=T.comp L := columnMap_comp T _
  refine ⟨Module.finrank ℂ M,hn0,w,B,?_,?_,?_⟩
  · rw [hw]
    have hn := ContinuousLinearMap.opNorm_comp_le T L
    have hT := krylovAverage_norm F ξ N
    have hL := basisColumn_norm M e
    exact hn.trans (by nlinarith [norm_nonneg T,norm_nonneg L])
  · rw [hw]
    exact krylov_column_reconstruct F ξ N hN0 e
  · intro b hb
    have hB : IsSelfAdjoint (B b) :=
      (basisColumn_compression_selfAdjoint M e b (hF b hb)).map matrixOperator.symm
    refine ⟨hB,?_⟩
    have hd : columnMap (fun j => b (w j)-∑ i, B b i j • w i) =
        (b*T-T*b).comp L := by
      rw [columnMap_sub,columnMap_comp,columnMap_matrix,hw]
      change b.comp (T.comp L)-(T.comp L).comp (matrixOperator (matrixOperator.symm _)) = _
      rw [StarAlgEquiv.apply_symm_apply]
      exact compressedColumn_defect M e T b (krylovAverage_projection F ξ N)
    rw [hd]
    calc
      _ ≤ ‖b*T-T*b‖*‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖b*T-T*b‖ := mul_le_of_le_one_right (norm_nonneg _) (basisColumn_norm M e)
      _ ≤ 2*‖b‖/(N:ℝ) := (krylovChain F ξ).average_commutator_norm_le b (hF b hb)
        (krylovChain_band F ξ b hb) N
      _ ≤ δ := by
        have hbK : ‖b‖ ≤ K := Finset.single_le_sum (fun b _ => norm_nonneg b) hb
        have hN' : 2*K < (N:ℝ)*δ := (div_lt_iff₀ hδ).mp hN
        apply (div_le_iff₀ (by exact_mod_cast hN0)).mpr
        nlinarith

end KOS

open scoped BigOperators
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixConst_mul_entry (b : A) (X : CStarMatrix ι ι A) (i j : ι) :
    (matrixConst (ι:=ι) b*X) i j = b*X i j := by
  simp only [CStarMatrix.mul_apply,matrixConst_apply,ite_mul,zero_mul]
  simp

lemma matrix_mulConst_entry (b : A) (X : CStarMatrix ι ι A) (i j : ι) :
    (X*matrixConst (ι:=ι) b) i j = X i j*b := by
  simp only [CStarMatrix.mul_apply,matrixConst_apply,mul_ite,mul_zero]
  simp

lemma scalar_const_commute (B : CStarMatrix ι ι ℂ) (a : A) :
    Commute (matrixScalar (A:=A) B) (matrixConst (ι:=ι) a) := by
  change matrixScalar (A:=A) B*matrixConst (ι:=ι) a = matrixConst a*matrixScalar B
  ext i j
  simp only [matrixConst_mul_entry,matrix_mulConst_entry,matrixScalar_apply,
    smul_mul_assoc,mul_smul_comm,mul_one,one_mul]

lemma matrixRow_mul_scalar (r : ι) (x : ι → A) (B : CStarMatrix ι ι ℂ) :
    matrixRow r x*matrixScalar B = matrixRow r (fun j => ∑ i, B i j • x i) := by
  ext i j
  simp only [CStarMatrix.mul_apply,matrixRow_apply,matrixScalar_apply]
  by_cases h : i=r
  · simp [h]
  · simp [h]

lemma matrixRow_defect (r : ι) (x : ι → A) (b e : A) (B : CStarMatrix ι ι ℂ) :
    matrixConst b*matrixRow r (fun i => x i*e) -
      matrixRow r (fun i => x i*e)*matrixScalar B =
    matrixRow r (fun j => (b*x j-∑ i, B i j • x i)*e) := by
  rw [matrixRow_mul_scalar]
  ext i j
  simp only [CStarMatrix.sub_apply,matrixConst_mul_entry,matrixRow_apply]
  split_ifs with h
  · simp only [sub_mul,Finset.sum_mul,smul_mul_assoc,mul_assoc]
  · simp

omit partialOrderA starOrderedRingA in
lemma commutator_factorization [PartialOrder A] [StarOrderedRing A] (b X C B : A) (hb : IsSelfAdjoint b)
    (hB : IsSelfAdjoint B) (hBC : Commute B C) :
    b*(X*C*star X)-(X*C*star X)*b =
      (b*X-X*B)*C*star X-X*C*star (b*X-X*B) := by
  simp only [star_sub,star_mul,hb.star_eq,hB.star_eq]
  have he := hBC.eq
  noncomm_ring [he]

lemma commutator_factorization_norm (b X C B : A) (hb : IsSelfAdjoint b)
    (hB : IsSelfAdjoint B) (hBC : Commute B C) :
    ‖b*(X*C*star X)-(X*C*star X)*b‖ ≤ 2*‖b*X-X*B‖*‖X‖*‖C‖ := by
  rw [commutator_factorization b X C B hb hB hBC]
  calc
    _ ≤ ‖(b*X-X*B)*C*star X‖+‖X*C*star (b*X-X*B)‖ := norm_sub_le _ _
    _ ≤ (‖b*X-X*B‖*‖C‖)*‖star X‖+(‖X‖*‖C‖)*‖star (b*X-X*B)‖ := by
      exact add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_mul_le _ _) (norm_nonneg _))) ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
    _ = _ := by simp only [norm_star]; ring

lemma rowAverage_commutator_norm (r : ι) (x : ι → A) (b e a : A)
    (hb : IsSelfAdjoint b) (B : CStarMatrix ι ι ℂ) (hB : IsSelfAdjoint B) :
    ‖b*rowAverage (fun i => x i*e) a-rowAverage (fun i => x i*e) a*b‖ ≤
      2*‖matrixRow r (fun j => (b*x j-∑ i, B i j • x i)*e)‖*
        ‖matrixRow r (fun i => x i*e)‖*‖a‖ := by
  let X := matrixRow r (fun i => x i*e)
  have hb' : IsSelfAdjoint (matrixConst (ι:=ι) b) := by
    change star _ = _
    rw [matrixConst_star,hb.star_eq]
  have hB' : IsSelfAdjoint (matrixScalar (A:=A) B) := hB.map _
  have hn := commutator_factorization_norm (matrixConst b) X (matrixConst a)
    (matrixScalar B) hb' hB' (scalar_const_commute B a)
  rw [matrixRow_defect] at hn
  have he : b*rowAverage (fun i => x i*e) a-rowAverage (fun i => x i*e) a*b =
      ((matrixConst (ι:=ι) b*(X*matrixConst a*star X)-(X*matrixConst a*star X)*matrixConst b) : CStarMatrix ι ι A) r r := by
    simp only [CStarMatrix.sub_apply,matrixConst_mul_entry,matrix_mulConst_entry,
      X,matrixRow_average]
  rw [he]
  exact CStarMatrix.norm_entry_le_norm.trans (hn.trans
    (mul_le_mul_of_nonneg_left (matrixConst_norm a) (by positivity)))

end KOS

open scoped InnerProductSpace BigOperators
open Filter Topology
namespace KOS
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma pureExcisionNet_strong
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (η : H) :
    Tendsto (fun e => π (pureExcisionNet π ξ e) η) atTop (𝓝 (⟪ξ,η⟫_ℂ • ξ)) := by
  have horth : ⟪ξ,η-⟪ξ,η⟫_ℂ • ξ⟫_ℂ = 0 := by
    simp [inner_self_eq_norm_sq_to_K,hξ]
  have ht := excision_orthogonal_strong π hπ ξ hξ (pureExcisionNet π ξ)
    (pureExcisionNet_nonneg π ξ) (pureExcisionNet_excision π hπ ξ hξ) _ horth
  have he (e : ExcisionIndex (vectorNullAlgebra π ξ)) :
      π (pureExcisionNet π ξ e) η = π (pureExcisionNet π ξ e) (η-⟪ξ,η⟫_ℂ • ξ) + ⟪ξ,η⟫_ℂ • ξ := by
    rw [map_sub,map_smul,pureExcisionNet_fixes π (irreducible_map_one π hπ) ξ]
    abel
  simpa only [he,zero_add] using ht.add_const (⟪ξ,η⟫_ℂ • ξ)

lemma pureExcisionNet_squared_strong
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (η : H) :
    Tendsto (fun e => π (pureExcisionNet π ξ e*pureExcisionNet π ξ e) η) atTop
      (𝓝 (⟪ξ,η⟫_ℂ • ξ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := ((pureExcisionNet_strong π hπ ξ hξ η).sub_const (⟪ξ,η⟫_ℂ • ξ)).norm
  apply squeeze_zero (fun _ => norm_nonneg _) ?_ (by simpa using ht)
  intro e
  have he : π (pureExcisionNet π ξ e*pureExcisionNet π ξ e) η-⟪ξ,η⟫_ℂ • ξ =
      π (pureExcisionNet π ξ e) (π (pureExcisionNet π ξ e) η-⟪ξ,η⟫_ℂ • ξ) := by
    simp only [map_mul,mul_apply_eq_comp,map_sub,map_smul,
      pureExcisionNet_fixes π (irreducible_map_one π hπ) ξ]
  rw [he]
  exact ((π (pureExcisionNet π ξ e)).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) ((NonUnitalStarAlgHom.norm_apply_le π _).trans
      (pureExcisionNet_norm π ξ e)))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma excision_rowAverage_vector_tendsto
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (c : ι → A) :
    Tendsto (fun e => π (rowAverage (fun i => c i*pureExcisionNet π ξ e) 1) ξ) atTop
      (𝓝 ((columnMap (fun i => π (c i) ξ))
        ((columnMap (fun i => π (c i) ξ)).adjoint ξ))) := by
  have hin (i : ι) : ⟪ξ,π (star (c i)) ξ⟫_ℂ = ⟪π (c i) ξ,ξ⟫_ℂ := by
    simp only [map_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  have ht (i : ι) := (π (c i)).continuous.tendsto _ |>.comp
    (pureExcisionNet_squared_strong π hπ ξ hξ (π (star (c i)) ξ))
  have hs := tendsto_finsetSum Finset.univ (fun i _ => ht i)
  convert hs using 1
  · funext e
    simp only [rowAverage,map_sum,sum_apply,star_mul,
      (IsSelfAdjoint.of_nonneg (pureExcisionNet_nonneg π ξ e)).star_eq,
      mul_one,mul_assoc,map_mul,mul_apply_eq_comp,Function.comp_def]
  · congr 1
    simp only [columnMap_apply,columnMap_adjoint_apply,hin,map_smul]

end KOS

open scoped BigOperators InnerProductSpace
open Filter Topology
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit partialOrderA starOrderedRingA in
lemma irreducible_vector_lift [PartialOrder A] [StarOrderedRing A]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (η : H) : ∃ v : A, π v ξ=η := by
  let M := Submodule.span ℂ ({ξ}:Set H)
  let : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton ξ)
  obtain ⟨v,_,hv⟩ := irreducible_adjoint_transitivity π hπ M (InnerProductSpace.rankOne ℂ η ξ)
  refine ⟨v,?_⟩
  simpa [InnerProductSpace.rankOne_apply,inner_self_eq_norm_sq_to_K,hξ] using
    (hv ξ (Submodule.subset_span (by simp))).1

theorem approximate_matrix_rows_selfAdjoint
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (F : Finset A) (hF : ∀ b ∈ F, IsSelfAdjoint b)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ (n : ℕ) (x : Fin n → A),
      (∀ a : A, ‖rowAverage x a‖ ≤ 4*‖a‖) ∧
      ‖π (rowAverage x 1) ξ-ξ‖ ≤ δ ∧
      ∀ b ∈ F, ∀ a : A, 0≤a → a≤1 → ‖b*rowAverage x a-rowAverage x a*b‖ ≤ δ := by
  classical
  let t : ℝ := min (1/2) (δ/8)
  have ht : 0<t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1/2 := min_le_left _ _
  have htδ : 8*t ≤ δ := by have := min_le_right (1/2:ℝ) (δ/8); dsimp [t]; linarith
  obtain ⟨n,hn,w,B,hw,hfix,hcomm⟩ := finite_quasicentral_columns (F.image π)
    (by intro b hb; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb; exact (hF a ha).map π)
    ξ hξ t ht
  choose v hv using fun i : Fin n => irreducible_vector_lift π hπ ξ hξ (w i)
  let r : Fin n := ⟨0,hn⟩
  have hfe := (excision_rowAverage_vector_tendsto π hπ ξ hξ v)
  simp only [hv,hfix] at hfe
  have hef : ∀ᶠ e in atTop,
      ‖π (rowAverage (fun i => v i*pureExcisionNet π ξ e) 1) ξ-ξ‖ < δ := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hfe δ hδ)
  have her : ∀ᶠ e in atTop, ‖matrixRow r (fun i => v i*pureExcisionNet π ξ e)‖ < 2 := by
    filter_upwards [excision_matrix_row_norm π hπ ξ hξ r v t ht] with e he
    simp only [hv] at he
    linarith
  let d := fun b : A => fun j : Fin n => b*v j-∑ i, B (π b) i j • v i
  have hd (b : A) (j : Fin n) : π (d b j) ξ = π b (w j)-∑ i, B (π b) i j • w i := by
    simp only [d,map_sub,sub_apply,map_sum,sum_apply,map_smul,smul_apply,map_mul,mul_apply_eq_comp,hv]
  have heD : ∀ᶠ e in atTop, ∀ b ∈ F,
      ‖matrixRow r (fun j => d b j*pureExcisionNet π ξ e)‖ < 2*t := by
    apply F.eventually_all.mpr
    intro b hb
    have hcb := (hcomm (π b) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)).2
    filter_upwards [excision_matrix_row_norm π hπ ξ hξ r (d b) t ht] with e he
    simp only [hd] at he
    linarith
  obtain ⟨e,hef,her,heD⟩ := (hef.and (her.and heD)).exists
  refine ⟨n,fun i => v i*pureExcisionNet π ξ e,?_,hef.le,?_⟩
  · intro a
    apply (matrixRow_average_norm r _ a).trans
    exact mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg (matrixRow r (fun i => v i*pureExcisionNet π ξ e))]) (norm_nonneg a)
  · intro b hb a ha ha1
    have hB := (hcomm (π b) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)).1
    have han : ‖a‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg a ha).mpr ha1
    have hn := rowAverage_commutator_norm r v b (pureExcisionNet π ξ e) a (hF b hb) (B (π b)) hB
    have hDb := (heD b hb).le
    change ‖matrixRow r (fun j => (b*v j-∑ i, B (π b) i j • v i)*pureExcisionNet π ξ e)‖ ≤ 2*t at hDb
    apply hn.trans
    calc
      _ ≤ 2*(2*t)*2*1 := by gcongr
      _ ≤ δ := by linarith

end KOS

open scoped BigOperators InnerProductSpace ComplexStarModule
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit partialOrderA starOrderedRingA in
lemma commutator_real_imaginary_norm [PartialOrder A] [StarOrderedRing A] (b y : A) :
    ‖b*y-y*b‖ ≤ ‖(realPart b:A)*y-y*(realPart b:A)‖ +
      ‖(imaginaryPart b:A)*y-y*(imaginaryPart b:A)‖ := by
  have he : b*y-y*b = ((realPart b:A)*y-y*(realPart b:A)) +
      Complex.I • ((imaginaryPart b:A)*y-y*(imaginaryPart b:A)) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart b]
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_sub]
    abel
  rw [he]
  simpa only [norm_smul,Complex.norm_I,one_mul] using norm_add_le
    ((realPart b:A)*y-y*(realPart b:A)) (Complex.I • ((imaginaryPart b:A)*y-y*(imaginaryPart b:A)))

lemma approximate_matrix_rows
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (F : Finset A) (δ : ℝ) (hδ : 0<δ) :
    ∃ (n : ℕ) (x : Fin n → A),
      (∀ a : A, ‖rowAverage x a‖ ≤ 4*‖a‖) ∧
      ‖π (rowAverage x 1) ξ-ξ‖ ≤ δ ∧
      ∀ b ∈ F, ∀ a : A, 0≤a → a≤1 → ‖b*rowAverage x a-rowAverage x a*b‖ ≤ δ := by
  classical
  let E := F.image (fun b => (realPart b:A)) ∪ F.image (fun b => (imaginaryPart b:A))
  have hE : ∀ b ∈ E, IsSelfAdjoint b := by
    intro b hb
    rcases Finset.mem_union.mp hb with hr|hi
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hr
      exact (realPart a).property
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
      exact (imaginaryPart a).property
  obtain ⟨n,x,hn,hfix,hcomm⟩ := approximate_matrix_rows_selfAdjoint π hπ ξ hξ E hE (δ/2) (by positivity)
  refine ⟨n,x,hn,by linarith,?_⟩
  intro b hb a ha ha1
  apply (commutator_real_imaginary_norm b (rowAverage x a)).trans
  have hr := hcomm (realPart b) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)) a ha ha1
  have hi := hcomm (imaginaryPart b) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)) a ha ha1
  linarith

omit partialOrderA starOrderedRingA in
lemma commutator_congruence_norm_four [PartialOrder A] [StarOrderedRing A] (F b y : A) (d c : ℝ)
    (hd : ‖b-1‖ ≤ d) (hd1 : d ≤ 1) (hy : ‖y‖ ≤ 4)
    (hc : ‖F*y-y*F‖ ≤ c) :
    ‖F*(b*y*star b)-(b*y*star b)*F‖ ≤ c+24*‖F‖*d := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hn : ‖b*y*star b-y‖ ≤ 12*d :=
    (near_congruence_norm b y d hd hd1).trans (by nlinarith)
  have he : F*(b*y*star b)-(b*y*star b)*F =
      (F*y-y*F) + F*(b*y*star b-y)-(b*y*star b-y)*F := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖F*y-y*F‖+‖F*(b*y*star b-y)‖+‖(b*y*star b-y)*F‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ c+‖F‖*(12*d)+(12*d)*‖F‖ := by
      apply add_le_add
      · exact add_le_add hc ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _)))
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    _ = _ := by ring

theorem nearCentralRows : NearCentralRows (A:=A) := by
  classical
  intro f hf F c hc
  let B : ℝ := ∑ z ∈ F, ‖z‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let t : ℝ := min (1/48) (c/(1+1152*B))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hc (by positivity))
  have ht48 : t ≤ 1/48 := min_le_left _ _
  have htc : t*(1+1152*B) ≤ c :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let π := pureGNS f hf
  let ξ := gnsVector (positiveOfSquares f hf.1.2)
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one _ ((isState_iff f).mp hf.1).1
  obtain ⟨n,x,hx,hfix,hcentral⟩ := approximate_matrix_rows π (pure_gns_irreducible f hf.1 hf) ξ hξ F t ht
  obtain ⟨b,hb,hbfix⟩ := irreducible_near_congruence π
    (pure_gns_irreducible f hf.1 hf) (rowAverage x 1)
    (rowAverage_selfAdjoint x 1 (IsSelfAdjoint.one A)) ξ hξ t hfix (by linarith)
  refine ⟨n,fun i => b*x i,?_,?_⟩
  · simpa only [rowAverage_congruence] using hbfix
  · intro z hz a ha ha1
    rw [rowAverage_congruence]
    have hay : ‖rowAverage x a‖ ≤ 4 := by
      have han : ‖a‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg a ha).mpr ha1
      exact (hx a).trans (by linarith)
    have hzB : ‖z‖ ≤ B := Finset.single_le_sum (fun z _ => norm_nonneg z) hz
    exact (commutator_congruence_norm_four z b (rowAverage x a) (48*t) t hb
      (by linarith) hay (hcentral z hz a ha ha1)).trans (by
        nlinarith [mul_le_mul_of_nonneg_right hzB ht.le])

theorem homogeneity [TopologicalSpace.SeparableSpace A]
    (hA : IsSimpleCStar A) (hinf : ¬ FiniteDimensional ℂ A)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    ∃ γ : A ≃⋆ₐ[ℂ] A, ∀ a, f (γ a) = g a :=
  homogeneity_of_nearCentralRows hA hinf nearCentralRows f g hf hg

end KOS

end NaimarkZFC

end

end OAI
