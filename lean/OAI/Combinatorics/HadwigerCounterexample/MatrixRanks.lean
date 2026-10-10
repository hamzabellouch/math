import OAI.Combinatorics.HadwigerCounterexample.LinearExtension

namespace OAI


/-! # Matrix Ranks -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function

section Generic
variable {V W U : Type}
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup U] [Module F U]

theorem rk_surj {f : V →ₗ[F] W} [FiniteDimensional F W] : Surjective f ↔ rk f = dim W := by
  rw [← range_eq_top]
  constructor
  · intro h; unfold rk dim; rw [h]; exact finrank_top _ _
  exact Submodule.eq_top_of_finrank_eq

theorem rk_inj {f : V →ₗ[F] W} [FiniteDimensional F V] : Injective f ↔ rk f = dim V := by
  constructor
  · exact LinearMap.finrank_range_of_inj
  intro h
  rw [← ker_eq_bot, ← Submodule.finrank_eq_zero (R:=F)]
  have hj := f.finrank_range_add_finrank_ker
  dsimp only [rk,dim] at h
  omega

theorem rk_comp_le_right [FiniteDimensional F W] (f : V →ₗ[F] W) (g : W →ₗ[F] U) :
    rk (g ∘ₗ f) ≤ rk f := by
  dsimp only [rk]; rw [LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

theorem rk_comp_le_left [FiniteDimensional F U] (f : V →ₗ[F] W) (g : W →ₗ[F] U) :
    rk (g ∘ₗ f) ≤ rk g :=
  Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

theorem rk_add_le [FiniteDimensional F W] (f g : V →ₗ[F] W) :
    rk (f+g) ≤ rk f+rk g :=
  (Submodule.finrank_mono (show LinearMap.range (f+g) ≤ range f ⊔ range g by
    rintro x ⟨y,rfl⟩
    exact Submodule.add_mem_sup (show f y ∈ range f from ⟨y,rfl⟩)
      (show g y ∈ range g from ⟨y,rfl⟩))).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

end Generic

variable {I J K : Type}
variable [Fintype I] [Fintype J]

omit [Fintype I] in
theorem rank_cast (P : Mat I J) : P.rank = rk P.mulVecLin := rfl
theorem dim_vec (K : Type) [Fintype K] : dim (Vec K) = Fintype.card K :=
  Module.finrank_pi F

omit [Fintype I] in
theorem mrk_inj {P : Mat I J} : Function.Injective P.mulVec ↔ P.rank = Fintype.card J := by
  rw [rank_cast,← dim_vec,rk_inj.symm]; rfl
theorem mrk_surj {P : Mat I J} : Function.Surjective P.mulVec ↔ P.rank = Fintype.card I := by
  rw [rank_cast,← dim_vec,rk_surj.symm]; rfl

theorem transpose_surj_iff {P : Mat I J} : Surjective Pᵀ.mulVec ↔ Injective P.mulVec := by
  rw [mrk_surj,mrk_inj,rank_transpose]

theorem mrk_add_le (A B : Mat I J) : (A+B).rank ≤ A.rank + B.rank := by
  rw [rank_cast,rank_cast,rank_cast,mulVecLin_add]; exact rk_add_le _ _

abbrev colSp (P : Mat I J) := range P.mulVecLin
omit [Fintype I] in
theorem colSp_dim (P : Mat I J) : dim (colSp P) = P.rank := rfl

omit [Fintype I] in
theorem colSp_mem {P : Mat I J} (j : J) : P.col j ∈ colSp P := by
  rw [colSp,range_mulVecLin]
  exact Submodule.subset_span ⟨j,rfl⟩

/-- A coordinate set of basis vectors of a subspace arranged as columns. -/
def pack (S : Space (Vec I)) : Mat I (Fin (dim S)) :=
  let E : Vec (Fin (dim S)) ≃ₗ[F] S := LinearEquiv.ofFinrankEq (Vec (Fin (dim S))) S (by
    rw [finrank_pi]; simp)
  LinearMap.toMatrix' (S.subtype ∘ₗ E.toLinearMap)

theorem pack_eq {S : Space (Vec I)} :
    ∃ E : Vec (Fin (dim S)) ≃ₗ[F] S, (pack S).mulVecLin = S.subtype ∘ₗ E.toLinearMap := by
  unfold pack
  refine ⟨LinearEquiv.ofFinrankEq _ _ (by rw [finrank_pi]; simp),?_⟩
  rw [← toLin'_apply']
  exact LinearEquiv.symm_apply_apply _ _

theorem pack_inj (S : Space (Vec I)) : Function.Injective (pack S).mulVec := by
  rw [← Matrix.coe_mulVecLin]
  obtain ⟨E,he⟩ := pack_eq (S:=S)
  rw [he]
  exact Subtype.val_injective.comp E.injective

theorem colSp_pack (S : Space (Vec I)) : colSp (pack S) = S := by
  obtain ⟨E,he⟩ := pack_eq (S:=S)
  rw [colSp,he,LinearMap.range_comp]
  simp

omit [Fintype I] in
/-- Matrix multiplication cancels when a left factor is injective. -/
theorem inj_comp_mat [Fintype K] (A : Mat I J) (B : Mat J K)
    (hA : Injective A.mulVec) (hB : Injective B.mulVec) :
    Injective (A*B).mulVec := by
  rw [← coe_mulVecLin,mulVecLin_mul]
  exact hA.comp hB

omit [Fintype I] in
theorem coe_mv_inj : Function.Injective (fun P : Mat I J => P.mulVecLin) := by
  classical
  rw [show (fun P : Mat I J => P.mulVecLin) = toLin' by rfl]
  exact LinearEquiv.injective _

omit [Fintype I] in
theorem toMat_map [DecidableEq J] (f : Vec J →ₗ[F] Vec I) :
    (LinearMap.toMatrix' f).mulVecLin = f := by
  rw [← toLin'_apply']; exact LinearEquiv.symm_apply_apply _ _

/-- Paired-frame transitivity of §3 in matrix form. -/
theorem frame_move [Fintype K] [DecidableEq K] {A A' : Mat K I} {B B' : Mat K J}
    (ha : Injective A.mulVec) (ha' : Injective A'.mulVec) (hb : Injective B.mulVec)
    (hb' : Injective B'.mulVec) (h : Aᵀ * B = A'ᵀ * B') :
    ∃ L R : Mat K K, L*R = 1 ∧ R*L = 1 ∧ L*A=A' ∧ Rᵀ*B = B' := by
  classical
  have he : (Bᵀ*A) = (B'ᵀ*A') := by
    simpa only [transpose_mul,transpose_transpose] using congrArg Matrix.transpose h
  obtain ⟨C,hC,hD⟩ := equate_pair (A:=A.mulVecLin) (A':=A'.mulVecLin) (G:=Bᵀ.mulVecLin)
    (G':=B'ᵀ.mulVecLin) ha ha' (transpose_surj_iff.mpr hb)
    (transpose_surj_iff.mpr hb') (by rw [← mulVecLin_mul,← mulVecLin_mul,he])
  let L := LinearMap.toMatrix' C.toLinearMap
  let R := LinearMap.toMatrix' C.symm.toLinearMap
  have hl : L * R = 1 := by
    apply coe_mv_inj
    change (L*R).mulVecLin = Matrix.mulVecLin 1
    dsimp only [L,R]
    rw [mulVecLin_mul,toMat_map,toMat_map,mulVecLin_one]
    exact LinearMap.ext fun x => C.apply_symm_apply x
  have hr : R * L = 1 := by
    apply coe_mv_inj
    change (R*L).mulVecLin = Matrix.mulVecLin 1
    dsimp only [L,R]
    rw [mulVecLin_mul,toMat_map,toMat_map,mulVecLin_one]
    exact LinearMap.ext fun x => C.symm_apply_apply x
  refine ⟨L,R,hl,hr,?_,?_⟩
  · apply coe_mv_inj
    change (L*A).mulVecLin = _
    dsimp only [L]; rw [mulVecLin_mul,toMat_map]
    exact LinearMap.ext hC
  · have hB : Bᵀ = B'ᵀ * L := by
      apply coe_mv_inj
      change _ = (B'ᵀ*L).mulVecLin
      dsimp only [L]; rw [mulVecLin_mul,toMat_map]
      exact LinearMap.ext hD
    apply_fun Matrix.transpose
    · rw [transpose_mul,transpose_transpose,hB,Matrix.mul_assoc,hl,Matrix.mul_one]
    · exact Matrix.transpose_injective

end HadwigerCounterexample

end

end OAI
