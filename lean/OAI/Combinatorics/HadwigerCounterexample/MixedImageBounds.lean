import OAI.Combinatorics.HadwigerCounterexample.FrameOrbitLaws
import OAI.Combinatorics.HadwigerCounterexample.ConditionalProductLaws
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace OAI

/-! # Mixed Image Bounds -/

noncomputable section

namespace HadwigerCounterexample
open Matrix Function LinearMap
open scoped BigOperators

variable {I J U S : Type} [Fintype I] [Fintype J] [Fintype U] [Fintype S]
  [DecidableEq I] [DecidableEq J] [DecidableEq U] [DecidableEq S]

def mixImage (D : Mat (I ⊕ I) J) (x : Mat U I × Mat U I) := fromCols x.1 x.2 * D

def mixImageLin (D : Mat (I ⊕ I) J) :
    (Mat U I × Mat U I) →ₗ[F] Mat U J where
  toFun := mixImage D
  map_add' a b := by
    have e : fromCols (a+b).1 (a+b).2 = fromCols a.1 a.2 + fromCols b.1 b.2 := by
      ext i j; cases j <;> rfl
    unfold mixImage
    rw [e,Matrix.add_mul]
  map_smul' b x := by
    have e : fromCols (b•x).1 (b•x).2 = b • fromCols x.1 x.2 := by
      ext i j; cases j <;> rfl
    unfold mixImage
    rw [e,Matrix.smul_mul]; rfl

/-- Exact image tests under a translate-stable minus (or plus) pair law cost
dim T bits per vector. Directions mix both endpoints in one direct sum. -/
theorem mixed_cap {w w' : Wgt (Mat U I)} (hw : SubLaw w) (hw' : SubLaw w')
    (T : Space (Vec U)) (hT : columnInv (w:=w) T) (hT' : columnInv (w:=w') T)
    (D : Mat (I ⊕ I) J) (hD : Injective D.mulVec) (M : Mat U J) :
    pr (pairW w w') (fun x => mixImage D x = M) ≤ bp (- (dim T:ℝ)*num J) := by
  let n := dim T
  obtain ⟨F,hF⟩ := mat_left_inv hD
  obtain ⟨R,hR⟩ := mat_left_inv (pack_inj T)
  have hi : Injective (fun A : Mat (Fin n) J => pack T * A) := by
    intro A B h
    have he := congrArg (R * ·) h
    simpa only [← Matrix.mul_assoc,hR,Matrix.one_mul] using he
  let e : Mat (Fin n) J ↪ Mat U J := ⟨(pack T * ·),hi⟩
  let f : (Mat U I × Mat U I) →ₗ[HadwigerCounterexample.F] Mat U J := mixImageLin D
  have he (t : Mat (Fin n) J) :
      ∃ x, f x = e t ∧ ∀ y, pairW w w' (y+x) = pairW w w' y := by
    let A := t*F
    let B := pack T * A.toCols₁
    let C := pack T * A.toCols₂
    have hu (G : Mat (Fin n) I) : colSp (pack T * G) ≤ T := by
      rintro x ⟨y,rfl⟩
      change (pack T * G) *ᵥ y ∈ T
      rw [← Matrix.mulVec_mulVec]
      have hg : pack T *ᵥ (G *ᵥ y) ∈ colSp (pack T) := ⟨G *ᵥ y,rfl⟩
      rwa [colSp_pack] at hg
    refine ⟨(B,C),?_,fun y => ?_⟩
    · have hx : fromCols A.toCols₁ A.toCols₂ = A := by ext i j; cases j <;> rfl
      change fromCols (pack T * A.toCols₁) _ * D = _
      rw [show C = pack T * A.toCols₂ from rfl,← Matrix.mul_fromCols,hx]
      change _ * _ = pack T * t
      unfold A
      rw [Matrix.mul_assoc,Matrix.mul_assoc,hF,Matrix.mul_one]
    · change w (y.1+B) * w' (y.2+C) = _
      rw [hT _ _ (hu _),hT' _ _ (hu _)]
      rfl
  have h := translate_cap (subLaw_pair hw hw') f e he M
  rw [card_space,dim_mat] at h
  refine le_trans h (le_of_eq ?_)
  have ht : (↑(Fintype.card (Fin n) * Fintype.card J) : ℝ) = (dim T:ℝ) * num J := by
    simp [num,n]
  rw [ht,neg_mul,bp_neg]

omit [DecidableEq I] [DecidableEq U] in
theorem kerTr_dim {P : Mat U I} (h : Injective P.mulVec) :
    (dim (ker Pᵀ.mulVecLin) : ℝ) = num U - num I := by
  have hx := Pᵀ.mulVecLin.finrank_range_add_finrank_ker
  change rk Pᵀ.mulVecLin + dim (ker Pᵀ.mulVecLin) = dim (Vec U) at hx
  rw [rk_surj.mp (show Surjective Pᵀ.mulVecLin from transpose_surj_iff.mpr h), dim_vec,
    dim_vec] at hx
  have hj : num I + dim (ker Pᵀ.mulVecLin) = num U := by exact_mod_cast hx
  linarith only [hj]

omit [DecidableEq I] [DecidableEq U] in
theorem two_kerTr {P Q : Mat U I} (h : Injective P.mulVec) (g : Injective Q.mulVec) :
    num U - 2*num I ≤ (dim (ker Pᵀ.mulVecLin ⊓ ker Qᵀ.mulVecLin : Submodule _ _) : ℝ) := by
  let A := ker Pᵀ.mulVecLin
  let B := ker Qᵀ.mulVecLin
  have he : (dim (A⊔B : Submodule _ _) : ℝ)+dim (A⊓B : Submodule _ _) = dim A + (dim B:ℝ) := by
    exact_mod_cast Submodule.finrank_sup_add_finrank_inf_eq A B
  have hf : (dim (A⊔B : Submodule _ _) : ℝ) ≤ num U := by
    have hh := Submodule.finrank_le (A ⊔ B)
    change dim _ ≤ dim _ at hh
    rw [dim_vec] at hh; exact_mod_cast hh
  change _ ≤ (dim (A⊓B : Submodule _ _) : ℝ)
  rw [show (dim A:ℝ) = _ from kerTr_dim h,show (dim B:ℝ) = _ from kerTr_dim g] at he
  linarith only [he,hf]

def weakMinus (C : Mat I I → Prop) (P : Mat U I) := unifOn (fun Q : Mat U I => C (Pᵀ*Q))

theorem weak_shift {C : Mat I I → Prop} (P : Mat U I) :
    columnInv (w:=weakMinus C P) (ker Pᵀ.mulVecLin) := by
  intro M A hA
  have h : Pᵀ * A = 0 := by
    apply coe_mv_inj
    change (Pᵀ * A).mulVecLin = _
    rw [mulVecLin_mul]
    exact LinearMap.ext fun x => by
      have hh : Pᵀ.mulVecLin (A.mulVecLin x)=0 := hA (show A.mulVecLin x ∈ colSp A from ⟨x,rfl⟩)
      simp only [LinearMap.comp_apply,hh,Matrix.mulVecLin_zero,LinearMap.zero_apply]
  simp only [weakMinus,unifOn_val,Matrix.mul_add,h,add_zero]

theorem minus_le_weak {C : Mat I I → Prop} (hc : ∃ M, C M) (P : Mat U I)
    (hP : Injective P.mulVec) (hu : 2*num I - num U ≤ -1) (x : Mat U I) :
    unifOn (fun Q => FramesAt C (P,Q)) x ≤ 2 * weakMinus C P x := by
  let w := weakMinus C P
  have hh : IsLaw w := by
    refine unifOn_law ?_
    obtain ⟨M,hM⟩ := hc
    obtain ⟨B,hB⟩ := gramL_surj I hP M
    change Pᵀ*B=M at hB
    exact ⟨B,hB.symm ▸ hM⟩
  have hg : pr w (fun M => ¬Injective M.mulVec) ≤ (2:ℝ)⁻¹ := by
    apply le_trans (shift_fail hh.sub _ (weak_shift P))
    rw [kerTr_dim hP,show (2:ℝ)⁻¹=bp (-1) by rw [bp_neg,bp_one]]
    exact bp_le (by linarith only [hu])
  rw [pr_not w (p:=fun M => Injective M.mulVec),hh.total] at hg
  have h1 := on_mon hh.nz (p:=fun M => Injective M.mulVec) (a:= (2:ℝ)⁻¹)
    (by norm_num) (by linarith only [hg]) x
  simp only [w,weakMinus,unifOn_and,inv_inv] at h1
  simpa only [FramesAt,hP,true_and,weakMinus] using h1

theorem plus_le_unif (hu : num I-num U ≤ -1) (P : Mat U I) :
    unifOn (fun P : Mat U I => Injective P.mulVec) P ≤ 2 * unif P := by
  have h : pr unif (fun P : Mat U I => ¬ Injective P.mulVec) ≤ (2:ℝ)⁻¹ := by
    apply le_trans unif_fail
    rw [show (2:ℝ)⁻¹=bp (-1) by rw [bp_neg,bp_one]]; exact bp_le hu
  rw [pr_not (unif:Wgt (Mat U I)) (p:=fun P => Injective P.mulVec),unif_law.total] at h
  have h1 := on_mon unif_law.nz (a:=(2:ℝ)⁻¹)
    (p:=fun P : Mat U I => Injective P.mulVec) (by norm_num) (by linarith only [h]) P
  rwa [on_unif,inv_inv] at h1

private theorem pair_cap_aux {A : Type} {w v w' v' : Wgt A}
    (hu : ∀ x, 0 ≤ w' x) (hg : ∀ x, 0 ≤ v x) (hc : ∀ x, w x ≤ 2*v x)
    (hd : ∀ x, w' x ≤ 2*v' x) (p) : pairW w w' p ≤ 4 * pairW v v' p := by
  refine (mul_le_mul (hc p.1) (hd p.2) (hu _) (mul_nonneg (by norm_num) (hg _))).trans_eq ?_
  rw [pairW]; ring

theorem comp_image_cap {C : Mat I I → Prop} (hc : ∃ M, C M)
    (hu : 2*num I-num U ≤ -1)
    (D : Mat (I⊕I) J) (D' : Mat (I⊕I) S)
    (hD : Injective D.mulVec) (hD' : Injective D'.mulVec)
    (M : Mat U J) (M' : Mat U S) :
    let w := unifOn (FramesAt (U:=U) C)
    pr (pairW w w) (fun x =>
      mixImage D (x.1.1,x.2.1) = M ∧ mixImage D' (x.1.2,x.2.2)=M') ≤
        16*bp (-num U * num J - (num U-2*num I)*num S) := by
  let Y (x : Mat U I) := Injective x.mulVec
  let w := unifOn (FramesAt (U:=U) C)
  let v := unifOn Y
  let k (x : Mat U I) := unifOn (fun Q => FramesAt C (x,Q))
  have h₀ : num I - num U ≤ -1 := by
    have hi : 0 ≤ num I := Nat.cast_nonneg _
    linarith
  have hh := framesAt_exists (U:=U) hc (show num I+num I<num U by linarith only [hu])
  have hw : w = semi v k := by
    funext x
    rcases x with ⟨x,y⟩
    rw [show w (x,y) = _ from unifOn_slice _ x y,plus_marginal hh]; rfl
  let p := fun x => mixImage D x=M
  let q := fun x => mixImage D' x=M'
  let b1 := bp (-num U * num J)
  let b2 := bp (- (num U-2*num I)*num S)
  change pr (pairW w w) _ ≤ _
  rw [hw,pair_semi_pr v v k k p q]
  have he1 : pr (pairW v v) p ≤ 4*b1 := by
    have hi := pr_cap (w:=pairW v v)
      (pair_cap_aux (unifOn_sub Y).nz unif_subLaw.nz (plus_le_unif h₀) (plus_le_unif h₀)) p
    refine hi.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    refine (mixed_cap unif_subLaw unif_subLaw ⊤ (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      _ hD _).trans ?_
    dsimp only [b1]
    rw [dim,finrank_top,show Module.finrank F (Vec U)=_ from dim_vec _]
  have he2 (P P' : Mat U I) :
      pr (pairW (k P) (k P')) q ≤ 4*b2 := by
    by_cases h : Y P
    · by_cases g : Y P'
      · let T := ker Pᵀ.mulVecLin ⊓ ker P'ᵀ.mulVecLin
        have hh : columnInv (w:=weakMinus C P) T :=
          fun M A hA => weak_shift P _ _ (hA.trans inf_le_left)
        have hh' : columnInv (w:=weakMinus C P') T :=
          fun M A hA => weak_shift P' _ _ (hA.trans inf_le_right)
        have hi := pr_cap (w:=pairW (k P) (k P'))
          (pair_cap_aux (unifOn_sub _).nz (v:=weakMinus C P) (unifOn_sub _).nz
            (minus_le_weak hc P h hu) (minus_le_weak hc P' g hu)) q
        refine hi.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
        refine (mixed_cap (unifOn_sub _) (unifOn_sub _) T hh hh' _ hD' M').trans (bp_le ?_)
        apply mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact neg_le_neg (two_kerTr h g)
      · have hi := bp_pos (- (num U-2*num I)*num S)
        change ¬ Injective _ at g
        simp [pr,avg,pairW,k,FramesAt,g,unifOn_val,b2]; exact (bp_pos _).le
    · have hi := bp_pos (- (num U-2*num I)*num S)
      change ¬ Injective _ at h
      simp [pr,avg,pairW,k,FramesAt,h,unifOn_val,b2]; exact (bp_pos _).le
  let r := pairW v v
  calc avg r (fun x => ind (p x)*pr (pairW (k x.1) (k x.2)) q)
    _ ≤ avg r (fun x => ind (p x)*(4*b2)) :=
        avg_mono (subLaw_pair (unifOn_sub _) (unifOn_sub Y)).nz
          (fun x => mul_le_mul_of_nonneg_left (he2 _ _) (ind_nonneg _))
    _ = pr r p * (4*b2) := avg_mul _ _ _
    _ ≤ (4*b1)*(4*b2) := mul_le_mul_of_nonneg_right he1 (mul_nonneg (by norm_num) (bp_pos _).le)
    _ = _ := by simp only [sub_eq_add_neg,← neg_mul, bp_add,b1,b2]; ring

end HadwigerCounterexample

end

end OAI
