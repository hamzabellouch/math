import OAI.Combinatorics.HadwigerCounterexample.IndependentPhaseBounds

namespace OAI

/-! # Offset Lifting -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Submodule Module Finset Function
variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

omit [Fintype I] in
theorem col_follow (A : Mat I J) (B : Mat J K) :
    colSp (A*B)≤colSp A := by
  rw [colSp,Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range ..

omit [Fintype I] in
theorem col_retain {A : Mat I J} {B : Mat J K} (h : Surjective B.mulVec) :
    colSp (A*B)=colSp A := by
  rw [colSp,Matrix.mulVecLin_mul,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (show Surjective B.mulVecLin from h),Submodule.map_top,colSp]

private theorem trans_surj {A : Mat I J} (hA : Surjective A.mulVec) : Injective Aᵀ.mulVec :=
  transpose_surj_iff.mp (by rwa [Matrix.transpose_transpose])

omit [Fintype I] in
theorem pull_cols (A : Mat I J) (B : Mat I K) (h : colSp B≤colSp A) :
    ∃ Q : Mat J K,A*Q=B := by
  classical
  have hf (i : K) : B.col i ∈ colSp A := h (colSp_mem i)
  choose v hv using show ∀ (i:K),∃ v : Vec J,A *ᵥ v = B.col i from hf
  refine ⟨Matrix.of (fun i j => v j i),?_⟩
  ext i j
  exact congr_fun (hv j) i

variable [DecidableEq I]

theorem chop_inj_pack {S : Space (Vec I)} {T : Mat I J} (h : Injective T.mulVec)
    (he : Disjoint S (colSp T)) :
    Injective (chop S*T).mulVec := by
  rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  rw [← Matrix.mulVec_mulVec] at hx
  have hh : T *ᵥ x∈S⊓colSp T := ⟨(chop_ker ..).mp hx,⟨_,rfl⟩⟩
  rw [he.eq_bot,Submodule.mem_bot] at hh
  exact h (hh.trans (Matrix.mulVec_zero T).symm)

private theorem frame_image_lift {S T : Space (Vec I)} {A : Mat I J}
    (h : colSp A≤chopSpace S T) :
    ∃ A' : Mat I J,colSp A'≤T ∧ chop S * A'=A := by
  classical
  have hf : chopSpace S T=colSp (chop S*pack T) := by
    rw [chopSpace,colSp,Matrix.mulVecLin_mul,LinearMap.range_comp,
      show LinearMap.range (pack T).mulVecLin=_ from colSp_pack T]
  obtain ⟨V,hV⟩ := pull_cols (chop S*pack T) A (hf ▸ h)
  refine ⟨pack T*V,(col_follow ..).trans_eq (colSp_pack T),?_⟩
  rw [←Matrix.mul_assoc,hV]

private theorem projected_unique {M V : Space (Vec I)} {M' V' : Space (Vec I)}
    (h : Disjoint M M') (h' : Disjoint V V') (A B : Mat I I)
    (hA : A∈ box M' V') (hB : B∈box M' V')
    (hf : liftM (chop M) (chop V) A=liftM (chop M) (chop V) B) :
    A=B := by
  classical
  obtain ⟨A,rfl⟩ := hA
  obtain ⟨B,rfl⟩ := hB
  have he := chop_inj_pack (S:=M) (pack_inj M') (by rw [colSp_pack]; exact h)
  have he' := chop_inj_pack (S:=V) (pack_inj V') (by rw [colSp_pack]; exact h')
  rw [liftM_comp,liftM_comp] at hf
  rw [liftM_inj he he' hf]

structure FrameProduct (M : Mat I I) (S T : Space (Vec I)) (X Y : Mat I J) : Prop where
  xin : Injective X.mulVec
  yin : Injective Y.mulVec
  xcol : colSp X ≤ S
  ycol : colSp Y ≤ T
  prod : X*Yᵀ=M

private theorem frame_extend (M : Mat I I) (S T V W : Space (Vec I)) (A B : Mat I K)
    (hV : M ∈ box V W)
    (hx : Disjoint S V) (hy : Disjoint T W)
    (hA : Injective A.mulVec) (hB : Injective B.mulVec)
    (he : liftM (chop S) (chop T) M=A*Bᵀ) :
    ∃ X Y : Mat I K,
      FrameProduct M V W X Y ∧ chop S*X=A ∧ chop T*Y=B := by
  classical
  have heq : A*Bᵀ ∈box (chopSpace S V) (chopSpace T W) := he ▸ lift_mem_box _ _ hV
  obtain ⟨hL,hH⟩ := (box_mem ..).mp heq
  rw [col_retain (transpose_surj_iff.mpr hB)] at hL
  rw [Matrix.transpose_mul,Matrix.transpose_transpose,col_retain (transpose_surj_iff.mpr hA)] at hH
  obtain ⟨X,hX,hZ⟩ := frame_image_lift hL
  obtain ⟨Y,hY,hU⟩ := frame_image_lift hH
  have hi {A B : Mat I K} (f : Mat I I)
      (h : f*A=B) (hB : Injective B.mulVec) : Injective A.mulVec := by
    rw [←h] at hB
    intro x y he
    apply hB
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,he]
  refine ⟨X,Y,⟨hi _ hZ hA,hi _ hU hB,hX,hY,?_⟩,hZ,hU⟩
  refine projected_unique hx hy _ _ ((box_mem ..).mpr ⟨(col_follow ..).trans hX,?_⟩) hV ?_
  · rw [Matrix.transpose_mul,Matrix.transpose_transpose]
    exact (col_follow ..).trans hY
  rw [he,liftM_def,←hU,←hZ,Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

private theorem frame_products (M : Bool → Mat I I) (S T : Space (Vec I))
    (a b : Bool → Space (Vec I))
    (h : ∀ i,M i∈box (a i) (b i)) (hg : vanish S T (M true+M false))
    (ha : ∀ i,Disjoint S (a i)) (hb : ∀ i,Disjoint T (b i)) :
    ∃ X Y : Bool → Mat I (Fin (M true).rank), (∀ i,FrameProduct (M i) (a i) (b i) (X i) (Y i)) ∧
      chop S*X true=chop S*X false ∧ chop T*Y true=chop T*Y false := by
  classical
  obtain ⟨A,B,hA,hB,hM⟩ := rank_product (M true)
  let C := Bᵀ
  have hC : Injective C.mulVec := trans_surj hB
  obtain ⟨hL,hR⟩ := (box_mem ..).mp (h true)
  rw [← hM,col_retain hB] at hL
  rw [←hM,Matrix.transpose_mul,col_retain (transpose_surj_iff.mpr hA)] at hR
  have hf : liftM (chop S) (chop T) (M true)= (chop S*A)*(chop T*C)ᵀ := by
    rw [liftM_def,Matrix.transpose_mul, show Cᵀ=B from rfl,Matrix.mul_assoc,Matrix.mul_assoc (chop S),← Matrix.mul_assoc A,
      hM]
  obtain ⟨P,Q,hP,hQ,hF⟩ := frame_extend (M false) S T (a false) (b false)
    (chop S*A) (chop T*C) (h false) (ha false) (hb false)
    (chop_inj_pack hA (Disjoint.mono_right hL (ha true)))
    (chop_inj_pack hC (Disjoint.mono_right hR (hb true))) (by
      have he := (vanish_chop _).mp hg
      rw [map_add] at he
      rw [←hf]
      exact add_left_cancel (he.trans (char_two _).symm))
  refine ⟨onSide (A,P), onSide (C,Q),fun i => ?_,hQ.symm,hF.symm⟩
  cases i
  · exact hP
  exact ⟨hA,hC,hL,hR,hM⟩

private theorem diff_into (a : Bool → Mat I J) (S : Space (Vec I))
    (h : chop S*a true=chop S*a false) :
    ∃ (k : ℕ) (P : Mat (Fin (dim S)) (Fin k)) (B : Mat (Fin k) J),
      k≤Fintype.card J ∧ Injective (pack S * P).mulVec ∧ Surjective B.mulVec ∧
      a true+a false=(pack S*P)*B := by
  classical
  let X := a true+a false
  obtain ⟨A,B,hA,hB,hX⟩ := rank_product X
  have hi : colSp X≤S := by
    rintro x ⟨y,rfl⟩
    apply (chop_ker ..).mp
    rw [mulVecLin_apply,Matrix.mulVec_mulVec,show X=_+_ from rfl,Matrix.mul_add,h,char_two,
      Matrix.zero_mulVec]
  obtain ⟨P,hP⟩ := pull_cols (pack S) A (by rw [← col_retain hB,hX,colSp_pack]; exact hi)
  refine ⟨X.rank,P,B,X.rank_le_card_width,?_,hB,?_⟩
  · rw [hP]; exact hA
  rw [hP,hX]

/-- δ expansion at one component: S*T offsets bases plus paired
companions Z for either reference endpoint. Cost recorded in actual
offset widths kp/km and kernel matrices. -/
theorem one_offsets (M : Bool → Mat I I) (S T : Space (Vec I))
    (a b : Bool → Space (Vec I))
    (h : ∀ i,M i∈box (a i) (b i)) (hg : vanish S T (M true+M false))
    (ha : ∀ i,Disjoint S (a i)) (hb : ∀ i,Disjoint T (b i)) :
    ∃ (kp km : ℕ) (A : Mat (Fin (dim S)) (Fin kp)) (B : Mat (Fin (dim T)) (Fin km))
      (H : Mat (Fin kp) (Fin km)),
      let X := pack S * A
      let Y := pack T * B
      kp≤(M true).rank ∧ km≤ (M true).rank ∧ Injective X.mulVec ∧ Injective Y.mulVec ∧
      ∀ i,∃ (Z : Mat I (Fin kp)) (W : Mat I (Fin km)), Injective Z.mulVec ∧ Injective W.mulVec ∧
        colSp Z≤ b i ∧ colSp W≤ a i ∧ M true+M false=X*Zᵀ+W*Yᵀ+X*H*Yᵀ := by
  classical
  obtain ⟨P,Q,hP,hQ,hF⟩ := frame_products M S T a b h hg ha hb
  obtain ⟨k,A,E,hk,hA,hE,hX⟩ := diff_into P S hQ
  obtain ⟨k',B,D,hk',hB,hD,hY⟩ := diff_into Q T hF
  rw [Fintype.card_fin] at hk hk'
  let X := pack S * A
  let Y := pack T * B
  refine ⟨k,k',A,B,E*Dᵀ,hk,hk',hA,hB,fun i => ?_⟩
  let V := P i
  let U := Q i
  have ht : M true+M false=M i+M (!i) := by cases i; exact add_comm _ _; rfl
  have hx : P (!i) = V+X*E := by
    rw [show X*E=P true+P false from hX.symm]
    cases i
    · change P true=P false+(P true+P false); rw [add_left_comm,char_two,add_zero]
    · change P false=P true+(P true+P false); rw [←add_assoc,char_two,zero_add]
  have hy : Q (!i)=U+Y*D := by
    rw [show Y*D=Q true+Q false from hY.symm]
    cases i
    · change Q true=Q false+(Q true+Q false); rw [add_left_comm,char_two,add_zero]
    · change Q false=Q true+(Q true+Q false); rw [←add_assoc,char_two,zero_add]
  refine ⟨U*Eᵀ,V*Dᵀ,inj_comp_mat _ _ (hP i).yin (trans_surj hE),
    inj_comp_mat _ _ (hP i).xin (trans_surj hD), (col_follow ..).trans (hP i).ycol,
    (col_follow ..).trans (hP i).xcol,?_⟩

  have hm :
      M true+M false=V*Uᵀ+(V+X*E)*(U+Y*D)ᵀ := ht.trans (congrArg₂ (· + ·)
    (hP i).prod.symm ((hP (!i)).prod.symm.trans (congrArg₂ (· * ·) hx
      (congrArg Matrix.transpose hy))))
  apply hm.trans
  change _=X * _ + _ * Yᵀ+ X * _ * Yᵀ
  simp only [transpose_add,transpose_mul,transpose_transpose,Matrix.add_mul,Matrix.mul_add,
    Matrix.mul_assoc,add_assoc]
  calc _ = (V*Uᵀ + V*Uᵀ) + (X * (E * Uᵀ) + (V * (Dᵀ*Yᵀ) + X * (E * (Dᵀ*Yᵀ)))) := by abel
       _ = _ := by rw [char_two,zero_add]

end HadwigerCounterexample

end

end OAI
