import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalCoproductUnits

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def centerPower (a : I → I → ℕ) (T : SplitTree I) (φ : ℤ → ℕ) :
    MvPolynomial T.Centers ℚ :=
  ∏ ij∈T.centerPairs,diagonal ij.1 ij.2 ^ φ (eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2))

noncomputable def crossPower (a : I → I → ℕ) (L R : SplitTree I) (φ : ℤ → ℕ) :
    MvPolynomial (L.node R).Centers ℚ :=
  ∏ z : L.Centers,∏ t : R.Centers,
    diagonal (Sum.inl z) (Sum.inr t)^φ (eulerForm a (L.leafDimension z) (R.leafDimension t))

noncomputable def crossSign (a : I → I → ℕ) (L R : SplitTree I) (φ : ℤ → ℕ) : ℚ :=
  ∏ z : L.Centers,∏ t : R.Centers,(-1)^φ (eulerForm a (L.leafDimension z) (R.leafDimension t))

omit [DecidableEq I] in
lemma centerPower_node (a : I → I → ℕ) (L R : SplitTree I) (φ : ℤ → ℕ) :
    centerPower a (L.node R) φ = rename Sum.inl (centerPower a L φ)*
      rename Sum.inr (centerPower a R φ)*crossPower a L R φ := by
  unfold centerPower
  rw [centerPairs_prod_node]
  simp only [crossPairs,Finset.prod_image (fun p _ q _ h=>crossPairs_injective L R h),
    Fintype.prod_prod_type,map_prod,map_pow,diagonal,map_sub,rename_X,leafDimension,crossPower]

omit [DecidableEq I] in
lemma crossPower_swap (a : I → I → ℕ) (L R : SplitTree I) (φ : ℤ → ℕ)
    (hs : ∀ z t,eulerForm a (L.leafDimension z) (R.leafDimension t)=
      eulerForm a (R.leafDimension t) (L.leafDimension z)) :
    rename (Equiv.sumComm L.Centers R.Centers) (crossPower a L R φ)=
      C (crossSign a L R φ)*crossPower a R L φ := by
  classical
  unfold crossPower crossSign
  simp only [map_prod,map_pow,diagonal,map_sub,rename_X,Equiv.sumComm_apply,
    Sum.swap_inl,Sum.swap_inr]
  rw [Finset.prod_comm (f:=fun (t : R.Centers) (z : L.Centers)=>
    (X (Sum.inr z)-X (Sum.inl t))^φ (eulerForm a (R.leafDimension t) (L.leafDimension z))),
    ←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro z hz
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t ht
  rw [hs z t,←mul_pow]
  congr 1
  simp only [map_neg,map_one]
  ring

omit [DecidableEq I] in
lemma centerPower_swap (a : I → I → ℕ) (L R : SplitTree I) (φ : ℤ → ℕ)
    (hs : ∀ z t,eulerForm a (L.leafDimension z) (R.leafDimension t)=
      eulerForm a (R.leafDimension t) (L.leafDimension z)) :
    rename (Equiv.sumComm L.Centers R.Centers) (centerPower a (L.node R) φ)=
      C (crossSign a L R φ)*centerPower a (R.node L) φ := by
  rw [centerPower_node,centerPower_node,map_mul,map_mul,crossPower_swap a L R φ hs]
  simp only [rename_rename,Equiv.sumComm_apply,Function.comp_def,Sum.swap_inl,Sum.swap_inr]
  ring

omit [DecidableEq I] in
lemma crossSign_sq (a : I → I → ℕ) (L R : SplitTree I) (φ : ℤ → ℕ) :
    crossSign a L R φ*crossSign a L R φ=1 := by
  unfold crossSign
  rw [←Finset.prod_mul_distrib]
  simp only [←Finset.prod_mul_distrib,←mul_pow,neg_mul_neg,one_mul,one_pow,Finset.prod_const_one]

omit [DecidableEq I] in
lemma sum_leaf_euler_left (a : I → I → ℕ) (L : SplitTree I) (d : I → ℕ) :
    (∑ z : L.Centers,eulerForm a (L.leafDimension z) d)=eulerForm a L.dim d := by
  classical
  induction L with
  | leaf d => simp [Centers,leafDimension,dim]
  | node T U hT hU =>
    change (∑ z : T.Centers ⊕ U.Centers,eulerForm a ((T.node U).leafDimension z) d)=_
    rw [Fintype.sum_sum_type]
    change (∑ z : T.Centers,eulerForm a (T.leafDimension z) d)+
      (∑ z : U.Centers,eulerForm a (U.leafDimension z) d)=eulerForm a (T.dim+U.dim) d
    rw [hT,hU,eulerForm_add_left]

omit [DecidableEq I] in
lemma sum_leaf_euler_right (a : I → I → ℕ) (d : I → ℕ) (R : SplitTree I) :
    (∑ z : R.Centers,eulerForm a d (R.leafDimension z))=eulerForm a d R.dim := by
  classical
  induction R with
  | leaf d => simp [Centers,leafDimension,dim]
  | node T U hT hU =>
    change (∑ z : T.Centers ⊕ U.Centers,eulerForm a d ((T.node U).leafDimension z))=_
    rw [Fintype.sum_sum_type]
    change (∑ z : T.Centers,eulerForm a d (T.leafDimension z))+
      (∑ z : U.Centers,eulerForm a d (U.leafDimension z))=eulerForm a d (T.dim+U.dim)
    rw [hT,hU,eulerForm_add_right]

lemma negOne_pos_neg (e : ℤ) : (-1:ℚ)^e.toNat*(-1)^(-e).toNat=(-1)^e := by
  cases e with
  | ofNat n => simp
  | negSucc n =>
    have h : Int.negSucc n = -((n+1:ℕ):ℤ) := by omega
    have h0 : (-((n+1:ℕ):ℤ)).toNat=0 := Int.toNat_eq_zero.mpr (by omega)
    rw [h,h0,pow_zero,one_mul,neg_neg,Int.toNat_natCast,zpow_neg,zpow_natCast]
    simp only [←inv_pow,inv_neg,inv_one]

lemma prod_negOne {α : Type*} (s : Finset α) (f : α → ℤ) :
    (∏ i∈s,(-1:ℚ)^f i)=(-1)^(∑ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx,Finset.sum_insert hx,ih,zpow_add₀ (by norm_num : (-1:ℚ)≠0)]

omit [DecidableEq I] in
lemma crossSign_pos_neg (a : I → I → ℕ) (L R : SplitTree I) :
    crossSign a L R Int.toNat*crossSign a L R (fun e=>(-e).toNat)=
      (-1:ℚ)^eulerForm a L.dim R.dim := by
  unfold crossSign
  rw [←Finset.prod_mul_distrib]
  simp only [←Finset.prod_mul_distrib,negOne_pos_neg,prod_negOne,
    sum_leaf_euler_right,sum_leaf_euler_left]

namespace Regroup
lemma clearedLeading_swap (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (f : sourceFiltration a c η hc θ (L.node R).dim W) :
    clearedLeading a c η hc θ (.node R L) ⟨hR,hL⟩
        (pairSymmetric_of_slope a c η θ hχ _ ⟨hR,hL⟩) W
        (filtrationDimensionEquiv a c η hc θ (Regroup.swap L R).dimension W f)=
      crossSign a L R (fun e=>(-e).toNat) •
        extendPolynomial ((Regroup.swap L R).equivalence
          (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
          (Regroup.swap L R).centers
          (clearedLeading a c η hc θ (.node L R) ⟨hL,hR⟩
            (pairSymmetric_of_slope a c η θ hχ _ ⟨hL,hR⟩) W f) := by
  have hs (z : L.Centers) (t : R.Centers) :
      eulerForm a (L.leafDimension z) (R.leafDimension t)=
        eulerForm a (R.leafDimension t) (L.leafDimension z) := by
    obtain ⟨hz,hzs⟩:=L.leafDimension_onSlope c η θ hL z
    obtain ⟨ht,hts⟩:=R.leafDimension_onSlope c η θ hR t
    exact hχ _ _ hz ht hzs hts
  have hd : rename (Regroup.swap L R).centers
      (centerDenominator a (L.node R) (L.node R).centerPairs)=
      C (crossSign a L R (fun e=>(-e).toNat))*
        centerDenominator a (R.node L) (R.node L).centerPairs :=
    centerPower_swap a L R (fun e=>(-e).toNat) hs
  apply scalar_mul_injective _ (centerDenominator_ne_zero a (R.node L))
  dsimp only
  rw [denominator_clearedLeading a c η hc θ (R.node L) ⟨hR,hL⟩
      (pairSymmetric_of_slope a c η θ hχ _ ⟨hR,hL⟩) W,
    filtrationDimensionEquiv_val,
    totalLeadingPolynomial_natural a c η hc θ (Regroup.swap L R) ⟨hL,hR⟩ ⟨hR,hL⟩ W,
    ←denominator_clearedLeading a c η hc θ (L.node R) ⟨hL,hR⟩
      (pairSymmetric_of_slope a c η θ hχ _ ⟨hL,hR⟩) W f,
    map_mul,extendPolynomial_map_algebra,hd,map_mul,map_C]
  rw [Algebra.smul_def]
  simp only [MvPolynomial.algebraMap_apply]
  ring

lemma normalizedSymbol_swap (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (f : sourceFiltration a c η hc θ (L.node R).dim W) :
    normalizedSymbol a c η hc θ (.node R L) ⟨hR,hL⟩
        (pairSymmetric_of_slope a c η θ hχ _ ⟨hR,hL⟩) W
        (filtrationDimensionEquiv a c η hc θ (Regroup.swap L R).dimension W f)=
      (-1:ℚ)^eulerForm a L.dim R.dim •
        extendPolynomial ((Regroup.swap L R).equivalence
          (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
          (Regroup.swap L R).centers
          (normalizedSymbol a c η hc θ (.node L R) ⟨hL,hR⟩
            (pairSymmetric_of_slope a c η θ hχ _ ⟨hL,hR⟩) W f) := by
  have hs (z : L.Centers) (t : R.Centers) :
      eulerForm a (L.leafDimension z) (R.leafDimension t)=
        eulerForm a (R.leafDimension t) (L.leafDimension z) := by
    obtain ⟨hz,hzs⟩:=L.leafDimension_onSlope c η θ hL z
    obtain ⟨ht,hts⟩:=R.leafDimension_onSlope c η θ hR t
    exact hχ _ _ hz ht hzs hts
  have hn : rename (Regroup.swap L R).centers
      (centerNumerator a (L.node R) (L.node R).centerPairs)=
      C (crossSign a L R Int.toNat)*centerNumerator a (R.node L) (R.node L).centerPairs :=
    centerPower_swap a L R Int.toNat hs
  have hsign : (-1:ℚ)^eulerForm a L.dim R.dim*crossSign a L R Int.toNat=
      crossSign a L R (fun e=>(-e).toNat) := by
    rw [←crossSign_pos_neg]
    calc
      _ = (crossSign a L R Int.toNat*crossSign a L R Int.toNat)*
        crossSign a L R (fun e=>(-e).toNat) := by ring
      _ = _ := by rw [crossSign_sq,one_mul]
  change map _ (centerNumerator a (R.node L) (R.node L).centerPairs)*
    clearedLeading a c η hc θ (.node R L) ⟨hR,hL⟩
      (pairSymmetric_of_slope a c η θ hχ _ ⟨hR,hL⟩) W _ =
    (-1:ℚ)^eulerForm a L.dim R.dim •
    extendPolynomial _ _ (map _ (centerNumerator a (L.node R) (L.node R).centerPairs)*
      clearedLeading a c η hc θ (.node L R) ⟨hL,hR⟩
        (pairSymmetric_of_slope a c η θ hχ _ ⟨hL,hR⟩) W f)
  rw [clearedLeading_swap a c η hc θ hχ L R hL hR W f,
    map_mul,extendPolynomial_map_algebra,hn,map_mul,map_C]
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_apply]
  have hh:=congrArg (fun r : ℚ =>
    (C ((algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node R L))) r) :
      MvPolynomial (R.node L).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node R L)))) hsign
  simp only [map_mul] at hh
  rw [←hh]
  ring

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
