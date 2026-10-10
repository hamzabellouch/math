import OAI.Analysis.InterpolatedFactors.ScalarGeneration

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace FreeGroupFactorMain.GaussianRecognition.System
variable {A : Type u_1} {E : Type u_2} {I : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

theorem normal_mem_of_generator_invariant (σ : I → I) (K : Submodule ℂ E)
    (hroot : X.root∈K) (hcoeff : ∀ a ξ,ξ∈K → X.coeff a ξ∈K)
    (hgen : ∀ i ξ,ξ∈K → X.generator σ i ξ∈K) (a : A) (w : List (I×A)) : X.normal a w∈K := by
  have main : ∀ n : ℕ,∀ w : List (I×A),w.length=n → ∀ a : A,X.normal a w∈K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn a
      cases w with
      | nil => simpa only [normal] using hcoeff a X.root hroot
      | cons q w =>
        rcases q with ⟨i,b⟩
        subst n
        have ht := ih w.length (by simp) w rfl b
        have ha : star (X.create (σ i)) (X.normal b w)∈K := by
          cases w with
          | nil => rw [X.annihilate_normal_nil];exact K.zero_mem
          | cons q w =>
            rcases q with ⟨j,c⟩
            rw [X.annihilate_normal_cons]
            exact ih w.length (by simp) w rfl _
        have hh := K.sub_mem (hgen i (X.normal b w) ht) ha
        have he : X.generator σ i (X.normal b w)-star (X.create (σ i)) (X.normal b w)=
            X.create i (X.normal b w) := by simp only [generator,add_apply,add_sub_cancel_right]
        rw [he] at hh
        exact hcoeff a _ hh
  exact main w.length w rfl a

theorem normalHull_le_of_generator_invariant (σ : I → I) (K : Submodule ℂ E)
    (hK : IsClosed (K : Set E)) (hroot : X.root∈K)
    (hcoeff : ∀ a ξ,ξ∈K → X.coeff a ξ∈K)
    (hgen : ∀ i ξ,ξ∈K → X.generator σ i ξ∈K) : X.normalHull≤K := by
  apply Submodule.topologicalClosure_minimal _ ?_ hK
  apply Submodule.span_le.mpr
  rintro ξ ⟨⟨a,w⟩,rfl⟩
  exact X.normal_mem_of_generator_invariant σ K hroot hcoeff hgen a w
end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification GaussianRecognition
variable {ι : Type u_4} [DecidableEq ι]

theorem P_range_apply (ξ : PRange ι) : P (ξ:H ι)=(ξ:H ι) := by
  obtain ⟨η,hη⟩ := ξ.property
  rw [← hη]
  exact DFunLike.congr_fun (projection_P (ι := ι)).isIdempotentElem.eq η

def pRight : PRange ι →L[ℂ] PRange ι := pRepresentation (pSandwich rightP)

theorem pRight_apply (ξ : PRange ι) : (pRight ξ : H ι)=rightP (ξ:H ι) := by
  rw [pRight,pRepresentation_apply]
  change P (rightP (P (ξ:H ι)))=rightP (ξ:H ι)
  rw [P_range_apply]
  have h := DFunLike.congr_fun (P_commute_rightP (ι := ι)).eq (ξ:H ι)
  change P (rightP (ξ:H ι))=rightP (P (ξ:H ι)) at h
  rwa [P_range_apply] at h

theorem pRight_projection : IsStarProjection (pRight : PRange ι →L[ℂ] PRange ι) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro ξ
    apply Subtype.ext
    change (pRight (pRight ξ) : H ι)=(pRight ξ : H ι)
    simp only [pRight_apply]
    exact DFunLike.congr_fun (rightP_projection (ι := ι)).isIdempotentElem.eq (ξ:H ι)
  · have hs : star (pSandwich (rightP : Operator ι))=pSandwich rightP := by
      apply Subtype.ext
      change star (P*rightP*P : Operator ι)=P*rightP*P
      simp only [star_mul,projection_P.isSelfAdjoint.star_eq,rightP_projection.isSelfAdjoint.star_eq,mul_assoc]
    exact ((pRepresentation (ι := ι)).map_star' (pSandwich rightP)).symm.trans
      (congrArg (pRepresentation (ι := ι)) hs)

theorem pRight_root : (pRight : PRange ι →L[ℂ] PRange ι) pRoot=pRoot := by
  apply Subtype.ext
  rw [pRight_apply]
  change CoordinateProjection.proj _ (lp.single 2 ([],true) 1)=_
  simp only [CoordinateProjection.proj_single,Set.mem_ofPred_eq,ite_true]
  rfl

theorem pRight_commute_ambient (u v : ℝ) (T : representedAmbient u v) :
    Commute (pRight : PRange ℕ →L[ℂ] PRange ℕ) T.val := by
  let x := (pRepresentation (ι := ℕ)).symm T.val
  have hx : (x:Operator ℕ)∈ambientAlgebra u v := T.property
  have hc : Commute (x:Operator ℕ) rightP :=
    ((StarSubalgebra.mem_centralizer_iff ℂ).mp hx rightP (rightP_mem_commutant u v)).1.symm
  have hh : Commute (pRepresentation (pSandwich rightP)) (pRepresentation x) := by
    change _ * _ = _ * _
    simpa only [map_mul] using congrArg (fun X : PCorner ℕ => pRepresentation X)
      (pSandwich_commute rightP P_commute_rightP x hc).eq
  change Commute (pRepresentation (pSandwich rightP)) (pRepresentation ((pRepresentation (ι := ℕ)).symm T.val)) at hh
  rw [StarAlgEquiv.apply_symm_apply] at hh
  exact hh

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem weighted_normalHull_le_right :
    (weightedSystem u v hv hvu).normalHull≤(pRight : PRange ℕ →L[ℂ] PRange ℕ).range := by
  have hpres (T : representedAmbient u v) (ξ : PRange ℕ) (hξ : ξ∈(pRight : PRange ℕ →L[ℂ] PRange ℕ).range) :
      T.val ξ∈(pRight : PRange ℕ →L[ℂ] PRange ℕ).range := by
    obtain ⟨η,rfl⟩ := hξ
    exact ⟨T.val η,(DFunLike.congr_fun (pRight_commute_ambient u v T).eq η)⟩
  apply (weightedSystem u v hv hvu).normalHull_le_of_generator_invariant scalarFlip _
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range pRight_projection.isIdempotentElem)
    ⟨pRoot,pRight_root⟩
  · intro a ξ hξ
    exact hpres ⟨(weightedSystem u v hv hvu).coeff a,
      weighted_generated_le_ambient u v hv hvu (Bicommutant.subset _ (Or.inl (Set.mem_range_self a)))⟩ ξ hξ
  · intro i ξ hξ
    exact hpres ⟨(weightedSystem u v hv hvu).generator scalarFlip i,
      weighted_generated_le_ambient u v hv hvu (Bicommutant.subset _ (Or.inr (Set.mem_range_self i)))⟩ ξ hξ

theorem pRight_pSandwich_basis (w : Path ι) (B : Operator ι) (hB : B (vacuum u v)=lp.single 2 w 1)
    (hBc : Commute B rightP) :
    (u:ℂ) • pRepresentation (pSandwich B) pRoot=pRight (pProject (lp.single 2 w 1)) := by
  apply Subtype.ext
  change (u:ℂ) • (pRepresentation (pSandwich B) pRoot : H ι)=_
  rw [pRepresentation_apply,pRight_apply,pProject_val,← hB]
  change (u:ℂ) • ((P*B*P : Operator ι) (lp.single 2 ([],true) 1))=rightP (P (B (vacuum u v)))
  have he : (u:ℂ) • lp.single 2 ([],true) 1=rightP (vacuum u v : H ι) := by
    simp only [vacuum,map_add,map_smul,rightP,CoordinateProjection.proj_single,Set.mem_ofPred_eq,
      ite_true,Bool.false_eq_true,ite_false,smul_zero,add_zero]
  rw [← map_smul,he]
  have hpv : P (rightP (vacuum u v : H ι))=rightP (vacuum u v : H ι) := by
    rw [← he,map_smul,P_nil_true]
  change P (B (P (rightP (vacuum u v))))=rightP (P (B (vacuum u v)))
  have hb : B (rightP (vacuum u v))=rightP (B (vacuum u v)) := DFunLike.congr_fun hBc.eq _
  rw [hpv,hb]
  exact DFunLike.congr_fun (P_commute_rightP (ι := ι)).eq (B (vacuum u v))
theorem right_le_weighted_normalHull :
    (pRight : PRange ℕ →L[ℂ] PRange ℕ).range≤(weightedSystem u v hv hvu).normalHull := by
  let K := (weightedSystem u v hv hvu).normalHull
  have he : K.comap (pRight : PRange ℕ →L[ℂ] PRange ℕ).toLinearMap=⊤ := by
    apply pRange_total _
      ((Submodule.isClosed_topologicalClosure _).preimage pRight.continuous)
    intro w
    obtain ⟨B,hB,hh⟩ := good_basis u v (hv.trans hvu).ne' hv.ne' w
    have hBc : Commute B rightP :=
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp hB.1 rightP (rightP_mem_commutant u v)).1.symm
    change pRight (pProject (lp.single 2 w 1))∈K
    rw [← pRight_pSandwich_basis u v w B hh hBc]
    apply K.smul_mem
    apply (weightedSystem u v hv hvu).normalHull_bicommutant scalarFlip
    apply representedAmbient_le_weightedGenerated u v hv hvu
    change (pRepresentation (ι := ℕ)).symm (pRepresentation (pSandwich B))∈pAmbient u v
    rw [StarAlgEquiv.symm_apply_apply]
    exact mul_mem (mul_mem (P_mem_ambient u v) hB.1) (P_mem_ambient u v)
  rintro ξ ⟨η,rfl⟩
  have hh : η∈K.comap (pRight : PRange ℕ →L[ℂ] PRange ℕ).toLinearMap := by rw [he];trivial
  exact hh

theorem weighted_normalHull_eq_right :
    (weightedSystem u v hv hvu).normalHull=(pRight : PRange ℕ →L[ℂ] PRange ℕ).range :=
  le_antisymm (weighted_normalHull_le_right u v hv hvu) (right_le_weighted_normalHull u v hv hvu)
end

open FreeFock Amplification GaussianRecognition
variable {ι : Type u_5} [DecidableEq ι]

theorem reverseConj_square (T : Operator ι) : reverseConj (reverseConj T)=T := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [reverseConj_apply,reverseOperator_involutive]

theorem reverseConj_mem_commutant (u v : ℝ) (T : Operator ι) (hT : T∈ambientAlgebra u v) :
    reverseConj T∈ambientCommutant u v := by
  have htest (y : Operator ι) (hy : y∈insert P (Set.range (S u v : ι → Operator ι))) : Commute y (reverseConj T) := by
    have hyr : reverseConj y∈ambientCommutant u v := by
      rcases hy with rfl | ⟨i,rfl⟩
      · rw [reverseConj_P];exact rightP_mem_commutant u v
      · rw [reverseConj_S];exact rightS_mem_commutant u v i
    have hc : Commute (reverseConj y) T := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ hyr).1
    have hh := Commute.map hc reverseConj.toStarAlgHom
    change Commute (reverseConj (reverseConj y)) (reverseConj T) at hh
    simpa only [reverseConj_square] using hh
  rw [ambientCommutant,StarSubalgebra.mem_centralizer_iff]
  intro y hy
  have hs : star y=y := by
    rcases hy with rfl | ⟨i,rfl⟩
    · exact projection_P.isSelfAdjoint.star_eq
    · exact (S_selfAdjoint u v i).star_eq
  exact ⟨(htest y hy).eq,by rw [hs];exact (htest y hy).eq⟩

theorem pSandwich_rep_apply (B : Operator ι) (hBP : Commute P B) (ξ : PRange ι) :
    (pRepresentation (pSandwich B) ξ : H ι)=B (ξ:H ι) := by
  rw [pRepresentation_apply]
  change P (B (P (ξ:H ι)))=B (ξ:H ι)
  rw [P_range_apply]
  have hh := DFunLike.congr_fun hBP.eq (ξ:H ι)
  change P (B (ξ:H ι))=B (P (ξ:H ι)) at hh
  rwa [P_range_apply] at hh

theorem pSandwich_star (B : Operator ι) : pSandwich (star B)=star (pSandwich B) := by
  apply Subtype.ext
  change P*star B*P=star (P*B*P)
  simp only [star_mul,projection_P.isSelfAdjoint.star_eq,mul_assoc]

variable (u v : ℝ)

def rightEdge : Operator ℕ := reverseConj (edgePolar u v (0:ℕ))

theorem rightEdge_mem : rightEdge u v∈ambientCommutant u v :=
  reverseConj_mem_commutant u v _ (edgePolar_mem_ambient u v (0:ℕ))

theorem P_commute_rightEdge : Commute P (rightEdge u v) :=
  ((StarSubalgebra.mem_centralizer_iff ℂ).mp (rightEdge_mem u v) P (Set.mem_insert _ _)).1

def pRightEdge : PRange ℕ →L[ℂ] PRange ℕ := pRepresentation (pSandwich (rightEdge u v))

theorem pRightEdge_apply (ξ : PRange ℕ) : (pRightEdge u v ξ : H ℕ)= rightEdge u v (ξ:H ℕ) :=
  pSandwich_rep_apply _ (P_commute_rightEdge u v) ξ

theorem pRightEdge_star_apply (ξ : PRange ℕ) : (star (pRightEdge u v) ξ : H ℕ)=star (rightEdge u v) (ξ:H ℕ) := by
  have hstar : star (pRightEdge u v)=pRepresentation (pSandwich (star (rightEdge u v))) := by
    rw [pSandwich_star]
    exact ((pRepresentation (ι := ℕ)).map_star' (pSandwich (rightEdge u v))).symm
  rw [hstar]
  apply pSandwich_rep_apply
  apply Commute.star_right
  simpa only [projection_P.isSelfAdjoint.star_eq] using P_commute_rightEdge u v

theorem pRightEdge_commute_ambient (T : representedAmbient u v) : Commute (pRightEdge u v) T.val := by
  let x := (pRepresentation (ι := ℕ)).symm T.val
  have hx : (x:Operator ℕ)∈ambientAlgebra u v := T.property
  have hc : Commute (x:Operator ℕ) (rightEdge u v) :=
    ((StarSubalgebra.mem_centralizer_iff ℂ).mp hx _ (rightEdge_mem u v)).1.symm
  have hh : Commute (pRepresentation (pSandwich (rightEdge u v))) (pRepresentation x) := by
    change _ * _ = _ * _
    simpa only [map_mul] using congrArg (fun X : PCorner ℕ => pRepresentation X)
      (pSandwich_commute _ (P_commute_rightEdge u v) x hc).eq
  change Commute (pRepresentation (pSandwich (rightEdge u v))) (pRepresentation ((pRepresentation (ι := ℕ)).symm T.val)) at hh
  rw [StarAlgEquiv.apply_symm_apply] at hh
  exact hh

theorem pRightEdge_left : pRight*pRightEdge u v=pRightEdge u v := by
  have he := congrArg (reverseConj (ι := ℕ)) (edgePolar_left u v (0:ℕ))
  rw [map_mul,reverseConj_P] at he
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change (pRight (pRightEdge u v ξ) : H ℕ)=(pRightEdge u v ξ:H ℕ)
  simp only [pRight_apply,pRightEdge_apply]
  exact DFunLike.congr_fun he (ξ:H ℕ)

theorem pRightEdge_right : pRightEdge u v*(1-pRight)=pRightEdge u v := by
  have he := congrArg (reverseConj (ι := ℕ)) (edgePolar_right u v (0:ℕ))
  rw [map_mul,map_sub,map_one,reverseConj_P] at he
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change (pRightEdge u v (ξ-pRight ξ) : H ℕ)=(pRightEdge u v ξ:H ℕ)
  rw [pRightEdge_apply,pRightEdge_apply]
  change rightEdge u v ((ξ:H ℕ)-(pRight ξ : H ℕ))=rightEdge u v (ξ:H ℕ)
  rw [pRight_apply]
  exact DFunLike.congr_fun he (ξ:H ℕ)

theorem pRightEdge_initial (hv : 0<v) (hvu : v<u) : star (pRightEdge u v)*pRightEdge u v=1-pRight := by
  have he := congrArg (reverseConj (ι := ℕ)) (edgePolar_initial u v hv.le hvu (0:ℕ))
  rw [map_mul,map_star,map_sub,map_one,reverseConj_P] at he
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change (star (pRightEdge u v) (pRightEdge u v ξ) : H ℕ)=(ξ:H ℕ)-(pRight ξ:H ℕ)
  rw [pRightEdge_star_apply,pRightEdge_apply,pRight_apply]
  exact DFunLike.congr_fun he (ξ:H ℕ)

variable (hv : 0<v) (hvu : v<u)

theorem starProjection_congr {E : Type u_6} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K L : Submodule ℂ E) [CompleteSpace K] [CompleteSpace L] (he : K=L) : K.starProjection=L.starProjection := by
  subst L
  rfl

theorem weightedHull_projection : (weightedSystem u v hv hvu).normalHull.starProjection=pRight := by
  let : CompleteSpace (pRight : PRange ℕ →L[ℂ] PRange ℕ).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range pRight_projection.isIdempotentElem).completeSpace_coe
  exact (starProjection_congr _ _ (weighted_normalHull_eq_right u v hv hvu)).trans
    (Amplification.projectionRange_starProjection _ pRight_projection)

theorem pRightEdge_mem_weightedCommutant :
    pRightEdge u v∈StarSubalgebra.centralizer ℂ ((weightedSystem u v hv hvu).generators scalarFlip) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  have hm := weighted_generated_le_ambient u v hv hvu (Bicommutant.subset _ hT)
  exact ⟨(pRightEdge_commute_ambient u v ⟨T,hm⟩).eq.symm,
    (pRightEdge_commute_ambient u v ⟨star T,star_mem hm⟩).eq.symm⟩
end FreeGroupFactorMain.WeightedFock

end

end OAI
