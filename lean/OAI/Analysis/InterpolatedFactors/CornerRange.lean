import OAI.Analysis.InterpolatedFactors.PairedAbsorption

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification WeightedCornerIndex

def oldAnnihilators (u v : ℝ) : Submodule ℂ (PCorner ℕ) where
  carrier := {X | ∀ a : Base u v, star (X : Operator ℕ) ((a.val : Operator ℕ) (vacuum u v))=0}
  zero_mem' := by intro a; simp [star_zero (Operator ℕ)]
  add_mem' := by
    intro X Y hX hY a
    change star ((X : Operator ℕ)+(Y : Operator ℕ)) _=0
    rw [star_add (R := Operator ℕ),add_apply,hX a,hY a,add_zero]
  smul_mem' := by
    intro c X hX a
    change star (c • (X : Operator ℕ)) _=0
    rw [star_smul,smul_apply,hX a,smul_zero]

theorem oldAnnihilators_sandwich (u v : ℝ) (p q : Base u v) (X : PCorner ℕ)
    (hX : X∈oldAnnihilators u v) : (p:PCorner ℕ)*X*(q:PCorner ℕ)∈oldAnnihilators u v := by
  intro a
  change star ((p.val : Operator ℕ)*(X : Operator ℕ)*(q.val : Operator ℕ)) _=0
  rw [star_mul,star_mul,mul_apply_eq_comp,mul_apply_eq_comp]
  have hh := hX (star p*a)
  change star (X : Operator ℕ) (star (p.val : Operator ℕ) ((a.val : Operator ℕ) (vacuum u v)))=0 at hh
  rw [hh,map_zero]

theorem kindCreator_annihilator (u v : ℝ) (k : Kind) (hk : k.valid) :
    kindCreator u v k∈oldAnnihilators u v := by
  intro a
  cases k with
  | fresh n r s =>
    exact normalizedCreation_annihilate u v (0:ℕ) 1 (n+2)
      (by omega) (by omega) (by omega) r s (filledOfCorner a)
  | residual r s => exact normalizedResidual_annihilate u v (0:ℕ) 1 (by omega) r s hk (filledOfCorner a)
  | diagonal r => exact normalizedDiagonal_annihilate u v (0:ℕ) 1 0 (by omega) (by omega) r (filledOfCorner a)

theorem rawReservoir_annihilator (u v : ℝ) (i : WeightedCornerIndex.Index) (n : ℕ) :
    rawReservoir u v i n∈oldAnnihilators u v := by
  intro a
  exact normalizedCreation_annihilate u v (0:ℕ) 1 (reservoirCode (i,n)+2)
    (by omega) (by omega) (by omega) false false (filledOfCorner a)

theorem cornerAbsorption_annihilator (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (i : WeightedCornerIndex.Index) (n : ℕ) :
    (cornerAbsorption u v hv hvu).output i n∈oldAnnihilators u v :=
  (cornerAbsorption u v hv hvu).output_mem (oldAnnihilators u v) (oldAnnihilators_sandwich u v)
    (fun i => kindCreator_annihilator u v _ (description_valid i)) (rawReservoir_annihilator u v) i n
end FreeGroupFactorMain.WeightedFock

namespace FreeGroupFactorMain.Amplification
variable {A : Type u_1} [CStarAlgebra A]

def cornerEqualityEquiv (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p=q) :
    Corner p hp ≃⋆ₐ[ℂ] Corner q hq := by
  subst q
  exact StarAlgEquiv.refl ℂ (Corner p hp)

theorem cornerEqualityEquiv_val (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p=q)
    (x : Corner p hp) : (cornerEqualityEquiv p q hp hq h x : A)=(x:A) := by
  subst q
  rfl

variable {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (p : E →L[ℂ] E) (hp : IsStarProjection p) [CompleteSpace p.range]

include hp in
theorem projectionRange_starProjection : p.range.starProjection=p :=
  (isStarProjection_iff_eq_starProjection_range.mp hp).choose_spec.symm

def projectionRepresentation : Corner p hp ≃⋆ₐ[ℂ] (p.range →L[ℂ] p.range) :=
  (cornerEqualityEquiv p p.range.starProjection hp isStarProjection_starProjection
    (projectionRange_starProjection p hp).symm).trans (cornerRepresentation p.range)

theorem projectionRepresentation_apply (x : Corner p hp) (ξ : p.range) :
    (projectionRepresentation p hp x ξ : E)=(x:E →L[ℂ] E) ξ := by
  change (cornerRestrict p.range
    (cornerEqualityEquiv p p.range.starProjection hp isStarProjection_starProjection
      (projectionRange_starProjection p hp).symm x) ξ : E) = _
  rw [cornerRestrict_apply,cornerEqualityEquiv_val]
end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification Filter Topology
open scoped ENNReal
variable {ι : Type u_3} [DecidableEq ι]

abbrev PRange (ι : Type u_4) [DecidableEq ι] := (P : Operator ι).range
instance pRange_complete : CompleteSpace (PRange ι) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (projection_P (ι := ι)).isIdempotentElem).completeSpace_coe

def pRoot : PRange ι := ⟨lp.single 2 ([],true) 1,⟨lp.single 2 ([],true) 1,P_nil_true 1⟩⟩

theorem pRoot_norm : ‖(pRoot : PRange ι)‖=1 := by
  change ‖lp.single (E := fun _ : Path ι => ℂ) 2 ([],true) 1‖=1
  rw [lp.norm_single] <;> norm_num

instance pRange_nontrivial : Nontrivial (PRange ι) := by
  apply nontrivial_of_ne (pRoot : PRange ι) 0
  intro h
  have hh := pRoot_norm (ι := ι)
  rw [h,norm_zero] at hh
  exact zero_ne_one hh

abbrev pRepresentation : PCorner ι ≃⋆ₐ[ℂ] (PRange ι →L[ℂ] PRange ι) :=
  projectionRepresentation P projection_P

theorem pRepresentation_apply (x : PCorner ι) (ξ : PRange ι) :
    (pRepresentation x ξ : H ι)=(x:Operator ι) ξ :=
  projectionRepresentation_apply P projection_P x ξ

def pProject : H ι →L[ℂ] PRange ι := (P : Operator ι).range.orthogonalProjectionOnto

theorem pProject_val (ξ : H ι) : (pProject ξ : H ι)=P ξ := by
  change (P : Operator ι).range.starProjection ξ=P ξ
  rw [projectionRange_starProjection P projection_P]

theorem pProject_coe (ξ : PRange ι) : pProject (ξ:H ι)=ξ :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ξ

theorem pRange_total (K : Submodule ℂ (PRange ι)) (hK : IsClosed (K : Set (PRange ι)))
    (hb : ∀ w : Path ι, pProject (lp.single 2 w 1)∈K) : K=⊤ := by
  apply top_unique
  intro ξ _
  have hs := (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) (ξ:H ι)).map pProject pProject.continuous
  rw [pProject_coe] at hs
  apply hK.mem_of_tendsto hs
  filter_upwards [] with s
  apply K.sum_mem
  intro w _
  have he : lp.single (E := fun _ : Path ι => ℂ) 2 w ((ξ:H ι) w)=
      ((ξ:H ι) w) • lp.single 2 w 1 := by
    ext q
    simp [lp.single_apply,Pi.single_apply]
  change pProject (lp.single 2 w ((ξ:H ι) w))∈K
  rw [he,map_smul]
  exact K.smul_mem _ (hb w)

def oldBaseCorner (u v : ℝ) (i j : ι) : PCorner ι :=
  ⟨oldBaseGenerator u v i j,oldBaseGenerator_left u v i j,oldBaseGenerator_right u v i j⟩

def oldBaseOp (u v : ℝ) (i j : ι) : PRange ι →L[ℂ] PRange ι := pRepresentation (oldBaseCorner u v i j)

theorem oldBaseCorner_selfAdjoint (u v : ℝ) (i j : ι) : IsSelfAdjoint (oldBaseCorner u v i j) :=
  Subtype.ext (oldBaseGenerator_selfAdjoint u v i j).star_eq

theorem oldBaseOp_selfAdjoint (u v : ℝ) (i j : ι) : IsSelfAdjoint (oldBaseOp u v i j) :=
by
  change star (pRepresentation (oldBaseCorner u v i j))=pRepresentation (oldBaseCorner u v i j)
  exact ((pRepresentation (ι := ι)).map_star' (oldBaseCorner u v i j)).symm.trans
    (congrArg (fun x : PCorner ι => pRepresentation x) (oldBaseCorner_selfAdjoint u v i j).star_eq)

theorem oldBaseOp_eigen_root_zero (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι)
    (z : ℂ) (η : PRange ι) (he : oldBaseOp u v i j η=z • η) : inner ℂ (pRoot : PRange ι) η=0 := by
  have hh := congrArg (fun x : PRange ι => (x:H ι)) he
  rw [oldBaseOp,pRepresentation_apply] at hh
  have hz := oldBaseGenerator_eigen_root_zero u v hv hvu i j z (η:H ι) hh
  change inner ℂ (lp.single 2 ([],true) 1) (η:H ι)=0
  simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using hz
end

open FreeFock Amplification
variable {ι : Type u_5} [DecidableEq ι]

def pSandwich (B : Operator ι) : PCorner ι :=
  ⟨P*B*P,by
    constructor
    · rw [← mul_assoc,← mul_assoc,projection_P.isIdempotentElem.eq]
    · rw [mul_assoc,mul_assoc,projection_P.isIdempotentElem.eq,mul_assoc]⟩

theorem pSandwich_commute (B : Operator ι) (hBP : Commute P B)
    (x : PCorner ι) (hBx : Commute (x:Operator ι) B) : Commute (pSandwich B) x := by
  apply Subtype.ext
  change P*B*P*(x:Operator ι)=(x:Operator ι)*(P*B*P)
  calc
    _ = P*(B*(x:Operator ι)) := by rw [mul_assoc (P*B),x.property.1,mul_assoc]
    _ = P*((x:Operator ι)*B) := by rw [hBx.eq]
    _ = (x:Operator ι)*B := by rw [← mul_assoc,x.property.1]
    _ = (x:Operator ι)*(P*B*P) := by
      symm
      rw [← mul_assoc,← mul_assoc,x.property.2,mul_assoc,← hBP.eq,← mul_assoc,x.property.2]

theorem pRoot_vacuum (u v : ℝ) : (P : Operator ι) (vacuum u v)=(u:ℂ) • ((pRoot : PRange ι):H ι) := by
  simp only [vacuum,map_add,map_smul,P_nil_true,P_nil_false,smul_zero,add_zero,pRoot]

theorem pSandwich_basis (u v : ℝ) (w : Path ι) (B : Operator ι)
    (hBP : Commute P B) (hB : B (vacuum u v)=lp.single 2 w 1) :
    (u:ℂ) • pRepresentation (pSandwich B) pRoot=pProject (lp.single 2 w 1) := by
  apply Subtype.ext
  change (u:ℂ) • (pRepresentation (pSandwich B) pRoot : H ι)=_
  rw [pRepresentation_apply,pProject_val,← hB]
  change (u:ℂ) • ((P*B*P : Operator ι) ((pRoot : PRange ι):H ι))=P (B (vacuum u v))
  rw [← map_smul,← pRoot_vacuum]
  have he : P*B*P*P=P*B := by
    rw [mul_assoc (P*B),projection_P.isIdempotentElem.eq,mul_assoc,← hBP.eq,
      ← mul_assoc,projection_P.isIdempotentElem.eq]
  exact DFunLike.congr_fun he (vacuum u v)

theorem centralizer_bicommutant {E : Type u_6} [Ring E] [StarRing E] [Algebra ℂ E] [StarModule ℂ E]
    (S : Set E) (B : StarSubalgebra.centralizer ℂ S) :
    (B:E)∈StarSubalgebra.centralizer ℂ (Bicommutant.algebra S : Set E) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  exact ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp hT B B.property).1.symm,
    ((StarSubalgebra.mem_centralizer_iff ℂ).mp (star_mem hT) B B.property).1.symm⟩

theorem oldBaseOp_commutant_total (u v : ℝ) (hu : u≠0) (hv : v≠0) (i j : ι) :
    (Submodule.span ℂ (Set.range (fun B : StarSubalgebra.centralizer ℂ
      (Bicommutant.algebra ({oldBaseOp u v i j} : Set (PRange ι →L[ℂ] PRange ι)) :
        Set (PRange ι →L[ℂ] PRange ι)) => (B:PRange ι →L[ℂ] PRange ι) pRoot))).topologicalClosure=⊤ := by
  let N := StarSubalgebra.centralizer ℂ
    (Bicommutant.algebra ({oldBaseOp u v i j} : Set (PRange ι →L[ℂ] PRange ι)) :
      Set (PRange ι →L[ℂ] PRange ι))
  let K := (Submodule.span ℂ (Set.range (fun B : N => (B:PRange ι →L[ℂ] PRange ι) pRoot))).topologicalClosure
  apply pRange_total K (Submodule.isClosed_topologicalClosure _)
  intro w
  obtain ⟨B,hB,heB,_⟩ := good_right_basis u v hu hv w
  have hBP : Commute P B := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hB P (Set.mem_insert _ _)).1
  have hBA : Commute (oldBaseGenerator u v i j) B :=
    ((StarSubalgebra.mem_centralizer_iff ℂ).mp (oldBaseGenerator_mem_ambient u v hu i j) B hB).1.symm
  have hc : Commute (pRepresentation (pSandwich B)) (pRepresentation (oldBaseCorner u v i j)) := by
    change _ * _ = _ * _
    simpa only [map_mul] using congrArg (fun x : PCorner ι => pRepresentation x)
      (pSandwich_commute B hBP (oldBaseCorner u v i j) hBA).eq
  have hm : pRepresentation (pSandwich B)∈N := by
    apply centralizer_bicommutant ({oldBaseOp u v i j} : Set (PRange ι →L[ℂ] PRange ι))
      ⟨pRepresentation (pSandwich B),?_⟩
    rw [StarSubalgebra.mem_centralizer_iff]
    intro T hT
    rcases hT with rfl
    exact ⟨hc.symm,(by rw [(oldBaseOp_selfAdjoint u v i j).star_eq]; exact hc.symm)⟩
  rw [← pSandwich_basis u v w B hBP heB]
  exact K.smul_mem _ (Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self (⟨pRepresentation (pSandwich B),hm⟩:N))))
end FreeGroupFactorMain.WeightedFock

end

end OAI
