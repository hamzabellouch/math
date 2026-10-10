import OAI.Analysis.InterpolatedFactors.Diagonal

namespace OAI

noncomputable section

universe u_1 u_2 u_3

namespace FreeGroupFactorMain.GaussianSplit
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (B : StarSubalgebra ℂ (E →L[ℂ] E)) (C : E →L[ℂ] E) (Ω : E)
variable (hC : ∀ a : B,star C*(a : E →L[ℂ] E)*C=(inner ℂ Ω ((a : E →L[ℂ] E) Ω)) • 1)
variable (hΩ : ∀ a : B,star C ((a : E →L[ℂ] E) Ω)=0)
variable (d : B) (hd : IsStarProjection d) (hcentral : ∀ a : B,Commute d a)

def cut (r : Bool) : B := if r then d else 1-d

include hd in
theorem cut_star (r : Bool) : star (cut B d r)=cut B d r := by
  cases r <;> simp only [cut,Bool.false_eq_true,ite_false,ite_true,star_sub (R := B),star_one,hd.isSelfAdjoint.star_eq]

include hd in
theorem cut_d (r : Bool) : cut B d r*d=if r then d else 0 := by
  cases r <;> simp only [cut,Bool.false_eq_true,ite_false,ite_true,sub_mul,one_mul,hd.isIdempotentElem.eq,sub_self]

include hd hcentral in
theorem cut_false_a_d (a : B) : cut B d false*a*d=0 := by
  rw [mul_assoc,← (hcentral a).eq,← mul_assoc,cut_d B d hd]
  simp only [Bool.false_eq_true,ite_false,zero_mul]

def block (r s : Bool) : E →L[ℂ] E := (cut B d r : E →L[ℂ] E)*C*(cut B d s : E →L[ℂ] E)

def D : E →L[ℂ] E := (d : E →L[ℂ] E)*C*(d : E →L[ℂ] E)

def covariance (a : B) : B := (inner ℂ Ω (((d*a*d : B) : E →L[ℂ] E) Ω)) • d

include hC hd in
theorem D_contraction (a : B) : star (D B C d)*(a : E →L[ℂ] E)*D B C d=
    (covariance B Ω d a : E →L[ℂ] E) := by
  have he := hC (d*a*d)
  have hs : star (d : E →L[ℂ] E)=(d : E →L[ℂ] E) := congrArg Subtype.val hd.isSelfAdjoint.star_eq
  have hid : (d : E →L[ℂ] E)*(d : E →L[ℂ] E)=(d : E →L[ℂ] E) := congrArg Subtype.val hd.isIdempotentElem.eq
  change star C*((d : E →L[ℂ] E)*(a : E →L[ℂ] E)*(d : E →L[ℂ] E))*C=_ at he
  calc
    _ = (d : E →L[ℂ] E)*(star C*((d : E →L[ℂ] E)*(a : E →L[ℂ] E)*(d : E →L[ℂ] E))*C)*(d : E →L[ℂ] E) := by
      simp only [D,star_mul,hs,mul_assoc]
    _ = _ := by rw [he,mul_smul_comm,smul_mul_assoc,mul_one,hid];rfl

include hΩ hd in
theorem D_annihilation (a : B) : star (D B C d) ((a : E →L[ℂ] E) Ω)=0 := by
  have he := hΩ (d*a)
  have hs : star (d : E →L[ℂ] E)=(d : E →L[ℂ] E) := congrArg Subtype.val hd.isSelfAdjoint.star_eq
  simp only [D,star_mul,hs,mul_apply_eq_comp]
  change star C ((d : E →L[ℂ] E) ((a : E →L[ℂ] E) Ω))=0 at he
  rw [he,map_zero]

include hC hd in
theorem block_contraction (r s r' s' : Bool) (a : B) :
    star (block B C d r s)*(a : E →L[ℂ] E)*block B C d r' s'=
      (inner ℂ ((cut B d r : E →L[ℂ] E) Ω)
        ((a : E →L[ℂ] E) ((cut B d r' : E →L[ℂ] E) Ω))) •
        ((cut B d s : E →L[ℂ] E)*(cut B d s' : E →L[ℂ] E)) := by
  have hs (r) : star (cut B d r : E →L[ℂ] E)=(cut B d r : E →L[ℂ] E) :=
    congrArg Subtype.val (cut_star B d hd r)
  have he := hC (cut B d r*a*cut B d r')
  change star C*((cut B d r : E →L[ℂ] E)*(a : E →L[ℂ] E)*(cut B d r' : E →L[ℂ] E))*C=_ at he
  calc
    _ = (cut B d s : E →L[ℂ] E)*
        (star C*((cut B d r : E →L[ℂ] E)*(a : E →L[ℂ] E)*(cut B d r' : E →L[ℂ] E))*C)*
        (cut B d s' : E →L[ℂ] E) := by simp only [block,star_mul,hs,mul_assoc]
    _ = _ := by
      rw [he,mul_smul_comm,smul_mul_assoc,mul_one]
      congr 1
      change inner ℂ Ω ((cut B d r : E →L[ℂ] E) ((a : E →L[ℂ] E) ((cut B d r' : E →L[ℂ] E) Ω)))=_
      rw [← ContinuousLinearMap.adjoint_inner_left]
      change inner ℂ ((star (cut B d r : E →L[ℂ] E)) Ω) _=_
      rw [hs r]

include hΩ hd in
theorem block_annihilation (r s : Bool) (a : B) : star (block B C d r s) ((a : E →L[ℂ] E) Ω)=0 := by
  have he := hΩ (cut B d r*a)
  have hs (r) : star (cut B d r : E →L[ℂ] E)=(cut B d r : E →L[ℂ] E) :=
    congrArg Subtype.val (cut_star B d hd r)
  simp only [block,star_mul,hs,mul_apply_eq_comp]
  change star C ((cut B d r : E →L[ℂ] E) ((a : E →L[ℂ] E) Ω))=0 at he
  rw [he,map_zero]

include hC hd hcentral in
theorem block_D (r s : Bool) (hrs : ¬(r=true ∧ s=true)) (a : B) :
    star (block B C d r s)*(a : E →L[ℂ] E)*D B C d=0 := by
  have he := block_contraction B C Ω hC d hd r s true true a
  change star (block B C d r s)*(a : E →L[ℂ] E)*D B C d=
    (inner ℂ ((cut B d r : E →L[ℂ] E) Ω)
      ((a : E →L[ℂ] E) ((d : E →L[ℂ] E) Ω))) •
      ((cut B d s : E →L[ℂ] E)*(d : E →L[ℂ] E)) at he
  rw [he]
  cases s with
  | false =>
    have hz : (cut B d false : E →L[ℂ] E)*(d : E →L[ℂ] E)=0 :=
      congrArg Subtype.val (cut_d B d hd false)
    rw [hz,smul_zero (M := ℂ) (A := E →L[ℂ] E)]
  | true =>
    have hr : r=false := by cases r <;> simp_all
    subst r
    have hz := congrArg Subtype.val (cut_false_a_d B d hd hcentral a)
    change (cut B d false : E →L[ℂ] E)*(a : E →L[ℂ] E)*(d : E →L[ℂ] E)=0 at hz
    have hs : star (cut B d false : E →L[ℂ] E)=(cut B d false : E →L[ℂ] E) :=
      congrArg Subtype.val (cut_star B d hd false)
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ Ω ((star (cut B d false : E →L[ℂ] E)*(a : E →L[ℂ] E)*(d : E →L[ℂ] E)) Ω) • _=0
    rw [hs,hz,zero_apply,inner_zero_right,zero_smul ℂ (A := E →L[ℂ] E)]

def filled : StarSubalgebra ℂ (E →L[ℂ] E) :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
    (insert (D B C d+star (D B C d)) (B : Set (E →L[ℂ] E))) : Set (E →L[ℂ] E))

include hC hΩ hd hcentral in

theorem residual_covariance (r s r' s' : Bool) (hrs : ¬(r=true ∧ s=true))
    (hrs' : ¬(r'=true ∧ s'=true)) (T : filled B C d) :
    star (block B C d r s)*(T : E →L[ℂ] E)*block B C d r' s'=
      (inner ℂ ((cut B d r : E →L[ℂ] E) Ω)
        ((T : E →L[ℂ] E) ((cut B d r' : E →L[ℂ] E) Ω))) •
        ((cut B d s : E →L[ℂ] E)*(cut B d s' : E →L[ℂ] E)) := by
  apply GaussianExtension.covariance_extension B (D B C d) (covariance B Ω d)
    (D_contraction B C Ω hC d hd) (block B C d r s) (block B C d r' s') _
    ((cut B d r : E →L[ℂ] E) Ω) ((cut B d r' : E →L[ℂ] E) Ω)
    (fun a => D_annihilation B C Ω hΩ d hd (a*cut B d r))
    (fun a => D_annihilation B C Ω hΩ d hd (a*cut B d r'))
    (block_D B C Ω hC d hd hcentral r s hrs) _
    (block_contraction B C Ω hC d hd r s r' s') (T : E →L[ℂ] E) T.property
  intro a
  have he := congrArg star (block_D B C Ω hC d hd hcentral r' s' hrs' (star a))
  simpa only [star_mul,star_star,star_zero (E →L[ℂ] E),StarMemClass.coe_star,mul_assoc] using he

include hC hΩ hd hcentral in
theorem residual_annihilation (r s : Bool) (hrs : ¬(r=true ∧ s=true)) (T : filled B C d) :
    star (block B C d r s) ((T : E →L[ℂ] E) Ω)=0 :=
  GaussianExtension.annihilation_extension B (D B C d) (covariance B Ω d)
    (D_contraction B C Ω hC d hd) (block B C d r s) Ω
    (D_annihilation B C Ω hΩ d hd) (block_annihilation B C Ω hΩ d hd r s)
    (block_D B C Ω hC d hd hcentral r s hrs) T T.property
end FreeGroupFactorMain.GaussianSplit

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

theorem edgeDefect_commute (u v : ℝ) (i : ι) (T : edgeAlgebra u v i) :
    Commute (edgeDefect u v i) (T : Operator ι) := by
  have hl (a : edgeAlgebra u v i) :
      edgeDefect u v i*(a : Operator ι)*edgeDefect u v i=(a : Operator ι)*edgeDefect u v i := by
    obtain ⟨c,hc⟩ := edge_algebra_scalar_on_defect u v i a
    rw [mul_assoc,hc,mul_smul_comm,(edgeDefect_projection u v i).isIdempotentElem.eq]
  have hr := congrArg star (hl (star T))
  simp only [star_mul,StarMemClass.coe_star,star_star,
    (edgeDefect_projection u v i).isSelfAdjoint.star_eq,← mul_assoc] at hr
  exact hr.symm.trans (hl T)

def defectAsEdge (u v : ℝ) (i : ι) : edgeAlgebra u v i :=
  ⟨edgeDefect u v i,edgeDefect_mem_edge u v i⟩

theorem defectAsEdge_projection (u v : ℝ) (i : ι) : IsStarProjection (defectAsEdge u v i) := by
  constructor
  · apply Subtype.ext
    exact (edgeDefect_projection u v i).isIdempotentElem.eq
  · apply Subtype.ext
    exact (edgeDefect_projection u v i).isSelfAdjoint.star_eq

theorem defectAsEdge_central (u v : ℝ) (i : ι) (a : edgeAlgebra u v i) :
    Commute (defectAsEdge u v i) a := Subtype.ext (edgeDefect_commute u v i a).eq

theorem fresh_C_edge_contraction (u v : ℝ) (i j : ι) (hji : j≠i) (a : edgeAlgebra u v i) :
    star (C u v j)*(a : Operator ι)*C u v j=
      (inner ℂ (vacuum u v) ((a : Operator ι) (vacuum u v))) • 1 := by
  have hh := fresh_C_contraction u v {i} j j hji hji
    ⟨a,edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) a.property⟩
  simpa only [ite_true,vacuumTrace] using hh

theorem fresh_C_edge_annihilation (u v : ℝ) (i j : ι) (hji : j≠i) (a : edgeAlgebra u v i) :
    star (C u v j) ((a : Operator ι) (vacuum u v))=0 :=
  fresh_C_annihilates_old_vacuum u v {i} j hji
    ⟨a,edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) a.property⟩

def splitCut (u v : ℝ) (i : ι) (b : Bool) : Operator ι :=
  GaussianSplit.cut (edgeAlgebra u v i) (defectAsEdge u v i) b

def splitBlock (u v : ℝ) (i j : ι) (r s : Bool) : Operator ι :=
  GaussianSplit.block (edgeAlgebra u v i) (C u v j) (defectAsEdge u v i) r s

theorem splitBlock_filled_covariance (u v : ℝ) (i j : ι) (hji : j≠i)
    (r s r' s' : Bool) (hrs : ¬(r=true ∧ s=true)) (hrs' : ¬(r'=true ∧ s'=true))
    (T : filledEdgeAlgebra u v i j) :
    star (splitBlock u v i j r s)*(T : Operator ι)*splitBlock u v i j r' s'=
      (inner ℂ (splitCut u v i r (vacuum u v))
        ((T : Operator ι) (splitCut u v i r' (vacuum u v)))) •
        (splitCut u v i s*splitCut u v i s') :=
  GaussianSplit.residual_covariance (edgeAlgebra u v i) (C u v j) (vacuum u v)
    (fresh_C_edge_contraction u v i j hji) (fresh_C_edge_annihilation u v i j hji)
    (defectAsEdge u v i) (defectAsEdge_projection u v i) (defectAsEdge_central u v i)
    r s r' s' hrs hrs' T

theorem splitBlock_filled_annihilation (u v : ℝ) (i j : ι) (hji : j≠i)
    (r s : Bool) (hrs : ¬(r=true ∧ s=true)) (T : filledEdgeAlgebra u v i j) :
    star (splitBlock u v i j r s) ((T : Operator ι) (vacuum u v))=0 :=
  GaussianSplit.residual_annihilation (edgeAlgebra u v i) (C u v j) (vacuum u v)
    (fresh_C_edge_contraction u v i j hji) (fresh_C_edge_annihilation u v i j hji)
    (defectAsEdge u v i) (defectAsEdge_projection u v i) (defectAsEdge_central u v i)
    r s hrs T

theorem splitCut_mem_edge (u v : ℝ) (i : ι) (b : Bool) : splitCut u v i b∈edgeAlgebra u v i :=
  (GaussianSplit.cut (edgeAlgebra u v i) (defectAsEdge u v i) b).property

theorem splitCut_selfAdjoint (u v : ℝ) (i : ι) (b : Bool) : IsSelfAdjoint (splitCut u v i b) :=
  congrArg Subtype.val (GaussianSplit.cut_star (edgeAlgebra u v i) (defectAsEdge u v i)
    (defectAsEdge_projection u v i) b)

def splitPair (u v : ℝ) (i j : ι) (r s : Bool) : Operator ι :=
  splitBlock u v i j r s+star (splitBlock u v i j s r)

theorem splitPair_eq (u v : ℝ) (i j : ι) (r s : Bool) :
    splitPair u v i j r s=splitCut u v i r*S u v j*splitCut u v i s := by
  change splitCut u v i r*C u v j*splitCut u v i s+
    star (splitCut u v i s*C u v j*splitCut u v i r)=_
  simp only [S_eq,star_mul,(splitCut_selfAdjoint u v i r).star_eq,
    (splitCut_selfAdjoint u v i s).star_eq,mul_add,add_mul,mul_assoc]

theorem splitPair_mem_ambient (u v : ℝ) (i j : ι) (r s : Bool) :
    splitPair u v i j r s∈ambientAlgebra u v := by
  rw [splitPair_eq]
  exact mul_mem (mul_mem (edgeAlgebra_le_ambient u v i (splitCut_mem_edge u v i r))
    (S_mem_ambient u v j)) (edgeAlgebra_le_ambient u v i (splitCut_mem_edge u v i s))

theorem splitPair_reconstruct (u v : ℝ) (i j : ι) :
    S u v j=splitPair u v i j false false+splitPair u v i j false true+
      splitPair u v i j true false+splitPair u v i j true true := by
  simp only [splitPair_eq]
  change S u v j=(1-edgeDefect u v i)*S u v j*(1-edgeDefect u v i)+
    (1-edgeDefect u v i)*S u v j*edgeDefect u v i+
    edgeDefect u v i*S u v j*(1-edgeDefect u v i)+
    edgeDefect u v i*S u v j*edgeDefect u v i
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  abel

end

open FreeFock
variable {ι : Type u_3} [DecidableEq ι]

def residualLeg (u v : ℝ) (i : ι) : Option Bool → Operator ι
  | none => edgeDefect u v i
  | some false => edgeRange u v i
  | some true => edgePolar u v i

def residualSupport (u v : ℝ) (i : ι) : Option Bool → Operator ι
  | none => edgeDefect u v i
  | some _ => edgeRange u v i

def residualCut : Option Bool → Bool
  | none => true
  | some _ => false

theorem residualLeg_mem_edge (u v : ℝ) (i : ι) (r : Option Bool) :
    residualLeg u v i r∈edgeAlgebra u v i := by
  cases r with
  | none => exact edgeDefect_mem_edge u v i
  | some r => cases r
              · exact edgeRange_mem_edge u v i
              · exact edgePolar_mem_edge u v i

theorem P_mul_residualLeg (u v : ℝ) (i : ι) (r : Option Bool) :
    P*residualLeg u v i r=residualLeg u v i r := by
  cases r with
  | none => exact P_mul_edgeDefect u v i
  | some r => cases r
              · exact edgeRange_le_P u v i
              · exact edgePolar_left u v i

theorem edgePolar_mul_defect (u v : ℝ) (i : ι) : edgePolar u v i*edgeDefect u v i=0 := by
  rw [← P_mul_edgeDefect u v i,← mul_assoc,edgePolar_mul_P,zero_mul]

theorem edgePolar_mul_range (u v : ℝ) (i : ι) : edgePolar u v i*edgeRange u v i=0 := by
  rw [← edgeRange_le_P u v i,← mul_assoc,edgePolar_mul_P,zero_mul]

theorem defect_mul_star_edgePolar (u v : ℝ) (i : ι) :
    edgeDefect u v i*star (edgePolar u v i)=0 := by
  simpa only [star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq,star_zero (Operator ι)]
    using congrArg star (edgePolar_mul_defect u v i)

theorem range_mul_star_edgePolar (u v : ℝ) (i : ι) :
    edgeRange u v i*star (edgePolar u v i)=0 := by
  simpa only [star_mul,(edgeRange_projection u v i).isSelfAdjoint.star_eq,star_zero (Operator ι)]
    using congrArg star (edgePolar_mul_range u v i)

theorem residualLeg_mul_star (u v : ℝ) (i : ι) (r s : Option Bool) :
    residualLeg u v i r*star (residualLeg u v i s)=
      if r=s then residualSupport u v i r else 0 := by
  rcases r with _ | (_ | _) <;> rcases s with _ | (_ | _)
  all_goals simp only [residualLeg,residualSupport,Option.some.injEq,Option.some_ne_none,
      reduceCtorEq,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false]
  · rw [(edgeDefect_projection u v i).isSelfAdjoint.star_eq]
    exact (edgeDefect_projection u v i).isIdempotentElem.eq
  · rw [(edgeRange_projection u v i).isSelfAdjoint.star_eq,defect_mul_edgeRange]
  · exact defect_mul_star_edgePolar u v i
  · rw [(edgeDefect_projection u v i).isSelfAdjoint.star_eq,edgeRange_mul_defect]
  · rw [(edgeRange_projection u v i).isSelfAdjoint.star_eq]
    exact (edgeRange_projection u v i).isIdempotentElem.eq
  · exact range_mul_star_edgePolar u v i
  · rw [(edgeDefect_projection u v i).isSelfAdjoint.star_eq,edgePolar_mul_defect]
  · rw [(edgeRange_projection u v i).isSelfAdjoint.star_eq,edgePolar_mul_range]
  · rfl

theorem residualLeg_cut (u v : ℝ) (i : ι) (r : Option Bool) :
    residualLeg u v i r*splitCut u v i (residualCut r)=residualLeg u v i r := by
  rcases r with _ | (_ | _)
  · exact (edgeDefect_projection u v i).isIdempotentElem.eq
  · change edgeRange u v i*(1-edgeDefect u v i)=edgeRange u v i
    rw [mul_sub,mul_one,edgeRange_mul_defect,sub_zero]
  · change edgePolar u v i*(1-edgeDefect u v i)=edgePolar u v i
    rw [mul_sub,mul_one,edgePolar_mul_defect,sub_zero]

theorem cut_star_residualLeg (u v : ℝ) (i : ι) (r : Option Bool) :
    splitCut u v i (residualCut r)*star (residualLeg u v i r)=star (residualLeg u v i r) := by
  simpa only [star_mul,(splitCut_selfAdjoint u v i (residualCut r)).star_eq]
    using congrArg star (residualLeg_cut u v i r)

theorem residualLeg_trace_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i : ι) (r s : Option Bool) (T : ambientAlgebra (ι := ι) u v) :
    vacuumTrace u v (star (residualLeg u v i r)*(T : Operator ι)*residualLeg u v i s)=
      if r=s then vacuumTrace u v ((T : Operator ι)*residualSupport u v i r) else 0 := by
  have ht := ambient_trace_mul u v hu hv
    ⟨star (residualLeg u v i r),star_mem (edgeAlgebra_le_ambient u v i (residualLeg_mem_edge u v i r))⟩
    (T*⟨residualLeg u v i s,edgeAlgebra_le_ambient u v i (residualLeg_mem_edge u v i s)⟩)
  change vacuumTrace u v (star (residualLeg u v i r)*((T : Operator ι)*residualLeg u v i s))=
    vacuumTrace u v (((T : Operator ι)*residualLeg u v i s)*star (residualLeg u v i r)) at ht
  rw [mul_assoc,ht,mul_assoc,residualLeg_mul_star]
  by_cases h : r=s
  · subst s; simp only [ite_true]
  · simp only [h,Ne.symm h,ite_false,mul_zero,vacuumTrace,zero_apply,inner_zero_right]

def residualCreation (u v : ℝ) (i j : ι) (r s : Option Bool) : Operator ι :=
  residualLeg u v i r*C u v j*star (residualLeg u v i s)

theorem residualCreation_split (u v : ℝ) (i j : ι) (r s : Option Bool) :
    residualCreation u v i j r s=
      residualLeg u v i r*splitBlock u v i j (residualCut r) (residualCut s)*star (residualLeg u v i s) := by
  change _=residualLeg u v i r*(splitCut u v i (residualCut r)*C u v j*
    splitCut u v i (residualCut s))*star (residualLeg u v i s)
  simp only [mul_assoc]
  rw [cut_star_residualLeg]
  rw [← mul_assoc, residualLeg_cut]
  rfl

theorem residual_allowed (r s : Option Bool) (h : ¬(r=none ∧ s=none)) :
    ¬(residualCut r=true ∧ residualCut s=true) := by
  rcases r with _ | (_ | _) <;> rcases s with _ | (_ | _) <;> simp_all [residualCut]

theorem residualCreation_filled_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j : ι) (hji : j≠i) (r s r' s' : Option Bool)
    (hrs : ¬(r=none ∧ s=none)) (hrs' : ¬(r'=none ∧ s'=none))
    (T : filledEdgeAlgebra u v i j) :
    star (residualCreation u v i j r s)*(T : Operator ι)*residualCreation u v i j r' s'=
      if r=r' ∧ s=s' then
        vacuumTrace u v ((T : Operator ι)*residualSupport u v i r) • residualSupport u v i s else 0 := by
  let a (t : Option Bool) : filledEdgeAlgebra u v i j :=
    ⟨residualLeg u v i t,edgeAlgebra_le_filled u v i j (residualLeg_mem_edge u v i t)⟩
  have hc := splitBlock_filled_covariance u v i j hji (residualCut r) (residualCut s)
    (residualCut r') (residualCut s') (residual_allowed r s hrs) (residual_allowed r' s' hrs')
    (star (a r)*T*a r')
  have hi : inner ℂ (splitCut u v i (residualCut r) (vacuum u v))
      (((star (a r)*T*a r' : filledEdgeAlgebra u v i j) : Operator ι)
        (splitCut u v i (residualCut r') (vacuum u v)))=
      vacuumTrace u v (star (residualLeg u v i r)*(T : Operator ι)*residualLeg u v i r') := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (vacuum u v) ((star (splitCut u v i (residualCut r))*
      (star (residualLeg u v i r)*(T : Operator ι)*residualLeg u v i r')*
      splitCut u v i (residualCut r')) (vacuum u v))=_
    rw [(splitCut_selfAdjoint u v i (residualCut r)).star_eq]
    simp only [← mul_assoc,cut_star_residualLeg]
    rw [mul_assoc _ _ (splitCut u v i (residualCut r')),residualLeg_cut]
    rfl
  rw [hi] at hc
  calc
    _ = residualLeg u v i s*(star (splitBlock u v i j (residualCut r) (residualCut s))*
        (star (residualLeg u v i r)*(T : Operator ι)*residualLeg u v i r')*
        splitBlock u v i j (residualCut r') (residualCut s'))*star (residualLeg u v i s') := by
      rw [residualCreation_split,residualCreation_split]
      simp only [star_mul,star_star,mul_assoc]
    _ = _ := by
      change (residualLeg u v i s*(star (splitBlock u v i j (residualCut r) (residualCut s))*
        ((star (a r)*T*a r' : filledEdgeAlgebra u v i j) : Operator ι)*
        splitBlock u v i j (residualCut r') (residualCut s'))*star (residualLeg u v i s'))=_
      rw [hc,mul_smul_comm,smul_mul_assoc]
      rw [← mul_assoc,mul_assoc _ (splitCut u v i (residualCut s')),
        cut_star_residualLeg,residualLeg_cut,residualLeg_mul_star]
      rw [residualLeg_trace_covariance u v hu hv i r r'
        ⟨T,filledEdgeAlgebra_le_ambient u v i j T.property⟩]
      by_cases hr : r=r' <;> by_cases hs : s=s' <;>
        simp only [hr,hs,ite_true,ite_false,zero_smul ℂ (A := Operator ι),
          smul_zero (M := ℂ) (A := Operator ι),true_and,false_and,and_false]

end FreeGroupFactorMain.WeightedFock

end

end OAI
