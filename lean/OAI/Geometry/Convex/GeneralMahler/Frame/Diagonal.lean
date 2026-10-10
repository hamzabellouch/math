import OAI.Geometry.Convex.GeneralMahler.LogDet
import OAI.Geometry.Convex.GeneralMahler.Frame.Selector

namespace OAI
/-! Borel choice of diagonalizing frame. Everything computed in a
diagonalization is defined on a full orthogonal matrix and its entries. -/
noncomputable section
open Set Filter MeasureTheory Metric Matrix Real
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m:ℕ}
abbrev Frm (m:ℕ) := ↥(unitary (Mat m))
namespace Frm
variable (u v:Frm m)
def loc (A:Mat m) := star u.val*A*u.val
def fixMat (A:Mat m) := u.val*A*star u.val
def eig (A:Mat m) := Matrix.diag (u.loc A)
def Dgn (A:Mat m) := u.loc A = Matrix.diagonal (u.eig A)
lemma m₁ : star u.val*u.val=1 := u.property.1
lemma m₂ : u.val*star u.val=1 := u.property.2

lemma loc_fix (A:Mat m) : u.loc (u.fixMat A)=A := by
  unfold loc fixMat
  simp only [mul_assoc]
  rw [u.m₁,mul_one,← mul_assoc,u.m₁,one_mul]
lemma fix_loc (A:Mat m) : u.fixMat (u.loc A)=A := by
  unfold loc fixMat; simp only [mul_assoc]
  rw [u.m₂,mul_one,← mul_assoc,u.m₂,one_mul]

lemma loc_inj : Function.Injective u.loc := fun _ b h =>
  (u.fix_loc _).symm.trans ((congrArg u.fixMat h).trans (u.fix_loc b))

lemma loc_mul (A B:Mat m) : u.loc (A*B)=u.loc A*u.loc B := by
  unfold loc; simp only [mul_assoc]
  rw [show u.val*(star u.val*(B*u.val))=B*u.val from by rw [← mul_assoc,u.m₂,one_mul]]

lemma loc_star (A:Mat m) : u.loc (star A)=star (u.loc A) := by
  unfold loc; rw [star_mul,star_mul,star_star,mul_assoc]
lemma loc_trace (A:Mat m) : trace (u.loc A) = trace A := by
  unfold loc; rw [trace_mul_comm,← mul_assoc,u.m₂,one_mul]
lemma loc_norm (A:Mat m) : ‖u.loc A‖=‖A‖ := by
  unfold loc; rw [CStarRing.norm_mul_mem_unitary _ u.property,CStarRing.norm_mem_unitary_mul]
  exact (star u).property

lemma loc_one : u.loc 1=1 := by unfold loc; rw [mul_one,u.m₁]
lemma loc_zero : u.loc 0=0 := by simp [loc]
lemma loc_sub (A B:Mat m) : u.loc (A-B)=u.loc A-u.loc B := by simp [loc,mul_sub,sub_mul]
lemma loc_add (A B:Mat m) : u.loc (A+B)=u.loc A+u.loc B := by simp [loc,mul_add,add_mul]
lemma loc_smul (a:ℝ) (A:Mat m) : u.loc (a• A)=a•u.loc A := by simp only [loc,mul_smul_comm,smul_mul_assoc]

lemma fix_mul_cross (A:Mat m) :
    star u.val*A*v.val=u.loc A*(star u.val*v.val) := by
  unfold loc; simp only [mul_assoc]
  rw [show u.val*(star u.val*v.val)=v.val from by rw [← mul_assoc,u.m₂,one_mul]]
lemma fix_mul_cross' (A:Mat m) :
    star u.val*A*v.val= (star u.val*v.val)*v.loc A := by
  unfold loc
  simp only [mul_assoc]
  rw [show v.val*(star v.val*(A*v.val))=A*v.val from by rw [← mul_assoc,v.m₂,one_mul]]

lemma cross_cancel (A B:Mat m) (h:star u.val*A*v.val= star u.val*B*v.val) : A=B := by
  have hi (A:Mat m) : u.val*(star u.val*A*v.val)*star v.val=A := by
    simp only [mul_assoc]; rw [v.m₂,mul_one,← mul_assoc,u.m₂,one_mul]
  exact (hi A).symm.trans ((congrArg (fun x=> u.val*x*star v.val) h).trans (hi B))

def specEval (A:Mat m) (f:ℝ→ℝ) := u.fixMat (Matrix.diagonal (fun i=> f (u.eig A i)))
lemma lSpecEq (A:Mat m) (f:ℝ→ℝ) : u.loc (u.specEval A f) = Matrix.diagonal (fun i=> f (u.eig A i)) :=
  u.loc_fix ..

lemma frame_cross {A:Mat m} (h:u.Dgn A) (g:v.Dgn A) (i j):
    u.eig A i*(star u.val*v.val) i j=(star u.val*v.val) i j*v.eig A j := by
  have hh := (u.fix_mul_cross v A).symm.trans (u.fix_mul_cross' v A)
  rw [show u.loc A=_ from h, show v.loc A=_ from g] at hh
  simpa only [Matrix.diagonal_mul,Matrix.mul_diagonal] using congrFun (congrFun hh i) j

lemma spec_unique {A:Mat m} (h:u.Dgn A) (g:v.Dgn A) (f:ℝ→ℝ) :
    u.specEval A f=v.specEval A f := by
  apply u.cross_cancel v
  rw [u.fix_mul_cross,u.fix_mul_cross',u.lSpecEq,v.lSpecEq]
  ext i j
  rw [Matrix.diagonal_mul,Matrix.mul_diagonal]
  have hh := u.frame_cross v h g i j
  rcases eq_or_ne ((star u.val*v.val) i j) 0 with hz|hz
  · simp [hz]
  have he : u.eig A i=v.eig A j := mul_right_cancel₀ hz (hh.trans (mul_comm ..))
  rw [he,mul_comm]

def eu {A:Mat m} (h:A.IsHermitian) : Frm m := h.eigenvectorUnitary
lemma eu_loc {A:Mat m} (h:A.IsHermitian) :
    (eu h).loc A= Matrix.diagonal h.eigenvalues := by
  open Unitary in
    have he := h.spectral_theorem
    simp only [conjStarAlgAut_apply,RCLike.ofReal_real_eq_id,Function.id_comp] at he
    exact (congrArg (eu h).loc he).trans ((eu h).loc_fix _)
lemma eu_eig {A:Mat m} (h:A.IsHermitian) : (eu h).eig A=h.eigenvalues := by rw [eig,eu_loc,Matrix.diag_diagonal]
lemma eu_d {A:Mat m} (h:A.IsHermitian) : (eu h).Dgn A := by rw [Dgn,eu_loc,eu_eig]

lemma loc_cfc {A:Mat m} (h:A.IsHermitian) (hu:u.Dgn A) (f:ℝ→ℝ) :
    u.loc (cfc f A)= Matrix.diagonal (fun i=>f (u.eig A i)) := by
  rw [← u.lSpecEq A]
  congr 1
  rw [u.spec_unique (eu h) hu (eu_d h) f,specEval,eu_eig]
  open Unitary in
    rw [Matrix.IsHermitian.cfc_eq h,Matrix.IsHermitian.cfc,conjStarAlgAut_apply]
    simp only [Function.comp_def]
    rfl

lemma cont_loc : Continuous (fun x:Mat m × Frm m=> x.2.loc x.1) := by
  let f := fun x:Mat m × Frm m=> x.2.val
  have hf : Continuous f := continuous_subtype_val.comp continuous_snd
  exact (hf.star.mul continuous_fst).mul hf
lemma cdiag : Continuous (Matrix.diag:Mat m→Fin m→ℝ) :=
  continuous_pi fun i=> (coeffMap i i).continuous
lemma cdiagonal : Continuous (Matrix.diagonal:(Fin m→ℝ)→Mat m) := by
  exact (Matrix.diagonalLinearMap (Fin m) ℝ ℝ).continuous_of_finiteDimensional
lemma Dgn_closed : IsClosed {p:Mat m×Frm m|p.2.Dgn p.1} :=
  isClosed_eq cont_loc (cdiagonal.comp (cdiag.comp cont_loc))

instance frame_cmp : CompactSpace (Frm m) := by
  change CompactSpace (↥((unitary (Mat m)):Set (Mat m)))
  rw [← isCompact_iff_compactSpace]
  let s : Set (Mat m) := unitary (Mat m)
  have hc : IsClosed s := (isClosed_eq (continuous_id.star.mul continuous_id)
    continuous_const).inter (isClosed_eq (continuous_id.mul continuous_id.star)
    continuous_const)
  exact (isCompact_closedBall 0 1).of_isClosed_subset hc
    (fun x hx=> by
      rw [mem_closedBall,dist_zero_right]
      rcases subsingleton_or_nontrivial (Mat m) with h | h
      · have h0 : x = 0 := @Subsingleton.elim _ h x 0
        rw [h0,norm_zero]
        exact zero_le_one
      · let : Nontrivial (Mat m) := h
        rw [CStarRing.norm_of_mem_unitary hx])

abbrev SH (m:ℕ) := {A:Mat m // A.IsHermitian}
lemma selectU :
    ∃ f:SH m→Frm m,Measurable f∧∀ A,(f A).Dgn A.val := by
  let F : Set (SH m × Frm m) := {x|x.2.Dgn x.1.val}
  have hs : IsClosed F :=
    (@Dgn_closed m).preimage ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have he (x:SH m) : ∃ y:Frm m,(x,y) ∈ F := ⟨eu x.property,eu_d x.property⟩
  exact Select.selector F he hs

def fr (A:SH m) : Frm m := selectU.choose A
lemma fr_m : Measurable (@fr m) := selectU.choose_spec.1
lemma fr_d (A:SH m) : (fr A).Dgn A.val := selectU.choose_spec.2 A
end Frm
end GeneralMahler

end

end OAI
