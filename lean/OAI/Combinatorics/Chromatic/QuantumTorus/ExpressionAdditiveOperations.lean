import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TriangularAnchorProjection
import OAI.Combinatorics.Chromatic.QuantumTorus.OrdinaryExpressionNaturality

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
noncomputable section

def ElementaryExpr.nscale {N:ℕ} (k:ℕ) (f:ElementaryExpr N) : ElementaryExpr N :=
  match k with
  | 0=>.zero N
  | k+1=>.add (nscale k f) f

def ElementaryExpr.zscale {N:ℕ} (z:ℤ) (f:ElementaryExpr N) : ElementaryExpr N :=
  match z with
  | .ofNat k=>nscale k f
  | .negSucc k=>.neg (nscale (k+1) f)

def ElementaryExpr.sumList {N:ℕ} : List (ElementaryExpr N) → ElementaryExpr N
  | []=>.zero N
  | f::fs=>.add f (sumList fs)

variable {σ:Type*} [Fintype σ] {R:Type*} [CommRing R]
lemma ElementaryExpr.ordinary_nscale {N:ℕ} (f:ElementaryExpr N) (k:ℕ) :
    (nscale k f).ordinary (σ:=σ) (R:=R)=k • f.ordinary := by
  induction k with
  | zero=>simp [nscale,ordinary]
  | succ k ih=>simp only [nscale,ordinary,ih,add_nsmul,one_nsmul]
lemma ElementaryExpr.ordinary_zscale {N:ℕ} (f:ElementaryExpr N) (z:ℤ) :
    (zscale z f).ordinary (σ:=σ) (R:=R)=z • f.ordinary := by
  cases z with
  | ofNat k=>simpa [zscale] using ordinary_nscale (σ:=σ) (R:=R) f k
  | negSucc k=>simp only [zscale,ordinary,ordinary_nscale,negSucc_zsmul]
lemma ElementaryExpr.ordinary_sumList {N:ℕ} (fs:List (ElementaryExpr N)) :
    (sumList fs).ordinary (σ:=σ) (R:=R)=(fs.map (fun f=>f.ordinary (σ:=σ) (R:=R))).sum := by
  induction fs with
  | nil=>rfl
  | cons f fs ih=>simp only [sumList,ordinary,List.map_cons,List.sum_cons,ih]
lemma ElementaryExpr.ordinary_symmetric {N:ℕ} (f:ElementaryExpr N) :
    (f.ordinary (σ:=σ) (R:=R)).IsSymmetric := by
  induction f with
  | zero=>intro e; exact map_zero _
  | one=>intro e; exact map_one _
  | atom k=>exact MvPolynomial.esymm_isSymmetric σ R k
  | add f g hf hg=>intro e; simp only [ordinary,map_add,hf e,hg e]
  | neg f hf=>intro e; simp only [ordinary,map_neg,hf e]
  | mul f g hf hg=>intro e; simp only [ordinary,map_mul,hf e,hg e]
end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance expressionAdditiveOperationsRing : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance expressionAdditiveOperationsAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance expressionAdditiveOperationsAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance expressionAdditiveOperationsAddGroup : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance expressionAdditiveOperationsSub : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub
lemma triangularExpression_nscale {N:ℕ} (f:ElementaryExpr N) (k:ℕ) :
    triangularExpression (n:=n) (f.nscale k)=k • triangularExpression f := by
  induction k with
  | zero=>simp [ElementaryExpr.nscale,triangularExpression,ElementaryExpr.eval]
  | succ k ih=>
    change triangularExpression (f.nscale k)+triangularExpression f=_
    rw [ih]
    apply Finsupp.ext
    intro m
    simp only [Finsupp.add_apply,Finsupp.smul_apply,add_smul,one_smul]
lemma triangularExpression_zscale {N:ℕ} (f:ElementaryExpr N) (z:ℤ) :
    triangularExpression (n:=n) (f.zscale z)=z • triangularExpression f := by
  apply Finsupp.ext
  intro m
  cases z with
  | ofNat k=>
    change triangularExpression (f.nscale k) m=_
    rw [triangularExpression_nscale]
    simp [Finsupp.smul_apply]
  | negSucc k=>
    change -(triangularExpression (f.nscale (k+1)) m)=_
    rw [triangularExpression_nscale]
    simp only [Finsupp.smul_apply,negSucc_zsmul]
lemma triangularExpression_sumList {N:ℕ} (fs:List (ElementaryExpr N)) :
    triangularExpression (n:=n) (.sumList fs)=(fs.map (triangularExpression (n:=n))).sum := by
  induction fs with
  | nil=>rfl
  | cons f fs ih=>change triangularExpression f+triangularExpression (.sumList fs)=_; rw [ih]; rfl

lemma triangularExpression_ordinary_equal {N:ℕ} (f g:ElementaryExpr N)
    (h:f.ordinary (σ:=Fin (n+1)) (R:=ℤ)=g.ordinary) : triangularExpression (n:=n) f=triangularExpression g := by
  have h':f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)=g.ordinary:=by
    rw [←ElementaryExpr.ordinary_map f (Int.castRingHom _),h,ElementaryExpr.ordinary_map]
  apply triangularPure_equal
  intro μ
  by_cases hn:∀a,0≤μ a
  · let d:Fin (n+1) →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun a=>(μ a).toNat)
    have hd:∀a,(d a:ℤ)=μ a:=fun a=>Int.toNat_of_nonneg (hn a)
    have he:includeVertices (pureAnchor μ)=anchorExponent d:=by
      change includeVertices (pureAnchor μ)=includeVertices (pureAnchor (fun a=>(d a:ℤ)))
      rw [show (fun a=>(d a:ℤ))=μ from funext hd]
    rw [he,triangularExpression_anchorCoeff,triangularExpression_anchorCoeff,h']
  · obtain ⟨a,ha⟩:=not_forall.mp hn
    have hz:∀e:ElementaryExpr N,triangularExpression e (includeVertices (pureAnchor μ))=0:=by
      intro e
      by_contra hh
      have H:0≤pureAnchor μ (.inl a):=triangularSeed_nonneg e _ (Finsupp.mem_support_iff.mpr hh) (.inl a)
      exact ha (by simpa only [pureAnchor_apply_anchor] using H)
    rw [hz,hz]
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
