import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationDegreeBound
import OAI.Combinatorics.Chromatic.GradedAlgebra.RealRootCoordinates
import OAI.Combinatorics.Chromatic.Walls.NamedIndependentRotation

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open Classical
noncomputable section

inductive ElementaryExpr : ℕ → Type
  | zero (k:ℕ) : ElementaryExpr k
  | one : ElementaryExpr 0
  | atom (k:ℕ) : ElementaryExpr k
  | add {k:ℕ} : ElementaryExpr k → ElementaryExpr k → ElementaryExpr k
  | neg {k:ℕ} : ElementaryExpr k → ElementaryExpr k
  | mul {k l:ℕ} : ElementaryExpr k → ElementaryExpr l → ElementaryExpr (k+l)

variable {M V:Type*} [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ)
local instance homogeneousElementaryExpressionsRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance homogeneousElementaryExpressionsAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance homogeneousElementaryExpressionsAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def ElementaryExpr.eval (w:V → M) : {k:ℕ} → ElementaryExpr k → Torus v Ω
  | _,.zero _ => 0
  | _,.one => 1
  | _,.atom k => independentElement v Ω w k
  | _,.add f g => eval w f+eval w g
  | _,.neg f => -eval w f
  | _,.mul f g => eval w f*eval w g

def CutSupported (ell:M →+ ℤ) (N:ℤ) (F:Torus v Ω) : Prop :=
  ∀m∈F.support,ell m≤N

lemma cutSupported_zero (ell:M →+ ℤ) (N:ℤ) : CutSupported v Ω ell N 0 := by
  simp [CutSupported]
lemma cutSupported_one (ell:M →+ ℤ) : CutSupported v Ω ell 0 1 := by
  intro m hm
  change m∈(Finsupp.single 0 (1:LaurentSeries ℚ)).support at hm
  have hh:m=0:=by simpa using hm
  subst m
  simp
lemma cutSupported_add (ell:M →+ ℤ) (N:ℤ) {F G:Torus v Ω}
    (hF:CutSupported v Ω ell N F) (hG:CutSupported v Ω ell N G) : CutSupported v Ω ell N (F+G) := by
  intro m hm
  rcases Finset.mem_union.mp (Finsupp.support_add hm) with hf|hg
  · exact hF m hf
  · exact hG m hg
lemma cutSupported_neg (ell:M →+ ℤ) (N:ℤ) {F:Torus v Ω}
    (hF:CutSupported v Ω ell N F) : CutSupported v Ω ell N (-F) := by
  intro m hm
  exact hF m (by simpa using hm)
lemma cutSupported_mul (ell:M →+ ℤ) (A B:ℤ) {F G:Torus v Ω}
    (hF:CutSupported v Ω ell A F) (hG:CutSupported v Ω ell B G) : CutSupported v Ω ell (A+B) (F*G) := by
  intro m hm
  have hh:=torus_mul_support v Ω F.support G.support F G (by rfl) (by rfl) hm
  obtain ⟨⟨a,b⟩,hab,rfl⟩:=Finset.mem_image.mp hh
  obtain ⟨ha,hb⟩:=Finset.mem_product.mp hab
  simpa only [map_add] using add_le_add (hF a ha) (hG b hb)

lemma independentElement_cutSupported (ell:M →+ ℤ) (w:V → M) (hw:∀x,ell (w x)≤1) (k:ℕ) :
    CutSupported v Ω ell k (independentElement v Ω w k) := by
  intro m hm
  have hn:independentElement v Ω w k m≠0:=Finsupp.mem_support_iff.mp hm
  simp only [independentElement,Finsupp.finsetSum_apply] at hn
  obtain ⟨s,_,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hn
  unfold independentTerm at hs
  split_ifs at hs with hc
  · have hms:m=∑x∈s,w x:=by
      by_contra h
      exact hs (Finsupp.single_eq_of_ne h)
    rw [hms,map_sum]
    calc
      ∑x∈s,ell (w x) ≤ ∑_x∈s,(1:ℤ) := Finset.sum_le_sum fun x _=>hw x
      _ = k := by simp [hc.2]
  · exact (hs rfl).elim

lemma ElementaryExpr.cutSupported {k:ℕ} (f:ElementaryExpr k) (ell:M →+ ℤ)
    (w:V → M) (hw:∀x,ell (w x)≤1) : CutSupported v Ω ell k (f.eval v Ω w) := by
  induction f with
  | zero k => exact cutSupported_zero v Ω ell k
  | one => exact cutSupported_one v Ω ell
  | atom k => exact independentElement_cutSupported v Ω ell w hw k
  | add f g hf hg => exact cutSupported_add v Ω ell _ hf hg
  | neg f hf => exact cutSupported_neg v Ω ell _ hf
  | mul f g hf hg => simpa only [eval,Nat.cast_add] using cutSupported_mul v Ω ell _ _ hf hg

open RationalFiber
lemma ElementaryExpr.rotation (hΩ:∀m,Ω m m=0) (ell:M →+ ℤ) (p:M) (hp:ell p=1)
    (w:V → M) (a b c:V) (hab:a≠b) (hbc:b≠c) (hac:a≠c)
    (hwb:w b=w a+p) (hpa:Ω p (w a)=1) (hpc:Ω p (w c)= -1)
    (hac0:Ω (w a) (w c)=0) (hw:∀x,x≠a → x≠b → x≠c → Ω p (w x)=0)
    {k:ℕ} (f:ElementaryExpr k) :
    pureAction v (complementOmega ell Ω) (complementAlpha ell p Ω)
      (embed v Ω hΩ ell p hp (f.eval v Ω (Function.update w b (w c+p))))=
        embed v Ω hΩ ell p hp (f.eval v Ω w) := by
  induction f with
  | zero k => simp [eval]
  | one => simp [eval]
  | atom k => exact independentElement_named_rotation v Ω hΩ ell p hp w a b c hab hbc hac hwb hpa hpc hac0 hw k
  | add f g hf hg => simp only [eval,map_add,hf,hg]
  | neg f hf => simp only [eval,map_neg,hf]
  | mul f g hf hg => simp only [eval,map_mul,hf,hg]
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
variable (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E)

def NearCut (h:Module.Dual ℝ E) : Prop :=
  |h (e (simpleRoot C pc))|<1/((mutationSize Ω C pc:ℝ)+1) ∧
    ∀i,i≠pc → h (e (simpleRoot C i))< -1

include hcoord in
lemma root_eval_split (h:Module.Dual ℝ E) {n:ℕ} {m:M} (hm:HasRootDegree C n m) :
    h (e m)=(coord m pc:ℝ)*h (e (simpleRoot C pc))+
      ∑i∈Finset.univ.erase pc,(coord m i:ℝ)*h (e (simpleRoot C i)) := by
  obtain ⟨d,hd,hc,he⟩:=root_coordinates C coord hcoord hm
  conv_lhs=>rw [←he,coefficient_simple_expansion C,map_sum,map_sum]
  simp only [map_zsmul,zsmul_eq_mul,hc]
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ pc),add_comm]

include hcoord in
lemma nearCut_fiber_negative (h:Module.Dual ℝ E) (hh:NearCut Ω C pc e h)
    (pos:Bool) {n:ℕ} (hn:0<n) {m:M} (hm:HasRootDegree C n m)
    (hb:m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) : h (e m)<0 := by
  have hp0:0≤(coord m pc:ℝ):=by exact_mod_cast hb.1
  have hnp:0<nonpDegree coord pc m:=by
    have H:=fiber_full_degree_bound Ω C coord hcoord pc pos hm hb
    have H0:=nonpDegree_root_nonneg C coord hcoord pc hm
    by_contra hnot
    have hz:nonpDegree coord pc m=0:=le_antisymm (le_of_not_gt hnot) H0
    rw [hz,mul_zero] at H
    omega
  have hnpR:0<(nonpDegree coord pc m:ℝ):=by exact_mod_cast hnp
  have HK:(coord m pc:ℝ)≤(mutationSize Ω C pc:ℝ)*(nonpDegree coord pc m:ℝ):=by
    exact_mod_cast hb.2.trans (fiberUpper_degree_bound Ω C coord hcoord pc pos hm)
  have Habs:(mutationSize Ω C pc:ℝ)*|h (e (simpleRoot C pc))|<1:=by
    have H0:(0:ℝ)<(mutationSize Ω C pc:ℝ)+1:=by positivity
    have H:= (lt_div_iff₀ H0).mp hh.1
    nlinarith [abs_nonneg (h (e (simpleRoot C pc)))]
  have Hsum:(∑i∈Finset.univ.erase pc,(coord m i:ℝ)*h (e (simpleRoot C i)))≤
      -(nonpDegree coord pc m:ℝ):=by
    have hc:∀i,0≤(coord m i:ℝ):=by
      obtain ⟨d,hd,hc,he⟩:=root_coordinates C coord hcoord hm
      intro i; rw [hc]; positivity
    change _≤-((∑i∈Finset.univ.erase pc,coord m i:ℤ):ℝ)
    push_cast
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have H:=mul_le_mul_of_nonneg_left (le_of_lt (hh.2 i (Finset.mem_erase.mp hi).1)) (hc i)
    simpa only [mul_neg,mul_one] using H
  have Hk:(coord m pc:ℝ)*h (e (simpleRoot C pc))≤
      (mutationSize Ω C pc:ℝ)*(nonpDegree coord pc m:ℝ)*|h (e (simpleRoot C pc))|:=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hp0).trans
      (mul_le_mul_of_nonneg_right HK (abs_nonneg _))
  rw [root_eval_split C coord hcoord pc e h hm]
  nlinarith [mul_lt_mul_of_pos_right Habs hnpR]

variable (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hcoord he hS hcomp hdeg in
lemma nearCut_noncut_wall (h:Module.Dual ℝ E) (hh:NearCut Ω C pc e h)
    (r:M) (dr:ℕ) (hdr:0<dr) (hr:HasRootDegree C dr r)
    (hg:∀N,RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos:Bool) (hp:cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val=1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero=>simpa only [coeff_zero_eq_constantCoeff,constantCoeff_one] using
      (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).property.1
  | succ n=>
    rw [coeff_one,ite_eq_right (Nat.succ_ne_zero _)]
    apply Finsupp.ext
    intro m
    change coeff (n+1) (chartZero LaurentRay.vUnit Ω C
      (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val m=0
    by_contra hm
    have HR:=chart_root_of_ne LaurentRay.vUnit Ω C _ _ _ hm
    have HB:=simple_fiber_bound Ω C coord hcoord pc e he S hS hcomp L hdeg r dr hdr hr h hg pos hp _ _ hm
    have Hneg:=nearCut_fiber_negative Ω C coord hcoord pc e h hh pos (by omega) HR HB
    have Hzero: h (e m)=0:=(chart_three_support LaurentRay.vUnit Ω C
      (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).2.1 n m hm
    linarith
end
end ElementaryPositivity.QuantumTorus

end

end OAI
