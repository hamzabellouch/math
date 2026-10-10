import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SectionGenericPerturbation
import OAI.Combinatorics.Chromatic.Walls.TriangularLinearSection

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open Classical
noncomputable section
variable {n:ℕ}
local instance triangularCommutativityRing : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance triangularCommutativityAddCommGroup : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularCommutativityAddGroup : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance triangularCommutativitySub : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub

lemma pureAnchor_pair (μ ν:Fin (n+1) → ℤ) : triangularOmega n (pureAnchor μ) (pureAnchor ν)=0 := by
  rw [pureAnchor,map_sum,AddMonoidHom.finsetSum_apply]
  simp only [map_zsmul,AddMonoidHom.zsmul_apply,anchor_pair_pure,zsmul_zero,Finset.sum_const_zero]

lemma pure_product_cyclic {k l:ℕ} (f:ElementaryExpr k) (g:ElementaryExpr l) (μ:Fin (n+1) → ℤ) :
    (triangularExpression (n:=n) f*triangularExpression (n:=n) g) (includeVertices (pureAnchor μ))=
      (triangularExpression (n:=n) g*triangularExpression (n:=n) f) (includeVertices (pureAnchor μ)) := by
  apply torus_target_cyclic LaurentRay.vUnit (extendedOmega n) extendedOmega_self
  intro r hr s hs he
  have hbridge:∀b,r.1 (.inr b)=0:=by
    intro b
    have H:=congrArg (fun x:Extended (Vertex n (Cell n))=>x.1 (.inr b)) he
    change r.1 (.inr b)+s.1 (.inr b)=pureAnchor μ (.inr b) at H
    rw [pureAnchor_apply_bridge] at H
    have h1:=triangularSeed_nonneg f r hr (.inr b)
    have h2:=triangularSeed_nonneg g s hs (.inr b)
    omega
  have hdual:=triangularSeed_dual_zero f r hr
  have hr':r=includeVertices (pureAnchor (fun a=>r.1 (.inl a))):=by
    apply Prod.ext
    · exact pureAnchor_of_bridges_zero r.1 hbridge
    · exact hdual
  rw [hr',extendedOmega_original,pureAnchor_pair]

lemma triangularPure_equal {N:ℕ} (f g:ElementaryExpr N)
    (hp:∀μ:Fin (n+1) → ℤ,triangularExpression f (includeVertices (pureAnchor μ))=
        triangularExpression g (includeVertices (pureAnchor μ))) :
    triangularExpression (n:=n) f=triangularExpression g := by
  have H:=triangularPure_detect (.add f (.neg g)) (by
    intro μ
    change triangularExpression f (includeVertices (pureAnchor μ))+
      -(triangularExpression g (includeVertices (pureAnchor μ)))=0
    rw [hp,add_neg_cancel])
  change triangularExpression f+ -(triangularExpression g)=0 at H
  exact sub_eq_zero.mp H

lemma triangularExpression_cast {k l:ℕ} (h:k=l) (f:ElementaryExpr k) :
    triangularExpression (n:=n) (h ▸ f)=triangularExpression f := by subst l; rfl

theorem triangularExpression_commute {k l:ℕ} (f:ElementaryExpr k) (g:ElementaryExpr l) :
    Commute (triangularExpression (n:=n) f) (triangularExpression g) := by
  let h:ElementaryExpr (k+l):=Nat.add_comm l k ▸ (.mul g f)
  have hh:triangularExpression (n:=n) h=triangularExpression g*triangularExpression f:=by
    exact triangularExpression_cast (Nat.add_comm l k) (.mul g f)
  have H:=triangularPure_equal (.mul f g) h (by intro μ; rw [hh]; exact pure_product_cyclic f g μ)
  exact H.trans hh
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry LaurentPositive WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in
lemma section_line_step (N : ℕ) (r : M) (F : CompletedPositive LaurentRay.vUnit Ω C)
    (walls : WallsPositiveThrough Ω C e N F) (X : PowerSeries (Torus LaurentRay.vUnit Ω))
    (ih : ∀j<N,∀h : Module.Dual ℝ E,TorusPositive Ω (coeff j (sectionValue LaurentRay.vUnit Ω C F (h.toAddMonoidHom.comp e) X)))
    (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) 0 (B.flip (e r)) k)
    (a : ℝ) (ha : a∈lineEvents (realRootsThrough e C N) (B.flip (e r)) k) :
    ∃ε>0,∀δ : ℝ,0<δ → δ<ε →
      Positive (coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+(a+δ) • B.flip (e r)).toAddMonoidHom.comp e) X) r) →
      Positive (coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+(a-δ) • B.flip (e r)).toAddMonoidHom.comp e) X) r) := by
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
  obtain ⟨p,d,hd,hdN,hp,hv,hgen⟩:=section_event_ray C e he L hdeg N (B.flip (e r)) k H a ha
  let h:=(k+a • B.flip (e r)).toAddMonoidHom.comp e
  let dir:=(B.flip (e r)).toAddMonoidHom.comp e
  obtain ⟨εp,hεp,Hεp⟩:=root_lex_epsilon C N h dir
  obtain ⟨εm,hεm,Hεm⟩:=root_lex_epsilon C N h (-dir)
  refine ⟨min εp εm,lt_min hεp hεm,?_⟩
  intro δ hδ hδε hplus
  have hδp:=lt_of_lt_of_le hδε (min_le_left _ _)
  have hδm:=lt_of_lt_of_le hδε (min_le_right _ _)
  let hpM:=(k+(a+δ) • B.flip (e r)).toAddMonoidHom.comp e
  let hmM:=(k+(a-δ) • B.flip (e r)).toAddMonoidHom.comp e
  have HC:=section_ray_crossing LaurentRay.vUnit Ω C F X N p h dir hpM hmM hgen
    (by simpa only [hpM,line_covector_add] using Hεp δ hδ hδp)
    (by simpa only [hmM,line_covector_sub] using Hεm δ hδ hδm)
  have HS : ∀n,0<n → n≤N → ∀m,coeff n (chartZero LaurentRay.vUnit Ω C h F).val m≠0 → OnPositiveRay p m:=by
    intro n hn hnN m hm
    by_contra hh
    exact hm ((hgen.ray_supported LaurentRay.vUnit Ω C F n hn hnN) m hh)
  have HI:=ray_increment_positive Ω C hΩ p r (chartZero LaurentRay.vUnit Ω C h F)
    (sectionValue LaurentRay.vUnit Ω C F hpM X) N HS
    (walls p d hd hp (k+a • B.flip (e r)) hgen)
    (fun j hj=>ih j hj (k+(a+δ) • B.flip (e r)))
  have Hpair : dir p=(Ω p r:ℝ):=hcomp p r
  have Hne : dir p≠0:=hv
  rcases lt_or_gt_of_ne Hne with hneg|hpos
  · have Hinc:=HI.2 (by exact_mod_cast (le_of_lt (Hpair ▸ hneg)))
    rw [←HC.2 hneg N le_rfl] at Hinc
    have HA:=Hinc.add hplus
    simpa only [hpM,hmM,sub_add_cancel] using HA
  · have Hinc:=HI.1 (by exact_mod_cast (le_of_lt (Hpair ▸ hpos)))
    rw [←HC.1 hpos N le_rfl] at Hinc
    have HA:=Hinc.add hplus
    simpa only [hpM,hmM,sub_add_cancel] using HA
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry FiniteEventTraversal LaurentPositive WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in

theorem positive_sections (F : CompletedPositive LaurentRay.vUnit Ω C)
    (incoming : PositiveIncomingPrescription Ω C F) (b : M)
    (X : PowerSeries (Torus LaurentRay.vUnit Ω)) (hX : ShiftGraded LaurentRay.vUnit Ω C b X)
    (hinc : ∀n,TorusPositive Ω (sectionIncoming LaurentRay.vUnit Ω C F b n X)) :
    ∀N,∀h : Module.Dual ℝ E,TorusPositive Ω (coeff N (sectionValue LaurentRay.vUnit Ω C F (h.toAddMonoidHom.comp e) X)) := by
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
  have walls:=positive_walls_through Ω C e he B hB hcomp L hdeg F incoming
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro h r
    obtain ⟨k,Hk,Heq⟩:=section_generic_offset LaurentRay.vUnit Ω C e L hdeg F X N h (B.flip (e r))
    rw [←Heq N le_rfl]
    let dir:=B.flip (e r)
    let S:=realRootsThrough e C N
    let events:=lineEvents S dir k
    let P (a : ℝ):=Positive (coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+a • dir).toAddMonoidHom.comp e) X) r)
    have h0 : (0:ℝ)∉events:=section_line_zero_not_event C e N dir k Hk
    have hstart : ∃a,0≤a ∧ (∀z∈events,z<a) ∧ P a:=by
      obtain ⟨a,ha,Hbound⟩:=finite_upper_bound events
      refine ⟨a,ha.le,Hbound,?_⟩
      change Positive (coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+a • dir).toAddMonoidHom.comp e) X) r)
      have Hpert:=section_incoming_perturbation LaurentRay.vUnit Ω C hΩ r
        (k.toAddMonoidHom.comp e) ((k+a • dir).toAddMonoidHom.comp e) F X N (by
          intro n hn m hm
          have HH:=far_line_lex S dir k a Hbound (e m) (realRoot_mem e C N n hn m hm)
          simp only [dir,LinearMap.flip_apply,hcomp] at HH
          exact HH)
      rw [Hpert]
      by_cases hr : HasRootDegree C N (r-b)
      · have HH:=hinc N r
        rw [sectionIncoming_apply,ite_eq_left hr] at HH
        exact HH
      · rw [(hX.sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω r)) N r hr]
        exact positive_zero
    have hcell : ∀a a',0≤a → 0≤a' → a∉events → a'∉events →
        (∀z∈events,a<z ↔ a'<z) → P a → P a':=by
      intro a a' ha ha' hna hna' Hside hpa
      have HH:=section_sign_congr_through LaurentRay.vUnit Ω C
        ((k+a • dir).toAddMonoidHom.comp e) ((k+a' • dir).toAddMonoidHom.comp e) F X N (by
          intro n hn hnN m hm
          exact line_cell_signs S dir k a a' hna hna' Hside (e m) (realRoot_mem e C N n hnN m hm))
      change Positive (coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+a' • dir).toAddMonoidHom.comp e) X) r)
      rw [←HH N le_rfl]
      exact hpa
    have hstep : ∀a∈events,0<a → ∃ε>0,∀δ : ℝ,0<δ → δ<ε → P (a+δ) → P (a-δ):=by
      intro a ha ha0
      exact section_line_step Ω C e he B hB hcomp L hdeg N r F (walls N) X ih k Hk a ha
    have HH:=descend events P hstart hcell hstep 0 (le_refl 0) h0
    simpa only [P,zero_smul,add_zero] using HH
include he hB hcomp hdeg in

theorem thetaValue_positive (F : CompletedPositive LaurentRay.vUnit Ω C)
    (incoming : PositiveIncomingPrescription Ω C F) (b : M) (h : Module.Dual ℝ E) :
    IntegralPositive Ω (thetaValue LaurentRay.vUnit Ω C F b (h.toAddMonoidHom.comp e)) := by
  intro N
  exact positive_sections Ω C e he B hB hcomp L hdeg F incoming b
    (thetaInitial LaurentRay.vUnit Ω C F b) (thetaInitial_graded LaurentRay.vUnit Ω C F b)
    (fun n=>by rw [thetaInitial_prescription]; exact completedPositive_C_X Ω b n) N h
end
end ElementaryPositivity.QuantumTorus

end

end OAI
