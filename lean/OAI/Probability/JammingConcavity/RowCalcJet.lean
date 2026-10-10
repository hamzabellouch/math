import Mathlib
import OAI.Probability.JammingConcavity.RowDerivativeApprox

namespace OAI

/-! Row Calc Jet. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open Set

namespace MicroscopicJamming.Hessian
 
structure CalcJet where
  val : ℝ → ℝ → ℝ
  dx : ℝ → ℝ → ℝ
  dxx : ℝ → ℝ → ℝ
  dt : ℝ → ℝ → ℝ
  valid : Jet val dx dxx dt
namespace CalcJet
def add (u v : CalcJet) : CalcJet :=
  ⟨fun t z => u.val t z+v.val t z,fun t z => u.dx t z+v.dx t z,
   fun t z => u.dxx t z+v.dxx t z,fun t z => u.dt t z+v.dt t z,u.valid.add v.valid⟩
def neg (u : CalcJet) : CalcJet :=
  ⟨fun t z => -u.val t z,fun t z => -u.dx t z,fun t z => -u.dxx t z,fun t z => -u.dt t z,u.valid.neg⟩
def mul (u v : CalcJet) : CalcJet :=
  ⟨fun t z => u.val t z*v.val t z,fun t z => u.dx t z*v.val t z+u.val t z*v.dx t z,
   fun t z => u.dxx t z*v.val t z+2*u.dx t z*v.dx t z+u.val t z*v.dxx t z,
   fun t z => u.dt t z*v.val t z+u.val t z*v.dt t z,u.valid.mul v.valid⟩
def const (c : ℝ) : CalcJet := ⟨fun _ _ => c,fun _ _ => 0,fun _ _ => 0,fun _ _ => 0,Jet.const c⟩
def smul (c : ℝ) (u : CalcJet) : CalcJet := (const c).mul u
def sq (u : CalcJet) : CalcJet := u.mul u
def rank : CalcJet := ⟨fun t _ => t,fun _ _ => 0,fun _ _ => 0,fun _ _ => 1,Jet.rank⟩
def coeff (a da : ℝ → ℝ) (ha : ∀ t∈Ico (0:ℝ) 1,HasDerivWithinAt a (da t) (Ici t) t) : CalcJet :=
  ⟨fun t _ => a t,fun _ _ => 0,fun _ _ => 0,fun t _ => da t,Jet.coeff ha⟩
def inv (u : CalcJet) (hu : ∀ t∈Icc (0:ℝ) 1,∀ x,u.val t x≠0) : CalcJet :=
  ⟨fun t x => (u.val t x)⁻¹,fun t x => -u.dx t x/(u.val t x)^2,
   fun t x => 2*(u.dx t x)^2/(u.val t x)^3-u.dxx t x/(u.val t x)^2,
   fun t x => -u.dt t x/(u.val t x)^2,u.valid.inv hu⟩
def gen (a b : ℝ → ℝ → ℝ) (u : CalcJet) (t x : ℝ) : ℝ := u.dt t x+a t x*u.dxx t x+b t x*u.dx t x
lemma gen_add (a b : ℝ → ℝ → ℝ) (u v : CalcJet) (t x : ℝ) :
    gen a b (u.add v) t x=gen a b u t x+gen a b v t x := by dsimp [gen,add]; ring
lemma gen_mul (a b : ℝ → ℝ → ℝ) (u v : CalcJet) (t x : ℝ) :
    gen a b (u.mul v) t x=gen a b u t x*v.val t x+u.val t x*gen a b v t x+2*a t x*u.dx t x*v.dx t x := by
  dsimp [gen,mul]; ring
lemma gen_inv (a b : ℝ → ℝ → ℝ) (u : CalcJet) (hu : ∀ t∈Icc (0:ℝ) 1,∀ x,u.val t x≠0)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : ℝ) :
    gen a b (u.inv hu) t x= -gen a b u t x/(u.val t x)^2+2*a t x*(u.dx t x)^2/(u.val t x)^3 := by
  dsimp [gen,inv]
  field_simp [hu t ht x]
  ring
end CalcJet
end MicroscopicJamming.Hessian

 
open Set Filter
open scoped Topology BigOperators

namespace MicroscopicJamming.Hessian
open Higher Parameter

lemma jet_of_evolution {f d : ℝ → ℝ → ℝ} (hf : JointSpatialSmooth (Icc 0 1) f)
    (ht : ∀ t∈Ico (0:ℝ) 1,∀ x,HasDerivWithinAt (fun s => f s x) (d t x) (Ici t) t) :
    Jet f (fun t => iteratedDeriv 1 (f t)) (fun t => iteratedDeriv 2 (f t)) d := by
  refine ⟨fun t htt x => ?_,fun t htt x => ?_,ht⟩
  · simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using ((hf.1 t htt).differentiable (by simp) x).hasDerivAt
  · simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using (((hf.jet 1).1 t htt).differentiable (by simp) x).hasDerivAt

structure EvolutionSystem (A B : ℝ → ℝ) (f v g : ℝ → ℝ → ℝ) : Prop where
  fs : JointSpatialSmooth (Icc 0 1) f
  vs : JointSpatialSmooth (Icc 0 1) v
  gs : JointSpatialSmooth (Icc 0 1) g
  ft : ∀ n,∀ t∈Ico (0:ℝ) 1,∀ x,HasDerivWithinAt (fun s => iteratedDeriv n (f s) x)
    (ftime (A t) t (fun k => iteratedDeriv k (f t) x) n) (Ici t) t
  vt : ∀ n,∀ t∈Ico (0:ℝ) 1,∀ x,HasDerivWithinAt (fun s => iteratedDeriv n (v s) x)
    (vtime (A t) (B t) t (fun k => iteratedDeriv k (f t) x) (fun k => iteratedDeriv k (v t) x) n) (Ici t) t
  gt : ∀ t∈Ico (0:ℝ) 1,∀ x,HasDerivWithinAt (fun s => g s x)
    (gtime (A t) (B t) t (fun k => iteratedDeriv k (f t) x) (fun k => iteratedDeriv k (v t) x)
      (fun k => iteratedDeriv k (g t) x)) (Ici t) t

lemma actual_evolution {r : ℝ} (hr : 0<r) {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F) :
    EvolutionSystem A B (F 0) (pjet F 0) (pjet2 F 0) := by
  have h0 : (0:ℝ)∈Ioo (-r) r := ⟨by linarith,hr⟩
  have hj := hf.parameter_jets hr
  have htime := hf.parameter_time_jets hr
  have hs := hf.smooth 0 h0
  have hG := hs.row_rhs hf.Acont continuousOn_id
  have hft := evolution_all_jets (by norm_num : (0:ℝ)<1) (hs.2 0) hG.2 hs.1 hG.1
    (fun t ht x => by simpa only [zero_mul,add_zero,id_eq] using hf.time 0 h0 t ht x)
  refine ⟨hs,hj.1.1,hj.2.1,?_,?_,?_⟩
  · intro n t ht x
    simpa only [iterated_rhs (A t) t (hs.1 t ⟨ht.1,ht.2.le⟩) n x,id_eq] using hft n t ht x
  · intro n t ht x
    simpa only [iterated_linearRhs (hs.1 t ⟨ht.1,ht.2.le⟩) (hj.1.1.1 t ⟨ht.1,ht.2.le⟩) n x]
      using htime.1 n t ht x
  · intro t ht x
    exact htime.2 0 t ht x

namespace EvolutionSystem
variable {A B : ℝ → ℝ} {f v g : ℝ → ℝ → ℝ} (h : EvolutionSystem A B f v g)
def fj (n : ℕ) : CalcJet where
  val := fun t => iteratedDeriv n (f t)
  dx := fun t => iteratedDeriv (n+1) (f t)
  dxx := fun t => iteratedDeriv (n+2) (f t)
  dt := fun t x => ftime (A t) t (fun k => iteratedDeriv k (f t) x) n
  valid := by
    simpa only [iteratedDeriv_iteratedDeriv,Nat.add_comm 1,Nat.add_comm 2] using jet_of_evolution (h.fs.jet n) (h.ft n)
def vj (n : ℕ) : CalcJet where
  val := fun t => iteratedDeriv n (v t)
  dx := fun t => iteratedDeriv (n+1) (v t)
  dxx := fun t => iteratedDeriv (n+2) (v t)
  dt := fun t x => vtime (A t) (B t) t (fun k => iteratedDeriv k (f t) x) (fun k => iteratedDeriv k (v t) x) n
  valid := by
    simpa only [iteratedDeriv_iteratedDeriv,Nat.add_comm 1,Nat.add_comm 2] using jet_of_evolution (h.vs.jet n) (h.vt n)
def gj : CalcJet where
  val := g
  dx := fun t => iteratedDeriv 1 (g t)
  dxx := fun t => iteratedDeriv 2 (g t)
  dt := fun t x => gtime (A t) (B t) t (fun k => iteratedDeriv k (f t) x) (fun k => iteratedDeriv k (v t) x) (fun k => iteratedDeriv k (g t) x)
  valid := jet_of_evolution h.gs h.gt

def drift (t x : ℝ) : ℝ := 2*A t*t*iteratedDeriv 1 (f t) x

def ell (E : CalcJet) : CalcJet := (h.vj 1).add
  ((CalcJet.smul (1/2) E).mul ((h.fj 3).add (CalcJet.smul 2 (CalcJet.rank.mul ((h.fj 1).mul (h.fj 2))))))
def mu : CalcJet := (h.fj 4).add
  ((CalcJet.smul 2 (CalcJet.rank.mul ((h.fj 2).sq))).add
    ((CalcJet.smul 4 (CalcJet.rank.mul ((h.fj 1).mul (h.fj 3)))).add
      (CalcJet.smul 4 (CalcJet.rank.sq.mul (((h.fj 1).sq).mul (h.fj 2))))))
def mainJet (E : CalcJet) : CalcJet := (CalcJet.smul 2 h.gj).add
  ((E.mul ((h.vj 2).add (CalcJet.smul 2 (CalcJet.rank.mul ((h.fj 1).mul (h.vj 1)))))).add
    ((CalcJet.smul (1/4) E.sq).mul h.mu))
end EvolutionSystem
end MicroscopicJamming.Hessian

 
open Set

namespace MicroscopicJamming.Hessian
namespace EvolutionSystem
variable {A B : ℝ → ℝ} {f v g : ℝ → ℝ → ℝ} (h : EvolutionSystem A B f v g)
variable {η : ℝ → ℝ} (hη : ∀ t∈Ico (0:ℝ) 1,HasDerivWithinAt η (2*B t) (Ici t) t)
local notation "E" => CalcJet.coeff η (fun t => 2*B t) hη
lemma gen_ell (t x : ℝ) :
    CalcJet.gen (fun t _ => A t) (drift (A:=A) (f:=f)) (h.ell E) t x =
      η t*iteratedDeriv 1 (f t) x*iteratedDeriv 2 (f t) x-
        2*A t*t*iteratedDeriv 2 (f t) x*(h.ell E).val t x := by
  dsimp [CalcJet.gen,ell,fj,vj,drift,CalcJet.add,CalcJet.mul,CalcJet.smul,CalcJet.rank,CalcJet.const,CalcJet.coeff]
  simp only [ftime,vtime,Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,Nat.choose_self]
  norm_num [Nat.choose]
  ring
lemma gen_curvature (t x : ℝ) :
    CalcJet.gen (fun t _ => A t) (drift (A:=A) (f:=f)) (h.fj 2).neg t x =
      2*A t*t*((h.fj 2).neg.val t x)^2 := by
  dsimp [CalcJet.gen,fj,drift,CalcJet.neg]
  simp only [ftime,Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,Nat.choose_self]
  norm_num [Nat.choose]
  ring
lemma gen_main (t x : ℝ) :
    CalcJet.gen (fun t _ => A t) (drift (A:=A) (f:=f)) (h.mainJet E) t x =
      2*η t*iteratedDeriv 1 (f t) x*(h.ell E).val t x-
      2*A t*t*((h.ell E).val t x)^2+η t^2*(iteratedDeriv 2 (f t) x)^2/2 := by
  dsimp [CalcJet.gen,mainJet,mu,ell,fj,vj,gj,drift,CalcJet.add,CalcJet.mul,CalcJet.smul,CalcJet.sq,CalcJet.rank,CalcJet.const,CalcJet.coeff]
  simp only [ftime,vtime,gtime,Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,Nat.choose_self]
  norm_num [Nat.choose]
  ring
end EvolutionSystem
end MicroscopicJamming.Hessian

 
open Set

namespace MicroscopicJamming.Hessian
open Higher
namespace CalcJet
def Controlled (u : CalcJet) : Prop :=
  ContinuousOn (fun p : ℝ × ℝ => u.val p.1 p.2) (Icc 0 1 ×ˢ univ) ∧
  UniformPolynomialGrowth (Icc 0 1) u.val
lemma Controlled.add {u v : CalcJet} (hu : Controlled u) (hv : Controlled v) : Controlled (u.add v) :=
  ⟨hu.1.add hv.1,hu.2.add hv.2⟩
lemma Controlled.mul {u v : CalcJet} (hu : Controlled u) (hv : Controlled v) : Controlled (u.mul v) :=
  ⟨hu.1.mul hv.1,hu.2.mul hv.2⟩
lemma controlled_const (c : ℝ) : Controlled (const c) :=
  ⟨continuousOn_const,UniformPolynomialGrowth.const _ c⟩
lemma Controlled.smul {u : CalcJet} (hu : Controlled u) (c : ℝ) : Controlled (smul c u) :=
  (controlled_const c).mul hu
lemma Controlled.neg {u : CalcJet} (hu : Controlled u) : Controlled u.neg :=
  ⟨hu.1.neg,by simpa only [neg_one_mul,CalcJet.neg] using hu.2.const_mul (-1)⟩
lemma Controlled.sq {u : CalcJet} (hu : Controlled u) : Controlled u.sq := hu.mul hu
lemma controlled_coeff {a da : ℝ → ℝ} (ha : ∀ t∈Ico (0:ℝ) 1,HasDerivWithinAt a (da t) (Ici t) t)
    (hc : ContinuousOn a (Icc 0 1)) : Controlled (coeff a da ha) := by
  refine ⟨hc.comp continuousOn_fst (fun p hp => hp.1),?_⟩
  obtain ⟨T,hT,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1)) hc.abs
  exact ⟨0,|a T|,abs_nonneg _,fun t ht x => by simpa only [CalcJet.coeff,pow_zero,mul_one] using (show |a t|≤|a T| from hm ht)⟩
lemma controlled_rank : Controlled rank := by
  refine ⟨continuousOn_fst,0,1,by norm_num,fun t ht x => ?_⟩
  simpa only [rank,pow_zero,mul_one,abs_of_nonneg ht.1] using ht.2
lemma Controlled.inv {u : CalcJet} (hu : Controlled u) {c : ℝ} (hc : 0<c)
    (hl : ∀ t∈Icc (0:ℝ) 1,∀ x,c≤u.val t x) :
    Controlled (u.inv (fun t ht x => ne_of_gt (hc.trans_le (hl t ht x)))) := by
  refine ⟨hu.1.inv₀ (fun p hp => ne_of_gt (hc.trans_le (hl p.1 hp.1 p.2))),0,c⁻¹,by positivity,?_⟩
  intro t ht x
  simp only [CalcJet.inv,pow_zero,mul_one,abs_inv,abs_of_pos (hc.trans_le (hl t ht x))]
  exact inv_anti₀ hc (hl t ht x)
lemma nonpos_of_gen_nonneg {u : CalcJet} (hu : Controlled u) {a b : ℝ → ℝ → ℝ} {A K : ℝ}
    (hA : 0≤A) (hK : 0≤K) (ha : ∀ t∈Icc (0:ℝ) 1,∀ x,0≤a t x ∧ a t x≤A)
    (hb : ∀ t∈Icc (0:ℝ) 1,∀ x,|b t x|≤K*(1+|x|))
    (hg : ∀ t∈Ico (0:ℝ) 1,∀ x,0≤gen a b u t x)
    (hterm : ∀ x,u.val 1 x≤0) : ∀ t∈Icc (0:ℝ) 1,∀ x,u.val t x≤0 := by
  have hx : ∀ t∈Icc (0:ℝ) 1,Differentiable ℝ (u.val t) ∧ Differentiable ℝ (deriv (u.val t)) := by
    intro t ht
    refine ⟨fun x => (u.valid.x t ht x).differentiableAt,?_⟩
    rw [u.valid.spatial_deriv ht]
    exact fun x => (u.valid.xx t ht x).differentiableAt
  apply VariableDiffusion.backward_polynomial_comparison (by norm_num : (0:ℝ)<1) hK hA hu.1
    hx u.valid.time ha hb hu.2 _ hterm
  intro t ht x _
  rw [u.valid.spatial_deriv2 ⟨ht.1,ht.2.le⟩,u.valid.spatial_deriv ⟨ht.1,ht.2.le⟩]
  exact hg t ht x
end CalcJet
end MicroscopicJamming.Hessian

 
open Set

namespace MicroscopicJamming.Hessian
lemma gen_square_quotient {a b : ℝ → ℝ → ℝ} (l k : CalcJet)
    (hk : ∀ t∈Icc (0:ℝ) 1,∀ x,k.val t x≠0) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : ℝ) :
    CalcJet.gen a b (l.sq.mul (k.inv hk)) t x =
      2*l.val t x/k.val t x*CalcJet.gen a b l t x-
      (l.val t x)^2/(k.val t x)^2*CalcJet.gen a b k t x+
      2*a t x/k.val t x*(l.dx t x-l.val t x*k.dx t x/k.val t x)^2 := by
  rw [CalcJet.gen_mul,CalcJet.gen_inv a b k hk ht x]
  change CalcJet.gen a b (l.mul l) t x*(k.val t x)⁻¹+
    (l.val t x*l.val t x)*(-CalcJet.gen a b k t x/(k.val t x)^2+2*a t x*(k.dx t x)^2/(k.val t x)^3)+
    2*a t x*(l.dx t x*l.val t x+l.val t x*l.dx t x)*(-k.dx t x/(k.val t x)^2)=_
  rw [CalcJet.gen_mul]
  field_simp [hk t ht x]
  ring
namespace EvolutionSystem
variable {A B : ℝ → ℝ} {f v g : ℝ → ℝ → ℝ} (h : EvolutionSystem A B f v g)
variable {η : ℝ → ℝ} (hη : ∀ t∈Ico (0:ℝ) 1,HasDerivWithinAt η (2*B t) (Ici t) t)
local notation "E" => CalcJet.coeff η (fun t => 2*B t) hη
lemma gen_corrected (hk : ∀ t∈Icc (0:ℝ) 1,∀ x,(h.fj 2).neg.val t x≠0)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : ℝ) :
    CalcJet.gen (fun t _ => A t) (drift (A:=A) (f:=f))
      ((h.mainJet E).add ((h.ell E).sq.mul ((h.fj 2).neg.inv hk))) t x =
      η t^2*(iteratedDeriv 2 (f t) x)^2/2+
      2*A t/(h.fj 2).neg.val t x*((h.ell E).dx t x-
        (h.ell E).val t x*(h.fj 2).neg.dx t x/(h.fj 2).neg.val t x)^2 := by
  rw [CalcJet.gen_add,gen_square_quotient _ _ hk ht x,h.gen_main hη,h.gen_ell hη,h.gen_curvature]
  have hn : iteratedDeriv 2 (f t) x≠0 := by simpa only [fj,CalcJet.neg,neg_ne_zero] using hk t ht x
  simp only [fj,CalcJet.neg]
  field_simp
  ring
end EvolutionSystem
end MicroscopicJamming.Hessian

 
open Set

namespace MicroscopicJamming.Hessian
open Higher Parameter
namespace EvolutionSystem
variable {A B : ℝ → ℝ} {f v g : ℝ → ℝ → ℝ} (h : EvolutionSystem A B f v g)
lemma controlled_fj (hpoly : ∀ n,UniformPolynomialGrowth (Icc 0 1) (fun t => iteratedDeriv n (f t))) (n : ℕ) :
    CalcJet.Controlled (h.fj n) := ⟨h.fs.2 n,hpoly n⟩
lemma controlled_vj (hpoly : ∀ n,UniformPolynomialGrowth (Icc 0 1) (fun t => iteratedDeriv n (v t))) (n : ℕ) :
    CalcJet.Controlled (h.vj n) := ⟨h.vs.2 n,hpoly n⟩
lemma controlled_gj (hpoly : UniformPolynomialGrowth (Icc 0 1) g) :
    CalcJet.Controlled h.gj := ⟨h.gs.2 0,hpoly⟩
lemma controlled_ell {E : CalcJet} (he : E.Controlled)
    (hf : ∀ n,UniformPolynomialGrowth (Icc 0 1) (fun t => iteratedDeriv n (f t)))
    (hv : ∀ n,UniformPolynomialGrowth (Icc 0 1) (fun t => iteratedDeriv n (v t))) :
    (h.ell E).Controlled :=
  (h.controlled_vj hv 1).add ((he.smul (1/2)).mul
    ((h.controlled_fj hf 3).add ((CalcJet.controlled_rank.mul
      ((h.controlled_fj hf 1).mul (h.controlled_fj hf 2))).smul 2)))
lemma controlled_mu
    (hf : ∀ n,UniformPolynomialGrowth (Icc 0 1) (fun t => iteratedDeriv n (f t))) : h.mu.Controlled :=
  (h.controlled_fj hf 4).add (((CalcJet.controlled_rank.mul ((h.controlled_fj hf 2).sq)).smul 2).add
    (((CalcJet.controlled_rank.mul ((h.controlled_fj hf 1).mul (h.controlled_fj hf 3))).smul 4).add
      ((CalcJet.controlled_rank.sq.mul (((h.controlled_fj hf 1).sq).mul (h.controlled_fj hf 2))).smul 4)))
lemma controlled_main {E : CalcJet} (he : E.Controlled)
    (hf : ∀ n,UniformPolynomialGrowth (Icc 0 1) (fun t => iteratedDeriv n (f t)))
    (hv : ∀ n,UniformPolynomialGrowth (Icc 0 1) (fun t => iteratedDeriv n (v t)))
    (hg : UniformPolynomialGrowth (Icc 0 1) g) : (h.mainJet E).Controlled :=
  ((h.controlled_gj hg).smul 2).add
    ((he.mul ((h.controlled_vj hv 2).add
      ((CalcJet.controlled_rank.mul ((h.controlled_fj hf 1).mul (h.controlled_vj hv 1))).smul 2))).add
        ((he.sq.smul (1/4)).mul (h.controlled_mu hf)))
end EvolutionSystem
end MicroscopicJamming.Hessian

 
open Set

namespace MicroscopicJamming.Hessian.CalcJet
lemma nonpos_of_reaction_nonneg {u : CalcJet} (hu : Controlled u) {a b r : ℝ → ℝ → ℝ} {A K R : ℝ}
    (hA : 0≤A) (hK : 0≤K) (hR : 0≤R)
    (ha : ∀ t∈Icc (0:ℝ) 1,∀ x,0≤a t x ∧ a t x≤A)
    (hb : ∀ t∈Icc (0:ℝ) 1,∀ x,|b t x|≤K*(1+|x|))
    (hr : ∀ t∈Ico (0:ℝ) 1,∀ x,r t x≤R)
    (hg : ∀ t∈Ico (0:ℝ) 1,∀ x,0≤gen a b u t x+r t x*u.val t x)
    (hterm : ∀ x,u.val 1 x≤0) : ∀ t∈Icc (0:ℝ) 1,∀ x,u.val t x≤0 := by
  have hx : ∀ t∈Icc (0:ℝ) 1,Differentiable ℝ (u.val t) ∧ Differentiable ℝ (deriv (u.val t)) := by
    intro t ht
    refine ⟨fun x => (u.valid.x t ht x).differentiableAt,?_⟩
    rw [u.valid.spatial_deriv ht]
    exact fun x => (u.valid.xx t ht x).differentiableAt
  have hh := VariableDiffusion.backward_reaction_source_upper (H:=0) (S:=0)
    (by norm_num : (0:ℝ)<1) hK hA hR (by norm_num) (by norm_num) hu.1 hx u.valid.time
    ha hb hu.2 hr (fun t ht x => ?_) hterm
  · simpa only [zero_mul,add_zero] using hh
  · rw [u.valid.spatial_deriv2 ⟨ht.1,ht.2.le⟩,u.valid.spatial_deriv ⟨ht.1,ht.2.le⟩]
    simpa only [neg_zero,CalcJet.gen] using hg t ht x
end MicroscopicJamming.Hessian.CalcJet

 
open Set

namespace MicroscopicJamming.Hessian
lemma strict_negative_curvature (u : CalcJet) (hu : u.Controlled)
    {a b c : ℝ → ℝ → ℝ} {A K C H ρ : ℝ}
    (hA : 0≤A) (hK : 0≤K) (hC : 0≤C) (hH : 0≤H) (hρ : 0<ρ)
    (ha : ∀ t∈Icc (0:ℝ) 1,∀ x,0≤a t x ∧ a t x≤A)
    (hb : ∀ t∈Icc (0:ℝ) 1,∀ x,|b t x|≤K*(1+|x|))
    (hc : ∀ t∈Icc (0:ℝ) 1,∀ x,0≤c t x ∧ c t x≤C)
    (hh : ∀ t∈Icc (0:ℝ) 1,∀ x,|u.val t x|≤H)
    (hp : ∀ t∈Ico (0:ℝ) 1,∀ x,CalcJet.gen a b u t x = -c t x*(u.val t x)^2)
    (hterm : ∀ x,u.val 1 x≤-ρ) :
    ∃ δ : ℝ,0<δ ∧ ∀ t∈Icc (0:ℝ) 1,∀ x,δ≤-u.val t x := by
  let R := C*H
  have hR : 0≤R := mul_nonneg hC hH
  have hr (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : ℝ) : |c t x*u.val t x|≤R := by
    rw [abs_mul,abs_of_nonneg (hc t ht x).1]
    exact mul_le_mul (hc t ht x).2 (hh t ht x) (abs_nonneg _) hC
  have hnon := CalcJet.nonpos_of_reaction_nonneg (r:=fun t x => c t x*u.val t x) hu hA hK hR ha hb
    (fun t ht x => (le_abs_self _).trans (hr t ⟨ht.1,ht.2.le⟩ x))
    (fun t ht x => by rw [hp t ht x]; nlinarith) (fun x => (hterm x).trans (by linarith))
  let φ : ℝ → ℝ := fun t => ρ*Real.exp (R*(t-1))
  have hφ (t : ℝ) : HasDerivAt φ (R*φ t) t := by
    convert ((((hasDerivAt_id t).sub_const 1).const_mul R).exp.const_mul ρ) using 1 <;>
      first | rfl | (dsimp [φ]; ring)
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr (fun t => (hφ t).continuousAt)
  let p := CalcJet.coeff φ (fun t => R*φ t) (fun t _ => (hφ t).hasDerivWithinAt)
  have hcV : (p.add u).Controlled := (CalcJet.controlled_coeff _ hφc.continuousOn).add hu
  have hV := CalcJet.nonpos_of_reaction_nonneg (a:=a) (b:=b) (r:=fun t x => c t x*u.val t x)
    hcV hA hK (R:=0) (by norm_num) ha hb
    (fun t ht x => mul_nonpos_of_nonneg_of_nonpos (hc t ⟨ht.1,ht.2.le⟩ x).1 (hnon t ⟨ht.1,ht.2.le⟩ x))
    (fun t ht x => ?_) (fun x => ?_)
  · refine ⟨ρ*Real.exp (-R),by positivity,fun t ht x => ?_⟩
    have hv := hV t ht x
    change φ t+u.val t x≤0 at hv
    have he : ρ*Real.exp (-R)≤φ t := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hρ.le
      nlinarith [mul_nonneg hR ht.1]
    linarith
  · rw [CalcJet.gen_add,hp t ht x]
    change 0≤R*φ t+a t x*0+b t x*0+-c t x*(u.val t x)^2+
      (c t x*u.val t x)*(φ t+u.val t x)
    have hr' := (abs_le.mp (hr t ⟨ht.1,ht.2.le⟩ x)).1
    have hφp : 0≤φ t := mul_nonneg hρ.le (Real.exp_nonneg _)
    nlinarith [mul_nonneg (show 0≤R+c t x*u.val t x by linarith) hφp]
  · change φ 1+u.val 1 x≤0
    have hp1 : φ 1=ρ := by simp [φ]
    rw [hp1]
    linarith [hterm x]
end MicroscopicJamming.Hessian

 
open Set

namespace MicroscopicJamming.Hessian
open Parameter Higher
lemma actual_second_nonpos {r : ℝ} (hr : 0<r) {A B η : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F)
    (hη : ∀ t∈Ico (0:ℝ) 1,HasDerivWithinAt η (2*B t) (Ici t) t)
    (hηc : ContinuousOn η (Icc 0 1)) (hη0 : η 0=0) (hη1 : η 1=0)
    {ρ : ℝ} (hρ : 0<ρ) (htcurv : ∀ x,iteratedDeriv 2 (F 0 1) x≤-ρ) :
    deriv (deriv (fun e => F e 0 0)) 0≤0 := by
  have h0 : (0:ℝ)∈Ioo (-r) r := ⟨by linarith,hr⟩
  let h := actual_evolution hr hf
  let E := CalcJet.coeff η (fun t => 2*B t) hη
  let a : ℝ → ℝ → ℝ := fun t _ => A t
  let b := EvolutionSystem.drift (A:=A) (f:=F 0)
  obtain ⟨D,hD,hcoef,_⟩ := hf.coeff
  obtain ⟨L,hL,hlo⟩ := hf.lower
  obtain ⟨H,hH,hh⟩ := hf.higher 2 (by norm_num)
  have ha (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : ℝ) : 0≤a t x ∧ a t x≤D := by
    simpa only [a,zero_mul,add_zero] using hcoef 0 h0 t ht
  have hb (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : ℝ) : |b t x|≤(2*D*L)*(1+|x|) := by
    have hat : 0≤A t := (ha t ht x).1
    have hd : A t≤D := (ha t ht x).2
    have hfac : |2*A t*t|≤2*D := by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hat) ht.1)]
      nlinarith [mul_nonneg hat (sub_nonneg.mpr ht.2)]
    change |(2*A t*t)*iteratedDeriv 1 (F 0 t) x|≤_
    rw [abs_mul]
    have hl := (hlo 0 h0 t ht x).2
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,mul_assoc] using
      mul_le_mul hfac hl (abs_nonneg _) (by positivity : 0≤2*D)
  have hpF (n : ℕ) : UniformPolynomialGrowth (Icc 0 1) (fun t => iteratedDeriv n (F 0 t)) :=
    (hf.poly.bounds n).individual h0
  have hcF := h.controlled_fj hpF 2
  have hcc (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : ℝ) : 0≤2*A t*t ∧ 2*A t*t≤2*D := by
    constructor
    · exact mul_nonneg (mul_nonneg (by norm_num) (ha t ht x).1) ht.1
    · nlinarith [mul_nonneg (ha t ht x).1 (sub_nonneg.mpr ht.2),(ha t ht x).2]
  have hP (t : ℝ) (ht : t∈Ico (0:ℝ) 1) (x : ℝ) :
      CalcJet.gen a b (h.fj 2) t x= -(2*A t*t)*((h.fj 2).val t x)^2 := by
    have hn : CalcJet.gen a b (h.fj 2).neg t x = -CalcJet.gen a b (h.fj 2) t x := by
      dsimp [CalcJet.gen,CalcJet.neg]; ring
    have hh' := h.gen_curvature t x
    rw [hn] at hh'
    change -CalcJet.gen a b (h.fj 2) t x=2*A t*t*(-(h.fj 2).val t x)^2 at hh'
    nlinarith
  obtain ⟨δ,hδ,hk⟩ := strict_negative_curvature (a:=a) (b:=b) (c:=fun t _ => 2*A t*t)
    (h.fj 2) hcF hD (show 0≤2*D*L by positivity) (show 0≤2*D by positivity) hH hρ ha hb hcc
    (fun t ht x => hh 0 h0 t ht x) hP htcurv
  have hnonzero : ∀ t∈Icc (0:ℝ) 1,∀ x,(h.fj 2).neg.val t x≠0 :=
    fun t ht x => ne_of_gt (hδ.trans_le (hk t ht x))
  have hparam := hf.parameter_growth hr
  have hterm := hf.parameter_terminal hr
  have hEc : E.Controlled := CalcJet.controlled_coeff hη hηc
  let J := (h.mainJet E).add ((h.ell E).sq.mul ((h.fj 2).neg.inv hnonzero))
  have hJc : J.Controlled :=
    (h.controlled_main hEc hpF hparam.1 (hparam.2 0)).add
      ((h.controlled_ell hEc hpF hparam.1).sq.mul (hcF.neg.inv hδ hk))
  have hJ := CalcJet.nonpos_of_gen_nonneg (u:=J) hJc hD (show 0≤2*D*L by positivity) ha hb
    (fun t ht x => ?_) (fun x => ?_)
  · have hv := hJ 0 (by norm_num) 0
    change (h.mainJet E).val 0 0+((h.ell E).val 0 0*(h.ell E).val 0 0)*((h.fj 2).neg.val 0 0)⁻¹≤0 at hv
    rw [←pow_two] at hv
    have hnn : 0≤((h.ell E).val 0 0)^2*((h.fj 2).neg.val 0 0)⁻¹ :=
      mul_nonneg (sq_nonneg _) (inv_nonneg.mpr ((hδ.trans_le (hk 0 (by norm_num) 0)).le))
    have he : (h.mainJet E).val 0 0=deriv (deriv (fun e => F e 0 0)) 0 := by
      simp only [EvolutionSystem.mainJet,CalcJet.add,CalcJet.smul,CalcJet.const,CalcJet.mul,CalcJet.sq,
        E,CalcJet.coeff,hη0,zero_mul,EvolutionSystem.gj,pjet2,iteratedDeriv_zero]
      ring
    rw [he] at hv
    linarith
  · rw [h.gen_corrected hη hnonzero ⟨ht.1,ht.2.le⟩ x]
    exact add_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num))
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (ha t ⟨ht.1,ht.2.le⟩ x).1)
        ((hδ.trans_le (hk t ⟨ht.1,ht.2.le⟩ x)).le)) (sq_nonneg _))
  · have hvterm : (pjet F 0) 1=fun _ => 0 := funext hterm.1
    have hgterm := hterm.2 x
    dsimp [J,EvolutionSystem.mainJet,EvolutionSystem.ell,CalcJet.add,CalcJet.smul,CalcJet.const,
      CalcJet.mul,CalcJet.sq,CalcJet.inv,E,CalcJet.coeff,EvolutionSystem.vj,EvolutionSystem.gj]
    rw [hη1]
    simp only [zero_mul,zero_add]
    rw [hvterm,hgterm]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero,deriv_const,mul_zero,zero_mul,add_zero,le_refl]
end MicroscopicJamming.Hessian

 
open Set

namespace MicroscopicJamming
 

def canonicalRank (u q : ℝ → ℝ) : ℝ → ℝ → ℝ := by
  classical
  exact if h : ∃ f,RowClassicalRankSolution u q f then Classical.choose h else fun _ _ => 0
lemma canonicalRank_spec {u q : ℝ → ℝ} (hex : ∃ f,RowClassicalRankSolution u q f) :
    RowClassicalRankSolution u q (canonicalRank u q) := by
  unfold canonicalRank; rw [dite_eq_left hex]; exact Classical.choose_spec hex
lemma canonicalRank_eq {A B C κ Q : ℝ} {u q : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hq : RowSmoothProfile Q q)
    {f : ℝ → ℝ → ℝ} (hf : RowClassicalRankSolution u q f) :
    ∀ t∈Icc (0:ℝ) 1,∀ x,canonicalRank u q t x=f t x := by
  obtain ⟨g,hg,_,huniq⟩ := row_rank_existence_unique hQ hu hq
  intro t ht x
  exact (huniq _ (canonicalRank_spec ⟨f,hf⟩) t ht x).symm.trans (huniq f hf t ht x)
lemma rowSmooth_chord {Q : ℝ} {q₀ q₁ : ℝ → ℝ}
    (h0 : RowSmoothProfile Q q₀) (h1 : RowSmoothProfile Q q₁) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1) :
    RowSmoothProfile Q (fun t => q₀ t+θ*(q₁ t-q₀ t)) := by
  refine ⟨h0.1.add (contDiff_const.mul (h1.1.sub h0.1)),?_,?_,?_⟩
  · simp only [h0.2.1,h1.2.1,sub_self,mul_zero,add_zero]
  · simp only [h0.2.2.1,h1.2.2.1,sub_self,mul_zero,add_zero]
  · intro t ht
    have hd := ((h0.1.differentiable (by simp) t).hasDerivAt.add
      (((h1.1.differentiable (by simp) t).hasDerivAt.sub
        (h0.1.differentiable (by simp) t).hasDerivAt).const_mul θ)).deriv
    change 0<deriv (fun s => q₀ s+θ*(q₁ s-q₀ s)) t
    change deriv (fun s => q₀ s+θ*(q₁ s-q₀ s)) t = _ at hd
    rw [hd]
    have a := h0.2.2.2 t ht
    have b := h1.2.2.2 t ht
    by_cases hz : θ=0
    · simpa only [hz,zero_mul,add_zero] using a
    · have hz' : 0<θ := lt_of_le_of_ne hθ.1 (Ne.symm hz)
      nlinarith [mul_pos hz' b,mul_nonneg (sub_nonneg.mpr hθ.2) a.le]
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma twice_derivative_local_shift {φ ψ : ℝ → ℝ} (θ : ℝ)
    (he : φ =ᶠ[𝓝 θ] fun y => ψ (y-θ))
    (hψ : DifferentiableAt ℝ ψ 0 ∧ DifferentiableAt ℝ (deriv ψ) 0) :
    DifferentiableAt ℝ φ θ ∧ DifferentiableAt ℝ (deriv φ) θ ∧
      deriv (deriv φ) θ=deriv (deriv ψ) 0 := by
  have hsub : DifferentiableAt ℝ (fun y : ℝ => y-θ) θ := differentiableAt_id.sub_const θ
  have hd : DifferentiableAt ℝ (fun y => ψ (y-θ)) θ := by
    apply DifferentiableAt.comp θ _ hsub
    simpa only [sub_self] using hψ.1
  have hd2 : DifferentiableAt ℝ (fun y => deriv ψ (y-θ)) θ := by
    have h := DifferentiableAt.comp (g := deriv ψ) (f := fun y : ℝ => y-θ) θ
      (show DifferentiableAt ℝ (deriv ψ) ((fun y : ℝ => y-θ) θ) from by simpa using hψ.2) hsub
    exact h
  have he2 : deriv φ =ᶠ[𝓝 θ] fun y => deriv ψ (y-θ) := by
    filter_upwards [he.deriv] with y hy
    simpa only [deriv_comp_sub_const] using hy
  refine ⟨hd.congr_of_eventuallyEq he,hd2.congr_of_eventuallyEq he2,?_⟩
  rw [he2.deriv_eq,deriv_comp_sub_const,sub_self]
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
open Parameter Hessian
lemma canonicalRank_chord_second {A B C κ Q ρ : ℝ} {u q η : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hρ : 0<ρ)
    (hucurv : ∀ x,iteratedDeriv 2 u x≤-ρ)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η) (hη0 : η 0=0) (hη1 : η 1=0)
    (θ : ℝ) (hqθ : RowSmoothProfile Q (fun s => q s+θ*η s)) :
    let φ := fun z => canonicalRank u (fun s => q s+z*η s) 0 0
    DifferentiableAt ℝ φ θ ∧ DifferentiableAt ℝ (deriv φ) θ ∧ deriv (deriv φ) θ≤0 := by
  dsimp only
  let qθ := fun s => q s+θ*η s
  obtain ⟨r,hr,F,hF,hdata⟩ := actual_parameter_family hQ hu hqθ hη hη0 hη1
  obtain ⟨d,hd,hdq⟩ := rowSmooth_perturbation hqθ hη hη0 hη1
  have hshift : (fun z => canonicalRank u (fun s => q s+z*η s) 0 0) =ᶠ[𝓝 θ] fun z => F (z-θ) 0 0 := by
    filter_upwards [Metric.ball_mem_nhds θ (lt_min hr hd)] with z hz
    have hz' : |z-θ| < min r d := by simpa only [Metric.mem_ball,Real.dist_eq] using hz
    have he : (fun s => (q s+θ*η s)+(z-θ)*η s)=(fun s => q s+z*η s) := by funext s; ring
    rw [←he]
    exact canonicalRank_eq hQ hu (hdq (z-θ) (hz'.trans_le (min_le_right _ _)))
      (hF (z-θ) (hz'.trans_le (min_le_left _ _))) 0 (by norm_num) 0
  have htwice := twice_derivative_local_shift θ hshift
    (show DifferentiableAt ℝ (fun e => F e 0 0) 0 ∧ DifferentiableAt ℝ (deriv (fun e => F e 0 0)) 0 from
      MicroscopicJamming.RankFamilyData.parameter_C2 hdata isOpen_Ioo ⟨by linarith,hr⟩ 0 0 (by norm_num) 0)
  refine ⟨htwice.1,htwice.2.1,?_⟩
  rw [htwice.2.2]
  apply actual_second_nonpos hr hdata _ hη.continuous.continuousOn hη0 hη1 hρ
  · have he : F 0 1=u := funext (hF 0 (by simpa using hr)).2.2.2.2.2.1
    rw [he]
    exact hucurv
  · intro t ht
    convert ((hη.differentiable (by simp) t).hasDerivAt.hasDerivWithinAt :
      HasDerivWithinAt η (deriv η t) (Ici t) t) using 1; first | rfl | ring

lemma canonicalRank_chord_concave_strict {A B C κ Q ρ : ℝ} {u q₀ q₁ : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hρ : 0<ρ)
    (hucurv : ∀ x,iteratedDeriv 2 u x≤-ρ)
    (hq0 : RowSmoothProfile Q q₀) (hq1 : RowSmoothProfile Q q₁) :
    ConcaveOn ℝ (Icc 0 1) (fun θ => canonicalRank u (fun s => q₀ s+θ*(q₁ s-q₀ s)) 0 0) := by
  have he := hq1.1.sub hq0.1
  have he0 : (fun s => q₁ s-q₀ s) 0=0 := by dsimp only; rw [hq0.2.1,hq1.2.1]; ring
  have he1 : (fun s => q₁ s-q₀ s) 1=0 := by dsimp only; rw [hq0.2.2.1,hq1.2.2.1]; ring
  have hd (θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) := canonicalRank_chord_second hQ hu hρ hucurv
    he he0 he1 θ (rowSmooth_chord hq0 hq1 hθ)
  apply concaveOn_of_deriv2_nonpos' (convex_Icc _ _)
    (fun θ hθ => (hd θ hθ).1.differentiableWithinAt)
    (fun θ hθ => (hd θ hθ).2.1.differentiableWithinAt)
  intro θ hθ
  exact (hd θ hθ).2.2
end MicroscopicJamming

 
open Set

namespace MicroscopicJamming
lemma rowTerminal_penalty_jets {u : ℝ → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (l : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun z => u z-l*z^2) x =
      iteratedDeriv n u x-l*((2:ℕ).descFactorial n*x^(2-n)) := by
  rw [iteratedDeriv_fun_sub (hu.of_le (show (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from by exact_mod_cast le_top)).contDiffAt
    (by fun_prop : ContDiffAt ℝ n (fun z : ℝ => l*z^2) x)]
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_pow]

lemma rowTerminal_penalty {A B C κ Q : ℝ} {u : ℝ → ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) {l : ℝ} (hl0 : 0≤l) (hl1 : l≤1) :
    RowAnalyticTerminal (fun z => u z-l*z^2) (A+1) B (C+2) κ Q := by
  refine ⟨hu.1.sub (by fun_prop),by linarith [hu.2.1],by linarith [hu.2.2.1],
    hu.2.2.2.1,hu.2.2.2.2.1,?_,?_⟩
  · intro n hn
    obtain ⟨K,hK⟩ := hu.2.2.2.2.2.1 n hn
    refine ⟨K+2,fun x => ?_⟩
    rw [rowTerminal_penalty_jets hu.1]
    have hn' : 2-n=0 := Nat.sub_eq_zero_of_le hn
    rw [hn',pow_zero,mul_one]
    have hdf : ((2:ℕ).descFactorial n:ℝ)≤2 := by
      rcases eq_or_lt_of_le hn with h|h
      · subst n; norm_num
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]; norm_num
    calc
      _ ≤ |iteratedDeriv n u x|+|l*((2:ℕ).descFactorial n:ℝ)| := abs_sub _ _
      _ ≤ K+2 := by rw [abs_of_nonneg (mul_nonneg hl0 (Nat.cast_nonneg _))]; nlinarith [hK x,(show (0:ℝ)≤((2:ℕ).descFactorial n:ℝ) by positivity)]
  · intro x
    have hh := hu.2.2.2.2.2.2 x
    have hj := rowTerminal_penalty_jets hu.1 l 2 x
    have hj' : deriv (deriv (fun z => u z-l*z^2)) x=deriv (deriv u) x-2*l := by
      norm_num [iteratedDeriv_succ,iteratedDeriv_zero] at hj ⊢
      linarith
    rw [hj']
    refine ⟨?_,?_,?_,?_⟩
    · nlinarith [sq_nonneg x,mul_le_mul_of_nonneg_right hl1 (sq_nonneg x)]
    · nlinarith [mul_nonneg hl0 (sq_nonneg x)]
    · linarith
    · linarith

lemma rowTerminal_penalty_strict {A B C κ Q : ℝ} {u : ℝ → ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (hc : ConcaveOn ℝ univ u) (l x : ℝ) :
    iteratedDeriv 2 (fun z => u z-l*z^2) x≤-(2*l) := by
  have ha : Antitone (deriv u) := by
    intro x y hxy
    exact hc.antitoneOn_deriv (fun z _ => hu.1.differentiable (by simp) z) (mem_univ x) (mem_univ y) hxy
  have hb := ha.deriv_nonpos (x := x)
  rw [rowTerminal_penalty_jets hu.1]
  norm_num [iteratedDeriv_succ,iteratedDeriv_zero] at *
  linarith
end MicroscopicJamming

end

end OAI
