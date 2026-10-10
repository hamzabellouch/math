import OAI.Analysis.ModularRecovery.CanonicalCalculus

namespace OAI

/-! Canonical square roots, the Tomita graph, and standard modular data. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate ComplexOrder
namespace BoundedRecovery

def intervalRoot : C(UnitInterval,ℂ) := ⟨fun r => (Real.sqrt r.1:ℂ), by fun_prop⟩
def intervalCoRoot : C(UnitInterval,ℂ) := ⟨fun r => (Real.sqrt (1-r.1):ℂ), by fun_prop⟩

lemma intervalRoot_nonneg : (0 : C(UnitInterval,ℂ)) ≤ intervalRoot := by
  intro r
  exact Complex.nonneg_iff.mpr ⟨Real.sqrt_nonneg _,rfl⟩
lemma intervalCoRoot_nonneg : (0 : C(UnitInterval,ℂ)) ≤ intervalCoRoot := by
  intro r
  exact Complex.nonneg_iff.mpr ⟨Real.sqrt_nonneg _,rfl⟩

lemma intervalRoot_sq : intervalRoot*intervalRoot=intervalCoordinate := by
  ext r
  change (Real.sqrt r.1:ℂ)*(Real.sqrt r.1:ℂ)=(r.1:ℂ)
  exact_mod_cast Real.mul_self_sqrt r.2.1
lemma intervalCoRoot_sq : intervalCoRoot*intervalCoRoot=1-intervalCoordinate := by
  ext r
  change (Real.sqrt (1-r.1):ℂ)*(Real.sqrt (1-r.1):ℂ)=1-(r.1:ℂ)
  exact_mod_cast Real.mul_self_sqrt (sub_nonneg.mpr r.2.2)

lemma intervalRootSum_pos (r : UnitInterval) : 0 < Real.sqrt r.1+Real.sqrt (1-r.1) := by
  nlinarith [Real.sqrt_nonneg r.1,Real.sqrt_nonneg (1-r.1),
    Real.sq_sqrt r.2.1,Real.sq_sqrt (sub_nonneg.mpr r.2.2)]

def intervalHalfRes : C(UnitInterval,ℂ) :=
  ⟨fun r => ((Real.sqrt r.1/(Real.sqrt r.1+Real.sqrt (1-r.1)):ℝ):ℂ), by
    apply Complex.continuous_ofReal.comp
    exact (by fun_prop : Continuous (fun r : UnitInterval => Real.sqrt r.1)).div
      (by fun_prop) (fun r => (intervalRootSum_pos r).ne')⟩

def intervalRootSumInv : C(UnitInterval,ℂ) :=
  ⟨fun r => (((Real.sqrt r.1+Real.sqrt (1-r.1))⁻¹:ℝ):ℂ), by
    apply Complex.continuous_ofReal.comp
    exact (by fun_prop : Continuous (fun r : UnitInterval => Real.sqrt r.1+Real.sqrt (1-r.1))).inv₀
      (fun r => (intervalRootSum_pos r).ne')⟩

lemma intervalRootSumInv_mul : intervalRootSumInv*(intervalRoot+intervalCoRoot)=1 := by
  ext r
  change (((Real.sqrt r.1+Real.sqrt (1-r.1))⁻¹:ℝ):ℂ)*((Real.sqrt r.1:ℂ)+(Real.sqrt (1-r.1):ℂ))=1
  exact_mod_cast inv_mul_cancel₀ (intervalRootSum_pos r).ne'

lemma intervalRootSum_mul_halfRes : (intervalRoot+intervalCoRoot)*intervalHalfRes=intervalRoot := by
  ext r
  change ((Real.sqrt r.1:ℂ)+(Real.sqrt (1-r.1):ℂ))*
    ((Real.sqrt r.1/(Real.sqrt r.1+Real.sqrt (1-r.1)):ℝ):ℂ)=(Real.sqrt r.1:ℂ)
  exact_mod_cast mul_div_cancel₀ (Real.sqrt r.1) (intervalRootSum_pos r).ne'

lemma halfResolvent_logit {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    halfResolvent (intervalLogit r) = ((Real.sqrt r/(Real.sqrt r+Real.sqrt (1-r)):ℝ):ℂ) := by
  have hq : 0 < (1-r)/r := div_pos (by linarith) h0
  have he : Real.exp (Real.log ((1-r)/r)/2)=Real.sqrt ((1-r)/r) := by
    apply (sq_eq_sq₀ (Real.exp_pos _).le (Real.sqrt_nonneg _)).mp
    rw [← exp_eq_sq_exp_half,Real.exp_log hq,Real.sq_sqrt hq.le]
  rw [halfResolvent_apply,intervalLogit,he,Real.sqrt_div (by linarith : 0 ≤ 1-r)]
  congr 1
  have hr : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
  have hs : Real.sqrt r+Real.sqrt (1-r) ≠ 0 := (add_pos_of_pos_of_nonneg
    (Real.sqrt_pos.mpr h0) (Real.sqrt_nonneg _)).ne'
  field_simp
  ring

lemma weightedPullback_halfResolvent : weightedPullback halfResolvent=intervalWeight*intervalHalfRes := by
  ext r
  by_cases h0 : r.1=0
  · simp [weightedPullback_apply,intervalWeight,intervalCoordinate,h0]
  by_cases h1 : r.1=1
  · simp [weightedPullback_apply,intervalWeight,intervalCoordinate,h1]
  change intervalWeight r*halfResolvent (intervalLogit r.1)=intervalWeight r*intervalHalfRes r
  rw [halfResolvent_logit (lt_of_le_of_ne r.2.1 (Ne.symm h0)) (lt_of_le_of_ne r.2.2 h1)]
  rfl

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace CyclicSeparatingData

def rootA (S : CyclicSeparatingData H) : H →L[ℂ] H := S.intervalCalculus intervalRoot
def coRootA (S : CyclicSeparatingData H) : H →L[ℂ] H := S.intervalCalculus intervalCoRoot

lemma rootA_sq (S : CyclicSeparatingData H) : S.rootA*S.rootA=S.A := by
  change S.intervalCalculus intervalRoot*S.intervalCalculus intervalRoot=_
  rw [← map_mul,intervalRoot_sq,S.intervalCalculus_coordinate]
lemma coRootA_sq (S : CyclicSeparatingData H) : S.coRootA*S.coRootA=1-S.A := by
  change S.intervalCalculus intervalCoRoot*S.intervalCalculus intervalCoRoot=_
  rw [← map_mul,intervalCoRoot_sq,map_sub,map_one,S.intervalCalculus_coordinate]
lemma rootA_injective (S : CyclicSeparatingData H) : Function.Injective S.rootA := by
  intro x y h
  apply S.A_injective
  have he := congrArg S.rootA h
  change (S.rootA*S.rootA) x=(S.rootA*S.rootA) y at he
  rwa [S.rootA_sq] at he

lemma rootA_mul_coRootA (S : CyclicSeparatingData H) : S.rootA*S.coRootA=S.Q := by
  symm
  apply CFC.sqrt_unique
  · change (S.intervalCalculus intervalRoot*S.intervalCalculus intervalCoRoot)*
      (S.intervalCalculus intervalRoot*S.intervalCalculus intervalCoRoot)=S.K
    rw [← map_mul,← map_mul,← S.intervalCalculus_weight]
    congr 1
    calc
      (intervalRoot*intervalCoRoot)*(intervalRoot*intervalCoRoot)=
        (intervalRoot*intervalRoot)*(intervalCoRoot*intervalCoRoot) := by ring
      _ = intervalWeight := by rw [intervalRoot_sq,intervalCoRoot_sq]; rfl
  · exact (S.intervalCalculus_commute intervalRoot intervalCoRoot).mul_nonneg
      (S.intervalCalculus_nonneg intervalRoot_nonneg) (S.intervalCalculus_nonneg intervalCoRoot_nonneg)

lemma rootSum_injective (S : CyclicSeparatingData H) : Function.Injective (S.rootA+S.coRootA) := by
  have hi : S.intervalCalculus intervalRootSumInv*(S.rootA+S.coRootA)=1 := by
    change S.intervalCalculus intervalRootSumInv*(S.intervalCalculus intervalRoot+S.intervalCalculus intervalCoRoot)=1
    rw [← map_add,← map_mul,intervalRootSumInv_mul,map_one]
  intro x y h
  have he := congrArg (S.intervalCalculus intervalRootSumInv) h
  change (S.intervalCalculus intervalRootSumInv*(S.rootA+S.coRootA)) x=
    (S.intervalCalculus intervalRootSumInv*(S.rootA+S.coRootA)) y at he
  simpa only [hi,one_apply_eq_self] using he

lemma D_halfResolvent (S : CyclicSeparatingData H) : S.D.calculus halfResolvent=S.intervalCalculus intervalHalfRes :=
  S.logCalculus_eq_interval _ _ weightedPullback_halfResolvent

lemma halfGraph_iff_roots (S : CyclicSeparatingData H) (x y : H) :
    (x,y) ∈ S.D.halfGraph ↔ S.coRootA x=S.rootA y := by
  rw [S.D.halfGraph_iff_resolvent,S.D_halfResolvent]
  have hi : (S.rootA+S.coRootA)*S.intervalCalculus intervalHalfRes=S.rootA := by
    change (S.intervalCalculus intervalRoot+S.intervalCalculus intervalCoRoot)*S.intervalCalculus intervalHalfRes=_
    rw [← map_add,← map_mul,intervalRootSum_mul_halfRes]
    rfl
  constructor
  · intro h
    have he := congrArg (S.rootA+S.coRootA) h
    change ((S.rootA+S.coRootA)*S.intervalCalculus intervalHalfRes) (x+y)=(S.rootA+S.coRootA) x at he
    rw [hi] at he
    rw [map_add] at he
    change S.rootA x+S.rootA y=S.rootA x+S.coRootA x at he
    exact (add_left_cancel he).symm
  · intro h
    apply S.rootSum_injective
    change ((S.rootA+S.coRootA)*S.intervalCalculus intervalHalfRes) (x+y)=(S.rootA+S.coRootA) x
    rw [hi]
    rw [map_add]
    change S.rootA x+S.rootA y=S.rootA x+S.coRootA x
    rw [h]

end CyclicSeparatingData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
namespace CyclicSeparatingData

lemma Jcl_A (S : CyclicSeparatingData H) (x : H) :
    S.Jcl (S.A x) = S.Jcl x-S.A (S.Jcl x) := by
  refine S.Q_dense.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) x
  rintro _ ⟨y,rfl⟩
  have hc : S.A (S.Q y)=S.Q (S.A y) :=
    (congrArg (fun f : H →L[ℂ] H => f y) S.Q_commute_A.eq).symm
  rw [hc,S.Jcl_Q,S.Jcl_Q]
  exact eq_sub_iff_add_eq.mpr (S.blocks_idempotent y).2

lemma Jcl_B (S : CyclicSeparatingData H) (x : H) : S.Jcl (S.B x)=S.Q x := by
  rw [← S.Jcl_Q,S.Jcl_involutive]

lemma B_eq_Q_Jcl (S : CyclicSeparatingData H) (x : H) : S.B x=S.Q (S.Jcl x) := by
  rw [← S.Jcl_Q,S.Jcl_commute_Q]

lemma graph_iff_roots (S : CyclicSeparatingData H) (x y : H) :
    HilbertPair.pair x y ∈ S.graph ↔ S.coRootA x=S.rootA (S.Jcl y) := by
  rw [← S.graph.starProjection_eq_self_iff,S.projection_pair]
  change HilbertPair.pair (S.A x+S.B y) (S.B x+S.A y)=HilbertPair.pair x y ↔ _
  constructor
  · intro hp
    have h2 : S.B x+S.A y=y := congrArg (WithLp.sndL 2 ℝ H H) hp
    have he := congrArg S.Jcl h2
    rw [map_add,S.Jcl_B,S.Jcl_A] at he
    have hQ : S.Q x=S.A (S.Jcl y) := by
      simpa only [sub_sub_cancel] using eq_sub_iff_add_eq.mpr he
    apply S.rootA_injective
    change (S.rootA*S.coRootA) x=(S.rootA*S.rootA) (S.Jcl y)
    rwa [S.rootA_mul_coRootA,S.rootA_sq]
  · intro h
    have hQ : S.Q x=S.A (S.Jcl y) := by
      have he := congrArg S.rootA h
      change (S.rootA*S.coRootA) x=(S.rootA*S.rootA) (S.Jcl y) at he
      rwa [S.rootA_mul_coRootA,S.rootA_sq] at he
    have hOne : x-S.A x=S.Q (S.Jcl y) := by
      have he := congrArg S.coRootA h
      change (S.coRootA*S.coRootA) x=(S.coRootA*S.rootA) (S.Jcl y) at he
      have hc : S.coRootA*S.rootA=S.Q :=
        (S.intervalCalculus_commute intervalCoRoot intervalRoot).eq.trans S.rootA_mul_coRootA
      rw [S.coRootA_sq,hc] at he
      exact he
    have h1 : S.A x+S.B y=x := by
      rw [S.B_eq_Q_Jcl,← hOne]
      abel
    have h2 : S.B x+S.A y=y := by
      apply S.Jcl_involutive.injective
      rw [map_add,S.Jcl_B,S.Jcl_A,hQ]
      abel
    rw [h1,h2]

lemma graph_iff_halfGraph (S : CyclicSeparatingData H) (x y : H) :
    HilbertPair.pair x y ∈ S.graph ↔ (x,S.J y) ∈ S.D.halfGraph := by
  rw [S.graph_iff_roots,S.halfGraph_iff_roots]
  rfl

lemma graph_iff_closure (S : CyclicSeparatingData H) (x y : H) :
    HilbertPair.pair x y ∈ S.graph ↔ (x,y) ∈ closure {p : H × H |
      ∃ a : H →L[ℂ] H, a ∈ S.M ∧ p=(a S.xi,(star a) S.xi)} := by
  let e := (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toHomeomorph
  change (x,y) ∈ e ⁻¹' closure (S.coreMap.range : Set (HilbertPair H)) ↔ _
  rw [e.preimage_closure]
  suffices he : e ⁻¹' (S.coreMap.range : Set (HilbertPair H)) =
      {p : H × H | ∃ a : H →L[ℂ] H, a ∈ S.M ∧ p=(a S.xi,(star a) S.xi)} by rw [he]
  ext p
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,a.property,?_⟩
    have he := congrArg (WithLp.prodContinuousLinearEquiv 2 ℂ H H) ha
    exact he.symm
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,ha⟩,rfl⟩

lemma tomita_graph (S : CyclicSeparatingData H) :
    closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p=(a S.xi,(star a) S.xi)} =
    {p | ∃ q : H, (p.1,q) ∈ S.D.halfGraph ∧ p.2=S.J q} := by
  ext p
  rw [← S.graph_iff_closure, S.graph_iff_halfGraph]
  constructor
  · intro hp
    exact ⟨S.J p.2,hp,(S.Jcl_involutive p.2).symm⟩
  · rintro ⟨q,hq,hpq⟩
    rw [hpq]
    simpa only [show S.J (S.J q)=q from S.Jcl_involutive q] using hq

def toStandardModularData (S : CyclicSeparatingData H) : StandardModularData H where
  M := S.M
  xi := S.xi
  norm_xi := S.norm_xi
  cyclic := S.cyclic
  separating := S.separating
  D := S.D
  J := S.J
  conjugation := S.Jcl_involutive
  tomita_graph := S.tomita_graph

end CyclicSeparatingData
end BoundedRecovery

end
end

end OAI
