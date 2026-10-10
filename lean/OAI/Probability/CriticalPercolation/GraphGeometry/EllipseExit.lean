import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.MoveExit
import OAI.Probability.CriticalPercolation.Gluing.RelayMoves
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteOpenWitness

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.EuclideanEllipse

lemma finite_circle_cover (zeta : ℝ) (hzeta : 0<zeta) :
    ∃ S : Finset Circle, ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta := by
  obtain ⟨S,_hS,hSf,hcover⟩ := (isCompact_univ : IsCompact (Set.univ : Set Circle)).finite_cover_balls hzeta
  refine ⟨hSf.toFinset,?_⟩
  intro c
  obtain ⟨d,hd,hcd⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ c))
  change dist (c : ℂ) (d : ℂ)<zeta at hcd
  exact ⟨d,hSf.mem_toFinset.mpr hd,by simpa only [dist_eq_norm] using hcd⟩

lemma exists_radial_circle (z : ℂ) (hz : z≠0) :
    ∃ c : Circle, z=‖z‖•(c : ℂ) := by
  let c : Circle := ⟨‖z‖⁻¹•z,by
    apply mem_sphere_zero_iff_norm.mpr
    exact norm_smul_inv_norm (𝕜 := ℝ) hz⟩
  refine ⟨c,?_⟩
  change z=‖z‖•(‖z‖⁻¹•z)
  rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul]

lemma annulus_covered (S : Finset Circle) (zeta : ℝ)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    (z : ℂ) (hlo : 1≤‖z‖) (hhi : ‖z‖≤1+zeta) :
    ∃ d∈S, ‖z-(d : ℂ)‖≤2*zeta := by
  have hz : z≠0 := by intro h; subst z; norm_num at hlo
  obtain ⟨c,hc⟩ := exists_radial_circle z hz
  obtain ⟨d,hd,hcd⟩ := hcover c
  have he : z-(c : ℂ)=(‖z‖-1)•(c : ℂ) := by rw [sub_smul,one_smul,←hc]
  have hdiff : ‖z-(c : ℂ)‖=‖z‖-1 := by
    rw [he,norm_smul,Real.norm_eq_abs,Circle.norm_coe,mul_one,abs_of_nonneg (by linarith)]
  refine ⟨d,hd,?_⟩
  have htri : ‖z-(d : ℂ)‖≤‖z-(c : ℂ)‖+‖(c : ℂ)-(d : ℂ)‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (z-(c : ℂ)) ((c : ℂ)-(d : ℂ))
  linarith

end CriticalPercolation.EuclideanEllipse
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ellipseExit (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) : Set (Set E) :=
  G.restrictedSeed A {x | ‖Psi x-(c : ℂ)‖≤2*zeta ∧ ‖Psi x‖≤1+zeta}
    (G.inducedEdges {x | ‖Psi x‖≤1+zeta})

lemma ellipseExit_iff (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) (ω : Set E) :
    ω∈G.ellipseExit Psi A zeta c ↔ ∃ a∈A, ∃ x, ∃ w : (G.openGraph ω).Walk a x,
      (∀ v∈w.support, ‖Psi v‖≤1+zeta) ∧ ‖Psi x-(c : ℂ)‖≤2*zeta := by
  constructor
  · intro h
    obtain ⟨a,ha,x,⟨w⟩,hx⟩ := Set.mem_iUnion₂.mp h
    refine ⟨a,ha,x,w.mapLe (G.openGraph_mono Set.inter_subset_left),?_,hx.1⟩
    intro v hv
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
    exact G.walk_induced_support w hx.2 v hv
  · rintro ⟨a,ha,x,w,hw,hx⟩
    exact Set.mem_iUnion₂.mpr ⟨a,ha,x,G.walk_reachable_induced _ ω w hw,hx,hw x w.end_mem_support⟩

lemma ellipseExit_upper (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) :
    IsUpperSet (G.ellipseExit Psi A zeta c) := G.restrictedSeed_upper _ _ _
lemma ellipseExit_finiteWitness (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) :
    BernoulliProduct.HasFiniteOpenWitness (G.ellipseExit Psi A zeta c) := G.restrictedSeed_finiteWitness _ _ _

lemma full_infinite_cluster_exit (Psi : V → ℂ) (ω : Set E) (a : V)
    (hi : (G.cluster ω a).Infinite)
    (hbound : (G.cluster (ω∩G.inducedEdges {x | ‖Psi x‖≤1}) a).Finite) :
    ∃ b∈G.cluster ω a, 1<‖Psi b‖ := by
  by_contra hn
  push Not at hn
  apply hi
  apply hbound.subset
  rintro b ⟨w⟩
  apply G.walk_reachable_induced _ ω w
  intro x hx
  exact hn x (w.takeUntil x hx).reachable

theorem infinite_cluster_ellipseExit (Psi : V → ℂ) (A : Set V) (zeta D : ℝ)
    (hD : 0≤D) (hDz : D≤zeta)
    (hPsi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖Psi x-Psi y‖≤D)
    (hseed : ∀ a∈A, ‖Psi a‖<1) (S : Finset Circle)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    {ω : Set E} (hi : ∃ a∈A, (G.cluster ω a).Infinite)
    (hbound : ∀ a∈A, (G.cluster (ω∩G.inducedEdges {x | ‖Psi x‖≤1}) a).Finite) :
    ω∈⋃ c∈S, G.ellipseExit Psi A zeta c := by
  obtain ⟨a,ha,hi⟩ := hi
  obtain ⟨b,⟨w⟩,hb⟩ := G.full_infinite_cluster_exit Psi ω a hi (hbound a ha)
  have hstep : ∀ ⦃x y⦄, (G.openGraph ω).Adj x y → |‖Psi x‖-‖Psi y‖|≤D := by
    intro x y hxy
    exact (abs_norm_sub_norm_le _ _).trans (hPsi (G.openGraph_mono (Set.subset_univ _) hxy))
  obtain ⟨x,p,_hp,hpb,hpx⟩ := _root_.OAI.SimpleGraph.Walk.bounded_first_crossing (fun x => ‖Psi x‖) D 1 hD hstep w (hseed a ha) hb.le
  obtain ⟨c,hc,hcx⟩ := EuclideanEllipse.annulus_covered S zeta hcover (Psi x) hpx (by linarith [hpb x p.end_mem_support])
  apply Set.mem_iUnion₂.mpr
  refine ⟨c,hc,(G.ellipseExit_iff Psi A zeta c ω).mpr ⟨a,ha,x,p,?_,hcx⟩⟩
  intro v hv
  linarith [hpb v hv]

end CriticalPercolation.BondGraph
end
end
end

end OAI
