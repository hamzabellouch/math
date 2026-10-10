import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.SmoothCutoff

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

lemma dirichlet_scalar_injective {N : ℕ} {L : Length} {a : ℝ} {u v : Jet N L}
    (hu : u∈dirichletDomain N L a) (hv : v∈dirichletDomain N L a) (he : u.1=v.1) : u=v := by
  have hz := derivative_zero_of_scalar_zero
    (show u-v∈dirichletDomain N L a from (dirichletSubmodule N L a).sub_mem hu hv)
    (show (u-v).1=0 by simp only [Prod.fst_sub,he,sub_self])
  apply Prod.ext he
  apply sub_eq_zero.mp
  exact hz

lemma SmoothMultiplier.onJet_mem_domain_of_support {N : ℕ} {L : Length} {a b : ℝ}
    (f : SmoothMultiplier N L) (hf : tsupport f.toFun⊆allowed N L a)
    {u : Jet N L} (hu : u∈dirichletDomain N L b) : f.onJet u∈dirichletDomain N L a := by
  apply map_mem_closure f.onJet.continuous hu
  rintro _ ⟨g,rfl⟩
  let h : SmoothTest N L a := {g.multiply f with
    support_allowed := tsupport_mul_subset_left.trans hf }
  exact ⟨h,g.jet_multiply f⟩

lemma dirichletDomain_of_closed_support {N : ℕ} {L : Length} {a b : ℝ}
    (hΩ : IsOpen (allowed N L a)) {K : Set (Configuration N L)}
    (hK : IsClosed K) (hKΩ : K⊆allowed N L a) {u : Jet N L}
    (hu : u∈dirichletDomain N L b)
    (hz : ∀ᵐ X ∂(volume : Measure (Configuration N L)), X∉K → u.1 X=0) :
    u∈dirichletDomain N L a := by
  obtain ⟨f,hf1,hfs⟩ := exists_smooth_cutoff N L hK hΩ hKΩ
  have he : (f.onJet u).1=u.1 := by
    apply Lp.ext
    filter_upwards [L2Multiplier.coe_clm f.toFun f.memLp_top u.1,hz] with X hc hz
    change (f.onScalar u.1) X=u.1 X
    rw [SmoothMultiplier.onScalar,hc]
    by_cases h : X∈K
    · rw [hf1 h,Pi.one_apply,one_mul]
    · rw [hz h,mul_zero]
  have heq := dirichlet_scalar_injective (f.onJet_mem_domain hu) hu he
  rw [← heq]
  exact f.onJet_mem_domain_of_support hfs hu

end HardSphere

end

end OAI
