import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.SubspacePointsEquiv
import OAI.Combinatorics.RamseyFive.Entropy.RelationMassCrossed

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem low_conflict_subsets (hdim : finrank K V=5)
    (p : Law (((ℙ K V)×(ℙ K (Dual K V)))×((ℙ K V)×(ℙ K (Dual K V)))))
    (GA : Finset (ℙ K V)) (GB : Finset (ℙ K (Dual K V)))
    (hconsistent : ∀z,0<p z→Incident z.1.1 z.2.2→Incident z.2.1 z.1.2)
    (μ : Law (Finset (ℙ K V))) (ν : Law (Finset (ℙ K (Dual K V))))
    (L : ℝ) (hL : 0≤L)
    (hGA : ∀A,0<μ A→A⊆GA) (hGB : ∀B,0<ν B→B⊆GB)
    (hμ : ∀a,(∑A,μ A*uniformWeight A a)≤L*first (first p) a)
    (hν : ∀b,(∑B,ν B*uniformWeight B b)≤L*second (second p) b) :
    let good := fun a b=>a∈GA ∧ b∈GB ∧ Incident a b
    (∑A,∑B,μ A*ν B*relationMass Incident (uniformWeight A) (uniformWeight B))≤
      L^2*80004*(entropy (first p)+entropy (second p)-entropy p+
        eventWeight p (fun z=>capturedEvent (first p) (second p)
          (fun b : ℙ K (Dual K V)=>b.rep) (fun c : ℙ K V=>c.rep) good
          z.1.1 z.1.2 z.2.1 z.2.2)) := by
  dsimp only
  have hc := low_conflict_bound hdim p
    (fun b : ℙ K (Dual K V)=>b.rep) (fun c : ℙ K V=>c.rep)
    (fun a b=>a∈GA ∧ b∈GB ∧ Incident a b) (by
      intro z hz hg
      exact (incident_iff _ _).mp (hconsistent z hz hg.2.2))
  have hs := independent_good_subset_domination Incident (first (first p)) (second (second p))
    GA GB μ ν L hL hGA hGB hμ hν
  rw [relationMass_crossed] at hs
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg L)
  exact hs.trans (by simpa only [mul_assoc] using hh)

end SharpRamseyFive.ProjectiveIncidence

end OAI
