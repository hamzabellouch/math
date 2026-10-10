import OAI.Analysis.CircleDomains.Sobolev.TrackedTailGradient
import OAI.Analysis.CircleDomains.Modulus.RecursiveTailBudget

namespace OAI

/-! The actual recursive construction preserves every saved separating
barrier at every later finite stage. No infinite pair-nullity is needed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def SavedSeparatingFamily.Holds {G : Set Sphere} {a η : ℝ}
    {p q : EuclideanPlane → ℝ}
    {Wp : DeGiorgi.MemW1pWitness 2 p (physicalPlaneDomain G)}
    {Wq : DeGiorgi.MemW1pWitness 2 q (physicalPlaneDomain G)}
    (S : SavedSeparatingFamily G a η p q Wp Wq) (p' q' : EuclideanPlane → ℝ) : Prop :=
  ∀ i,
    (∀ z ∈ S.neighborhood i, S.barrier i (planePair (p' (complexPlaneCoordinates.symm z))
      (q' (complexPlaneCoordinates.symm z))) = 1) ∧
    (∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a →
      S.barrier i (planePair (p' (complexPlaneCoordinates.symm z))
        (q' (complexPlaneCoordinates.symm z))) = 0) ∧
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => S.barrier i (planePair (p' x) (q' x)))
      (physicalPlaneDomain G ∩ ball 0 (65*a)),
      (eLpNorm W.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η

namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "f" => tailScalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => tailWitness hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem saved_barriers_persist (s n : ℕ) :
    let step := (states s).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε s
    let ip : Fin (states (s+1)).family.count := (0 : Fin ((states s).family.count+1)).succ
    let iq : Fin (states (s+1)).family.count :=
      ⟨0,by change 0 < (states s).family.count+2; omega⟩
    step.saved.Holds (f (s+1) ip n) (f (s+1) iq n) := by
  let step := (states s).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε s
  let ip : Fin (states (s+1)).family.count := (0 : Fin ((states s).family.count+1)).succ
  let iq : Fin (states (s+1)).family.count :=
      ⟨0,by change 0 < (states s).family.count+2; omega⟩
  let p := f (s+1) ip n
  let q := f (s+1) iq n
  let τ := step.saved.tolerance
  have hτ : 0 < τ := step.saved.tolerance_pos
  have hb := tail_budget_le_saved hsupply hsard hsch hG hinf hTD ha hBa hε T
    (s := s) (k := s+1) le_rfl n
  have hpE (x : EuclideanPlane) : |p x-step.data.p x| ≤ τ/4 :=
    (tail_uniform_error hsupply hsard hsch hG hinf hTD ha hBa hε T (s+1) ip n x).trans hb
  have hqE (x : EuclideanPlane) : |q x-step.data.q x| ≤ τ/4 :=
    (tail_uniform_error hsupply hsard hsch hG hinf hTD ha hBa hε T (s+1) iq n x).trans hb
  have hopen := (isOpen_physicalPlaneDomain hG).inter (isOpen_ball (x := (0 : EuclideanPlane)) (ε := 65*a))
  let Wp := (W (s+1) ip n).restrict hopen inter_subset_left
  let Wq := (W (s+1) iq n).restrict hopen inter_subset_left
  apply step.saved.stable p q
    ((states (s+1+n)).family.continuous _)
    ((states (s+1+n)).family.continuous _) Wp Wq
  · intro x
    have he : planePair (p x) (q x)-planePair (step.data.p x) (step.data.q x) =
        planePair (p x-step.data.p x) (q x-step.data.q x) := by
      ext i
      fin_cases i <;> simp
    rw [he]
    exact (planePair_norm_le _ _).trans (by linarith [hpE x,hqE x])
  · have hg := (tail_gradient_norm_error hsupply hsard hsch hG hinf hTD ha hBa hε T
      (s+1) ip n (65*a)).trans hb
    exact hg.trans (show τ/4 ≤ τ by linarith)
  · have hg := (tail_gradient_norm_error hsupply hsard hsch hG hinf hTD ha hBa hε T
      (s+1) iq n (65*a)).trans hb
    exact hg.trans (show τ/4 ≤ τ by linarith)

end AppendingSequence
end CircleDomainRigidity

end

end OAI
