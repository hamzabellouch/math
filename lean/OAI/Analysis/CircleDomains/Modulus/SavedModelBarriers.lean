import OAI.Analysis.CircleDomains.Modulus.SmallModelBarrier
import OAI.Analysis.CircleDomains.Topology.CompactScalarModelFromCircle
import OAI.Analysis.CircleDomains.Modulus.PersistentSavedBarriers

namespace OAI

/-! Every saved source contour has an actual compact global barrier on
every later finite circle model, with energy tending to zero in the
saved stage. All witnesses come from the recursive construction. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem saved_model_barrier (harea : ExteriorCoefficientAreaTheorem) (s n : ℕ)
    (M : CompactScalarCircleModel G (states (s+1+n)).family.test) :
    let S := ((states s).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε s).saved
    ∀ l : Fin S.count,
      ∃ (v : EuclideanPlane → ℝ) (W : DeGiorgi.MemW1pWitness 2 v univ),
        Continuous v ∧ tsupport v ⊆ ball 0 (65*a) ∧
        (∀ x, v x ∈ Icc (0 : ℝ) 1) ∧
        (∀ z ∈ range (S.curve l), v (complexPlaneCoordinates.symm (M.function z)) = 1) ∧
        (∫ x, ‖W.weakGrad x‖^2) < (1/((s:ℝ)+1))^2 := by
  dsimp only
  let step := (states s).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε s
  let ip : Fin (states (s+1)).family.count := (0 : Fin ((states s).family.count+1)).succ
  let iq : Fin (states (s+1)).family.count :=
    ⟨0,by change 0 < (states s).family.count+2; omega⟩
  let i := tailIndex hsupply hsard hsch hG hinf hTD ha hBa hε T (s+1) ip n
  let j := tailIndex hsupply hsard hsch hG hinf hTD ha hBa hε T (s+1) iq n
  have hhold := saved_barriers_persist hsupply hsard hsch hG hinf hTD ha hBa hε T s n
  obtain ⟨b,hb⟩ := M.exists_coefficient hG hinf
  let A := M.toCompactScalarModel hinf (states (s+1+n)).family.compact b hb
  have hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G := by
    intro p hp
    by_contra hpG
    cases p using OnePoint.rec with
    | infty => exact hpG hinf
    | coe z => exact hp ⟨z,hBa hpG,rfl⟩
  intro l
  obtain ⟨H,hH⟩ := (hhold l).2.2
  have hcl (z : ℂ) (hz : z ∈ range (step.saved.curve l)) :
      z ∈ closure (jordanInterior (step.saved.jordan l)) := by
    apply frontier_subset_closure
    rwa [(step.saved.regular l).2.2.1]
  apply A.exists_small_pair_barrier harea hG hinf (states (s+1+n)).family.continuous
    (states (s+1+n)).family.compact i j ha (by positivity) hsource
    (step.saved.smooth l) (step.saved.compact l) (step.saved.unit l) H hH (hhold l).2.1
    (fun z hz => (step.saved.regular l).2.2.2 z hz)
  · intro z hz
    have h := step.saved.inside l (hcl z hz)
    rw [mem_ball_zero_iff] at h ⊢
    linarith
  · intro z hz
    exact (hhold l).1 z (step.saved.contains l (hcl z hz))

end AppendingSequence
end CircleDomainRigidity

end

end OAI
