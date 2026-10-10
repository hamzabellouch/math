import Mathlib
import OAI.Combinatorics.UniformKServer.ActualAnchorDriftSum
import OAI.Combinatorics.UniformKServer.ActualAnchorPotential

namespace OAI

                                            
section

/-! The five-substep potential's filtering and hidden-motion identity is an
unconditional finite-law identity at every step. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def frozenPotential (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t s : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin J,∑ l : LevelMap.HeavySlot X,anchorTerm A D hk z j l t t s t ω

theorem frozen_regroup (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t s : ℕ) (ω : Ω) :
    frozenPotential A D hk z t s ω=∑ p,HiddenFlow.current D s ω p*
      ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*heavyValue A D hk z j t ω (word A D hk z s ω p j) p := by
  have hj (j : Fin J) : (∑ l : LevelMap.HeavySlot X,anchorTerm A D hk z j l t t s t ω)=
      GeometricMass.radius A.R A.q j.val*(∑ p,HiddenFlow.current D s ω p*
        heavyValue A D hk z j t ω (word A D hk z s ω p j) p) := by
    have hm := AnchorPotential.regroup (GeometricMass.radius A.R A.q j.val) (HiddenFlow.current D s ω)
      (heavyCoefficient A D hk z j t ω) (heavyState A D hk z j t ω).center (fun p=>word A D hk z s ω p j)
    dsimp only [heavyValue]
    rw [←hm,mul_sum]
    apply sum_congr rfl
    intro l _
    dsimp only [anchorTerm,anchorIntegral,heavyCoefficient,keyRegion]
    ring_nf
    congr 2
    ext p
    simp only [mem_filter,mem_univ,true_and]
  simp only [frozenPotential,hj,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro j _
  ring

theorem heavyValue_measurable (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω v : Ω) (h : (D.filtration t).r ω v)
    (l : Label X A.C k) (p : X) : heavyValue A D hk z j t ω l p=heavyValue A D hk z j t v l p := by
  cases l with
  | inr a => rfl
  | inl l =>
    dsimp only [heavyValue,AnchorScalar.value,heavyCoefficient]
    have hp := labelPark_measurable A D hk z j (Sum.inl l) t ω v h
    have hu := KeySizeTracker.held_measurable (labelTracker A D hk z j (Sum.inl l)) t ω v h
    have ha := A.anchor_measurable (N:=N) (J:=J) D hk ω v t j.val h (z j) (Sum.inl l)
    change (heavyState A D hk z j t ω).center l=(heavyState A D hk z j t v).center l at ha
    rw [hp,hu,ha]

theorem frozen_testing (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t s : ℕ) (hts : t ≤ s) :
    average D.weight (frozenPotential A D hk z t s)=
      average D.weight (fun ω=>∑ a : Fin k,∑ j : Fin J,GeometricMass.radius A.R A.q j.val*
        heavyValue A D hk z j t ω (word A D hk z s ω (D.position s ω a) j) (D.position s ω a)) := by
  change average D.weight (fun ω=>frozenPotential A D hk z t s ω)=_
  simp_rw [frozen_regroup]
  apply HiddenFlow.current_test
  intro ω v h
  funext p
  apply sum_congr rfl
  intro j _
  have hk' := A.key_measurable (N:=N) (J:=J) D hk ω v s j.val h (z j) p
  change word A D hk z s ω p j=word A D hk z s v p j at hk'
  rw [hk']
  exact congrArg (fun x : ℝ=>GeometricMass.radius A.R A.q j.val*x)
    (heavyValue_measurable A D hk z j t ω v (HiddenFlow.refines_le D t s hts ω v h) _ p)

theorem expected_drift (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2 ≤ k)
    (z : Tape A k N J) (t : ℕ) (hdiam : ∀ p q : X,dist p q ≤ 40*A.R) :
    average D.weight (fun ω=>frozenPotential A D hk z t (t+1) ω-frozenPotential A D hk z t t ω) ≤
      average D.weight (fun ω=>(6/5)*132*A.q*coordinateCost A D hk z t ω+
        (driftLog k/3)*dist (D.position t ω (D.chosen t ω)) (D.request t ω)) := by
  have he : average D.weight (fun ω=>frozenPotential A D hk z t (t+1) ω-frozenPotential A D hk z t t ω)=
      average D.weight (fun ω=>∑ a : Fin k,memberDrift A D hk z t ω a) := by
    have h1 := frozen_testing A D hk z t (t+1) (by omega)
    have h0 := frozen_testing A D hk z t t le_rfl
    simp only [average,mul_sub,sum_sub_distrib] at h1 h0 ⊢
    rw [h1,h0]
    simp only [memberDrift,mul_sub,sum_sub_distrib]
  rw [he]
  exact PilotEdits.average_mono D.weight _ _ (fun ω=>(D.positive ω).le)
    (fun ω=>members_drift A D hk z t ω hdiam)

end UniformKServer.PartitionTree

end


end

end OAI
