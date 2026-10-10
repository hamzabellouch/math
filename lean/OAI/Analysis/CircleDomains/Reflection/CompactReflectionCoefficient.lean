import OAI.Analysis.CircleDomains.Reflection.RoundReflectionCoefficient

namespace OAI

/-! The reflection-invariant extension remains compactly supported: every
non-base tile lies inside one of the original finitely many disks. -/
open Set Function MeasureTheory Metric Bornology
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

lemma exists_compact_reflection_coefficient {I : Type*} [Finite I]
    (c : I → ℂ) (r : I → ℝ) (hr : ∀i,0<r i)
    (hd : Pairwise (fun i j => Disjoint
      (((↑) : ℂ → Sphere) '' closedBall (c i) (r i))
      (((↑) : ℂ → Sphere) '' closedBall (c j) (r j))))
    (μ : ℂ → ℂ) (hm : Measurable μ) {k R : ℝ}
    (hk : 0≤k) (hb : ∀z,‖μ z‖≤k) (hz : ∀z,R≤‖z‖ → μ z=0) :
    ∃ (E : Sphere → ℂ) (S : ℝ),Measurable E ∧ 0<S ∧ (∀p,‖E p‖≤k) ∧
      (∀z : ℂ,S≤‖z‖ → E (z : Sphere)=0) ∧
      EqOn E (sphereCoefficient 0 μ)
        (⋃i,((↑) : ℂ → Sphere) '' closedBall (c i) (r i))ᶜ ∧
      ∀i p,E p=roundReflectionCoefficient (c i) p
        (E (roundDiskReflection (c i) (r i) (hr i) p)) := by
  have hμb (p : Sphere) : ‖sphereCoefficient 0 μ p‖≤k := by
    induction p using OnePoint.rec with
    | infty => simpa only [sphereCoefficient_infty,norm_zero] using hk
    | coe z => exact hb z
  obtain ⟨E,hEm,hEb,hbase,hEinv⟩ := exists_round_reflection_coefficient c r hr hd
    (sphereCoefficient 0 μ) (sphereCoefficient_measurable 0 hm) hk hμb
  obtain ⟨B,hB,hbound⟩ := (isCompact_iUnion (fun i => isCompact_closedBall (c i) (r i))).isBounded.exists_pos_norm_lt
  let S := max B R
  have hS : 0<S := hB.trans_le (le_max_left B R)
  refine ⟨E,S,hEm,hS,hEb,?_,hbase,hEinv⟩
  intro z hsz
  have hout : (z : Sphere)∉⋃i,((↑) : ℂ → Sphere) '' closedBall (c i) (r i) := by
    intro hz'
    obtain ⟨i,w,hw,he⟩ := mem_iUnion.mp hz'
    have hwz : w=z := OnePoint.coe_injective he
    subst w
    have hlt := hbound z (mem_iUnion.mpr ⟨i,hw⟩)
    exact (not_lt_of_ge ((le_max_left B R).trans hsz)) hlt
  rw [hbase hout,sphereCoefficient_coe,hz z ((le_max_right B R).trans hsz)]

end CircleDomainRigidity

end

end OAI
