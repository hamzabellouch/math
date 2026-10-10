import Mathlib
import OAI.Analysis.CoulombRadii.Packets.RawMasterNewton
import OAI.Analysis.CoulombRadii.FieldAnalysis.AtomicNear

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma physical_closed_near_le_open {N : ℕ} (u : Coulomb.H1Vector (N+1))
    (hu : Coulomb.Antisymmetric u) (y : Position) {R : ℝ} (hR : 0<R) :
    (∫ z in Metric.closedBall y R,coulombKernel (y-z)*density (fromH1Wave u) z)≤
      Coulomb.potentialForm (Coulomb.nearPotential y (2*R)) u := by
  rw [Coulomb.nearPotential_physical u hu]
  have hi := density_weight_integrable (fromH1Wave u) (fun z => coulombKernel (y-z))
    (fun σ => fromH1_coulomb_weight_integrable u y σ 0)
  have hh := setIntegral_mono_set (s := Metric.closedBall y R) (t := Metric.ball y (2*R)) hi.integrableOn
    (Eventually.of_forall (fun z => mul_nonneg (Coulomb.coulombKernel_nonneg _) (by unfold density; positivity)))
    (Eventually.of_forall (fun z (hz : z∈Metric.closedBall y R) =>
      (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (by linarith : R<2*R)))))
  simpa only [coulombKernel,Coulomb.coulombKernel,mul_comm] using hh

theorem exists_atomic_master_error_scale : ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1 ∧
    ∀ {J N : ℕ} (S : Coulomb.Nuclei J), (∀ i,S.position i=0) →
    ∀ (u : Coulomb.H1Vector (N+1)), Coulomb.Antisymmetric u → Coulomb.mass u=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom S → Coulomb.form S u≤E+δ → 0≤δ →
    ∀ (y : Position), y≠0 → Coulomb.atomicCellScale y<s₀ → δ≤(Coulomb.atomicCellScale y)^(-349/50:ℝ) →
    ∀ (g : 𝓢(Position,ℝ)), (∫ w,g w^2)=1 →
    (∀ w,g w=g (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g w=0) →
    ∀ {c r₀ s : ℝ}, 0<c → 0<r₀ → 0<s → c*(1+packetExponent)*s^packetExponent≤1/2 →
    packetWidth c r₀ s y≤Coulomb.atomicCellScale y →
    0≤Coulomb.coreCoulombPotential u y-
      potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y ∧
    Coulomb.coreCoulombPotential u y-
      potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y≤
      Coulomb.atomicNearConstant*(Coulomb.atomicCellScale y)^(-21/5:ℝ)*(4*packetWidth c r₀ s y)^(1/5:ℝ) := by
  obtain ⟨s₀,hs₀,hs₀1,H⟩ := Coulomb.exists_atomic_near_scale
  refine ⟨s₀,hs₀,hs₀1,?_⟩
  intro J N S hatom u hu hm E δ hE hstate hδ y hy hys hd g hgm hrad hgs c r₀ s hc hr hs hq hw
  obtain ⟨hl,hh⟩ := physical_master_near_deficit u hu hm g hgm hrad hgs hc hr hs hq y
  have hp := packetWidth_pos hc hr hs y
  refine ⟨hl,hh.trans ?_⟩
  have hb := physical_closed_near_le_open u hu y (mul_pos (by norm_num : (0:ℝ)<2) hp)
  have hn := H S hatom u hu hm hE hstate hδ y hy hys hd
    (R := 4*packetWidth c r₀ s y) (by positivity) (by linarith)
  rw [show (2:ℝ)*(2*packetWidth c r₀ s y)=4*packetWidth c r₀ s y by ring] at hb
  exact hb.trans hn
end NeutralAtom
end

end
end

end OAI
