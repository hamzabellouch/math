import Mathlib
import OAI.Geometry.Cannon.Flows.NoVanishingLocalMesh
import OAI.Geometry.Cannon.Energy.ClopenNeighborhoodComponent

namespace OAI

section
section
section
noncomputable section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set Topology

namespace CannonCrossEnergyLocal

open Set Metric Filter Topology CannonApprox CannonCrossEnergy CannonContinuum

theorem escaping_level_energy_obstruction {X : Type*} [MetricSpace X] [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (f w : ℕ → X → ℝ) (S : ℕ → Set X)
    (b c : X) (ρ ε : ℝ) (P : Set X)
    (hP : ∀ x ∈ P, ρ < dist x b)
    (a d q : ℝ) (had : a < d) (hq : 0 < q)
    (hKS : ∀ᶠ n in atTop, {z | ρ ≤ dist z b ∧ ε ≤ dist z c} ⊆ S n)
    (hCS : ∀ᶠ n in atTop, ∀ i,
      (ball (p n i) (2*r n) ∩ {z | ρ ≤ dist z b ∧ ε ≤ dist z c}).Nonempty →
      closedBall (p n i) (2*r n) ⊆ S n)
    (hf : ∀ᶠ n in atTop, ContinuousOn (f n) (S n))
    (hw : ∀ᶠ n in atTop, ContinuousOn (w n) (S n))
    (hgap : ∀ᶠ n in atTop, ∀ x ∈ P, ∀ z, dist z b = ρ →
      q ≤ |w n x-w n z|)
    (hlevels : ∀ᶠ n in atTop, ∀ t ∈ Icc a d, ∃ D : Set X,
      IsCompact D ∧ IsConnected D ∧ (D ∩ P).Nonempty ∧
      (∀ x ∈ D, f n x = t) ∧ (∃ z ∈ D, dist z b < ρ) ∧
      ∀ z ∈ D, ε ≤ dist z c)
    (hfe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (f n)
      {z | ρ ≤ dist z b ∧ ε ≤ dist z c}) atTop (𝓝 0))
    (hwe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (w n)
      {z | ρ ≤ dist z b ∧ ε ≤ dist z c}) atTop (𝓝 0)) : False := by
  apply no_vanishing_local_mesh ι p r hr hpnet f w S _ hKS hCS hf hw a d q had hq _ hfe hwe
  filter_upwards [hlevels,hgap,hw,hKS] with n hn hgn hwn hKSn
  intro t ht
  obtain ⟨D,hD,hDconn,⟨x,hxD,hxP⟩,hfD,hin,havoid⟩ := hn t ht
  obtain ⟨C,hC,hCconn,hCD,hxC,⟨z,hzC,hzr⟩,hout⟩ :=
    stop_continuum hD hDconn hxD (hP x hxP) hin
  have hCK : C ⊆ {z | ρ ≤ dist z b ∧ ε ≤ dist z c} :=
    fun v hv => ⟨hout v hv,havoid v (hCD hv)⟩
  have hwC : ContinuousOn (w n) C := hwn.mono (hCK.trans hKSn)
  have hxx := mem_rangeInterval hwC hC hxC
  have hzz := mem_rangeInterval hwC hC hzC
  have habs : |w n x-w n z| ≤ CannonCrossEnergy.oscillation (w n) C := by
    apply abs_le.mpr
    rcases hxx with ⟨hxlo,hxhi⟩
    rcases hzz with ⟨hzlo,hzhi⟩
    constructor <;> dsimp [CannonCrossEnergy.oscillation] <;> linarith
  exact ⟨C,hC,hCconn.nonempty,hCconn.isPreconnected,hCK,
    fun v hv => hfD v (hCD hv),(hgn x hxP z hzr).trans habs⟩

end CannonCrossEnergyLocal

end

end
end
end
end
end
end
end

end OAI
