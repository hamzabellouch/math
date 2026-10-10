import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyAnchorGeometry
import OAI.Combinatorics.UniformKServer.HeavyKeyGeometry

namespace OAI

                                         
section

/-! The actual persistent level process releases potential on every retained
slot whose center moves. No independent event-conditional expectation is used. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

theorem anchor_release (D : LevelMap.Data X N H) (is : List (Fin H))
    (z : Tape D) (t : ℕ) (l : HeavySlot X)
    (ho : l∈(D.heavyState z.1 t).present) (hn : l∈(D.heavyState z.1 (t+1)).present)
    (hm : (D.heavyState z.1 t).center l≠(D.heavyState z.1 (t+1)).center l)
    (μ : X→ℝ) (hμ : ∀ p,0≤μ p) (γ δ b u : ℝ) (hγ : γ<1) (hδ : δ≤1/100)
    (hb : 0≤b) (hu : 0<u)
    (hH : 1≤GeometricMass.mass μ (D.point t) (γ*D.r))
    (hh : D.heavyFlag t→GeometricMass.mass μ (D.point t) (51200*D.r)≤
      (1+δ)*GeometricMass.mass μ (D.point t) (γ*D.r))
    (hd : u≤(6/5)*(1+∑ p∈univ.filter (fun p=>D.key is z (t+1) p=Sum.inl l),μ p)) :
    D.r*b/u*(∑ p∈univ.filter (fun p=>D.key is z (t+1) p=Sum.inl l),μ p*
      (AnchorRamp.value D.r ((D.heavyState z.1 (t+1)).center l) p-
       AnchorRamp.value D.r ((D.heavyState z.1 t).center l) p))≤-(1/4)*D.r*b := by
  have he : univ.filter (fun p=>D.key is z (t+1) p=Sum.inl l)=
      univ.filter (HeavyRecords.covers (D.heavyState z.1 (t+1)) l) := by
    apply filter_congr
    intro p _
    exact key_heavy_iff D is z (t+1) p l
  rw [he] at hd ⊢
  exact HeavyProcess.release (D.heavyState z.1 t)
    (HeavyProcess.runPair D.base D.positive.le (by simp [HeavySlot]) D.heavyFlag D.point
      (HeavyProcess.radiusStream D.r N z.1) (HeavyProcess.radiusStream_bounds D.r D.positive.le N z.1) t).1
    D.positive (by simp [HeavySlot]) (D.heavyFlag t) (D.point t)
    (HeavyProcess.radiusStream D.r N z.1 t) (HeavyProcess.radiusStream_bounds D.r D.positive.le N z.1 t)
    l ho hn hm μ hμ γ δ b u hγ hδ hb hu hH hh hd

end UniformKServer.LevelMap.Data

end


end

end OAI
