import Mathlib
import OAI.Geometry.HyperbolicGroups.Basic

namespace OAI

section

noncomputable section
open Set Metric
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

lemma proper_of_uniform_compact_balls (g : IsGeodesic X) {ε : ℝ} (hε : 0<ε)
    (hc : ∀ a : X, IsCompact (closedBall a ε)) : ProperSpace X := by
  have hn (a : X) (n : ℕ) : IsCompact (closedBall a ((n:ℝ)*(ε/2))) := by
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨s,hs,hfin,hcover⟩:=ih.finite_cover_balls (by positivity : 0<ε/2)
      have hC : IsCompact (⋃ b ∈ s, closedBall b ε) := hfin.isCompact_biUnion (fun b hb => hc b)
      apply hC.of_isClosed_subset isClosed_closedBall
      intro b hb
      obtain ⟨γ,hγ⟩:=g a b
      let t : ℝ := (n:ℝ)/(n+1)
      have ht : t ∈ Icc (0:ℝ) 1 := by
        constructor
        · dsimp [t]; positivity
        · dsimp [t]; apply (div_le_one (by positivity)).mpr; linarith
      have hd : dist a b≤(n+1:ℝ)*(ε/2) := by simpa [mem_closedBall,dist_comm] using hb
      have hda : dist (γ t) a≤(n:ℝ)*(ε/2) := by
        have distanceFromSource : dist (γ t) a = t * dist a b := by
          simpa [hγ.1, abs_of_nonneg ht.1] using hγ.2.2 t ht 0 (by norm_num)
        rw [distanceFromSource]
        calc
          _ ≤ t*((n+1:ℝ)*(ε/2)) := mul_le_mul_of_nonneg_left hd ht.1
          _ = _ := by dsimp [t]; field_simp
      have hdb : dist b (γ t)≤ε/2 := by
        have hh:=hγ.2.2 1 (by norm_num) t ht
        rw [hγ.2.1,abs_of_nonneg (by linarith [ht.2] : 0≤1-t)] at hh
        rw [hh]
        calc
          _ ≤ (1-t)*((n+1:ℝ)*(ε/2)) := mul_le_mul_of_nonneg_left hd (by linarith [ht.2])
          _ = _ := by dsimp [t]; field_simp; ring
      obtain ⟨c,hcs,hcgt⟩:=mem_iUnion₂.mp (hcover hda)
      apply mem_iUnion₂.mpr
      refine ⟨c,hcs,?_⟩
      have hct : dist (γ t) c<ε/2 := hcgt
      exact (dist_triangle b (γ t) c).trans (by linarith)
  apply ProperSpace.of_isCompact_closedBall_of_le 0
  intro a R hR
  obtain ⟨n,hnR⟩:=exists_nat_gt (R/(ε/2))
  apply (hn a n).of_isClosed_subset isClosed_closedBall
  apply closedBall_subset_closedBall
  exact ((div_lt_iff₀ (by positivity : 0<ε/2)).mp hnR).le
end HyperbolicObstruction
end
end

section

end

end OAI
