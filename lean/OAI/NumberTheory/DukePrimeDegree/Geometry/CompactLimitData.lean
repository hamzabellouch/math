import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingCollision

namespace OAI

/-!
# Fixed observable values at compact orbit limits
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem compact_orbit_limit_with_data
    {n : ℕ} {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (p : ℕ → X n) (H : ℕ → G n) (h : G n)
    (hp : ∀ m, p m ∈ K) (hq : ∀ m, rightAction (p m) (H m) ∈ K)
    (a b : Z) (ha : ∀ m, F (p m) = a) (hb : ∀ m, F (rightAction (p m) (H m)) = b)
    (hH : Tendsto H atTop (𝓝 h)) :
    ∃ z ∈ K, rightAction z h ∈ K ∧ F z = a ∧ F (rightAction z h) = b := by
  obtain ⟨z, hz, φ, hφ, hlim⟩ := hK.isSeqCompact hp
  have hpLim : Tendsto (p ∘ φ) atTop (𝓝 z) := hlim
  have hqLim : Tendsto (fun m => rightAction (p (φ m)) (H (φ m)))
      atTop (𝓝 (rightAction z h)) :=
    (continuous_rightAction_uncurry n).continuousAt.tendsto.comp
      (hpLim.prodMk_nhds (hH.comp hφ.tendsto_atTop))
  have hz' : rightAction z h ∈ K := hK.isClosed.mem_of_tendsto hqLim
    (Eventually.of_forall fun m => hq (φ m))
  have haLim : Tendsto (fun m => F (p (φ m))) atTop (𝓝 (F z)) :=
    (hF z hz).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hpLim, Eventually.of_forall fun m => hp (φ m)⟩)
  have hbLim : Tendsto (fun m => F (rightAction (p (φ m)) (H (φ m))))
      atTop (𝓝 (F (rightAction z h))) :=
    (hF _ hz').tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hqLim, Eventually.of_forall fun m => hq (φ m)⟩)
  refine ⟨z, hz, hz', ?_, ?_⟩
  · have hc : Tendsto (fun m => F (p (φ m))) atTop (𝓝 a) := by
      simpa only [ha] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
    exact tendsto_nhds_unique haLim hc
  · have hc : Tendsto (fun m => F (rightAction (p (φ m)) (H (φ m)))) atTop (𝓝 b) := by
      simpa only [hb] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b))
    exact tendsto_nhds_unique hbLim hc

end DukePrimeDegree

end

end OAI
