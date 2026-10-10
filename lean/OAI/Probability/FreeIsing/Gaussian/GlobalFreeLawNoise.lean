import OAI.Probability.FreeIsing.Estimates.LawUniqueness
import OAI.Probability.FreeIsing.Gaussian.FreeLawNoise
import OAI.Probability.FreeIsing.Spins.Moments
import OAI.Probability.FreeIsing.Trees.ConnectedHull
import OAI.Probability.FreeIsing.Trees.RootedBroadcast

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

lemma RootedBroadcast.noiseFromSpins_restrict {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) (σ : TreeVertex d → IsingSpin) :
    D.restrict (noiseFromSpins σ) =
      connectedSpinEncode hD (ConnectedHull.root d) hr
        (fun _ _ => Nat.zero_le _) (D.restrict σ) := by
  classical
  funext v
  by_cases hv : v.1 = ConnectedHull.root d
  · have hnil : v.1.1 = [] := congrArg Subtype.val hv
    simp [noiseFromSpins, connectedSpinEncode, hv, ConnectedHull.root]
  · have hnil : v.1.1 ≠ [] := by
      intro hn
      exact hv (Subtype.ext hn)
    simp [noiseFromSpins, connectedSpinEncode, hv, hnil,
      spinMul, spinAgreementCode, eq_comm]

lemma HasFreeIsingLaw.map_noiseFromSpins {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) :
    Measure.map RootedBroadcast.noiseFromSpins mu =
      Measure.infinitePi (fun v : TreeVertex d =>
        (treeNoisePMF hlo hhi (ConnectedHull.root d) v).toMeasure) := by
  classical
  let : IsProbabilityMeasure mu := hmu.isProbabilityMeasure
  apply measure_eq_of_cofinal_restrict_eq
    (fun D => ConnectedFinset D ∧ ConnectedHull.root d ∈ D)
  · intro D
    refine ⟨ConnectedHull.hull D, ConnectedHull.subset_hull D,
      ConnectedHull.connected_hull D, ?_⟩
    exact Finset.mem_insert_self _ _
  · intro D hD
    rw [Measure.map_map (Finset.measurable_restrict D)
      (RootedBroadcast.measurable_noiseFromSpins d)]
    have hfun : D.restrict ∘ RootedBroadcast.noiseFromSpins =
        (fun σ : TreeVertex d → IsingSpin =>
          connectedSpinEncode hD.1 (ConnectedHull.root d) hD.2
            (fun _ _ => Nat.zero_le _) (fun v : D => σ v)) := by
      funext σ
      exact RootedBroadcast.noiseFromSpins_restrict hD.1 hD.2 σ
    rw [hfun]
    exact (hmu.map_connectedSpinEncode hlo hhi hD.1 (ConnectedHull.root d) hD.2
      (fun _ _ => Nat.zero_le _)).trans (Measure.infinitePi_map_restrict
      (fun v : TreeVertex d => (treeNoisePMF hlo hhi (ConnectedHull.root d) v).toMeasure)
      (I := D)).symm

lemma HasFreeIsingLaw.map_noiseFromSpins_coord {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (v : TreeVertex d) :
    Measure.map (fun σ => RootedBroadcast.noiseFromSpins σ v) mu =
      (treeNoisePMF hlo hhi (ConnectedHull.root d) v).toMeasure := by
  change Measure.map ((fun x : TreeVertex d → IsingSpin => x v) ∘
    RootedBroadcast.noiseFromSpins) mu = _
  rw [← Measure.map_map (measurable_pi_apply v)
    (RootedBroadcast.measurable_noiseFromSpins d), hmu.map_noiseFromSpins hlo hhi]
  exact Measure.infinitePi_map_eval _ v

lemma HasFreeIsingLaw.iIndepFun_noiseFromSpins {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) :
    ProbabilityTheory.iIndepFun
      (fun v : TreeVertex d => fun σ => RootedBroadcast.noiseFromSpins σ v) mu := by
  let : IsProbabilityMeasure mu := hmu.isProbabilityMeasure
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun v => (measurable_pi_apply v).comp
      (RootedBroadcast.measurable_noiseFromSpins d))).mpr
  change Measure.map RootedBroadcast.noiseFromSpins mu = _
  rw [hmu.map_noiseFromSpins hlo hhi]
  congr 1
  funext v
  exact (hmu.map_noiseFromSpins_coord hlo hhi v).symm

lemma HasFreeIsingLaw.eq_map_ofNoise {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) :
    mu = Measure.map RootedBroadcast.ofNoise
      (Measure.infinitePi (fun v : TreeVertex d =>
        (treeNoisePMF hlo hhi (ConnectedHull.root d) v).toMeasure)) := by
  rw [← hmu.map_noiseFromSpins hlo hhi,
    Measure.map_map (RootedBroadcast.measurable_ofNoise d)
      (RootedBroadcast.measurable_noiseFromSpins d)]
  have hfun : RootedBroadcast.ofNoise ∘ RootedBroadcast.noiseFromSpins =
      (id : (TreeVertex d → IsingSpin) → (TreeVertex d → IsingSpin)) := by
    funext σ
    exact RootedBroadcast.ofNoise_noiseFromSpins σ
  rw [hfun, Measure.map_id]

end Problem367

end

end OAI
