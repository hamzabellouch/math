import OAI.Probability.FreeIsing.Estimates.CylinderAutomorphism
import OAI.Probability.FreeIsing.Estimates.InfiniteBlockIndependence
import OAI.Probability.FreeIsing.Estimates.RelabelMeasure
import OAI.Probability.FreeIsing.Gaussian.GlobalFreeLawNoise

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

namespace RootedBroadcast

def rerootedNoise {d : ℕ} (g : TreeAut d)
    (σ : TreeVertex d → IsingSpin) : TreeVertex d → IsingSpin :=
  noiseFromSpins (relabel g σ)

lemma measurable_rerootedNoise {d : ℕ} (g : TreeAut d) :
    Measurable (rerootedNoise g) :=
  (measurable_noiseFromSpins d).comp (measurable_relabel g)

@[simp] lemma rerootedNoise_root {d : ℕ} (g : TreeAut d)
    (σ : TreeVertex d → IsingSpin) :
    rerootedNoise g σ (ConnectedHull.root d) =
      σ (g.toEquiv.symm (ConnectedHull.root d)) := by
  simp [rerootedNoise, noiseFromSpins, ConnectedHull.root, relabel]

lemma rerootedNoise_root_of_map {d : ℕ} (g : TreeAut d)
    (r : TreeVertex d) (hr : g.toEquiv r = ConnectedHull.root d)
    (σ : TreeVertex d → IsingSpin) :
    rerootedNoise g σ (ConnectedHull.root d) = σ r := by
  rw [rerootedNoise_root, ← hr, Equiv.symm_apply_apply]

lemma rerootedNoise_nonroot {d : ℕ} (g : TreeAut d)
    (σ : TreeVertex d → IsingSpin) (v : TreeVertex d) (hv : v.1 ≠ []) :
    rerootedNoise g σ v =
      spinMul (σ (g.toEquiv.symm v)) (σ (g.toEquiv.symm (parent v))) := by
  simp [rerootedNoise, noiseFromSpins, hv, relabel]

end RootedBroadcast

lemma HasFreeIsingLaw.map_rerootedNoise {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (g : TreeAut d) :
    mu.map (RootedBroadcast.rerootedNoise g) =
      Measure.infinitePi (fun v : TreeVertex d =>
        (treeNoisePMF hlo hhi (ConnectedHull.root d) v).toMeasure) := by
  change mu.map (RootedBroadcast.noiseFromSpins ∘ relabel g) = _
  rw [← Measure.map_map (RootedBroadcast.measurable_noiseFromSpins d)
    (measurable_relabel g)]
  exact (hmu.map_relabel g).map_noiseFromSpins hlo hhi

lemma HasFreeIsingLaw.iIndepFun_rerootedNoise {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (g : TreeAut d) :
    iIndepFun (fun v : TreeVertex d => fun σ =>
      RootedBroadcast.rerootedNoise g σ v) mu := by
  let : IsProbabilityMeasure mu := hmu.isProbabilityMeasure
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun v => (measurable_pi_apply v).comp
      (RootedBroadcast.measurable_rerootedNoise g))).mpr
  change mu.map (RootedBroadcast.rerootedNoise g) = _
  rw [hmu.map_rerootedNoise hlo hhi g]
  congr 1
  funext v
  change _ = mu.map ((fun x : TreeVertex d → IsingSpin => x v) ∘
    RootedBroadcast.rerootedNoise g)
  rw [← Measure.map_map (measurable_pi_apply v)
    (RootedBroadcast.measurable_rerootedNoise g), hmu.map_rerootedNoise hlo hhi g]
  exact (Measure.infinitePi_map_eval
    (fun w : TreeVertex d =>
      (treeNoisePMF hlo hhi (ConnectedHull.root d) w).toMeasure) v).symm

lemma HasFreeIsingLaw.indepFun_rerootedNoise_blocks {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (g : TreeAut d)
    (S T : Set (TreeVertex d)) (hst : Disjoint S T) :
    IndepFun (fun σ (v : S) => RootedBroadcast.rerootedNoise g σ v)
      (fun σ (v : T) => RootedBroadcast.rerootedNoise g σ v) mu :=
  indepFun_disjoint_blocks (hmu.iIndepFun_rerootedNoise hlo hhi g)
    (fun v => (measurable_pi_apply v).comp
      (RootedBroadcast.measurable_rerootedNoise g)) S T hst

lemma HasFreeIsingLaw.iIndepFun_rerootedNoise_blocks {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (g : TreeAut d)
    {ι : Type*} (S : ι → Set (TreeVertex d))
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepFun (fun i σ (v : S i) => RootedBroadcast.rerootedNoise g σ v) mu :=
  iIndepFun_disjoint_blocks (hmu.iIndepFun_rerootedNoise hlo hhi g)
    (fun v => (measurable_pi_apply v).comp
      (RootedBroadcast.measurable_rerootedNoise g)) S hS

lemma HasFreeIsingLaw.map_rerootedNoise_blocks {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (g : TreeAut d)
    (S T : Set (TreeVertex d)) (hst : Disjoint S T) :
    mu.map (fun σ => (S.domRestrict (RootedBroadcast.rerootedNoise g σ),
      T.domRestrict (RootedBroadcast.rerootedNoise g σ))) =
      (Measure.infinitePi (fun v : S =>
        (treeNoisePMF hlo hhi (ConnectedHull.root d) v).toMeasure)).prod
      (Measure.infinitePi (fun v : T =>
        (treeNoisePMF hlo hhi (ConnectedHull.root d) v).toMeasure)) := by
  change mu.map ((fun x : TreeVertex d → IsingSpin =>
    (S.domRestrict x, T.domRestrict x)) ∘ RootedBroadcast.rerootedNoise g) = _
  rw [← Measure.map_map (by fun_prop)
    (RootedBroadcast.measurable_rerootedNoise g), hmu.map_rerootedNoise hlo hhi g]
  exact infinitePi_map_disjoint_blocks _ S T hst

end Problem367

end

end OAI
