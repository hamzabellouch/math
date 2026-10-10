import OAI.Probability.FreeIsing.Trees.WeightEncoding

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

local instance freeLawNoiseMeasurableSingleton : MeasurableSingletonClass IsingSpin where
  measurableSet_singleton _ := trivial

def treeNoisePMF {d : ℕ} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (r v : TreeVertex d) : PMF IsingSpin :=
  PMF.ofFintype (fun s => ENNReal.ofReal (treeNoiseMass theta r v s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => treeNoiseMass_nonneg hlo hhi r v s)]
    simp [treeNoiseMass_sum])

@[simp] lemma treeNoisePMF_apply {d : ℕ} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (r v : TreeVertex d) (s : IsingSpin) :
    treeNoisePMF hlo hhi r v s = ENNReal.ofReal (treeNoiseMass theta r v s) := rfl

@[simp] lemma treeNoisePMF_toMeasure_singleton {d : ℕ} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (r v : TreeVertex d) (s : IsingSpin) :
    (treeNoisePMF hlo hhi r v).toMeasure {s} =
      ENNReal.ofReal (treeNoiseMass theta r v s) := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton s)]
  rfl

lemma measurable_connectedSpinEncode_restrict {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    Measurable (fun σ : TreeVertex d → IsingSpin =>
      connectedSpinEncode hD r hr hmin (fun v : D => σ v)) := by
  apply (measurable_of_finite (connectedSpinEncode hD r hr hmin)).comp
  exact Measurable.of_eval (fun v => measurable_pi_apply v.1)

lemma HasFreeIsingLaw.connectedSpinEncode_atom {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) (ξ : D → IsingSpin) :
    mu {σ | connectedSpinEncode hD r hr hmin (fun v : D => σ v) = ξ} =
      ENNReal.ofReal (∏ v : D, treeNoiseMass theta r v (ξ v)) := by
  classical
  let τ : D → IsingSpin := (connectedSpinEquiv hD r hr hmin).symm ξ
  let eta : TreeVertex d → IsingSpin := fun v =>
    if hv : v ∈ D then τ ⟨v, hv⟩ else .neg
  have heta : (fun v : D => eta v) = τ := by
    funext v
    simp [eta, v.2]
  have hcode : connectedSpinEncode hD r hr hmin (fun v : D => eta v) = ξ := by
    rw [heta]
    exact (connectedSpinEquiv hD r hr hmin).apply_symm_apply ξ
  have hevent : {σ : TreeVertex d → IsingSpin | connectedSpinEncode hD r hr hmin (fun v : D => σ v) = ξ} =
      {σ | ∀ v ∈ D, σ v = eta v} := by
    ext σ
    constructor
    · intro h
      have heq : (fun v : D => σ v) = (fun v : D => eta v) :=
        connectedSpinEncode_injective hD r hr hmin (h.trans hcode.symm)
      intro v hv
      exact congrFun heq ⟨v, hv⟩
    · intro h
      have heq : (fun v : D => σ v) = (fun v : D => eta v) := by
        funext v
        exact h v v.2
      change connectedSpinEncode hD r hr hmin (fun v : D => σ v) = ξ
      rw [heq, hcode]
  rw [hevent, hmu D hD eta, hD.freeCylinderWeight_eq_noise_prod r hr hmin, hcode]

lemma HasFreeIsingLaw.map_connectedSpinEncode {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    Measure.map (fun σ : TreeVertex d → IsingSpin =>
      connectedSpinEncode hD r hr hmin (fun v : D => σ v)) mu =
      Measure.pi (fun v : D => (treeNoisePMF hlo hhi r v).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro ξ
  rw [Measure.map_apply (measurable_connectedSpinEncode_restrict hD r hr hmin)
    (measurableSet_singleton ξ)]
  change mu {σ | connectedSpinEncode hD r hr hmin (fun v : D => σ v) = ξ} = _
  rw [hmu.connectedSpinEncode_atom hD r hr hmin ξ, Measure.pi_singleton]
  simp only [treeNoisePMF_toMeasure_singleton]
  exact ENNReal.ofReal_prod_of_nonneg (fun v _ => treeNoiseMass_nonneg hlo hhi r v (ξ v))

lemma HasFreeIsingLaw.map_connectedSpinEncode_coord {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) (v : D) :
    Measure.map (fun σ : TreeVertex d → IsingSpin =>
      connectedSpinEncode hD r hr hmin (fun w : D => σ w) v) mu =
      (treeNoisePMF hlo hhi r v).toMeasure := by
  change Measure.map ((fun f : D → IsingSpin => f v) ∘
    (fun σ : TreeVertex d → IsingSpin =>
      connectedSpinEncode hD r hr hmin (fun w : D => σ w))) mu = _
  rw [← Measure.map_map (measurable_pi_apply v)
    (measurable_connectedSpinEncode_restrict hD r hr hmin)]
  rw [hmu.map_connectedSpinEncode hlo hhi hD r hr hmin]
  exact (measurePreserving_eval (fun w : D => (treeNoisePMF hlo hhi r w).toMeasure) v).map_eq

lemma HasFreeIsingLaw.iIndepFun_connectedSpinEncode {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length) :
    ProbabilityTheory.iIndepFun (fun v : D => fun σ : TreeVertex d → IsingSpin =>
      connectedSpinEncode hD r hr hmin (fun w : D => σ w) v) mu := by
  let F := fun σ : TreeVertex d → IsingSpin =>
    connectedSpinEncode hD r hr hmin (fun w : D => σ w)
  have hF : Measurable F := measurable_connectedSpinEncode_restrict hD r hr hmin
  have hmap : Measure.map F mu =
      Measure.pi (fun v : D => (treeNoisePMF hlo hhi r v).toMeasure) :=
    hmu.map_connectedSpinEncode hlo hhi hD r hr hmin
  let : IsProbabilityMeasure (Measure.map F mu) := by
    rw [hmap]
    infer_instance
  let : IsProbabilityMeasure mu := Measure.isProbabilityMeasure_of_map hF.aemeasurable
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun v => ((measurable_pi_apply v).comp hF).aemeasurable)).mpr
  change Measure.map F mu = Measure.pi (fun v : D => Measure.map (fun σ => F σ v) mu)
  rw [hmap]
  congr 1
  funext v
  exact (hmu.map_connectedSpinEncode_coord hlo hhi hD r hr hmin v).symm

end Problem367

end

end OAI
