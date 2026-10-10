import OAI.Probability.FreeIsing.Estimates.FairSpin
import OAI.Probability.FreeIsing.Estimates.IndependentLabelSampler

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.ClusterInput

local instance (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  infer_instance

abbrev Rows (d : ℕ) := TreeVertex d × ℕ → ℝ

abbrev Space (d : ℕ) :=
  (TreeVertex d → ℝ) × (Rows d × (TreeVertex d → ℝ))

def rowLaw (d : ℕ) : Measure (Rows d) :=
  Measure.infinitePi (fun _ : TreeVertex d × ℕ => uniform01)

def law (d : ℕ) : Measure (Space d) :=
  (labelMeasure d).prod ((rowLaw d).prod (labelMeasure d))

instance rowLaw_probability (d : ℕ) : IsProbabilityMeasure (rowLaw d) := by
  unfold rowLaw
  infer_instance

instance law_probability (d : ℕ) : IsProbabilityMeasure (law d) := by
  unfold law labelMeasure
  infer_instance

def relabelRows {d : ℕ} (g : TreeAut d) (Z : Rows d) : Rows d :=
  fun p => Z (g.toEquiv.symm p.1, p.2)

def relabelInputs {d : ℕ} (g : TreeAut d) (p : Space d) : Space d :=
  (relabel g p.1, relabelRows g p.2.1, relabel g p.2.2)

abbrev Seed := ℝ × ((ℕ → ℝ) × ℝ)

def seedLaw : Measure Seed :=
  uniform01.prod ((Measure.infinitePi (fun _ : ℕ => uniform01)).prod uniform01)

instance seedLaw_probability : IsProbabilityMeasure seedLaw := by
  unfold seedLaw
  infer_instance

def unpack {d : ℕ} (U : TreeVertex d → Seed) : Space d :=
  (fun v => (U v).1, (fun p => (U p.1).2.1 p.2), fun v => (U v).2.2)

lemma measurable_unpack (d : ℕ) : Measurable (@unpack d) := by
  unfold unpack
  fun_prop

@[simp] lemma unpack_relabel {d : ℕ} (g : TreeAut d) (U : TreeVertex d → Seed) :
    unpack (relabel g U) = relabelInputs g (unpack U) := rfl

lemma map_flatten_rows (d : ℕ) :
    (Measure.infinitePi (fun _ : TreeVertex d =>
      Measure.infinitePi (fun _ : ℕ => uniform01))).map
        (fun Z p => Z p.1 p.2) = rowLaw d := by
  exact Measure.infinitePi_map_curry_symm (fun (_ : TreeVertex d) (_ : ℕ) => uniform01)

lemma map_unpack (d : ℕ) :
    (Measure.infinitePi (fun _ : TreeVertex d => seedLaw)).map unpack = law d := by
  let split : (TreeVertex d → (ℕ → ℝ) × ℝ) →
      (TreeVertex d → ℕ → ℝ) × (TreeVertex d → ℝ) :=
    fun U => (fun v => (U v).1, fun v => (U v).2)
  have hsplit :
      (Measure.infinitePi (fun _ : TreeVertex d =>
        (Measure.infinitePi (fun _ : ℕ => uniform01)).prod uniform01)).map split =
        (Measure.infinitePi (fun _ : TreeVertex d =>
          Measure.infinitePi (fun _ : ℕ => uniform01))).prod (labelMeasure d) :=
    infinitePi_map_split_pairs (fun _ => Measure.infinitePi (fun _ : ℕ => uniform01))
      (fun _ => uniform01)
  let pack : (TreeVertex d → (ℕ → ℝ) × ℝ) → Rows d × (TreeVertex d → ℝ) :=
    fun U => (fun p => (U p.1).1 p.2, fun v => (U v).2)
  have hpack :
      (Measure.infinitePi (fun _ : TreeVertex d =>
        (Measure.infinitePi (fun _ : ℕ => uniform01)).prod uniform01)).map pack =
        (rowLaw d).prod (labelMeasure d) := by
    change (Measure.infinitePi _).map
      ((Prod.map (fun (Z : TreeVertex d → ℕ → ℝ) (p : TreeVertex d × ℕ) =>
        Z p.1 p.2) id) ∘ split) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop), hsplit,
      ← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
      map_flatten_rows, Measure.map_id]
  change (Measure.infinitePi (fun _ : TreeVertex d =>
    uniform01.prod ((Measure.infinitePi (fun _ : ℕ => uniform01)).prod uniform01))).map
      ((Prod.map id pack) ∘ (fun U => (fun v => (U v).1, fun v => (U v).2))) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    infinitePi_map_split_pairs,
    ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, hpack]
  rfl

theorem exists_sampler (d : ℕ) :
    ∃ S : (TreeVertex d → ℝ) → Space d,
      Measurable S ∧ (labelMeasure d).map S = law d ∧
      ∀ (g : TreeAut d) U, S (relabel g U) = relabelInputs g (S U) := by
  obtain ⟨ξ, hξ, hξlaw⟩ := exists_uniform01_sampler seedLaw
  refine ⟨unpack ∘ vertexSampler ξ, (measurable_unpack d).comp
    (measurable_vertexSampler hξ), ?_, ?_⟩
  · rw [← Measure.map_map (measurable_unpack d) (measurable_vertexSampler hξ),
      map_vertexSampler_labelMeasure hξ, hξlaw]
    exact map_unpack d
  · intro g U
    rfl

abbrev SpinSpace (d : ℕ) :=
  ((TreeVertex d → ℝ) × Rows d) × (TreeVertex d → IsingSpin)

def spinLaw (d : ℕ) : Measure (SpinSpace d) :=
  ((labelMeasure d).prod (rowLaw d)).prod
    (Measure.infinitePi (fun _ : TreeVertex d => uniform01.map fairSpin))

def relabelSpinInputs {d : ℕ} (g : TreeAut d) (p : SpinSpace d) : SpinSpace d :=
  ((relabel g p.1.1, relabelRows g p.1.2), relabel g p.2)

def toSpinInputs {d : ℕ} (p : Space d) : SpinSpace d :=
  ((p.1, p.2.1), vertexSampler fairSpin p.2.2)

lemma measurable_toSpinInputs (d : ℕ) : Measurable (@toSpinInputs d) := by
  exact (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_vertexSampler measurable_fairSpin).comp
      (measurable_snd.comp measurable_snd))

@[simp] lemma toSpinInputs_relabel {d : ℕ} (g : TreeAut d) (p : Space d) :
    toSpinInputs (relabelInputs g p) = relabelSpinInputs g (toSpinInputs p) := rfl

lemma map_toSpinInputs (d : ℕ) : (law d).map toSpinInputs = spinLaw d := by
  change ((labelMeasure d).prod ((rowLaw d).prod (labelMeasure d))).map
    ((Prod.map id (vertexSampler fairSpin)) ∘ MeasurableEquiv.prodAssoc.symm) = _
  rw [← Measure.map_map (measurable_id.prodMap
      (measurable_vertexSampler measurable_fairSpin))
      MeasurableEquiv.prodAssoc.symm.measurable,
    (measurePreserving_prodAssoc (labelMeasure d) (rowLaw d) (labelMeasure d)).symm.map_eq,
    ← Measure.map_prod_map _ _ measurable_id (measurable_vertexSampler measurable_fairSpin),
    Measure.map_id, map_vertexSampler_labelMeasure measurable_fairSpin]
  rfl

theorem exists_spin_sampler (d : ℕ) :
    ∃ S : (TreeVertex d → ℝ) → SpinSpace d,
      Measurable S ∧ (labelMeasure d).map S = spinLaw d ∧
      ∀ (g : TreeAut d) U, S (relabel g U) = relabelSpinInputs g (S U) := by
  obtain ⟨S, hS, hSlaw, hSeq⟩ := exists_sampler d
  refine ⟨toSpinInputs ∘ S, (measurable_toSpinInputs d).comp hS, ?_, ?_⟩
  · rw [← Measure.map_map (measurable_toSpinInputs d) hS, hSlaw, map_toSpinInputs]
  · intro g U
    change toSpinInputs (S (relabel g U)) = _
    rw [hSeq]
    rfl

theorem isFactorOfIID_of_spin_inputs {d : ℕ} {theta : ℝ}
    (H : SpinSpace d → (TreeVertex d → IsingSpin)) (hH : Measurable H)
    (hLaw : HasFreeIsingLaw theta ((spinLaw d).map H))
    (hEquiv : ∀ g : TreeAut d, ∀ᵐ p ∂spinLaw d,
      H (relabelSpinInputs g p) = relabel g (H p)) :
    IsFactorOfIID d theta := by
  obtain ⟨S, hS, hSlaw, hSeq⟩ := exists_spin_sampler d
  refine ⟨H ∘ S, hH.comp hS, ?_, ?_⟩
  · rw [← Measure.map_map hH hS, hSlaw]
    exact hLaw
  · intro g
    have h : ∀ᵐ p ∂(labelMeasure d).map S,
        H (relabelSpinInputs g p) = relabel g (H p) := by
      rw [hSlaw]
      exact hEquiv g
    filter_upwards [ae_of_ae_map hS.aemeasurable h] with U hU
    simpa only [Function.comp_apply, hSeq] using hU

end Problem367.ClusterInput

end

end OAI
