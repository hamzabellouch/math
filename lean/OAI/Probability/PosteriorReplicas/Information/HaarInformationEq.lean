import OAI.Probability.PosteriorReplicas.Gaussian.GaussianWishart
import OAI.Probability.PosteriorReplicas.Information.RandomProjectionInformation

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma measurable_gramSchmidtNormed_rows {d ℓ : ℕ} :
    Measurable (gramSchmidtNormed ℝ : Rows d ℓ → Rows d ℓ) :=
  Measurable.of_eval (fun index => measurable_gramSchmidtNormed index)

instance haarRows_probability (d ℓ : ℕ) : IsProbabilityMeasure (haarRows d ℓ) := by
  unfold haarRows
  infer_instance

lemma cmi_attachSide_equiv {X Y Z Z' : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace Z']
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    [Fintype Y] [MeasurableSingletonClass Y]
    {g : X → Z} (hg : Measurable g) (e : Z ≃ᵐ Z')
    (q : Measure (X × Y)) [IsProbabilityMeasure q] :
    cmi (attachSide (e ∘ g) q) = cmi (attachSide g q) := by
  have hh := mutualInformation_attachSide_chain hg q
  have hh' := mutualInformation_attachSide_chain (e.measurable.comp hg) q
  have hp : ((q.fst.map g).prod q.snd).map (Prod.map e id) =
      (q.fst.map (e ∘ g)).prod q.snd := by
    rw [← Measure.map_prod_map _ _ e.measurable measurable_id,Measure.map_id,
      Measure.map_map e.measurable hg]
  have hq : (q.map (fun z => (g z.1,z.2))).map (Prod.map e id) =
      q.map (fun z => ((e ∘ g) z.1,z.2)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have he := klDiv_map_leftInverse (q.map (fun z => (g z.1,z.2)))
    ((q.fst.map g).prod q.snd)
    (show Measurable (Prod.map e id : Z×Y → Z'×Y) by fun_prop)
    (show Measurable (Prod.map e.symm id : Z'×Y → Z×Y) by fun_prop)
    (by intro z; exact Prod.ext (e.symm_apply_apply z.1) rfl)
  rw [hp,hq] at he
  rw [he] at hh'
  have hfin : klDiv q (q.fst.prod q.snd) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (mutualInformation_le_finiteEntropy q)
  have hB : klDiv (q.map (fun z => (g z.1,z.2))) ((q.fst.map g).prod q.snd) ≠ ∞ := by
    apply ne_top_of_le_ne_top hfin
    rw [hh]
    exact le_add_left le_rfl
  exact (ENNReal.add_left_inj hB).mp (hh'.symm.trans hh)

lemma cmi_labels_gramSchmidtNormed {d ℓ N : ℕ} [NeZero N]
    {A : Rows d ℓ} (hA : LinearIndependent ℝ A)
    (q : Measure (Vec d × Fin N)) [IsProbabilityMeasure q] :
    cmi (attachSide (labels (gramSchmidtNormed ℝ A)) q) =
      cmi (attachSide (labels A) q) := by
  let e := (matrixLinearEquiv (pairingTriangular A).transpose
    (pairingTriangular_det_pos hA).ne').toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : labels A = e ∘ labels (gramSchmidtNormed ℝ A) := pairings_eq_triangular hA
  rw [he]
  exact (cmi_attachSide_equiv (by unfold labels; fun_prop) e q).symm

lemma cmi_haar_eq_gaussian {d ℓ N : ℕ} [NeZero N] (hℓ : ℓ ≤ d)
    (q : Measure (Vec d × Fin N)) [IsProbabilityMeasure q] :
    cmi (randomSideLaw (haarRows d ℓ) (fun z => labels z.1 z.2) q) =
      conditionalInformation (sideLaw ℓ q) := by
  change cmi (randomSideLaw (haarRows d ℓ) (fun z => labels z.1 z.2) q) =
    cmi (randomSideLaw (gaussianRows d ℓ) (fun z => labels z.1 z.2) q)
  rw [cmi_randomSideLaw _ measurable_labels,cmi_randomSideLaw _ measurable_labels]
  rw [haarRows,lintegral_map (measurable_cmi_attachSide measurable_labels q)
    measurable_gramSchmidtNormed_rows]
  apply lintegral_congr_ae
  have hfull := ae_gaussian_columns_independent (E := Vec d) ℓ (by simpa using hℓ)
  filter_upwards [hfull] with A hA
  exact cmi_labels_gramSchmidtNormed hA q

end PosteriorReplicas
end

end OAI
