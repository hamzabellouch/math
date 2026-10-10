import OAI.Probability.DilutedSpin.UpperRealEndpoint

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators

lemma integrable_rootArray_sum {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → ℝ) (hg : Integrable g μ) (k : ℕ) :
    Integrable (fun z : RootPath X k => ∑ a,g (rootArray k z a)) (rootLaw k (fun _ => μ)) := by
  apply integrable_finsetSum
  intro a _
  simpa only [Function.comp_def, rootArrayEquiv_apply] using
    (measurePreserving_rootArray μ k).integrable_comp_of_integrable
      (integrable_comp_eval (μ := fun _ : Fin k => μ) (i := a) hg)

lemma integral_rootArray_sum {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → ℝ) (hg : Integrable g μ) (k : ℕ) :
    (∫ z : RootPath X k,∑ a,g (rootArray k z a) ∂rootLaw k (fun _ => μ))=k*∫ x,g x ∂μ := by
  rw [integral_rootArray_eq_pi μ k (fun z => ∑ a,g (z a)),
    integral_finsetSum _ (fun a _ => integrable_comp_eval (μ := fun _ : Fin k => μ) (i := a) hg)]
  have he (a : Fin k) : (∫ z : Fin k → X,g (z a) ∂Measure.pi (fun _ => μ))=∫ x,g x ∂μ :=
    integral_comp_eval (μ := fun _ : Fin k => μ) (i := a) hg.aestronglyMeasurable
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

namespace PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma datumRoot_norm_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |datumRoot T U V x m j f k l z w|≤B+(∑ a,‖(rootArray k z a).1.1‖)+(∑ a,‖(rootArray l w a).1.1‖) := by
  have hbase (y : FinitePath Ω n) :
      |realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f y|≤B+∑ a,‖(rootArray k z a).1.1‖ := by
    apply (abs_add_le _ _).trans
    apply add_le_add (hf y)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun a _ => by simpa only [rootArray_rootMap,Real.norm_eq_abs] using norm_le_pi_norm (rootArray k z a).1.1 _)
  simpa only [rootArray_rootMap,datumRoot] using cavityRoot_bound T U V x m hm j l
    (rootMap (fun a => a.2.2) l w) (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w) _ hbase

omit [MeasurableSingletonClass R] in
lemma upperDatum_integrable_norm (M : Model p) (hM : Admissible M) (Q : FiniteLaw R) :
    Integrable (fun a : UpperDatum p N R => ‖a.1.1‖) (upperDatumLaw (N := N) M Q) :=
  measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable

lemma datumRoot_integrable_firstMoment (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    Integrable (fun z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l =>
      datumRoot T U V x m j f k l z.1 z.2)
      ((rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) := by
  have hk := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) (fun a => ‖a.1.1‖) (upperDatum_integrable_norm M hM Q) k
  have hl := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) (fun a => ‖a.1.1‖) (upperDatum_integrable_norm M hM Q) l
  apply ((integrable_const B).add (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))).add (hl.comp_snd (rootLaw k (fun _ => upperDatumLaw (N := N) M Q))) |>.mono'
    (measurable_datumRoot T U V x m j f k l).aestronglyMeasurable
  exact ae_of_all _ (fun z => datumRoot_norm_bound T U V x m hm j f k l z.1 z.2 hf)

lemma upperCountMean_bound_firstMoment (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |upperCountMean M T Q U V x m j f k l|≤B+(∫ a,‖a.1‖ ∂M.disorder.toMeasure)*(k+l) := by
  let g := fun a : UpperDatum p N R => ‖a.1.1‖
  have hg := upperDatum_integrable_norm (N := N) M hM Q
  have hk := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) g hg k
  have hl := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) g hg l
  have hB := ((integrable_const B).add (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))).add (hl.comp_snd (rootLaw k (fun _ => upperDatumLaw (N := N) M Q)))
  unfold upperCountMean
  rw [← integral_prod _ (datumRoot_integrable_firstMoment M hM Q T U V x m hm j f k l hf)]
  apply (abs_integral_le_integral_abs).trans
  apply (integral_mono (datumRoot_integrable_firstMoment M hM Q T U V x m hm j f k l hf).abs hB
    (fun z => datumRoot_norm_bound T U V x m hm j f k l z.1 z.2 hf)).trans_eq
  change (∫ z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l,
      (B + ∑ a, g (rootArray k z.1 a)) + ∑ a, g (rootArray l z.2 a)
      ∂(rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) = _
  have he1 := integral_add ((integrable_const B).add (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))) (hl.comp_snd (rootLaw k (fun _ => upperDatumLaw (N := N) M Q)))
  have he2 := integral_add (integrable_const B) (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))
  simp only [Pi.add_apply] at he1 he2
  rw [he1,he2]
  have hek : (∫ z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l,
      ∑ a,g (rootArray k z.1 a) ∂(rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod
        (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) =
      ∫ z : RootPath (UpperDatum p N R) k,∑ a,g (rootArray k z a) ∂rootLaw k (fun _ => upperDatumLaw (N := N) M Q) :=
    by simpa only [probReal_univ,one_smul] using (integral_fun_fst (μ := rootLaw k (fun _ => upperDatumLaw (N := N) M Q)) (ν := rootLaw l (fun _ => upperDatumLaw (N := N) M Q)) (fun z => ∑ a,g (rootArray k z a)))
  have hel : (∫ z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l,
      ∑ a,g (rootArray l z.2 a) ∂(rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod
        (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) =
      ∫ z : RootPath (UpperDatum p N R) l,∑ a,g (rootArray l z a) ∂rootLaw l (fun _ => upperDatumLaw (N := N) M Q) :=
    by simpa only [probReal_univ,one_smul] using (integral_fun_snd (μ := rootLaw k (fun _ => upperDatumLaw (N := N) M Q)) (ν := rootLaw l (fun _ => upperDatumLaw (N := N) M Q)) (fun z => ∑ a,g (rootArray l z a)))
  rw [hek,hel,integral_rootArray_sum _ g hg k,integral_rootArray_sum _ g hg l]
  have he : (∫ a,g a ∂upperDatumLaw (N := N) M Q)=∫ a,‖a.1‖ ∂M.disorder.toMeasure := by
    simpa only [g,upperDatumLaw,probReal_univ,one_smul] using (integral_fun_fst (μ := M.disorder.toMeasure) (ν := ((FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).asProbability id).toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) (fun a : InteractionSample p => ‖a.1‖))
  rw [he]
  simp only [integral_const,probReal_univ,one_smul]
  ring

end PrescribedTree
end DilutedSpinGlass

end

end OAI
