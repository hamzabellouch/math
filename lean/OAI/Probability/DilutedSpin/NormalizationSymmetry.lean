import OAI.Probability.DilutedSpin.InsertionStability

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def centeredInteraction {p : ℕ} (z : InteractionSample p) : Interaction p :=
  fun s => z.1 s-z.1 (fun _ => true)

noncomputable def normalizedFactor {p : ℕ} (z : ℝ×(Fin p → Spin → ℝ)) : Interaction p :=
  fun s => Real.log (1+z.1*∏ l,z.2 l (s l))-Real.log (1+z.1*∏ l,z.2 l true)

lemma measurable_centeredInteraction (p : ℕ) : Measurable (centeredInteraction (p := p)) := by
  unfold centeredInteraction
  fun_prop
lemma measurable_normalizedFactor (p : ℕ) : Measurable (normalizedFactor (p := p)) := by
  unfold normalizedFactor
  fun_prop

lemma centeredInteraction_factorization {p : ℕ} (M : Model p) (hM : Admissible M) :
    centeredInteraction =ᵐ[M.disorder.toMeasure] (fun z => normalizedFactor (z.2.2.1,z.2.2.2)) := by
  filter_upwards [hM.factorization] with z hz
  funext s
  have hp (s : Fin p → Spin) : 0<1+z.2.2.1*∏ l,z.2.2.2 l (s l) := by
    have hh := (abs_lt.mp (hz.2 s).2).1
    linarith
  have he (s : Fin p → Spin) : z.1 s = Real.log z.2.1 + Real.log (1+z.2.2.1*∏ l,z.2.2.2 l (s l)) := by
    rw [← Real.log_mul hz.1.ne' (hp s).ne',← (hz.2 s).1,Real.log_exp]
  simp only [centeredInteraction,normalizedFactor,he]
  ring

lemma normalizedFactor_permutation {p : ℕ} (e : Equiv.Perm (Fin p))
    (b : ℝ) (f : Fin p → Spin → ℝ) :
    normalizedFactor (b,fun l => f (e.symm l)) =
      (fun s => normalizedFactor (b,f) (fun l => s (e l))) := by
  funext s
  unfold normalizedFactor
  have h1 : (∏ l, f (e.symm l) (s l)) = ∏ l, f l (s (e l)) := by
    simpa only [Equiv.symm_apply_apply] using (Equiv.prod_comp e (fun l => f (e.symm l) (s l))).symm
  have h2 : (∏ l, f (e.symm l) true) = ∏ l, f l true := Equiv.prod_comp e.symm (fun l => f l true)
  rw [h1,h2]

/-- Exact symmetry of the centered physical interaction, derived from the
 original factorization, iid coordinates and independent b. The multiplier a
 need not be independent of anything, nor need log a be integrable. -/
theorem centeredInteraction_permutation {p : ℕ} (M : Model p) (hM : Admissible M)
    (e : Equiv.Perm (Fin p)) :
    IdentDistrib (centeredInteraction (p := p))
      (fun z s => centeredInteraction z (fun l => s (e l)))
      M.disorder.toMeasure M.disorder.toMeasure := by
  have hf := IdentDistrib.pi (fun l => hM.identically_distributed_f l (e.symm l))
    hM.independent_f (hM.independent_f.precomp e.symm.injective)
  have hb : IdentDistrib (fun z : InteractionSample p => z.2.2.1)
      (fun z : InteractionSample p => z.2.2.1) M.disorder.toMeasure M.disorder.toMeasure :=
    IdentDistrib.refl (by fun_prop)
  have hj := hb.prodMk hf hM.independent_b
    (hM.independent_b.comp measurable_id (show Measurable (fun f : Fin p → Spin → ℝ => fun l => f (e.symm l)) by fun_prop))
  have hn := hj.comp (measurable_normalizedFactor p)
  simp only [Function.comp_def] at hn
  simp_rw [normalizedFactor_permutation e] at hn
  have hc := IdentDistrib.of_ae_eq (measurable_centeredInteraction p).aemeasurable
    (centeredInteraction_factorization M hM)
  have hp := hc.comp (show Measurable (fun θ : Interaction p => fun s : Fin p → Spin => θ (fun l => s (e l))) by fun_prop)
  exact hc.trans (hn.trans hp.symm)

lemma centeredInteraction_norm_le {p : ℕ} (z : InteractionSample p) : ‖centeredInteraction z‖≤2*‖z.1‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro s
  exact (norm_sub_le _ _).trans ((add_le_add (norm_le_pi_norm z.1 s)
    (norm_le_pi_norm z.1 (fun _ => true))).trans_eq (by ring))

lemma centeredInteraction_integrable {p : ℕ} (M : Model p)
    (h : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) :
    Integrable (fun z => ‖centeredInteraction z‖) M.disorder.toMeasure := by
  apply (h.const_mul 2).mono' ((measurable_centeredInteraction p).norm.aestronglyMeasurable)
  exact ae_of_all _ (fun z => by simpa only [norm_norm] using centeredInteraction_norm_le z)
end DilutedSpinGlass

end

end OAI
