import OAI.NumberTheory.PrimePackets.ConditionalFibers

namespace OAI

/-! # Conditioning a leaf kernel on a finite observed label

Adding a finite label to the transverse coordinate restricts the actual
conditional leaf to the corresponding label fiber and normalizes it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]

def finiteLabelLift {N : ℕ} (Q : S × T → Fin N) (z : S × T) : (S × Fin N) × T :=
  ((z.1,Q z),z.2)

omit [StandardBorelSpace T] [Nonempty T] in
lemma finiteLabelLift_measurable {N : ℕ} {Q : S × T → Fin N} (hQ : Measurable Q) :
    Measurable (finiteLabelLift Q) :=
  (measurable_fst.prodMk hQ).prodMk measurable_snd

omit [StandardBorelSpace T] [Nonempty T] in
lemma finiteLabelLift_restrict {N : ℕ} (ρ : Measure (S × T))
    {Q : S × T → Fin N} (hQ : Measurable Q) (b : Fin N) :
    (ρ.map (finiteLabelLift Q)).restrict ({s : S × Fin N | s.2=b} ×ˢ univ) =
      (ρ.restrict {z | Q z=b}).map (fun z : S × T => ((z.1,b),z.2)) := by
  rw [Measure.restrict_map (finiteLabelLift_measurable hQ)
    ((measurableSet_eq_fun measurable_snd measurable_const).prod MeasurableSet.univ)]
  have he : finiteLabelLift Q ⁻¹' ({s : S × Fin N | s.2=b} ×ˢ univ) = {z | Q z=b} := by
    ext z
    simp [finiteLabelLift]
  rw [he]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (measurableSet_eq_fun hQ measurable_const)] with z hz
  simp only [finiteLabelLift,hz]

theorem finiteLabelLift_condKernel_on_label {N : ℕ}
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {Q : S × T → Fin N} (hQ : Measurable Q) (b : Fin N) :
    ∀ᵐ s ∂(ρ.restrict {z | Q z=b}).fst,
      (ρ.map (finiteLabelLift Q)).condKernel (s,b) =
        ((ρ.restrict {z | Q z=b}).condKernel s) := by
  let σ := ρ.map (finiteLabelLift Q)
  let U : Set (S × Fin N) := {s | s.2=b}
  let ρb := ρ.restrict {z | Q z=b}
  have hU : MeasurableSet U := measurableSet_eq_fun measurable_snd measurable_const
  have hs : σ.restrict (U ×ˢ univ) =
      ρb.map (fun z : S × T => ((z.1,b),z.2)) := finiteLabelLift_restrict ρ hQ b
  have hm : (σ.restrict (U ×ˢ univ)).fst = σ.fst.restrict U := by
    rw [restricted_conditional_marginal σ hU MeasurableSet.univ]
    simp only [measure_univ,withDensity_const,one_smul]
  have hmap : (σ.restrict (U ×ˢ univ)).fst = ρb.fst.map (fun s : S => (s,b)) := by
    rw [hs]
    exact fst_map_fibers_of_measurable ρb
      (fun s : S => (s,b)) (measurable_id.prodMk measurable_const) Prod.snd measurable_snd
  have hrestr := restricted_conditional_kernel σ hU MeasurableSet.univ
  simp only [measure_univ,one_smul,Measure.restrict_univ] at hrestr
  rw [←hm,hmap] at hrestr
  have hrestr' := ae_of_ae_map (measurable_id.prodMk measurable_const).aemeasurable hrestr
  have hfixed := conditional_map_fibers_leftInverse ρb
    (fun s : S => (s,b)) (measurable_id.prodMk measurable_const)
    Prod.fst measurable_fst (fun _ => rfl) Prod.snd measurable_snd
  filter_upwards [hrestr',hfixed] with s hs' hf
  simp only [hs,id_eq] at hs'
  change _ = (ρb.condKernel s).map id at hf
  rw [Measure.map_id] at hf
  exact hs'.symm.trans hf

theorem finiteLabelLift_condKernel {N : ℕ}
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {Q : S × T → Fin N} (hQ : Measurable Q) :
    ∀ᵐ z ∂ρ,
      ρ.condKernel z.1 {t | Q (z.1,t)=Q z} ≠ 0 ∧
      (ρ.map (finiteLabelLift Q)).condKernel (z.1,Q z) =
        (anchorNormalize (ρ.condKernel z.1) {t | Q (z.1,t)=Q z}).restrict
          {t | Q (z.1,t)=Q z} := by
  have H (b : Fin N) : ∀ᵐ z ∂ρ.restrict {z | Q z=b},
      ρ.condKernel z.1 {t | Q (z.1,t)=b} ≠ 0 ∧
      (ρ.map (finiteLabelLift Q)).condKernel (z.1,b) =
        (anchorNormalize (ρ.condKernel z.1) {t | Q (z.1,t)=b}).restrict
          {t | Q (z.1,t)=b} := by
    have hb := (finiteLabelLift_condKernel_on_label ρ hQ b).and
      (conditional_restrict_normalized ρ {z | Q z=b} (measurableSet_eq_fun hQ measurable_const))
    have hb' := ae_of_ae_map measurable_fst.aemeasurable hb
    filter_upwards [hb'] with z hz
    exact ⟨hz.2.1,hz.1.trans hz.2.2⟩
  have H' (b : Fin N) : ∀ᵐ z ∂ρ, Q z=b →
      ρ.condKernel z.1 {t | Q (z.1,t)=b} ≠ 0 ∧
      (ρ.map (finiteLabelLift Q)).condKernel (z.1,b) =
        (anchorNormalize (ρ.condKernel z.1) {t | Q (z.1,t)=b}).restrict
          {t | Q (z.1,t)=b} :=
    (ae_restrict_iff' (measurableSet_eq_fun hQ measurable_const)).mp (H b)
  filter_upwards [ae_all_iff.mpr H'] with z hz
  exact hz (Q z) rfl

end DukePrimeDegree

end

end OAI
