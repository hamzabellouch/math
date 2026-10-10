import OAI.Probability.DilutedSpin.CountBridgeTools
import OAI.Probability.DilutedSpin.UpperCountState

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators

def rootMap {X Y : Type} (f : X → Y) : (k : ℕ) → RootPath X k → RootPath Y k
  | 0,_ => ()
  | k+1,z => (f z.1,rootMap f k z.2)

lemma rootArray_rootMap {X Y : Type} (f : X → Y) (k : ℕ) (z : RootPath X k) (i : Fin k) :
    rootArray k (rootMap f k z) i=f (rootArray k z i) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases rfl (fun i => ?_) i
    exact ih z.2 i

lemma measurable_rootMap {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) (k : ℕ) : Measurable (rootMap f k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact (hf.comp measurable_fst).prodMk (ih.comp measurable_snd)

lemma rootLaw_ae_every {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {P : X → Prop} (hP : ∀ᵐ x ∂μ,P x) (k : ℕ) :
    ∀ᵐ z ∂rootLaw k (fun _ => μ),∀ i : Fin k,P (rootArray k z i) := by
  have hp : ∀ᵐ z ∂Measure.pi (fun _ : Fin k => μ),∀ i : Fin k,P (z i) :=
    Filter.eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => μ) (i := i)).eventually hP)
  simpa only [rootArrayEquiv_apply] using (measurePreserving_rootArray μ k).quasiMeasurePreserving.ae hp

namespace PrescribedTree
variable {Ω Λ R X : Type} [Fintype Ω] [Fintype Λ] [Fintype R] [MeasurableSpace X]
    {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma measurable_cavityEnergy (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : X → RootPath (InteractionSample p) l) (hz : Measurable z)
    (f : X → FinitePath Ω n → ℝ) (hf : ∀ y,Measurable (fun a => f a y))
    (y : FinitePath (CavityState Ω Λ p l) n) :
    Measurable (fun a => cavityEnergy V x j l r i (z a) (f a) y) := by
  induction l with
  | zero => exact hf y
  | succ l ih =>
    apply (ih r.2 i.2 (fun a => (z a).2) (measurable_snd.comp hz) (KernelTower.pathFst n y)).add
    exact (measurable_mixedEnergy _ _ _).comp (measurable_fst.comp hz)

omit [Fintype R] [NeZero N] in
lemma measurable_cavityRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : X → RootPath (InteractionSample p) l) (hz : Measurable z)
    (f : X → FinitePath Ω n → ℝ) (hf : ∀ y,Measurable (fun a => f a y)) :
    Measurable (fun a => cavityRoot T U V x m j l r i (z a) (f a)) :=
  KernelTower.measurable_backwardLog n _ m (measurable_cavityEnergy V x j l r i z hz f hf)

abbrev UpperDatum (p N : ℕ) (R : Type) := InteractionSample p × (Fin p → Fin N) × (Fin p → R)

noncomputable def upperDatumLaw [MeasurableSpace R] (M : Model p) (Q : FiniteLaw R) :
    Measure (UpperDatum p N R) :=
  M.disorder.toMeasure.prod
    (((FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).asProbability id).toMeasure.prod
      ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
