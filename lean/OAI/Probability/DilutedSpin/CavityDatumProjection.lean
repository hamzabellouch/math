import OAI.Probability.DilutedSpin.PhysicalReservoirIncrement
import OAI.Probability.DilutedSpin.RootProductLaw

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
lemma measurable_selectRoot {X : Type} [MeasurableSpace X] (l : ℕ) (b : RootPath Bool l) :
    Measurable (selectRoot (X := X) l b) := by
  induction l with
  | zero => exact measurable_id
  | succ l ih =>
    cases b with | mk a b =>
      cases a
      · exact (ih b).comp measurable_snd
      · exact measurable_fst.prodMk ((ih b).comp measurable_snd)
namespace PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperDatum_site_projection (M : Model p) (Q : FiniteLaw R) (j : Fin p) :
    MeasurePreserving (fun a : UpperDatum p N R => (a.2.1 j,(a.1,a.2.2)))
      (upperDatumLaw M Q) ((finiteUniform (Fin N)).prod
        (M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure)) := by
  unfold upperDatumLaw
  rw [FiniteLaw.pi_uniform,FiniteLaw.uniform_asProbability,←finiteUniform_pi]
  exact ((measurePreserving_eval (fun _ : Fin p => finiteUniform (Fin N)) j).prod
    (MeasurePreserving.id _)).comp
    ((measurePreserving_prodAssoc _ _ _).comp
      (((Measure.measurePreserving_swap : MeasurePreserving Prod.swap
        (M.disorder.toMeasure.prod (Measure.pi (fun _ : Fin p => finiteUniform (Fin N))))
        ((Measure.pi (fun _ : Fin p => finiteUniform (Fin N))).prod M.disorder.toMeasure)).prod
        (MeasurePreserving.id _)).comp (MeasurePreserving.symm MeasurableEquiv.prodAssoc
          (measurePreserving_prodAssoc _ _ _))))

omit [Fintype Ω] [Fintype Λ] [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma allocatedEnergy_bound (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (s : Fin N) (l : ℕ)
    (r : RootPath (Fin p → R) l) (c : RootPath (Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ)
    {B : ℝ} (hf : ∀ y,|f y|≤B) (y : FinitePath (CavityState Ω Λ p l) n) :
    |allocatedEnergy V x j s l r c z f y|≤B+∑ i,‖(rootArray l z i).1‖ := by
  induction l with
  | zero => simpa [allocatedEnergy] using hf y
  | succ l ih =>
    apply (abs_add_le _ _).trans
    have he : |if c.1=s then singleBlockEnergy V x j l r.1 z.1 y else 0|≤‖z.1.1‖ := by
      split_ifs
      · exact mixedEnergy_bound _ _ _ _
      · simp
    have h := add_le_add (ih r.2 c.2 z.2 (pathFst n y)) he
    simpa only [Fin.sum_univ_succ,rootArray,Fin.cons_zero,Fin.cons_succ,add_assoc,add_comm,add_left_comm] using h

noncomputable def allocatedDatumRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (s : Fin N) (f : FinitePath Ω n → ℝ) (l : ℕ)
    (c : RootPath (Fin N) l) (z : RootPath (InteractionSample p × (Fin p → R)) l) : ℝ :=
  backwardLog n (cavityTower T U l (rootMap Prod.snd l z)) m
    (allocatedEnergy V x j s l (rootMap Prod.snd l z) c (rootMap Prod.fst l z) f)

omit [NeZero N] in
lemma measurable_allocatedDatumRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (s : Fin N) (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Measurable (fun z : RootPath (Fin N) l × RootPath (InteractionSample p × (Fin p → R)) l =>
      allocatedDatumRoot T U V x m j s f l z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro c
  simp only [allocatedDatumRoot,allocatedRoot_selected,←rootMap_selectRoot]
  exact (measurable_activeDatumRoot T U V x m j f _).comp
    (measurable_selectRoot l (rootMap (fun a => decide (a=s)) l c))

end PrescribedTree
end DilutedSpinGlass

end

end OAI
