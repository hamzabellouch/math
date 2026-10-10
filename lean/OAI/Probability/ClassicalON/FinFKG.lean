import OAI.Probability.ClassicalON.PlanarPositive

namespace OAI

universe uA uX uY uι

noncomputable section
open MeasureTheory
namespace ClassicalON

section Equivalence
variable {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace X] [TopologicalSpace Y] [Lattice X] [Lattice Y]
  {μ : Measure X} {ν : Measure Y}

omit [TopologicalSpace X] [TopologicalSpace Y] [Lattice X] [Lattice Y] in
theorem weightedMean_equiv (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (w f : Y → ℝ) :
    weightedMean μ (w ∘ e) (f ∘ e) = weightedMean ν w f := by
  unfold weightedMean
  change (∫ x,(fun y => w y*f y) (e x) ∂μ)/(∫ x,w (e x) ∂μ) = _
  rw [he.integral_comp' (fun y => w y*f y),he.integral_comp' w]

theorem continuousFKG_equiv (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (hc : Continuous e) (hm : Monotone e)
    (hi : ∀ x y,e (x⊓y)=e x⊓e y) (hs : ∀ x y,e (x⊔y)=e x⊔e y)
    (hX : ContinuousFKG μ) : ContinuousFKG ν := by
  intro w hw hp hLS f g hf hg hfn hgn hfm hgm
  have hL : LogSupermodular (w ∘ e) := by
    intro x y
    simpa [Function.comp_def,hi,hs] using hLS (e x) (e y)
  have h := hX (w ∘ e) (hw.comp hc) (fun x => hp (e x)) hL
    (f ∘ e) (g ∘ e) (hf.comp hc) (hg.comp hc) (fun x => hfn (e x))
    (fun x => hgn (e x)) (hfm.comp hm) (hgm.comp hm)
  change weightedMean μ (w ∘ e) (f ∘ e)*weightedMean μ (w ∘ e) (g ∘ e) ≤
    weightedMean μ (w ∘ e) ((fun y => f y*g y) ∘ e) at h
  simpa only [weightedMean_equiv e he] using h

end Equivalence

theorem continuousFKG_subsingleton {X : Type uX} [Subsingleton X] [Nonempty X]
    [MeasurableSpace X] [TopologicalSpace X] [Lattice X]
    (μ : Measure X) [IsProbabilityMeasure μ] : ContinuousFKG μ := by
  intro w _ hp _ f g _ _ _ _ _ _
  let x : X := Classical.choice inferInstance
  have hw : w=fun _ => w x := funext fun y => congrArg w (Subsingleton.elim y x)
  have hf : f=fun _ => f x := funext fun y => congrArg f (Subsingleton.elim y x)
  have hg : g=fun _ => g x := funext fun y => congrArg g (Subsingleton.elim y x)
  rw [hw,hf,hg]
  simp only [weightedMean,integral_const,probReal_univ,one_smul]
  field_simp [(hp x).ne']
  exact le_rfl

section Finite
variable {A : Type uA} [LinearOrder A] [TopologicalSpace A] [CompactSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [LocallyCompactSpace A] (μ : Measure A) [IsProbabilityMeasure μ]

theorem continuousFKG_fin (k : ℕ) : ContinuousFKG (Measure.pi (fun _ : Fin k => μ)) := by
  induction k with
  | zero => exact continuousFKG_subsingleton _
  | succ k ih =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => A) 0).symm
    have he : MeasurePreserving e (μ.prod (Measure.pi (fun _ : Fin k => μ)))
        (Measure.pi (fun _ : Fin (k+1) => μ)) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) 0).symm
    have ha (p : A×(Fin k → A)) : e p = Fin.cons p.1 p.2 := by
      simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero']
    apply continuousFKG_equiv e he
    · apply continuous_pi
      intro i
      cases i using Fin.cases with
      | zero => simpa [ha] using (continuous_fst : Continuous (fun p : A×(Fin k → A) => p.1))
      | succ j => simpa [ha,Function.comp_def] using (continuous_apply j).comp (continuous_snd : Continuous (fun p : A×(Fin k → A) => p.2))
    · intro p q hpq i
      cases i using Fin.cases with
      | zero => simpa [ha] using hpq.1
      | succ j => simpa [ha] using hpq.2 j
    · intro p q
      ext i
      cases i using Fin.cases <;> simp [ha]
    · intro p q
      ext i
      cases i using Fin.cases <;> simp [ha]
    · exact continuousFKG_prod ih

theorem continuousFKG_pi {ι : Type uι} [Fintype ι] :
    ContinuousFKG (Measure.pi (fun _ : ι => μ)) := by
  let f := (Fintype.equivFin ι).symm
  let e := MeasurableEquiv.piCongrLeft (fun _ : ι => A) f
  have ha (u : Fin (Fintype.card ι) → A) (i : ι) : e u i=u (f.symm i) := by
    simpa only [e,f.apply_symm_apply] using
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => A) f u (f.symm i)
  apply continuousFKG_equiv e (measurePreserving_piCongrLeft (fun _ : ι => μ) f)
  · apply continuous_pi
    intro i
    simpa only [ha] using (continuous_apply (f.symm i) : Continuous (fun u : Fin (Fintype.card ι) → A => u (f.symm i)))
  · intro u v huv i
    simpa only [ha] using huv (f.symm i)
  · intro u v; ext i; simp only [ha,Pi.inf_apply]
  · intro u v; ext i; simp only [ha,Pi.sup_apply]
  · exact continuousFKG_fin μ _

end Finite
end ClassicalON

end

end OAI
