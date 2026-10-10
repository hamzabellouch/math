import OAI.NumberTheory.DirichletL.Detector.RawPhysicalIntegral

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical

lemma count_product {A B : Type*} [Countable A] [Countable B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    (Measure.count:Measure A).prod (Measure.count:Measure B)=Measure.count := by
  apply Measure.ext_of_singleton
  rintro ⟨a,b⟩
  rw [←Set.singleton_prod_singleton,Measure.prod_prod]
  simp

lemma count_equiv_preserving {A B : Type*} [Countable A] [Countable B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (e : A≃ᵐB) : MeasurePreserving e Measure.count Measure.count := by
  refine ⟨e.measurable,?_⟩
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply e.measurable (measurableSet_singleton b)]
  have he : e ⁻¹' {b}={e.symm b} := by ext a;simp [e.eq_symm_apply]
  rw [he]
  simp

def quadShuffle {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] : (A×B)×(C×D) ≃ᵐ (A×C)×(B×D) where
  toFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  invFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  left_inv p := rfl
  right_inv p := rfl
  measurable_toFun := by change Measurable (fun p : (A×B)×(C×D)=>((p.1.1,p.2.1),(p.1.2,p.2.2)));fun_prop
  measurable_invFun := by change Measurable (fun p : (A×C)×(B×D)=>((p.1.1,p.2.1),(p.1.2,p.2.2)));fun_prop

lemma quadShuffle_preserving {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μA : Measure A) (μB : Measure B)
    (μC : Measure C) (μD : Measure D) [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] :
    MeasurePreserving (quadShuffle : (A×B)×(C×D) ≃ᵐ (A×C)×(B×D))
      ((μA.prod μB).prod (μC.prod μD)) ((μA.prod μC).prod (μB.prod μD)) := by
  have h1 := measurePreserving_prodAssoc μA μB (μC.prod μD)
  have h2 := (MeasurePreserving.id μA).prod ((measurePreserving_prodAssoc μB μC μD).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id μA).prod
    ((Measure.measurePreserving_swap (μ:=μB) (ν:=μC)).prod (MeasurePreserving.id μD))
  have h4 := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μC μB μD)
  have h5 := (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm MeasurableEquiv.prodAssoc
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

def physicalNestingEquiv {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F] :
    (A×(B×C))×((D×E)×F) ≃ᵐ A×(F×(D×(B×(E×C)))) where
  toFun p := (p.1.1,(p.2.2,(p.2.1.1,(p.1.2.1,(p.2.1.2,p.1.2.2)))))
  invFun p := ((p.1,(p.2.2.2.1,p.2.2.2.2.2)),((p.2.2.1,p.2.2.2.2.1),p.2.1))
  left_inv p := rfl
  right_inv p := rfl
  measurable_toFun := by
    change Measurable (fun p : (A×(B×C))×((D×E)×F)=>
      (p.1.1,(p.2.2,(p.2.1.1,(p.1.2.1,(p.2.1.2,p.1.2.2))))))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : A×(F×(D×(B×(E×C))))=>
      ((p.1,(p.2.2.2.1,p.2.2.2.2.2)),((p.2.2.1,p.2.2.2.2.1),p.2.1)))
    fun_prop

lemma physicalNesting_preserving {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F]
    (μA : Measure A) (μB : Measure B) (μC : Measure C)
    (μD : Measure D) (μE : Measure E) (μF : Measure F)
    [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] [SFinite μE] [SFinite μF] :
    MeasurePreserving (physicalNestingEquiv : (A×(B×C))×((D×E)×F) ≃ᵐ A×(F×(D×(B×(E×C)))))
      ((μA.prod (μB.prod μC)).prod ((μD.prod μE).prod μF))
      (μA.prod (μF.prod (μD.prod (μB.prod (μE.prod μC))))) := by
  have h1 := measurePreserving_prodAssoc μA (μB.prod μC) ((μD.prod μE).prod μF)
  have hr := (Measure.measurePreserving_swap (μ:=(μB.prod μC).prod (μD.prod μE)) (ν:=μF)).comp
    ((measurePreserving_prodAssoc (μB.prod μC) (μD.prod μE) μF).symm MeasurableEquiv.prodAssoc)
  have hq := quadShuffle_preserving μB μC μD μE
  have hs := (Measure.measurePreserving_swap (μ:=μB) (ν:=μD)).prod
    (Measure.measurePreserving_swap (μ:=μC) (ν:=μE))
  have ha := measurePreserving_prodAssoc μD μB (μE.prod μC)
  exact ((MeasurePreserving.id μA).prod
    (((MeasurePreserving.id μF).prod (ha.comp (hs.comp hq))).comp hr)).comp h1

lemma integral_count_eq_tsum {A : Type*} [Countable A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (f : A→ℂ) (hf : Integrable f Measure.count) :
    (∫a,f a ∂Measure.count)=∑'a,f a := by
  simpa using integral_countable hf

theorem integral_physical_nesting {A B C : Type*} [Countable A] [Countable B] [Countable C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (F : A×(ℝ×(ℝ×(B×(ℝ×C))))→ℂ)
    (hF : Integrable F ((Measure.count:Measure A).prod (volume.prod (volume.prod
      ((Measure.count:Measure B).prod (volume.prod (Measure.count:Measure C))))))) :
    (∫p,F p ∂((Measure.count:Measure A).prod (volume.prod (volume.prod
      ((Measure.count:Measure B).prod (volume.prod (Measure.count:Measure C)))))))=
      ∑'a : A,∫w : ℝ,∫t : ℝ,∑'b : B,∫z : ℝ,∑'c : C,F (a,(w,(t,(b,(z,c))))) := by
  rw [integral_prod _ hF,integral_count_eq_tsum _ hF.integral_prod_left]
  apply tsum_congr
  intro a
  have ha := (Measure.ae_count_iff.mp hF.prod_right_ae) a
  rw [integral_prod _ ha]
  apply integral_congr_ae
  filter_upwards [ha.prod_right_ae] with w hw
  rw [integral_prod _ hw]
  apply integral_congr_ae
  filter_upwards [hw.prod_right_ae] with t ht
  rw [integral_prod _ ht,integral_count_eq_tsum _ ht.integral_prod_left]
  apply tsum_congr
  intro b
  have hb := (Measure.ae_count_iff.mp ht.prod_right_ae) b
  rw [integral_prod _ hb]
  apply integral_congr_ae
  filter_upwards [hb.prod_right_ae] with z hz
  exact integral_count_eq_tsum _ hz

end SevenEighths.ProbePhysical
end

end OAI
