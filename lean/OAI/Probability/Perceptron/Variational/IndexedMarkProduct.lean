import Mathlib
import OAI.Probability.Perceptron.Variational.CouplingKernel
import OAI.Probability.Perceptron.Cavity.IndexedFreshTilt

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

section
variable {S T : Type} [MeasurableSpace S] [MeasurableSpace T]

def indexedMarksZip : (n : ℕ) → IndexedCascadeMarks S n × IndexedCascadeMarks T n →
    IndexedCascadeMarks (S×T) n
  | 0, _ => ()
  | n+1, p => fun i j => (((p.1 i j).1,(p.2 i j).1),
      indexedMarksZip n ((p.1 i j).2,(p.2 i j).2))

lemma indexedMarksZip_measurable (n : ℕ) : Measurable (indexedMarksZip (S:=S) (T:=T) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact ((by fun_prop : Measurable (fun p : IndexedCascadeMarks S (n+1) × IndexedCascadeMarks T (n+1) =>
      ((p.1 i j).1,(p.2 i j).1)))).prodMk (ih.comp (by fun_prop))

lemma indexedMarksZip_vertices (n : ℕ) (a : IndexedVertex n→S) (b : IndexedVertex n→T) :
    indexedMarksZip n (indexedMarksFromVertices n a,indexedMarksFromVertices n b)=
      indexedMarksFromVertices n (fun v => (a v,b v)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i j
    exact congrArg (fun x => ((a (i,j,.inl ()),b (i,j,.inl ())),x))
      (ih (fun v => a (i,j,.inr v)) (fun v => b (i,j,.inr v)))

lemma indexedMarksZip_law (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T) (n : ℕ) :
    ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
      (indexedCascadeMarksLaw ρ n : Measure (IndexedCascadeMarks T n))).map (indexedMarksZip n)=
        (indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n)) := by
  let A := Measure.infinitePi (fun _ : IndexedVertex n => (ν : Measure S))
  let B := Measure.infinitePi (fun _ : IndexedVertex n => (ρ : Measure T))
  have he : (fun p : (IndexedVertex n→S)×(IndexedVertex n→T) =>
      indexedMarksZip n (indexedMarksFromVertices n p.1,indexedMarksFromVertices n p.2))=
        indexedMarksFromVertices n ∘ (fun p v => (p.1 v,p.2 v)) := by
    funext p
    exact indexedMarksZip_vertices n p.1 p.2
  rw [← indexedMarksFromVertices_law ν n,← indexedMarksFromVertices_law ρ n,
    Measure.map_prod_map _ _ (indexedMarksFromVertices_measurable n) (indexedMarksFromVertices_measurable n),
    Measure.map_map (indexedMarksZip_measurable n)
      ((indexedMarksFromVertices_measurable n).prodMap (indexedMarksFromVertices_measurable n))]
  change (A.prod B).map (fun p => indexedMarksZip n (indexedMarksFromVertices n p.1,indexedMarksFromVertices n p.2))=_
  rw [he,← Measure.map_map (indexedMarksFromVertices_measurable n) (by fun_prop)]
  dsimp [A,B]
  rw [infinitePi_zip]
  exact indexedMarksFromVertices_law (productMarkLaw ν ρ) n

lemma indexedLeafState_product {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (step₁ : X×S→X) (step₂ : Y×T→Y)
    (n : ℕ) (x : X) (y : Y) (a : IndexedCascadeMarks S n) (b : IndexedCascadeMarks T n)
    (l : IndexedLeaf n) :
    indexedLeafState (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n
      ((x,y),indexedMarksZip n (a,b)) l=
        (indexedLeafState step₁ n (x,a) l,indexedLeafState step₂ n (y,b) l) := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih => exact ih _ _ _ _ _

end

theorem indexed_independent_arrays_fresh_log {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    [Nonempty S] [Nonempty T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    {H : X→ℝ} {G : Y→ℝ} (hH : Measurable H) (hG : Measurable G)
    (hIH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hIG : finiteCascadeFractionalIntegrable ρ step₂ G n z) (x : X) (y : Y) :
    (∫ p, Real.log (tiltMean (indexedLeafProbability n p.1)
      (fun l => G (indexedLeafState step₂ n (y,p.2.2) l))
      (fun l => Real.exp (H (indexedLeafState step₁ n (x,p.2.1) l))) 1)
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
          (indexedCascadeMarksLaw ρ n))) =
      finiteCascadeLogRecursion ν step₁ n z H x := by
  let step : (X×Y)×(S×T)→X×Y := fun a => (step₁ (a.1.1,a.2.1),step₂ (a.1.2,a.2.2))
  have hs : Measurable step := by fun_prop
  let F : IndexedCascadeBase n×IndexedCascadeMarks (S×T) n→ℝ := fun p =>
    Real.log (tiltMean (indexedLeafProbability n p.1)
      (fun l => G (indexedLeafState step n ((x,y),p.2) l).2)
      (fun l => Real.exp (H (indexedLeafState step n ((x,y),p.2) l).1)) 1)
  let κ : Kernel (IndexedCascadeBase n × IndexedCascadeMarks (S×T) n) (IndexedLeaf n) := (indexedLeafKernel n).comap
    (Prod.fst : IndexedCascadeBase n×IndexedCascadeMarks (S×T) n→IndexedCascadeBase n) measurable_fst
  have hstate : Measurable (fun a : (IndexedCascadeBase n×IndexedCascadeMarks (S×T) n)×IndexedLeaf n =>
      indexedLeafState step n ((x,y),a.1.2) a.2) :=
    (indexedLeafState_measurable hs n).comp (show Measurable (fun a : (IndexedCascadeBase n×IndexedCascadeMarks (S×T) n)×IndexedLeaf n => (((x,y),a.1.2),a.2)) from (measurable_const.prodMk measurable_fst.snd).prodMk measurable_snd)
  have hF : Measurable F := (kernel_tiltMean_measurable κ
    (H := fun p l => G (indexedLeafState step n ((x,y),p.2) l).2)
    (Y := fun p l => Real.exp (H (indexedLeafState step n ((x,y),p.2) l).1))
    (hG.comp hstate.snd) (hH.comp hstate.fst |>.exp)).log
  let B := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n))
  let M := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
    (indexedCascadeMarksLaw ρ n : Measure (IndexedCascadeMarks T n))
  let M' := (indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n))
  let a : IndexedCascadeBase n × (IndexedCascadeMarks S n × IndexedCascadeMarks T n) →
      IndexedCascadeBase n × IndexedCascadeMarks (S×T) n :=
    Prod.map (id : IndexedCascadeBase n→IndexedCascadeBase n) (indexedMarksZip (S:=S) (T:=T) n)
  have ha : Measurable a := measurable_id.prodMap (indexedMarksZip_measurable n)
  have hmap : (B.prod M).map a=B.prod M' := by
    rw [← Measure.map_prod_map _ _ measurable_id (indexedMarksZip_measurable n),Measure.map_id]
    exact congrArg (Measure.prod B) (indexedMarksZip_law ν ρ n)
  have hval := indexed_independent_fresh_log ν ρ step₁ step₂ hs₁ hs₂ n z hz hz0 hz1 hH hG hIH hIG x y
  change (∫ p, F p ∂B.prod M')=_ at hval
  rw [← hmap,integral_map ha.aemeasurable hF.aestronglyMeasurable] at hval
  convert hval using 1
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    rcases p with ⟨b,m₁,m₂⟩
    dsimp only [a,Prod.map,F,step,id_eq]
    simp only [indexedLeafState_product]

end SphericalPerceptronFreeEnergy
end

end OAI
