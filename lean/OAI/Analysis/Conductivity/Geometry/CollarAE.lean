import Mathlib
import OAI.Analysis.Conductivity.Variational.NormalStretch
import OAI.Analysis.Conductivity.Geometry.CollarLocalInverse
import OAI.Analysis.Conductivity.Geometry.PhysicalCollarBand

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceCollarOpenBox_eq_interior : sourceCollarOpenBox=
    interior (sourceExtendedBox (-(1:ℝ)/100) (1/100)) := by
  have hbox : sourceExtendedBox (-(1:ℝ)/100) (1/100)=
      (univ : Set (Fin 3)).pi (fun k => Icc (![(-(1:ℝ)/100),-1,-1] k) (![1/100,1,1] k)) := by
    ext x
    simp only [sourceExtendedBox,mem_Icc,Set.mem_pi,mem_univ,true_implies,Pi.le_def]
    simp only [forall_and]
  rw [hbox,interior_pi_set (finite_univ),show (fun k : Fin 3 => interior
    (Icc (![(-(1:ℝ)/100),-1,-1] k) (![1/100,1,1] k)))=
      (fun k => Ioo (![(-(1:ℝ)/100),-1,-1] k) (![1/100,1,1] k)) from funext (fun _ => interior_Icc)]
  ext x
  simp only [sourceCollarOpenBox,mem_ofPred_eq,Set.mem_pi,mem_univ,true_implies,Fin.forall_fin_succ,
    mem_Ioo,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.forall_fin_zero,
    abs_lt]
  simp

lemma sourceCollar_frontier_null (i j : Fin 4) :
    volume (sourceCollarPiece i j '' frontier (sourceExtendedBox (-(1:ℝ)/100) (1/100)))=0 := by
  let B := sourceExtendedBox (-(1:ℝ)/100) (1/100)
  have hB : IsClosed B := isClosed_Icc
  have hs : frontier B⊆B := hB.frontier_subset
  have hzero : volume (frontier B)=0 := (convex_Icc _ _).addHaar_frontier volume
  have H := measure_image_le_det volume isClosed_frontier.measurableSet
    (fun x hx => (sourceCollarPiece_contDiff i j).differentiable (by simp) x)
    ((sourceExtendedBox_injOn i j (by rfl) (by rfl)).mono hs)
    (C:=2) (fun x hx => by
      rw [(sourceCollarPiece_hasFDeriv i j x).fderiv]
      exact sourceExtended_jacobian_upper i j (by rfl) (by rfl) (hs hx))
  have H' : volume (sourceCollarPiece i j '' frontier B) ≤ 0 := by
    simpa only [hzero,mul_zero] using H
  exact le_antisymm H' bot_le

lemma sourceCollar_open_charts_ae : ∀ᵐ y : Fin 3 → ℝ,
    y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) →
      ∃ i j : Fin 4,∃ x∈sourceCollarOpenBox,sourceCollarPiece i j x=y := by
  let N := ⋃ i : Fin 4,⋃ j : Fin 4,sourceCollarPiece i j ''
    frontier (sourceExtendedBox (-(1:ℝ)/100) (1/100))
  have hN : volume N=0 := measure_iUnion_null (fun i =>
    measure_iUnion_null (fun j => sourceCollar_frontier_null i j))
  have hn : ∀ᵐ y : Fin 3 → ℝ,y∉N := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hN
  filter_upwards [hn] with y hy ht
  rw [sourceClosedCollarBand_eq _ _ (by rfl) (by rfl)] at ht
  obtain ⟨i,hi⟩ := mem_iUnion.mp ht
  obtain ⟨j,x,hx,he⟩ := mem_iUnion.mp hi
  refine ⟨i,j,x,?_,he⟩
  rw [sourceCollarOpenBox_eq_interior]
  by_contra hn
  apply hy
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,⟨x,
    ⟨subset_closure hx,hn⟩,he⟩⟩⟩

end ScalarConductivity

end

end OAI
