import Mathlib
import OAI.Probability.LogConcave.JetEstimates.MatrixArray

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped NNReal BigOperators
open TensorEnergy

def transportMajorant (n : ℕ) : ℝ := (probabilityTransport_iterated_split n).choose
lemma transportMajorant_nonneg (n : ℕ) : 0≤transportMajorant n :=
  (probabilityTransport_iterated_split n).choose_spec.1

lemma probabilityTransport_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (s t : Icc (0:ℝ) T) :
    ContDiff ℝ (⊤:ℕ∞) (probabilityTransport hF x hr hl hT0 hT1 s t) := by
  have he : probabilityTransport hF x hr hl hT0 hT1 s t=
      fun z => spatialTransport hF x hr hl hT0 hT1 s (t,z) :=
    funext (fun z => (spatialTransport_eq hF x hr hl hT0 hT1 s t z).symm)
  rw [he]
  exact (spatialTransport_smooth hF x hr hl hT0 hT1 s).comp (contDiff_const.prodMk contDiff_id)

lemma transportMajorant_bound {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (s t : Icc (0:ℝ) T) (y : Point d) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n
      (probabilityTransport hF x hr.le hl hT0 hT1 s t) y)) (transportMajorant n/R^(n-1)) :=
  (probabilityTransport_iterated_split n).choose_spec.2 d F lam hF x r R T hr hlam hl hR hRT hT0 hT1 s t y

def jacobianMajorant (n : ℕ) : ℝ :=
  ∑c : OrderedFinpartition n,transportMajorant (c.length+1)*∏i,transportMajorant (c.partSize i)
lemma jacobianMajorant_nonneg (n : ℕ) : 0≤jacobianMajorant n :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (transportMajorant_nonneg _)
    (Finset.prod_nonneg (fun _ _ => transportMajorant_nonneg _)))

lemma terminalJacobian_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (t : Icc (0:ℝ) T) (y : Point d) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      (fun z => matrixArray d (terminalJacobian hF x hr hl hT0 hT1 (t,z))) y))
      (jacobianMajorant n/R^n) := by
  let f := probabilityTransport hF x hr.le hl hT0 hT1 ⟨T,hT0,le_rfl⟩ t
  let g := probabilityTransport hF x hr.le hl hT0 hT1 t ⟨T,hT0,le_rfl⟩
  have hf : ContDiff ℝ (⊤:ℕ∞) f := probabilityTransport_smooth hF x hr.le hl hT0 hT1 _ _
  have hg : ContDiff ℝ (⊤:ℕ∞) g := probabilityTransport_smooth hF x hr.le hl hT0 hT1 _ _
  have hh := allSplit_jacobian_comp (n:=n) hf hg transportMajorant transportMajorant
    transportMajorant_nonneg transportMajorant_nonneg R hR y
    (fun _ _ => transportMajorant_bound hF x hr hlam hl hR hRT hT0 hT1 _ _ (f y))
    (fun _ _ => transportMajorant_bound hF x hr hlam hl hR hRT hT0 hT1 _ _ y)
  have he : (fun z => matrixArray d (terminalJacobian hF x hr hl hT0 hT1 (t,z)))=
      (fun z => matrixArray d (fderiv ℝ g z)) ∘ f := by
    funext z
    rw [terminalJacobian_eq,terminalBackward_eq]
    rfl
  rw [he]
  simpa only [Nat.add_zero,jacobianMajorant] using hh
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

lemma matrixArray_firstJet {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L ρ : ℝ)
    (y : Point d) (c : Unit ⊕ Unit → Fin d) :
    matrixArray d (conditionalFirstJet F x r L (ρ,y)) c=
      conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ()))) L
        (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ()))) [()] := by
  simp only [matrixArray_apply,conditionalFirstJet,sum_apply,
    smul_apply,coordinateRankOne,ContinuousLinearMap.smulRight_apply,
    real_inner_smul_right,inner_sum,innerSL_apply_apply]
  simp only [orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal,
    mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma normalizedMatrix_eq_firstJet {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L ρ : ℝ)
    (y : Point d) (c : Unit ⊕ Unit → Fin d) :
    L*normalizedTensor F x r ρ L y (Sum.elim (fun _ => true) (fun _ => false))
      [Sum.inr (),Sum.inl ()] c=matrixArray d (conditionalFirstJet F x r L (ρ,y)) c := by
  rw [matrixArray_firstJet]
  have hi : conditionalSlotEmbedding d (Sum.elim (fun _ : Unit => true) (fun _ : Unit => false)) c
      (Sum.inr ())=Sum.inl (c (Sum.inr ())) := rfl
  have ho : conditionalSlotEmbedding d (Sum.elim (fun _ : Unit => true) (fun _ : Unit => false)) c
      (Sum.inl ())=Sum.inr (c (Sum.inl ())) := rfl
  simp only [normalizedTensor,conditionalU,Fintype.card_sum,Fintype.card_unit,
    Nat.add_sub_cancel,pow_one,List.length_singleton,JetCalculus.jet,hi,ho]
  rw [←jointPosition_basis,←jointField_basis]
  ring

lemma normalizedMatrix_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      (fun z c => normalizedTensor F x r ρ ((lam:ℝ)*r) z
        (Sum.elim (fun _ : Unit => true) (fun _ : Unit => false)) [Sum.inr (),Sum.inl ()] c) y))
      (normalizedTensorMajorant (n+2) (1-ρ^2)) := by
  let mask : Unit ⊕ Unit → Bool := Sum.elim (fun _ => true) (fun _ => false)
  let l : List (Unit ⊕ Unit) := [Sum.inr (),Sum.inl ()]
  let g : Point d → (Unit ⊕ Unit → Fin d) → ℝ :=
    fun z c => normalizedTensor F x r ρ ((lam:ℝ)*r) z mask l c
  have hg : ContDiff ℝ (⊤:ℕ∞) g := contDiff_pi.mpr (fun c =>
    normalizedTensor_smooth hF x hr hlam hl hρ0 hρ1 mask l (by simp [l]) c)
  have hN : l.Nodup := by simp [l]
  have hall : ∀s,s∈l := by rintro (u|u) <;> cases u <;> simp [l]
  have hb := normalizedTensor_spatial_allSplit hF x hr hlam hl hρ0 hρ1 y mask l
    (by simp [l]) hN hall (List.finRange n) (List.nodup_finRange _) (by simp)
  change AllSplitBound (spatialTensor (fun c z => g z c) (List.finRange n) y) _ at hb
  have hh := AllSplitBound.of_spatialTensor hg y hb
  simpa only [Fintype.card_fin,Fintype.card_sum,Fintype.card_unit] using hh

lemma conditionalFirstJet_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ R : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (hR : 0<R) (ha : R^2≤1-ρ^2) (y : Point d) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      (fun z => matrixArray d (conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,z))) y))
      (((lam:ℝ)*r)*normalizedTensorMajorant (n+2) 1/R^n) := by
  let g : Point d → (Unit ⊕ Unit → Fin d) → ℝ := fun z c =>
    normalizedTensor F x r ρ ((lam:ℝ)*r) z (Sum.elim (fun _ => true) (fun _ => false))
      [Sum.inr (),Sum.inl ()] c
  have hg : ContDiff ℝ (⊤:ℕ∞) g := contDiff_pi.mpr (fun c =>
    normalizedTensor_smooth hF x hr hlam hl hρ0 hρ1 _ _ (by simp) c)
  have hbase := normalizedMatrix_iterated_split (n:=n) hF x hr hlam hl hρ0 hρ1 y
  have hscale := (hbase.mono (normalizedTensorMajorant_nonneg _ _)
    (by simpa only [Nat.add_sub_cancel] using normalizedTensorMajorant_scale (n:=n+2) hR ha)).const_mul
    ((lam:ℝ)*r)
  have he : (fun z => matrixArray d (conditionalFirstJet F x r ((lam:ℝ)*r) (ρ,z)))=
      fun z => ((lam:ℝ)*r) • g z := by
    funext z c
    exact (normalizedMatrix_eq_firstJet F x r ((lam:ℝ)*r) ρ z c).symm
  rw [he,iteratedFDeriv_const_smul_apply' (hg.contDiffAt.of_le
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))]
  change AllSplitBound (fun a => ((lam:ℝ)*r) * arrayTensor (iteratedFDeriv ℝ n g y) a) _
  simpa only [mul_div_assoc,g] using hscale
end LogConcaveSampling

end

end

end

end OAI
