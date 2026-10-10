import OAI.Geometry.IsometricImmersion.Assembly.AssemblyProfiles
import OAI.Geometry.IsometricImmersion.Metrics.AffineTensorNeighborhood
import OAI.Geometry.IsometricImmersion.Assembly.DisjointTensorAssembly

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

def patchAddressCenter (a : PatchAddress) : Coord := a.2.2.2.val

def patchAddressMatrix (a : PatchAddress) : Matrix (Fin 2) (Fin 2) ℝ :=
  orientedPatchScale a.1 a.2.1 a.2.2.1 • a.2.2.1.val

theorem patchAddressMatrix_isUnit (a : PatchAddress) : IsUnit (patchAddressMatrix a) :=
  orientedPatchMatrix_isUnit a.1 a.2.1 a.2.2.1

def patchTensorIndex (a : PatchAddress) : ℕ :=
  Encodable.encode (Sum.inr a : AssemblyProfileIndex)

theorem patchTensorIndex_injective : Injective patchTensorIndex := by
  intro a b h
  exact Sum.inr.inj (Encodable.encode_injective h)

def patchTensorAddress (j : ℕ) : Option PatchAddress :=
  match Encodable.decode₂ AssemblyProfileIndex j with
  | some (.inr a) => some a
  | _ => none

theorem patchTensorAddress_index (a : PatchAddress) :
    patchTensorAddress (patchTensorIndex a) = some a := by
  simp only [patchTensorAddress,patchTensorIndex,Encodable.decode₂_encode]

theorem patchTensorAddress_eq_some_iff {j : ℕ} {a : PatchAddress} :
    patchTensorAddress j = some a ↔ patchTensorIndex a = j := by
  constructor
  · intro h
    cases hd : Encodable.decode₂ AssemblyProfileIndex j with
    | none => simp only [patchTensorAddress,hd] at h; cases h
    | some i =>
      cases i with
      | inl n => simp only [patchTensorAddress,hd] at h; cases h
      | inr b =>
        have hba : b = a := by simpa only [patchTensorAddress,hd,Option.some.injEq] using h
        subst b
        exact Encodable.decode₂_eq_some.mp hd
  · intro h
    rw [← h]
    exact patchTensorAddress_index a

def patchAddressTensor (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress) : MetricField :=
  affinePushforwardMetric (perturbationTensor (eta a)) (patchAddressCenter a) (patchAddressMatrix a)

theorem patchAddressTensor_contDiff (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress) :
    ContDiff ℝ ∞ (patchAddressTensor eta a) :=
  (affineTensorCongruence (patchAddressMatrix a)).contDiff.comp
    ((perturbationTensor_contDiff (eta a)).comp
      (affineInverseCoordinates_contDiff (patchAddressCenter a) (patchAddressMatrix a)))

theorem patchAddressTensor_tsupport_subset (eta : PatchAddress → SymmetricPerturbation)
    (a : PatchAddress) : tsupport (patchAddressTensor eta a) ⊆ patchAddressCarrier a := by
  have hs := affinePushforwardMetric_tsupport_subset (perturbationTensor (eta a))
    (patchAddressCenter a) (patchAddressMatrix a) (patchAddressMatrix_isUnit a)
    (perturbationTensor_tsupport_subset (eta a))
  intro p hp
  obtain ⟨q,hq,rfl⟩ := hs hp
  refine ⟨q,?_,rfl⟩
  intro i
  exact ⟨by linarith [hq.1 i],by linarith [hq.2 i]⟩

theorem patchAddressCarrier_isCompact (a : PatchAddress) : IsCompact (patchAddressCarrier a) :=
  orientedClosedPatch_isCompact a.1 a.2.1 a.2.2.1 a.2.2.2.val

theorem patchAddressTensor_hasCompactSupport (eta : PatchAddress → SymmetricPerturbation)
    (a : PatchAddress) : HasCompactSupport (patchAddressTensor eta a) :=
  (patchAddressCarrier_isCompact a).of_isClosed_subset (isClosed_tsupport _)
    (patchAddressTensor_tsupport_subset eta a)

def enumeratedPatchTensor (eta : PatchAddress → SymmetricPerturbation) (j : ℕ) : MetricField :=
  match patchTensorAddress j with
  | none => 0
  | some a => patchAddressTensor eta a

def enumeratedPatchCarrier (j : ℕ) : Set Coord :=
  match patchTensorAddress j with
  | none => ∅
  | some a => patchAddressCarrier a

theorem enumeratedPatchTensor_index (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress) :
    enumeratedPatchTensor eta (patchTensorIndex a) = patchAddressTensor eta a := by
  simp only [enumeratedPatchTensor,patchTensorAddress_index]

theorem enumeratedPatchCarrier_index (a : PatchAddress) :
    enumeratedPatchCarrier (patchTensorIndex a) = patchAddressCarrier a := by
  simp only [enumeratedPatchCarrier,patchTensorAddress_index]

theorem enumeratedPatchTensor_contDiff (eta : PatchAddress → SymmetricPerturbation) (j : ℕ) :
    ContDiff ℝ ∞ (enumeratedPatchTensor eta j) := by
  cases h : patchTensorAddress j with
  | none =>
      simp only [enumeratedPatchTensor,h]
      change ContDiff ℝ ∞ (fun _ : Coord => (0 : Matrix (Fin 2) (Fin 2) ℝ))
      exact contDiff_const
  | some a => simpa only [enumeratedPatchTensor,h] using patchAddressTensor_contDiff eta a

theorem enumeratedPatchCarrier_isCompact (j : ℕ) : IsCompact (enumeratedPatchCarrier j) := by
  cases h : patchTensorAddress j with
  | none => simpa only [enumeratedPatchCarrier,h] using (isCompact_empty : IsCompact (∅ : Set Coord))
  | some a => simpa only [enumeratedPatchCarrier,h] using patchAddressCarrier_isCompact a

theorem enumeratedPatchTensor_tsupport_subset (eta : PatchAddress → SymmetricPerturbation) (j : ℕ) :
    tsupport (enumeratedPatchTensor eta j) ⊆ enumeratedPatchCarrier j := by
  cases h : patchTensorAddress j with
  | none => simp [enumeratedPatchTensor,enumeratedPatchCarrier,h]
  | some a => simpa only [enumeratedPatchTensor,enumeratedPatchCarrier,h] using
      patchAddressTensor_tsupport_subset eta a

theorem enumeratedPatchTensor_hasCompactSupport (eta : PatchAddress → SymmetricPerturbation) (j : ℕ) :
    HasCompactSupport (enumeratedPatchTensor eta j) :=
  (enumeratedPatchCarrier_isCompact j).of_isClosed_subset (isClosed_tsupport _)
    (enumeratedPatchTensor_tsupport_subset eta j)

theorem enumeratedPatchCarriers_pairwise_disjoint :
    Pairwise (fun i j => Disjoint (enumeratedPatchCarrier i) (enumeratedPatchCarrier j)) := by
  intro i j hij
  cases hi : patchTensorAddress i with
  | none => simp [enumeratedPatchCarrier,hi]
  | some a =>
    cases hj : patchTensorAddress j with
    | none => simp [enumeratedPatchCarrier,hj]
    | some b =>
      have hab : a ≠ b := by
        intro h
        subst b
        exact hij ((patchTensorAddress_eq_some_iff.mp hi).symm.trans
          (patchTensorAddress_eq_some_iff.mp hj))
      simpa only [enumeratedPatchCarrier,hi,hj] using patchAddressCarriers_pairwise_disjoint hab

theorem zero_not_mem_enumeratedPatchCarrier (j : ℕ) :
    (0 : Coord) ∉ enumeratedPatchCarrier j := by
  cases h : patchTensorAddress j with
  | none => simp [enumeratedPatchCarrier,h]
  | some a =>
      simpa only [enumeratedPatchCarrier,h,assemblyCarrier] using
        zero_not_mem_assemblyCarrier (Sum.inr a)

theorem enumeratedPatchCarrier_disjoint_disk (j n : ℕ) :
    Disjoint (enumeratedPatchCarrier j) (accumulatingDisk n) := by
  cases h : patchTensorAddress j with
  | none => simp [enumeratedPatchCarrier,h]
  | some a =>
    simpa only [enumeratedPatchCarrier,h,patchAddressCarrier] using
      orientedClosedPatch_disjoint_every_disk a.1 a.2.1 a.2.2.1 a.2.2.2.property n

def patchTensorBudgetNeighborhood (epsilon : ℝ) (a : PatchAddress) : Set SymmetricPerturbation :=
  affineTensorJetNeighborhood (patchAddressMatrix a) (patchTensorIndex a)
    (patchSeriesWeight epsilon (patchTensorIndex a))

theorem patchTensorBudgetNeighborhood_isOpen (epsilon : ℝ) (a : PatchAddress) :
    IsOpen (patchTensorBudgetNeighborhood epsilon a) :=
  affineTensorJetNeighborhood_isOpen _ _ _

theorem zero_mem_patchTensorBudgetNeighborhood {epsilon : ℝ} (he : 0 < epsilon) (a : PatchAddress) :
    (0 : SymmetricPerturbation) ∈ patchTensorBudgetNeighborhood epsilon a :=
  zero_mem_affineTensorJetNeighborhood _ _ (patchSeriesWeight_pos he _)

theorem enumeratedPatchTensor_diagonal_bound {epsilon : ℝ} (he : 0 < epsilon)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (j k : ℕ) (hkj : k ≤ j) (p : Coord) :
    ‖iteratedFDeriv ℝ k (enumeratedPatchTensor eta j) p‖ ≤ patchSeriesWeight epsilon j := by
  cases h : patchTensorAddress j with
  | none =>
    simpa only [enumeratedPatchTensor,h,iteratedFDeriv_zero,Pi.zero_apply,norm_zero] using
      (patchSeriesWeight_pos he j).le
  | some a =>
    have ha := patchTensorAddress_eq_some_iff.mp h
    have hb := affineTensorJetNeighborhood_physical_bounds
      (patchAddressCenter a) (patchAddressMatrix a) (patchTensorIndex a) (hsmall a)
        (show k ≤ patchTensorIndex a by omega) p
    simpa only [enumeratedPatchTensor,h,patchAddressTensor,ha] using hb.le

end SmoothLocal.Geometry

end

end OAI
