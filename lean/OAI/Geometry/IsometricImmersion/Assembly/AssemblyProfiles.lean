import OAI.Geometry.IsometricImmersion.Curvature.DiskCurvatureProfiles
import OAI.Geometry.IsometricImmersion.Curvature.PatchCurvatureProfiles
import Mathlib.Basic.Countable.Basic
import Mathlib.Logic.Encodable.Basic

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.Geometry

abbrev PatchAddress := Σ n : ℕ, Σ k : ℕ, Σ R : OrientationLabel,
  {c : Coord // c ∈ orientedExteriorCenters n k R}

instance : Countable PatchAddress := by
  classical
  let : ∀ (n k : ℕ) (R : OrientationLabel),
      Finite {c : Coord // c ∈ orientedExteriorCenters n k R} :=
    fun n k R => (orientedExteriorCenters n k R).finite_toSet.to_subtype
  infer_instance

abbrev AssemblyProfileIndex := ℕ ⊕ PatchAddress

instance assemblyProfileEncodable : Encodable AssemblyProfileIndex :=
  Encodable.ofCountable AssemblyProfileIndex

def patchAddressCarrier (a : PatchAddress) : Set Coord :=
  orientedClosedPatch a.1 a.2.1 a.2.2.1 a.2.2.2.val

def patchAddressProfile (a : PatchAddress) : Coord → ℝ :=
  orientedPatchProfile a.1 a.2.1 a.2.2.1 a.2.2.2.val

theorem patchAddressCarriers_pairwise_disjoint :
    Pairwise (fun a b => Disjoint (patchAddressCarrier a) (patchAddressCarrier b)) := by
  intro a b hab
  rcases a with ⟨n, k, R, c, hc⟩
  rcases b with ⟨m, l, S, d, hd⟩
  by_cases hnm : n = m
  · subst m
    by_cases hkl : k = l
    · subst l
      by_cases hRS : R = S
      · subst S
        apply orientedClosedPatches_disjoint_same_layer n k R hc hd
        intro hcd
        subst d
        exact hab rfl
      · apply orientedClosedPatches_disjoint_different_layers n
          (a := (k, R)) (b := (k, S)) _ hc hd
        exact fun h => hRS (congrArg Prod.snd h)
    · apply orientedClosedPatches_disjoint_different_layers n
        (a := (k, R)) (b := (l, S)) _ hc hd
      exact fun h => hkl (congrArg Prod.fst h)
  · exact orientedClosedPatches_disjoint_different_disks hnm k l R S hc hd

def assemblyCarrier : AssemblyProfileIndex → Set Coord
  | .inl n => accumulatingDisk n
  | .inr a => patchAddressCarrier a

def assemblyProfile : AssemblyProfileIndex → Coord → ℝ
  | .inl n => accumulatingDiskProfile n
  | .inr a => patchAddressProfile a

theorem assemblyProfile_contDiff (i : AssemblyProfileIndex) : ContDiff ℝ ∞ (assemblyProfile i) := by
  cases i with
  | inl n => exact accumulatingDiskProfile_contDiff n
  | inr a => exact orientedPatchProfile_contDiff _ _ _ _

theorem assemblyProfile_hasCompactSupport (i : AssemblyProfileIndex) :
    HasCompactSupport (assemblyProfile i) := by
  cases i with
  | inl n => exact accumulatingDiskProfile_hasCompactSupport n
  | inr a => exact orientedPatchProfile_hasCompactSupport _ _ _ _

theorem assemblyProfile_tsupport_subset (i : AssemblyProfileIndex) :
    tsupport (assemblyProfile i) ⊆ assemblyCarrier i := by
  cases i with
  | inl n => exact accumulatingDiskProfile_tsupport_subset n
  | inr a => exact orientedPatchProfile_tsupport_subset_patch _ _ _ _

theorem assemblyCarriers_pairwise_disjoint :
    Pairwise (fun i j => Disjoint (assemblyCarrier i) (assemblyCarrier j)) := by
  intro i j hij
  cases i with
  | inl n =>
    cases j with
    | inl m => exact accumulatingDisks_pairwise_disjoint (fun h => hij (congrArg Sum.inl h))
    | inr a =>
      exact (orientedClosedPatch_disjoint_every_disk a.1 a.2.1 a.2.2.1 a.2.2.2.property n).symm
  | inr a =>
    cases j with
    | inl n => exact orientedClosedPatch_disjoint_every_disk a.1 a.2.1 a.2.2.1 a.2.2.2.property n
    | inr b => exact patchAddressCarriers_pairwise_disjoint (fun h => hij (congrArg Sum.inr h))

theorem zero_not_mem_assemblyCarrier (i : AssemblyProfileIndex) :
    (0 : Coord) ∉ assemblyCarrier i := by
  cases i with
  | inl n => exact zero_not_mem_accumulatingDisk n
  | inr a =>
    intro h
    exact zero_not_mem_enlargedAccumulatingDisk a.1
      (orientedClosedPatch_subset_enlarged a.1 a.2.1 a.2.2.1 a.2.2.2.property h)

def enumeratedAssemblyProfile (j : ℕ) : Coord → ℝ :=
  match Encodable.decode₂ AssemblyProfileIndex j with
  | none => 0
  | some i => assemblyProfile i

theorem enumeratedAssemblyProfile_encode (i : AssemblyProfileIndex) :
    enumeratedAssemblyProfile (Encodable.encode i) = assemblyProfile i := by
  simp only [enumeratedAssemblyProfile, Encodable.decode₂_encode]

theorem enumeratedAssemblyProfile_contDiff (j : ℕ) :
    ContDiff ℝ ∞ (enumeratedAssemblyProfile j) := by
  cases h : Encodable.decode₂ AssemblyProfileIndex j with
  | none =>
      simp only [enumeratedAssemblyProfile, h]
      change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ))
      exact contDiff_const
  | some i => simpa only [enumeratedAssemblyProfile, h] using assemblyProfile_contDiff i

theorem enumeratedAssemblyProfile_hasCompactSupport (j : ℕ) :
    HasCompactSupport (enumeratedAssemblyProfile j) := by
  cases h : Encodable.decode₂ AssemblyProfileIndex j with
  | none => simpa only [enumeratedAssemblyProfile, h] using
      (HasCompactSupport.zero : HasCompactSupport (0 : Coord → ℝ))
  | some i => simpa only [enumeratedAssemblyProfile, h] using assemblyProfile_hasCompactSupport i

theorem zero_not_mem_enumeratedAssemblyProfile_tsupport (j : ℕ) :
    (0 : Coord) ∉ tsupport (enumeratedAssemblyProfile j) := by
  cases h : Encodable.decode₂ AssemblyProfileIndex j with
  | none => simp [enumeratedAssemblyProfile, h]
  | some i =>
      simpa only [enumeratedAssemblyProfile, h] using
        (fun hp => zero_not_mem_assemblyCarrier i (assemblyProfile_tsupport_subset i hp))

theorem enumeratedAssemblyProfile_zero_other (i : AssemblyProfileIndex) {p : Coord}
    (hp : p ∈ assemblyCarrier i) {j : ℕ} (hj : j ≠ Encodable.encode i) :
    enumeratedAssemblyProfile j p = 0 := by
  cases hd : Encodable.decode₂ AssemblyProfileIndex j with
  | none => simp [enumeratedAssemblyProfile, hd]
  | some a =>
      have ha : a ≠ i := by
        intro hai
        subst a
        exact hj (Encodable.decode₂_eq_some.mp hd).symm
      have hnot : p ∉ tsupport (assemblyProfile a) := fun hpa =>
        Set.disjoint_left.mp (assemblyCarriers_pairwise_disjoint ha)
          (assemblyProfile_tsupport_subset a hpa) hp
      have hz : assemblyProfile a p = 0 := by
        by_contra hne
        exact hnot (subset_tsupport (assemblyProfile a) hne)
      simpa only [enumeratedAssemblyProfile, hd] using hz

end SmoothLocal.Geometry

end

end OAI
