import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.Center
import OAI.Combinatorics.RamseyFive.Decoding.CoordinateMap

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.AffineChart
open Module
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def splitEquiv (φ : V →ₗ[K] K) (o : V) (ho : φ o = 1) :
    V ≃ₗ[K] K × LinearMap.ker φ where
  toFun v := (φ v, ⟨v - φ v • o, by simp [LinearMap.mem_ker, ho]⟩)
  invFun v := v.1 • o + v.2
  left_inv v := by simp
  right_inv v := by
    rcases v with ⟨a, w⟩
    ext
    · simp [ho]
    · simp [ho]
  map_add' u v := by
    ext
    · simp
    · simp [add_smul]; abel
  map_smul' a v := by
    ext
    · simp
    · simp [smul_sub, smul_smul]

theorem exists_coordinates_of_vectors [Infinite K] [FiniteDimensional K V]
    {ι : Type*} [Finite ι] [Nonempty ι] (n : ℕ) (hdim : finrank K V = n+1)
    (v : ι → V) (hv : ∀ i, v i ≠ 0) :
    ∃ e : V ≃ₗ[K] K × (Fin n → K), ∀ i, (e (v i)).1 ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Module.exists_dual_forall_apply_ne_zero (K := K) v hv
  have hφ0 : φ ≠ 0 := by
    intro h
    exact hφ (Classical.arbitrary ι) (by simp [h])
  obtain ⟨o, ho⟩ := LinearMap.surjective hφ0 1
  have hk : finrank K (LinearMap.ker φ) = n := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hφ0
    omega
  let c : LinearMap.ker φ ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hk)
  exact ⟨(splitEquiv φ o ho).trans ((LinearEquiv.refl K K).prodCongr c), hφ⟩

theorem exists_coordinates [Infinite K] [FiniteDimensional K V]
    {ι : Type*} [Finite ι] [Nonempty ι] (n : ℕ) (hdim : finrank K V = n+1)
    (p : ι → ℙ K V) :
    ∃ e : V ≃ₗ[K] K × (Fin n → K), ∀ i, (e (p i).rep).1 ≠ 0 :=
  exists_coordinates_of_vectors n hdim (fun i => (p i).rep)
    (fun i => (p i).rep_nonzero)

variable {U : Type*} [AddCommGroup U] [Module K U]

def normalize (v : K × U) : U := v.1⁻¹ • v.2

lemma lift_normalize (v : K × U) (hv : v.1 ≠ 0) :
    (1, normalize v) = v.1⁻¹ • v := by
  ext <;> simp [normalize, hv]

lemma reconstruct (v : K × U) (hv : v.1 ≠ 0) :
    v.1 • (1, normalize v) = v := by
  rw [lift_normalize v hv, smul_smul, mul_inv_cancel₀ hv, one_smul]

lemma normalize_eq_iff (v w : K × U) (hv : v.1 ≠ 0) (hw : w.1 ≠ 0) :
    normalize v = normalize w ↔ ∃ a : K, a ≠ 0 ∧ a • w = v := by
  constructor
  · intro h
    refine ⟨v.1 * w.1⁻¹, mul_ne_zero hv (inv_ne_zero hw), ?_⟩
    rw [← smul_smul, ← lift_normalize w hw, ← h, reconstruct v hv]
  · rintro ⟨a, ha, rfl⟩
    simp [normalize, smul_smul, ha]

noncomputable def point (e : V ≃ₗ[K] K × U) (p : ℙ K V) : U :=
  normalize (e p.rep)

lemma point_injective_on (e : V ≃ₗ[K] K × U) :
    Set.InjOn (point e) {p : ℙ K V | (e p.rep).1 ≠ 0} := by
  intro p hp r hr h
  obtain ⟨a, _, ha⟩ := (normalize_eq_iff _ _ hp hr).mp h
  have he : a • r.rep = p.rep := e.injective (by simpa using ha)
  rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep r]
  exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨a, he⟩

end SharpRamseyFive.AffineChart

namespace SharpRamseyFive.ProjectiveReduction
open Module Submodule
variable {K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

theorem exists_projection_preserving_ranks [FiniteDimensional K V]
    (n : ℕ) (hdim : finrank K V = n + 1) (X : Finset V) :
    ∃ f : V →ₗ[K] (Fin n → K), Function.Surjective f ∧
      ∀ Y : Finset V, Y ⊆ X →
        finrank K (Submodule.span K (f '' (Y : Set V))) =
          min (finrank K (Submodule.span K (Y : Set V))) n := by
  obtain ⟨f, hf, hfi⟩ := exists_projection_preserving_spans n hdim X
  refine ⟨f, hf, ?_⟩
  intro Y hY
  rw [Submodule.span_image]
  by_cases he : Submodule.span K (Y : Set V) = ⊤
  · rw [he, Submodule.map_top, LinearMap.range_eq_top.mpr hf]
    simp [hdim]
  · rw [finrank_map_of_injOn f _ (hfi Y hY he)]
    have hr := Submodule.finrank_lt he
    rw [hdim] at hr
    exact (min_eq_left (by omega)).symm
end SharpRamseyFive.ProjectiveReduction

namespace SharpRamseyFive.ScalarExtension
open Module
variable {K L I : Type*} [Field K] [Field L] [Algebra K L]

lemma coordinateMap_mem_span {s : Set (I → K)} {v : I → K}
    (hv : v ∈ Submodule.span K s) :
    coordinateMap (L := L) v ∈ Submodule.span L (coordinateMap '' s) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    simpa using Submodule.smul_mem
      (Submodule.span L (coordinateMap '' s)) (algebraMap K L a) ih

theorem finrank_span_range [Finite I] {J : Type*} (v : J → I → K) :
    finrank L (Submodule.span L (Set.range (coordinateMap (L := L) ∘ v))) =
      finrank K (Submodule.span K (Set.range v)) := by
  classical
  obtain ⟨B, a, _, hspan, hi⟩ := exists_linearIndependent' K v
  let := hi.finite
  let : Fintype B := Fintype.ofFinite B
  have hiL : LinearIndependent L (coordinateMap (L := L) ∘ (v ∘ a)) :=
    linearIndependent_algebraMap_comp_iff.mpr hi
  have he : Submodule.span L (Set.range (coordinateMap (L := L) ∘ (v ∘ a))) =
      Submodule.span L (Set.range (coordinateMap (L := L) ∘ v)) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨b, rfl⟩
      exact ⟨a b, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hm : v i ∈ Submodule.span K (Set.range (v ∘ a)) := by
        rw [hspan]
        exact Submodule.subset_span ⟨i, rfl⟩
      have H := coordinateMap_mem_span (L := L) hm
      simpa [← Set.range_comp, Function.comp_assoc] using H
  rw [← he, finrank_span_eq_card hiL, ← hspan, finrank_span_eq_card hi]
end SharpRamseyFive.ScalarExtension

end OAI
