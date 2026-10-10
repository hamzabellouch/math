import Mathlib

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem positive_ray_mem_connectedComponentIn {C : Set E}
    (hC : ∀ r : ℝ, 0 < r → ∀ v ∈ C, r • v ∈ C)
    {v : E} (hv : v ∈ C) {r : ℝ} (hr : 0 < r) :
    r • v ∈ connectedComponentIn C v := by
  have hcont : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
  have hpre : IsPreconnected ((fun t : ℝ => t • v) '' Ioi 0) :=
    isPreconnected_Ioi.image _ hcont.continuousOn
  have hmem : v ∈ (fun t : ℝ => t • v) '' Ioi 0 := ⟨1,by norm_num,one_smul ℝ v⟩
  have hsub : (fun t : ℝ => t • v) '' Ioi 0 ⊆ C := by
    rintro _ ⟨t,ht,rfl⟩
    exact hC t ht v hv
  exact hpre.subset_connectedComponentIn hmem hsub ⟨r,hr,rfl⟩

theorem cone_connectedComponentIn_smul_iff {C : Set E}
    (hC : ∀ r : ℝ, 0 < r → ∀ v ∈ C, r • v ∈ C)
    (a : E) {r : ℝ} (hr : 0 < r) (v : E) :
    r • v ∈ connectedComponentIn C a ↔ v ∈ connectedComponentIn C a := by
  have hpres : ∀ {s : ℝ}, 0 < s → ∀ {y : E}, y ∈ connectedComponentIn C a →
      s • y ∈ connectedComponentIn C a := by
    intro s hs y hy
    rw [connectedComponentIn_eq hy]
    exact positive_ray_mem_connectedComponentIn hC (connectedComponentIn_subset C a hy) hs
  constructor
  · intro hv
    have hi := hpres (inv_pos.mpr hr) hv
    simpa only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul] using hi
  · exact hpres hr

theorem open_cone_component {C : Set E} (ho : IsOpen C)
    (hC : ∀ r : ℝ, 0 < r → ∀ v ∈ C, r • v ∈ C) {a : E} (ha : a ∈ C) :
    IsOpen (connectedComponentIn C a) ∧ IsConnected (connectedComponentIn C a) ∧
      ∀ r : ℝ, 0 < r → ∀ v,
        r • v ∈ connectedComponentIn C a ↔ v ∈ connectedComponentIn C a := by
  exact ⟨ho.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr ha,
    fun _ hr v => cone_connectedComponentIn_smul_iff hC a hr v⟩

end

open Complex

def complexifyRealLinear {k j : ℕ}
    (L : (Fin k → ℝ) →ₗ[ℝ] (Fin j → ℝ)) :
    (Fin k → ℂ) →ₗ[ℂ] (Fin j → ℂ) where
  toFun z := fun i => (L (fun t => (z t).re) i : ℂ)+I*(L (fun t => (z t).im) i : ℂ)
  map_add' z w := by
    funext i
    change (L (fun t => ((z+w) t).re) i : ℂ)+I*(L (fun t => ((z+w) t).im) i : ℂ) = _
    have hr : (fun t => ((z+w) t).re) = (fun t => (z t).re)+(fun t => (w t).re) := rfl
    have hi : (fun t => ((z+w) t).im) = (fun t => (z t).im)+(fun t => (w t).im) := rfl
    rw [hr,hi,map_add,map_add]
    simp only [Pi.add_apply,ofReal_add]
    ring
  map_smul' c z := by
    funext i
    change (L (fun t => ((c • z) t).re) i : ℂ)+I*(L (fun t => ((c • z) t).im) i : ℂ) = _
    have hr : (fun t => ((c • z) t).re) =
        c.re • (fun t => (z t).re)-c.im • (fun t => (z t).im) := rfl
    have hi : (fun t => ((c • z) t).im) =
        c.re • (fun t => (z t).im)+c.im • (fun t => (z t).re) := rfl
    rw [hr,hi,map_sub,map_add,map_smul,map_smul,map_smul,map_smul]
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    apply Complex.ext <;> simp [mul_re,mul_im]

@[simp] lemma complexifyRealLinear_re {k j : ℕ}
    (L : (Fin k → ℝ) →ₗ[ℝ] (Fin j → ℝ)) (z : Fin k → ℂ) (i : Fin j) :
    (complexifyRealLinear L z i).re = L (fun t => (z t).re) i := by
  simp [complexifyRealLinear]

@[simp] lemma complexifyRealLinear_im {k j : ℕ}
    (L : (Fin k → ℝ) →ₗ[ℝ] (Fin j → ℝ)) (z : Fin k → ℂ) (i : Fin j) :
    (complexifyRealLinear L z i).im = L (fun t => (z t).im) i := by
  simp [complexifyRealLinear]

def complexifyRealEquiv {k j : ℕ} (e : (Fin k → ℝ) ≃ₗ[ℝ] (Fin j → ℝ)) :
    (Fin k → ℂ) ≃ₗ[ℂ] (Fin j → ℂ) where
  toLinearMap := complexifyRealLinear e.toLinearMap
  invFun := complexifyRealLinear e.symm.toLinearMap
  left_inv z := by
    funext i
    apply Complex.ext <;> simp
  right_inv z := by
    funext i
    apply Complex.ext <;> simp

def complexifyRealContinuousEquiv {k j : ℕ}
    (e : (Fin k → ℝ) ≃L[ℝ] (Fin j → ℝ)) :
    (Fin k → ℂ) ≃L[ℂ] (Fin j → ℂ) :=
  (complexifyRealEquiv e.toLinearEquiv).toContinuousLinearEquiv

@[simp] lemma complexifyRealContinuousEquiv_im {k j : ℕ}
    (e : (Fin k → ℝ) ≃L[ℝ] (Fin j → ℝ)) (z : Fin k → ℂ) (i : Fin j) :
    (complexifyRealContinuousEquiv e z i).im = e (fun t => (z t).im) i := by
  exact complexifyRealLinear_im e.toLinearEquiv.toLinearMap z i

end Release061

end

end OAI
