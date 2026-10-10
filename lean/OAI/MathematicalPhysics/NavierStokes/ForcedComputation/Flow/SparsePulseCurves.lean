import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarSparseStages
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SuspensionConcatenation

namespace OAI

/-! Inserting the stationary cells between a branch's selected pulse curves.
This supplies the complete family of curves needed by `suspension_chain`. -/

noncomputable section
namespace ForcedComputation.PlanarRouting
open ShearFlows Set

def sparseCurve {m n : ℕ} (J : Fin m → Fin n) (p : Fin (m + 1) → Plane)
    (γ : Fin m → ℝ → Plane) (i : ℕ) : ℝ → Plane :=
  if h : ∃ k, (J k).val = i then γ h.choose else fun _ => sparseAnchor J p i

theorem sparseCurve_selected {m n : ℕ} {J : Fin m → Fin n} (hJ : StrictMono J)
    (p : Fin (m + 1) → Plane) (γ : Fin m → ℝ → Plane) (k : Fin m) :
    sparseCurve J p γ (J k).val = γ k := by
  have h : ∃ l, (J l).val = (J k).val := ⟨k, rfl⟩
  have hk : h.choose = k := hJ.injective (Fin.ext h.choose_spec)
  simp only [sparseCurve, dite_eq_left h, hk]

theorem sparseCurve_unused {m n : ℕ} (J : Fin m → Fin n)
    (p : Fin (m + 1) → Plane) (γ : Fin m → ℝ → Plane) (i : ℕ)
    (hi : ∀ k, (J k).val ≠ i) : sparseCurve J p γ i = fun _ => sparseAnchor J p i := by
  have hn : ¬ ∃ k, (J k).val = i := by simpa only [not_exists] using hi
  simp only [sparseCurve, dite_eq_right hn]

theorem sparseCurve_endpoints {m n : ℕ} {J : Fin m → Fin n} (hJ : StrictMono J)
    (p : Fin (m + 1) → Plane) (γ : Fin m → ℝ → Plane) (cuts : ℕ → ℝ)
    (hstart : ∀ k, γ k (cuts (J k).val) = p k.castSucc)
    (hfinish : ∀ k, γ k (cuts ((J k).val + 1)) = p k.succ) (i : ℕ) :
    sparseCurve J p γ i (cuts i) = sparseAnchor J p i ∧
      sparseCurve J p γ i (cuts (i + 1)) = sparseAnchor J p (i + 1) := by
  by_cases hi : ∃ k, (J k).val = i
  · obtain ⟨k, rfl⟩ := hi
    rw [sparseCurve_selected hJ, sparseAnchor_selected hJ, sparseAnchor_selected_succ hJ]
    exact ⟨hstart k, hfinish k⟩
  · have hn : ∀ k, (J k).val ≠ i := by simpa only [not_exists] using hi
    rw [sparseCurve_unused J p γ i hn, sparseAnchor_unused J p i hn]
    exact ⟨rfl, rfl⟩

theorem sparseCurve_continuousOn {m n : ℕ} {J : Fin m → Fin n} (hJ : StrictMono J)
    (p : Fin (m + 1) → Plane) (γ : Fin m → ℝ → Plane) (cuts : ℕ → ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (cuts (J k).val) (cuts ((J k).val + 1))))
    (i : ℕ) : ContinuousOn (sparseCurve J p γ i) (Icc (cuts i) (cuts (i + 1))) := by
  by_cases hi : ∃ k, (J k).val = i
  · obtain ⟨k, rfl⟩ := hi
    rw [sparseCurve_selected hJ]
    exact hγ k
  · have hn : ∀ k, (J k).val ≠ i := by simpa only [not_exists] using hi
    rw [sparseCurve_unused J p γ i hn]
    exact continuousOn_const

theorem sparseCurve_ode {m n : ℕ} {J : Fin m → Fin n} (hJ : StrictMono J)
    (p : Fin (m + 1) → Plane) (γ : Fin m → ℝ → Plane) (cuts : ℕ → ℝ)
    (V : ℝ → Plane → Plane)
    (hγ : ∀ k s, s ∈ Ico (cuts (J k).val) (cuts ((J k).val + 1)) →
      HasDerivAt (γ k) (V s (γ k s)) s)
    (i : ℕ) (s : ℝ) (hs : s ∈ Ico (cuts i) (cuts (i + 1)))
    (hz : (∀ k, (J k).val ≠ i) → V s (sparseAnchor J p i) = 0) :
    HasDerivAt (sparseCurve J p γ i) (V s (sparseCurve J p γ i s)) s := by
  by_cases hi : ∃ k, (J k).val = i
  · obtain ⟨k, rfl⟩ := hi
    rw [sparseCurve_selected hJ]
    exact hγ k s hs
  · have hn : ∀ k, (J k).val ≠ i := by simpa only [not_exists] using hi
    rw [sparseCurve_unused J p γ i hn]
    change HasDerivAt (fun _ => sparseAnchor J p i) (V s (sparseAnchor J p i)) s
    rw [hz hn]
    exact hasDerivAt_const s _

theorem sparseCurve_mem {m n : ℕ} {J : Fin m → Fin n} (hJ : StrictMono J)
    (p : Fin (m + 1) → Plane) (γ : Fin m → ℝ → Plane) (cuts : ℕ → ℝ)
    {S : Set Plane} (hp : ∀ k, p k ∈ S)
    (hγ : ∀ k s, s ∈ Icc (cuts (J k).val) (cuts ((J k).val + 1)) → γ k s ∈ S)
    (i : ℕ) (s : ℝ) (hs : s ∈ Icc (cuts i) (cuts (i + 1))) :
    sparseCurve J p γ i s ∈ S := by
  by_cases hi : ∃ k, (J k).val = i
  · obtain ⟨k, rfl⟩ := hi
    rw [sparseCurve_selected hJ]
    exact hγ k s hs
  · have hn : ∀ k, (J k).val ≠ i := by simpa only [not_exists] using hi
    rw [sparseCurve_unused J p γ i hn]
    exact hp _

end ForcedComputation.PlanarRouting

end

end OAI
