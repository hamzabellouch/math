import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.CoordinateGeometry
import OAI.Geometry.WeakMTW.Variations.FlowLinearization

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace NormalCoordinates
open Set Filter CoordinateGeometry
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem hasFDerivAt_flow_zero {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {x : E} (hx : x ∈ S) {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x, 0)) ∈ U) :
    HasFDerivAt (fun q => Φ (T, q))
      (ContinuousLinearMap.id ℝ (E × E) + T •
        (ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E)) (x, 0) := by
  have heq := FlowLinearization.equilibrium hU (hΦ.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    (hS.prod isOpen_univ) ((contDiffOn_geodesicSpray hS hG hpos).of_le (by simp))
    hzero (fun q hq => ⟨⟨(hode q hq).1, mem_univ _⟩, (hode q hq).2⟩)
    (x := (x, 0)) ⟨hx, mem_univ _⟩ (geodesicSpray_zero G x) hT hseg
  have hd := hasFDerivAt_geodesicSpray_zero hS hG hpos hx
  have hlin := FlowLinearization.nilpotent_variation hU (hΦ.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hzero
    (fun q hq => (hode q hq).2) hd (by intro w; simp) hT hseg heq
  have hTx := hseg T ⟨hT, le_rfl⟩
  have hder := (((hΦ _ hTx).contDiffAt (hU.mem_nhds hTx)).differentiableAt (by simp)).hasFDerivAt.comp
    (x, 0) ((hasFDerivAt_const T (x, 0)).prodMk (hasFDerivAt_id (x, 0)))
  convert! hder using 1
  apply ContinuousLinearMap.ext
  intro w
  simpa [ContinuousLinearMap.comp_apply] using (hlin w T ⟨hT, le_rfl⟩).symm

def normalShear (T : ℝ) (hT : T ≠ 0) : (E × E) ≃L[ℝ] (E × E) where
  toFun q := (q.1, q.1 + T • q.2)
  invFun q := (q.1, T⁻¹ • (q.2 - q.1))
  map_add' a b := by
    ext <;> simp
    abel
  map_smul' a b := by
    apply Prod.ext
    · rfl
    · change a • b.1 + T • (a • b.2) = a • (b.1 + T • b.2)
      rw [smul_add, smul_comm T a]
  left_inv q := by ext <;> simp [smul_smul, hT]
  right_inv q := by ext <;> simp [smul_smul, hT]
  continuous_toFun := continuous_fst.prodMk (continuous_fst.add (continuous_const.smul continuous_snd))
  continuous_invFun := continuous_fst.prodMk (continuous_const.smul (continuous_snd.sub continuous_fst))

theorem hasFDerivAt_normalMap_zero {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {x : E} (hx : x ∈ S) {T : ℝ} (hT : 0 < T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x, 0)) ∈ U) :
    HasFDerivAt (fun q => (q.1, (Φ (T, q)).1)) ((normalShear (E := E) T (ne_of_gt hT)) : E × E →L[ℝ] E × E) (x, 0) := by
  have hd := hasFDerivAt_flow_zero hS hG hpos hU hΦ hzero hode hx hT.le hseg
  convert! hasFDerivAt_fst.prodMk hd.fst using 1

end
end NormalCoordinates

end

end WeakMTWGlobalSupport

end OAI
