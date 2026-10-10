import OAI.Geometry.Arnold.Coordinates

namespace OAI

universe uE

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

open scoped ContDiff Topology
open Set Filter

namespace ArnoldCounterexample.Extension
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma contDiff_mul_of_tsupport_subset {b g : E → ℝ} {U : Set E}
    (hb : ContDiff ℝ ∞ b) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hs : tsupport b ⊆ U) : ContDiff ℝ ∞ (fun x ↦ b x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hb.contDiffAt.mul ((hg x hx).contDiffAt (hU.mem_nhds hx))
  · have hz : x ∉ tsupport b := fun h ↦ hx (hs h)
    have heq : (fun y ↦ b y * g y) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hz] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Local ambient smooth extensions glue globally on a compact subset of a
finite-dimensional real vector space. No extension theorem is assumed. -/
theorem global_extension {K : Set E} (hK : IsCompact K) (f : K → ℝ)
    (hlocal : ∀ z : K, ∃ U : Set E, ∃ g : E → ℝ,
      IsOpen U ∧ ↑z ∈ U ∧ ContDiffOn ℝ ∞ g U ∧ ∀ y : K, ↑y ∈ U → g y = f y) :
    ∃ G : E → ℝ, ContDiff ℝ ∞ G ∧ ∀ z : K, G z = f z := by
  classical
  choose U g hU hz hg heq using hlocal
  have hb : ∀ z : K, ∃ b : E → ℝ,
      tsupport b ⊆ U z ∧ HasCompactSupport b ∧ ContDiff ℝ ∞ b ∧
      range b ⊆ Icc 0 1 ∧ b z = 1 := fun z ↦
    exists_contDiff_tsupport_subset ((hU z).mem_nhds (hz z))
  choose b hbs hbc hbd hbr hbz using hb
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun z : K ↦ Function.support (b z))
    (fun z ↦ (hbd z).continuous.isOpen_support) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simp [Function.mem_support, hbz]⟩)
  obtain ⟨δ, hδs, hδd, hδr⟩ := hK.isClosed.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  let S : E → ℝ := fun x ↦ ∑ z ∈ T, b z x
  let N : E → ℝ := fun x ↦ ∑ z ∈ T, b z x * g z x
  have hS : ContDiff ℝ ∞ S := ContDiff.sum (fun z _ ↦ hbd z)
  have hN : ContDiff ℝ ∞ N := ContDiff.sum (fun z _ ↦
    contDiff_mul_of_tsupport_subset (hbd z) (hU z) (hg z) (hbs z))
  have hSnon (x : E) : 0 ≤ S x := Finset.sum_nonneg (fun z _ ↦ (hbr z ⟨x, rfl⟩).1)
  have hpositive (x : E) : 0 < S x + δ x := by
    by_cases hx : x ∈ K
    · obtain ⟨z, hzT, hzbx⟩ := mem_iUnion₂.mp (hT hx)
      have hbpos : 0 < b z x := lt_of_le_of_ne (hbr z ⟨x, rfl⟩).1 (Ne.symm hzbx)
      have hlt : 0 < S x := lt_of_lt_of_le hbpos
        (Finset.single_le_sum (fun i _ ↦ (hbr i ⟨x, rfl⟩).1) hzT)
      exact add_pos_of_pos_of_nonneg hlt (hδr ⟨x, rfl⟩).1
    · have hδx : δ x ≠ 0 := by
        change x ∈ Function.support δ
        rw [hδs]
        exact hx
      exact add_pos_of_nonneg_of_pos (hSnon x)
        (lt_of_le_of_ne (hδr ⟨x, rfl⟩).1 hδx.symm)
  refine ⟨fun x ↦ N x / (S x + δ x), hN.div (hS.add hδd) (fun x ↦ (hpositive x).ne'), ?_⟩
  intro z
  have hδz : δ z = 0 := by
    by_contra hne
    have hz : ↑z ∈ Function.support δ := hne
    rw [hδs] at hz
    exact hz z.property
  have hNz : N z = S z * f z := by
    dsimp [N, S]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hby : b y z = 0
    · simp [hby]
    · rw [heq y z (hbs y (subset_tsupport (b y) hby))]
  change N z / (S z + δ z) = f z
  rw [hNz, hδz, add_zero]
  exact mul_div_cancel_left₀ (f z) (by simpa [hδz] using (hpositive z).ne')

end ArnoldCounterexample.Extension

end

end OAI
