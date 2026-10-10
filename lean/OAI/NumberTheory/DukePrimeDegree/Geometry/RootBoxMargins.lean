import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafBoxMaximal

namespace OAI

/-!
# Root boxes with a uniform interval margin

Every point has a smaller open root box for which a fixed positive time
interval stays inside a larger root box. Compactness makes these margins
uniform on any prescribed compact set.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

structure BufferedRootBox {n : ℕ} {i j : Fin n} (hij : i ≠ j) where
  pivot : Fin n
  box : RootBox hij pivot
  radius : ℝ
  time_bound : box.time ⊆ rootLeafWindow radius 0
  core : Set (X n)
  core_open : IsOpen core
  core_subset : core ⊆ box.range
  margin : ℝ
  margin_pos : 0 < margin
  time_margin : ∀ z ∈ box.domain, rootQuotientParametrization hij z ∈ core →
    closedBall z.2 margin ⊆ box.time

theorem exists_bufferedRootBox_at {n : ℕ} {i j : Fin n} (hij : i ≠ j) (x : X n) :
    ∃ A : BufferedRootBox hij, x ∈ A.core := by
  obtain ⟨A, hx⟩ := exists_boundedRootBox_at hij x
  obtain ⟨z, hz⟩ := hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp A.box.time_open z.val.2 z.property.2
  have hsmall : ball z.val.2 (ε / 2) ⊆ A.box.time := by
    apply (ball_subset_ball (by linarith : ε / 2 ≤ ε)).trans hball
  let B := A.box.shrink A.box.transverse (ball z.val.2 (ε / 2))
    A.box.transverse_open isOpen_ball subset_rfl hsmall
  have hsub : B.range ⊆ A.box.range := by
    rintro y ⟨w, rfl⟩
    exact ⟨⟨w.val, w.property.1, hsmall w.property.2⟩, rfl⟩
  refine ⟨⟨A.pivot, A.box, A.radius, A.time_bound, B.range, B.range_open,
    hsub, ε / 4, by positivity, ?_⟩, ?_⟩
  · intro w hw hwB v hv
    obtain ⟨u, hu⟩ := hwB
    have he : (⟨u.val, u.property.1, hsmall u.property.2⟩ : A.box.domain) = ⟨w, hw⟩ :=
      A.box.embedding.injective hu
    have huw : u.val = w := congrArg Subtype.val he
    have hwclose : dist w.2 z.val.2 < ε / 2 := by
      simpa only [huw] using (show dist u.val.2 z.val.2 < ε / 2 from u.property.2)
    apply hball
    have hvclose : dist v w.2 ≤ ε / 4 := hv
    have hd := dist_triangle v w.2 z.val.2
    change dist v z.val.2 < ε
    linarith
  · exact ⟨⟨z.val, z.property.1, mem_ball_self (by positivity)⟩, hz⟩

theorem compact_bufferedRootBox_cover {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (K : Set (X n)) (hK : IsCompact K) :
    ∃ (F : Finset (BufferedRootBox hij)) (δ : ℝ), 0 < δ ∧
      K ⊆ ⋃ A ∈ F, A.core ∧ ∀ A ∈ F, δ ≤ A.margin := by
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun A : BufferedRootBox hij => A.core)
    (fun A => A.core_open) (by
      intro x _
      obtain ⟨A, hx⟩ := exists_bufferedRootBox_at hij x
      exact mem_iUnion.mpr ⟨A, hx⟩)
  by_cases hne : F.Nonempty
  · refine ⟨F, F.inf' hne BufferedRootBox.margin, ?_, hF, ?_⟩
    · exact (Finset.lt_inf'_iff hne).mpr fun A _ => A.margin_pos
    · intro A hA
      exact Finset.inf'_le _ hA
  · refine ⟨F, 1, zero_lt_one, hF, ?_⟩
    intro A hA
    exact (hne ⟨A, hA⟩).elim

end DukePrimeDegree

end

end OAI
