import OAI.Geometry.RCD.Coordinates.RegularActualPatches

namespace OAI

/-! # The working chart and a total inverse for the actual patch data -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

/-- Restrict an existing open coordinate chart to a smaller open set. -/
theorem restrict_open_coordinate_chart {X E : Type*} [TopologicalSpace X]
    [TopologicalSpace E] {A U : Set X} {O : Set E} (hA : IsOpen A) (hO : IsOpen O)
    (hAU : A ⊆ U) (f : X → E) (u : U ≃ₜ O) (hu : ∀ x, (u x).val = f x.val) :
    IsOpen (Set.range (fun x : A => f x.val)) ∧
      ∃ v : A ≃ₜ Set.range (fun x : A => f x.val), ∀ x, (v x).val = f x.val := by
  have hi : Topology.IsOpenEmbedding (Set.inclusion hAU) :=
    .inclusion hAU (hA.preimage continuous_subtype_val)
  have hg := hO.isOpenEmbedding_subtypeVal.comp (u.isOpenEmbedding.comp hi)
  have heq : (Subtype.val ∘ u ∘ Set.inclusion hAU) = (fun x : A => f x.val) := by
    funext x
    exact hu (Set.inclusion hAU x)
  rw [heq] at hg
  exact ⟨hg.isOpen_range, hg.isEmbedding.toHomeomorph, fun _ => rfl⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem RegularBilinearData.patch_region_subset_initial {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
    {base : X} {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    {enlargement zeta : ℝ} (d : RegularBilinearData hX base hk enlargement zeta) :
    d.patchRegion ⊆ ball base (d.radius / 1024) := by
  apply ball_subset_ball
  have hp : (1024 : ℝ) ≤ 2 ^ (d.shift + 10) := by
    calc
      1024 = (2 : ℝ) ^ 10 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  exact div_le_div_of_nonneg_left d.radius_pos.le (by norm_num) hp

/-- The region used for the finite heat nets is an open subchart of the
previously constructed initial coordinate neighborhood. -/
theorem regular_working_chart {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta : 0 ≤ zeta) (hzetaSmall : zeta ≤ 1 / 2048)
    (hgramSmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 4 : ℝ) ^ n)⁻¹) * zeta) ≤ 3 / 4) :
    IsOpen (Set.range (fun x : e.heat.patchRegion => e.heat.values x.val)) ∧
      ∃ chart : e.heat.patchRegion ≃ₜ Set.range (fun x : e.heat.patchRegion => e.heat.values x.val),
        ∀ x, (chart x).val = e.heat.values x.val := by
  obtain ⟨hO, chart, hc⟩ := regular_initial_chart hX e hzeta hzetaSmall hgramSmall
  exact restrict_open_coordinate_chart isOpen_ball hO e.heat.patch_region_subset_initial
    e.heat.values chart hc

/-- The inverse of a working chart, extended outside its image, takes
values in the same original-space neighborhood as every energy field. -/
theorem exists_working_chart_inverse {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    [(hausdorff n X).Regular] {base : X} {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    {enlargement zeta : ℝ} (d : RegularBilinearData hX base hk enlargement zeta)
    {Ω : Set (Euclidean n)} (u : d.patchRegion ≃ₜ Ω)
    (hu : ∀ q, (u q).val = d.values q.val) :
    ∃ inverse : Euclidean n → {q : X // q ∈ ball base (d.radius / 32)},
      ∀ x ∈ Ω, (inverse x).val ∈ d.patchRegion ∧ d.values (inverse x).val = x := by
  classical
  let fallback : {q : X // q ∈ ball base (d.radius / 32)} :=
    ⟨base, mem_ball_self (div_pos d.radius_pos (by norm_num))⟩
  let inverse := fun x => if hx : x ∈ Ω then
    (⟨(u.symm ⟨x, hx⟩).val, d.patch_region_subset (u.symm ⟨x, hx⟩).property⟩ :
      {q : X // q ∈ ball base (d.radius / 32)}) else fallback
  refine ⟨inverse, ?_⟩
  intro x hx
  simp only [inverse, dite_eq_left hx]
  refine ⟨(u.symm ⟨x, hx⟩).property, ?_⟩
  rw [← hu, u.apply_symm_apply]

/-- A right inverse lying in the working region is also a left inverse
there, because these are the same open chart coordinates. -/
theorem working_chart_inverse_left {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    [(hausdorff n X).Regular] {base : X} {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    {enlargement zeta : ℝ} (d : RegularBilinearData hX base hk enlargement zeta)
    {Ω : Set (Euclidean n)} (u : d.patchRegion ≃ₜ Ω)
    (hu : ∀ q, (u q).val = d.values q.val)
    (inverse : Euclidean n → {q : X // q ∈ ball base (d.radius / 32)})
    (hinverse : ∀ x ∈ Ω, (inverse x).val ∈ d.patchRegion ∧ d.values (inverse x).val = x)
    {q : X} (hq : q ∈ d.patchRegion) : (inverse (d.values q)).val = q := by
  have hmem : d.values q ∈ Ω := by rw [← hu ⟨q, hq⟩]; exact (u ⟨q, hq⟩).property
  have hq' := hinverse (d.values q) hmem
  have heq : u ⟨(inverse (d.values q)).val, hq'.1⟩ = u ⟨q, hq⟩ := by
    apply Subtype.ext
    simp only [hu, hq'.2]
  exact congrArg Subtype.val (u.injective heq)

end RegularPointCoordinates

end

end OAI
