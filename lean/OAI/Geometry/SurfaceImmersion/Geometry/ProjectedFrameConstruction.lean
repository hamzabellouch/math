import OAI.Geometry.SurfaceImmersion.Primitive.ProjectedVelocityFrame
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! Construct the collar interpolation of the velocity frame from boundary
non-antipodality, with no interpolation function assumed. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma nonopposite_region_open {Ω : Set E} (hΩ : IsOpen Ω) {B n : E → Vec}
    (hB : ContDiffOn ℝ ∞ B Ω) (hn : ContDiffOn ℝ ∞ n Ω) :
    IsOpen {x | x ∈ Ω ∧ B x ≠ 0 ∧ normalize (B x) ≠ -n x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hb := hB.contDiffAt (hΩ.mem_nhds hx.1)
  have hn' := hn.contDiffAt (hΩ.mem_nhds hx.1)
  have hanti := ((normalize_smoothAt hb hx.2.1).continuousAt.ne_iff_eventually_ne
    hn'.continuousAt.neg).mp hx.2.2
  filter_upwards [hΩ.mem_nhds hx.1, hb.continuousAt.eventually_ne hx.2.1, hanti] with y hy hb' ha'
  exact ⟨hy, hb', ha'⟩

theorem exists_projected_collar_frame {K Ω : Set E}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {X Y C B n : E → Vec} {μ ν : E → ℝ}
    (hX : ContDiffOn ℝ ∞ X Ω) (hY : ContDiffOn ℝ ∞ Y Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hn : ContDiffOn ℝ ∞ n Ω)
    (hgeom : ∀ x ∈ Ω, gramDet (X x) (Y x) ≠ 0 ∧ μ x < 0 ∧
      X x ⬝ᵥ B x = 0 ∧ Y x ⬝ᵥ B x = 0 ∧
      C x = μ x • X x + ν x • Y x + B x ∧
      X x ⬝ᵥ n x = 0 ∧ Y x ⬝ᵥ n x = 0 ∧ n x ⬝ᵥ n x = 1)
    (hboundary : ∀ x ∈ K, B x ≠ 0 ∧ normalize (B x) ≠ -n x) :
    ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ Ω ∧
      ∃ e₁ e₂ : E → Vec, ContDiffOn ℝ ∞ e₁ Ω ∧ ContDiffOn ℝ ∞ e₂ Ω ∧
        (∀ x ∈ Ω, e₁ x ⬝ᵥ e₁ x = 1 ∧ e₂ x ⬝ᵥ e₂ x = 1 ∧ e₁ x ⬝ᵥ e₂ x = 0 ∧
          Y x ⬝ᵥ e₁ x = 0 ∧ C x ⬝ᵥ e₁ x = 0 ∧
          Y x ⬝ᵥ e₂ x = 0 ∧ C x ⬝ᵥ e₂ x = 0) ∧
        (∀ x ∈ W, e₁ x = normalize (RealModes.realNormalPart (Y x) (C x) (X x))) := by
  let U : Set E := {x | x ∈ Ω ∧ B x ≠ 0 ∧ normalize (B x) ≠ -n x}
  have hU : IsOpen U := nonopposite_region_open hΩ hB hn
  have hKU : K ⊆ U := fun x hx => ⟨hKΩ hx, hboundary x hx⟩
  obtain ⟨W, hW, hKW, hWU, χ, ψ, hχ, _, _, _, hχr, _, _, hχs, hχone, _⟩ :=
    CollarVelocity.nested_compact_cutoffs hK hU hKU
  let t : E → ℝ := fun x => 1 - χ x
  have ht : ContDiff ℝ ∞ t := contDiff_const.sub hχ
  have hDt (x : E) (hx : x ∈ Ω) : gramDet (Y x) (C x) ≠ 0 := by
    obtain ⟨hd, hm, hxb, hyb, hc, _, _, _⟩ := hgeom x hx
    exact (velocity_gram_pos hd hm.ne hxb hyb hc).ne'
  have hblend (x : E) (hx : x ∈ Ω) :
      blend (RealModes.realNormalPart (Y x) (C x) (X x))
        (RealModes.realNormalPart (Y x) (C x) (n x)) (t x) ≠ 0 := by
    obtain ⟨hd, hm, hxb, hyb, hc, hxn, hyn, hn1⟩ := hgeom x hx
    have htr : t x ∈ Icc (0 : ℝ) 1 := by
      obtain ⟨hl, hu⟩ := hχr x
      exact ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
    have htu : t x < 1 → x ∈ U := by
      intro hlt
      apply hχs
      apply subset_tsupport χ
      apply Function.mem_support.mpr
      intro hz
      dsimp [t] at hlt
      linarith
    exact projected_blend_nonzero hd hm hxb hyb hc hxn hyn hn1 htr
      (fun h => (htu h).2.1) (fun h => (htu h).2.2)
  obtain ⟨he₁, he₂⟩ := projected_frame_smoothOn hΩ hX hY hC hn ht.contDiffOn hDt hblend
  refine ⟨W, hW, hKW, hWU.trans (fun _ hx => hx.1),
    (fun x => projectedFirst (X x) (Y x) (C x) (n x) (t x)),
    (fun x => projectedSecond (X x) (Y x) (C x) (n x) (t x)),
    he₁, he₂, ?_, ?_⟩
  · exact fun x hx => projected_frame_orthonormal (hDt x hx) (hblend x hx)
  · intro x hx
    have ht0 : t x = 0 := by simp [t, hχone x hx]
    simpa only [ht0] using projectedFirst_zero (X x) (Y x) (C x) (n x)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
