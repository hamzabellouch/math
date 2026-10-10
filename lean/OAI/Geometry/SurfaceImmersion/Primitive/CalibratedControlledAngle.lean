import OAI.Geometry.SurfaceImmersion.Whitney.CalibratedCollarData
import OAI.Geometry.SurfaceImmersion.Whitney.ControlledCollarLoop

namespace OAI

/-! The controlled angle from geometric scalar coordinates. The collar,
amplitude, transition, small translation and density are all constructed. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open TransverseSmallFunction

theorem calibrated_controlled_angle {C K L U Ω P : Set Base}
    (hC : IsCompact C) (hK : IsCompact K) (hL : IsCompact L)
    (hCL : C ⊆ L) (hKL : K ⊆ L) (hKU : Disjoint K (closure U))
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hCU : C ⊆ U) (hUΩ : U ⊆ Ω) (hLΩ : L ⊆ Ω)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
        fderiv ℝ f p (0, 1) ≠ 0)
    {R u v a : Base → ℝ} (hR : ContDiffOn ℝ ∞ R Ω)
    (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ha : ContDiffOn ℝ ∞ a Ω)
    (hRp : ∀ x ∈ Ω, 0 < R x)
    (hquad : ∀ x ∈ Ω, R x ^ 2 = u x ^ 2 + v x ^ 2 + a x ^ 2)
    (hup : ∀ x ∈ U, 0 < u x) (hvz : ∀ x ∈ U, v x = 0)
    (hap : ∀ x ∈ L \ C, 0 < a x) (T : ℝ) :
    ∃ Z : Set Base, IsOpen Z ∧ L ⊆ Z ∧ Z ⊆ Ω ∧
      ∃ α : Base × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
        (∀ x ∈ Z, Function.Periodic (fun t => α (x, t)) 1) ∧
        (∀ x ∈ Z, (∫ t in 0..1, ![Real.cos (α (x, t)), Real.sin (α (x, t))]) =
          ![u x / R x, v x / R x]) ∧
        (∃ W : Set Base, IsOpen W ∧ C ⊆ W ∧ W ⊆ U ∧
          ∀ x ∈ W, a x = 0 → ∀ t, α (x, t) = 0) ∧
        ∃ τ : Base → ℝ,
          (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
            deriv (fun t => α (x, t)) θ = 0 ↔ θ = 0 ∨ θ = τ x) ∧
          ∀ x ∈ K, T < fderiv ℝ (fun y => α (y, 0)) x (0, 1) ∧
            T < fderiv ℝ (fun y => α (y, τ x)) x (0, 1) := by
  obtain ⟨c, hc, V₀, hV₀, hLV₀, hV₀Ω, hcL, W, hW, hCW, hWU, b, s, hb, hs, _, hbp, hw, hshape⟩ :=
    calibrated_collar_data hC hL hCL hU hΩ hCU hUΩ hLΩ hR hu hv ha hRp hquad hup hvz hap
  let O := Ω \ closure W
  have hO : IsOpen O := hΩ.sdiff isClosed_closure
  have hKO : K ⊆ O := by
    intro x hx
    exact ⟨hLΩ (hKL hx), fun hxw => Set.disjoint_left.mp hKU hx (closure_mono hWU hxw)⟩
  have hOW : Disjoint O W := by
    apply Set.disjoint_left.mpr
    exact fun _ hx hw' => hx.2 (subset_closure hw')
  have hpos : ∀ x ∈ K, 0 < b x := by
    intro x hx
    exact hbp x ⟨hKL hx, fun hw' => Set.disjoint_left.mp hOW (hKO hx) hw'⟩
  obtain ⟨h, hh, _, hhs, _, V, hV, hLV, ρ, hρ, _, _, _, _, hα, hper, hmean,
    hturn, hlarge⟩ := controlled_collar_loop hK hL hKL hO hKO hOW hW hC.isClosed hCW
      hP hPK hlocal hb (a := b) (A := fun _ => Real.pi + 1) contDiff_const hs hc hpos
      (fun x hx => ⟨(hw x hx).2.1, (hw x hx).2.2⟩) hshape T (by norm_num : (0 : ℝ) < 1)
  let α := normalizedAngle ρ b (fun _ => Real.pi + 1) s h
  have hz (x : Base) (hx : x ∈ W) : h x = 0 := by
    by_contra hn
    exact Set.disjoint_left.mp hOW
      (hhs (subset_tsupport h (Function.mem_support.mpr hn))) hx
  refine ⟨V ∩ V₀, hV.inter hV₀, subset_inter hLV hLV₀, inter_subset_right.trans hV₀Ω,
    α, hα.mono (prod_mono inter_subset_left (Subset.rfl)), ?_, ?_, ?_,
    (fun x => PositiveDensity.clock ρ x (1 / 2)), hturn, hlarge⟩
  · exact fun x hx => hper x hx.1
  · intro x hx
    exact (hmean x hx.1).trans (hcL x hx.2)
  · refine ⟨W, hW, hCW, hWU, ?_⟩
    intro x hx haz t
    have hbz : b x = 0 := by rw [(hw x hx).1]; simp [amplitude, haz]
    simp [α, normalizedAngle, PositiveDensity.reparametrize, unitAngle,
      blendedAngle, baseAngle, hbz, (hw x hx).2.1, hz x hx]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
