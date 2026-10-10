import OAI.Geometry.SurfaceImmersion.Whitney.CalibratedCollarData
import OAI.Geometry.SurfaceImmersion.Primitive.JetVelocityLoop

namespace OAI

/-! Calibrate the controlled angle on a neighborhood of the actual second
jets, retaining the prescribed spatial derivatives on the original surface. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open RealModes TransverseSmallFunction

theorem calibrated_jet_angle {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {K O P : Set Base} {C L U Ω : Set JetBase}
    (hK : IsCompact K) (hC : IsCompact C) (hL : IsCompact L)
    (hCL : C ⊆ L) (hKL : MapsTo (jetSection F) K L)
    (hO : IsOpen O) (hKO : K ⊆ O) (hOU : ∀ j ∈ U, j.1 ∉ O)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hCU : C ⊆ U) (hUΩ : U ⊆ Ω) (hLΩ : L ⊆ Ω)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
        fderiv ℝ f p (0, 1) ≠ 0)
    {R u v a : JetBase → ℝ} (hR : ContDiffOn ℝ ∞ R Ω)
    (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ha : ContDiffOn ℝ ∞ a Ω) (hRp : ∀ j ∈ Ω, 0 < R j)
    (hquad : ∀ j ∈ Ω, R j ^ 2 = u j ^ 2 + v j ^ 2 + a j ^ 2)
    (hup : ∀ j ∈ U, 0 < u j) (hvz : ∀ j ∈ U, v j = 0)
    (hap : ∀ j ∈ L \ C, 0 < a j) (T : ℝ) :
    ∃ Z : Set JetBase, IsOpen Z ∧ L ⊆ Z ∧ Z ⊆ Ω ∧
      ∃ α : JetBase × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
        (∀ j ∈ Z, Function.Periodic (fun t => α (j, t)) 1) ∧
        (∀ j ∈ Z, (∫ t in 0..1, ![Real.cos (α (j, t)), Real.sin (α (j, t))]) =
          ![u j / R j, v j / R j]) ∧
        (∃ W : Set JetBase, IsOpen W ∧ C ⊆ W ∧ W ⊆ U ∧
          ∀ j ∈ W, a j = 0 → ∀ t, α (j, t) = 0) ∧
        ∃ τ : Base → ℝ,
          (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
            deriv (fun t => α (jetSection F x, t)) θ = 0 ↔ θ = 0 ∨ θ = τ x) ∧
          ∀ x ∈ K,
            T < fderiv ℝ (fun y => α (jetSection F y, 0)) x (0, 1) ∧
            T < fderiv ℝ (fun y => α (jetSection F y, τ x)) x (0, 1) := by
  obtain ⟨c, hc, V₀, hV₀, hLV₀, hV₀Ω, hcL, W, hW, hCW, hWU, b, s, hb, hs,
    _, hbp, hw, hshape⟩ := calibrated_collar_data hC hL hCL hU hΩ hCU hUΩ hLΩ
      hR hu hv ha hRp hquad hup hvz hap
  have hOW : ∀ j ∈ W, j.1 ∉ O := fun j hj => hOU j (hWU hj)
  have hbK : ∀ x ∈ K, 0 < b (jetSection F x) := by
    intro x hx
    exact hbp _ ⟨hKL hx, fun hj => hOW _ hj (hKO hx)⟩
  obtain ⟨h, _, _, hhs, _, V, hV, hLV, ρ, _, _, _, _, _, hα, hper, hmean,
    hturn, hlarge⟩ := controlled_jet_loop hF hK hL hKL hO hKO hOW hW hC.isClosed hCW
      hP hPK hlocal hb (A := fun _ => Real.pi + 1) contDiff_const hs hc hbK
      (fun j hj => ⟨(hw j hj).2.1, (hw j hj).2.2⟩) hshape T (by norm_num : (0 : ℝ) < 1)
  let α := jetAngle ρ b (fun _ => Real.pi + 1) s (fun j => h j.1)
  have hz (j : JetBase) (hj : j ∈ W) : h j.1 = 0 := by
    by_contra hn
    exact hOW j hj (hhs (subset_tsupport h (Function.mem_support.mpr hn)))
  refine ⟨V ∩ V₀, hV.inter hV₀, subset_inter hLV hLV₀,
    inter_subset_right.trans hV₀Ω, α,
    hα.mono (prod_mono inter_subset_left (Subset.rfl)), ?_, ?_, ?_,
    (fun x => PositiveDensity.clock ρ (jetSection F x) (1 / 2)), hturn, hlarge⟩
  · exact fun j hj => hper j hj.1
  · intro j hj
    exact (hmean j hj.1).trans (hcL j hj.2)
  · refine ⟨W, hW, hCW, hWU, ?_⟩
    intro j hj haz t
    have hbz : b j = 0 := by rw [(hw j hj).1]; simp [amplitude, haz]
    simp [α, jetAngle, PositiveDensity.reparametrize, unitAngle,
      blendedAngle, baseAngle, hbz, (hw j hj).2.1, hz j hj]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
