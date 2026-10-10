import OAI.Geometry.SurfaceImmersion.Whitney.SmallCollarAngle

namespace OAI

/-! The small-angle collar is chosen before the compact interior curve set
and before its turn threshold. The later translation may overlap that collar. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.CollarVelocity
open RealModes TransverseSmallFunction

theorem calibrated_jet_collar_family {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {C L U Ω : Set JetBase} (hC : IsCompact C) (hL : IsCompact L) (hCL : C ⊆ L)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hCU : C ⊆ U) (hUΩ : U ⊆ Ω) (hLΩ : L ⊆ Ω)
    {R u v a : JetBase → ℝ} (hR : ContDiffOn ℝ ∞ R Ω)
    (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ha : ContDiffOn ℝ ∞ a Ω) (hRp : ∀ j ∈ Ω, 0 < R j)
    (hquad : ∀ j ∈ Ω, R j ^ 2 = u j ^ 2 + v j ^ 2 + a j ^ 2)
    (hup : ∀ j ∈ U, 0 < u j) (hvz : ∀ j ∈ U, v j = 0)
    (hap : ∀ j ∈ L \ C, 0 < a j) (haC : ∀ j ∈ C, a j = 0) :
    ∃ W : Set JetBase, IsOpen W ∧ C ⊆ W ∧ W ⊆ U ∧
      ∀ ε : ℝ, 0 < ε → ∃ V : Set JetBase, IsOpen V ∧ C ⊆ V ∧ V ⊆ W ∧
      ∀ (K O P : Set Base), IsCompact K → MapsTo (jetSection F) K L →
        IsOpen O → K ⊆ O → (∀ j ∈ C, j.1 ∉ closure O) →
        P.Finite → P ⊆ K →
        (∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
          ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
            fderiv ℝ f p (0,1) ≠ 0) →
      ∀ T : ℝ, ∃ Z : Set JetBase, IsOpen Z ∧ L ⊆ Z ∧ Z ⊆ Ω ∧
        ∃ α : JetBase × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
          (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
          (∀ j ∈ Z, (∫ t in 0..1, ![Real.cos (α (j,t)),Real.sin (α (j,t))]) =
            ![u j/R j,v j/R j]) ∧
          (∀ j ∈ V, ∀ t, |α (j,t)| < ε) ∧
          (∃ W' : Set JetBase, IsOpen W' ∧ C ⊆ W' ∧ W' ⊆ W ∧
            ∀ j ∈ W', a j = 0 → ∀ t, α (j,t) = 0) ∧
          ∃ τ : Base → ℝ,
            (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
              deriv (fun t => α (jetSection F x,t)) θ = 0 ↔ θ = 0 ∨ θ = τ x) ∧
            ∀ x ∈ K,
              T < fderiv ℝ (fun y => α (jetSection F y,0)) x (0,1) ∧
              T < fderiv ℝ (fun y => α (jetSection F y,τ x)) x (0,1) := by
  obtain ⟨c,hc,V₀,hV₀,hLV₀,hV₀Ω,hcL,W,hW,hCW,hWU,b,s,hb,hs,hsr,hbp,hw,hshape⟩ :=
    calibrated_collar_data hC hL hCL hU hΩ hCU hUΩ hLΩ hR hu hv ha hRp hquad hup hvz hap
  have hbC : ∀ j ∈ C, b j = 0 := by
    intro j hj
    rw [(hw j (hCW hj)).1,haC j hj]
    simp [amplitude]
  have hbpos : ∀ j ∈ L \ C, 0 < b j := by
    intro j hj
    by_cases hjW : j ∈ W
    · rw [(hw j hjW).1]
      exact div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (hap j hj))
        (add_pos (hRp j (hLΩ hj.1)) (hup j (hWU hjW)))
    · exact hbp j ⟨hj.1,hjW⟩
  refine ⟨W,hW,hCW,hWU,?_⟩
  intro ε hε
  obtain ⟨V,hV,hCV,hVW,δ,hδ,hangle⟩ := small_collar_angle_window hW hCW hb.continuous hbC hε
  refine ⟨V,hV,hCV,hVW,?_⟩
  intro K O P hK hKL hO hKO hCO hP hPK hlocal T
  let W' : Set JetBase := W ∩ (Prod.fst ⁻¹' closure O)ᶜ
  have hW' : IsOpen W' := hW.inter (isClosed_closure.preimage continuous_fst).isOpen_compl
  have hCW' : C ⊆ W' := fun j hj => ⟨hCW hj,hCO j hj⟩
  have hW'W : W' ⊆ W := inter_subset_left
  have hOW' : ∀ j ∈ W', j.1 ∉ O := fun j hj ho => hj.2 (subset_closure ho)
  have hbK : ∀ x ∈ K, 0 < b (jetSection F x) := by
    intro x hx
    apply hbpos _ ⟨hKL hx,?_⟩
    intro hxc
    exact hCO _ hxc (subset_closure (hKO hx))
  have hshape' : ∀ j ∈ L \ W',
      (0 < b j ∧ 2 * Real.arctan (b j) ≤ Real.pi+1 ∧ s j ∈ Icc (0 : ℝ) 1 ∧
        c j = ![(1-b j^2/2)/(1+b j^2/2),0]) ∨
      (s j = 1 ∧ Real.pi < Real.pi+1 ∧ c j 0^2+c j 1^2 < 1) := by
    intro j hj
    by_cases hjW : j ∈ W
    · left
      refine ⟨hbpos j ⟨hj.1,fun hc => hj.2 (hCW' hc)⟩,?_,hsr j,(hw j hjW).2.2⟩
      linarith [Real.arctan_lt_pi_div_two (b j)]
    · exact hshape j ⟨hj.1,hjW⟩
  obtain ⟨h,_,_,hhs,hhδ,V₁,hV₁,hLV₁,ρ,_,_,_,_,_,hα,hper,hmean,hturn,hlarge⟩ :=
    controlled_jet_loop hF hK hL hKL hO hKO hOW' hW' hC.isClosed hCW'
      hP hPK hlocal hb (A := fun _ => Real.pi+1) contDiff_const hs hc hbK
      (fun j hj => ⟨(hw j (hW'W hj)).2.1,(hw j (hW'W hj)).2.2⟩) hshape' T hδ
  let α := jetAngle ρ b (fun _ => Real.pi+1) s (fun j => h j.1)
  have hz (j : JetBase) (hj : j ∈ W') : h j.1 = 0 := by
    by_contra hn
    exact hOW' j hj (hhs (subset_tsupport h (Function.mem_support.mpr hn)))
  refine ⟨V₁ ∩ V₀,hV₁.inter hV₀,subset_inter hLV₁ hLV₀,
    inter_subset_right.trans hV₀Ω,α,hα.mono (prod_mono inter_subset_left Subset.rfl),
    (fun j hj => hper j hj.1),(fun j hj => (hmean j hj.1).trans (hcL j hj.2)),?_,
    ⟨W',hW',hCW',hW'W,?_⟩,_,hturn,hlarge⟩
  · intro j hj t
    exact hangle (fun _ => Real.pi+1) s (fun j => h j.1) ρ
      (fun j hj => (hw j hj).2.1) (fun j => hhδ j.1) j hj t
  · intro j hj haz t
    have hbz : b j = 0 := by rw [(hw j (hW'W hj)).1]; simp [amplitude,haz]
    simp [α,jetAngle,PositiveDensity.reparametrize,unitAngle,blendedAngle,baseAngle,
      hbz,(hw j (hW'W hj)).2.1,hz j hj]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
