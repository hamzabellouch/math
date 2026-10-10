import OAI.Geometry.SurfaceImmersion.Geometry.RegularCurvePieces

namespace OAI

/-! Finite loop removal for a compact regular curve. The selected embedded
path uses only its original image and retains a finite smooth decomposition. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem regular_curve_loop_removal {γ : ℝ → M} {U : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U)
    (hreg : ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t))
    (hab : a < b) (hsub : Icc a b ⊆ U)
    (hstart : ∀ t ∈ Ioc a b, γ t ≠ γ a) :
    ∃ P : Path (γ a) (γ b), FiniteRegularPath planeModel P ∧
      Function.Injective P ∧ range P ⊆ γ '' Icc a b := by
  obtain ⟨τ,N,hzero,hmono,hbounds,hend,hpieces⟩ :=
    regular_curve_finite_pieces hU hγ hreg hab.le hsub
  have hstep (n : ℕ) : τ n = a ∨
      ∃ P : Path (γ a) (γ (τ n)), FiniteRegularPath planeModel P ∧
        Function.Injective P ∧ range P ⊆ γ '' Icc a (τ n) := by
    induction n with
    | zero => exact Or.inl hzero
    | succ n ih =>
      by_cases heq : τ (n+1) = a
      · exact Or.inl heq
      right
      by_cases hn : τ n = τ (n+1)
      · rcases ih with ha | ⟨P,hPp,hPi,hPr⟩
        · exact False.elim (heq (hn.symm.trans ha))
        · let Q : Path (γ a) (γ (τ (n+1))) := P.cast rfl (congrArg γ hn.symm)
          refine ⟨Q,hPp.cast _ _,hPi,?_⟩
          change range P ⊆ _
          rw [← hn]
          exact hPr
      have hlt : τ n < τ (n+1) := lt_of_le_of_ne (hmono (Nat.le_succ n)) hn
      obtain ⟨R,hRc,hRs,hRf⟩ := hpieces n hlt
      have hleft : γ (τ n) = R.curve R.start := by rw [hRc,hRs]
      have hright : γ (τ (n+1)) = R.curve R.finish := by rw [hRc,hRf]
      let δ : Path (γ (τ n)) (γ (τ (n+1))) := R.path.cast hleft hright
      have hδp : FiniteRegularPath planeModel δ := (FiniteRegularPath.arc R).cast hleft hright
      have hδi : Function.Injective δ := R.path_injective
      have hδr : range δ = γ '' Icc (τ n) (τ (n+1)) := by
        change range R.path = _
        rw [R.path_range,hRc,hRs,hRf]
      by_cases ha : τ n = a
      · let Q : Path (γ a) (γ (τ (n+1))) := δ.cast (congrArg γ ha.symm) rfl
        refine ⟨Q,hδp.cast _ _,hδi,?_⟩
        change range δ ⊆ _
        rw [hδr,ha]
      · obtain ⟨P,hPp,hPi,hPr⟩ := ih.resolve_left ha
        have hna : a < τ n := lt_of_le_of_ne (hbounds n).1 (Ne.symm ha)
        have hn1a : a < τ (n+1) := hna.trans hlt
        have havoid : γ a ∉ range δ := by
          rw [hδr]
          rintro ⟨t,ht,het⟩
          exact hstart t ⟨hna.trans_le ht.1,ht.2.trans (hbounds (n+1)).2⟩ het
        obtain ⟨Q,hQp,hQi,hQr⟩ := finite_regular_path_join hPp hδp hPi hδi
          (hstart _ ⟨hn1a,(hbounds (n+1)).2⟩).symm havoid
        refine ⟨Q,hQp,hQi,hQr.trans ?_⟩
        apply union_subset
        · exact hPr.trans (image_mono (Icc_subset_Icc_right (hmono (Nat.le_succ n))))
        · rw [hδr]
          exact image_mono (Icc_subset_Icc_left (hbounds n).1)
  rcases hstep N with hNa | ⟨P,hPp,hPi,hPr⟩
  · exact False.elim (hab.ne (hNa.symm.trans (hend N le_rfl)))
  · let Q : Path (γ a) (γ b) := P.cast rfl (congrArg γ (hend N le_rfl).symm)
    refine ⟨Q,hPp.cast _ _,hPi,?_⟩
    change range P ⊆ _
    rw [← hend N le_rfl]
    exact hPr

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
