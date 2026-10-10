import OAI.Geometry.SurfaceImmersion.Correction.CompactTransverseCorrection
import OAI.Geometry.SurfaceImmersion.Correction.FiniteSpecialPointCorrection

namespace OAI

/-! A small function with constant vertical derivative on a compact curve set,
allowing finitely many exceptional points. The regular local defining functions
are the only geometric input; all support and patching choices are constructed. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.TransverseSmallFunction

theorem finite_exceptional_transverse_correction {K O P : Set Base}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧
      ∃ f : Base → ℝ, ContDiff ℝ ∞ f ∧ (∀ x ∈ K ∩ U, f x = 0) ∧
        ∀ x ∈ U, fderiv ℝ f x (0, 1) ≠ 0)
    (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Base → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ O ∧
      (∀ x, |H x| < ε) ∧ ∀ x ∈ K, fderiv ℝ H x (0, 1) = B := by
  classical
  let : Fintype P := hP.fintype
  obtain ⟨H₀, hH₀, hH₀c, hH₀s, hH₀b, V, hV, hPV, _, hH₀d⟩ :=
    exists_finite_special_correction (fun p : P => p.val) Subtype.val_injective hO
      (fun p => hKO (hPK p.property)) B (half_pos hε)
  let T : Base → ℝ := fun x => B - fderiv ℝ H₀ x (0, 1)
  have hT : ContDiff ℝ ∞ T :=
    contDiff_const.sub (((hH₀.fderiv_right (by simp)).clm_apply contDiff_const))
  have hTV (p : Base) (hp : p ∈ V) : p ∉ tsupport T := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [hV.mem_nhds hp] with x hx
    change B - fderiv ℝ H₀ x (0, 1) = 0
    rw [hH₀d x hx, sub_self]
  have hl (p : Base) (hp : p ∈ K ∩ tsupport T) :=
    hlocal p ⟨hp.1, fun hpp => hTV p (hPV ⟨p, hpp⟩) hp.2⟩
  obtain ⟨H₁, hH₁, hH₁c, hH₁s, hH₁b, hH₁d⟩ :=
    compact_transverse_correction (0, 1) hK hO hKO hT hl (half_pos hε)
  refine ⟨fun x => H₀ x + H₁ x, hH₀.add hH₁, ?_, ?_, ?_, ?_⟩
  · exact (hH₀c.union hH₁c).of_isClosed_subset (isClosed_tsupport _) (tsupport_add H₀ H₁)
  · exact (tsupport_add H₀ H₁).trans (union_subset hH₀s hH₁s)
  · intro x
    calc
      |H₀ x + H₁ x| ≤ |H₀ x| + |H₁ x| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hH₀b x) (hH₁b x)
      _ = ε := add_halves ε
  · intro x hx
    rw [fderiv_fun_add (hH₀.differentiable (by simp) x)
      (hH₁.differentiable (by simp) x), add_apply, hH₁d x hx]
    change fderiv ℝ H₀ x (0, 1) + (B - fderiv ℝ H₀ x (0, 1)) = B
    ring

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
