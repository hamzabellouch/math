import OAI.Geometry.SurfaceImmersion.Whitney.ShiftedCollarDensity
import OAI.Geometry.SurfaceImmersion.Primitive.ControlledInteriorLoop

namespace OAI

/-! Assemble the velocity angle with its prescribed collar density: a small translation with large turn
jets, an actual positive density, the exact prescribed vector mean, and exactly
two turns. No density or transverse-correction solvability is assumed. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open TransverseSmallFunction

theorem controlled_collar_loop {K L O P U C : Set Base}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L)
    (hO : IsOpen O) (hKO : K ⊆ O) (hOU : Disjoint O U)
    (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f U ∧ (∀ x ∈ K ∩ U, f x = 0) ∧
        fderiv ℝ f p (0, 1) ≠ 0)
    {a A s : Base → ℝ} {c : Base → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hc : ContDiff ℝ ∞ c)
    (hapos : ∀ b ∈ K, 0 < a b)
    (hcollar : ∀ b ∈ U, s b = 0 ∧ c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0])
    (hshape : ∀ b ∈ L \ U,
      (0 < a b ∧ 2 * Real.arctan (a b) ≤ A b ∧ s b ∈ Icc (0 : ℝ) 1 ∧
        c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0]) ∨
      (s b = 1 ∧ Real.pi < A b ∧ c b 0 ^ 2 + c b 1 ^ 2 < 1))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : Base → ℝ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ O ∧
      (∀ x, |h x| < ε) ∧ ∃ W : Set Base, IsOpen W ∧ L ⊆ W ∧
      ∃ ρ : Base × ℝ → ℝ, ContDiffOn ℝ ∞ ρ (W ×ˢ univ) ∧
        (∀ b ∈ W, ∀ t, 0 < ρ (b, t)) ∧
        (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
        (∀ b ∈ W, (∫ t in 0..1, ρ (b, t)) = 1) ∧
        (∀ b ∈ W ∩ C, ∀ t, ρ (b, t) = unitDensity (a b) t) ∧
        ContDiffOn ℝ ∞ (normalizedAngle ρ a A s h) (W ×ˢ univ) ∧
        (∀ b ∈ W, Function.Periodic (fun t => normalizedAngle ρ a A s h (b, t)) 1) ∧
        (∀ b ∈ W, (∫ t in 0..1,
          ![Real.cos (normalizedAngle ρ a A s h (b, t)),
            Real.sin (normalizedAngle ρ a A s h (b, t))]) = c b) ∧
        (∀ b ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
          deriv (fun t => normalizedAngle ρ a A s h (b, t)) θ = 0 ↔
            θ = 0 ∨ θ = PositiveDensity.clock ρ b (1 / 2)) ∧
        ∀ b ∈ K,
          T < fderiv ℝ (fun x => normalizedAngle ρ a A s h (x, 0)) b (0, 1) ∧
          T < fderiv ℝ (fun x => normalizedAngle ρ a A s h
            (x, PositiveDensity.clock ρ b (1 / 2))) b (0, 1) := by
  obtain ⟨δ, hδ, hdensity⟩ := small_shift_collar_density ha hA hs hc hU hC hCU hL hcollar hshape
  obtain ⟨h, hh, hhc, hhs, hhb, hhlarge⟩ := exists_small_turn_function
    hK hO hKO hP hPK hlocal ha hA hs T (lt_min hε hδ)
  have hhδ : ∀ b, |h b| < δ := fun b => lt_of_lt_of_le (hhb b) (min_le_right _ _)
  have hzero : ∀ b ∈ U, h b = 0 := by
    intro b hb
    by_contra hn
    exact Set.disjoint_left.mp hOU
      (hhs (subset_tsupport h (Function.mem_support.mpr hn))) hb
  obtain ⟨W, hW, hKW, ρ, hρ, hpos, hper, hmom, hfixed⟩ := hdensity h hh hhδ hzero
  have hboth (b : Base) (hb : b ∈ W) := LoopDensity.mass_and_mean
    (LocalPeriodicCalculus.smooth_slice hW hρ hb).continuous
    ((blendedPath_smooth ha hA hs hh).continuous.comp
      (continuous_const.prodMk continuous_id)) (hmom b hb)
  have hmass : ∀ b ∈ W, (∫ t in 0..1, ρ (b, t)) = 1 := fun b hb => (hboth b hb).1
  have hmean : ∀ b ∈ W, (∫ t in 0..1, ρ (b, t) •
      blendedPath (a b) (A b) (s b) (h b) t) = c b := fun b hb => (hboth b hb).2
  have hnotU (b : Base) (hb : b ∈ K) : b ∉ U :=
    fun hu => Set.disjoint_left.mp hOU (hKO hb) hu
  have hα := PositiveDensity.reparametrize_smoothOn hW hρ hpos
    (fun b _ => hper b) hmass (unitAngle_smooth ha hA hs hh).contDiffOn
  have hp := blendedPath_smooth ha hA hs hh
  have hqmean (b : Base) (hb : b ∈ W) :
      (∫ t in 0..1, PositiveDensity.reparametrize ρ
        (fun z => blendedPath (a z.1) (A z.1) (s z.1) (h z.1) z.2) (b, t)) = c b :=
    (PositiveDensity.reparametrize_mean hW hρ hpos (fun b _ => hper b)
      hmass hp.contDiffOn hb).trans (hmean b hb)
  refine ⟨h, hh, hhc, hhs, (fun x => lt_of_lt_of_le (hhb x) (min_le_left _ _)),
    W, hW, hKW, ρ, hρ, hpos, hper, hmass, hfixed, hα, ?_, ?_, ?_, ?_⟩
  · intro b hb
    exact PositiveDensity.reparametrize_periodic hW hρ hpos (fun b _ => hper b)
      hmass (fun b _ => unitAngle_periodic (a b) (A b) (s b) (h b)) hb
  · intro b hb
    exact hqmean b hb
  · intro b hb θ hθ
    have hAb : 0 < A b := by
      rcases hshape b ⟨hKL hb, hnotU b hb⟩ with hbase | hinterior
      · exact lt_of_lt_of_le (mul_pos (by norm_num) (Real.arctan_pos.mpr hbase.1)) hbase.2.1
      · exact Real.pi_pos.trans hinterior.2.1
    have hsb : s b ∈ Icc (0 : ℝ) 1 := by
      rcases hshape b ⟨hKL hb, hnotU b hb⟩ with hbase | hinterior
      · exact hbase.2.2.1
      · rw [hinterior.1]; exact ⟨zero_le_one, le_rfl⟩
    exact reparametrized_two_turns ha hA hs hh hW hρ hpos
      (fun b _ => hper b) hmass (hKW (hKL hb)) (hapos b hb) hAb hsb hθ
  · exact large_turns_after_reparametrization ha hA hs hh hW (hKL.trans hKW) hρ hpos
      (fun b _ => hper b) hmass hhlarge

end ClosedSurfaceR4.CollarVelocity

end

end OAI
