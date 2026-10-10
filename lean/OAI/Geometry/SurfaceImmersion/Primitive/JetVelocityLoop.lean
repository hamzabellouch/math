import OAI.Geometry.SurfaceImmersion.Whitney.ControlledCollarLoop
import OAI.Geometry.SurfaceImmersion.Geometry.PositiveDensityPullback
import OAI.Geometry.Immersion.ClosedSurface.NormalJets

namespace OAI

/-! A controlled loop on a neighborhood of the actual second-jet section.
Its translation depends on position alone, so the prescribed turn derivatives
along the original section persist under the joint density construction. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open RealModes TransverseSmallFunction

abbrev JetBase := Base × RealTwoJet

def jetSection (F : RField 4) (x : Base) : JetBase := (x, realTwoJet F x)

lemma jetSection_smooth {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (jetSection F) := contDiff_id.prodMk (contDiff_realTwoJet hF)

def jetAngle (ρ : JetBase × ℝ → ℝ) (a A s h : JetBase → ℝ) : JetBase × ℝ → ℝ :=
  PositiveDensity.reparametrize ρ
    (fun z => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2)

lemma jetAngle_on_section (F : RField 4) (ρ : JetBase × ℝ → ℝ)
    (a A s : JetBase → ℝ) (h : Base → ℝ) (x : Base) (t : ℝ) :
    jetAngle ρ a A s (fun z => h z.1) (jetSection F x, t) =
      normalizedAngle (PositiveDensity.pullbackDensity ρ (jetSection F))
        (a ∘ jetSection F) (A ∘ jetSection F) (s ∘ jetSection F) h (x, t) := rfl

theorem controlled_jet_loop {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {K O P : Set Base} {L U C : Set JetBase}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : MapsTo (jetSection F) K L)
    (hO : IsOpen O) (hKO : K ⊆ O)
    (hOU : ∀ j ∈ U, j.1 ∉ O)
    (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
        fderiv ℝ f p (0, 1) ≠ 0)
    {a A s : JetBase → ℝ} {c : JetBase → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hc : ContDiff ℝ ∞ c)
    (hapos : ∀ x ∈ K, 0 < a (jetSection F x))
    (hcollar : ∀ j ∈ U, s j = 0 ∧ c j = ![(1 - a j ^ 2 / 2) / (1 + a j ^ 2 / 2), 0])
    (hshape : ∀ j ∈ L \ U,
      (0 < a j ∧ 2 * Real.arctan (a j) ≤ A j ∧ s j ∈ Icc (0 : ℝ) 1 ∧
        c j = ![(1 - a j ^ 2 / 2) / (1 + a j ^ 2 / 2), 0]) ∨
      (s j = 1 ∧ Real.pi < A j ∧ c j 0 ^ 2 + c j 1 ^ 2 < 1))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : Base → ℝ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ O ∧
      (∀ x, |h x| < ε) ∧ ∃ W : Set JetBase, IsOpen W ∧ L ⊆ W ∧
      ∃ ρ : JetBase × ℝ → ℝ, ContDiffOn ℝ ∞ ρ (W ×ˢ univ) ∧
        (∀ j ∈ W, ∀ t, 0 < ρ (j, t)) ∧
        (∀ j, Function.Periodic (fun t => ρ (j, t)) 1) ∧
        (∀ j ∈ W, (∫ t in 0..1, ρ (j, t)) = 1) ∧
        (∀ j ∈ W ∩ C, ∀ t, ρ (j, t) = unitDensity (a j) t) ∧
        ContDiffOn ℝ ∞ (jetAngle ρ a A s (fun j => h j.1)) (W ×ˢ univ) ∧
        (∀ j ∈ W, Function.Periodic (fun t => jetAngle ρ a A s (fun j => h j.1) (j, t)) 1) ∧
        (∀ j ∈ W, (∫ t in 0..1,
          ![Real.cos (jetAngle ρ a A s (fun j => h j.1) (j, t)),
            Real.sin (jetAngle ρ a A s (fun j => h j.1) (j, t))]) = c j) ∧
        (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
          deriv (fun t => jetAngle ρ a A s (fun j => h j.1) (jetSection F x, t)) θ = 0 ↔
            θ = 0 ∨ θ = PositiveDensity.clock ρ (jetSection F x) (1 / 2)) ∧
        ∀ x ∈ K,
          T < fderiv ℝ (fun y => jetAngle ρ a A s (fun j => h j.1) (jetSection F y, 0)) x (0, 1) ∧
          T < fderiv ℝ (fun y => jetAngle ρ a A s (fun j => h j.1)
            (jetSection F y, PositiveDensity.clock ρ (jetSection F x) (1 / 2))) x (0, 1) := by
  have hσ := jetSection_smooth hF
  have haσ := ha.comp hσ
  have hAσ := hA.comp hσ
  have hsσ := hs.comp hσ
  obtain ⟨δ, hδ, hdensity⟩ := small_shift_collar_density ha hA hs hc hU hC hCU hL hcollar hshape
  obtain ⟨h, hh, hhc, hhs, hhb, hlarge⟩ := exists_small_turn_function
    hK hO hKO hP hPK hlocal haσ hAσ hsσ T (lt_min hε hδ)
  let H : JetBase → ℝ := fun j => h j.1
  have hH : ContDiff ℝ ∞ H := hh.comp contDiff_fst
  have hHδ : ∀ j, |H j| < δ := fun j => lt_of_lt_of_le (hhb j.1) (min_le_right _ _)
  have hHz : ∀ j ∈ U, H j = 0 := by
    intro j hj
    by_contra hn
    exact hOU j hj (hhs (subset_tsupport h (Function.mem_support.mpr hn)))
  obtain ⟨W, hW, hLW, ρ, hρ, hpos, hper, hmom, hfixed⟩ := hdensity H hH hHδ hHz
  have hboth (j : JetBase) (hj : j ∈ W) := LoopDensity.mass_and_mean
    (LocalPeriodicCalculus.smooth_slice hW hρ hj).continuous
    ((blendedPath_smooth ha hA hs hH).continuous.comp
      (continuous_const.prodMk continuous_id)) (hmom j hj)
  have hmass : ∀ j ∈ W, (∫ t in 0..1, ρ (j, t)) = 1 := fun j hj => (hboth j hj).1
  have hα := PositiveDensity.reparametrize_smoothOn hW hρ hpos
    (fun j _ => hper j) hmass (unitAngle_smooth ha hA hs hH).contDiffOn
  let Wσ := (jetSection F) ⁻¹' W
  have hWσ : IsOpen Wσ := hW.preimage hσ.continuous
  have hKWσ : K ⊆ Wσ := fun x hx => hLW (hKL hx)
  let ρσ := PositiveDensity.pullbackDensity ρ (jetSection F)
  have hρσ : ContDiffOn ℝ ∞ ρσ (Wσ ×ˢ univ) :=
    PositiveDensity.pullbackDensity_smoothOn hρ hσ.contDiffOn (fun _ hx => hx)
  have hposσ : ∀ x ∈ Wσ, ∀ t, 0 < ρσ (x, t) := fun x hx t => hpos _ hx t
  have hperσ : ∀ x ∈ Wσ, Function.Periodic (fun t => ρσ (x, t)) 1 :=
    fun x _ => hper (jetSection F x)
  have hmassσ : ∀ x ∈ Wσ, (∫ t in 0..1, ρσ (x, t)) = 1 := fun x hx => hmass _ hx
  refine ⟨h, hh, hhc, hhs, (fun x => lt_of_lt_of_le (hhb x) (min_le_left _ _)),
    W, hW, hLW, ρ, hρ, hpos, hper, hmass, hfixed, hα, ?_, ?_, ?_, ?_⟩
  · exact fun j hj => PositiveDensity.reparametrize_periodic hW hρ hpos
      (fun j _ => hper j) hmass (fun j _ => unitAngle_periodic (a j) (A j) (s j) (H j)) hj
  · intro j hj
    exact (PositiveDensity.reparametrize_mean hW hρ hpos (fun j _ => hper j) hmass
      (blendedPath_smooth ha hA hs hH).contDiffOn hj).trans (hboth j hj).2
  · intro x hx θ hθ
    have hnotU : jetSection F x ∉ U := fun hj => hOU _ hj (hKO hx)
    have hAb : 0 < A (jetSection F x) := by
      rcases hshape _ ⟨hKL hx, hnotU⟩ with hbase | hinterior
      · exact lt_of_lt_of_le (mul_pos (by norm_num) (Real.arctan_pos.mpr hbase.1)) hbase.2.1
      · exact Real.pi_pos.trans hinterior.2.1
    have hsb : s (jetSection F x) ∈ Icc (0 : ℝ) 1 := by
      rcases hshape _ ⟨hKL hx, hnotU⟩ with hbase | hinterior
      · exact hbase.2.2.1
      · rw [hinterior.1]; exact ⟨zero_le_one, le_rfl⟩
    simpa only [jetAngle_on_section, ρσ, normalizedAngle, PositiveDensity.clock_pullback] using reparametrized_two_turns
      haσ hAσ hsσ hh hWσ hρσ hposσ hperσ hmassσ (hKWσ hx) (hapos x hx) hAb hsb hθ
  · simpa only [jetAngle_on_section, ρσ, normalizedAngle, PositiveDensity.clock_pullback] using large_turns_after_reparametrization
      haσ hAσ hsσ hh hWσ hKWσ hρσ hposσ hperσ hmassσ hlarge

end ClosedSurfaceR4.CollarVelocity

end

end OAI
