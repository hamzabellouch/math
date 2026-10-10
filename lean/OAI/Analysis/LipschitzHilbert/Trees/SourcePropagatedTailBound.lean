import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualPropagation
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualWeightBudget

namespace OAI

/-! The actual propagated residual tail has one fixed polynomial loss.
This estimate uses the full-root mass bound, including for later starts. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

theorem intervalOscillation_le_of_subinterval {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (H a b c d : ℕ) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hb : b ≤ H) : intervalOscillation F H c d ≤ intervalOscillation F H a b := by
  obtain ⟨u,v,hcu,huv,hvd,heq⟩ := exists_intervalOscillation_eq F H c d hcd
  rw [heq]
  exact increment_le_intervalOscillation F H a b u v (hac.trans hcu) huv (hvd.trans hdb) hb

namespace AngularGrid

theorem eventually_source_propagated_tail_bound (Cmass : ℝ) (hCmass : 0 ≤ Cmass) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ σ X E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
      (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
      (weight : τ → X → ℝ), (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
    ∀ (K : ℕ), 0 < K → (K:ℝ) ≤ L^2 →
    ∀ (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : σ → E) (phase : ℕ → ℂ) (a Z Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (x : X) (level : ℕ → ℕ), StrictMono level →
    ∀ (count : ℕ) (top : τ), top ∈ tops →
    ∀ (e f H : ℕ), e < f → f ≤ count → level f ≤ H →
      g.eligible cutoff (precision top) (level f) →
      1 ≤ g.mass tops slope precision cutoff weight (level f) (g.index (level f) (slope top)) x →
      g.mass tops slope precision cutoff weight 0 (g.index 0 (slope top)) x ≤ L^Cmass*Nmass →
      (∀ k < level f, 0 ≤ (phase k).re) → (∀ k < level f, ‖phase k‖ ≤ Z) →
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x
    let Q := g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope top)
    let raw := fun k => ∑ q ∈ Q.filter (fun q => stop q = k), value q
    ∀ j ∈ Finset.Icc e f,
      ‖∑ k ∈ Finset.Ico j f,
        unaryPropagator (fun b => g.packetPathProduct transition (level b) (level (b+1)) (slope top)) j k •
          g.packetResidual (g.sourceContinuingPackets tops slope precision cutoff packets assigned
            (level (k+1)) (slope top)) (fun q => slope (assigned q)) stop base transition
            (level k) (level (k+1)) (g.index (level k) (slope top))‖ ≤
        L^6*intervalOscillation (packetPrefix raw) H (level e) (level f) := by
  filter_upwards [eventually_source_residual_weight_budget Cmass hCmass] with L hbudget
  intro τ σ X E _ _ g tops slope precision cutoff weight hp hw K hK hKL gap packets
    assigned stop value phase a Z Nmass ha0 ha1 hZ0 hZ hN hlogN x level hlevel count top
    htop e f H hef hfc hH he hnend hnroot hz0 hz
  dsimp only
  intro j hj
  have hji := Finset.mem_Icc.mp hj
  let Q := g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope top)
  let raw := fun k => ∑ q ∈ Q.filter (fun q => stop q = k), value q
  have hnonneg : 0 ≤ L^6*intervalOscillation (packetPrefix raw) H (level e) (level f) :=
    mul_nonneg (by positivity) (intervalOscillation_nonneg ..)
  by_cases hjf : j = f
  · subst j
    simpa only [Finset.Ico_self,Finset.sum_empty,norm_zero] using hnonneg
  · have hjlt : j < f := lt_of_le_of_ne hji.2 hjf
    have hb := g.source_propagated_residual_bound tops slope precision cutoff weight hp hw hK gap
      packets assigned stop value phase a x level hlevel count top htop hjlt hfc he H hH
      ha0 (by norm_num : (0:ℝ)<1) hZ0 hnend hz0 hz
    have hn0 : 1 ≤ g.mass tops slope precision cutoff weight 0 (g.index 0 (slope top)) x :=
      hnend.trans (g.path_mass_antitone tops slope precision cutoff weight hp
        (fun t x => (hw t x).le) top x (Nat.zero_le _))
    have hnum := hbudget a Z Nmass
      (g.mass tops slope precision cutoff weight 0 (g.index 0 (slope top)) x) K
      ha0 ha1 hZ0 hZ hKL hN hlogN hn0 hnroot
    simp only [Real.one_rpow,one_mul,div_one] at hb
    apply hb.trans
    apply mul_le_mul hnum
      (intervalOscillation_le_of_subinterval (packetPrefix raw) H (level e) (level f)
        (level j) (level f) (hlevel.monotone hji.1) (hlevel.monotone hji.2) le_rfl hH)
      (intervalOscillation_nonneg ..) (by positivity)

end AngularGrid
end LipschitzHilbert

end

end OAI
