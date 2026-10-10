import OAI.Analysis.LipschitzHilbert.Phase.SourceLocalPrediction
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceStoppedError

namespace OAI

/-! Local source predictors integrate on the original line grid. The
stopping argument supplies the total error from the actual mass cutoff. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

/-- The independently constructed local predictors suffice for the whole
weighted path integral; no joint measurability of their choices is needed. -/
theorem source_local_path_integral
    (g : FiniteLineGrid) (T : SlopeBox) (K D y E : ℝ)
    (hK : 1 ≤ K) (hD : 0 ≤ D) (hwidth : g.width ≤ T.length)
    (level : ℕ → ℕ) (count : ℕ) (hlevel : ∀ j ≤ count, level j ≤ g.depth)
    (hmono : ∀ j < count, level j ≤ level (j+1))
    (good : Set ℝ) (beta error : ℕ → ℝ → ℝ) (F : ℕ → ℕ → ℝ → ℝ)
    (hF : ∀ j < count, ∀ i < g.branching^level j, ∀ x, 0 ≤ F j i x)
    (hint : ∀ j < count, ∀ i < g.branching^level j,
      Integrable (F j i) (intervalProbability
        (g.lineWindow (level j) i (level (j+1)-level j)).origin
        ((g.lineWindow (level j) i (level (j+1)-level j)).origin+
          (g.lineWindow (level j) i (level (j+1)-level j)).width)))
    (haverage : ∀ j < count, ∀ i < g.branching^level j,
      (∫ x, F j i x ∂intervalProbability
        (g.lineWindow (level j) i (level (j+1)-level j)).origin
        ((g.lineWindow (level j) i (level (j+1)-level j)).origin+
          (g.lineWindow (level j) i (level (j+1)-level j)).width)) ≤ 1)
    (hconstant : ∀ j < count, ∀ i < g.branching^level j, ∀ x z,
      (g.lineWindow (level j) i (level (j+1)-level j)).index (level (j+1)-level j) x =
        (g.lineWindow (level j) i (level (j+1)-level j)).index (level (j+1)-level j) z →
        F j i x = F j i z)
    (hcompare : ∀ j < count, ∀ i < g.branching^level j,
      ∀ x ∈ g.cell (level j) i ∩ good, beta j x ≤ Real.exp (error j x)*F j i x)
    (hbeta : ∀ x ∈ g.root ∩ good, ∀ j < count, 0 ≤ beta j x)
    (hbudget : ∀ x ∈ g.root ∩ good, (∑ j ∈ Finset.range count, error j x) ≤ E)
    (hf : AEStronglyMeasurable (good.indicator (fun x =>
      T.weight K D (x,y+T.slope*x)*∏ j ∈ Finset.range count, beta j x)) volume) :
    IntegrableOn (good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, beta j x)) g.root volume ∧
    (∫ x in g.root, good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, beta j x) x) ≤
      Real.exp E*Real.exp (2*D)*∫ x in g.root, T.weight K D (x,y+T.slope*x) := by
  classical
  have hfactor : ∀ j : ℕ, ∃ Γ : ℝ → ℝ, j < count →
      (∀ x, 0 ≤ Γ x) ∧
      (∀ x z, g.index (level (j+1)) x = g.index (level (j+1)) z → Γ x = Γ z) ∧
      (∀ i : Fin (g.branching^g.depth),
        (∫ x in {x | g.index (level j) x = i}, Γ x ∂volume.restrict g.root) ≤
          (volume.restrict g.root).real {x | g.index (level j) x = i}) ∧
      ∀ x ∈ g.root ∩ good, beta j x ≤ Real.exp (error j x)*Γ x := by
    intro j
    by_cases hj : j < count
    · obtain ⟨Γ,_,hpos,hconst,havg,hcomp⟩ := g.exists_patched_source_prediction
        (level j) (level (j+1)) (hmono j hj) (hlevel (j+1) (by omega)) good
        (beta j) (error j) (F j) (hF j hj) (hint j hj) (haverage j hj)
        (hconstant j hj) (hcompare j hj)
      exact ⟨Γ,fun _ => ⟨hpos,hconst,havg,hcomp⟩⟩
    · exact ⟨fun _ => 1,fun h => False.elim (hj h)⟩
  choose Γ hΓ using hfactor
  exact source_skipped_path_integral g T K D y E hK hD hwidth level count hlevel hmono
    good beta error Γ (fun j hj => (hΓ j hj).1) (fun j hj => (hΓ j hj).2.1)
    (fun j hj => (hΓ j hj).2.2.1) hbeta (fun x hx j hj => (hΓ j hj).2.2.2 x hx)
    hbudget hf

/-- At the source cutoff the total prediction error is at most one. Thus
all the local factors give a uniform weighted line integral. -/
theorem eventually_source_stopped_path_integral (C A_M : ℝ)
    (hC : 0 ≤ C) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (g : FiniteLineGrid) (T : SlopeBox) (K D y N : ℝ),
      1 ≤ K → 0 ≤ D → g.width ≤ T.length → 0 < N → Real.log N ≤ 2*L →
    ∀ (level : ℕ → ℕ) (count : ℕ), (∀ j ≤ count, level j ≤ g.depth) →
      (∀ j < count, level j ≤ level (j+1)) →
    ∀ (good : Set ℝ) (beta error snapshot : ℕ → ℝ → ℝ) (n : ℝ → ℕ → ℝ)
      (stop : ℝ → ℕ) (F : ℕ → ℕ → ℝ → ℝ),
    (∀ j < count, ∀ i < g.branching^level j, ∀ x, 0 ≤ F j i x) →
    (∀ j < count, ∀ i < g.branching^level j,
      Integrable (F j i) (intervalProbability
        (g.lineWindow (level j) i (level (j+1)-level j)).origin
        ((g.lineWindow (level j) i (level (j+1)-level j)).origin+
          (g.lineWindow (level j) i (level (j+1)-level j)).width))) →
    (∀ j < count, ∀ i < g.branching^level j,
      (∫ x, F j i x ∂intervalProbability
        (g.lineWindow (level j) i (level (j+1)-level j)).origin
        ((g.lineWindow (level j) i (level (j+1)-level j)).origin+
          (g.lineWindow (level j) i (level (j+1)-level j)).width)) ≤ 1) →
    (∀ j < count, ∀ i < g.branching^level j, ∀ x z,
      (g.lineWindow (level j) i (level (j+1)-level j)).index (level (j+1)-level j) x =
        (g.lineWindow (level j) i (level (j+1)-level j)).index (level (j+1)-level j) z →
        F j i x = F j i z) →
    (∀ j < count, ∀ i < g.branching^level j,
      ∀ x ∈ g.cell (level j) i ∩ good, beta j x ≤ Real.exp (error j x)*F j i x) →
    (∀ x ∈ g.root ∩ good, ∀ j < count, 0 ≤ beta j x) →
    (∀ x ∈ g.root ∩ good, stop x ≤ count ∧ n x 0 ≤ L^C*N^2 ∧
      (∀ j < stop x, L^A_M < n x j) ∧ 0 ≤ n x (stop x) ∧
      (∀ j < stop x, snapshot j x/2 ≤ pathDrop (n x) j) ∧
      ∀ j < count, error j x ≤ if j < stop x then
        SourceParameters.step L^(-(1/32:ℝ))*snapshot j x else 0) →
    AEStronglyMeasurable (good.indicator (fun x =>
      T.weight K D (x,y+T.slope*x)*∏ j ∈ Finset.range count, beta j x)) volume →
    IntegrableOn (good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, beta j x)) g.root volume ∧
    (∫ x in g.root, good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, beta j x) x) ≤
      Real.exp 1*Real.exp (2*D)*∫ x in g.root, T.weight K D (x,y+T.slope*x) := by
  filter_upwards [eventually_source_snapshot_stopped_error C A_M hC hAM] with L hL
  intro g T K D y N hK hD hwidth hN hlog level count hlevel hmono good beta error
    snapshot n stop F hF hint havg hconstant hcompare hbeta hstop hf
  apply source_local_path_integral g T K D y 1 hK hD hwidth level count hlevel hmono
    good beta error F hF hint havg hconstant hcompare hbeta _ hf
  intro x hx
  obtain ⟨hsc,hmass,hactive,hlast,hdrop,he⟩ := hstop x hx
  exact hL (n x) (fun j => error j x) (fun j => snapshot j x) count (stop x) hsc
    N hN hlog hmass hactive hlast hdrop he

end LipschitzHilbert

end

end OAI
