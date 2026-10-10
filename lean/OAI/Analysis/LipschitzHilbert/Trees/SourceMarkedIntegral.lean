import OAI.Analysis.LipschitzHilbert.Phase.SourceMarkedPrediction
import OAI.Analysis.LipschitzHilbert.Trees.SourceReverseBlocks

namespace OAI

/-! Marked predictors are patched cellwise, then integrated in reverse
geometric order. Their logarithmic errors are summed in the original
forward angular order and paid by the actual first mass crossing. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def reverseMarkedValue (g : FiniteLineGrid) (level : ℕ → ℕ) (count : ℕ)
    (marked : ℕ → ℕ → Prop) (value : ℕ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  g.markedValue (level (ShiftedBlocks.reverseIndex count j)) (marked j) (value j)

def reverseMarkedError (g : FiniteLineGrid) (level : ℕ → ℕ) (count : ℕ)
    (marked : ℕ → ℕ → Prop) (error : ℕ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  g.markedError (level (ShiftedBlocks.reverseIndex count j)) (marked j) (error j)

/-- The geometric hypotheses concern increasing line levels. The local
predictors, original factors, and error budget remain in forward path order. -/
theorem source_marked_path_integral
    (g : FiniteLineGrid) (T : SlopeBox) (K D y E : ℝ)
    (hK : 1 ≤ K) (hD : 0 ≤ D) (hwidth : g.width ≤ T.length)
    (level : ℕ → ℕ) (count : ℕ) (hlevel : ∀ k ≤ count, level k ≤ g.depth)
    (hmono : ∀ k < count, level k ≤ level (k+1))
    (good : Set ℝ) (marked : ℕ → ℕ → Prop) (beta error : ℕ → ℝ → ℝ)
    (F : ℕ → ℕ → ℝ → ℝ)
    (hF : ∀ j < count, ∀ i < g.branching^level (ShiftedBlocks.reverseIndex count j),
      marked j i → ∀ x, 0 ≤ F j i x)
    (hint : ∀ j < count, ∀ i < g.branching^level (ShiftedBlocks.reverseIndex count j),
      marked j i → Integrable (F j i) (intervalProbability
        (g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).origin
        ((g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).origin+
        (g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).width)))
    (haverage : ∀ j < count, ∀ i < g.branching^level (ShiftedBlocks.reverseIndex count j),
      marked j i → (∫ x, F j i x ∂intervalProbability
        (g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).origin
        ((g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).origin+
        (g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).width)) ≤ 1)
    (hconstant : ∀ j < count, ∀ i < g.branching^level (ShiftedBlocks.reverseIndex count j),
      marked j i → ∀ x z,
      (g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).index
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j)) x =
        (g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).index
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j)) z →
        F j i x = F j i z)
    (hcompare : ∀ j < count, ∀ i < g.branching^level (ShiftedBlocks.reverseIndex count j),
      marked j i → ∀ x ∈ g.cell (level (ShiftedBlocks.reverseIndex count j)) i ∩ good,
        beta j x ≤ Real.exp (error j x)*F j i x)
    (hbeta : ∀ x ∈ g.root ∩ good, ∀ j < count, 0 ≤ beta j x)
    (hbudget : ∀ x ∈ g.root ∩ good,
      (∑ j ∈ Finset.range count, reverseMarkedError g level count marked error j x) ≤ E)
    (hf : AEStronglyMeasurable (good.indicator (fun x =>
      T.weight K D (x,y+T.slope*x)*
        ∏ j ∈ Finset.range count, reverseMarkedValue g level count marked beta j x)) volume) :
    IntegrableOn (good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue g level count marked beta j x)) g.root volume ∧
    (∫ x in g.root, good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue g level count marked beta j x) x) ≤
      Real.exp E*Real.exp (2*D)*∫ x in g.root, T.weight K D (x,y+T.slope*x) := by
  have hfactor : ∀ j : ℕ, ∃ Γ : ℝ → ℝ, j < count →
      (∀ x, 0 ≤ Γ x) ∧
      (∀ x z, g.index (level (ShiftedBlocks.reverseIndex count j+1)) x =
        g.index (level (ShiftedBlocks.reverseIndex count j+1)) z → Γ x = Γ z) ∧
      (∀ i : Fin (g.branching^g.depth),
        (∫ x in {x | g.index (level (ShiftedBlocks.reverseIndex count j)) x = i},
          Γ x ∂volume.restrict g.root) ≤
          (volume.restrict g.root).real {x | g.index (level (ShiftedBlocks.reverseIndex count j)) x = i}) ∧
      ∀ x ∈ g.root ∩ good, reverseMarkedValue g level count marked beta j x ≤
        Real.exp (reverseMarkedError g level count marked error j x)*Γ x := by
    intro j
    by_cases hj : j < count
    · have hr := ShiftedBlocks.reverseIndex_lt hj
      obtain ⟨Γ,_,hpos,hconst,havg,_,hcomp⟩ := g.exists_marked_source_prediction
        (level (ShiftedBlocks.reverseIndex count j))
        (level (ShiftedBlocks.reverseIndex count j+1)) (hmono _ hr)
        (hlevel _ (by omega)) (marked j) good (beta j) (error j) (F j)
        (hF j hj) (hint j hj) (haverage j hj) (hconstant j hj) (hcompare j hj)
      exact ⟨Γ,fun _ => ⟨hpos,hconst,havg,hcomp⟩⟩
    · exact ⟨fun _ => 1,fun h => False.elim (hj h)⟩
  choose Γ hΓ using hfactor
  let B := reverseMarkedValue g level count marked beta
  let e := reverseMarkedError g level count marked error
  have hprod (x : ℝ) := ShiftedBlocks.prod_reverseIndex (fun j => B j x) count
  have hsum (x : ℝ) := ShiftedBlocks.sum_reverseIndex (fun j => e j x) count
  have hf' : AEStronglyMeasurable (good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, B (ShiftedBlocks.reverseIndex count j) x)) volume := by
    simpa only [hprod] using hf
  have hresult := source_skipped_path_integral g T K D y E hK hD hwidth level count hlevel hmono
    good (fun k => B (ShiftedBlocks.reverseIndex count k))
    (fun k => e (ShiftedBlocks.reverseIndex count k))
    (fun k => Γ (ShiftedBlocks.reverseIndex count k))
    (fun k hk => (hΓ _ (ShiftedBlocks.reverseIndex_lt hk)).1)
    (fun k hk => by
      simpa only [ShiftedBlocks.reverseIndex_involutive hk] using
        (hΓ _ (ShiftedBlocks.reverseIndex_lt hk)).2.1)
    (fun k hk => by
      simpa only [ShiftedBlocks.reverseIndex_involutive hk] using
        (hΓ _ (ShiftedBlocks.reverseIndex_lt hk)).2.2.1)
    (fun x hx k hk => by
      dsimp only [B,reverseMarkedValue,FiniteLineGrid.markedValue]
      split_ifs
      · exact hbeta x hx _ (ShiftedBlocks.reverseIndex_lt hk)
      · norm_num)
    (fun x hx k hk => (hΓ _ (ShiftedBlocks.reverseIndex_lt hk)).2.2.2 x hx)
    (fun x hx => by simpa only [hsum] using hbudget x hx) hf'
  simpa only [hprod] using hresult


/-- The actual first mass crossing pays the error of every marked factor.
The product is still written in forward angular order. -/
theorem eventually_source_marked_path_integral (C A_M : ℝ)
    (hC : 0 ≤ C) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (g : FiniteLineGrid) (T : SlopeBox) (K D y N : ℝ)
    (_hK : 1 ≤ K) (_hD : 0 ≤ D) (_hwidth : g.width ≤ T.length)
    (_hN : 0 < N) (_hlog : Real.log N ≤ 2*L)
    (level : ℕ → ℕ) (count : ℕ) (_hlevel : ∀ k ≤ count, level k ≤ g.depth)
    (_hmono : ∀ k < count, level k ≤ level (k+1))
    (good : Set ℝ) (marked : ℕ → ℕ → Prop) (beta error : ℕ → ℝ → ℝ)
    (F : ℕ → ℕ → ℝ → ℝ)
    (_hF : ∀ j < count, ∀ i < g.branching^level (ShiftedBlocks.reverseIndex count j),
      marked j i → ∀ x, 0 ≤ F j i x)
    (_hint : ∀ j < count, ∀ i < g.branching^level (ShiftedBlocks.reverseIndex count j),
      marked j i → Integrable (F j i) (intervalProbability
        (g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).origin
        ((g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).origin+
        (g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).width)))
    (_haverage : ∀ j < count, ∀ i < g.branching^level (ShiftedBlocks.reverseIndex count j),
      marked j i → (∫ x, F j i x ∂intervalProbability
        (g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).origin
        ((g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).origin+
        (g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).width)) ≤ 1)
    (_hconstant : ∀ j < count, ∀ i < g.branching^level (ShiftedBlocks.reverseIndex count j),
      marked j i → ∀ x z,
      (g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).index
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j)) x =
        (g.lineWindow (level (ShiftedBlocks.reverseIndex count j)) i
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j))).index
          (level (ShiftedBlocks.reverseIndex count j+1)-level (ShiftedBlocks.reverseIndex count j)) z →
        F j i x = F j i z)
    (_hcompare : ∀ j < count, ∀ i < g.branching^level (ShiftedBlocks.reverseIndex count j),
      marked j i → ∀ x ∈ g.cell (level (ShiftedBlocks.reverseIndex count j)) i ∩ good,
        beta j x ≤ Real.exp (error j x)*F j i x)
    (_hbeta : ∀ x ∈ g.root ∩ good, ∀ j < count, 0 ≤ beta j x)
    (n : ℝ → ℕ → ℝ) (snapshot : ℕ → ℝ → ℝ)
    (_hmass : ∀ x ∈ g.root ∩ good, n x 0 ≤ L^C*N^2)
    (_hn : ∀ x ∈ g.root ∩ good, ∀ j, 0 ≤ n x j)
    (_hanti : ∀ x ∈ g.root ∩ good, Antitone (n x))
    (_hlast : ∀ x ∈ g.root ∩ good, n x count ≤ L^A_M)
    (_hmarked : ∀ x ∈ g.root ∩ good, ∀ j < count,
      marked j (g.index (level (ShiftedBlocks.reverseIndex count j)) x).val → L^A_M < n x j)
    (_hdrop : ∀ x ∈ g.root ∩ good, ∀ j < count,
      marked j (g.index (level (ShiftedBlocks.reverseIndex count j)) x).val →
        snapshot j x/2 ≤ pathDrop (n x) j)
    (_herror : ∀ x ∈ g.root ∩ good, ∀ j < count,
      marked j (g.index (level (ShiftedBlocks.reverseIndex count j)) x).val →
        error j x ≤ SourceParameters.step L^(-(1/32:ℝ))*snapshot j x)
    (_hf : AEStronglyMeasurable (good.indicator (fun x =>
      T.weight K D (x,y+T.slope*x)*
        ∏ j ∈ Finset.range count, reverseMarkedValue g level count marked beta j x)) volume),
    IntegrableOn (good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue g level count marked beta j x)) g.root volume ∧
    (∫ x in g.root, good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue g level count marked beta j x) x) ≤
      Real.exp 1*Real.exp (2*D)*∫ x in g.root, T.weight K D (x,y+T.slope*x) := by
  filter_upwards [eventually_source_marked_error C A_M hC hAM] with L hL
  intro g T K D y N hK hD hwidth hN hlog level count hlevel hmono
    good marked beta error F hF hint havg hconstant hcompare hbeta n snapshot
    hmass hn hanti hlast hmarked hdrop herror hf
  apply source_marked_path_integral g T K D y 1 hK hD hwidth level count hlevel hmono
    good marked beta error F hF hint havg hconstant hcompare hbeta _ hf
  intro x hx
  simpa only [reverseMarkedError,FiniteLineGrid.markedError] using
    hL (n x) (fun j => error j x) (fun j => snapshot j x) count
      (fun j => marked j (g.index (level (ShiftedBlocks.reverseIndex count j)) x).val)
      N hN hlog (hmass x hx) (hn x hx) (hanti x hx) (hlast x hx)
      (hmarked x hx) (hdrop x hx) (herror x hx)

end LipschitzHilbert

end

end OAI
