import OAI.Analysis.LipschitzHilbert.Trees.SourceMarkedIntegral

namespace OAI

/-! Integrate the already patched source factors. Their normalizations
are exact, while the forward mass path pays the pointwise marked errors. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem source_marked_factors_integral
    (g : FiniteLineGrid) (T : SlopeBox) (K D y E : ℝ)
    (hK : 1 ≤ K) (hD : 0 ≤ D) (hwidth : g.width ≤ T.length)
    (level : ℕ → ℕ) (count : ℕ) (hlevel : ∀ k ≤ count, level k ≤ g.depth)
    (hmono : ∀ k < count, level k ≤ level (k+1))
    (good : Set ℝ) (marked : ℕ → ℕ → Prop) (beta error Γ : ℕ → ℝ → ℝ)
    (hΓ : ∀ j < count, ∀ x, 0 ≤ Γ j x)
    (hconst : ∀ j < count, ∀ x z,
      g.index (level (ShiftedBlocks.reverseIndex count j+1)) x =
        g.index (level (ShiftedBlocks.reverseIndex count j+1)) z → Γ j x = Γ j z)
    (havg : ∀ j < count, ∀ i : Fin (g.branching^g.depth),
      (∫ x in {x | g.index (level (ShiftedBlocks.reverseIndex count j)) x = i},
        Γ j x ∂volume.restrict g.root) ≤
        (volume.restrict g.root).real {x | g.index (level (ShiftedBlocks.reverseIndex count j)) x = i})
    (hbeta : ∀ x ∈ g.root ∩ good, ∀ j < count, 0 ≤ beta j x)
    (hcompare : ∀ x ∈ g.root ∩ good, ∀ j < count,
      reverseMarkedValue g level count marked beta j x ≤
        Real.exp (reverseMarkedError g level count marked error j x)*Γ j x)
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
  let B := reverseMarkedValue g level count marked beta
  let e := reverseMarkedError g level count marked error
  have hprod (x : ℝ) := ShiftedBlocks.prod_reverseIndex (fun j => B j x) count
  have hsum (x : ℝ) := ShiftedBlocks.sum_reverseIndex (fun j => e j x) count
  have hf' : AEStronglyMeasurable (good.indicator (fun x => T.weight K D (x,y+T.slope*x)*
      ∏ j ∈ Finset.range count, B (ShiftedBlocks.reverseIndex count j) x)) volume := by
    simpa only [hprod] using hf
  have hi := source_skipped_path_integral g T K D y E hK hD hwidth level count hlevel hmono
    good (fun k => B (ShiftedBlocks.reverseIndex count k))
    (fun k => e (ShiftedBlocks.reverseIndex count k))
    (fun k => Γ (ShiftedBlocks.reverseIndex count k))
    (fun k hk => hΓ _ (ShiftedBlocks.reverseIndex_lt hk))
    (fun k hk => by
      simpa only [ShiftedBlocks.reverseIndex_involutive hk] using
        hconst _ (ShiftedBlocks.reverseIndex_lt hk))
    (fun k hk => by
      simpa only [ShiftedBlocks.reverseIndex_involutive hk] using
        havg _ (ShiftedBlocks.reverseIndex_lt hk))
    (fun x hx k hk => by
      dsimp only [B,reverseMarkedValue,FiniteLineGrid.markedValue]
      split_ifs
      · exact hbeta x hx _ (ShiftedBlocks.reverseIndex_lt hk)
      · norm_num)
    (fun x hx k hk => hcompare x hx _ (ShiftedBlocks.reverseIndex_lt hk))
    (fun x hx => by simpa only [hsum] using hbudget x hx) hf'
  simpa only [hprod] using hi

/-- Actual pointwise drops can pay the doubled snapshot error. -/
theorem eventually_source_marked_drop_budget (C A_M : ℝ)
    (hC : 0 ≤ C) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ → ℝ) (count : ℕ) (marked : ℕ → Prop),
      ∀ N : ℝ, 0 < N → Real.log N ≤ 2*L → n 0 ≤ L^C*N^2 →
        (∀ j, 0 ≤ n j) → Antitone n → n count ≤ L^A_M →
        (∀ j < count, marked j → L^A_M < n j) →
        (∑ j ∈ Finset.range count, if marked j then
          (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop n j else 0) ≤ 1 := by
  filter_upwards [eventually_source_marked_error C A_M hC hAM] with L hL
  intro n count marked N hN hlog hmass hn hanti hlast hmarked
  apply hL n (fun j => (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop n j)
    (fun j => 2*pathDrop n j) count marked N hN hlog hmass hn hanti hlast hmarked
  · intro j hj hm
    linarith
  · intro j hj hm
    exact le_of_eq (by ring)

end LipschitzHilbert

end

end OAI
