import OAI.Probability.FreeIsing.Estimates.PairCorrelation
import OAI.Probability.FreeIsing.Estimates.SeparatedLocalSupports
import OAI.Probability.FreeIsing.Estimates.TwoSeparatorRegression
import OAI.Probability.FreeIsing.Trees.FreeLawConeMarkov

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367
open RootedBroadcast

local instance freeLawLocalCovarianceMeasurableSingletonSpin : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩

theorem HasFreeIsingLaw.abs_correlation_separated_cones {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (b c : TreeVertex d) (hb : b.val ≠ []) (hbc : b.val <+: c.val)
    (F : (OutsideConeVertex b → IsingSpin) → ℝ)
    (G : (DescendantVertex c → IsingSpin) → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hFzero : ∫ x, F (fun v => x v.val) ∂μ = 0)
    (hGzero : ∫ x, G (fun v => x v.val) ∂μ = 0)
    (hF2 : MemLp (fun x => F (fun v => x v.val)) 2 μ)
    (hG2 : MemLp (fun x => G (fun v => x v.val)) 2 μ) :
    |∫ x, F (fun v => x v.val) * G (fun v => x v.val) ∂μ| ≤
      Real.sqrt (∫ x, (F (fun v => x v.val))^2 ∂μ) *
        Real.sqrt (∫ x, (G (fun v => x v.val))^2 ∂μ) *
          theta ^ reducedWordDistance (parent b).val c.val := by
  have hm : -1 ≤ theta := by linarith
  have hc : c.val ≠ [] := by
    intro h
    exact hb (List.prefix_nil.mp (h ▸ hbc))
  have hac : ¬ c.val <+: (parent b).val := by
    intro h
    have hl := (hbc.trans h).length_le
    change b.val.length ≤ (parentVertex b).val.length at hl
    rw [parentVertex_length] at hl
    have hp := List.length_pos_iff.mpr hb
    omega
  let R : (DescendantVertex b → IsingSpin) → (DescendantVertex c → IsingSpin) :=
    fun z v => z ⟨v.val, hbc.trans v.property⟩
  have hR : Measurable R := by fun_prop
  have hleft := (hμ.condIndepFun_outside_cone_given_parent hm h1 b hb).comp
    hF (hG.comp hR)
  have hright := (hμ.condIndepFun_outside_cone_given_child hm h1 c hc).comp
    (measurable_pi_apply (⟨parent b, hac⟩ : OutsideConeVertex c)) hG
  have hbound := BinaryRegression.abs_correlation_le_of_two_separators
    (measurable_pi_apply (parent b)) (measurable_pi_apply c)
    (hμ.marginal (parent b)) (hμ.marginal c)
    (hF.comp (Measurable.of_eval (fun vertex => measurable_pi_apply vertex.val)))
    (hG.comp (Measurable.of_eval (fun vertex => measurable_pi_apply vertex.val)))
    hFzero hGzero hF2 hG2 hleft hright
  rw [hμ.pair_correlation hm h1, abs_of_nonneg (pow_nonneg h0 _)] at hbound
  exact hbound

theorem reducedWordDistance_append_prefix {α : Type*} [DecidableEq α]
    (u w : List α) : reducedWordDistance u (u ++ w) = w.length := by
  induction u with
  | nil => rfl
  | cons a u ih => simpa only [List.cons_append, reducedWordDistance_cons_same] using ih

theorem HasFreeIsingLaw.abs_correlation_separated_local_blocks
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ] (hμ : HasFreeIsingLaw theta μ)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {I J : Type*} (u : I → TreeVertex d) (v : J → TreeVertex d)
    (R : ℕ) (hu : ∀ i, (u i).val.length ≤ R) (hv : ∀ j, (v j).val.length ≤ R)
    (g : TreeAut d) (hsep : R + R < (g.toEquiv TreeEscape.root).val.length)
    (F : (I → IsingSpin) → ℝ) (G : (J → IsingSpin) → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hFzero : ∫ x, F (fun i => x (u i)) ∂μ = 0)
    (hGzero : ∫ x, G (fun j => x (g.toEquiv (v j))) ∂μ = 0)
    (hF2 : MemLp (fun x => F (fun i => x (u i))) 2 μ)
    (hG2 : MemLp (fun x => G (fun j => x (g.toEquiv (v j)))) 2 μ) :
    |∫ x, F (fun i => x (u i)) * G (fun j => x (g.toEquiv (v j))) ∂μ| ≤
      Real.sqrt (∫ x, (F (fun i => x (u i)))^2 ∂μ) *
        Real.sqrt (∫ x, (G (fun j => x (g.toEquiv (v j))))^2 ∂μ) *
          theta ^ ((g.toEquiv TreeEscape.root).val.length - (R + R)) := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hleft, hright, middle, hmiddle, hlen⟩ :=
    LocalSupportGeometry.separated_ball_endpoints g R hsep
  have hbnil : b.val ≠ [] := by
    intro hn
    simp only [hn, List.length_nil] at hb
    omega
  have hparent : parent b = a := treeAdj_parent_of_length_lt hab (by omega)
  let FF : (OutsideConeVertex b → IsingSpin) → ℝ :=
    fun z => F (fun i => z ⟨u i, hleft (u i) (hu i)⟩)
  let GG : (DescendantVertex c → IsingSpin) → ℝ :=
    fun z => G (fun j => z ⟨g.toEquiv (v j), hright (v j) (hv j)⟩)
  have hFF : Measurable FF := hF.comp (by fun_prop)
  have hGG : Measurable GG := hG.comp (by fun_prop)
  have h := hμ.abs_correlation_separated_cones h0 h1 b c hbnil hbc FF GG hFF hGG
    hFzero hGzero hF2 hG2
  have hdist : reducedWordDistance (parent b).val c.val =
      (g.toEquiv TreeEscape.root).val.length - (R + R) := by
    rw [hparent, hmiddle, reducedWordDistance_append_prefix, hlen]
  rw [hdist] at h
  exact h

end Problem367

end

end OAI
