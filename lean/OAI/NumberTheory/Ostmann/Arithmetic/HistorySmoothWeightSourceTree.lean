import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSmooth
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceLeaf

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistoryOccurrenceVariables
open InitialCoordinatesTemplate
variable {ι : Type*}

theorem encode_norm_le_sourceRanges (b s k : ℕ) (X tb td G Δ E : ℝ) (center : ℕ → ℝ)
    (outside : List ℕ) (slot : ι → Option SmallSlot) (x : ι → ℝ)
    (hX : 0 < X) (hx : ∀ i, 0 < x i) (houtside : ∀ q ∈ outside, 0 < q)
    (hout : outside.length = 2*s) (hsource : IndependentSourceCells slot center x)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ i,topCenters b center h i)+
      (∑ h,∑ j : Fin k,∑ i,compensationCenters b center h j i))
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside)
    (hleaf : ∀ a ∈ h.leafStates, Template.Matches (Template.initial (2*b) k) a.small)
    (e : StateExpr h.root ι) (comp : InternalKey h → Expr ι)
    (he : StateAtomSlots slot e)
    (hc : ∀ i, ∃ j, comp i = .atom j ∧ slot j = some (internalSlot h i))
    (hp : 0 < e.plus.realEval x) (hm : 0 < e.minus.realEval x)
    (hgp : |Real.log (e.plus.realEval x)-G| ≤ 1)
    (hgm : |Real.log (e.minus.realEval x)-G| ≤ 1) :
    ‖realHistoryScalar b s X tb td G outside x h (encode V outside h hs e comp)‖ ≤
      (sourceLeafAmplitude k Δ E)^(2^l) := by
  induction h with
  | leaf a =>
    change ‖e.realScalar b s X tb td outside x‖ ≤ (sourceLeafAmplitude k Δ E)^(2^0)
    rw [pow_zero, pow_one]
    exact e.realScalar_norm_le_sourceRanges b s k X tb td G Δ E center outside slot x hX hx houtside hout
      (hleaf a (by simp only [History.leafStates,List.mem_singleton])) he hsource hp hm hgp hgm hcenter
  | @node l a p u hplus hminus left right ihl ihr =>
    let c := fun i => comp (Sum.inl i)
    let P := (pivotExpr hs e c).realEval x
    have hu : AtomSlotsCorrect slot u c := by
      intro i
      simpa only [internalSlot,Sum.elim_inl,c] using hc (Sum.inl i)
    have hchildren := children_atomSlots slot hs e c he hu
    have hleft : ∀ a ∈ left.leafStates, Template.Matches (Template.initial (2*b) k) a.small :=
      fun a ha => hleaf a (by simp only [History.leafStates,List.mem_append]; exact Or.inl ha)
    have hright : ∀ a ∈ right.leafStates, Template.Matches (Template.initial (2*b) k) a.small :=
      fun a ha => hleaf a (by simp only [History.leafStates,List.mem_append]; exact Or.inr ha)
    have hcl : ∀ i, ∃ j, comp (Sum.inr (Sum.inl i)) = .atom j ∧ slot j = some (internalSlot left i) := by
      intro i
      simpa only [internalSlot,Sum.elim_inr,Sum.elim_inl] using hc (Sum.inr (Sum.inl i))
    have hcr : ∀ i, ∃ j, comp (Sum.inr (Sum.inr i)) = .atom j ∧ slot j = some (internalSlot right i) := by
      intro i
      simpa only [internalSlot,Sum.elim_inr] using hc (Sum.inr (Sum.inr i))
    simp only [encode,realHistoryScalar,treeRoot_encode]
    change ‖(giantCell G P:ℂ) *
      realHistoryScalar b s X tb td G outside x left
        (encode V outside left (History.supported_left hs) (leftState hs e c) (fun i => comp (Sum.inr (Sum.inl i)))) *
      star (realHistoryScalar b s X tb td G outside x right
        (encode V outside right (History.supported_right hs) (rightState hs e c) (fun i => comp (Sum.inr (Sum.inr i)))))‖ ≤ _
    by_cases hzero : giantCell G P = 0
    · simp only [hzero,Complex.ofReal_zero,zero_mul,norm_zero]
      exact pow_nonneg (sourceLeafAmplitude_pos k Δ E).le _
    · obtain ⟨hP,hPG⟩ := giantCell_ne_zero_support G P hzero
      have hl := ihl (History.supported_left hs) hleft (leftState hs e c) _ hchildren.1 hcl hP hp hPG hgp
      have hr := ihr (History.supported_right hs) hright (rightState hs e c) _ hchildren.2 hcr hP hm hPG hgm
      have hcut := giantCell_bounds G P
      rw [norm_mul,norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hcut.1]
      calc
        _ ≤ (1 * (sourceLeafAmplitude k Δ E)^(2^l)) * (sourceLeafAmplitude k Δ E)^(2^l) :=
          mul_le_mul (mul_le_mul hcut.2 hl (norm_nonneg _) zero_le_one) hr (norm_nonneg _)
            (mul_nonneg zero_le_one (pow_nonneg (sourceLeafAmplitude_pos k Δ E).le _))
        _ = _ := by
          rw [one_mul,← pow_add,pow_succ]
          congr 1
          omega

theorem actualRealHistoryScalar_norm_le_sourceRanges (b s k : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (outside : List ℕ)
    (hX : 0 < X) (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length=2*s)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside)
    (hleaf : ∀ a ∈ h.leafStates, Template.Matches (Template.initial (2*b) k) a.small)
    (x : Key h → ℝ) (hx : ∀ i, 0 < x i)
    (hsource : IndependentSourceCells (independentSlot h) center x)
    (hgiant : ∀ j : Bool, |Real.log (x (Sum.inl j))-G| ≤ 1)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ i,topCenters b center h i)+
      (∑ h,∑ j : Fin k,∑ i,compensationCenters b center h j i)) :
    ‖actualRealHistoryScalar b s X tb td G outside h hs x‖ ≤
      (sourceLeafAmplitude k Δ E)^(2^l) :=
  encode_norm_le_sourceRanges b s k X tb td G Δ E center outside (independentSlot h) x hX hx houtside hout
    hsource hcenter h hs hleaf (rootExpr h) (compensationExpr h)
    (fun i => ⟨Sum.inr (Sum.inl i),rfl,rfl⟩) (fun i => ⟨Sum.inr (Sum.inr i),rfl,rfl⟩)
    (hx _) (hx _) (hgiant false) (hgiant true)

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
