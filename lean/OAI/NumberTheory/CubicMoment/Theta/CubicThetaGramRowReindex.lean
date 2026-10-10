import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanPeriodization
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramRowSupport

namespace OAI

/-! The actual nonidentity Poincare rows reindexed by their two Eisenstein
entries, with the inadmissible pairs extended by zero. -/
noncomputable section
open Set
open scoped CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaGramRowLift (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    (p : ℂ × ℝ) (x : Eisenstein × Eisenstein) : ℂ :=
  if hc : (3:Eisenstein)∣x.1 ∧ x.1≠0 then
    cubicThetaKloostermanWeight h k x.1 hc.1 x.2*
      cubicThetaGramInversionKernel h k V (x.1:ℂ) (p.1+(x.2:ℂ)/(x.1:ℂ)) p.2
  else 0

lemma cubicThetaGramRowLift_row (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    (r : CubicThetaBottomRow) (hr : r.c≠0) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaGramRowLift h k V p (r.c,r.d)=
      star (cubicThetaHorizontalCharacter h p.1)*cubicThetaFourierProfileTerm k r p V := by
  have hc : (3:Eisenstein)∣r.c ∧ r.c≠0 := ⟨r.c_three,hr⟩
  have hd : primary r.d ∧ IsCoprime r.c r.d := ⟨r.d_primary,r.coprime⟩
  simp only [cubicThetaGramRowLift,dite_eq_left hc,
    cubicThetaKloostermanWeight,dite_eq_left hd]
  exact (cubicThetaGramRowKernel_identity h k r hr V hp).symm

lemma cubicThetaPositiveFourierProfileTerm_summable (k : Eisenstein) (V : C_c(ℝ,ℂ))
    {δ : ℝ} (hδ : 0<δ) (hV : ∀ t≤δ,V t=0) {p : ℂ × ℝ} (hp : 0<p.2) :
    Summable (fun r : CubicThetaBottomRow => cubicThetaFourierProfileTerm k r p V) := by
  obtain ⟨S,hS⟩ := cubicThetaRows_compact_below hδ (isCompact_singleton (x:=p))
    (by intro q hq; simpa only [mem_singleton_iff.mp hq] using hp)
  apply summable_of_ne_finset_zero (s:=S)
  intro r hr
  exact cubicThetaFourierProfileTerm_zero k r p V (hV _ (hS p (mem_singleton p) r hr).le)

lemma cubicThetaGramRowLift_hasSum (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    {δ : ℝ} (hδ : 0<δ) (hV : ∀ t≤δ,V t=0) {p : ℂ × ℝ} (hp : 0<p.2) :
    HasSum (cubicThetaGramRowLift h k V p)
      (∑' r : CubicThetaBottomRow,if r=cubicThetaZeroRow then 0 else
        star (cubicThetaHorizontalCharacter h p.1)*cubicThetaFourierProfileTerm k r p V) := by
  classical
  let G : CubicThetaBottomRow → ℂ := fun r => if r=cubicThetaZeroRow then 0 else
    star (cubicThetaHorizontalCharacter h p.1)*cubicThetaFourierProfileTerm k r p V
  let i : Function.support G → Eisenstein × Eisenstein := fun r => (r.1.c,r.1.d)
  have hi : Function.Injective i := by
    intro r s he
    apply Subtype.ext
    exact CubicThetaBottomRow.ext (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hm (r : Function.support G) : cubicThetaGramRowLift h k V p (i r)=G r := by
    have hr0 : r.val≠cubicThetaZeroRow := by
      intro he
      exact r.property (by simp [G,he])
    have hr : r.val.c≠0 := fun hz => hr0 ((CubicThetaBottomRow.c_zero_iff r.val).mp hz)
    change cubicThetaGramRowLift h k V p (r.val.c,r.val.d)=G r.val
    rw [cubicThetaGramRowLift_row h k V r.val hr hp]
    simp only [G,ite_eq_right hr0]
  have hcover : Function.support (cubicThetaGramRowLift h k V p)⊆Set.range i := by
    intro x hx
    by_cases hc : (3:Eisenstein)∣x.1 ∧ x.1≠0
    · by_cases hd : primary x.2 ∧ IsCoprime x.1 x.2
      · let r : CubicThetaBottomRow := ⟨x.1,x.2,hc.1,hd.1,hd.2⟩
        have hr : r≠cubicThetaZeroRow := by
          intro he
          have hec := congrArg CubicThetaBottomRow.c he
          exact hc.2 hec
        have he : G r=cubicThetaGramRowLift h k V p x := by
          simp only [G,ite_eq_right hr]
          exact (cubicThetaGramRowLift_row h k V r hc.2 hp).symm
        exact ⟨⟨r,by change G r≠0; rw [he]; exact hx⟩,rfl⟩
      · exact False.elim (hx (by simp [cubicThetaGramRowLift,hc,cubicThetaKloostermanWeight,hd]))
    · exact False.elim (hx (by simp [cubicThetaGramRowLift,hc]))
  have hG : Summable G := by
    have hf := (cubicThetaPositiveFourierProfileTerm_summable k V hδ hV hp).mul_left
      (star (cubicThetaHorizontalCharacter h p.1))
    apply (hf.indicator {r | r≠cubicThetaZeroRow}).congr
    intro r
    by_cases hr : r=cubicThetaZeroRow <;> simp [G,hr]
  exact (hasSum_iff_hasSum_of_ne_zero_bij i hi hcover hm).mpr hG.hasSum

theorem cubicThetaGramRows_reindex (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    {δ : ℝ} (hδ : 0<δ) (hV : ∀ t≤δ,V t=0) {p : ℂ × ℝ} (hp : 0<p.2) :
    star (cubicThetaHorizontalCharacter h p.1)*cubicThetaFourierProfileSeries k p V=
      star (cubicThetaHorizontalCharacter h p.1)*
        cubicThetaFourierProfileTerm k cubicThetaZeroRow p V+
      ∑' x : Eisenstein × Eisenstein,cubicThetaGramRowLift h k V p x := by
  classical
  have hf := (cubicThetaPositiveFourierProfileTerm_summable k V hδ hV hp).mul_left
    (star (cubicThetaHorizontalCharacter h p.1))
  rw [cubicThetaFourierProfileSeries,←tsum_mul_left,
    hf.tsum_eq_add_tsum_ite cubicThetaZeroRow,(cubicThetaGramRowLift_hasSum h k V hδ hV hp).tsum_eq]

end CubicFirstMoment

end

end OAI
