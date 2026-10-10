import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIntegerBox

namespace OAI

/-! Summable nonnegative coordinate masses pushed to the actual Fourier lattice. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaMassPushforward {ι κ : Type*} (g : ι → κ) (w : ι → ℝ) (n : κ) : ℝ :=
  ∑' p,if g p=n then w p else 0

lemma cubicThetaMassPushforward_properties {ι κ : Type*} (g : ι → κ) (w : ι → ℝ)
    (hw0 : ∀ p,0≤w p) (hw : Summable w) :
    Summable (cubicThetaMassPushforward g w) ∧
    (∑' n,cubicThetaMassPushforward g w n)=∑' p,w p ∧
    (∀ n,0≤cubicThetaMassPushforward g w n) ∧
    ∀ p,w p≤cubicThetaMassPushforward g w (g p) := by
  have hnon : ∀ q : ι × κ,0≤(if g q.1=q.2 then w q.1 else 0) := by
    intro q; split_ifs <;> first | exact hw0 _ | exact le_rfl
  have hrows (p : ι) : Summable (fun n : κ => if g p=n then w p else 0) :=
    (hasSum_ite_eq' (g p) (w p)).summable
  have houter : Summable (fun p : ι => ∑' n : κ,if g p=n then w p else 0) := by
    simpa only [tsum_ite_eq'] using hw
  have hp : Summable (fun q : ι × κ => if g q.1=q.2 then w q.1 else 0) :=
    (summable_prod_of_nonneg hnon).mpr ⟨hrows,houter⟩
  have hs := (summable_prod_of_nonneg (fun q : κ × ι => hnon (q.2,q.1))).mp hp.prod_symm
  have he : (∑' n,cubicThetaMassPushforward g w n)=∑' p,w p := by
    change (∑' n,∑' p,if g p=n then w p else 0)=_
    have hc := hp.tsum_comm (f := fun p n => if g p=n then w p else 0)
    exact hc.trans (by simp only [tsum_ite_eq'])
  refine ⟨hs.2,he,fun n => tsum_nonneg (fun p => hnon (p,n)),?_⟩
  intro p
  have h := (hs.1 (g p)).sum_le_tsum {p} (fun q _ => hnon (q,g p))
  simpa only [cubicThetaMassPushforward,Finset.sum_singleton,ite_true] using h

end CubicFirstMoment

end

end OAI
