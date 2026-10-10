import OAI.Analysis.AncientFlat.Weighted.ExactXNorm

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ENNReal
namespace FlatWeighted
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
omit [InnerProductSpace ℝ V] in
lemma holderNorm_congr {α : ℝ} {Ω : Set (V × ℝ)} {f g : V × ℝ → ℂ}
    (h : EqOn f g Ω) : holderNorm α Ω f=holderNorm α Ω g := by
  classical
  unfold holderNorm
  congr 1
  · apply iSup_congr
    intro p
    apply iSup_congr
    intro hp
    rw [h hp]
  · apply iSup_congr
    intro p
    apply iSup_congr
    intro hp
    apply iSup_congr
    intro q
    apply iSup_congr
    intro hq
    rw [h hp,h hq]
lemma xNorm_time_congr {m : ℕ} (e : OrthonormalBasis (Fin m) ℝ V) (α w a : ℝ)
    (u ut vt : ℝ → V → ℂ) (h : ∀ t : ℝ, t<0 → ∀ x : V, ut t x=vt t x) :
    xNorm e α w a u ut=xNorm e α w a u vt := by
  unfold xNorm
  apply iSup_congr
  intro p
  unfold localXNorm
  congr 1
  apply holderNorm_congr
  intro q hq
  simp only [weightedTime]
  rw [h _ hq.2.2.2]
end FlatWeighted

end

end OAI
