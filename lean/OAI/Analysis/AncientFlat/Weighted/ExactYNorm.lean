import OAI.Analysis.AncientFlat.Weighted.WeightedLocalCore
import OAI.Analysis.AncientFlat.Regularity.HolderAlgebra

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ENNReal
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V]
lemma pdist_pos_of_ne {p q : V × ℝ} (hpq : p≠q) : 0<pdist p q := by
  by_cases hxy : p.1=q.1
  · have ht : p.2≠q.2 := fun ht => hpq (Prod.ext hxy ht)
    have ha : 0< |p.2-q.2| := abs_pos.mpr (sub_ne_zero.mpr ht)
    exact add_pos_of_nonneg_of_pos (norm_nonneg _) (Real.rpow_pos_of_pos ha _)
  · exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
      (Real.rpow_nonneg (abs_nonneg _) _)
lemma holderNorm_holderBound {α M : ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → ℂ}
    (hM : 0≤M) (h : holderNorm α Ω f≤ENNReal.ofReal M) : HolderBound α Ω f M := by
  classical
  constructor
  · intro p hp
    have h0 : ‖f p‖ₑ≤holderNorm α Ω f := by
      unfold holderNorm
      apply le_trans (le_iSup₂_of_le p hp le_rfl)
      exact le_add_right (le_refl _)
    exact (ENNReal.ofReal_le_ofReal_iff hM).mp (by simpa only [ofReal_norm] using h0.trans h)
  · intro p hp q hq
    by_cases he : p=q
    · subst q; simp only [sub_self,norm_zero]; exact mul_nonneg hM (Real.rpow_nonneg (pdist_nonneg _ _) _)
    have hd : 0<pdist p q^α := Real.rpow_pos_of_pos (pdist_pos_of_ne he) _
    have h0 : ‖f p-f q‖ₑ/ENNReal.ofReal (pdist p q^α)≤holderNorm α Ω f := by
      have hh : ‖f p-f q‖ₑ/ENNReal.ofReal (pdist p q^α)≤
          (⨆ r∈Ω, ⨆ s∈Ω, if r=s then 0 else ‖f r-f s‖ₑ/ENNReal.ofReal (pdist r s^α)) :=
        le_iSup_of_le p (le_iSup_of_le hp (le_iSup_of_le q (le_iSup_of_le hq (by simp [he]))))
      exact hh.trans (le_add_left (le_refl _))
    have hh := (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top).mp (h0.trans h)
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM hd.le)).mp
    simpa only [ofReal_norm,ENNReal.ofReal_mul hM] using hh
variable [InnerProductSpace ℝ V]
lemma yNorm_YBound {α w a M : ℝ} {f : V × ℝ → ℂ} (hM : 0≤M)
    (h : yNorm α w a f≤ENNReal.ofReal M) : YBound α w a M f := by
  intro p hp
  apply holderNorm_holderBound hM
  have hh : holderNorm α (localDomain a p) (pullback (w-4) p f)≤yNorm α w a f := by
    unfold yNorm
    exact le_iSup (fun P : {P : V × ℝ // P.2<0} =>
      holderNorm α (localDomain a P.val) (pullback (w-4) P.val f)) ⟨p,hp⟩
  exact hh.trans h
end FlatWeighted

end

end OAI
