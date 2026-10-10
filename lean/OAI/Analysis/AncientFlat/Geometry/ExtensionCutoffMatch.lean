import OAI.Analysis.AncientFlat.Geometry.ExtensionCutoff
import OAI.Analysis.AncientFlat.Geometry.ExtensionGeometry

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff NNReal
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma extensionWeight_eq_regular {ψ : ℝ → ℝ} (hψ : ExtensionCutoff ψ) {T : ℝ} (hT : 0<T)
    (p : V × ℝ) (hp : p.2<0) (hs : (1:ℝ)/2≤ sigma p) :
    extensionWeight ψ T p=regularWeight ψ T p := by
  have hbp : 0<‖p.1‖^2+Real.sqrt T := add_pos_of_nonneg_of_pos (sq_nonneg _) (Real.sqrt_pos.mpr hT)
  have hB : 0< max (‖p.1‖^2+Real.sqrt T) ((1:ℝ)/64) := hbp.trans_le (le_max_left _ _)
  by_cases ht : -T≤p.2
  · have hn : (-p.2-T)/(max (‖p.1‖^2+Real.sqrt T) ((1:ℝ)/64))^2≤0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    simp only [extensionWeight,ite_eq_left ht,regularWeight,clip01,max_eq_left hn,
      min_eq_right (show (0:ℝ)≤1 by norm_num),cutoff_zero hψ]
  · have hn : 0≤ -p.2-T := by linarith [not_le.mp ht]
    by_cases hb : (1:ℝ)/64≤‖p.1‖^2+Real.sqrt T
    · simp only [extensionWeight,ite_eq_right ht,regularWeight,max_eq_left hb]
      exact (cutoff_clip hψ _ (div_nonneg hn (sq_nonneg _))).symm
    · have hb' : ‖p.1‖^2+Real.sqrt T<(1:ℝ)/64 := not_le.mp hb
      have hsq := sigma_sq p
      have htime := Real.sq_sqrt (neg_pos.mpr hp).le
      have hTsq := Real.sq_sqrt hT.le
      have hsqrt : (15:ℝ)/64≤Real.sqrt (-p.2) := by
        nlinarith [sq_nonneg ‖p.1‖,Real.sqrt_nonneg T,Real.sqrt_nonneg (-p.2)]
      have htimebound : (1:ℝ)/4096≤ -p.2-T := by
        nlinarith [sq_nonneg ‖p.1‖,Real.sqrt_nonneg T,Real.sqrt_nonneg (-p.2)]
      have harg1 : 1≤(-p.2-T)/(‖p.1‖^2+Real.sqrt T)^2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hbp)).mpr
        nlinarith
      have harg2 : 1≤(-p.2-T)/((1:ℝ)/64)^2 := by
        norm_num
        nlinarith
      simp only [extensionWeight,ite_eq_right ht,regularWeight,max_eq_right hb'.le,
        hψ.2.2.2 _ harg1,clip01,max_eq_right (show (0:ℝ)≤(-p.2-T)/((1:ℝ)/64)^2 by positivity),
        min_eq_left harg2,hψ.2.2.2 1 le_rfl]
end FlatWeighted

end

end OAI
