import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityScaledForest
import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityTail

namespace OAI

/-! At the manuscript's polynomial density threshold, the selected actual
witnesses obey the polynomial radius, precision and area hypotheses used
by concentration. The threshold is fixed before all finite data. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem density_dyadic_length_order {w : ℝ} (hw : 0 < w) {i j : ℤ}
    (h : w/DyadicLineGrid.scale i ≤ w/DyadicLineGrid.scale j) : j ≤ i := by
  have hmul := (div_le_div_iff₀ (DyadicLineGrid.scale_pos i) (DyadicLineGrid.scale_pos j)).mp h
  have hscale : DyadicLineGrid.scale j ≤ DyadicLineGrid.scale i :=
    (mul_le_mul_iff_right₀ hw).mp (by simpa only [mul_comm] using hmul)
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hscale

theorem densitySpatialBox_radius_le (T : SlopeBox) (K : ℝ) {z : ℝ×ℝ}
    (hz : z ∈ densitySpatialBox T K) : T.radius z ≤ 2*K := by
  have h := (densitySpatialBox_iff T K z).mp hz
  change |T.horizontal z|+|T.transverse z| ≤ 2*K
  linarith [h.1,h.2]

theorem exists_power_density_forest (a : ℝ) (ha : 0 ≤ a) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι : Type*) (candidates : Finset ι) (T : ι → SlopeBox)
      (level cell : ι → ℤ) (q : ℤ) (ell0 w W : ℝ), 0 < ell0 → 0 < w → 12*w ≤ W →
      (∀ i ∈ candidates, (T i).length = ell0/DyadicLineGrid.scale (level i)) →
      (∀ i ∈ candidates, (T i).width = W) →
      (∀ i ∈ candidates, (T i).slope ∈ scaledAngularCell (w/ell0) q (level i) (cell i)) →
    ∀ (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ), MeasurableSet E →
      (volume.prod volume) E ≠ ∞ → Measurable u →
      (∀ i ∈ candidates, L^(-a)*(T i).area ≤ ∫ z in E ∩
        u ⁻¹' scaledAngularCell (w/ell0) q (level i) (cell i), (T i).densityKernel 203 z
        ∂volume.prod volume) →
      let K := L^(a/100+1)
      let witness := fun i => densityTest E u (T i) (scaledAngularCell (w/ell0) q (level i) (cell i)) K
      ∃ keepers : Finset ι, keepers ⊆ candidates ∧
        (∀ i ∈ keepers, MeasurableSet (witness i)) ∧
        Set.PairwiseDisjoint (keepers : Set ι) witness ∧
        (∑ i ∈ keepers, (T i).area) ≤ 2*L^a*(volume.prod volume).real E ∧
        (∀ i ∈ keepers, L^(-(a+2))*(T i).area ≤ (volume.prod volume).real (witness i)) ∧
        (∀ i ∈ keepers, ∀ z ∈ witness i, z ∈ E ∧ (T i).radius z ≤ L^(a+2) ∧
          |u z-(T i).slope| ≤ w/(T i).length ∧
          |u z-(T i).slope| ≤ (T i).width/(12*(T i).length)) ∧
        (∀ i ∈ candidates, ∃ j ∈ keepers, (T i).length ≤ (T j).length ∧
          scaledAngularCell (w/ell0) q (level j) (cell j) ⊆ scaledAngularCell (w/ell0) q (level i) (cell i) ∧
          ∀ z ∈ densitySpatialBox (T i) K, (T j).radius z ≤ L^(a+2)) := by
  obtain ⟨Ltail,hLtail,htail⟩ := density_tail_at_power_scale a ha
  refine ⟨max Ltail 10,by linarith [le_max_right Ltail (10:ℝ)],?_⟩
  intro L hL ι candidates T level cell q ell0 w W hell0 hw hW hlength hwidth hslope E u hE hEfin hu hdensity
    K witness
  have hLt : Ltail ≤ L := (le_max_left _ _).trans hL
  have hL10 : 10 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hK : 1 ≤ K := Real.one_le_rpow hL1 (by linarith)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKb : 10*K ≤ L^(a+2) := by
    calc
      _ ≤ L*K := mul_le_mul_of_nonneg_right hL10 hKpos.le
      _ = L^(a/100+2) := by
        dsimp only [K]
        conv_lhs => lhs; rw [← Real.rpow_one L]
        rw [← Real.rpow_add hLp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hmass (i : ι) (hi : i ∈ candidates) : (L^(-a)/2)*(T i).area ≤
      (volume.prod volume).real (witness i) :=
    density_witness_mass (T i) hK (by norm_num) (Real.rpow_nonneg hLp.le _)
      E u (scaledAngularCell (w/ell0) q (level i) (cell i)) hE hEfin hu
      (scaledAngularCell_measurable (w/ell0) q (level i) (cell i))
      (htail L hLt) (hdensity i hi)
  have horder (i : ι) (hi : i ∈ candidates) (j : ι) (hj : j ∈ candidates)
      (hij : (T i).length ≤ (T j).length) : level j ≤ level i :=
    density_dyadic_length_order hell0 (by simpa only [hlength i hi,hlength j hj] using hij)
  have hang (i : ι) (hi : i ∈ candidates) :
      ((w/ell0)*DyadicLineGrid.scale (level i))*(T i).length ≤ 1*(T i).width := by
    rw [hlength i hi,hwidth i hi,one_mul]
    have hs := DyadicLineGrid.scale_pos (level i)
    have heq : ((w/ell0)*DyadicLineGrid.scale (level i))*(ell0/DyadicLineGrid.scale (level i)) = w := by
      field_simp [hell0.ne',hs.ne']
    rw [heq]
    linarith
  obtain ⟨keepers,hsub,hmeas,hdisj,harea,hinside,hcover⟩ := exists_scaled_dyadic_density_forest
    candidates T level cell q (w/ell0) K 1 (L^(-a)/2) (div_pos hw hell0) hKpos.le (by norm_num) (by positivity)
    E u hE hEfin hu horder
    (fun i hi j hj => (hwidth i hi).trans (hwidth j hj).symm) hslope hang hmass
  have hlower : L^(-(a+2)) ≤ L^(-a)/2 := by
    calc
      _ ≤ L^(-a-1) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L^(-a)/L := by
        rw [sub_eq_add_neg,Real.rpow_add hLp,Real.rpow_neg_one]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hLp.le _) (by norm_num) (by linarith)
  refine ⟨keepers,hsub,hmeas,hdisj,?_,?_,?_,?_⟩
  · apply harea.trans_eq
    rw [Real.rpow_neg hLp.le]
    field_simp [(Real.rpow_pos_of_pos hLp a).ne']
  · intro i hi
    exact (mul_le_mul_of_nonneg_right hlower (T i).area_pos.le).trans (hmass i (hsub hi))
  · intro i hi z hz
    have hs := hinside i hi z hz
    have hrad := densitySpatialBox_radius_le (T i) K hz.1.2
    have hprec : |u z-(T i).slope| ≤ w/(T i).length := by
      convert hs.2 using 1
      rw [hlength i (hsub hi)]
      field_simp [hw.ne',hell0.ne',(DyadicLineGrid.scale_pos (level i)).ne']
    refine ⟨hs.1,hrad.trans (by linarith),hprec,hprec.trans ?_⟩
    rw [hwidth i (hsub hi)]
    apply (div_le_div_iff₀ (T i).length_pos (mul_pos (by norm_num) (T i).length_pos)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hW (T i).length_pos.le]
  · intro i hi
    obtain ⟨j,hj,hlen,hnested,hboxes⟩ := hcover i hi
    refine ⟨j,hj,hlen,hnested,?_⟩
    intro z hz
    have hr := densitySpatialBox_radius_le (T j) ((3+2*(1:ℝ))*K) (hboxes hz)
    exact hr.trans (by nlinarith)

end LipschitzHilbert

end

end OAI
