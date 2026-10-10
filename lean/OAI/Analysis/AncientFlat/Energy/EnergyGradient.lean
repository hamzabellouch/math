import OAI.Analysis.AncientFlat.Energy.EnergyQuadratic

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Laplacian
namespace ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def basisVec (i : Fin (Module.finrank ℝ V)) : V := stdOrthonormalBasis ℝ V i
def gradMass (u : V → ℂ) : ℝ := ∑ i, mass (dir (basisVec i) u)
omit [MeasurableSpace V] [BorelSpace V] in
lemma basisVec_norm (i : Fin (Module.finrank ℝ V)) : ‖basisVec i‖=1 :=
  (stdOrthonormalBasis ℝ V).norm_eq_one i
lemma gradMass_nonneg (u : V → ℂ) : 0 ≤ gradMass u :=
  Finset.sum_nonneg (fun _ _ => mass_nonneg _)
lemma gradient_balance_dir (u : V → ℂ) (hu : ContDiff ℝ 2 u) (hb : BoundedJets 2 u) (v : V) :
    mass (dir v u) = -pair u (dir v (dir v u)) -
      ∫ x, dir v weight x*inner ℝ (u x) (dir v u x) := by
  have hdu := contDiff_dir (n := 1) v u hu
  have hdu0 := hdu.continuous
  have hdb := (hb.dir hu v).zero
  have hwa := (contDiff_weight 2).smul hu
  have hwub := decays_weight.smul hb.zero
  have hdwub := decays_dir_smul v (contDiff_weight 2) hu decays_weight (decays_dir_weight v) hb
  have he := integral_inner_dir v (fun x => weight x • u x) (dir v u)
    (hwa.of_le (by norm_num)) hdu hwub hdwub hdb
      ((hb.dir hu v).dir hdu v).zero
  rw [dir_smul _ _ _ ((contDiff_weight 2).differentiable (by norm_num))
    (hu.differentiable (by norm_num))] at he
  simp_rw [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq] at he
  have hi : Integrable (fun x => dir v weight x*inner ℝ (u x) (dir v u x)) :=
    ((decays_dir_weight v).smul (hb.zero.inner hdb)).integrable
      ((contDiff_dir (n := 1) v weight (contDiff_weight 2)).continuous.mul (hu.continuous.inner hdu0))
  rw [integral_add hi (integrable_mass hdu0 hdb)] at he
  change pair u (dir v (dir v u)) = -((∫ x, dir v weight x*inner ℝ (u x) (dir v u x)) + mass (dir v u)) at he
  linarith
lemma pair_laplacian (u : V → ℂ) (hu : ContDiff ℝ 2 u) (hb : BoundedJets 2 u) :
    pair u (Δ u) = ∑ i, pair u (dir (basisVec i) (dir (basisVec i) u)) := by
  unfold pair
  rw [laplacian_eq_sum_dir u hu]
  simp_rw [inner_sum,Finset.mul_sum]
  rw [integral_finsetSum]
  · rfl
  · intro i _
    exact integrable_pair hu.continuous
      (contDiff_dir (n := 0) _ _ (contDiff_dir (n := 1) _ _ hu)).continuous
      hb.zero ((hb.dir hu _).dir (contDiff_dir _ _ hu) _).zero
lemma gradient_balance (u : V → ℂ) (hu : ContDiff ℝ 2 u) (hb : BoundedJets 2 u) :
    gradMass u = -pair u (Δ u) -
      ∑ i, ∫ x, dir (basisVec i) weight x*inner ℝ (u x) (dir (basisVec i) u x) := by
  rw [gradMass,pair_laplacian u hu hb]
  simp_rw [gradient_balance_dir u hu hb]
  rw [Finset.sum_sub_distrib,Finset.sum_neg_distrib]
lemma gradient_cross_bound (u : V → ℂ) (hu : ContDiff ℝ 2 u) (hb : BoundedJets 2 u) :
    gradMass u ≤ cross u (Δ u)+∑ i, cross u (dir (basisVec i) u) := by
  have hlo := (ClassicalIBP.contDiff_laplacian u 0 hu).continuous
  have hlb := (hb.laplacian 0 hu).zero
  have hmain := (neg_le_abs (pair u (Δ u))).trans (abs_pair_le hu.continuous hlo hb.zero hlb)
  have hterms (i : Fin (Module.finrank ℝ V)) :
      -(∫ x, dir (basisVec i) weight x*inner ℝ (u x) (dir (basisVec i) u x)) ≤
        cross u (dir (basisVec i) u) := by
    apply (neg_le_abs _).trans
    have hv := basisVec_norm i
    have hm : ∀ x, |dir (basisVec i) weight x|≤1*weight x := by
      intro x
      have hh := (fderiv ℝ weight x).le_opNorm (basisVec i)
      simpa only [dir,hv,mul_one,one_mul,Real.norm_eq_abs] using
        hh.trans (mul_le_mul_of_nonneg_right (norm_fderiv_weight_le x) (norm_nonneg _))
    simpa only [one_mul] using abs_coeff_pair_le hu.continuous (contDiff_dir (n := 1) _ _ hu).continuous
      hb.zero (hb.dir hu _).zero _ (contDiff_dir (n := 1) _ _ (contDiff_weight 2)).continuous
      1 (by norm_num) hm
  rw [gradient_balance u hu hb,sub_eq_add_neg,←Finset.sum_neg_distrib]
  exact add_le_add hmain (Finset.sum_le_sum (fun i _ => hterms i))
lemma cross_comm (f g : V → ℂ) : cross f g=cross g f := by
  unfold cross
  congr 1; funext x; ring
lemma gradient_interpolation (u : V → ℂ) (hu : ContDiff ℝ 2 u) (hb : BoundedJets 2 u)
    (ε : ℝ) (hε : 0<ε) :
    gradMass u ≤ ε*mass (Δ u)+(ε⁻¹+(Module.finrank ℝ V : ℝ))*mass u := by
  have hc := (ClassicalIBP.contDiff_laplacian u 0 hu).continuous
  have hd := (hb.laplacian 0 hu).zero
  have hy := weighted_young hc hu.continuous hd hb.zero ε hε
  rw [cross_comm (Δ u) u] at hy
  have hterms (i : Fin (Module.finrank ℝ V)) :
      2*cross u (dir (basisVec i) u) ≤ mass u+mass (dir (basisVec i) u) := by
    simpa using weighted_young hu.continuous (contDiff_dir (n := 1) _ _ hu).continuous
      hb.zero (hb.dir hu _).zero 1 (by norm_num)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterms i)
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at hs
  have hh := gradient_cross_bound u hu hb
  unfold gradMass at hh ⊢
  nlinarith
end ParametrixUniqueness

end

end OAI
