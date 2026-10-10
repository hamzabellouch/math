import OAI.Analysis.AncientFlat.Energy.EnergyGradient

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Laplacian
namespace ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def principal (a : V → ℝ) (u : V → ℂ) : ℝ :=
  ∫ x, (weight x*a x)*inner ℝ (u x) (Δ (Δ u) x)
omit [MeasurableSpace V] [BorelSpace V] in
lemma laplacian_smul_expand (a : V → ℝ) (u : V → ℂ)
    (ha : ContDiff ℝ 2 a) (hu : ContDiff ℝ 2 u) (x : V) :
    Δ (fun y => a y • u y) x = a x • Δ u x +
      (∑ i, (2*dir (basisVec i) a x) • dir (basisVec i) u x) +
      ∑ i, dir (basisVec i) (dir (basisVec i) a) x • u x := by
  rw [laplacian_eq_sum_dir (fun y => a y • u y) (ha.smul hu),laplacian_eq_sum_dir u hu]
  simp_rw [dir_dir_smul _ _ _ ha hu]
  simp only [Finset.sum_add_distrib,Finset.smul_sum,basisVec]
  module
lemma integral_coeff_pair {f g : V → ℂ} (hc : Continuous f) (hd : Continuous g)
    (hb : Bounded f) (he : Bounded g) {c : V → ℝ} (hc' : Continuous c) (hdec : Decays c) :
    Integrable (fun x => c x*inner ℝ (f x) (g x)) :=
  (hdec.smul (hb.inner he)).integrable (hc'.mul (hc.inner hd))
lemma principal_expand (a : V → ℝ) (u : V → ℂ)
    (ha : ContDiff ℝ 2 a) (hab : BoundedJets 2 a)
    (hu : ContDiff ℝ 4 u) (hub : BoundedJets 4 u) :
    principal a u = (∫ x, (weight x*a x)*‖Δ u x‖^2) +
      (∑ i, ∫ x, (2*dir (basisVec i) (fun y => weight y*a y) x)*
        inner ℝ (dir (basisVec i) u x) (Δ u x)) +
      ∑ i, ∫ x, dir (basisVec i) (dir (basisVec i) (fun y => weight y*a y)) x*
        inner ℝ (u x) (Δ u x) := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hb2 : BoundedJets 2 u := hub.of_le (by norm_num)
  have hwa := (contDiff_weight 2).mul ha
  have hlu := (ClassicalIBP.contDiff_laplacian u 2 hu).continuous
  have hlb := (hub.laplacian 2 hu).zero
  have hi0 : Integrable (fun x => (weight x*a x)*‖Δ u x‖^2) := by
    simpa only [pow_two,smul_eq_mul] using ((decays_weight_mul hab.zero).smul (hlb.norm.mul hlb.norm)).integrable
      (hwa.continuous.mul (hlu.norm.mul hlu.norm))
  have hi1 (i : Fin (Module.finrank ℝ V)) :
      Integrable (fun x => (2*dir (basisVec i) (fun y => weight y*a y) x)*inner ℝ (dir (basisVec i) u x) (Δ u x)) :=
    integral_coeff_pair (contDiff_dir (n := 1) _ _ hu2).continuous hlu (hb2.dir hu2 _).zero hlb
      (continuous_const.mul (contDiff_dir (n := 1) _ _ hwa).continuous)
      ((decays_dir_weight_mul ha hab _).const_smul 2)
  have hi2 (i : Fin (Module.finrank ℝ V)) :
      Integrable (fun x => dir (basisVec i) (dir (basisVec i) (fun y => weight y*a y)) x*inner ℝ (u x) (Δ u x)) :=
    integral_coeff_pair hu.continuous hlu hub.zero hlb
      (contDiff_dir (n := 0) _ _ (contDiff_dir (n := 1) _ _ hwa)).continuous
      (decays_dir_dir_weight_mul ha hab _)
  rw [principal,integral_weight_bilaplacian a u ha hab hu hub]
  simp_rw [laplacian_smul_expand _ _ hwa hu2,inner_add_left,sum_inner,real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  erw [integral_add (hi0.add (integrable_finsetSum Finset.univ (fun i _ => hi1 i)))
    (integrable_finsetSum Finset.univ (fun i _ => hi2 i)),
    integral_add hi0 (integrable_finsetSum Finset.univ (fun i _ => hi1 i)),
    integral_finsetSum Finset.univ (fun i _ => hi1 i),integral_finsetSum Finset.univ (fun i _ => hi2 i)]
lemma principal_lower_cross (a : V → ℝ) (u : V → ℂ) (α C : ℝ) (hC : 0≤C)
    (ha : ContDiff ℝ 2 a) (haj : ∀ k : ℕ, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k a x‖≤C)
    (ha0 : ∀ x, α≤a x) (hu : ContDiff ℝ 4 u) (hub : BoundedJets 4 u) :
    α*mass (Δ u) -4*C*(∑ i, cross (dir (basisVec i) u) (Δ u)) -
      (4*C*(Module.finrank ℝ V : ℝ))*cross u (Δ u) ≤ principal a u := by
  have hab : BoundedJets 2 a := fun k hk => ⟨C,hC,haj k hk⟩
  have hwa := (contDiff_weight 2).mul ha
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hb2 : BoundedJets 2 u := hub.of_le (by norm_num)
  have hlu := (ClassicalIBP.contDiff_laplacian u 2 hu).continuous
  have hlb := (hub.laplacian 2 hu).zero
  have hi0 : Integrable (fun x => (weight x*a x)*‖Δ u x‖^2) := by
    simpa only [pow_two,smul_eq_mul] using ((decays_weight_mul hab.zero).smul (hlb.norm.mul hlb.norm)).integrable
      (hwa.continuous.mul (hlu.norm.mul hlu.norm))
  have hlead : α*mass (Δ u) ≤ ∫ x, (weight x*a x)*‖Δ u x‖^2 := by
    rw [mass,←integral_const_mul]
    apply integral_mono ((integrable_mass hlu hlb).const_mul α) hi0
    intro x
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha0 x) (weight_pos x).le) (sq_nonneg ‖Δ u x‖)]
  have hterm1 (i : Fin (Module.finrank ℝ V)) :
      -(4*C*cross (dir (basisVec i) u) (Δ u)) ≤ ∫ x,
        (2*dir (basisVec i) (fun y => weight y*a y) x)*inner ℝ (dir (basisVec i) u x) (Δ u x) := by
    have hbd (x : V) := (weight_mul_bounds a ha C hC haj (basisVec i) x (basisVec_norm i).le).2.1
    have hh := abs_coeff_pair_le (contDiff_dir (n := 1) (basisVec i) u hu2).continuous hlu
      (hb2.dir hu2 (basisVec i)).zero hlb (fun x => 2*dir (basisVec i) (fun y => weight y*a y) x)
      (continuous_const.mul (contDiff_dir (n := 1) _ _ hwa).continuous)
      (4*C) (by positivity) (fun x => by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]; nlinarith [hbd x])
    linarith [neg_abs_le (∫ x, (2*dir (basisVec i) (fun y => weight y*a y) x)*inner ℝ (dir (basisVec i) u x) (Δ u x))]
  have hterm2 (i : Fin (Module.finrank ℝ V)) :
      -(4*C*cross u (Δ u)) ≤ ∫ x,
        dir (basisVec i) (dir (basisVec i) (fun y => weight y*a y)) x*inner ℝ (u x) (Δ u x) := by
    have hh := abs_coeff_pair_le hu.continuous hlu hub.zero hlb (dir (basisVec i) (dir (basisVec i) (fun y => weight y*a y)))
      (contDiff_dir (n := 0) _ _ (contDiff_dir (n := 1) _ _ hwa)).continuous
      (4*C) (by positivity) (fun x => (weight_mul_bounds a ha C hC haj (basisVec i) x (basisVec_norm i).le).2.2)
    linarith [neg_abs_le (∫ x, dir (basisVec i) (dir (basisVec i) (fun y => weight y*a y)) x*inner ℝ (u x) (Δ u x))]
  have hs1 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm1 i)
  have hs2 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm2 i)
  simp only [Finset.sum_neg_distrib,←Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs1 hs2
  rw [principal_expand _ _ ha hab hu hub]
  nlinarith
end ParametrixUniqueness

end

end OAI
