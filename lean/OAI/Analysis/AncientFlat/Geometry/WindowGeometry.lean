import OAI.Analysis.AncientFlat.Geometry.ParabolicWindows

namespace OAI
noncomputable section
open Set Filter
namespace ParabolicLocalization
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def windowInv (p0 : V × ℝ) (q : ℝ) (p : V × ℝ) : V × ℝ :=
  (q⁻¹ • (p.1-p0.1),(p.2-p0.2)/q^4)
omit [FiniteDimensional ℝ V] in
lemma window_windowInv (p0 : V × ℝ) {q : ℝ} (hq : q≠0) (p : V × ℝ) :
    window p0 q (windowInv p0 q p)=p := by
  ext
  · simp [window,windowInv,smul_smul,hq]
  · dsimp [window,windowInv]; field_simp; ring
omit [FiniteDimensional ℝ V] in
lemma window_zero (p0 : V × ℝ) (q : ℝ) : window p0 q (0,0)=p0 := by
  simp [window]
lemma pow_quarter_four {r : ℝ} (hr : 0≤r) : (r^((1:ℝ)/4))^4=r := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hr]
  norm_num
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma cylinder_pdist_zero {R : ℝ} (hR : 0≤R) {p : V × ℝ} (hp : p∈cylinder R) :
    pdist (0,0) p≤2*R := by
  have ht : |p.2|≤R^4 := by rw [abs_of_nonpos hp.2.2]; linarith [hp.2.1]
  have ht' := Real.rpow_le_rpow (abs_nonneg _) ht (by norm_num : (0:ℝ)≤1/4)
  rw [pow_four_quarter hR] at ht'
  simp only [pdist,zero_sub,norm_neg,abs_neg]
  linarith [hp.1]
omit [FiniteDimensional ℝ V] in
lemma small_window_maps {r R q : ℝ} (hr : 0≤r) (hq : 0<q) (hgap : 4*q≤R-r)
    (p0 : V × ℝ) (hp0 : p0∈cylinder r) :
    MapsTo (window p0 q) (cylinder 4) (cylinder R) := by
  have ht : r^4+(4*q)^4≤R^4 := (pow_add_pow_le hr (by positivity) (by norm_num : (4:ℕ)≠0)).trans
    (pow_le_pow_left₀ (by positivity) (by linarith : r+4*q≤R) 4)
  intro p hp
  refine ⟨?_,?_,?_⟩
  · change ‖p0.1+q • p.1‖<R
    have hn : ‖q • p.1‖=q*‖p.1‖ := by rw [norm_smul,Real.norm_of_nonneg hq.le]
    apply (norm_add_le _ _).trans_lt
    rw [hn]
    nlinarith [hp0.1,hp.1]
  · change -(R^4)<p0.2+q^4*p.2
    have hp' := hp.2.1
    have hp0' := hp0.2.1
    have hq4 : 0<q^4 := pow_pos hq _
    norm_num at hp'
    nlinarith
  · change p0.2+q^4*p.2≤0
    have hm := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hq.le 4) hp.2.2
    linarith [hp0.2.2]
omit [FiniteDimensional ℝ V] in
lemma windowInv_mem_one (p0 : V × ℝ) {q : ℝ} (hq : 0<q) (p : V × ℝ)
    (hx : ‖p.1-p0.1‖<q) (ht : |p.2-p0.2|<q^4) (ht0 : p.2≤p0.2) :
    windowInv p0 q p∈cylinder 1 := by
  refine ⟨?_,?_,?_⟩
  · change ‖q⁻¹ • (p.1-p0.1)‖<1
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hq.le)]
    have := mul_lt_mul_of_pos_left hx (inv_pos.mpr hq)
    simpa only [inv_mul_cancel₀ hq.ne'] using this
  · change -(1:ℝ)^4<(p.2-p0.2)/q^4
    rw [lt_div_iff₀ (pow_pos hq 4)]
    rw [abs_of_nonpos (sub_nonpos.mpr ht0)] at ht
    norm_num; linarith
  · change (p.2-p0.2)/q^4≤0
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht0) (pow_nonneg hq.le 4)
omit [FiniteDimensional ℝ V] in
lemma close_pair_window {r q : ℝ} (hq : 0<q) (p z : V × ℝ)
    (hp : p∈cylinder r) (hz : z∈cylinder r) (hd : pdist p z<q) :
    let p0 : V × ℝ := (p.1,max p.2 z.2)
    p0∈cylinder r ∧ windowInv p0 q p∈cylinder 1 ∧ windowInv p0 q z∈cylinder 1 := by
  dsimp only
  have ht : |p.2-z.2|<q^4 := by
    have hh : |p.2-z.2|^((1:ℝ)/4)<q := by
      dsimp [pdist] at hd; linarith [norm_nonneg (p.1-z.1)]
    have hh' : (|p.2-z.2|^((1:ℝ)/4))^4<q^4 := by gcongr
    rwa [pow_quarter_four (abs_nonneg _)] at hh'
  have hx : ‖p.1-z.1‖<q := by
    dsimp [pdist] at hd; linarith [Real.rpow_nonneg (abs_nonneg (p.2-z.2)) ((1:ℝ)/4)]
  have ht1 : |p.2-max p.2 z.2|<q^4 := by
    rcases le_total p.2 z.2 with h | h
    · simpa only [max_eq_right h] using ht
    · simp only [max_eq_left h,sub_self,abs_zero]; positivity
  have ht2 : |z.2-max p.2 z.2|<q^4 := by
    rcases le_total p.2 z.2 with h | h
    · simp only [max_eq_right h,sub_self,abs_zero]; positivity
    · simpa only [max_eq_left h,abs_sub_comm] using ht
  refine ⟨⟨hp.1,hp.2.1.trans_le (le_max_left _ _),max_le hp.2.2 hz.2.2⟩,?_,?_⟩
  · exact windowInv_mem_one _ hq p (by simpa using hq) ht1 (le_max_left _ _)
  · exact windowInv_mem_one _ hq z (by simpa only [norm_sub_rev] using hx) ht2 (le_max_right _ _)
end ParabolicLocalization

end

end OAI
