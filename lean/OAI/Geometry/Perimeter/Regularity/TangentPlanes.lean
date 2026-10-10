import OAI.Geometry.Perimeter.Regularity.SlabIteration

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem FullSlab.undilate_height {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : Euc n} {R a t : ℝ} (ht : 0 < t)
    (h : FullSlab (blownUpSet E 0 t) v R a) :
    ∀ x∈perimeterSupport E ∩ Metric.ball 0 (t*R), |inner ℝ v x|≤t*a := by
  intro x hx
  let y := t⁻¹•x
  have hxy : t•y=x := smul_inv_smul₀ ht.ne' x
  have hyS : y∈perimeterSupport (blownUpSet E 0 t) := by
    rw [perimeterSupport_blownUpSet hE 0 ht,zero_add,hxy]
    exact hx.1
  have hyB : y∈Metric.ball 0 R := by
    have hh : t*‖y‖<t*R := by
      rw [← show ‖t‖*‖y‖=t*‖y‖ by rw [Real.norm_of_nonneg ht.le],← norm_smul,hxy]
      simpa only [Metric.mem_ball,dist_zero_right] using hx.2
    simpa only [Metric.mem_ball,dist_zero_right] using (mul_lt_mul_iff_right₀ ht).mp hh
  have hh := mul_le_mul_of_nonneg_left (h.1 y ⟨hyS,hyB⟩) ht.le
  have hi : |inner ℝ v x|=t*|inner ℝ v y| := by
    rw [← hxy,real_inner_smul_right,abs_mul,abs_of_pos ht]
  exact hi ▸ hh

theorem relative_tangent_estimate {q M a : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hM : 0≤M) (ha : 0≤a) {E : Set (Euc n)} (hE : MeasurableSet E)
    {v : ℕ → Euc n} {w : Euc n}
    (hslab : ∀ j, FullSlab (blownUpSet E 0 (q^j)) (v j) 8 (a*(1/2)^j))
    (hlimit : ∀ j, ‖v j-w‖≤2*M*a*(1/2)^j) :
    ∀ j x, x∈perimeterSupport E → ‖x‖≤4*q^j →
      |inner ℝ w x|≤a*(2*M+1/(4*q))*(1/2)^j*‖x‖ := by
  intro j x hx hnx
  by_cases hx0 : x=0
  · simp [hx0]
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hden : 0 < 4*q^j := by positivity
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hxp hden) ((div_le_one hden).mpr hnx) hq hq1
  let l := j+k
  have hnlo : 4*q^(l+1)<‖x‖ := by
    have hh := (lt_div_iff₀ hden).mp hlo
    dsimp [l]
    rw [Nat.add_assoc,pow_add q j (k+1)]
    nlinarith
  have hnhi : ‖x‖≤4*q^l := by
    have hh := (div_le_iff₀ hden).mp hhi
    dsimp [l]
    rw [pow_add]
    nlinarith
  have hxB : x∈Metric.ball 0 (q^l*8) := by
    simp only [Metric.mem_ball,dist_zero_right]
    nlinarith [pow_pos hq l]
  have hheight := (hslab l).undilate_height hE (pow_pos hq l) x ⟨hx,hxB⟩
  have hqbound : q^l≤‖x‖/(4*q) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [pow_succ] at hnlo
    nlinarith
  have hpow : (1/2:ℝ)^l≤(1/2:ℝ)^j := by
    dsimp [l]
    rw [pow_add]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  have hnorm : ‖w-v l‖≤2*M*a*(1/2)^l := by rw [norm_sub_rev]; exact hlimit l
  have hi : inner ℝ w x=inner ℝ (w-v l) x+inner ℝ (v l) x := by
    rw [inner_sub_left]; ring
  calc
    |inner ℝ w x| ≤ ‖w-v l‖*‖x‖+|inner ℝ (v l) x| := by
      rw [hi]
      exact (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm (w-v l) x) le_rfl)
    _ ≤ (2*M*a*(1/2)^l)*‖x‖+q^l*(a*(1/2)^l) :=
      add_le_add (mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)) hheight
    _ ≤ (2*M*a*(1/2)^l)*‖x‖+(‖x‖/(4*q))*(a*(1/2)^l) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hqbound (show 0≤a*(1/2:ℝ)^l by positivity))
    _ = a*(2*M+1/(4*q))*(1/2)^l*‖x‖ := by ring
    _ ≤ a*(2*M+1/(4*q))*(1/2)^j*‖x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) (norm_nonneg x)

theorem exists_full_support_tangent_plane {q M δ : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hM : 0≤M) (hstep : SlabContractionProperty n q M δ) {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (hzero : (0:Euc n)∈perimeterSupport E)
    {v₀ : Euc n} (hv₀ : ‖v₀‖=1) {a : ℝ} (ha : 0 < a) (haδ : a < δ)
    (hs : FullSlab E v₀ 8 a) :
    ∃ w : Euc n, ‖w‖=1 ∧ ‖w-v₀‖≤2*M*a ∧
      ∀ j x, x∈perimeterSupport E → ‖x‖≤4*q^j →
        |inner ℝ w x|≤a*(2*M+1/(4*q))*(1/2)^j*‖x‖ := by
  obtain ⟨v,w,hv0,hunit,hwn,hwt,hslab,hlimit⟩ :=
    slab_normal_limit hq hstep hmin hzero hv₀ ha haδ hs
  refine ⟨w,hwn,?_,relative_tangent_estimate hq hq1 hM ha.le hmin.1 hslab hlimit⟩
  have hh := hlimit 0
  rw [hv0,pow_zero,mul_one,norm_sub_rev] at hh
  exact hh

end RPISingularHarnack

end

end OAI
