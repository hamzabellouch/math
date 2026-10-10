import Mathlib
import OAI.MathematicalPhysics.BFSS.GaugeOrbits

namespace OAI

/-! Normal chord estimates, reach and unique tube fibers. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset
variable {N : ℕ} (M : AlgebraData N)

lemma bracketLinearization_gaugeTangent (q : Boson N) (w : ColorVector N)
    (i j : SpaceIndex) :
    M.bracketLinearization q (M.gaugeTangent q w) i j =
      M.colorLie w (M.colorLie (spatialColor q i) (spatialColor q j)) := by
  simp only [bracketLinearization,M.spatialColor_gaugeTangent]
  have he := M.colorLie_jacobi w (spatialColor q i) (spatialColor q j)
  have := eq_add_of_sub_eq he
  simpa only [add_comm] using this.symm

lemma cyclicLinearization_gaugeTangent (q : Boson N) (w : ColorVector N)
    (i j k : SpaceIndex) :
    M.cyclicLinearization q (M.gaugeTangent q w) i j k =
      M.colorLie w (M.colorLie (spatialColor q i) (spatialColor q j) -
        (2:ℝ) • spatialColor q k) := by
  simp only [cyclicLinearization,M.bracketLinearization_gaugeTangent,
    M.spatialColor_gaugeTangent]
  change M.colorAd w _ - (2:ℝ) • M.colorAd w _ = M.colorAd w _
  rw [map_sub,map_smul]

lemma normalQuadratic_sub_tangent (q z t : Boson N)
    (hq : q ∈ M.massiveZeros) (ht : t ∈ LinearMap.range (M.gaugeTangent q)) :
    M.normalQuadratic q (z-t) = M.normalQuadratic q z := by
  obtain ⟨w,rfl⟩ := ht
  have hr := M.potential_zero_relations q hq
  have hc (i j k : SpaceIndex)
      (h : M.colorLie (spatialColor q i) (spatialColor q j) = (2:ℝ) • spatialColor q k) :
      M.cyclicLinearization q (z-M.gaugeTangent q w) i j k =
        M.cyclicLinearization q z i j k := by
    rw [←M.cyclicLinearizationMap_apply q (z-M.gaugeTangent q w) i j k]
    rw [map_sub,M.cyclicLinearizationMap_apply,M.cyclicLinearizationMap_apply,
      M.cyclicLinearization_gaugeTangent,h,sub_self,M.colorLie_zero_right,sub_zero]
  have hb (i j : SpaceIndex) (hj : 3 ≤ j.val) :
      M.bracketLinearization q (z-M.gaugeTangent q w) i j =
        M.bracketLinearization q z i j := by
    rw [←M.bracketLinearizationMap_apply q (z-M.gaugeTangent q w) i j]
    rw [map_sub,M.bracketLinearizationMap_apply,M.bracketLinearizationMap_apply,
      M.bracketLinearization_gaugeTangent,hr.2.2.2 j hj,
      M.colorLie_zero_right,M.colorLie_zero_right,sub_zero]
  have hs (i : SpaceIndex) (hi : 3 ≤ i.val) :
      spatialColor (z-M.gaugeTangent q w) i = spatialColor z i := by
    change spatialColorMap i (z-M.gaugeTangent q w) = _
    rw [map_sub]
    change spatialColor z i - spatialColor (M.gaugeTangent q w) i = _
    rw [M.spatialColor_gaugeTangent,hr.2.2.2 i hi,M.colorLie_zero_right,sub_zero]
  have hbSum : (∑ i : SpaceIndex, ∑ j : SpaceIndex, if i < j ∧ 3 ≤ j.val then
      ‖M.bracketLinearization q (z-M.gaugeTangent q w) i j‖^2 else 0) =
      ∑ i : SpaceIndex, ∑ j : SpaceIndex, if i < j ∧ 3 ≤ j.val then
        ‖M.bracketLinearization q z i j‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs with hh
    · rw [hb i j hh.2]
    · rfl
  have hsSum : (∑ i : SpaceIndex, if 3 ≤ i.val then
      ‖spatialColor (z-M.gaugeTangent q w) i‖^2 else 0) =
      ∑ i : SpaceIndex, if 3 ≤ i.val then ‖spatialColor z i‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with hh
    · rw [hs i hh]
    · rfl
  unfold normalQuadratic
  rw [hc 0 1 2 hr.1,hc 1 2 0 hr.2.1,hc 2 0 1 hr.2.2.1,hbSum,hsSum]

lemma normalQuadratic_projection (q z : Boson N) (hq : q ∈ M.massiveZeros) :
    M.normalQuadratic q ((M.normalSlice q).starProjection z) = M.normalQuadratic q z := by
  have ht : z-(M.normalSlice q).starProjection z ∈ LinearMap.range (M.gaugeTangent q) := by
    have hh := (M.normalSlice q).sub_starProjection_mem_orthogonal z
    simpa only [normalSlice,Submodule.orthogonal_orthogonal] using hh
  have hh := M.normalQuadratic_sub_tangent q z _ hq ht
  rw [sub_sub_cancel] at hh
  exact hh

theorem massiveZeros_normal_chord (hN : 2 ≤ N) :
    ∃ K : ℝ, 0 < K ∧ ∀ q ∈ M.massiveZeros, ∀ p ∈ M.massiveZeros,
      ‖(M.normalSlice q).starProjection (p-q)‖ ≤ K * ‖p-q‖^2 := by
  obtain ⟨c,hc,hcQ⟩ := M.normalQuadratic_uniform_coercive hN
  obtain ⟨C,hC,hCR⟩ := M.quarticRemainder_bound
  let K := max 1 (2*C/c)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hKC : 2*C ≤ c*K := by
    have hh := (div_le_iff₀ hc).mp (le_max_right 1 (2*C/c))
    simpa only [K,mul_comm] using hh
  refine ⟨K,hK0,?_⟩
  intro q hq p hp
  have ht := M.potential_taylor_lower q (p-q) hq
  rw [add_sub_cancel,hp] at ht
  have hQ := hcQ q hq ((M.normalSlice q).starProjection (p-q))
    ((M.normalSlice q).starProjection_apply_mem (p-q))
  rw [M.normalQuadratic_projection q (p-q) hq] at hQ
  have hR := hCR (p-q)
  have hsq : ‖(M.normalSlice q).starProjection (p-q)‖^2 ≤ K*‖p-q‖^4 := by
    have hh := mul_le_mul_of_nonneg_right hKC (pow_nonneg (norm_nonneg (p-q)) 4)
    nlinarith
  have hKsq : K ≤ K^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hKsq (pow_nonneg (norm_nonneg (p-q)) 4)
  have hpos : 0 ≤ K*‖p-q‖^2 := by positivity
  nlinarith [norm_nonneg ((M.normalSlice q).starProjection (p-q))]

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
variable {N : ℕ} (M : AlgebraData N)

lemma normal_pairing_chord {q p z : Boson N}
    (hz : z ∈ M.normalSlice q) :
    |inner ℝ z (p-q)| ≤ ‖z‖ * ‖(M.normalSlice q).starProjection (p-q)‖ := by
  have he := (M.normalSlice q).starProjection_inner_eq_zero (p-q) z hz
  rw [inner_sub_left] at he
  have he' : inner ℝ z (p-q) = inner ℝ z ((M.normalSlice q).starProjection (p-q)) := by
    calc
      _ = inner ℝ (p-q) z := real_inner_comm _ _
      _ = inner ℝ ((M.normalSlice q).starProjection (p-q)) z := sub_eq_zero.mp he
      _ = _ := real_inner_comm _ _
  rw [he']
  exact abs_real_inner_le_norm _ _

theorem massiveZeros_normal_reach (hN : 2 ≤ N) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ M.massiveZeros, ∀ p ∈ M.massiveZeros,
      ∀ z w : Boson N, z ∈ M.normalSlice q → w ∈ M.normalSlice p →
      ‖z‖ ≤ ρ → ‖w‖ ≤ ρ → q+z=p+w → q=p ∧ z=w := by
  obtain ⟨K,hK,hbound⟩ := M.massiveZeros_normal_chord hN
  let ρ := 1/(4*K)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hKr : K*ρ = 1/4 := by dsimp [ρ]; field_simp [ne_of_gt hK]
  refine ⟨ρ,hρ,?_⟩
  intro q hq p hp z w hz hw hzr hwr hsum
  have az := (M.normal_pairing_chord hz).trans
    (mul_le_mul_of_nonneg_left (hbound q hq p hp) (norm_nonneg z))
  have aw := (M.normal_pairing_chord hw).trans
    (mul_le_mul_of_nonneg_left (hbound p hp q hq) (norm_nonneg w))
  have ez : inner ℝ z (p-q) ≤ ‖z‖*(K*‖p-q‖^2) := (le_abs_self _).trans az
  have ew : inner ℝ w (q-p) ≤ ‖w‖*(K*‖q-p‖^2) := (le_abs_self _).trans aw
  rw [norm_sub_rev q p] at ew
  have hd : p-q = z-w := by
    calc
      p-q = (p+w)-q-w := by abel
      _ = (q+z)-q-w := congrArg (fun x : Boson N => x-q-w) hsum.symm
      _ = z-w := by abel
  have he : ‖p-q‖^2 = inner ℝ z (p-q)+inner ℝ w (q-p) := by
    rw [←real_inner_self_eq_norm_sq]
    conv_lhs => lhs; rw [hd]
    rw [inner_sub_left,←neg_sub p q,inner_neg_right]
    ring
  have hcoef : K*(‖z‖+‖w‖) ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hzr hwr) hK.le
    nlinarith [hh]
  have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖p-q‖)
  have hn : ‖p-q‖^2 = 0 := by nlinarith [sq_nonneg ‖p-q‖]
  have hpq : p=q := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  refine ⟨hpq.symm,?_⟩
  rw [hpq] at hsum
  exact add_left_cancel hsum

theorem massiveZeros_normal_tubes (hN : 2 ≤ N) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ q ∈ M.massiveZeros, ∀ z : Boson N,
        z ∈ M.normalSlice q → ‖z‖ ≤ ρ →
        Metric.infDist (q+z) M.massiveZeros = ‖z‖) ∧
      (∀ x : Boson N, Metric.infDist x M.massiveZeros ≤ ρ →
        ∃! q : Boson N, q ∈ M.massiveZeros ∧ x-q ∈ M.normalSlice q ∧ ‖x-q‖ ≤ ρ) := by
  obtain ⟨ρ,hρ,hreach⟩ := M.massiveZeros_normal_reach hN
  refine ⟨ρ,hρ,?_,?_⟩
  · intro q hq z hz hzr
    obtain ⟨p,hp,he,hn⟩ := M.nearest_massive_zero hN (q+z)
    have hdist : Metric.infDist (q+z) M.massiveZeros ≤ ‖z‖ := by
      simpa only [dist_eq_norm,add_sub_cancel_left] using
        Metric.infDist_le_dist_of_mem (x := q+z) hq
    have hpq := hreach q hq p hp z (q+z-p) hz hn hzr
      (by rw [he]; exact hdist.trans hzr) (by abel)
    rw [←hpq.1,add_sub_cancel_left] at he
    exact he.symm
  · intro x hx
    obtain ⟨q,hq,he,hn⟩ := M.nearest_massive_zero hN x
    refine ⟨q,⟨hq,hn,he ▸ hx⟩,?_⟩
    intro p hp
    have hr := hreach p hp.1 q hq (x-p) (x-q) hp.2.1 hn hp.2.2 (he ▸ hx)
      (by simp only [add_sub_cancel])
    exact hr.1

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
variable {N : ℕ} (M : AlgebraData N)

lemma gaugeAction_add (U : unitary (ColorMatrix N)) (x y : Boson N) :
    M.gaugeAction U (x+y) = M.gaugeAction U x+M.gaugeAction U y := by
  obtain ⟨L,hL⟩ := M.gaugeConjugate_linear U
  change M.gaugeConjugate U (x+y) = _
  rw [←hL, map_add,hL,hL]
  rfl

lemma gaugeAction_smul (U : unitary (ColorMatrix N)) (c : ℝ) (x : Boson N) :
    M.gaugeAction U (c • x) = c • M.gaugeAction U x := by
  obtain ⟨L,hL⟩ := M.gaugeConjugate_linear U
  change M.gaugeConjugate U (c • x) = _
  rw [←hL, map_smul,hL]
  rfl

lemma gaugeAction_norm (U : unitary (ColorMatrix N)) (x : Boson N) :
    ‖M.gaugeAction U x‖ = ‖x‖ := by
  have he := M.gaugeConjugate_inner U U.prop x x
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at he
  change ‖M.gaugeAction U x‖^2 = ‖x‖^2 at he
  nlinarith [norm_nonneg (M.gaugeAction U x),norm_nonneg x]

theorem massiveZeros_tube_fiber (hN : 2 ≤ N) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ M.massiveZeros,
      ∀ U V : unitary (ColorMatrix N), ∀ z w : Boson N,
      z ∈ M.normalSlice q → w ∈ M.normalSlice q → ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
      (M.gaugeAction U (q+z) = M.gaugeAction V (q+w) ↔
        V⁻¹*U ∈ M.gaugeStabilizer q ∧ w=M.gaugeAction (V⁻¹*U) z) := by
  obtain ⟨ρ,hρ,hreach⟩ := M.massiveZeros_normal_reach hN
  refine ⟨ρ,hρ,?_⟩
  intro q hq U V z w hz hw hzr hwr
  constructor
  · intro he
    have hUq := M.gaugeConjugate_mem_massiveZeros U U.prop q hq
    have hVq := M.gaugeConjugate_mem_massiveZeros V V.prop q hq
    have hUz := M.normalSlice_equivariant U U.prop q z hz
    have hVw := M.normalSlice_equivariant V V.prop q w hw
    rw [M.gaugeAction_add,M.gaugeAction_add] at he
    have hh := hreach (M.gaugeAction U q) hUq (M.gaugeAction V q) hVq
      (M.gaugeAction U z) (M.gaugeAction V w) hUz hVw
      (by rw [M.gaugeAction_norm]; exact hzr)
      (by rw [M.gaugeAction_norm]; exact hwr) he
    refine ⟨(M.gaugeOrbit_fiber q U V).mp hh.1,?_⟩
    have he' := congrArg (M.gaugeAction V⁻¹) hh.2
    rw [M.gaugeAction_inv,←M.gaugeAction_mul] at he'
    exact he'.symm
  · rintro ⟨hs,rfl⟩
    rw [M.gaugeAction_add,M.gaugeAction_add,←M.gaugeAction_mul]
    have he := (M.gaugeOrbit_fiber q U V).mpr hs
    rw [mul_inv_cancel_left,he]

theorem massiveDistance_normal_tube (hN : 2 ≤ N) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ h : ℝ, 0 < h → ∀ q ∈ M.massiveZeros,
      ∀ z : Boson N, z ∈ M.normalSlice q → h*‖z‖ ≤ ρ →
      M.massiveDistance h (h⁻¹ • q+z) = ‖z‖ := by
  obtain ⟨ρ,hρ,htube,_⟩ := M.massiveZeros_normal_tubes hN
  refine ⟨ρ,hρ,?_⟩
  intro h hh q hq z hz hzr
  have hsz : h • z ∈ M.normalSlice q := (M.normalSlice q).smul_mem h hz
  have hn : ‖h • z‖ = h*‖z‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hh]
  have he := htube q hq (h • z) hsz (hn ▸ hzr)
  have hsc := M.massiveDistance_rescale h hh (h⁻¹ • q+z)
  rw [smul_add,smul_smul,mul_inv_cancel₀ hh.ne',one_smul] at hsc
  rw [he,hn] at hsc
  exact (mul_left_cancel₀ hh.ne' hsc).symm

end
end BFSSQuantum.AlgebraData

end OAI
