import Mathlib
import OAI.MathematicalPhysics.BFSS.MassiveMoments
import OAI.MathematicalPhysics.BFSS.GaugeGeometry

namespace OAI

/-! Uniform potential and energy bounds by distance to the zero set. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset
variable {N : ℕ} (M : BFSSQuantum.AlgebraData N)

lemma potential_uniform_normal_lower (hN : 2 ≤ N) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ q ∈ M.massiveZeros, ∀ z : Boson N,
      z ∈ M.normalSlice q → ‖z‖ ≤ δ →
      c * ‖z‖^2 ≤ M.deformedBosonicPotential 1 1 (q+z) := by
  obtain ⟨c,hc,hcQ⟩ := M.normalQuadratic_uniform_coercive hN
  obtain ⟨C,hC,hCR⟩ := M.quarticRemainder_bound
  refine ⟨c/4,min 1 (c/(4*C)),by positivity,lt_min zero_lt_one (by positivity),?_⟩
  intro q hq z hz hsmall
  have h1 : ‖z‖ ≤ 1 := hsmall.trans (min_le_left _ _)
  have hsq : ‖z‖^2 ≤ ‖z‖ := by nlinarith [norm_nonneg z]
  have h2 : ‖z‖^2 ≤ c/(4*C) :=
    hsq.trans (hsmall.trans (min_le_right _ _))
  have h3 : C * ‖z‖^2 ≤ c/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*C)).mp h2
    nlinarith
  have h4 : C * ‖z‖^4 ≤ (c/4)*‖z‖^2 := by
    have hh := mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖z‖)
    nlinarith [hh]
  have ht := M.potential_taylor_lower q z hq
  have hr := hCR z
  have hq' := hcQ q hq z hz
  linarith

lemma nearest_massive_zero (hN : 2 ≤ N) (x : Boson N) :
    ∃ q ∈ M.massiveZeros, ‖x-q‖ = Metric.infDist x M.massiveZeros ∧
      x-q ∈ M.normalSlice q := by
  obtain ⟨q,hq,he⟩ := (M.massiveZeros_isCompact hN).exists_infDist_eq_dist
    ⟨0,M.zero_mem_massiveZeros⟩ x
  have he' : ‖x-q‖ = Metric.infDist x M.massiveZeros := by simpa only [dist_eq_norm] using he.symm
  refine ⟨q,hq,he',M.nearest_zero_normal x q hq ?_⟩
  intro p hp
  rw [he']
  simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := x) hp

lemma infDist_massiveZeros_le_norm (x : Boson N) : Metric.infDist x M.massiveZeros ≤ ‖x‖ := by
  simpa only [dist_zero_right] using
    Metric.infDist_le_dist_of_mem (x := x) M.zero_mem_massiveZeros

theorem potential_global_distance_lower (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Boson N,
      c * (Metric.infDist x M.massiveZeros)^2 ≤ M.deformedBosonicPotential 1 1 x := by
  obtain ⟨c₀,δ,hc₀,hδ,hlocal⟩ := M.potential_uniform_normal_lower hN
  obtain ⟨cI,hcI,R₀,hI⟩ := M.deformedBosonicPotential_coercive hN
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let K : Set (Boson N) := Metric.closedBall 0 R ∩ {x | δ ≤ Metric.infDist x M.massiveZeros}
  have hK : IsCompact K := (isCompact_closedBall (0:Boson N) R).inter_right
    (isClosed_le continuous_const (Metric.continuous_infDist_pt M.massiveZeros))
  have hpos (x : Boson N) (hx : x ∈ K) : 0 < M.deformedBosonicPotential 1 1 x := by
    have hn : M.deformedBosonicPotential 1 1 x ≠ 0 := by
      intro he
      have hd := Metric.infDist_zero_of_mem (show x ∈ M.massiveZeros from he)
      exact (not_lt_of_ge hx.2) (hd ▸ hδ)
    exact lt_of_le_of_ne (M.potential_nonneg x) hn.symm
  have hlower : ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ K, κ ≤ M.deformedBosonicPotential 1 1 x := by
    rcases Set.eq_empty_or_nonempty K with he|hn
    · refine ⟨1,zero_lt_one,?_⟩
      intro x hx
      rw [he] at hx
      exact hx.elim
    · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hn M.potential_continuous.continuousOn
      exact ⟨_,hpos x hx,fun y hy => hmin hy⟩
  obtain ⟨κ,hκ,hκbound⟩ := hlower
  let c := min c₀ (min cI (κ/R^2))
  have hc : 0 < c := lt_min hc₀ (lt_min hcI (div_pos hκ (sq_pos_of_pos hR)))
  refine ⟨c,hc,?_⟩
  intro x
  have hd0 := Metric.infDist_nonneg (x := x) (s := M.massiveZeros)
  have hdn := M.infDist_massiveZeros_le_norm x
  have hd2 : (Metric.infDist x M.massiveZeros)^2 ≤ ‖x‖^2 :=
    (sq_le_sq₀ hd0 (norm_nonneg x)).mpr hdn
  by_cases hnear : Metric.infDist x M.massiveZeros ≤ δ
  · obtain ⟨q,hq,he,hnormal⟩ := M.nearest_massive_zero hN x
    have hh := hlocal q hq (x-q) hnormal (he ▸ hnear)
    rw [add_sub_cancel] at hh
    rw [he] at hh
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans hh
  · by_cases hfar : R ≤ ‖x‖
    · have hh := hI x ((le_max_left _ _).trans hfar)
      have hc' : c ≤ cI := (min_le_right _ _).trans (min_le_left _ _)
      exact (mul_le_mul_of_nonneg_right hc' (sq_nonneg _)).trans
        ((mul_le_mul_of_nonneg_left hd2 hcI.le).trans hh)
    · have hxn : ‖x‖ ≤ R := (lt_of_not_ge hfar).le
      have hx : x ∈ K := ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxn,
        (lt_of_not_ge hnear).le⟩
      have hdR : (Metric.infDist x M.massiveZeros)^2 ≤ R^2 :=
        hd2.trans ((sq_le_sq₀ (norm_nonneg x) hR.le).mpr hxn)
      have hc' : c ≤ κ/R^2 := (min_le_right _ _).trans (min_le_right _ _)
      calc
        c * (Metric.infDist x M.massiveZeros)^2 ≤ (κ/R^2) * (Metric.infDist x M.massiveZeros)^2 :=
          mul_le_mul_of_nonneg_right hc' (sq_nonneg _)
        _ ≤ (κ/R^2) * R^2 := mul_le_mul_of_nonneg_left hdR (div_nonneg hκ.le (sq_nonneg _))
        _ = κ := div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hR))
        _ ≤ M.deformedBosonicPotential 1 1 x := hκbound x hx
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Finset
open scoped Pointwise
variable {N : ℕ} (M : AlgebraData N)

def massiveDistance (h : ℝ) (x : Boson N) : ℝ :=
  Metric.infDist x (h⁻¹ • M.massiveZeros)

lemma massiveDistance_continuous (h : ℝ) : Continuous (M.massiveDistance h) :=
  Metric.continuous_infDist_pt _

lemma massiveDistance_nonneg (h : ℝ) (x : Boson N) : 0 ≤ M.massiveDistance h x :=
  Metric.infDist_nonneg

lemma massiveDistance_rescale (h : ℝ) (hh : 0 < h) (x : Boson N) :
    Metric.infDist (h • x) M.massiveZeros = h*M.massiveDistance h x := by
  have he := infDist_smul₀ (inv_ne_zero (ne_of_gt hh)) M.massiveZeros (h • x)
  rw [inv_smul_smul₀ (ne_of_gt hh),norm_inv,Real.norm_eq_abs,abs_of_pos hh] at he
  change M.massiveDistance h x = h⁻¹ * Metric.infDist (h • x) M.massiveZeros at he
  rw [he,mul_inv_cancel_left₀ (ne_of_gt hh)]

theorem potential_uniform_distance (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ h : ℝ, 0 < h → ∀ x : Boson N,
      c*(M.massiveDistance h x)^2 ≤ M.deformedBosonicPotential h 1 x := by
  obtain ⟨c,hc,hbound⟩ := M.potential_global_distance_lower hN
  refine ⟨c,hc,?_⟩
  intro h hh x
  have hd := mul_le_mul_of_nonneg_left (hbound (h • x))
    (show 0 ≤ 1/h^2 by positivity)
  rw [M.massiveDistance_rescale h hh] at hd
  rw [M.deformedBosonicPotential_scaling h 1 hh zero_lt_one]
  simp only [one_pow,div_one]
  have he : (1/h^2)*(c*(h*M.massiveDistance h x)^2) = c*(M.massiveDistance h x)^2 := by
    field_simp
  rw [he] at hd
  exact hd

lemma massiveDistance_scaled_norm (hN : 2 ≤ N) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ h : ℝ, 0 < h → ∀ x : Boson N,
      h*‖x‖ ≤ h*M.massiveDistance h x + R := by
  obtain ⟨R,hR⟩ := (M.massiveZeros_isCompact hN).isBounded.exists_norm_le
  refine ⟨R,?_,?_⟩
  · simpa using hR 0 M.zero_mem_massiveZeros
  intro h hh x
  obtain ⟨q,hq,he,_⟩ := M.nearest_massive_zero hN (h • x)
  have ht := norm_add_le (h • x - q) q
  rw [sub_add_cancel, norm_smul,Real.norm_eq_abs,abs_of_pos hh,he,
    M.massiveDistance_rescale h hh] at ht
  linarith [hR q hq]

theorem deformedPotential_fermion_uniform_distance (hN : 2 ≤ N) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ (x : Boson N) (z : Fermion N),
      (c/2*(M.massiveDistance h x)^2-K)*‖z‖^2 ≤
        M.deformedBosonicPotential h 1 x*‖z‖^2 +
          inner ℝ z (M.deformedFermionField h 1 x z) := by
  obtain ⟨c,hc,hu⟩ := M.potential_uniform_distance hN
  obtain ⟨R,hR,hr⟩ := M.massiveDistance_scaled_norm hN
  let A := M.fermionGrowthConstant
  have hA : 0 ≤ A := M.fermionGrowthConstant_nonneg
  let K := A*(R+1)+A^2/(2*c)
  refine ⟨c,K,hc,by dsimp [K]; positivity,?_⟩
  intro h hh h1 x z
  have hd := M.massiveDistance_nonneg h x
  have hx : h*‖x‖+1 ≤ M.massiveDistance h x+R+1 := by
    have he := mul_le_mul_of_nonneg_right h1 hd
    linarith [hr h hh x]
  have hy : c/2*(M.massiveDistance h x)^2-K ≤
      c*(M.massiveDistance h x)^2-A*(M.massiveDistance h x+R+1) := by
    have he : (c*M.massiveDistance h x-A)^2/(2*c) =
        (c*(M.massiveDistance h x)^2-A*(M.massiveDistance h x+R+1)) -
          (c/2*(M.massiveDistance h x)^2-K) := by
      dsimp [K]
      field_simp
      ring
    have hs : 0 ≤ (c*M.massiveDistance h x-A)^2/(2*c) := by positivity
    rw [he] at hs
    linarith
  have hl : c/2*(M.massiveDistance h x)^2-K ≤
      M.deformedBosonicPotential h 1 x - A*(h*‖x‖+1) := by
    have hax := mul_le_mul_of_nonneg_left hx hA
    linarith [hu h hh x]
  have hf := M.deformedFermionField_inner_lower h 1 x z
  rw [abs_of_pos hh,abs_one] at hf
  have hz := mul_le_mul_of_nonneg_right hl (sq_nonneg ‖z‖)
  change -(A*(h*‖x‖+1))*‖z‖^2 ≤ _ at hf
  nlinarith

theorem massive_core_uniform_distance (hN : 2 ≤ N) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SmoothCore N,
      (1/2 : ℝ)*∑ p : SpaceIndex × ColorIndex N,
        ‖coreToL2 (coordinateDerivative p.1 p.2 f)‖^2 +
        c/2*(∫ x : Boson N, (M.massiveDistance h x)^2*‖f x‖^2) ≤
      M.deformedCoreEnergy h 1 f + K*‖coreToL2 f‖^2 := by
  obtain ⟨c,K,hc,hK,hbound⟩ := M.deformedPotential_fermion_uniform_distance hN
  refine ⟨c,K,hc,hK,?_⟩
  intro h hh h1 f
  have hi : Integrable (fun x : Boson N => (c/2*(M.massiveDistance h x)^2-K)*‖f x‖^2) volume :=
    weighted_core_square_integrable _ ((continuous_const.mul ((M.massiveDistance_continuous h).pow 2)).sub continuous_const) f
  have hmom := weighted_core_square_integrable
    (fun x : Boson N => (M.massiveDistance h x)^2) ((M.massiveDistance_continuous h).pow 2) f
  have hn := coreNormSq_integrable f
  have hr := (M.bosonic_core_integrable h 1 f).add (M.fermion_core_integrable h 1 f)
  have hint := integral_mono hi hr (fun x => hbound h hh h1 x (f x))
  have he : (∫ x : Boson N, (c/2*(M.massiveDistance h x)^2-K)*‖f x‖^2) =
      c/2*(∫ x : Boson N, (M.massiveDistance h x)^2*‖f x‖^2) - K*‖coreToL2 f‖^2 := by
    simp_rw [sub_mul,mul_assoc]
    rw [integral_sub (hmom.const_mul _) (hn.const_mul K),integral_const_mul,
      integral_const_mul,←coreToL2_norm_sq]
  rw [he] at hint
  simp only [Pi.add_apply] at hint
  unfold deformedCoreEnergy
  rw [M.averaged_core_energy]
  linarith
end
end BFSSQuantum.AlgebraData

end OAI
