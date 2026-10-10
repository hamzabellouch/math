import Mathlib
import OAI.Probability.SLE.RetainedSeedMoments

namespace OAI

/-! Retained Dyadic Geometry for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
 
def retainedDyadicSquare (k : ℕ) (ij : ℤ × ℤ) : Set ℂ :=
  {z | (ij.1 : ℝ) ≤ (2:ℝ)^k*z.re ∧ (2:ℝ)^k*z.re < (ij.1 : ℝ)+1 ∧
    (ij.2 : ℝ) ≤ (2:ℝ)^k*z.im ∧ (2:ℝ)^k*z.im < (ij.2 : ℝ)+1}
noncomputable def retainedDyadicAddress (k : ℕ) (z : ℂ) : ℤ × ℤ :=
  (⌊(2:ℝ)^k*z.re⌋, ⌊(2:ℝ)^k*z.im⌋)
noncomputable def retainedCandidates (M k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(M:ℤ)*2^k) ((M:ℤ)*2^k)).product
    (Finset.Icc (-(M:ℤ)*2^k) ((M:ℤ)*2^k))

lemma retainedSquare_measurable (k : ℕ) (ij : ℤ × ℤ) :
    MeasurableSet (retainedDyadicSquare k ij) := by
  have hre : Measurable (fun z : ℂ => (2:ℝ)^k*z.re) := by fun_prop
  have him : Measurable (fun z : ℂ => (2:ℝ)^k*z.im) := by fun_prop
  exact (measurableSet_le measurable_const hre).inter
    ((measurableSet_lt hre measurable_const).inter
    ((measurableSet_le measurable_const him).inter (measurableSet_lt him measurable_const)))

lemma retainedSquare_iff_address (k : ℕ) (ij : ℤ × ℤ) (z : ℂ) :
    z ∈ retainedDyadicSquare k ij ↔ retainedDyadicAddress k z = ij := by
  simp only [retainedDyadicSquare, mem_ofPred_eq, retainedDyadicAddress,
    Prod.ext_iff, Int.floor_eq_iff]
  tauto

lemma retainedSquare_address (k : ℕ) (z : ℂ) :
    z ∈ retainedDyadicSquare k (retainedDyadicAddress k z) :=
  (retainedSquare_iff_address _ _ _).mpr rfl

lemma retainedAddress_mem_candidates (M k : ℕ) {z : ℂ} (hz : ‖z‖ ≤ M) :
    retainedDyadicAddress k z ∈ retainedCandidates M k := by
  have hn : 0 ≤ (2:ℝ)^k := by positivity
  have hr : |z.re| ≤ (M:ℝ) := Complex.abs_re_le_norm z |>.trans hz
  have hi : |z.im| ≤ (M:ℝ) := Complex.abs_im_le_norm z |>.trans hz
  have bound (x : ℝ) (hx : |x| ≤ M) :
      -(M:ℤ)*2^k ≤ ⌊(2:ℝ)^k*x⌋ ∧ ⌊(2:ℝ)^k*x⌋ ≤ (M:ℤ)*2^k := by
    constructor
    · apply Int.le_floor.mpr
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp hx).1 hn]
    · apply Int.floor_le_iff.mpr
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp hx).2 hn]
  change (⌊(2:ℝ)^k*z.re⌋, ⌊(2:ℝ)^k*z.im⌋) ∈
    (Finset.Icc (-(M:ℤ)*2^k) ((M:ℤ)*2^k)) ×ˢ
      (Finset.Icc (-(M:ℤ)*2^k) ((M:ℤ)*2^k))
  simpa only [Finset.mem_product, Finset.mem_Icc] using
    And.intro (bound z.re hr) (bound z.im hi)

lemma compact_retained_candidate_radius {K : Set ℂ} (hK : IsCompact K) :
    ∃ M : ℕ, ∀ z ∈ K, ‖z‖ ≤ M := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0:ℂ)
  obtain ⟨M, hM⟩ := exists_nat_ge R
  refine ⟨M, fun z hz => ?_⟩
  have := hR hz
  simpa using (Metric.mem_closedBall.mp this).trans hM

lemma retainedCandidates_cover (M k : ℕ) {K : Set ℂ}
    (hK : ∀ z ∈ K, ‖z‖ ≤ M) :
    K ⊆ ⋃ ij ∈ (retainedCandidates M k : Set (ℤ × ℤ)), retainedDyadicSquare k ij := by
  intro z hz
  exact mem_iUnion.mpr ⟨retainedDyadicAddress k z, mem_iUnion.mpr
    ⟨retainedAddress_mem_candidates M k (hK z hz), retainedSquare_address k z⟩⟩

lemma retainedCandidates_card (M k : ℕ) :
    ((retainedCandidates M k).card : ℝ) = (2*(M:ℝ)*(2:ℝ)^k+1)^2 := by
  have hi : -(M:ℤ)*2^k ≤ (M:ℤ)*2^k + 1 := by
    have hh : (0:ℤ) ≤ (M:ℤ)*2^k := by positivity
    linarith
  have he : ((Finset.Icc (-(M:ℤ)*2^k) ((M:ℤ)*2^k)).card : ℝ) =
      (M:ℝ)*(2:ℝ)^k + 1 - (-(M:ℝ)*(2:ℝ)^k) := by
    exact_mod_cast Int.card_Icc_of_le _ _ hi
  change (((Finset.Icc (-(M:ℤ)*2^k) ((M:ℤ)*2^k)) ×ˢ
    (Finset.Icc (-(M:ℤ)*2^k) ((M:ℤ)*2^k))).card : ℝ) = _
  rw [Finset.card_product, Nat.cast_mul, he]
  ring

lemma retainedCandidates_scale_card (M k : ℕ) :
    ((retainedCandidates M k).card : ℝ) * ((2:ℝ)^(-(k:ℝ)))^2 ≤ (2*(M:ℝ)+1)^2 := by
  rw [retainedCandidates_card, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  have hn : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  have hn0 : 0 < (2:ℝ)^k := by positivity
  have hinv : ((2:ℝ)^k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hid : (2*(M:ℝ)*(2:ℝ)^k+1)^2 * ((2:ℝ)^k)⁻¹^2 =
      (2*(M:ℝ) + ((2:ℝ)^k)⁻¹)^2 := by
        field_simp
  rw [hid]
  gcongr

end SLEExactGauge
end

 
section
open Set Filter Metric Complex
open scoped Topology
namespace SLEExactGauge
noncomputable section
def sourceDyadicCenter (k : ℕ) (ij : ℤ × ℤ) : ℂ :=
  ⟨((ij.1:ℝ)+1/2)*(2:ℝ)^(-(k:ℝ)),((ij.2:ℝ)+1/2)*(2:ℝ)^(-(k:ℝ))⟩
lemma source_dyadic_side_eq (k : ℕ) : (2:ℝ)^(-(k:ℝ)) = (1/2:ℝ)^k := by
  rw [Real.rpow_neg (by norm_num),Real.rpow_natCast,←inv_pow]
  norm_num
lemma source_dyadic_side_pos (k : ℕ) : 0 < (2:ℝ)^(-(k:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
lemma source_dyadic_side_le (k N : ℕ) (h : k ≤ N) : (2:ℝ)^(-(N:ℝ)) ≤ (2:ℝ)^(-(k:ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact neg_le_neg (Nat.cast_le.mpr h)
lemma source_square_subset_ball (k : ℕ) (ij : ℤ × ℤ) :
    retainedDyadicSquare k ij ⊆ ball (sourceDyadicCenter k ij) ((2:ℝ)^(-(k:ℝ))) := by
  let l := (2:ℝ)^(-(k:ℝ))
  have hl : 0 < l := source_dyadic_side_pos k
  have hinv : l*(2:ℝ)^k = 1 := by
    dsimp [l]
    rw [Real.rpow_neg (by norm_num),Real.rpow_natCast,inv_mul_cancel₀ (by positivity)]
  intro z ⟨hr1,hr2,hi1,hi2⟩
  have bound (j x : ℝ) (h1 : j ≤ (2:ℝ)^k*x) (h2 : (2:ℝ)^k*x < j+1) :
      (x-(j+1/2)*l)^2 ≤ (l/2)^2 := by
    have ha := mul_le_mul_of_nonneg_left h1 hl.le
    have hb := mul_lt_mul_of_pos_left h2 hl
    have he : l*((2:ℝ)^k*x) = x := by rw [←mul_assoc,hinv,one_mul]
    rw [he] at ha hb
    nlinarith [sq_nonneg (x-(j+1/2)*l+l/2),sq_nonneg (x-(j+1/2)*l-l/2),
      mul_nonneg (show 0 ≤ x-j*l by nlinarith) (show 0 ≤ (j+1)*l-x by nlinarith)]
  have hr := bound ij.1 z.re hr1 hr2
  have hi := bound ij.2 z.im hi1 hi2
  have hn := norm_nonneg (z-sourceDyadicCenter k ij)
  have hs : ‖z-sourceDyadicCenter k ij‖^2 =
      (z.re-((ij.1:ℝ)+1/2)*l)^2+(z.im-((ij.2:ℝ)+1/2)*l)^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,sourceDyadicCenter,l,pow_two]
  rw [Metric.mem_ball,dist_eq_norm]
  change ‖z-sourceDyadicCenter k ij‖ < l
  nlinarith [sq_pos_of_pos hl]
lemma source_square_center_height (z₀ : ℂ) (k : ℕ) (ij : ℤ × ℤ)
    (hm : (closedBall z₀ 1 ∩ retainedDyadicSquare k ij).Nonempty) :
    z₀.im-2 ≤ (sourceDyadicCenter k ij).im := by
  obtain ⟨z,hzK,hzQ⟩ := hm
  have hd : dist z (sourceDyadicCenter k ij) < (2:ℝ)^(-(k:ℝ)) := source_square_subset_ball k ij hzQ
  have hs : (2:ℝ)^(-(k:ℝ)) ≤ 1 := by
    rw [source_dyadic_side_eq]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hK : dist z z₀ ≤ 1 := hzK
  have ha : abs (z.im-z₀.im) ≤ dist z z₀ := by
    simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-z₀)
  have hb : abs (z.im-(sourceDyadicCenter k ij).im) ≤ dist z (sourceDyadicCenter k ij) := by
    simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-sourceDyadicCenter k ij)
  have := neg_abs_le (z.im-z₀.im)
  have := le_abs_self (z.im-(sourceDyadicCenter k ij).im)
  linarith
lemma source_small_dyadic_level (H : ℝ) (hH : 0 < H) :
    ∃ kmin : ℕ, ∀ k : ℕ, kmin ≤ k →
      4*(2:ℝ)^(-(k:ℝ)) ≤ H ∧
      Real.exp 1*((128*Real.pi)*(4*(2:ℝ)^(-(k:ℝ)))) ≤ 2*H := by
  have ht : Tendsto (fun k : ℕ => (2:ℝ)^(-(k:ℝ))) atTop (𝓝 0) := by
    simp_rw [source_dyadic_side_eq]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have he : ∀ᶠ k : ℕ in atTop, (2:ℝ)^(-(k:ℝ)) <
      min (H/4) (H/(256*Real.pi*Real.exp 1)) :=
    ht.eventually (gt_mem_nhds (lt_min (by positivity) (by positivity)))
  obtain ⟨kmin,he⟩ := eventually_atTop.mp he
  refine ⟨kmin,fun k hk => ?_⟩
  have ha := (lt_min_iff.mp (he k hk)).1
  have hb := (lt_min_iff.mp (he k hk)).2
  constructor
  · linarith
  · have hh := (lt_div_iff₀ (by positivity : 0 < 256*Real.pi*Real.exp 1)).mp hb
    nlinarith
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_finite_mass_le_ball {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (z₀ : ℂ) (r rf : ℝ)
    (hr : 0 < r) (hy : 4*r ≤ z₀.im) (hf : 0 < rf) (hfr : rf ≤ r)
    (T : ℝ≥0) (K : Set ℂ) (hK : K ⊆ ball z₀ r) (ω : a.samples) :
    (finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf T K).toReal ≤
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ r) := by
  have hheight (z : ℂ) (hz : z ∈ ball z₀ r) : rf ≤ z.im := by
    have ha : abs (z.im-z₀.im) ≤ dist z z₀ := by
      simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-z₀)
    have hb := neg_abs_le (z.im-z₀.im)
    have hd : dist z z₀ < r := hz
    linarith
  have hi := a.spatialGreenWeight_spatial_integrable hκ hκ8 rf hf (ball z₀ r)
    measurableSet_ball (measure_ball_lt_top (μ := volume) (x := z₀) (r := r)).ne hheight ω
  have hn (z : ℂ) : 0 ≤ spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z rf := by
    dsimp [spatialGreenWeight]; split_ifs
    · exact le_rfl
    · exact greenDensity_nonneg (a.witness ω) κ _ z
  have hbound : finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf T K ≤
      ENNReal.ofReal (spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ r)) := by
    rw [spatialRealMass,ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)]
    apply (lintegral_mono_set hK).trans
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    split_ifs
    · exact le_rfl
    · exact hn z
  have hrn : 0 ≤ spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ r) :=
    integral_nonneg hn
  simpa only [ENNReal.toReal_ofReal hrn] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourceActualSquareTailTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 2 < z₀.im →
  ∃ (A c : ℝ) (kmin : ℕ), 0 < A ∧ 0 < c ∧
  ∀ (T : ℝ≥0) (N k : ℕ), kmin ≤ k → k ≤ N → ∀ ij : ℤ × ℤ, ∀ u : ℝ, 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | ((2:ℝ)^(-(k:ℝ)))^dimension κ*u <
      (finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω)
        ((2:ℝ)^(-(N:ℝ))) T (closedBall z₀ 1 ∩ retainedDyadicSquare k ij)).toReal} ≤
    ENNReal.ofReal (A*((2:ℝ)^(-(k:ℝ)))^codimension κ*Real.exp (-c*u^(2/codimension κ)))
theorem sourceActualSquareTail_proved : SourceActualSquareTailTarget := by
  intro κ hκ hκ8 Ω m P hP γ a z₀ hz₀
  obtain ⟨C,c,hC,hc,ht⟩ := sourcePhysicalBallAllTail_proved κ hκ hκ8
  let H := z₀.im-2
  have hH : 0 < H := sub_pos.mpr hz₀
  let G := (2:ℝ)^(-codimension κ)*H^(-codimension κ)
  have hG : 0 < G := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hH _)
  obtain ⟨kmin,hkmin⟩ := source_small_dyadic_level H hH
  refine ⟨C*G,c,kmin,mul_pos hC hG,hc,?_⟩
  intro T N k hk hkN ij u hu
  let l := (2:ℝ)^(-(k:ℝ))
  let rf := (2:ℝ)^(-(N:ℝ))
  have hl : 0 < l := source_dyadic_side_pos k
  have hf : 0 < rf := source_dyadic_side_pos N
  have hfl : rf ≤ l := source_dyadic_side_le k N hkN
  have hpos : 0 < l^dimension κ*u := mul_pos (Real.rpow_pos_of_pos hl _) (zero_lt_one.trans_le hu)
  by_cases hmeet : (closedBall z₀ 1 ∩ retainedDyadicSquare k ij).Nonempty
  · let z := sourceDyadicCenter k ij
    have hheight : H ≤ z.im := source_square_center_height z₀ k ij hmeet
    have hy : 4*l ≤ z.im := (hkmin k hk).1.trans hheight
    have hsmall : 1 ≤ Real.log ((2*z.im)/((128*Real.pi)*(4*l))) := by
      apply (Real.le_log_iff_exp_le (div_pos (by linarith) (by positivity))).mpr
      apply (le_div_iff₀ (by positivity : 0 < (128*Real.pi)*(4*l))).mpr
      exact (hkmin k hk).2.trans (mul_le_mul_of_nonneg_left hheight (by norm_num))
    have hgreen : initialGreen κ z ≤ G := by
      apply (initialGreen_le_height κ (by linarith) hκ8 z (hH.trans_le hheight)).trans
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
      exact Real.rpow_le_rpow_of_nonpos hH hheight (neg_nonpos.mpr (codimension_pos κ hκ8).le)
    have hh := ht Ω m P hP γ a z l hl hy hsmall rf u hf hfl hu
    apply le_trans (measure_mono (show {ω : a.samples | l^dimension κ*u <
      (finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf T
        (closedBall z₀ 1 ∩ retainedDyadicSquare k ij)).toReal} ⊆
      {ω | l^dimension κ*u < spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
        (γ ω) (a.G ω) rf (ball z l)} from ?_)) (hh.trans ?_)
    · intro ω hω
      exact hω.trans_le (source_finite_mass_le_ball a (by linarith) hκ8 z l rf hl hy hf hfl T
        _ (fun w hw => source_square_subset_ball k ij hw.2) ω)
    · apply ENNReal.ofReal_le_ofReal
      calc
        C*l^codimension κ*initialGreen κ z*Real.exp (-c*u^(2/codimension κ)) ≤
            C*l^codimension κ*G*Real.exp (-c*u^(2/codimension κ)) := by gcongr
        _ = _ := by ring
  · have he : closedBall z₀ 1 ∩ retainedDyadicSquare k ij = ∅ := not_nonempty_iff_eq_empty.mp hmeet
    have hempty : {ω : a.samples | l^dimension κ*u <
      (finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf T
        (closedBall z₀ 1 ∩ retainedDyadicSquare k ij)).toReal} = ∅ := by
      simp only [he,finiteSpatialGreenMass,Measure.restrict_empty,lintegral_zero_measure,ENNReal.toReal_zero,
        not_lt_of_ge hpos.le,Set.ofPred_false]
    change (P.comap Subtype.val) _ ≤ _
    rw [hempty,measure_empty]
    exact bot_le
end
end SLEExactGauge
end

end OAI
