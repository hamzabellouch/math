import Mathlib
import OAI.Geometry.CubicTorus.Reflection.CoordinateReflection2

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotientMap_nsmul (n : ℕ) (v : Cover) : quotientMap (n • v) = n • quotientMap v := by
  induction n with
  | zero => ext i; simp [quotientMap]
  | succ n ih => simp only [succ_nsmul,quotientMap_add,ih]

lemma torus_same_short_step {a b c : Torus} {δ : ℝ}
    (hsmall : δ < 1/4) (hab : dist a b = δ) (hbc : dist c b = δ)
    (hac : dist c a = 2*δ) : c-b = b-a := by
  let u := shortestLift (c-b)
  let v := -shortestLift (a-b)
  have hu : ‖u‖ = δ := by simpa only [u,norm_shortestLift,←dist_eq_norm] using hbc
  have hv : ‖v‖ = δ := by simpa only [v,norm_neg,norm_shortestLift,←dist_eq_norm] using hab
  have hs : ‖u+v‖ = 2*δ := by
    change ‖shortestLift (c-b)-shortestLift (a-b)‖ = 2*δ
    rw [←shortestLift_sub_local (by rw [hab,hbc]; linarith),
      norm_shortestLift,←dist_eq_norm,hac]
  have he : u=v := eq_of_norm_eq_of_norm_add_eq (hu.trans hv.symm)
    (by rw [hs,hu,hv]; ring)
  have hh := congrArg quotientMap he
  simpa only [u,v,quotientMap_neg,quotientMap_shortestLift,neg_sub] using hh

lemma isometry_straight_step (φ : Torus ≃ᵢ Torus) (x v : Cover) (hv : ‖v‖ < 1/4) :
    φ (quotientMap (x+v+v))-φ (quotientMap (x+v)) =
      φ (quotientMap (x+v))-φ (quotientMap x) := by
  apply torus_same_short_step hv
  · rw [φ.dist_eq,dist_eq_norm,←quotientMap_sub]
    have he : x-(x+v) = -v := by abel
    rw [he,quotientMap_neg,norm_neg,norm_quotientMap_of_small (by linarith)]
  · rw [φ.dist_eq,dist_eq_norm,←quotientMap_sub]
    have he : x+v+v-(x+v) = v := by abel
    rw [he,norm_quotientMap_of_small (by linarith)]
  · rw [φ.dist_eq,dist_eq_norm,←quotientMap_sub]
    have he : x+v+v-x = (2 : ℝ) • v := by module
    rw [he,norm_quotientMap_of_small]
    · simp [norm_smul]
    · rw [norm_smul]; norm_num; linarith

lemma isometry_straight_nsmul (φ : Torus ≃ᵢ Torus) (v : Cover) (hv : ‖v‖ < 1/4) (n : ℕ) :
    φ (quotientMap (n • v)) = n • (φ (quotientMap v)-φ 0)+φ 0 := by
  have hq0 : quotientMap (0 : Cover) = 0 := by ext i; simp [quotientMap]
  have hd : ∀ k : ℕ,φ (quotientMap ((k+1) • v))-φ (quotientMap (k • v)) =
      φ (quotientMap v)-φ 0 := by
    intro k
    induction k with
    | zero => simp [hq0]
    | succ k ih =>
      have hs := isometry_straight_step φ (k • v) v hv
      simpa only [succ_nsmul,add_nsmul,one_nsmul,Nat.succ_eq_add_one] using hs.trans ih
  induction n with
  | zero => simp [hq0]
  | succ n ih =>
    have hh := hd n
    rw [ih] at hh
    have he := sub_eq_iff_eq_add.mp hh
    change φ (quotientMap ((n+1) • v)) = (n+1) • (φ (quotientMap v)-φ 0)+φ 0
    rw [he,add_nsmul,one_nsmul]
    abel

theorem torusIsometry_global_linear (φ : Torus ≃ᵢ Torus) :
    ∃ L : Cover ≃ₗᵢ[ℝ] Cover, ∀ x, φ (quotientMap x) = quotientMap (L x)+φ 0 := by
  obtain ⟨L,hL⟩ := torusIsometry_local_linear φ
  refine ⟨L,fun x ↦ ?_⟩
  obtain ⟨n,hn⟩ := exists_nat_gt (4*‖x‖+1)
  have hnpos : (0 : ℝ) < n := by linarith [norm_nonneg x]
  let v := (n : ℝ)⁻¹ • x
  have hv : ‖v‖ < 1/4 := by
    dsimp only [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hnpos)]
    rw [←div_eq_inv_mul,div_lt_iff₀ hnpos]
    linarith
  have hnV : n • v = x := by
    rw [←Nat.cast_smul_eq_nsmul ℝ]
    dsimp only [v]
    rw [smul_smul,mul_inv_cancel₀ hnpos.ne',one_smul]
  have hg : φ (quotientMap v)-φ 0 = quotientMap (L v) := by
    simpa only [centeredIsometryLift,quotientMap_shortestLift] using congrArg quotientMap (hL v hv)
  have hh := isometry_straight_nsmul φ v hv n
  rw [hnV,hg] at hh
  simpa only [←quotientMap_nsmul,←map_nsmul L,hnV] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem torusIsometry_lattice_translation (φ : Torus ≃ᵢ Torus) :
    ∃ e : LatticeIsometry, ∀ z,φ z=e.torus z+φ 0 := by
  obtain ⟨L,hL⟩ := torusIsometry_global_linear φ
  let ψ : Torus ≃ᵢ Torus :=
    { toFun := fun z ↦ φ z-φ 0
      invFun := fun z ↦ φ.symm (z+φ 0)
      left_inv := by intro z; simp
      right_inv := by intro z; simp
      isometry_toFun := isometry_iff_dist_eq.mpr (by intro x y; simpa only [dist_sub_right] using φ.dist_eq x y) }
  let e : LatticeIsometry :=
    { cover := L
      torus := ψ
      commute := fun x ↦ by change quotientMap (L x)=φ (quotientMap x)-φ 0; rw [hL]; abel }
  refine ⟨e,fun z ↦ ?_⟩
  change φ z=(φ z-φ 0)+φ 0
  abel

theorem torusIsometry_measurePreserving (φ : Torus ≃ᵢ Torus) :
    MeasurePreserving φ torusVolume torusVolume := by
  obtain ⟨e,he⟩ := torusIsometry_lattice_translation φ
  have hf : (fun z : Torus ↦ z+φ 0) ∘ e.torus = φ := by
    funext z
    exact (he z).symm
  rw [←hf]
  exact (measurePreserving_add_right torusVolume (φ 0)).comp e.measurePreserving

theorem perimeter_torusIsometry (φ : Torus ≃ᵢ Torus) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) : perimeter (φ ⁻¹' E)=perimeter E := by
  obtain ⟨e,he⟩ := torusIsometry_lattice_translation φ
  have hs : φ ⁻¹' E = e.torus ⁻¹' ((fun z ↦ z+φ 0) ⁻¹' E) := by
    ext z
    change φ z∈E ↔ e.torus z+φ 0∈E
    rw [he z]
  rw [hs,e.perimeter_eq,
    perimeter_translation hE]
  exact hE.preimage (measurePreserving_add_right torusVolume (φ 0)).quasiMeasurePreserving

lemma finitePerimeter_torusIsometry (φ : Torus ≃ᵢ Torus) {E : Set Torus}
    (hE : FinitePerimeter E) : FinitePerimeter (φ ⁻¹' E) :=
  ⟨hE.1.preimage (torusIsometry_measurePreserving φ).quasiMeasurePreserving,
    by rw [perimeter_torusIsometry φ hE.1]; exact hE.2⟩

theorem isMinimizerAt_torusIsometry (φ : Torus ≃ᵢ Torus) {V : ℝ} {E : Set Torus}
    (hE : IsMinimizerAt V E) : IsMinimizerAt V (φ ⁻¹' E) := by
  refine ⟨finitePerimeter_torusIsometry φ hE.1,?_,?_⟩
  · rw [(torusIsometry_measurePreserving φ).measure_preimage hE.1.1,hE.2.1]
  · intro F hF hv
    rw [perimeter_torusIsometry φ hE.1.1]
    exact hE.2.2 F hF hv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isometry_image_eq_symm_preimage (φ : Torus ≃ᵢ Torus) (F : Set Torus) :
    φ '' F = φ.symm ⁻¹' F := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa using hy
  · intro hx
    exact ⟨φ.symm x,hx,φ.apply_symm_apply x⟩

theorem CongruentAE.symm {E F : Set Torus} (h : CongruentAE E F) : CongruentAE F E := by
  obtain ⟨φ,hφ⟩ := h
  refine ⟨φ.symm,?_⟩
  have hh := (torusIsometry_measurePreserving φ).quasiMeasurePreserving.preimage_ae_eq hφ
  have hs : φ ⁻¹' (φ '' F)=F := by ext x; simp
  rw [hs] at hh
  simpa only [isometry_image_eq_symm_preimage,IsometryEquiv.symm_symm] using hh.symm

lemma CongruentAE.nullMeasurableSet {E F : Set Torus} (h : CongruentAE E F)
    (hF : NullMeasurableSet F torusVolume) : NullMeasurableSet E torusVolume := by
  obtain ⟨φ,hφ⟩ := h
  rw [isometry_image_eq_symm_preimage] at hφ
  exact (hF.preimage (torusIsometry_measurePreserving φ.symm).quasiMeasurePreserving).congr hφ.symm

theorem CongruentAE.perimeter_eq {E F : Set Torus} (h : CongruentAE E F)
    (hF : NullMeasurableSet F torusVolume) : perimeter E=perimeter F := by
  obtain ⟨φ,hφ⟩ := h
  rw [perimeter_congr_ae hφ,isometry_image_eq_symm_preimage,perimeter_torusIsometry φ.symm hF]

theorem CongruentAE.volume_eq {E F : Set Torus} (h : CongruentAE E F)
    (hF : NullMeasurableSet F torusVolume) : torusVolume E=torusVolume F := by
  obtain ⟨φ,hφ⟩ := h
  rw [measure_congr hφ,isometry_image_eq_symm_preimage,
    (torusIsometry_measurePreserving φ.symm).measure_preimage hF]

theorem CongruentAE.isMinimizerAt {E F : Set Torus} {V : ℝ} (h : CongruentAE E F)
    (hF : IsMinimizerAt V F) : IsMinimizerAt V E := by
  obtain ⟨φ,hφ⟩ := h
  rw [isometry_image_eq_symm_preimage] at hφ
  exact (isMinimizerAt_congr_ae hφ).mpr (isMinimizerAt_torusIsometry φ.symm hF)

theorem CongruentAE.isMinimizerAt_iff {E F : Set Torus} {V : ℝ} (h : CongruentAE E F) :
    IsMinimizerAt V E ↔ IsMinimizerAt V F :=
  ⟨h.symm.isMinimizerAt,h.isMinimizerAt⟩

theorem stripe_congruentAE_slab {V : ℝ} (hV : V∈Icc 0 1) :
    CongruentAE (stripe V) (canonicalSlab V) := by
  let K : Set (AddCircle (1 : ℝ)) := {x | ((AddCircle.equivIco (1 : ℝ) 0) x : ℝ)<V}
  have hK : MeasurableSet K := measurableSet_lt
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable) measurable_const
  have he : ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' K ∩ Ioc 0 1 : Set ℝ)
      =ᵐ[volume] Ioo 0 V := by
    filter_upwards [(volume : Measure ℝ).ae_ne (1 : ℝ)] with t ht
    apply propext
    constructor
    · rintro ⟨hK,hI⟩
      have hlt : t<1 := lt_of_le_of_ne hI.2 ht
      have hrep := AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := 0)
        (show t∈Ico 0 (0+1) by exact ⟨hI.1.le,by simpa using hlt⟩)
      change ((AddCircle.equivIco (1 : ℝ) 0) (t : AddCircle (1 : ℝ)) : ℝ)<V at hK
      rw [hrep] at hK
      exact ⟨hI.1,hK⟩
    · intro hI
      have hlt : t<1 := lt_of_lt_of_le hI.2 hV.2
      refine ⟨?_,hI.1,hlt.le⟩
      change ((AddCircle.equivIco (1 : ℝ) 0) (t : AddCircle (1 : ℝ)) : ℝ)<V
      rw [AddCircle.equivIco_coe_of_mem (show t∈Ico 0 (0+1) by exact ⟨hI.1.le,by simpa using hlt⟩)]
      exact hI.2
  have hh := circle_interval_ae_ball hK (show (0 : ℝ)≤0 by rfl) hV.1 (by simpa using hV.2) (by simpa only [zero_add] using he)
  simp only [zero_add,sub_zero] at hh
  have ha := (torus_coordinate_measurePreserving 0).quasiMeasurePreserving.preimage_ae_eq hh
  obtain ⟨φ,hφ⟩ := coordinate_ball_isometric_slab V 0 (((V/2 : ℝ) : AddCircle (1 : ℝ)))
  refine ⟨φ,?_⟩
  rw [hφ]
  exact ha

lemma perimeter_canonicalSlab_le {V : ℝ} (hV : V∈Icc 0 1) :
    perimeter (canonicalSlab V)≤2 := by
  have hh := (stripe_congruentAE_slab hV).perimeter_eq (measurableSet_canonicalSlab V).nullMeasurableSet
  rw [←hh]
  exact perimeter_stripe_le hV

lemma finitePerimeter_canonicalSlab {V : ℝ} (hV : V∈Icc 0 1) :
    FinitePerimeter (canonicalSlab V) :=
  ⟨(measurableSet_canonicalSlab V).nullMeasurableSet,
    (perimeter_canonicalSlab_le hV).trans_lt (by norm_num)⟩

end CubicTorus

end
end

section

namespace CubicTorus.TwoVolume
noncomputable section
open Set Filter
open scoped Topology
open Reduction

def sphereArea (v : ℝ) : ℝ := (9 * Real.pi / 2) ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ)
def tubeArea (v : ℝ) : ℝ := Real.sqrt (Real.pi * v)
def V₁ : ℝ := 4 * Real.pi / 81
def V₂ : ℝ := 1 / Real.pi

def envelope (V : ℝ) : ℝ :=
  let v := min V (1 - V)
  min (sphereArea v) (min (tubeArea v) 1)

lemma transitions : 0 < V₁ ∧ V₁ < V₂ ∧ V₂ < 1 / 2 := by
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hp4 : Real.pi < 4 := Real.pi_lt_four
  dsimp [V₁, V₂]
  constructor
  · positivity
  constructor
  · apply (lt_div_iff₀ hp).2
    nlinarith [sq_nonneg (4 - Real.pi)]
  · apply (div_lt_iff₀ hp).2
    linarith

lemma sphereArea_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ sphereArea v := by
  unfold sphereArea
  positivity

lemma sphereArea_pos {v : ℝ} (hv : 0 < v) : 0 < sphereArea v := by
  unfold sphereArea
  positivity

lemma sphereArea_cube {v : ℝ} (hv : 0 ≤ v) :
    sphereArea v ^ 3 = (9 * Real.pi / 2) * v ^ 2 := by
  have ha : ((9 * Real.pi / 2) ^ (1 / 3 : ℝ)) ^ 3 = 9 * Real.pi / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hb : (v ^ (2 / 3 : ℝ)) ^ 3 = v ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv]
    norm_num
  simp only [sphereArea, mul_pow, ha, hb]

lemma tubeArea_sq {v : ℝ} (hv : 0 ≤ v) : tubeArea v ^ 2 = Real.pi * v := by
  exact Real.sq_sqrt (mul_nonneg Real.pi_pos.le hv)

lemma sphereArea_le_tubeArea_iff {v : ℝ} (hv : 0 < v) :
    sphereArea v ≤ tubeArea v ↔ v ≤ V₁ := by
  have hs := sphereArea_cube hv.le
  have ht := tubeArea_sq hv.le
  have h0 : 0 < Real.pi ^ 2 * v ^ 3 := by positivity
  have h₆ : sphereArea v ^ 6 - tubeArea v ^ 6 =
      (81 / 4 * v - Real.pi) * (Real.pi ^ 2 * v ^ 3) := by
    calc
      _ = (sphereArea v ^ 3) ^ 2 - (tubeArea v ^ 2) ^ 3 := by ring
      _ = _ := by rw [hs, ht]; ring
  have ht0 : 0 ≤ tubeArea v := Real.sqrt_nonneg _
  rw [← pow_le_pow_iff_left₀ (sphereArea_nonneg hv.le) ht0 (by decide : 6 ≠ 0)]
  rw [← sub_nonpos, h₆]
  dsimp [V₁]
  constructor
  · intro h
    by_contra! hn
    have hpos : 0 < 81 / 4 * v - Real.pi := by linarith
    exact (not_lt_of_ge h) (mul_pos hpos h0)
  · intro h
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) h0.le

lemma tubeArea_le_one_iff {v : ℝ} (_ : 0 ≤ v) : tubeArea v ≤ 1 ↔ v ≤ V₂ := by
  rw [tubeArea, Real.sqrt_le_iff]
  norm_num
  simpa [V₂, mul_comm] using (le_div_iff₀ Real.pi_pos : v ≤ 1 / Real.pi ↔ v * Real.pi ≤ 1).symm

lemma sphereArea_zero : sphereArea 0 = 0 := by norm_num [sphereArea]
lemma tubeArea_zero : tubeArea 0 = 0 := by simp [tubeArea]
lemma tubeArea_nonneg (v : ℝ) : 0 ≤ tubeArea v := Real.sqrt_nonneg _
lemma tubeArea_pos {v : ℝ} (hv : 0 < v) : 0 < tubeArea v := by
  exact Real.sqrt_pos.2 (mul_pos Real.pi_pos hv)

lemma sphereArea_eq_tubeArea_V₁ : sphereArea V₁ = tubeArea V₁ := by
  have hs := sphereArea_cube transitions.1.le
  have ht := tubeArea_sq transitions.1.le
  have hp : sphereArea V₁ ^ 6 = tubeArea V₁ ^ 6 := by
    calc
      _ = (sphereArea V₁ ^ 3) ^ 2 := by ring
      _ = (tubeArea V₁ ^ 2) ^ 3 := by rw [hs, ht]; dsimp [V₁]; ring
      _ = _ := by ring
  exact (pow_left_inj₀ (sphereArea_nonneg transitions.1.le) (tubeArea_nonneg _)
    (by decide : (6 : ℕ) ≠ 0)).mp hp

lemma tubeArea_V₂ : tubeArea V₂ = 1 := by
  simp [tubeArea, V₂, ne_of_gt Real.pi_pos]

lemma envelope_compl (v : ℝ) : envelope (1-v) = envelope v := by
  simp only [envelope, show 1-(1-v) = v by ring, min_comm (1-v) v]

lemma envelope_sphere {v : ℝ} (hv : v ∈ Icc 0 V₁) : envelope v = sphereArea v := by
  have hvhalf : v ≤ 1 / 2 := hv.2.trans (transitions.2.1.le.trans transitions.2.2.le)
  have hmin : min v (1-v) = v := min_eq_left (by linarith)
  by_cases hz : v = 0
  · subst v; simp [envelope, sphereArea_zero, tubeArea_zero]
  have hpos : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hz)
  have hst := (sphereArea_le_tubeArea_iff hpos).2 hv.2
  have ht1 := (tubeArea_le_one_iff hv.1).2 (hv.2.trans transitions.2.1.le)
  simp only [envelope, hmin, min_eq_left ht1, min_eq_left hst]

lemma envelope_tube {v : ℝ} (hv : v ∈ Icc V₁ V₂) : envelope v = tubeArea v := by
  have hv0 : 0 < v := transitions.1.trans_le hv.1
  have hvhalf : v ≤ 1 / 2 := hv.2.trans transitions.2.2.le
  have hmin : min v (1-v) = v := min_eq_left (by linarith)
  have hts : tubeArea v ≤ sphereArea v := by
    by_cases heq : v = V₁
    · subst v; exact sphereArea_eq_tubeArea_V₁.ge
    · exact le_of_lt (not_le.1 (fun h => heq (le_antisymm
        ((sphereArea_le_tubeArea_iff hv0).1 h) hv.1)))
  have ht1 := (tubeArea_le_one_iff hv0.le).2 hv.2
  simp only [envelope, hmin, min_eq_left ht1, min_eq_right hts]

lemma envelope_constant {v : ℝ} (hv : v ∈ Icc V₂ (1-V₂)) : envelope v = 1 := by
  let w := min v (1-v)
  have hw : V₂ ≤ w := le_min hv.1 (by linarith [hv.2])
  have hw0 : 0 < w := (transitions.1.trans transitions.2.1).trans_le hw
  have ht1 : 1 ≤ tubeArea w := by
    by_cases heq : w = V₂
    · rw [heq, tubeArea_V₂]
    · exact le_of_lt (not_le.1 (fun h => heq
        (le_antisymm ((tubeArea_le_one_iff hw0.le).1 h) hw)))
  have hst : tubeArea w ≤ sphereArea w := by
    exact le_of_lt (not_le.1 (fun h =>
      (not_lt_of_ge ((sphereArea_le_tubeArea_iff hw0).1 h)) (transitions.2.1.trans_le hw)))
  change min (sphereArea w) (min (tubeArea w) 1) = 1
  rw [min_eq_right ht1, min_eq_right (ht1.trans hst)]

lemma envelope_zero : envelope 0 = 0 := by
  rw [envelope_sphere ⟨le_rfl, transitions.1.le⟩, sphereArea_zero]

lemma envelope_one : envelope 1 = 0 := by
  simpa using envelope_compl 0 |>.trans envelope_zero

lemma continuous_sphereArea : Continuous sphereArea := by
  exact continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num)))

lemma continuous_tubeArea : Continuous tubeArea := by
  exact Real.continuous_sqrt.comp (continuous_const.mul continuous_id)

lemma continuous_envelope : Continuous envelope := by
  have hv : Continuous (fun v : ℝ => min v (1-v)) := continuous_id.min (continuous_const.sub continuous_id)
  exact (continuous_sphereArea.comp hv).min ((continuous_tubeArea.comp hv).min continuous_const)

lemma envelope_pos {v : ℝ} (hv : v ∈ Ioo 0 1) : 0 < envelope v := by
  have hw : 0 < min v (1-v) := lt_min hv.1 (by linarith [hv.2])
  exact lt_min (sphereArea_pos hw) (lt_min (tubeArea_pos hw) zero_lt_one)

lemma ode_power {a p x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ode (fun v : ℝ => a * v ^ p) x = a * p * (2*p-1) * x^p / x^2 := by
  have hx0 := ne_of_gt hx
  have hxp : x ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx p)
  simp only [ode, deriv_const_mul_field', Real.deriv_rpow_const']
  simp only [Real.rpow_sub_one hx0]
  field_simp
  ring

lemma smooth_sphereArea {v : ℝ} (hv : 0 < v) : ContDiffAt ℝ 2 sphereArea v := by
  exact contDiffAt_const.mul (Real.contDiffAt_rpow_const (Or.inl (ne_of_gt hv)))

lemma ode_sphereArea {v : ℝ} (hv : 0 < v) : 0 ≤ ode sphereArea v := by
  change 0 ≤ ode (fun v : ℝ => (9 * Real.pi / 2) ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ)) v
  rw [ode_power (by positivity) hv]
  positivity

lemma tubeArea_power : tubeArea = fun v : ℝ => Real.pi ^ (1/2 : ℝ) * v ^ (1/2 : ℝ) := by
  funext v
  simp only [tubeArea, ← Real.sqrt_eq_rpow, Real.sqrt_mul Real.pi_pos.le]

lemma smooth_tubeArea {v : ℝ} (hv : 0 < v) : ContDiffAt ℝ 2 tubeArea v := by
  rw [tubeArea_power]
  exact contDiffAt_const.mul (Real.contDiffAt_rpow_const (Or.inl (ne_of_gt hv)))

lemma ode_tubeArea {v : ℝ} (hv : 0 < v) : ode tubeArea v = 0 := by
  rw [tubeArea_power, ode_power (by positivity) hv]
  norm_num

lemma ode_eventuallyEq {F G : ℝ → ℝ} {x : ℝ} (h : F =ᶠ[𝓝 x] G) :
    ode F x = ode G x := by
  rw [ode, ode, h.deriv.deriv_eq, h.deriv_eq, h.self_of_nhds]

lemma smooth_ode_sphere {v : ℝ} (hv : v ∈ Ioo 0 V₁) :
    ContDiffAt ℝ 2 envelope v ∧ 0 ≤ ode envelope v := by
  have he : envelope =ᶠ[𝓝 v] sphereArea := by
    filter_upwards [Icc_mem_nhds hv.1 hv.2] with x hx using envelope_sphere hx
  exact ⟨(smooth_sphereArea hv.1).congr_of_eventuallyEq he,
    (ode_eventuallyEq he).symm ▸ ode_sphereArea hv.1⟩

lemma smooth_ode_tube {v : ℝ} (hv : v ∈ Ioo V₁ V₂) :
    ContDiffAt ℝ 2 envelope v ∧ 0 ≤ ode envelope v := by
  have he : envelope =ᶠ[𝓝 v] tubeArea := by
    filter_upwards [Icc_mem_nhds hv.1 hv.2] with x hx using envelope_tube hx
  exact ⟨(smooth_tubeArea (transitions.1.trans hv.1)).congr_of_eventuallyEq he,
    (ode_eventuallyEq he).symm ▸ (ode_tubeArea (transitions.1.trans hv.1)).ge⟩

lemma smooth_ode_constant {v : ℝ} (hv : v ∈ Ioo V₂ (1-V₂)) :
    ContDiffAt ℝ 2 envelope v ∧ 0 ≤ ode envelope v := by
  have he : envelope =ᶠ[𝓝 v] (fun _ => 1) := by
    filter_upwards [Icc_mem_nhds hv.1 hv.2] with x hx using envelope_constant hx
  refine ⟨contDiffAt_const.congr_of_eventuallyEq he, ?_⟩
  rw [ode_eventuallyEq he]
  simp [ode]

lemma candidateProfile_eq_two_envelope (v : ℝ) : candidateProfile v = 2 * envelope v := by
  have hc : (36 * Real.pi) ^ (1/3 : ℝ) = 2 * (9 * Real.pi / 2) ^ (1/3 : ℝ) := by
    have hcube (a : ℝ) (ha : 0 ≤ a) : (a ^ (1/3 : ℝ)) ^ 3 = a := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
      norm_num
    apply (pow_left_inj₀ (by positivity) (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp
    rw [hcube _ (by positivity), mul_pow, hcube _ (by positivity)]
    ring
  simp only [candidateProfile, envelope, sphereArea, tubeArea, hc,
    mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  ring_nf

theorem two_volume_comparison {I : ℝ → ℝ}
    (hI : ContinuousOn I (Icc 0 1))
    (hsym : ∀ x ∈ Icc (0 : ℝ) 1, I (1-x) = I x)
    (hzero : I 0 = 0)
    (hupper : ∀ x ∈ Icc (0 : ℝ) 1, I x ≤ envelope x)
    (hpositive : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < I x)
    (hone : I V₁ = envelope V₁) (htwo : I V₂ = envelope V₂)
    (hsupport : ∀ x ∈ Ioo (0 : ℝ) 1, I x < envelope x →
      ∃ C : ℝ → ℝ, UpperSupport I C x ∧ ode C x < 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, I x = envelope x := by
  have branch (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b)
      (haleft : I a = envelope a) (hbright : I b = envelope b)
      (hregular : ∀ x ∈ Ioo a b, ContDiffAt ℝ 2 envelope x ∧ 0 ≤ ode envelope x) :
      ∀ x ∈ Icc a b, I x = envelope x := by
    exact branch_comparison hab (hI.mono (Icc_subset_Icc ha hb))
      continuous_envelope.continuousOn
      (fun x hx => hupper x ⟨ha.trans hx.1, hx.2.trans hb⟩) haleft hbright
      (fun x hx => hpositive x ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩)
      (fun x hx => (hregular x hx).1) (fun x hx => (hregular x hx).2)
      (fun x hx hh => hsupport x ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩ hh)
  have hv1lt : V₁ < 1 := by linarith [transitions.2.1, transitions.2.2]
  have hv2pos : 0 < V₂ := transitions.1.trans transitions.2.1
  have hfirst := branch 0 V₁ le_rfl hv1lt.le transitions.1
    (hzero.trans envelope_zero.symm) hone (fun _ hx => smooth_ode_sphere hx)
  have hsecond := branch V₁ V₂ transitions.1.le (by linarith [transitions.2.2])
    transitions.2.1 hone htwo (fun _ hx => smooth_ode_tube hx)
  have hmidend : I (1-V₂) = envelope (1-V₂) := by
    rw [hsym V₂ ⟨hv2pos.le, by linarith [transitions.2.2]⟩, envelope_compl, htwo]
  have hmiddle := branch V₂ (1-V₂) hv2pos.le (by linarith)
    (by linarith [transitions.2.2]) htwo hmidend (fun _ hx => smooth_ode_constant hx)
  have hlower : ∀ x ∈ Icc (0 : ℝ) (1/2), I x = envelope x := by
    intro x hx
    by_cases hx1 : x ≤ V₁
    · exact hfirst x ⟨hx.1, hx1⟩
    by_cases hx2 : x ≤ V₂
    · exact hsecond x ⟨(lt_of_not_ge hx1).le, hx2⟩
    · exact hmiddle x ⟨(lt_of_not_ge hx2).le, by linarith [transitions.2.2, hx.2]⟩
  intro x hx
  by_cases hhalf : x ≤ 1/2
  · exact hlower x ⟨hx.1, hhalf⟩
  · rw [← hsym x hx, ← envelope_compl x]
    exact hlower (1-x) ⟨by linarith [hx.2], by linarith⟩

lemma smooth_ode_lower {x : ℝ} (hx : x ∈ Ioc 0 (1/2 : ℝ))
    (hx1 : x ≠ V₁) (hx2 : x ≠ V₂) :
    ContDiffAt ℝ 2 envelope x ∧ 0 ≤ ode envelope x := by
  by_cases h1 : x < V₁
  · exact smooth_ode_sphere ⟨hx.1, h1⟩
  by_cases h2 : x < V₂
  · exact smooth_ode_tube ⟨lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm hx1), h2⟩
  · exact smooth_ode_constant ⟨lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm hx2),
      by linarith [hx.2, transitions.2.2]⟩

theorem exclude_negative_support_lower {I C : ℝ → ℝ} {x : ℝ}
    (heq : ∀ y ∈ Icc (0 : ℝ) 1, I y = envelope y)
    (hx : x ∈ Ioc 0 (1/2 : ℝ)) (hx1 : x ≠ V₁) (hx2 : x ≠ V₂)
    (hs : UpperSupport I C x) : ¬ ode C x < 0 := by
  have hxfull : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
  have hlocal : I =ᶠ[𝓝 x] envelope := by
    filter_upwards [Icc_mem_nhds hxfull.1 hxfull.2] with y hy using heq y hy
  exact no_negative_support hlocal hs (smooth_ode_lower hx hx1 hx2).1
    (envelope_pos hxfull) (smooth_ode_lower hx hx1 hx2).2

end
end CubicTorus.TwoVolume

end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma canonicalBall_radius_lt {V : ℝ} (hV : V∈Ioc 0 (1/2 : ℝ)) :
    (3*V/(4*Real.pi))^(1/3 : ℝ)<1/2 := by
  have hpos := hV.1
  have hc := UpperComparison.cube_cuberoot (3*V/(4*Real.pi)) (by positivity)
  apply (show Odd (3 : ℕ) by decide).strictMono_pow.lt_iff_lt.mp
  rw [hc]
  apply (div_lt_iff₀ (by positivity : 0<4*Real.pi)).mpr
  nlinarith [Real.pi_gt_three,hV.2]

lemma canonicalTube_radius_lt {V : ℝ} (hV : V∈Ioc 0 (1/2 : ℝ)) :
    Real.sqrt (V/Real.pi)<1/2 := by
  have hpos := hV.1
  apply (Real.sqrt_lt (by positivity) (by norm_num : (0 : ℝ)≤1/2)).mpr
  apply (div_lt_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_gt_three,hV.2]

theorem perimeter_canonicalBall_eq {V : ℝ} (hV : V∈Ioc 0 (1/2 : ℝ)) :
    perimeter (canonicalBall V)=ENNReal.ofReal ((36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ)) := by
  obtain ⟨hr0,_,_⟩ := UpperComparison.canonicalBall_radius_properties hV
  rw [canonicalBall,metricBall_perimeter 0 hr0 (canonicalBall_radius_lt hV),
    UpperComparison.ballArea_formula hV.1.le]

theorem perimeter_canonicalTube_eq {V : ℝ} (hV : V∈Ioc 0 (1/2 : ℝ)) :
    perimeter (canonicalTube V)=ENNReal.ofReal (2*Real.sqrt (Real.pi*V)) := by
  obtain ⟨hr0,_,_⟩ := UpperComparison.canonicalTube_radius_properties hV
  change perimeter (UpperComparison.centeredTube _)=_
  rw [UpperComparison.centeredTube_eq_cubeTube_preimage hr0.le,
    perimeter_translation (UpperComparison.measurableSet_cubeTube _).nullMeasurableSet,
    UpperComparison.perimeter_cubeTube_eq hr0 (canonicalTube_radius_lt hV),
    UpperComparison.tubeArea_formula hV.1.le]

theorem perimeter_canonicalSlab_eq {V : ℝ} (hV : V∈Ioo 0 1) :
    perimeter (canonicalSlab V)=2 := by
  let K : Set (AddCircle (1 : ℝ)) := Metric.ball 0 (V/2)
  have heq : (integerCharacter (Pi.single 0 (1 : ℤ))) ⁻¹' K=canonicalSlab V := by
    ext x
    simp [integerCharacter_single,K,Metric.mem_ball,dist_zero_right,canonicalSlab]
  have hm : (Pi.single 0 (1 : ℤ) : Fin 3 → ℤ)≠0 := by
    intro h
    have hh := congrFun h 0
    simp at hh
  have hvol : volume K=ENNReal.ofReal V := by
    rw [← volume_canonicalSlab ⟨hV.1.le,hV.2.le⟩,← heq]
    exact ((integerCharacter_measurePreserving hm).measure_preimage
      Metric.isOpen_ball.measurableSet.nullMeasurableSet).symm
  have hneg : volume Kᶜ≠0 := by
    rw [measure_compl Metric.isOpen_ball.measurableSet (measure_ne_top _ _),hvol]
    apply ne_of_gt
    apply tsub_pos_of_lt
    simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ)<1)).mpr hV.2
  have hP := (finitePerimeter_canonicalSlab ⟨hV.1.le,hV.2.le⟩).2.ne
  have hh := circle_nontrivial_phase_lower_bound hm Metric.isOpen_ball.measurableSet
    (show volume K≠0 by rw [hvol]; exact ne_of_gt (ENNReal.ofReal_pos.mpr hV.1)) hneg
    (show perimeter ((integerCharacter (Pi.single 0 (1 : ℤ))) ⁻¹' K)≠⊤ by rwa [heq])
  have hn : ‖latticeVector (Pi.single 0 (1 : ℤ))‖=1 := by
    have he : latticeVector (Pi.single 0 (1 : ℤ))=EuclideanSpace.single (0 : Fin 3) 1 := by
      ext i
      by_cases hi : i=0 <;> simp [latticeVector,Pi.single_apply,hi]
    rw [he,PiLp.norm_single]
    norm_num
  rw [hn,heq] at hh
  norm_num only [mul_one] at hh
  apply le_antisymm (perimeter_canonicalSlab_le ⟨hV.1.le,hV.2.le⟩)
  exact (ENNReal.toReal_le_toReal (by norm_num) hP).mp (by simpa using hh)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma unit_sphereArea (V : ℝ) :
    (36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ)=2*TwoVolume.sphereArea V := by
  have hc : (36*Real.pi)^(1/3 : ℝ)=2*(9*Real.pi/2)^(1/3 : ℝ) := by
    apply (show Odd (3 : ℕ) by decide).pow_injective
    dsimp only
    rw [mul_pow,UpperComparison.cube_cuberoot _ (by positivity),
      UpperComparison.cube_cuberoot _ (by positivity)]
    ring
  rw [hc,TwoVolume.sphereArea]
  ring

lemma candidateProfile_sphere {V : ℝ} (hV : V∈Icc 0 TwoVolume.V₁) :
    candidateProfile V=(36*Real.pi)^(1/3 : ℝ)*V^(2/3 : ℝ) := by
  rw [TwoVolume.candidateProfile_eq_two_envelope,TwoVolume.envelope_sphere hV,unit_sphereArea]

lemma candidateProfile_tube {V : ℝ} (hV : V∈Icc TwoVolume.V₁ TwoVolume.V₂) :
    candidateProfile V=2*Real.sqrt (Real.pi*V) := by
  rw [TwoVolume.candidateProfile_eq_two_envelope,TwoVolume.envelope_tube hV]
  rfl

lemma candidateProfile_slab {V : ℝ} (hV : V∈Icc TwoVolume.V₂ (1-TwoVolume.V₂)) :
    candidateProfile V=2 := by
  rw [TwoVolume.candidateProfile_eq_two_envelope,TwoVolume.envelope_constant hV,mul_one]

lemma candidateProfile_compl (V : ℝ) : candidateProfile (1-V)=candidateProfile V := by
  rw [TwoVolume.candidateProfile_eq_two_envelope,TwoVolume.candidateProfile_eq_two_envelope,
    TwoVolume.envelope_compl]

lemma CongruentAE.finitePerimeter {E F : Set Torus} (h : CongruentAE E F)
    (hF : FinitePerimeter F) : FinitePerimeter E :=
  ⟨h.nullMeasurableSet hF.1,(h.perimeter_eq hF.1).trans_lt hF.2⟩

theorem SmallStandardRegion.bv_data {V : ℝ} (hV : V∈Ioc 0 (1/2 : ℝ))
    {E : Set Torus} (hE : SmallStandardRegion V E) :
    FinitePerimeter E ∧ torusVolume E=ENNReal.ofReal V ∧
      perimeter E=ENNReal.ofReal (candidateProfile V) := by
  rcases hE with ⟨hsmall,hcong⟩|⟨hlo,hhi,hcong⟩|⟨hlarge,hcong⟩
  · have hF := UpperComparison.finitePerimeter_canonicalBall hV
    refine ⟨hcong.finitePerimeter hF,(hcong.volume_eq hF.1).trans
      (UpperComparison.volume_canonicalBall hV),?_⟩
    rw [hcong.perimeter_eq hF.1,perimeter_canonicalBall_eq hV,
      candidateProfile_sphere ⟨hV.1.le,hsmall⟩]
  · have hF := UpperComparison.finitePerimeter_canonicalTube hV
    refine ⟨hcong.finitePerimeter hF,(hcong.volume_eq hF.1).trans
      (UpperComparison.volume_canonicalTube hV),?_⟩
    rw [hcong.perimeter_eq hF.1,perimeter_canonicalTube_eq hV,
      candidateProfile_tube ⟨hlo,hhi⟩]
  · have h01 : V∈Icc (0 : ℝ) 1 := ⟨hV.1.le,by linarith [hV.2]⟩
    have hF := finitePerimeter_canonicalSlab h01
    refine ⟨hcong.finitePerimeter hF,(hcong.volume_eq hF.1).trans
      (volume_canonicalSlab h01),?_⟩
    rw [hcong.perimeter_eq hF.1,perimeter_canonicalSlab_eq ⟨hV.1,by linarith [hV.2]⟩,
      candidateProfile_slab ⟨hlarge,by linarith [hV.2,TwoVolume.transitions.2.2]⟩]
    norm_num

theorem StandardRegionAt.bv_data {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : StandardRegionAt V E) :
    FinitePerimeter E ∧ torusVolume E=ENNReal.ofReal V ∧
      perimeter E=ENNReal.ofReal (candidateProfile V) := by
  unfold StandardRegionAt at hE
  split_ifs at hE with hv
  · exact hE.bv_data ⟨hV.1,hv⟩
  · obtain ⟨hF,hvol,hP⟩ := hE.bv_data (show 1-V∈Ioc (0 : ℝ) (1/2) by
      constructor <;> linarith [hV.2])
    have hEF := finitePerimeter_compl.mp hF
    refine ⟨hEF,?_,?_⟩
    · have hh := volume_compl_of_volume hF.1 (by linarith [hV.2] : 0≤1-V) hvol
      simpa only [compl_compl,sub_sub_cancel] using hh
    · rw [perimeter_compl hEF.1,candidateProfile_compl] at hP
      exact hP

lemma isMinimizerAt_iff_profile {V : ℝ} (hV : V∈Icc 0 1) {E : Set Torus}
    (hE : FinitePerimeter E) (hvol : torusVolume E=ENNReal.ofReal V) :
    IsMinimizerAt V E ↔ (perimeter E).toReal/2=isoperimetricProfile V := by
  constructor
  · exact fun h ↦ (isoperimetricProfile_eq_of_isMinimizerAt h).symm
  · intro hp
    refine ⟨hE,hvol,?_⟩
    intro F hF hFv
    have hh := isoperimetricProfile_le_competitor hV hF hFv
    rw [←hp] at hh
    exact (ENNReal.toReal_le_toReal hE.2.ne hF.2.ne).mp (by linarith)

theorem StandardRegionAt.minimizer_iff {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : StandardRegionAt V E) :
    IsMinimizerAt V E ↔ isoperimetricProfile V=TwoVolume.envelope V := by
  obtain ⟨hF,hvol,hP⟩ := hE.bv_data hV
  rw [isMinimizerAt_iff_profile ⟨hV.1.le,hV.2.le⟩ hF hvol,hP,
    TwoVolume.candidateProfile_eq_two_envelope,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (TwoVolume.envelope_pos hV).le)]
  constructor <;> intro h <;> linarith

end CubicTorus

end
end

end OAI
