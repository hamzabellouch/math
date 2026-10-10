import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ConeArgument

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise

namespace RVM

lemma sphere_neg_preserving : MeasurePreserving (Neg.neg : Sphere → Sphere)
    sphereMeasure sphereMeasure := by
  refine ⟨continuous_neg.measurable, ?_⟩
  ext A hA
  rw [Measure.map_apply continuous_neg.measurable hA,
    Measure.toSphere_apply' _ (continuous_neg.measurable hA),
    Measure.toSphere_apply' _ hA]
  have he : (Subtype.val '' ((Neg.neg : Sphere → Sphere) ⁻¹' A) : Set Vec) =
      -(Subtype.val '' A) := by
    ext x
    constructor
    · rintro ⟨n,hn,rfl⟩
      exact ⟨-n,hn,rfl⟩
    · rintro ⟨n,hn,hnx⟩
      exact ⟨-n,by simpa using hn,by simpa using congrArg Neg.neg hnx⟩
  rw [he,Set.smul_neg,Measure.measure_neg]

lemma integral_sphere_neg {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : Sphere → W) :
    (∫ n : Sphere, f (-n) ∂sphereMeasure) = ∫ n : Sphere, f n ∂sphereMeasure :=
  sphere_neg_preserving.integral_comp (MeasurableEquiv.neg Sphere).measurableEmbedding f

def nullConeFlux (s : Solution) (T : ℝ) (x₀ : Vec) (t : ℝ) (n : Sphere) : ℝ :=
  (T-t)^2 * (totalEnergy s (t,x₀-(T-t) • n.1) -
    dot n.1 (totalFlux s (t,x₀-(T-t) • n.1)))

lemma nullConeFlux_spherical_eq (s : Solution) (T t : ℝ) (x₀ : Vec) :
    (∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) =
      ∫ n : Sphere, radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure := by
  rw [← integral_sphere_neg (fun n => nullConeFlux s T x₀ t n)]
  apply integral_congr_ae
  apply ae_of_all
  intro n
  simp only [nullConeFlux,radialConeProfile,coe_neg_sphere,smul_neg,sub_neg_eq_add,
    dot_eq_inner,inner_neg_left]
  ring

lemma classical_null_cone_flux {d : Datum} {s : Solution} (hs : Classical d s)
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Vec) :
    IntegrableOn (fun t => ∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) (Ioo 0 T) ∧
    (∫ t in 0..T, ∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) ≤
      ∫ x : Vec, totalEnergy s (0,x) := by
  simp_rw [nullConeFlux_spherical_eq]
  exact classical_light_cone_flux hs hT x₀

lemma classical_particle_cone_identity {d : Datum} {s : Solution} (hs : Classical d s)
    {t : ℝ} (ht : 0 ≤ t) (x n : Vec) :
    (∫ v : Vec, q v * (1-dot n (velocity v)) * s.f (t,x,v)) =
      particleEnergy s (t,x) - dot n (particleFlux s (t,x)) := by
  obtain ⟨hf,hc⟩ := classical_velocity_slice hs ht x
  have hi : Integrable (fun v : Vec => s.f (t,x,v) • v) :=
    (hf.continuous.smul continuous_id).integrable_of_hasCompactSupport hc.smul_right
  have hqi : Integrable (fun v : Vec => q v * s.f (t,x,v)) :=
    ((contDiff_q (k := 1)).continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hni := (innerSL ℝ n).integrable_comp hi
  have hh := (innerSL ℝ n).integral_comp_comm hi
  simp only [innerSL_apply_apply] at hh hni
  simp only [particleEnergy,particleFlux,dot_eq_inner]
  rw [← hh,← integral_sub hqi hni]
  apply integral_congr_ae
  apply ae_of_all
  intro v
  simp only [inner_smul_right,← dot_eq_inner]
  have hq : q v * dot n (velocity v) = dot n v := by
    simp only [dot,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_left_comm,q_mul_velocity]
  rw [← hq]
  ring

lemma classical_particle_cone_nonneg {d : Datum} {s : Solution} (hs : Classical d s)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) {n : Vec} (hn : ‖n‖ = 1) :
    0 ≤ particleEnergy s (t,x) - dot n (particleFlux s (t,x)) := by
  have hh := dot_le_norm n (particleFlux s (t,x))
  rw [hn,one_mul] at hh
  linarith [classical_particle_flux_bound hs ht x]

def goodConeDensity (s : Solution) (p : ℝ × Vec) (n : Vec) : ℝ :=
  (‖s.E p + cross n (s.B p)‖ + |dot n (s.B p)|)^2 +
    (particleEnergy s p - dot n (particleFlux s p))

lemma goodConeDensity_bounds {d : Datum} {s : Solution} (hs : Classical d s)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) {n : Vec} (hn : ‖n‖=1) :
    0 ≤ goodConeDensity s (t,x) n ∧
      goodConeDensity s (t,x) n ≤ 4*(totalEnergy s (t,x)-dot n (totalFlux s (t,x))) := by
  have hG := good_field_square_le_flux (s.E (t,x)) (s.B (t,x)) n hn
  have hP := classical_particle_cone_nonneg hs ht x hn
  dsimp [goodConeDensity,totalEnergy,totalFlux]
  rw [dot_add_right]
  constructor
  · positivity
  · linarith

lemma goodConeDensity_continuousOn {d : Datum} {s : Solution} (hs : Classical d s)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun p : (ℝ × Vec) × Vec => goodConeDensity s p.1 p.2)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) := by
  have hE : ContinuousOn (fun p : (ℝ × Vec) × Vec => s.E p.1)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) :=
    hs.2.1.continuousOn.comp continuous_fst.continuousOn (by
      intro p hp; exact hp.1.1.1)
  have hB : ContinuousOn (fun p : (ℝ × Vec) × Vec => s.B p.1)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) :=
    hs.2.2.1.continuousOn.comp continuous_fst.continuousOn (by
      intro p hp; exact hp.1.1.1)
  have hF : ContinuousOn (fun p : (ℝ × Vec) × Vec => particleFlux s p.1)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) :=
    (classical_particle_flux_continuous_slab hs hT).comp
      continuous_fst.continuousOn (fun _ h => h.1)
  have hP : ContinuousOn (fun p : (ℝ × Vec) × Vec => particleEnergy s p.1)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) :=
    (classical_particle_energy_continuous_slab hs hT).comp
      continuous_fst.continuousOn (fun _ h => h.1)
  have hc := (contDiff_cross (k := 1)).continuous.comp_continuousOn
    (continuous_snd.continuousOn.prodMk hB)
  simp only [goodConeDensity,dot_eq_inner]
  exact (((hE.add hc).norm.add (continuous_snd.continuousOn.inner hB).abs).pow 2).add
    (hP.sub (continuous_snd.continuousOn.inner hF))

lemma goodConeDensity_cone_continuous {d : Datum} {s : Solution} (hs : Classical d s)
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Vec) :
    ContinuousOn (fun p : ℝ × Sphere =>
      (T-p.1)^2 * goodConeDensity s (p.1,x₀-(T-p.1) • p.2.1) p.2.1) (Icc 0 T ×ˢ univ) := by
  have hn : Continuous (fun p : ℝ × Sphere => p.2.1) := continuous_subtype_val.comp continuous_snd
  have hx : Continuous (fun p : ℝ × Sphere => x₀-(T-p.1) • p.2.1) :=
    continuous_const.sub ((continuous_const.sub continuous_fst).smul hn)
  have hmap : Continuous (fun p : ℝ × Sphere => ((p.1,x₀-(T-p.1) • p.2.1),p.2.1)) :=
    (continuous_fst.prodMk hx).prodMk hn
  have hg : ContinuousOn (fun p : ℝ × Sphere =>
      goodConeDensity s (p.1,x₀-(T-p.1) • p.2.1) p.2.1) (Icc 0 T ×ˢ univ) := by
    apply (goodConeDensity_continuousOn hs hT).comp hmap.continuousOn
    intro p hp
    exact ⟨⟨hp.1,mem_univ _⟩,mem_univ _⟩
  have hw : Continuous (fun p : ℝ × Sphere => (T-p.1)^2) :=
    (continuous_const.sub continuous_fst).pow 2
  convert! hw.continuousOn.mul hg using 1

lemma nullConeFlux_sphere_continuous {d : Datum} {s : Solution} (hs : Classical d s)
    {t : ℝ} (ht : 0 ≤ t) (T : ℝ) (x₀ : Vec) :
    Continuous (fun n : Sphere => nullConeFlux s T x₀ t n) := by
  have hc : Continuous (fun n : Sphere => radialConeProfile s t (T-t) x₀ (T-t) n) :=
    (continuous_radialConeProfile hs ht (T-t) x₀).comp
      (continuous_const.prodMk continuous_id)
  convert! hc.comp continuous_neg using 1
  funext n
  simp only [Function.comp_apply,nullConeFlux,radialConeProfile,coe_neg_sphere,smul_neg,
    ← sub_eq_add_neg,dot_eq_inner,inner_neg_left]
  ring

lemma goodConeDensity_sphere_integral_bound {d : Datum} {s : Solution} (hs : Classical d s)
    {T t : ℝ} (ht : t ∈ Icc 0 T) (x₀ : Vec) :
    (∫ n : Sphere, (T-t)^2 * goodConeDensity s (t,x₀-(T-t) • n.1) n.1 ∂sphereMeasure) ≤
      4*(∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) := by
  rw [← integral_const_mul]
  apply integral_mono
  · have hc := (goodConeDensity_cone_continuous hs (ht.1.trans ht.2) x₀).comp_continuous
      (continuous_const.prodMk continuous_id) (fun n => ⟨ht,mem_univ n⟩)
    exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  · exact integrableOn_univ.mp (((nullConeFlux_sphere_continuous hs ht.1 T x₀).const_mul 4).continuousOn.integrableOn_compact isCompact_univ)
  · intro n
    have hn := (goodConeDensity_bounds hs ht.1 (x₀-(T-t) • n.1) (sphere_norm n)).2
    dsimp [nullConeFlux]
    nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg (T-t))]

lemma goodConeDensity_time_integral_bound {d : Datum} {s : Solution} (hs : Classical d s)
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Vec) :
    (∫ t in 0..T, ∫ n : Sphere,
      (T-t)^2 * goodConeDensity s (t,x₀-(T-t) • n.1) n.1 ∂sphereMeasure) ≤
        4*(∫ x : Vec, totalEnergy s (0,x)) := by
  let F : ℝ → ℝ := fun t => ∫ n : Sphere,
    (T-t)^2 * goodConeDensity s (t,x₀-(T-t) • n.1) n.1 ∂sphereMeasure
  have hFi : ContinuousOn F (Icc 0 T) := by
    apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
      (goodConeDensity_cone_continuous hs hT x₀)
    intro t n _ hn
    exact (hn (mem_univ n)).elim
  have hNi := (classical_null_cone_flux hs hT x₀).1
  have hFint : IntegrableOn F (Ioo 0 T) :=
    (hFi.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hle : (∫ t in Ioo 0 T, F t) ≤
      ∫ t in Ioo 0 T, 4*(∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) := by
    apply integral_mono_ae hFint (hNi.const_mul 4)
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    exact goodConeDensity_sphere_integral_bound hs ⟨ht.1.le,ht.2.le⟩ x₀
  rw [integral_const_mul] at hle
  simp only [restrict_Ioo_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le hT] at hle
  have hbound := (classical_null_cone_flux hs hT x₀).2
  exact le_trans hle (by linarith)

theorem classical_good_cone_energy {d : Datum} {s : Solution} (hs : Classical d s)
    {T : ℝ} (hT : 0 ≤ T) (x₀ : Vec) :
    (∫ t in 0..T, ∫ n : Sphere, (T-t)^2 *
      ((‖s.E (t,x₀-(T-t) • n.1)+cross n.1 (s.B (t,x₀-(T-t) • n.1))‖+
          |dot n.1 (s.B (t,x₀-(T-t) • n.1))|)^2 +
        ∫ v : Vec, q v*(1-dot n.1 (velocity v))*s.f (t,x₀-(T-t) • n.1,v))
          ∂sphereMeasure) ≤ 4*(∫ x : Vec, totalEnergy s (0,x)) := by
  convert! goodConeDensity_time_integral_bound hs hT x₀ using 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  apply integral_congr_ae
  apply ae_of_all
  intro n
  dsimp only
  rw [classical_particle_cone_identity hs ht.1]
  rfl

def velocityProjection (u b : Vec) : Vec := b - dot u b • u

def goodField (E B n : Vec) : ℝ := ‖E+cross n B‖+|dot n B|

lemma velocityProjection_add (u b c : Vec) :
    velocityProjection u (b+c) = velocityProjection u b + velocityProjection u c := by
  simp only [velocityProjection,dot_add_right,add_smul]
  module

lemma velocityProjection_norm (u b : Vec) (hu : ‖u‖ ≤ 1) :
    ‖velocityProjection u b‖ ≤ ‖b‖ := by
  have hsq : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have he : ‖velocityProjection u b‖^2 =
      ‖b‖^2 - 2*(dot u b)^2+(dot u b)^2*‖u‖^2 := by
    rw [velocityProjection,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,inner_smul_right,← dot_eq_inner,dot_comm b u]
    ring
  have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg (dot u b))
  nlinarith [norm_nonneg (velocityProjection u b), norm_nonneg b]

lemma velocityProjection_dot_symm (u b n : Vec) :
    dot n (velocityProjection u b) = dot (velocityProjection u n) b := by
  simp only [velocityProjection,dot_sub_right,dot_sub_left,dot_smul_left,dot_smul_right]
  rw [dot_comm n u]
  ring

lemma norm_velocityProjection_normal (u n : Vec) (hu : ‖u‖ ≤ 1) (hn : ‖n‖=1) :
    ‖velocityProjection u n‖ ≤ Real.sqrt (2*(1-dot n u)) := by
  have hs : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hdot := dot_le_norm n u
  rw [hn,one_mul] at hdot
  have hd : 0 ≤ 2*(1-dot n u) := by linarith
  have he : ‖velocityProjection u n‖^2 =
      1-2*(dot n u)^2+(dot n u)^2*‖u‖^2 := by
    rw [velocityProjection,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,inner_smul_right,← dot_eq_inner,dot_comm u n,hn]
    ring
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg (dot n u))
  have hsq := Real.sq_sqrt hd
  nlinarith [Real.sqrt_nonneg (2*(1-dot n u)),sq_nonneg (1-dot n u)]

lemma cross_sub_left (a b c : Vec) : cross (a-b) c = cross a c-cross b c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma cross_sub_right (a b c : Vec) : cross a (b-c) = cross a b-cross a c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma cross_self (a : Vec) : cross a a=0 := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma cross_normal_decomposition (u n B : Vec) :
    dot n n • cross u B = dot n u • cross n B +
      dot n (cross u B) • n + dot n B • cross u n := by
  ext i
  fin_cases i <;> simp [cross,dot,Fin.sum_univ_succ] <;> ring

lemma magnetic_projection_identity (u n B : Vec) (hn : ‖n‖=1) :
    velocityProjection u (cross (u-n) B) =
      -(1-dot n u) • cross n B - dot n (cross (u-n) B) • (u-n) +
        dot n B • cross u n := by
  have hn' : dot n n=1 := by rw [dot_self,hn]; norm_num
  have hd := cross_normal_decomposition u n B
  rw [hn',one_smul] at hd
  have hc : dot u (cross (u-n) B) = dot n (cross (u-n) B) := by
    have hh := dot_cross_self_left (u-n) B
    rw [dot_sub_left] at hh
    linarith
  unfold velocityProjection
  rw [hc,cross_sub_left]
  have he : dot n (cross u B-cross n B) = dot n (cross u B) := by
    rw [dot_sub_right,dot_cross_self_left,sub_zero]
  rw [he]
  ext i
  have hi := congrArg (fun w : Vec => w i) hd
  simp only [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hi ⊢
  linear_combination hi

lemma magnetic_projection_normal_identity (u n B : Vec) :
    dot n (velocityProjection u (cross (u-n) B)) =
      (1-dot n u)*dot n (cross (u-n) B) := by
  have hc : dot u (cross (u-n) B) = dot n (cross (u-n) B) := by
    have hh := dot_cross_self_left (u-n) B
    rw [dot_sub_left] at hh
    linarith
  simp only [velocityProjection,dot_sub_right,dot_smul_right,hc]
  ring

lemma abs_dot_le (a b : Vec) : |dot a b| ≤ ‖a‖*‖b‖ := by
  rw [dot_eq_inner]
  exact abs_real_inner_le_norm a b

lemma velocity_normal_distance_bound (v n : Vec) (hn : ‖n‖=1) :
    ‖velocity v-n‖ ≤ Real.sqrt (2*(1-dot n (velocity v))) := by
  have hi := cone_angle_identity v n hn
  rw [norm_sub_rev] at hi
  have hd := (cone_denom_pos v n hn).le
  have hh := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hd)
  nlinarith [sq_nonneg ((q v)⁻¹), Real.sqrt_nonneg (2*(1-dot n (velocity v))),
    norm_nonneg (velocity v-n)]

lemma source_energy_rate_bound (v E B n : Vec) (hn : ‖n‖=1) :
    |dot (velocity v) E| ≤ goodField E B n +
      Real.sqrt (2*(1-dot n (velocity v)))*‖B‖ := by
  let u := velocity v
  have he : dot u E = dot u (E+cross n B)-dot (u-n) (cross n B) := by
    rw [dot_add_right,dot_sub_left,dot_cross_self_left]
    ring
  have hh := (abs_sub _ _).trans (add_le_add (abs_dot_le u (E+cross n B))
    (abs_dot_le (u-n) (cross n B)))
  rw [← he] at hh
  have hu : ‖u‖ ≤ 1 := (norm_velocity_lt_one v).le
  have hcross : ‖cross n B‖ ≤ ‖B‖ := by simpa only [hn,one_mul] using norm_cross_le n B
  have hb := mul_le_mul (velocity_normal_distance_bound v n hn) hcross
    (norm_nonneg _) (Real.sqrt_nonneg _)
  have hg := mul_le_mul_of_nonneg_right hu (norm_nonneg (E+cross n B))
  dsimp [goodField]
  dsimp only [u] at hh hg
  linarith [abs_nonneg (dot n B)]

lemma magnetic_projection_bound (v n B : Vec) (hn : ‖n‖=1) :
    ‖velocityProjection (velocity v) (cross (velocity v-n) B)‖ ≤
      3*(1-dot n (velocity v))*‖B‖+|dot n B| := by
  let u := velocity v
  let d := 1-dot n u
  let θ := Real.sqrt (2*d)
  have hd : 0 ≤ d := (cone_denom_pos v n hn).le
  have ht : 0 ≤ θ := Real.sqrt_nonneg _
  have ht2 : θ^2=2*d := Real.sq_sqrt (by positivity)
  have hk : ‖u-n‖ ≤ θ := velocity_normal_distance_bound v n hn
  have hb : ‖cross n B‖ ≤ ‖B‖ := by simpa only [hn,one_mul] using norm_cross_le n B
  have hcn : ‖cross u n‖ ≤ 1 := by
    have hh := norm_cross_le u n
    rw [hn,mul_one] at hh
    exact hh.trans (norm_velocity_lt_one v).le
  have hc : |dot n (cross (u-n) B)| ≤ θ*‖B‖ := by
    have hh := abs_dot_le n (cross (u-n) B)
    rw [hn,one_mul] at hh
    exact hh.trans ((norm_cross_le (u-n) B).trans
      (mul_le_mul_of_nonneg_right hk (norm_nonneg B)))
  have hmul := mul_le_mul hc hk (norm_nonneg _) (mul_nonneg ht (norm_nonneg B))
  have hmul' : |dot n (cross (u-n) B)| *‖u-n‖ ≤ 2*d*‖B‖ := by
    calc
      _ ≤ θ*‖B‖*θ := hmul
      _ = θ^2*‖B‖ := by ring
      _ = 2*d*‖B‖ := by rw [ht2]
  have htri := norm_add_le (-(1-dot n u) • cross n B -
      dot n (cross (u-n) B) • (u-n)) (dot n B • cross u n)
  rw [magnetic_projection_identity _ _ _ hn]
  have hsub := norm_sub_le (-(1-dot n u) • cross n B)
    (dot n (cross (u-n) B) • (u-n))
  simp only [norm_smul,Real.norm_eq_abs,abs_neg] at htri hsub
  rw [abs_of_nonneg hd] at hsub
  have hh₁ := mul_le_mul_of_nonneg_left hb hd
  have hh₂ := mul_le_mul_of_nonneg_left hcn (abs_nonneg (dot n B))
  dsimp only [u,d] at *
  linarith

lemma lorentz_source_acceleration_bound (v E B n : Vec) (hn : ‖n‖=1) :
    ‖fderiv ℝ velocity v (E+cross (velocity v) B)‖ ≤
      (q v)⁻¹*(goodField E B n+3*(1-dot n (velocity v))*‖B‖) := by
  rw [fderiv_velocity_apply,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (q_pos v))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (q_pos v).le)
  have he : E+cross (velocity v) B =
      (E+cross n B)+cross (velocity v-n) B := by
    rw [cross_sub_left]
    module
  change ‖velocityProjection (velocity v) (E+cross (velocity v) B)‖ ≤ _
  rw [he,velocityProjection_add]
  have ht := norm_add_le (velocityProjection (velocity v) (E+cross n B))
      (velocityProjection (velocity v) (cross (velocity v-n) B))
  have hg := velocityProjection_norm (velocity v) (E+cross n B) (norm_velocity_lt_one v).le
  have hb := magnetic_projection_bound v n B hn
  dsimp only [goodField]
  linarith

lemma lorentz_source_normal_acceleration_bound (v E B n : Vec) (hn : ‖n‖=1) :
    |dot n (fderiv ℝ velocity v (E+cross (velocity v) B))| ≤
      (q v)⁻¹*Real.sqrt (2*(1-dot n (velocity v)))*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  let u := velocity v
  let d := 1-dot n u
  let θ := Real.sqrt (2*d)
  have hd : 0 ≤ d := (cone_denom_pos v n hn).le
  have ht : 0 ≤ θ := Real.sqrt_nonneg _
  have he : E+cross u B = (E+cross n B)+cross (u-n) B := by
    rw [cross_sub_left]
    module
  have hg : |dot n (velocityProjection u (E+cross n B))| ≤ θ*‖E+cross n B‖ := by
    rw [velocityProjection_dot_symm]
    exact (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right
      (norm_velocityProjection_normal u n (norm_velocity_lt_one v).le hn) (norm_nonneg _))
  have hb : |dot n (velocityProjection u (cross (u-n) B))| ≤ d*θ*‖B‖ := by
    rw [magnetic_projection_normal_identity,abs_mul,abs_of_nonneg hd]
    have hc : |dot n (cross (u-n) B)| ≤ θ*‖B‖ := by
      have hh := abs_dot_le n (cross (u-n) B)
      rw [hn,one_mul] at hh
      exact hh.trans ((norm_cross_le _ _).trans (mul_le_mul_of_nonneg_right
        (velocity_normal_distance_bound v n hn) (norm_nonneg _)))
    nlinarith [mul_le_mul_of_nonneg_left hc hd]
  have hsum : |dot n (velocityProjection u (E+cross u B))| ≤
      θ*(goodField E B n+d*‖B‖) := by
    rw [he,velocityProjection_add,dot_add_right]
    have hh := abs_add_le (dot n (velocityProjection u (E+cross n B)))
      (dot n (velocityProjection u (cross (u-n) B)))
    dsimp only [goodField]
    nlinarith [mul_nonneg ht (abs_nonneg (dot n B))]
  rw [fderiv_velocity_apply,dot_smul_right,abs_mul,
    abs_of_pos (inv_pos.mpr (q_pos v))]
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (q_pos v).le)
  convert! h using 1; ring

end RVM

end

end OAI
