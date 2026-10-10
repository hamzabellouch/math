import OAI.Analysis.PlaneSpectrum.Ergodicity
import OAI.Geometry.PlaneColoring.Coloring

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
def colorValue (i : Fin k) (η : Space k) : ℂ := if η.val 0 = i then 1 else 0
lemma color_memLp (i : Fin k) : MemLp (colorValue k i) 2 (measure k ω) := by
  refine MemLp.of_bound ?_ 1 ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_singleton i).preimage (show Measurable (fun η : Space k => η.val 0) from
      ((continuous_apply (0 : E)).comp continuous_subtype_val).measurable)
  · exact .of_forall fun η => by dsimp [colorValue]; split_ifs <;> simp
abbrev colorVector (i : Fin k) : Hilbert k ω := (color_memLp k ω i).toLp (colorValue k i)
lemma color_ae (i : Fin k) : colorVector k ω i =ᵐ[measure k ω] colorValue k i := (color_memLp k ω i).coeFn_toLp
lemma color_rotation_fixed (i : Fin k) (b : K) :
    (rotation k ω b : Hilbert k ω →L[ℂ] Hilbert k ω) (colorVector k ω i) = colorVector k ω i := by
  rw [rotation_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (colorVector k ω i) (rotate_preserving k ω b),
    (rotate_preserving k ω b).quasiMeasurePreserving.ae (color_ae k ω i),color_ae k ω i] with η h1 h2 h3
  simp only [Function.comp_apply,h1,h2,h3,colorValue,rotate_apply,mul_zero]
lemma color_unit_correlation (i : Fin k) (b : K) :
    ⟪colorVector k ω i,op (representation k ω) (kCoeff b) (colorVector k ω i)⟫_ℂ = 0 := by
  rw [op_apply,L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [color_ae k ω i,Lp.coeFn_compMeasurePreserving (colorVector k ω i) (trans_preserving k ω (kCoeff b)),
    (trans_preserving k ω (kCoeff b)).quasiMeasurePreserving.ae (color_ae k ω i)] with η h1 h2 h3
  simp only [h1,h2,Function.comp_apply,h3,colorValue,trans_apply,zero_add]
  have hp : η.val 0 ≠ η.val (kCoeff b) := η.property 0 (kCoeff b) (by
    change ‖(0 : ℂ)-(b.val:ℂ)‖ = 1
    rw [zero_sub,norm_neg]
    exact Circle.norm_coe b.val)
  by_cases hi : η.val 0 = i
  · have hj : η.val (kCoeff b) ≠ i := fun h => hp (hi.trans h.symm)
    simp [hi,hj]
  · simp [hi]
instance continuous_complete : CompleteSpace (space (A := E) (representation k ω)) :=
  (isClosed_space (A := E) (representation k ω)).completeSpace_coe
def projected (i : Fin k) : Hilbert k ω := (space (A := E) (representation k ω)).starProjection (colorVector k ω i)
lemma projected_range (i : Fin k) : ∀ᵐ η ∂measure k ω,
    ((projected k ω i) η).im = 0 ∧ 0 ≤ ((projected k ω i) η).re ∧ ((projected k ω i) η).re ≤ 1 := by
  apply projection_range (measure k ω) (representation k ω) (trans k) (trans_preserving k ω) (op_apply k ω)
  filter_upwards [color_ae k ω i] with η h
  rw [h]
  dsimp [colorValue]
  split_ifs <;> norm_num
lemma projected_rotation_fixed (i : Fin k) (b : K) :
    (rotation k ω b : Hilbert k ω →L[ℂ] Hilbert k ω) (projected k ω i) = projected k ω i := by
  exact projection_covariance_fixed (representation k ω) (rotation k ω b)
    (Homeomorph.mulLeft₀ (kCoeff b) (kCoeff_ne_zero b)) (mul_zero _)
    (rotation_covariance k ω b) _ (color_rotation_fixed k ω i b)
lemma projected_unit_correlation (i : Fin k) (b : K) :
    ⟪projected k ω i,op (representation k ω) (kCoeff b) (projected k ω i)⟫_ℂ = 0 := by
  have hb := residual_fourier (representation k ω) (rotation k ω) (rotation_covariance k ω)
    (colorVector k ω i-projected k ω i)
    ((space (A := E) (representation k ω)).sub_starProjection_mem_orthogonal (colorVector k ω i))
    (fun b => by rw [map_sub,color_rotation_fixed,projected_rotation_fixed]) (kCoeff b) (kCoeff_ne_zero b)
  exact (projection_coefficient (representation k ω) (colorVector k ω i) (kCoeff b) hb).trans (color_unit_correlation k ω i b)
end PlaneFiveColor.LabelModel
end

noncomputable section
open MeasureTheory Filter Topology
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
def oneVector : Hilbert k ω := (memLp_const (1 : ℂ)).toLp (fun _ : Space k => (1 : ℂ))
lemma one_ae : oneVector k ω =ᵐ[measure k ω] fun _ => (1 : ℂ) := MemLp.coeFn_toLp _
lemma one_fixed (a : E) : op (representation k ω) a (oneVector k ω) = oneVector k ω := by
  rw [op_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (oneVector k ω) (trans_preserving k ω a),
    (trans_preserving k ω a).quasiMeasurePreserving.ae (one_ae k ω),one_ae k ω] with η h1 h2 h3
  exact h1.trans (h2.trans h3.symm)
lemma one_continuous : oneVector k ω ∈ space (A := E) (representation k ω) := by
  change Tendsto (fun a : E => op (representation k ω) a (oneVector k ω)) (𝓝 0) (𝓝 (oneVector k ω))
  simpa only [one_fixed] using (tendsto_const_nhds : Tendsto (fun _ : E => oneVector k ω) (𝓝 0) (𝓝 (oneVector k ω)))
lemma color_sum : ∑ i : Fin k, colorVector k ω i = oneVector k ω := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ) (colorVector k ω),ae_all_iff.mpr (color_ae k ω),one_ae k ω] with η h1 h2 h3
  rw [h1,h3]
  simp_rw [h2,colorValue]
  simp
lemma projected_sum : ∑ i : Fin k, projected k ω i = oneVector k ω := by
  change ∑ i : Fin k, (space (A := E) (representation k ω)).starProjection (colorVector k ω i) = _
  rw [← map_sum,color_sum]
  exact (space (A := E) (representation k ω)).starProjection_eq_self_iff.mpr (one_continuous k ω)
end PlaneFiveColor.LabelModel
end

noncomputable section
open Filter Topology
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral
lemma dense_E : Dense (E : Set ℂ) := by
  intro z
  have hh : ∀ x y : ℝ, (x : ℂ)+(y : ℂ)*Complex.I ∈ closure (E : Set ℂ) := by
    intro x y
    refine (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).induction_on₂
      (p := fun x y : ℝ => (x : ℂ)+(y : ℂ)*Complex.I ∈ closure (E : Set ℂ)) ?_ ?_ x y
    · exact isClosed_closure.preimage ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul_const Complex.I))
    · intro q r
      apply subset_closure
      apply mem_algebraicClosure_iff.mpr
      have hq : IsAlgebraic ℚ ((q : ℝ) : ℂ) := by simpa using isAlgebraic_ratCast ℚ (A := ℂ) q
      have hr : IsAlgebraic ℚ ((r : ℝ) : ℂ) := by simpa using isAlgebraic_ratCast ℚ (A := ℂ) r
      exact hq.add (hr.mul (mem_algebraicClosure_iff.mp imagUnit.property))
  simpa only [Complex.re_add_im] using hh z.re z.im
lemma algebraic_norm (z : E) : IsAlgebraic ℚ (‖(z:ℂ)‖ : ℂ) := by
  have hz : IsAlgebraic ℚ (z : ℂ) := mem_algebraicClosure_iff.mp z.property
  have hc : IsAlgebraic ℚ (conj (z : ℂ)) := hz.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
  apply IsAlgebraic.of_pow (n := 2) (by norm_num)
  simpa only [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_pow] using hz.mul hc
end PlaneFiveColor.Spectral
end

noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.ContinuousVectors
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H))
lemma orbit_uniformContinuous {v : H} (hv : v ∈ space (A := E) U) : UniformContinuous (fun a : E => op U a v) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,h⟩ := Metric.continuousAt_iff.mp (orbit_continuous U hv).continuousAt ε hε
  refine ⟨δ,hδ,fun a b hab => ?_⟩
  have ht : dist (op U (a-b) v) v < ε := by
    have hh := h (show dist (a-b) 0 < δ by simpa only [dist_zero_right,dist_eq_norm,sub_zero] using hab)
    simpa only [op_zero (A := E) U] using hh
  calc
    _ = dist (op U b (op U (a-b) v)) (op U b v) := by
      rw [← op_add (A := E) U]
      congr 2
      abel_nf
    _ = dist (op U (a-b) v) v := dist_op U b _ _
    _ < ε := ht
def orbitExtension (v : H) : ℂ → H := dense_E.extend (fun a : E => op U a v)
lemma orbitExtension_continuous {v : H} (hv : v ∈ space (A := E) U) : Continuous (orbitExtension U v) :=
  (dense_E.uniformContinuous_extend (orbit_uniformContinuous U hv)).continuous
lemma orbitExtension_eq {v : H} (hv : v ∈ space (A := E) U) (a : E) : orbitExtension U v (a : ℂ) = op U a v :=
  dense_E.extend_eq (orbit_continuous U hv) a
lemma orbitExtension_inner {v w : H} (hv : v ∈ space (A := E) U) (hw : w ∈ space (A := E) U) (x y : ℂ) :
    ⟪orbitExtension U v x,orbitExtension U w (x+y)⟫_ℂ = ⟪v,orbitExtension U w y⟫_ℂ := by
  have hc := orbitExtension_continuous U hv
  have hd := orbitExtension_continuous U hw
  refine dense_E.denseRange_val.induction_on₂
    (p := fun x y : ℂ => ⟪orbitExtension U v x,orbitExtension U w (x+y)⟫_ℂ = ⟪v,orbitExtension U w y⟫_ℂ) ?_ ?_ x y
  · exact isClosed_eq ((hc.comp continuous_fst).inner (hd.comp (continuous_fst.add continuous_snd)))
      (continuous_const.inner (hd.comp continuous_snd))
  · intro a b
    change ⟪orbitExtension U v (a : ℂ),orbitExtension U w ((a+b : E) : ℂ)⟫_ℂ = _
    rw [orbitExtension_eq U hv,orbitExtension_eq U hw,orbitExtension_eq U hw,op_add (A := E) U]
    exact Unitary.inner_map_map (U (Multiplicative.ofAdd a)) v (op U b w)
end PlaneFiveColor.Spectral
end

noncomputable section
open Filter Topology
namespace PlaneFiveColor.Spectral
lemma normalized_algebraic (z : E) (hz : z ≠ 0) :
    ∃ b : K, (b.val : ℂ) = (z : ℂ) / (‖(z:ℂ)‖ : ℂ) := by
  have hn : ‖(z:ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (Subtype.coe_ne_coe.mpr hz)
  have hb : ‖(z:ℂ) / (‖(z:ℂ)‖ : ℂ)‖ = 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_self hn]
  have hzalg : IsAlgebraic ℚ (z : ℂ) := mem_algebraicClosure_iff.mp z.property
  exact ⟨⟨⟨_,mem_sphere_zero_iff_norm.mpr hb⟩,
    by
      change IsAlgebraic ℚ ((z : ℂ)/(‖(z:ℂ)‖ : ℂ))
      simpa only [div_eq_mul_inv] using hzalg.mul (algebraic_norm z).inv⟩,rfl⟩
lemma circle_closed_induction {p : ℂ → Prop} (hp : IsClosed {z | p z})
    (halg : ∀ b : K, p (b.val : ℂ)) (u : Circle) : p (u : ℂ) := by
  obtain ⟨s,hs,ht⟩ := mem_closure_iff_seq_limit.mp (dense_E (u : ℂ))
  have hne : ∀ᶠ n in atTop, s n ≠ 0 := ht.eventually (isOpen_compl_singleton.mem_nhds (Circle.coe_ne_zero u))
  have hnorm : Tendsto (fun n => s n / (‖s n‖ : ℂ)) atTop (𝓝 (u : ℂ)) := by
    have h := ht.div (Complex.continuous_ofReal.continuousAt.tendsto.comp ht.norm)
      (show (‖(u:ℂ)‖ : ℂ) ≠ 0 by simp [Circle.norm_coe])
    have he : (u : ℂ) / (‖(u:ℂ)‖ : ℂ) = (u : ℂ) := by simp only [Circle.norm_coe,Complex.ofReal_one,div_one]
    rw [he] at h
    convert h using 1
    rfl
  apply hp.mem_of_tendsto hnorm
  filter_upwards [hne] with n hn
  obtain ⟨b,hb⟩ := normalized_algebraic ⟨s n,hs n⟩ (fun h => hn (congrArg Subtype.val h))
  rw [← hb]
  exact halg b
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
lemma projected_continuous (i : Fin k) : projected k ω i ∈ space (A := E) (representation k ω) :=
  (space (A := E) (representation k ω)).starProjection_apply_mem _
def fieldVector (i : Fin k) (x : ℂ) : Hilbert k ω := orbitExtension (representation k ω) (projected k ω i) x
lemma fieldVector_continuous (i : Fin k) : Continuous (fieldVector k ω i) :=
  orbitExtension_continuous _ (projected_continuous k ω i)
lemma fieldVector_algebraic (i : Fin k) (a : E) : fieldVector k ω i (a : ℂ) = op (representation k ω) a (projected k ω i) :=
  orbitExtension_eq _ (projected_continuous k ω i) a
lemma fieldVector_sum (x : ℂ) : ∑ i : Fin k, fieldVector k ω i x = oneVector k ω := by
  refine dense_E.denseRange_val.induction_on x (isClosed_eq (continuous_finsetSum _ (fun i _ => fieldVector_continuous k ω i)) continuous_const) ?_
  intro a
  simp only [fieldVector_algebraic,← map_sum,projected_sum,one_fixed]
lemma fieldVector_range (i : Fin k) (x : ℂ) : ∀ᵐ η ∂measure k ω,
    (fieldVector k ω i x η).im = 0 ∧ 0 ≤ (fieldVector k ω i x η).re ∧ (fieldVector k ω i x η).re ≤ 1 := by
  have he : clamp_lipschitz.compLp clamp_zero (fieldVector k ω i x) = fieldVector k ω i x := by
    refine dense_E.denseRange_val.induction_on x (isClosed_eq
      ((clamp_lipschitz.continuous_compLp clamp_zero).comp (fieldVector_continuous k ω i)) (fieldVector_continuous k ω i)) ?_
    intro a
    rw [fieldVector_algebraic,op_apply]
    apply Lp.ext
    filter_upwards [clamp_lipschitz.coeFn_compLp clamp_zero (Lp.compMeasurePreserving (trans k a) (trans_preserving k ω a) (projected k ω i)),
      Lp.coeFn_compMeasurePreserving (projected k ω i) (trans_preserving k ω a),
      (trans_preserving k ω a).quasiMeasurePreserving.ae (projected_range k ω i)] with η h1 h2 h3
    simp only [Function.comp_apply] at h1 h2
    rw [h1,h2]
    exact clamp_eq h3
  have ha := clamp_lipschitz.coeFn_compLp clamp_zero (fieldVector k ω i x)
  rw [he] at ha
  filter_upwards [ha] with η hη
  exact hη.symm ▸ clamp_range _
lemma fieldVector_unit_correlation (i : Fin k) (x : ℂ) (u : Circle) :
    ⟪fieldVector k ω i x,fieldVector k ω i (x+u)⟫_ℂ = 0 := by
  rw [show ⟪fieldVector k ω i x,fieldVector k ω i (x+u)⟫_ℂ =
    ⟪projected k ω i,fieldVector k ω i u⟫_ℂ from
    orbitExtension_inner _ (projected_continuous k ω i) (projected_continuous k ω i) x u]
  apply circle_closed_induction (isClosed_eq (continuous_const.inner (fieldVector_continuous k ω i)) continuous_const) _ u
  intro b
  change ⟪projected k ω i,fieldVector k ω i ((kCoeff b : E) : ℂ)⟫_ℂ = 0
  rw [fieldVector_algebraic]
  exact projected_unit_correlation k ω i b
end PlaneFiveColor.LabelModel
end

noncomputable section
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal
namespace EuclideanFiveColor
variable {T X : Type*} [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
  [MeasurableSpace T] [BorelSpace T] [MeasurableSpace X] (μ : Measure X)
  (f : T → Lp ℂ 2 μ) (hf : Continuous f)
include hf
omit [MeasurableSpace T] [BorelSpace T] in
lemma dense_approx (t : T) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, dist (f (TopologicalSpace.denseSeq T n)) (f t) < ε := by
  have h := mem_closure_image hf.continuousAt (TopologicalSpace.denseRange_denseSeq T t)
  rw [← Set.range_comp] at h
  obtain ⟨n,hn⟩ := Metric.mem_closure_range_iff.mp h ε hε
  exact ⟨n,by simpa only [Function.comp_apply,dist_comm] using hn⟩
def approxIndex (n : ℕ) (t : T) : ℕ := Nat.find (dense_approx μ f hf t ((1/2:ℝ)^n) (by positivity))
lemma index_measurable (n : ℕ) : Measurable (approxIndex μ f hf n) := by
  apply measurable_find
  intro j
  exact isOpen_lt (continuous_const.dist hf) continuous_const |>.measurableSet
omit [MeasurableSpace T] [BorelSpace T] in
lemma index_bound (n : ℕ) (t : T) :
    dist (f (TopologicalSpace.denseSeq T (approxIndex μ f hf n t))) (f t) < (1/2:ℝ)^n := by
  unfold approxIndex
  exact Nat.find_spec (dense_approx μ f hf t ((1/2:ℝ)^n) (by positivity))
def approxField (n : ℕ) (p : T × X) : ℂ :=
  f (TopologicalSpace.denseSeq T (approxIndex μ f hf n p.1)) p.2
lemma approxField_measurable (n : ℕ) : Measurable (approxField μ f hf n) := by
  have h : Measurable (fun p : ℕ × X => f (TopologicalSpace.denseSeq T p.1) p.2) :=
    measurable_from_prod_countable_right fun j => (Lp.stronglyMeasurable (f (TopologicalSpace.denseSeq T j))).measurable
  exact h.comp (((index_measurable μ f hf n).comp measurable_fst).prodMk measurable_snd)
omit [MeasurableSpace T] [BorelSpace T] in
lemma approxField_tendsto (t : T) : ∀ᵐ x ∂μ,
    Tendsto (fun n => approxField μ f hf n (t,x)) atTop (𝓝 (f t x)) := by
  let g : ℕ → Lp ℂ 2 μ := fun n => f (TopologicalSpace.denseSeq T (approxIndex μ f hf n t))-f t
  have hs : Summable (fun n => ‖g n‖) := summable_geometric_two.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by simpa only [g,dist_eq_norm] using (index_bound μ f hf n t).le)
  have ha : ∀ᵐ x ∂μ, Summable (fun n => ‖g n x‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1:ℝ≥0∞) ≤ 2)
    simpa only [← Lp.enorm_def] using (tsum_enorm_ne_top_iff_summable_norm.mpr hs)
  have he : ∀ᵐ x ∂μ, ∀ n, g n x = approxField μ f hf n (t,x)-f t x :=
    ae_all_iff.mpr fun n => Lp.coeFn_sub _ _
  filter_upwards [ha,he] with x hx he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [he] using hx.tendsto_atTop_zero
def measurableField (p : T × X) : ℂ :=
  ⟨limsup (fun n => (approxField μ f hf n p).re) atTop,
   limsup (fun n => (approxField μ f hf n p).im) atTop⟩
lemma measurableField_measurable : Measurable (measurableField μ f hf) := by
  have hr := Measurable.limsup fun n => Complex.continuous_re.measurable.comp (approxField_measurable μ f hf n)
  have hi := Measurable.limsup fun n => Complex.continuous_im.measurable.comp (approxField_measurable μ f hf n)
  have hh := (Complex.continuous_ofReal.measurable.comp hr).add ((Complex.continuous_ofReal.measurable.comp hi).mul_const Complex.I)
  convert hh using 1
  funext p
  apply Complex.ext <;> simp [measurableField]
lemma exists_measurable_field : ∃ F : T × X → ℂ, Measurable F ∧ ∀ t, (fun x => F (t,x)) =ᵐ[μ] f t := by
  refine ⟨measurableField μ f hf,?_,?_⟩
  · exact measurableField_measurable μ f hf
  · intro t
    filter_upwards [approxField_tendsto μ f hf t] with x hx
    apply Complex.ext
    · exact (Complex.continuous_re.continuousAt.tendsto.comp hx).limsup_eq
    · exact (Complex.continuous_im.continuousAt.tendsto.comp hx).limsup_eq
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma positive_orthogonal (v w : Lp ℂ 2 μ)
    (hv : ∀ᵐ x ∂μ, (v x).im = 0 ∧ 0 ≤ (v x).re)
    (hw : ∀ᵐ x ∂μ, (w x).im = 0 ∧ 0 ≤ (w x).re)
    (ho : ⟪v,w⟫_ℂ = 0) : ∀ᵐ x ∂μ, (v x).re * (w x).re = 0 := by
  have hi := L2.integrable_inner (𝕜 := ℂ) v w
  have he : (fun x => (⟪v x,w x⟫_ℂ).re) =ᵐ[μ] (fun x => (v x).re * (w x).re) := by
    filter_upwards [hv,hw] with x hx hy
    simp [RCLike.inner_apply,Complex.mul_re,hx.1,hy.1,mul_comm]
  have hh : Integrable (fun x => (v x).re * (w x).re) μ := hi.re.congr he
  apply (integral_eq_zero_iff_of_nonneg_ae _ hh).mp
  · rw [← integral_congr_ae he]
    change (∫ x, RCLike.re (⟪v x,w x⟫_ℂ) ∂μ) = 0
    rw [integral_re hi,← L2.inner_def,ho]
    rfl
  · filter_upwards [hv,hw] with x hx hy
    exact mul_nonneg hx.2 hy.2
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace PlaneFiveColor.LabelModel
open Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
variable (k : ℕ) (ω : Space k)
lemma exists_label_field : ∃ H : Fin k → ℂ × Space k → ℝ,
    (∀ i, Measurable (H i)) ∧
    (∀ x : ℂ, ∀ᵐ η ∂measure k ω, ∑ i, H i (x,η) = 1) ∧
    (∀ x : ℂ, ∀ u : Circle, ∀ᵐ η ∂measure k ω, ∀ i, H i (x,η)*H i (x+u,η) = 0) := by
  have hex (i : Fin k) := exists_measurable_field (measure k ω) (fieldVector k ω i) (fieldVector_continuous k ω i)
  choose F hm hae using hex
  refine ⟨fun i p => (F i p).re,fun i => Complex.continuous_re.measurable.comp (hm i),?_,?_⟩
  · intro x
    have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin k => fieldVector k ω i x)
    rw [fieldVector_sum] at hs
    filter_upwards [ae_all_iff.mpr (fun i => hae i x),hs,one_ae k ω] with η he hs h1
    have hc : ∑ i : Fin k, F i (x,η) = 1 := by
      simp_rw [he]
      exact hs.symm.trans h1
    have hr := congrArg Complex.re hc
    simpa only [map_sum,Complex.re_sum,Complex.one_re] using hr
  · intro x u
    apply ae_all_iff.mpr
    intro i
    have hz := positive_orthogonal (measure k ω) (fieldVector k ω i x) (fieldVector k ω i (x+u))
      ((fieldVector_range k ω i x).mono fun _ h => ⟨h.1,h.2.1⟩)
      ((fieldVector_range k ω i (x+u)).mono fun _ h => ⟨h.1,h.2.1⟩)
      (fieldVector_unit_correlation k ω i x u)
    filter_upwards [hae i x,hae i (x+u),hz] with η h1 h2 h3
    simpa only [h1,h2] using h3
end PlaneFiveColor.LabelModel
end

noncomputable section
open MeasureTheory
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] {k : ℕ} [NeZero k]
def positiveSupport (f : Fin k → X → ℝ) (x : X) : Finset (Fin k) := Finset.univ.filter fun i => 0 < f i x
omit [NeZero k] in
lemma positiveSupport_measurable (f : Fin k → X → ℝ) (hf : ∀ i, Measurable (f i)) : Measurable (positiveSupport f) := by
  apply measurable_finset_iff.mpr
  intro i
  simp only [positiveSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const (hf i))
private def pickSupport (s : Finset (Fin k)) : Fin k := if h : s.Nonempty then h.choose else 0
def positiveSelect (f : Fin k → X → ℝ) (x : X) : Fin k := pickSupport (positiveSupport f x)
lemma positiveSelect_measurable (f : Fin k → X → ℝ) (hf : ∀ i, Measurable (f i)) : Measurable (positiveSelect f) :=
  (measurable_of_countable pickSupport).comp (positiveSupport_measurable f hf)
omit [MeasurableSpace X] in
lemma positiveSelect_pos (f : Fin k → X → ℝ) (x : X) (hs : ∑ i, f i x = 1) : 0 < f (positiveSelect f x) x := by
  have hex : ∃ i, 0 < f i x := by
    by_contra! h
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    linarith
  have hn : (positiveSupport f x).Nonempty := by
    obtain ⟨i,hi⟩ := hex
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  have hmem : positiveSelect f x ∈ positiveSupport f x := by
    simp only [positiveSelect,pickSupport,dite_eq_left hn]
    exact hn.choose_spec
  exact (Finset.mem_filter.mp hmem).2
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter
namespace EuclideanFiveColor
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure S) [SFinite ν]
  (d : S → ℂ) (hd : Measurable d) {k : ℕ} [NeZero k]
include hd
lemma sample_field (H : Fin k → ℂ × Ω → ℝ) (hm : ∀ i, Measurable (H i))
    (hp : ∀ x : ℂ, ∀ᵐ ω ∂μ, ∑ i, H i (x,ω) = 1)
    (ho : ∀ x : ℂ, ∀ s : S, ∀ᵐ ω ∂μ, ∀ i, H i (x,ω)*H i (x+d s,ω) = 0) :
    ∃ c : ℂ → Fin k, Measurable c ∧ ∀ᵐ p ∂(volume : Measure ℂ).prod ν, c p.1 ≠ c (p.1+d p.2) := by
  let c : ℂ × Ω → Fin k := positiveSelect H
  have hc : Measurable c := positiveSelect_measurable H hm
  have ha (p : ℂ × S) : ∀ᵐ ω ∂μ, c (p.1,ω) ≠ c (p.1+d p.2,ω) := by
    filter_upwards [hp p.1,hp (p.1+d p.2),ho p.1 p.2] with ω h1 h2 h3
    intro he
    have hpos1 := positiveSelect_pos H (p.1,ω) h1
    have hpos2 := positiveSelect_pos H (p.1+d p.2,ω) h2
    change 0 < H (c (p.1,ω)) (p.1,ω) at hpos1
    change 0 < H (c (p.1+d p.2,ω)) (p.1+d p.2,ω) at hpos2
    rw [← he] at hpos2
    exact (mul_pos hpos1 hpos2).ne' (h3 _)
  have hm1 : Measurable (fun q : (ℂ × S) × Ω => c (q.1.1,q.2)) :=
    hc.comp ((measurable_fst.fst).prodMk measurable_snd)
  have hm2 : Measurable (fun q : (ℂ × S) × Ω => c (q.1.1+d q.1.2,q.2)) :=
    hc.comp (((measurable_fst.fst).add (hd.comp measurable_fst.snd)).prodMk measurable_snd)
  have hh : ∀ᵐ ω ∂μ, ∀ᵐ p ∂(volume : Measure ℂ).prod ν, c (p.1,ω) ≠ c (p.1+d p.2,ω) :=
    (Measure.ae_ae_comm (measurableSet_eq_fun hm1 hm2).compl).mp (.of_forall ha)
  obtain ⟨ω,hω⟩ := hh.exists
  exact ⟨fun x => c (x,ω),hc.comp (measurable_id.prodMk measurable_const),hω⟩
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory
namespace EuclideanFiveColor
lemma proper_to_borel_weak {k : ℕ} [NeZero k] {c : ℂ → Fin k} (hc : ProperColoring k c) :
    ∃ d : ℂ → Fin k, Measurable d ∧ WeakColoring k d := by
  let ω : PlaneFiveColor.LabelModel.Space k := ⟨fun x => c x,fun x y h => hc x y h⟩
  obtain ⟨H,hm,hp,ho⟩ := PlaneFiveColor.LabelModel.exists_label_field k ω
  obtain ⟨d,hd,hunit⟩ := sample_field (PlaneFiveColor.LabelModel.measure k ω) angularMeasure
    direction direction_continuous.measurable
    H hm hp (fun x t => ho x (AddCircle.toCircle t))
  exact ⟨d,hd,hd.aemeasurable,hunit⟩
lemma proper_to_weak {k : ℕ} [NeZero k] {c : ℂ → Fin k} (hc : ProperColoring k c) :
    ∃ d : ℂ → Fin k, WeakColoring k d := by
  obtain ⟨d,_,h⟩ := proper_to_borel_weak hc
  exact ⟨d,h⟩
end EuclideanFiveColor
end

end OAI
