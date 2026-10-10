import Mathlib
import OAI.Probability.Subsphere.Mixture.BetaTheory

namespace OAI

noncomputable section

namespace SubsphereCurrent.Mixture
section
open MeasureTheory ProbabilityTheory Set

section
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma nested_projection_beta (U N : Submodule ℝ E) (hUN : U ≤ N)
    (hU : 0 < Module.finrank ℝ U) (hN : Module.finrank ℝ U < Module.finrank ℝ N) :
    MeasurePreserving (fun x : N => ‖U.orthogonalProjectionOnto (x : E)‖^2)
      SubsphereRegression.ambientSphereLaw
      (betaMeasure ((Module.finrank ℝ U : ℝ)/2)
        (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ U : ℝ))/2)) := by
  let H := U.comap N.subtype
  have hH : Module.finrank ℝ H = Module.finrank ℝ U := nested_rank U N hUN
  have hdim := H.finrank_add_finrank_orthogonal
  have hHc : 0 < Module.finrank ℝ Hᗮ := by omega
  let : Nontrivial N := Module.nontrivial_of_finrank_pos (R := ℝ) (M := N) (by omega)
  let : Nontrivial H := Module.nontrivial_of_finrank_pos (hH ▸ hU)
  let : Nontrivial Hᗮ := Module.nontrivial_of_finrank_pos hHc
  have hc : (Module.finrank ℝ Hᗮ : ℝ) =
      (Module.finrank ℝ N : ℝ)-(Module.finrank ℝ U : ℝ) := by
    have hd : (Module.finrank ℝ H : ℝ)+(Module.finrank ℝ Hᗮ : ℝ) = Module.finrank ℝ N := by
      exact_mod_cast hdim
    rw [hH] at hd
    linarith
  have he : (fun x : N => ‖H.orthogonalProjectionOnto x‖^2) =
      (fun x : N => ‖U.orthogonalProjectionOnto (x : E)‖^2) := by
    funext x
    rw [nested_projection_norm U N hUN]
  simpa only [he,hH,hc] using sphere_projection_beta H

lemma nested_perp_beta (U N : Submodule ℝ E) (hUN : U ≤ N)
    (hU : 0 < Module.finrank ℝ U) (hN : Module.finrank ℝ U < Module.finrank ℝ N) :
    MeasurePreserving (fun x : N => ‖Uᗮ.orthogonalProjectionOnto (x : E)‖^2)
      SubsphereRegression.ambientSphereLaw
      (betaMeasure (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ U : ℝ))/2)
        ((Module.finrank ℝ U : ℝ)/2)) := by
  let H := U.comap N.subtype
  have hH : Module.finrank ℝ H = Module.finrank ℝ U := nested_rank U N hUN
  have hdim := H.finrank_add_finrank_orthogonal
  have hHc : 0 < Module.finrank ℝ Hᗮ := by omega
  let : Nontrivial N := Module.nontrivial_of_finrank_pos (R := ℝ) (M := N) (by omega)
  let : Nontrivial H := Module.nontrivial_of_finrank_pos (hH ▸ hU)
  let : Nontrivial Hᗮ := Module.nontrivial_of_finrank_pos hHc
  let : Nontrivial Hᗮᗮ := by simpa using (inferInstance : Nontrivial H)
  have hc : (Module.finrank ℝ Hᗮ : ℝ) =
      (Module.finrank ℝ N : ℝ)-(Module.finrank ℝ U : ℝ) := by
    have hd : (Module.finrank ℝ H : ℝ)+(Module.finrank ℝ Hᗮ : ℝ) = Module.finrank ℝ N := by
      exact_mod_cast hdim
    rw [hH] at hd
    linarith
  have he : (fun x : N => ‖Hᗮ.orthogonalProjectionOnto x‖^2) =
      (fun x : N => ‖Uᗮ.orthogonalProjectionOnto (x : E)‖^2) := by
    funext x
    rw [nested_orthogonal_projection_norm U N hUN]
  have hHcc : Module.finrank ℝ Hᗮᗮ = Module.finrank ℝ H :=
    congrArg (fun S : Submodule ℝ N => Module.finrank ℝ S) (Submodule.orthogonal_orthogonal H)
  simpa only [he,hHcc,hH,hc] using sphere_projection_beta Hᗮ


lemma measurable_directionSampler (V N : Submodule ℝ E) :
    Measurable (fun z : Orthogonal Vᗮ × N => blockIso V 1 z.1 (z.2 : E)) :=
  ((continuous_blockIso V).comp
    ((continuous_const.prodMk continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).measurable

instance directionLaw_probability (V N : Submodule ℝ E) [Nontrivial N] :
    IsProbabilityMeasure (directionLaw V N) := by
  unfold directionLaw
  infer_instance

lemma directionLaw_unit (V N : Submodule ℝ E) [Nontrivial N] :
    ∀ᵐ x ∂directionLaw V N, ‖x‖ = 1 := by
  rw [directionLaw,ae_map_iff (measurable_directionSampler V N).aemeasurable (by measurability)]
  have h : ∀ᵐ z : Orthogonal Vᗮ × N ∂(orthogonalLaw (E := Vᗮ)).prod
      SubsphereRegression.ambientSphereLaw, ‖z.2‖ = 1 :=
    measurePreserving_snd.quasiMeasurePreserving.ae SubsphereRegression.ambientSphereLaw_ae_norm
  filter_upwards [h] with z hz
  simpa using hz

lemma directionLaw_invariant (V N : Submodule ℝ E) [Nontrivial N] (hVN : V ≤ N)
    (u : Orthogonal V) (w : Orthogonal Vᗮ) :
    MeasurePreserving (blockIso V u w) (directionLaw V N) (directionLaw V N) := by
  let r := restrictIso N (blockIso V u 1) (block_left_stable V N hVN u)
  have hr : MeasurePreserving r SubsphereRegression.ambientSphereLaw
      SubsphereRegression.ambientSphereLaw := SubsphereRegression.ambientSphereLaw_isometry r
  have hg := (measurePreserving_mul_left (orthogonalLaw (E := Vᗮ)) w).prod hr
  apply preserving_map_of_intertwining (measurable_directionSampler V N) hg
    (blockIso V u w).continuous.measurable
  intro z
  change blockIso V 1 (w*z.1) (blockIso V u 1 (z.2 : E)) =
    blockIso V u w (blockIso V 1 z.1 (z.2 : E))
  rw [← blockIso_mul,← blockIso_mul]
  simp

lemma directionLaw_beta (V N : Submodule ℝ E) (hVN : V ≤ N)
    (hV : 0 < Module.finrank ℝ V) (hN : Module.finrank ℝ V < Module.finrank ℝ N) :
    MeasurePreserving (perpCoordinate V) (directionLaw V N)
      (betaMeasure (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ V : ℝ))/2)
        ((Module.finrank ℝ V : ℝ)/2)) := by
  let : Nontrivial N := Module.nontrivial_of_finrank_pos (R := ℝ) (M := N) (by omega)
  have h := (nested_perp_beta V N hVN hV hN).comp
    (measurePreserving_snd (μ := orthogonalLaw (E := Vᗮ)))
  refine ⟨measurable_perpCoordinate V,?_⟩
  rw [directionLaw,Measure.map_map (measurable_perpCoordinate V) (measurable_directionSampler V N)]
  calc
    _ = Measure.map (fun z : Orthogonal Vᗮ × N => perpCoordinate V (z.2 : E))
        ((orthogonalLaw (E := Vᗮ)).prod SubsphereRegression.ambientSphereLaw) := by
      congr 1
      funext z
      exact perpCoordinate_blockIso V 1 z.1 (z.2 : E)
    _ = _ := h.map_eq


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma latitude_norm (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (x : latitudeSpace V e) (hx : ‖x‖ = 1) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖Real.sqrt (1-q) • (e.val : E)+Real.sqrt q • (x : E)‖ = 1 := by
  have ho : ⟪Real.sqrt (1-q) • (e.val : E),Real.sqrt q • (x : E)⟫ = 0 := by
    have := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.prop
    simp [real_inner_smul_left,real_inner_smul_right,this]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real ho
  have hn : ‖(x : E)‖ = 1 := hx
  simp only [← pow_two,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    latitude_e_norm V e,hn,mul_one,Real.sq_sqrt (sub_nonneg.mpr hq1),Real.sq_sqrt hq] at h
  nlinarith [norm_nonneg (Real.sqrt (1-q) • (e.val : E)+Real.sqrt q • (x : E))]

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_coordinate (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (u : Orthogonal V) (x : latitudeSpace V e) {q : ℝ} (hq : 0 ≤ q) :
    perpCoordinate V (blockIso V u 1
      (Real.sqrt (1-q) • (e.val : E)+Real.sqrt q • (x : E))) =
      q * perpCoordinate V (x : E) := by
  rw [perpCoordinate_blockIso,perpCoordinate,map_add,map_smul,map_smul,
    Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)]
  simp only [smul_zero,zero_add,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hq,perpCoordinate]

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_rank_one (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (hV : Module.finrank ℝ V = 1) : latitudeSpace V e = Vᗮ := by
  have he : (e.val : E) ≠ 0 := by intro h; have := latitude_e_norm V e; simp [h] at this
  have hspan : ℝ ∙ (e.val : E) = V := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by simp)
    · rw [finrank_span_singleton he,hV]
  exact congrArg Submodule.orthogonal hspan

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_coordinate_rank_one (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (hV : Module.finrank ℝ V = 1) (x : latitudeSpace V e) :
    perpCoordinate V (x : E) = ‖x‖^2 := by
  have hx : (x : E) ∈ Vᗮ := (latitude_rank_one V e hV) ▸ x.prop
  unfold perpCoordinate
  change ‖Vᗮ.starProjection (x : E)‖^2 = ‖(x : E)‖^2
  rw [Submodule.starProjection_eq_self_iff.mpr hx]


lemma measurable_latitudeSampler (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) :
    Measurable (fun z : ℝ × (Orthogonal V × latitudeSpace V e) => blockIso V z.2.1 1
      (Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • (z.2.2 : E))) :=
  ((continuous_blockIso V).comp
    (((continuous_fst.comp continuous_snd).prodMk continuous_const).prodMk
      (((continuous_const.sub continuous_fst).sqrt.smul continuous_const).add
        (continuous_fst.sqrt.smul (continuous_subtype_val.comp
          (continuous_snd.comp continuous_snd)))))).measurable

lemma latitudeLaw_probability (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    [Nontrivial (latitudeSpace V e)] {a delta : ℝ} (ha : 0 < a) (hd : 0 < delta) :
    IsProbabilityMeasure (latitudeLaw V e a delta) := by
  let : IsProbabilityMeasure (betaMeasure a delta) := isProbabilityMeasureBeta ha hd
  unfold latitudeLaw
  infer_instance

lemma latitudeLaw_unit (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    [Nontrivial (latitudeSpace V e)] {a delta : ℝ} (ha : 0 < a) (hd : 0 < delta) :
    ∀ᵐ x ∂latitudeLaw V e a delta, ‖x‖ = 1 := by
  let : IsProbabilityMeasure (betaMeasure a delta) := isProbabilityMeasureBeta ha hd
  let μ := (betaMeasure a delta).prod ((orthogonalLaw (E := V)).prod
    (SubsphereRegression.ambientSphereLaw (E := latitudeSpace V e)))
  have hq : ∀ᵐ z : ℝ × (Orthogonal V × latitudeSpace V e) ∂μ, z.1 ∈ Ioo (0 : ℝ) 1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae (beta_ae_mem a delta)
  have hx : ∀ᵐ z : ℝ × (Orthogonal V × latitudeSpace V e) ∂μ, ‖z.2.2‖ = 1 :=
    (measurePreserving_snd.comp measurePreserving_snd).quasiMeasurePreserving.ae
      SubsphereRegression.ambientSphereLaw_ae_norm
  rw [latitudeLaw,ae_map_iff (measurable_latitudeSampler V e).aemeasurable (by measurability)]
  filter_upwards [hq,hx] with z hz hzx
  simpa only [LinearIsometryEquiv.norm_map] using
    latitude_norm V e z.2.2 hzx hz.1.le hz.2.le

lemma latitudeLaw_invariant (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    [Nontrivial (latitudeSpace V e)] {a delta : ℝ} (ha : 0 < a) (hd : 0 < delta)
    (u : Orthogonal V) (w : Orthogonal Vᗮ) :
    MeasurePreserving (blockIso V u w) (latitudeLaw V e a delta) (latitudeLaw V e a delta) := by
  let : IsProbabilityMeasure (betaMeasure a delta) := isProbabilityMeasureBeta ha hd
  let r := restrictIso (latitudeSpace V e) (blockIso V 1 w) (block_right_latitude_stable V e w)
  have hr : MeasurePreserving r SubsphereRegression.ambientSphereLaw
      SubsphereRegression.ambientSphereLaw := SubsphereRegression.ambientSphereLaw_isometry r
  have hg := (MeasurePreserving.id (betaMeasure a delta)).prod
    ((measurePreserving_mul_left (orthogonalLaw (E := V)) u).prod hr)
  apply preserving_map_of_intertwining (measurable_latitudeSampler V e) hg
    (blockIso V u w).continuous.measurable
  intro z
  change blockIso V (u*z.2.1) 1
      (Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • blockIso V 1 w (z.2.2 : E)) =
    blockIso V u w (blockIso V z.2.1 1
      (Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • (z.2.2 : E)))
  have he : Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • blockIso V 1 w (z.2.2 : E) =
      blockIso V 1 w (Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • (z.2.2 : E)) := by
    simp only [map_add,map_smul,block_right_fix_e]
  rw [he,← blockIso_mul,← blockIso_mul]
  simp

end
open scoped ENNReal NNReal

lemma beta_product_preserving {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    MeasurePreserving (fun z : ℝ × ℝ => z.1*z.2)
      ((betaMeasure a b).prod (betaMeasure (a+b) c)) (betaMeasure a (b+c)) := by
  let : IsProbabilityMeasure (gammaMeasure a 1) := isProbabilityMeasure_gammaMeasure ha (by norm_num)
  let : IsProbabilityMeasure (gammaMeasure b 1) := isProbabilityMeasure_gammaMeasure hb (by norm_num)
  let : IsProbabilityMeasure (gammaMeasure c 1) := isProbabilityMeasure_gammaMeasure hc (by norm_num)
  let : IsProbabilityMeasure (gammaMeasure (a+b) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) (by norm_num)
  let : IsProbabilityMeasure (gammaMeasure (b+c) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos hb hc) (by norm_num)
  let : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  let μ := ((gammaMeasure a 1).prod (gammaMeasure b 1)).prod (gammaMeasure c 1)
  have hF : MeasurePreserving
      (fun z : (ℝ × ℝ) × ℝ => (z.1.1/(z.1.1+z.1.2),(z.1.1+z.1.2)/(z.1.1+z.1.2+z.2)))
      μ ((betaMeasure a b).prod (betaMeasure (a+b) c)) := by
    exact ((MeasurePreserving.id (betaMeasure a b)).prod (gamma_ratio_preserving (add_pos ha hb) hc)).comp
      ((measurePreserving_prodAssoc (betaMeasure a b) (gammaMeasure (a+b) 1) (gammaMeasure c 1)).comp
        ((betaJoin_preserving ha hb).prod (MeasurePreserving.id (gammaMeasure c 1))))
  have hG : MeasurePreserving (fun z : (ℝ × ℝ) × ℝ => z.1.1/(z.1.1+(z.1.2+z.2)))
      μ (betaMeasure a (b+c)) := by
    exact (gamma_ratio_preserving ha (add_pos hb hc)).comp
      (((MeasurePreserving.id (gammaMeasure a 1)).prod (gamma_sum_preserving hb hc)).comp
        (measurePreserving_prodAssoc (gammaMeasure a 1) (gammaMeasure b 1) (gammaMeasure c 1)))
  refine ⟨by fun_prop,?_⟩
  rw [← hF.map_eq,Measure.map_map (by fun_prop) hF.measurable]
  calc
    _ = Measure.map (fun z : (ℝ × ℝ) × ℝ => z.1.1/(z.1.1+(z.1.2+z.2))) μ := by
      apply Measure.map_congr
      have hpos : ∀ᵐ z : (ℝ × ℝ) × ℝ ∂μ, 0 < z.1.1 ∧ 0 < z.1.2 :=
        (measurePreserving_fst.quasiMeasurePreserving.ae (gamma_prod_ae_domain a b hb))
      filter_upwards [hpos] with z hz
      dsimp only [Function.comp_apply]
      rw [← mul_div_assoc,div_mul_cancel₀ _ (add_pos hz.1 hz.2).ne',add_assoc]
    _ = _ := hG.map_eq

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma latitudeLaw_beta_gt_one (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (hV : 1 < Module.finrank ℝ V) (hD : Module.finrank ℝ V < Module.finrank ℝ E)
    {a delta : ℝ} (ha : 0 < a) (hd : 0 < delta)
    (hshape : a+delta = ((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ V : ℝ))/2) :
    MeasurePreserving (perpCoordinate V) (latitudeLaw V e a delta)
      (betaMeasure a (delta+((Module.finrank ℝ V : ℝ)-1)/2)) := by
  have hr := latitude_rank V e
  have hk := V.finrank_add_finrank_orthogonal
  have hK : 0 < Module.finrank ℝ Vᗮ := by omega
  have hKL : Module.finrank ℝ Vᗮ < Module.finrank ℝ (latitudeSpace V e) := by omega
  let : Nontrivial (latitudeSpace V e) := Module.nontrivial_of_finrank_pos
    (R := ℝ) (M := latitudeSpace V e) (by omega)
  let : IsProbabilityMeasure (betaMeasure a delta) := isProbabilityMeasureBeta ha hd
  have hA : (Module.finrank ℝ Vᗮ : ℝ)/2 = a+delta := by
    have hk' : (Module.finrank ℝ V : ℝ)+(Module.finrank ℝ Vᗮ : ℝ) = Module.finrank ℝ E := by exact_mod_cast hk
    linarith
  have hC : ((Module.finrank ℝ (latitudeSpace V e) : ℝ)-(Module.finrank ℝ Vᗮ : ℝ))/2 =
      ((Module.finrank ℝ V : ℝ)-1)/2 := by
    have hk' : (Module.finrank ℝ V : ℝ)+(Module.finrank ℝ Vᗮ : ℝ) = Module.finrank ℝ E := by exact_mod_cast hk
    have hr' : (Module.finrank ℝ (latitudeSpace V e) : ℝ)+1 = Module.finrank ℝ E := by exact_mod_cast hr
    linarith
  have hcoord : MeasurePreserving (fun x : latitudeSpace V e => perpCoordinate V (x : E))
      SubsphereRegression.ambientSphereLaw (betaMeasure (a+delta) (((Module.finrank ℝ V : ℝ)-1)/2)) := by
    simpa only [hA,hC,perpCoordinate] using
      nested_projection_beta Vᗮ (latitudeSpace V e) (latitude_perp_le V e) hK hKL
  have hc : 0 < ((Module.finrank ℝ V : ℝ)-1)/2 := by
    have hvr : (1 : ℝ) < Module.finrank ℝ V := by exact_mod_cast hV
    linarith
  have hpair := (MeasurePreserving.id (betaMeasure a delta)).prod
    (hcoord.comp (measurePreserving_snd (μ := orthogonalLaw (E := V))))
  have hprod := (beta_product_preserving ha hd hc).comp hpair
  refine ⟨measurable_perpCoordinate V,?_⟩
  rw [latitudeLaw,Measure.map_map (measurable_perpCoordinate V) (measurable_latitudeSampler V e)]
  calc
    _ = Measure.map (fun z : ℝ × (Orthogonal V × latitudeSpace V e) =>
        z.1 * perpCoordinate V (z.2.2 : E))
        ((betaMeasure a delta).prod ((orthogonalLaw (E := V)).prod
          SubsphereRegression.ambientSphereLaw)) := by
      apply Measure.map_congr
      have hq : ∀ᵐ z : ℝ × (Orthogonal V × latitudeSpace V e)
          ∂(betaMeasure a delta).prod ((orthogonalLaw (E := V)).prod SubsphereRegression.ambientSphereLaw),
          z.1 ∈ Ioo (0 : ℝ) 1 :=
        measurePreserving_fst.quasiMeasurePreserving.ae (beta_ae_mem a delta)
      filter_upwards [hq] with z hz
      exact latitude_coordinate V e z.2.1 z.2.2 hz.1.le
    _ = _ := hprod.map_eq

lemma latitudeLaw_beta_one (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (hV : Module.finrank ℝ V = 1) (hD : 1 < Module.finrank ℝ E)
    {a delta : ℝ} (ha : 0 < a) (hd : 0 < delta) :
    MeasurePreserving (perpCoordinate V) (latitudeLaw V e a delta) (betaMeasure a delta) := by
  have hr := latitude_rank V e
  let : Nontrivial (latitudeSpace V e) := Module.nontrivial_of_finrank_pos
    (R := ℝ) (M := latitudeSpace V e) (by omega)
  let : IsProbabilityMeasure (betaMeasure a delta) := isProbabilityMeasureBeta ha hd
  let μ := (betaMeasure a delta).prod ((orthogonalLaw (E := V)).prod
    (SubsphereRegression.ambientSphereLaw (E := latitudeSpace V e)))
  have hq : ∀ᵐ z : ℝ × (Orthogonal V × latitudeSpace V e) ∂μ, z.1 ∈ Ioo (0 : ℝ) 1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae (beta_ae_mem a delta)
  have hx : ∀ᵐ z : ℝ × (Orthogonal V × latitudeSpace V e) ∂μ, ‖z.2.2‖ = 1 :=
    (measurePreserving_snd.comp measurePreserving_snd).quasiMeasurePreserving.ae
      SubsphereRegression.ambientSphereLaw_ae_norm
  refine ⟨measurable_perpCoordinate V,?_⟩
  rw [latitudeLaw,Measure.map_map (measurable_perpCoordinate V) (measurable_latitudeSampler V e)]
  calc
    _ = μ.map Prod.fst := by
      apply Measure.map_congr
      filter_upwards [hq,hx] with z hz hzx
      dsimp only [Function.comp_apply]
      rw [latitude_coordinate V e z.2.1 z.2.2 hz.1.le,
        latitude_coordinate_rank_one V e hV,hzx,one_pow,mul_one]
    _ = _ := measurePreserving_fst.map_eq

end SubsphereCurrent.Mixture

end

end OAI
