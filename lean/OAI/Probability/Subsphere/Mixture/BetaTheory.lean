import Mathlib
import OAI.Probability.Subsphere.Mixture.Haar
import OAI.Probability.Subsphere.Geometry.Integration

namespace OAI

section
open MeasureTheory Set
open scoped RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma nested_starProjection (U N : Submodule ℝ E) (h : U ≤ N) (x : N) :
    (((U.comap N.subtype).starProjection x : N) : E) = U.starProjection (x : E) := by
  have he : (U.comap N.subtype).starProjection x =
      (⟨U.starProjection (x : E), h (U.orthogonalProjectionOnto (x : E)).prop⟩ : N) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact (U.orthogonalProjectionOnto (x : E)).prop
    · intro w hw
      exact U.starProjection_inner_eq_zero (x : E) (w : E) hw
  exact congrArg Subtype.val he

lemma nested_orthogonal_starProjection (U N : Submodule ℝ E) (h : U ≤ N) (x : N) :
    ((((U.comap N.subtype)ᗮ).starProjection x : N) : E) = Uᗮ.starProjection (x : E) := by
  rw [Submodule.starProjection_orthogonal_val,Submodule.starProjection_orthogonal_val]
  change (x : E)-(((U.comap N.subtype).starProjection x : N) : E) = _
  rw [nested_starProjection U N h]

lemma nested_projection_norm (U N : Submodule ℝ E) (h : U ≤ N) (x : N) :
    ‖(U.comap N.subtype).orthogonalProjectionOnto x‖ = ‖U.orthogonalProjectionOnto (x : E)‖ := by
  exact congrArg norm (nested_starProjection U N h x)

lemma nested_orthogonal_projection_norm (U N : Submodule ℝ E) (h : U ≤ N) (x : N) :
    ‖(U.comap N.subtype)ᗮ.orthogonalProjectionOnto x‖ = ‖Uᗮ.orthogonalProjectionOnto (x : E)‖ := by
  exact congrArg norm (nested_orthogonal_starProjection U N h x)

omit [FiniteDimensional ℝ E] in
lemma nested_rank (U N : Submodule ℝ E) (h : U ≤ N) :
    Module.finrank ℝ (U.comap N.subtype) = Module.finrank ℝ U :=
  (Submodule.comapSubtypeEquivOfLe h).finrank_eq

/-- Restriction of an actual ambient orthogonal map to a stable subspace. -/
def restrictIso (N : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (he : N.map e.toLinearMap = N) : N ≃ₗᵢ[ℝ] N :=
  (LinearIsometryEquiv.submoduleMap N e).trans (LinearIsometryEquiv.ofEq _ _ he)

omit [FiniteDimensional ℝ E] in
lemma restrictIso_coe (N : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (he : N.map e.toLinearMap = N) (x : N) : (restrictIso N e he x : E) = e (x : E) := rfl

omit [FiniteDimensional ℝ E] in
lemma stable_map_eq (N : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x ∈ N, e x ∈ N) (hinv : ∀ x ∈ N, e.symm x ∈ N) :
    N.map e.toLinearMap = N := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact h x hx
  · intro x hx
    exact ⟨e.symm x,hinv x hx,e.apply_symm_apply x⟩

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma haar_scaled_integral [Nontrivial E] (x : E) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u : Orthogonal E, f (act u x) ∂orthogonalLaw) =
      ∫⁻ y, f (‖x‖ • y) ∂SubsphereRegression.ambientSphereLaw := by
  by_cases hx : x = 0
  · subst x
    simp [act]
  · have he (u : Orthogonal E) : act u x = ‖x‖ • act u (NormedSpace.normalize x) := by
      change u.val x = ‖x‖ • u.val (NormedSpace.normalize x)
      rw [← map_smul,NormedSpace.norm_smul_normalize]
    simp_rw [he]
    exact haar_eval_integral (NormedSpace.norm_normalize hx)
      (f := fun y => f (‖x‖ • y)) (hf.comp (by fun_prop))

/-- Squared norm of the distinguished perpendicular component. -/
def perpCoordinate (V : Submodule ℝ E) (x : E) : ℝ := ‖Vᗮ.orthogonalProjectionOnto x‖^2

lemma measurable_perpCoordinate (V : Submodule ℝ E) : Measurable (perpCoordinate V) := by
  unfold perpCoordinate
  fun_prop

/-- Common direction kernel for all block-invariant spherical laws. -/
def mixtureSampler (V : Submodule ℝ E) (z : ℝ × (V × Vᗮ)) : E :=
  Real.sqrt (1-z.1) • (z.2.1 : E) + Real.sqrt z.1 • (z.2.2 : E)

lemma measurable_mixtureSampler (V : Submodule ℝ E) : Measurable (mixtureSampler V) := by
  unfold mixtureSampler
  fun_prop

def mixtureLaw (V : Submodule ℝ E) (ρ : Measure ℝ) : Measure E :=
  (ρ.prod ((SubsphereRegression.ambientSphereLaw (E := V)).prod
    (SubsphereRegression.ambientSphereLaw (E := Vᗮ)))).map (mixtureSampler V)

lemma block_average (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    (x : E) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : Orthogonal V × Orthogonal Vᗮ, f (blockIso V z.1 z.2 x)
      ∂(orthogonalLaw (E := V)).prod (orthogonalLaw (E := Vᗮ))) =
    ∫⁻ s : V, ∫⁻ t : Vᗮ,
      f (‖V.orthogonalProjectionOnto x‖ • (s : E)+‖Vᗮ.orthogonalProjectionOnto x‖ • (t : E))
      ∂SubsphereRegression.ambientSphereLaw ∂SubsphereRegression.ambientSphereLaw := by
  have hm : Measurable (fun z : Orthogonal V × Orthogonal Vᗮ => f (blockIso V z.1 z.2 x)) :=
    hf.comp (continuous_blockIso V |>.comp (continuous_id.prodMk continuous_const)).measurable
  rw [lintegral_prod _ hm.aemeasurable]
  simp only [blockIso_apply]
  have hright (u : Orthogonal V) :
      (∫⁻ w : Orthogonal Vᗮ,
        f ((act (E := V) u (V.orthogonalProjectionOnto x) : E)+(act (E := Vᗮ) w (Vᗮ.orthogonalProjectionOnto x) : E))
        ∂orthogonalLaw) =
      ∫⁻ t : Vᗮ, f ((act (E := V) u (V.orthogonalProjectionOnto x) : E)+
        ‖Vᗮ.orthogonalProjectionOnto x‖ • (t : E)) ∂SubsphereRegression.ambientSphereLaw := by
    exact haar_scaled_integral (Vᗮ.orthogonalProjectionOnto x)
      (f := fun t : Vᗮ => f ((act (E := V) u (V.orthogonalProjectionOnto x) : E)+(t : E)))
      (hf.comp (by fun_prop))
  simp_rw [hright]
  have hmf : Measurable (fun s : V => ∫⁻ t : Vᗮ,
      f ((s : E)+‖Vᗮ.orthogonalProjectionOnto x‖ • (t : E))
        ∂SubsphereRegression.ambientSphereLaw) := by
    apply Measurable.lintegral_prod_right
    exact hf.comp (by fun_prop)
  exact haar_scaled_integral (V.orthogonalProjectionOnto x) hmf

lemma block_average_unit (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    {x : E} (hx : ‖x‖ = 1) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : Orthogonal V × Orthogonal Vᗮ, f (blockIso V z.1 z.2 x)
      ∂(orthogonalLaw (E := V)).prod (orthogonalLaw (E := Vᗮ))) =
    ∫⁻ z : V × Vᗮ, f (mixtureSampler V (perpCoordinate V x,z))
      ∂(SubsphereRegression.ambientSphereLaw (E := V)).prod
        (SubsphereRegression.ambientSphereLaw (E := Vᗮ)) := by
  rw [block_average V x hf]
  have hm : Measurable (fun z : V × Vᗮ => f (mixtureSampler V (perpCoordinate V x,z))) :=
    hf.comp (measurable_mixtureSampler V |>.comp (measurable_const.prodMk measurable_id))
  rw [lintegral_prod (fun z : V × Vᗮ => f (mixtureSampler V (perpCoordinate V x,z))) hm.aemeasurable]
  have hn := V.norm_sq_eq_add_norm_sq_projection x
  rw [hx,one_pow] at hn
  have hleft : Real.sqrt (1-perpCoordinate V x) = ‖V.orthogonalProjectionOnto x‖ := by
    unfold perpCoordinate
    rw [show 1-‖Vᗮ.orthogonalProjectionOnto x‖^2 = ‖V.orthogonalProjectionOnto x‖^2 by linarith,
      Real.sqrt_sq (norm_nonneg _)]
  change Real.sqrt (1-‖Vᗮ.orthogonalProjectionOnto x‖^2) = ‖V.orthogonalProjectionOnto x‖ at hleft
  simp only [mixtureSampler,perpCoordinate,hleft,Real.sqrt_sq (norm_nonneg _)]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma blockIso_symm (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) :
    (blockIso V u w).symm = blockIso V u⁻¹ w⁻¹ := by
  ext x
  apply (blockIso V u w).injective
  rw [LinearIsometryEquiv.apply_symm_apply,← blockIso_mul]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
lemma perpCoordinate_blockIso (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : E) :
    perpCoordinate V (blockIso V u w x) = perpCoordinate V x := by
  rw [perpCoordinate,blockIso_apply,map_add,
    Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)]
  simp [perpCoordinate,act_norm]

omit [MeasurableSpace E] [BorelSpace E] in
lemma block_left_mem (V N : Submodule ℝ E) (hVN : V ≤ N) (u : Orthogonal V)
    {x : E} (hx : x ∈ N) : blockIso V u 1 x ∈ N := by
  rw [blockIso_apply,act_one]
  apply N.add_mem (hVN (act (E := V) u (V.orthogonalProjectionOnto x)).prop)
  change Vᗮ.starProjection x ∈ N
  rw [Submodule.starProjection_orthogonal_val]
  exact N.sub_mem hx (hVN (V.orthogonalProjectionOnto x).prop)

omit [MeasurableSpace E] [BorelSpace E] in
lemma block_left_stable (V N : Submodule ℝ E) (hVN : V ≤ N) (u : Orthogonal V) :
    N.map (blockIso V u 1).toLinearMap = N := by
  apply stable_map_eq
  · exact fun _ hx => block_left_mem V N hVN u hx
  · rw [blockIso_symm]
    simpa using (fun x (hx : x ∈ N) => block_left_mem V N hVN u⁻¹ hx)

omit [MeasurableSpace E] [BorelSpace E] in
lemma block_right_fix_e (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) (w : Orthogonal Vᗮ) :
    blockIso V 1 w (e.val : E) = (e.val : E) := by simp [act_one]

omit [MeasurableSpace E] [BorelSpace E] in
lemma block_right_latitude_mem (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (w : Orthogonal Vᗮ) {x : E} (hx : x ∈ latitudeSpace V e) :
    blockIso V 1 w x ∈ latitudeSpace V e := by
  rw [latitudeSpace,Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
  rw [← block_right_fix_e V e w,LinearIsometryEquiv.inner_map_map]
  exact hx

omit [MeasurableSpace E] [BorelSpace E] in
lemma block_right_latitude_stable (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (w : Orthogonal Vᗮ) :
    (latitudeSpace V e).map (blockIso V 1 w).toLinearMap = latitudeSpace V e := by
  apply stable_map_eq
  · exact fun _ hx => block_right_latitude_mem V e w hx
  · rw [blockIso_symm]
    simpa using (fun x (hx : x ∈ latitudeSpace V e) => block_right_latitude_mem V e w⁻¹ hx)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma latitude_perp_le (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) :
    Vᗮ ≤ latitudeSpace V e := by
  apply Submodule.orthogonal_le
  exact Submodule.span_le.mpr (by simp)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma latitude_e_norm (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) : ‖(e.val : E)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp e.prop

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_rank (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) :
    Module.finrank ℝ (latitudeSpace V e)+1 = Module.finrank ℝ E := by
  have he : (e.val : E) ≠ 0 := by intro h; have := latitude_e_norm V e; simp [h] at this
  have h := (ℝ ∙ (e.val : E)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton he] at h
  change Module.finrank ℝ (ℝ ∙ (e.val : E))ᗮ + 1 = Module.finrank ℝ E
  exact (Nat.add_comm _ _).trans h

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory
noncomputable section
namespace SubsphereCurrent.Mixture

lemma preserving_map_of_intertwining {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {f : X → Y} {g : X → X} {h : Y → Y}
    (hf : Measurable f) (hg : MeasurePreserving g μ μ) (hh : Measurable h)
    (hc : ∀ x, f (g x) = h (f x)) : MeasurePreserving h (μ.map f) (μ.map f) := by
  refine ⟨hh,?_⟩
  rw [Measure.map_map hh hf]
  calc
    _ = μ.map (f ∘ g) := by congr 1; funext x; exact (hc x).symm
    _ = (μ.map g).map f := (Measure.map_map hf hg.measurable).symm
    _ = _ := by rw [hg.map_eq]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set Module
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

def betaSplit (z : ℝ × ℝ) : ℝ × ℝ := (z.1*z.2,(1-z.1)*z.2)
def betaJoin (z : ℝ × ℝ) : ℝ × ℝ := (z.1/(z.1+z.2),z.1+z.2)
def betaDomain : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)
def gammaDomain : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)

def betaSplitDeriv (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (z.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + z.1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((-z.2) • ContinuousLinearMap.fst ℝ ℝ ℝ + (1-z.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma betaSplitDeriv_apply (z h : ℝ × ℝ) : betaSplitDeriv z h =
    (z.2*h.1+z.1*h.2, -z.2*h.1+(1-z.1)*h.2) := rfl

lemma betaSplit_hasFDeriv (z : ℝ × ℝ) : HasFDerivAt betaSplit (betaSplitDeriv z) z := by
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).mul (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have h2 := ((hasFDerivAt_const (1 : ℝ) z).sub (hasFDerivAt_fst (𝕜 := ℝ) (p := z))).mul
    (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have hd : (z.1 • ContinuousLinearMap.snd ℝ ℝ ℝ + z.2 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((1-z.1) • ContinuousLinearMap.snd ℝ ℝ ℝ + z.2 • (0 - ContinuousLinearMap.fst ℝ ℝ ℝ)) =
      betaSplitDeriv z := by
    ext <;> simp [betaSplitDeriv_apply]
  rw [← hd]
  exact h1.prodMk h2

lemma betaSplit_det (z : ℝ × ℝ) : (betaSplitDeriv z).det = z.2 := by
  change LinearMap.det (betaSplitDeriv z).toLinearMap = _
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℝ)]
  have he : LinearMap.toMatrix (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
      (betaSplitDeriv z).toLinearMap = !![z.2,z.1;-z.2,1-z.1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply,betaSplitDeriv_apply,
      Basis.coe_finTwoProd_repr]
  rw [he,Matrix.det_fin_two_of]
  ring

lemma betaJoin_split {z : ℝ × ℝ} (hz : z ∈ betaDomain) : betaJoin (betaSplit z) = z := by
  have hr : z.2 ≠ 0 := ne_of_gt hz.2
  ext <;> simp only [betaSplit,betaJoin]
  · have he : z.1*z.2+(1-z.1)*z.2 = z.2 := by ring
    rw [he,mul_div_cancel_right₀ _ hr]
  · ring

lemma betaSplit_join {z : ℝ × ℝ} (hz : z ∈ gammaDomain) : betaSplit (betaJoin z) = z := by
  have hr : z.1+z.2 ≠ 0 := ne_of_gt (add_pos hz.1 hz.2)
  ext <;> simp only [betaSplit,betaJoin] <;> field_simp
  ring

lemma betaSplit_image : betaSplit '' betaDomain = gammaDomain := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨mul_pos hw.1.1 hw.2,mul_pos (sub_pos.mpr hw.1.2) hw.2⟩
  · intro hz
    refine ⟨betaJoin z,?_,betaSplit_join hz⟩
    have hr : 0 < z.1 + z.2 := add_pos hz.1 hz.2
    exact ⟨⟨div_pos hz.1 hr,(div_lt_one hr).2 (by linarith [show 0 < z.2 from hz.2])⟩,hr⟩

lemma betaSplit_inj : InjOn betaSplit betaDomain := by
  intro x hx y hy h
  rw [← betaJoin_split hx,← betaJoin_split hy,h]

lemma lintegral_betaSplit (f : (ℝ × ℝ) → ℝ≥0∞) :
    (∫⁻ z in gammaDomain, f z) =
      ∫⁻ z in betaDomain, ENNReal.ofReal z.2 * f (betaSplit z) := by
  rw [← betaSplit_image]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_Ioo.prod measurableSet_Ioi)
    (fun z _ => (betaSplit_hasFDeriv z).hasFDerivWithinAt) betaSplit_inj]
  apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioi)
  intro z hz
  dsimp only
  rw [betaSplit_det,abs_of_pos hz.2]

end SubsphereCurrent.Mixture
end
end
section
/-! Exact beta/gamma independence and products, needed to identify the scalar
coordinate laws in the geometric comparison. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

lemma gammaPDF_measurable (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal
lemma betaPDF_measurable (a b : ℝ) : Measurable (betaPDF a b) :=
  (measurable_betaPDFReal a b).ennreal_ofReal

lemma gamma_beta_density {a b q r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : q ∈ Ioo (0 : ℝ) 1) (hr : 0 < r) :
    ENNReal.ofReal r * (gammaPDF a 1 (q*r) * gammaPDF b 1 ((1-q)*r)) =
      betaPDF a b q * gammaPDF (a+b) 1 r := by
  change 0 < q ∧ q < 1 at hq
  have hq0 : 0 < q := hq.1
  have hq1 : 0 < 1-q := sub_pos.mpr hq.2
  have hbeta : 0 < beta a b := beta_pos ha hb
  have hga := (Real.Gamma_pos_of_pos ha).ne'
  have hgb := (Real.Gamma_pos_of_pos hb).ne'
  have hg := (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  have hp : r * r^(a-1) * r^(b-1) = r^(a+b-1) := by
    calc
      _ = r^(1 : ℝ) * r^(a-1) * r^(b-1) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hr,← Real.rpow_add hr]
        congr 1
        ring
  have he : Real.exp (-(q*r)) * Real.exp (-((1-q)*r)) = Real.exp (-r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [gammaPDF_of_nonneg (mul_pos hq0 hr).le,
    gammaPDF_of_nonneg (mul_pos hq1 hr).le,gammaPDF_of_nonneg hr.le,
    betaPDF,betaPDFReal,ite_eq_left hq,Real.one_rpow,one_mul]
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul hr.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.mul_rpow hq0.le hr.le,Real.mul_rpow hq1.le hr.le]
  calc
    _ = (1/Real.Gamma a / Real.Gamma b) * q^(a-1) * (1-q)^(b-1) *
      (r*r^(a-1)*r^(b-1)) * (Real.exp (-(q*r))*Real.exp (-((1-q)*r))) := by ring
    _ = _ := by
      rw [hp,he]
      unfold beta
      field_simp [hga,hgb,hg]

lemma lintegral_gamma_eq {f : ℝ → ℝ≥0∞} (hf : Measurable f) (a : ℝ) :
    (∫⁻ x, f x ∂gammaMeasure a 1) = ∫⁻ x in Ioi (0 : ℝ), gammaPDF a 1 x * f x := by
  rw [gammaMeasure,lintegral_withDensity_eq_lintegral_mul volume (gammaPDF_measurable _ _) hf,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr_ae
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
  filter_upwards [hn] with x hx
  by_cases hp : 0 < x
  · simp [hp]
  · have hneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simp [hp,gammaPDF_of_neg hneg]

lemma gammaMeasure_restrict_density (a : ℝ) :
    gammaMeasure a 1 = (volume.restrict (Ioi (0 : ℝ))).withDensity (gammaPDF a 1) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_gamma_eq hf,lintegral_withDensity_eq_lintegral_mul _ (gammaPDF_measurable _ _) hf]
  rfl

lemma betaMeasure_restrict_density (a b : ℝ) :
    betaMeasure a b = (volume.restrict (Ioo (0 : ℝ) 1)).withDensity (betaPDF a b) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [betaMeasure,lintegral_withDensity_eq_lintegral_mul _ (betaPDF_measurable _ _) hf,
    lintegral_withDensity_eq_lintegral_mul _ (betaPDF_measurable _ _) hf,
    ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro x
  by_cases h : 0 < x ∧ x < 1
  · simp [h]
  · simp [Set.indicator,betaPDF,betaPDFReal,h]

lemma lintegral_gamma_prod {f : (ℝ × ℝ) → ℝ≥0∞} (hf : Measurable f) (a b : ℝ) :
    (∫⁻ z, f z ∂(gammaMeasure a 1).prod (gammaMeasure b 1)) =
      ∫⁻ z in gammaDomain, (gammaPDF a 1 z.1 * gammaPDF b 1 z.2) * f z := by
  rw [gammaMeasure_restrict_density,gammaMeasure_restrict_density,
    prod_withDensity (gammaPDF_measurable _ _) (gammaPDF_measurable _ _),
    Measure.prod_restrict,← Measure.volume_eq_prod,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : ℝ × ℝ => gammaPDF a 1 z.1 * gammaPDF b 1 z.2) from
        ((gammaPDF_measurable _ _).comp measurable_fst).mul
          ((gammaPDF_measurable _ _).comp measurable_snd)) hf]
  rfl

lemma lintegral_beta_gamma {f : (ℝ × ℝ) → ℝ≥0∞} (hf : Measurable f) (a b c : ℝ) :
    (∫⁻ z, f z ∂(betaMeasure a b).prod (gammaMeasure c 1)) =
      ∫⁻ z in betaDomain, (betaPDF a b z.1 * gammaPDF c 1 z.2) * f z := by
  rw [betaMeasure_restrict_density,gammaMeasure_restrict_density,
    prod_withDensity (betaPDF_measurable _ _) (gammaPDF_measurable _ _),
    Measure.prod_restrict,← Measure.volume_eq_prod,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : ℝ × ℝ => betaPDF a b z.1 * gammaPDF c 1 z.2) from
        ((betaPDF_measurable _ _).comp measurable_fst).mul
          ((gammaPDF_measurable _ _).comp measurable_snd)) hf]
  rfl

/-- The exact beta/gamma change of variables as a positive-measure identity. -/
lemma betaSplit_preserving {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MeasurePreserving betaSplit ((betaMeasure a b).prod (gammaMeasure (a+b) 1))
      ((gammaMeasure a 1).prod (gammaMeasure b 1)) := by
  have hm : Measurable betaSplit := by unfold betaSplit; fun_prop
  refine ⟨hm,?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm,lintegral_beta_gamma (f := fun z => f (betaSplit z)) (hf.comp hm),lintegral_gamma_prod hf,
    lintegral_betaSplit]
  apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioi)
  intro z hz
  change (betaPDF a b z.1 * gammaPDF (a+b) 1 z.2) * f (betaSplit z) =
    ENNReal.ofReal z.2 * ((gammaPDF a 1 (z.1*z.2) * gammaPDF b 1 ((1-z.1)*z.2)) * f (betaSplit z))
  rw [← gamma_beta_density ha hb hz.1 hz.2,mul_assoc]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

lemma square_image_Ioi : (fun r : ℝ => r^2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact sq_pos_of_pos (show 0 < r from hr)
  · intro hx
    exact ⟨Real.sqrt x,Real.sqrt_pos.mpr hx,Real.sq_sqrt hx.le⟩

lemma square_inj_Ioi : InjOn (fun r : ℝ => r^2) (Ioi (0 : ℝ)) := by
  intro x hx y hy he
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  nlinarith

lemma lintegral_square (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in Ioi (0 : ℝ), f x) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2*r) * f (r^2) := by
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal |2*r| * f (r^2) := by
      simpa only [square_image_Ioi, Nat.cast_ofNat, show 2-1=1 by decide, pow_one, mul_one, id_eq] using
        (lintegral_image_eq_lintegral_abs_deriv_mul (f := fun r : ℝ => r^2)
          measurableSet_Ioi (fun r _ => ((hasDerivAt_id r).pow 2).hasDerivWithinAt)
          square_inj_Ioi f)
    _ = _ := ?_
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [abs_of_pos (mul_pos (by norm_num) hr)]

lemma gamma_square_density {d : ℕ} (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (2*r) * gammaPDF ((d : ℝ)/2) 1 (r^2) =
      ENNReal.ofReal (2/Real.Gamma ((d : ℝ)/2)) * ENNReal.ofReal (r^(d-1)) *
        ENNReal.ofReal (Real.exp (-(r^2))) := by
  have hd0 : 0 < (d : ℝ)/2 := by positivity
  have hg : 0 < Real.Gamma ((d : ℝ)/2) := Real.Gamma_pos_of_pos hd0
  have hp : r * (r^2)^((d : ℝ)/2-1) = r^(d-1) := by
    rw [← Real.rpow_natCast_mul hr.le]
    calc
      _ = r^(1 : ℝ) * r^((2 : ℝ)*((d : ℝ)/2-1)) := by norm_num only [Real.rpow_one,Nat.cast_ofNat]
      _ = r^((d-1 : ℕ) : ℝ) := by
        rw [← Real.rpow_add hr]
        congr 1
        rw [Nat.cast_sub hd]
        norm_num
        ring
      _ = _ := Real.rpow_natCast r (d-1)
  rw [gammaPDF_of_nonneg (sq_nonneg r)]
  simp only [Real.one_rpow,one_mul]
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  calc
    _ = (2/Real.Gamma ((d : ℝ)/2)) * (r*(r^2)^((d : ℝ)/2-1)) * Real.exp (-(r^2)) := by ring
    _ = _ := by rw [hp]

lemma gamma_sqrt_lintegral (d : ℕ) (hd : 0 < d) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f (Real.sqrt x) ∂gammaMeasure ((d : ℝ)/2) 1) =
      ENNReal.ofReal (2/Real.Gamma ((d : ℝ)/2)) *
        ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(r.val^2))) * f r.val
          ∂Measure.volumeIoiPow (d-1) := by
  rw [lintegral_gamma_eq (f := fun x => f (Real.sqrt x)) (hf.comp (by fun_prop)),lintegral_square]
  have he : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2*r) *
      (gammaPDF ((d : ℝ)/2) 1 (r^2) * f (Real.sqrt (r^2)))) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2/Real.Gamma ((d : ℝ)/2)) *
        (ENNReal.ofReal (r^(d-1)) * (ENNReal.ofReal (Real.exp (-(r^2))) * f r)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [Real.sqrt_sq hr.le,← mul_assoc,gamma_square_density hd hr]
    simp only [mul_assoc]
  rw [he,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [Measure.volumeIoiPow,lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  exact (lintegral_subtype_comap measurableSet_Ioi _).symm

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- A uniform direction with independent squared radius Γ(dim/2,1). -/
def gammaSphere : Measure E :=
  ((SubsphereRegression.sphereLaw (E := E)).prod
    (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1)).map
      (fun z => Real.sqrt z.2 • z.1.val)

def gammaSphereConstant (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : ℝ≥0∞ :=
  ENNReal.ofReal (2/Real.Gamma ((Module.finrank ℝ E : ℝ)/2)) *
    ((volume : Measure E).toSphere univ)⁻¹

instance gammaSphere_probability : IsProbabilityMeasure (gammaSphere (E := E)) := by
  let : IsProbabilityMeasure (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1) :=
    isProbabilityMeasure_gammaMeasure (by have := Module.finrank_pos (R := ℝ) (M := E); positivity)
      (by norm_num)
  unfold gammaSphere
  infer_instance

lemma gammaSphere_lintegral {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂gammaSphere (E := E)) = gammaSphereConstant E *
      ∫⁻ x : E, ENNReal.ofReal (Real.exp (-‖x‖^2)) * f x ∂volume := by
  let : IsProbabilityMeasure (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1) :=
    isProbabilityMeasure_gammaMeasure (by have := Module.finrank_pos (R := ℝ) (M := E); positivity)
      (by norm_num)
  have hm : Measurable (fun z : Metric.sphere (0 : E) 1 × ℝ => Real.sqrt z.2 • z.1.val) := by fun_prop
  rw [gammaSphere,lintegral_map hf hm]
  rw [lintegral_prod (fun z : Metric.sphere (0 : E) 1 × ℝ => f (Real.sqrt z.2 • z.1.val))
    (hf.comp hm).aemeasurable]
  have hs (s : Metric.sphere (0 : E) 1) :
      (∫⁻ x, f (Real.sqrt x • s.val) ∂gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1) =
      ENNReal.ofReal (2/Real.Gamma ((Module.finrank ℝ E : ℝ)/2)) *
        ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(r.val^2))) * f (r.val • s.val)
          ∂Measure.volumeIoiPow (Module.finrank ℝ E-1) :=
    gamma_sqrt_lintegral (Module.finrank ℝ E) Module.finrank_pos
      (f := fun r : ℝ => f (r • s.val)) (hf.comp (by fun_prop))
  simp_rw [hs]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,SubsphereRegression.sphereLaw,
    lintegral_smul_measure,Polar.lintegral_polar _ (by fun_prop)]
  simp only [smul_eq_mul,gammaSphereConstant,mul_assoc]
  congr 2
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro r
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.property,
    mem_sphere_zero_iff_norm.mp s.property,mul_one]

lemma gammaSphere_density : gammaSphere (E := E) = gammaSphereConstant E •
    (volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-‖x‖^2))) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [gammaSphere_lintegral hf,lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  rfl

lemma gammaSphereConstant_ne_top : gammaSphereConstant E ≠ ∞ := by
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ENNReal.inv_ne_top.mpr
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne')
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma invariant_sphere_unique (μ : Measure E) [IsProbabilityMeasure μ]
    (hunit : ∀ᵐ x ∂μ, ‖x‖ = 1)
    (hinv : ∀ u : Orthogonal E, MeasurePreserving (act u) μ μ) :
    μ = SubsphereRegression.ambientSphereLaw := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun z : E × Orthogonal E => f (act z.2 z.1)) :=
    hf.comp (continuous_act.comp continuous_swap).measurable
  calc
    _ = ∫⁻ u : Orthogonal E, ∫⁻ x, f (act u x) ∂μ ∂orthogonalLaw := by
      simp_rw [(hinv _).lintegral_comp hf]
      simp
    _ = ∫⁻ x, ∫⁻ u : Orthogonal E, f (act u x) ∂orthogonalLaw ∂μ :=
      (lintegral_lintegral_swap hm.aemeasurable).symm
    _ = ∫⁻ _x : E, ∫⁻ y, f y ∂SubsphereRegression.ambientSphereLaw ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hunit] with x hx
      exact haar_eval_integral hx hf
    _ = _ := by simp

omit [Nontrivial E] in
lemma measurable_normalize : Measurable (NormedSpace.normalize : E → E) := by
  unfold NormedSpace.normalize
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma normalize_isometry (e : E ≃ₗᵢ[ℝ] E) (x : E) :
    NormedSpace.normalize (e x) = e (NormedSpace.normalize x) := by
  simp [NormedSpace.normalize]

lemma normalized_invariant (μ : Measure E) [IsProbabilityMeasure μ]
    (hnz : ∀ᵐ x ∂μ, x ≠ 0)
    (hinv : ∀ e : E ≃ₗᵢ[ℝ] E, MeasurePreserving e μ μ) :
    μ.map NormedSpace.normalize = SubsphereRegression.ambientSphereLaw := by
  let : IsProbabilityMeasure (μ.map NormedSpace.normalize) := inferInstance
  apply invariant_sphere_unique
  · rw [ae_map_iff measurable_normalize.aemeasurable (by measurability)]
    exact hnz.mono (fun _ hx => NormedSpace.norm_normalize hx)
  · intro u
    have hm : Measurable (act u : E → E) :=
      (continuous_act.comp (continuous_const.prodMk continuous_id)).measurable
    refine ⟨hm,?_⟩
    rw [Measure.map_map hm measurable_normalize]
    have he : (act u ∘ NormedSpace.normalize : E → E) =
        NormedSpace.normalize ∘ Unitary.linearIsometryEquiv u := by
      funext x
      exact (normalize_isometry (Unitary.linearIsometryEquiv u) x).symm
    rw [he,← Measure.map_map measurable_normalize (Unitary.linearIsometryEquiv u).continuous.measurable,
      (hinv _).map_eq]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
lemma isotropic_density_preserving (c : ℝ≥0∞) (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving e
      (c • (volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-‖x‖^2))))
      (c • (volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-‖x‖^2)))) := by
  refine ⟨e.continuous.measurable,?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf e.continuous.measurable,lintegral_smul_measure,lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (f := fun x => ENNReal.ofReal (Real.exp (-‖x‖^2)))
      (g := fun x => f (e x)) (by fun_prop) (hf.comp e.continuous.measurable),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  simp only [smul_eq_mul]
  congr 1
  have hm : Measurable (fun x : E => ENNReal.ofReal (Real.exp (-‖x‖^2)) * f x) := by fun_prop
  simpa only [Pi.mul_apply,e.norm_map] using e.measurePreserving.lintegral_comp hm

lemma normalized_density_uniform (μ : Measure E) [IsProbabilityMeasure μ] {c : ℝ≥0∞}
    (hμ : μ = c • (volume : Measure E).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-‖x‖^2)))) :
    μ.map NormedSpace.normalize = SubsphereRegression.ambientSphereLaw := by
  apply normalized_invariant μ
  · rw [hμ,ae_iff]
    have hz : ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-‖x‖^2)))) {0} = 0 :=
      withDensity_absolutelyContinuous _ _ (measure_singleton 0)
    simp only [not_not,Set.ofPred_eq_eq_singleton,Measure.smul_apply,smul_eq_mul,hz,mul_zero]
  · intro e
    rw [hμ]
    exact isotropic_density_preserving c e

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma orthogonal_norm_add (V : Submodule ℝ E) (x : V) (y : Vᗮ) :
    ‖(x : E)+(y : E)‖^2 = ‖x‖^2+‖y‖^2 :=
  by simpa only [pow_two, Submodule.norm_coe] using
    (norm_add_sq_eq_norm_sq_add_norm_sq_real (V.inner_right_of_mem_orthogonal x.prop y.prop))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma orthogonal_exp_mul (V : Submodule ℝ E) (x : V) (y : Vᗮ) :
    ENNReal.ofReal (Real.exp (-‖x‖^2)) * ENNReal.ofReal (Real.exp (-‖y‖^2)) =
      ENNReal.ofReal (Real.exp (-‖(x : E)+(y : E)‖^2)) := by
  rw [← ENNReal.ofReal_mul (by positivity),← Real.exp_add,orthogonal_norm_add]
  congr 2
  ring

def sumGamma (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ] : Measure E :=
  ((gammaSphere (E := V)).prod (gammaSphere (E := Vᗮ))).map
    (fun z => (z.1 : E)+(z.2 : E))

instance sumGamma_probability (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ] :
    IsProbabilityMeasure (sumGamma V) := by
  unfold sumGamma
  infer_instance

omit [Nontrivial E] in
lemma sumGamma_density (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ] :
    sumGamma V = (gammaSphereConstant V * gammaSphereConstant Vᗮ) •
      (volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-‖x‖^2))) := by
  rw [sumGamma,gammaSphere_density,gammaSphere_density,Measure.prod_smul_left,
    Measure.prod_smul_right,smul_smul,Measure.map_smul _ (by fun_prop)]
  congr 1
  rw [prod_withDensity (by fun_prop) (by fun_prop)]
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun z : V × Vᗮ => (z.1 : E)+(z.2 : E)) := by fun_prop
  rw [lintegral_map hf hm,
    lintegral_withDensity_eq_lintegral_mul _ (g := fun z : V × Vᗮ => f ((z.1 : E)+(z.2 : E)))
      (by fun_prop) (hf.comp hm),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  simp only [Pi.mul_apply,orthogonal_exp_mul]
  exact (Polar.orthogonal_sum_volume V).lintegral_comp
    (f := fun x : E => ENNReal.ofReal (Real.exp (-‖x‖^2)) * f x) (by fun_prop)

lemma sumGamma_direction (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ] :
    (sumGamma V).map NormedSpace.normalize = SubsphereRegression.ambientSphereLaw :=
  normalized_density_uniform (sumGamma V) (sumGamma_density V)

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

lemma gamma_ae_pos (a : ℝ) : ∀ᵐ x ∂gammaMeasure a 1, 0 < x := by
  rw [gammaMeasure_restrict_density]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

lemma beta_ae_mem (a b : ℝ) : ∀ᵐ x ∂betaMeasure a b, x ∈ Ioo (0 : ℝ) 1 := by
  rw [betaMeasure_restrict_density]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

lemma beta_gamma_ae_domain (a b c : ℝ) (hc : 0 < c) :
    ∀ᵐ z ∂(betaMeasure a b).prod (gammaMeasure c 1), z ∈ betaDomain := by
  let : IsProbabilityMeasure (gammaMeasure c 1) :=
    isProbabilityMeasure_gammaMeasure hc (by norm_num)
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioi)).2
  filter_upwards [beta_ae_mem a b] with x hx
  filter_upwards [gamma_ae_pos c] with y hy
  exact ⟨hx,hy⟩

lemma gamma_prod_ae_domain (a b : ℝ) (hb : 0 < b) :
    ∀ᵐ z ∂(gammaMeasure a 1).prod (gammaMeasure b 1), z ∈ gammaDomain := by
  let : IsProbabilityMeasure (gammaMeasure b 1) :=
    isProbabilityMeasure_gammaMeasure hb (by norm_num)
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioi.prod measurableSet_Ioi)).2
  filter_upwards [gamma_ae_pos a] with x hx
  filter_upwards [gamma_ae_pos b] with y hy
  exact ⟨hx,hy⟩

lemma measurable_betaJoin : Measurable betaJoin := by unfold betaJoin; fun_prop

lemma betaJoin_preserving {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MeasurePreserving betaJoin ((gammaMeasure a 1).prod (gammaMeasure b 1))
      ((betaMeasure a b).prod (gammaMeasure (a+b) 1)) := by
  refine ⟨measurable_betaJoin,?_⟩
  rw [← (betaSplit_preserving ha hb).map_eq,
    Measure.map_map measurable_betaJoin (by unfold betaSplit; fun_prop)]
  calc
    _ = Measure.map id ((betaMeasure a b).prod (gammaMeasure (a+b) 1)) := by
      apply Measure.map_congr
      filter_upwards [beta_gamma_ae_domain a b (a+b) (add_pos ha hb)] with z hz
      exact betaJoin_split hz
    _ = _ := Measure.map_id

lemma gamma_ratio_preserving {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MeasurePreserving (fun z : ℝ × ℝ => z.1/(z.1+z.2))
      ((gammaMeasure a 1).prod (gammaMeasure b 1)) (betaMeasure a b) := by
  let : IsProbabilityMeasure (gammaMeasure (a+b) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) (by norm_num)
  exact measurePreserving_fst.comp
    (betaJoin_preserving ha hb)

lemma gamma_sum_preserving {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MeasurePreserving (fun z : ℝ × ℝ => z.1+z.2)
      ((gammaMeasure a 1).prod (gammaMeasure b 1)) (gammaMeasure (a+b) 1) := by
  let : IsProbabilityMeasure (gammaMeasure (a+b) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) (by norm_num)
  let : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  exact measurePreserving_snd.comp
    (betaJoin_preserving ha hb)

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma gammaSphere_sqnorm : MeasurePreserving (fun x : E => ‖x‖^2) gammaSphere
    (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1) := by
  let : IsProbabilityMeasure (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1) :=
    isProbabilityMeasure_gammaMeasure (by have := Module.finrank_pos (R := ℝ) (M := E); positivity)
      (by norm_num)
  have hm : Measurable (fun z : Metric.sphere (0 : E) 1 × ℝ => Real.sqrt z.2 • z.1.val) := by fun_prop
  refine ⟨by fun_prop,?_⟩
  rw [gammaSphere,Measure.map_map (by fun_prop) hm]
  calc
    _ = Measure.map Prod.snd ((SubsphereRegression.sphereLaw (E := E)).prod
      (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1)) := by
      apply Measure.map_congr
      have hp : ∀ᵐ z : Metric.sphere (0 : E) 1 × ℝ ∂(SubsphereRegression.sphereLaw (E := E)).prod
          (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1), 0 < z.2 :=
        measurePreserving_snd.quasiMeasurePreserving.ae (gamma_ae_pos _)
      filter_upwards [hp] with z hz
      simp only [Function.comp_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),mem_sphere_zero_iff_norm.mp z.1.property,mul_one]
      exact Real.sq_sqrt hz.le
    _ = _ := measurePreserving_snd.map_eq

end SubsphereCurrent.Mixture
end
end
section
/-! Actual squared-projection beta law of the normalized Haar sphere. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma normalize_sum_sqproj (V : Submodule ℝ E) (x : V) (y : Vᗮ) :
    ‖V.orthogonalProjectionOnto (NormedSpace.normalize ((x : E)+(y : E)))‖^2 =
      ‖x‖^2/(‖x‖^2+‖y‖^2) := by
  rw [NormedSpace.normalize,map_smul,map_add,
    V.orthogonalProjectionOnto_apply_of_mem_orthogonal y.property]
  simp only [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,add_zero,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),mul_pow,inv_pow,
    orthogonal_norm_add,div_eq_mul_inv,mul_comm]

lemma sphere_projection_beta (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ] :
    MeasurePreserving (fun x : E => ‖V.orthogonalProjectionOnto x‖^2)
      SubsphereRegression.ambientSphereLaw
      (betaMeasure ((Module.finrank ℝ V : ℝ)/2) ((Module.finrank ℝ Vᗮ : ℝ)/2)) := by
  have ha : 0 < (Module.finrank ℝ V : ℝ)/2 := by have := Module.finrank_pos (R := ℝ) (M := V); positivity
  have hb : 0 < (Module.finrank ℝ Vᗮ : ℝ)/2 := by have := Module.finrank_pos (R := ℝ) (M := Vᗮ); positivity
  have h : MeasurePreserving (fun z : V × Vᗮ => ‖z.1‖^2/(‖z.1‖^2+‖z.2‖^2))
      ((gammaSphere (E := V)).prod (gammaSphere (E := Vᗮ)))
      (betaMeasure ((Module.finrank ℝ V : ℝ)/2) ((Module.finrank ℝ Vᗮ : ℝ)/2)) :=
    (gamma_ratio_preserving ha hb).comp (gammaSphere_sqnorm.prod gammaSphere_sqnorm)
  refine ⟨by fun_prop,?_⟩
  have hp : Measurable (fun x : E => ‖V.orthogonalProjectionOnto x‖^2) := by fun_prop
  rw [← sumGamma_direction V,Measure.map_map hp measurable_normalize,
    sumGamma,Measure.map_map (hp.comp measurable_normalize) (by fun_prop)]
  convert h.map_eq using 1
  congr 1
  funext z
  exact normalize_sum_sqproj V z.1 z.2

end SubsphereCurrent.Mixture
end
end

end OAI
