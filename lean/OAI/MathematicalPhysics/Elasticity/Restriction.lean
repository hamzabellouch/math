import OAI.MathematicalPhysics.Elasticity.Variational

namespace OAI

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Elasticity
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (μ : Measure α) (s : Set α)
def lpRestrictCLM : Lp E 2 μ →L[ℝ] Lp E 2 (μ.restrict s) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using Measure.restrict_le_self (μ := μ) (s := s))
lemma lpRestrict_coe (f : Lp E 2 μ) : (lpRestrictCLM μ s f : α → E)=ᵐ[μ.restrict s] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f
variable (hs : MeasurableSet s)
def lpZeroValue (f : Lp E 2 (μ.restrict s)) : Lp E 2 μ :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator f)
omit [NormedSpace ℝ E] in
lemma lpZeroValue_coe (f : Lp E 2 (μ.restrict s)) :
    (lpZeroValue μ s hs f : α → E)=ᵐ[μ] s.indicator f := by
  unfold lpZeroValue
  exact @MemLp.coeFn_toLp α E _ 2 μ _ (s.indicator (⇑f))
    ((memLp_indicator_iff_restrict (p := 2) (μ := μ) hs).mpr (Lp.memLp f))
omit [NormedSpace ℝ E] in
lemma lpZeroValue_add (f g : Lp E 2 (μ.restrict s)) :
    lpZeroValue μ s hs (f+g)=lpZeroValue μ s hs f+lpZeroValue μ s hs g := by
  apply Lp.ext
  filter_upwards [lpZeroValue_coe μ s hs (f+g),lpZeroValue_coe μ s hs f,
    lpZeroValue_coe μ s hs g,Lp.coeFn_add (lpZeroValue μ s hs f) (lpZeroValue μ s hs g),
    (ae_restrict_iff' hs).mp (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
  rw [h1,h4]
  change s.indicator (⇑(f+g)) x=lpZeroValue μ s hs f x+lpZeroValue μ s hs g x
  rw [h2,h3]
  by_cases hx : x∈s
  · simp only [indicator_of_mem hx,h5 hx,Pi.add_apply]
  · simp only [indicator_of_notMem hx,add_zero]
lemma lpZeroValue_smul (c : ℝ) (f : Lp E 2 (μ.restrict s)) :
    lpZeroValue μ s hs (c • f)=c • lpZeroValue μ s hs f := by
  apply Lp.ext
  filter_upwards [lpZeroValue_coe μ s hs (c • f),lpZeroValue_coe μ s hs f,
    Lp.coeFn_smul c (lpZeroValue μ s hs f),
    (ae_restrict_iff' hs).mp (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
  rw [h1,h3]
  change s.indicator (⇑(c • f)) x=c • lpZeroValue μ s hs f x
  rw [h2]
  by_cases hx : x∈s
  · simp only [indicator_of_mem hx,h4 hx,Pi.smul_apply]
  · simp only [indicator_of_notMem hx,smul_zero]
def lpZeroExtend : Lp E 2 (μ.restrict s) →ₗ[ℝ] Lp E 2 μ where
  toFun := lpZeroValue μ s hs
  map_add' := lpZeroValue_add μ s hs
  map_smul' := lpZeroValue_smul μ s hs
lemma lpZeroExtend_norm (f : Lp E 2 (μ.restrict s)) : ‖lpZeroExtend μ s hs f‖=‖f‖ := by
  change ‖((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator f)‖=‖f‖
  rw [Lp.norm_toLp,Lp.norm_def,eLpNorm_indicator_eq_eLpNorm_restrict hs]
def lpZeroExtendCLM : Lp E 2 (μ.restrict s) →L[ℝ] Lp E 2 μ :=
  (lpZeroExtend μ s hs).mkContinuous 1 (fun f => by rw [lpZeroExtend_norm,one_mul])
lemma lpZeroExtend_coe (f : Lp E 2 (μ.restrict s)) :
    (lpZeroExtendCLM μ s hs f : α → E)=ᵐ[μ] s.indicator f := lpZeroValue_coe μ s hs f
lemma lpRestrict_zeroExtend (f : Lp E 2 (μ.restrict s)) :
    lpRestrictCLM μ s (lpZeroExtendCLM μ s hs f)=f := by
  apply Lp.ext
  filter_upwards [lpRestrict_coe μ s (lpZeroExtendCLM μ s hs f),
    ae_restrict_of_ae (lpZeroExtend_coe μ s hs f),ae_restrict_mem hs] with x h1 h2 hx
  rw [h1,h2,indicator_of_mem hx]
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
namespace Elasticity
variable {Ω B : Set X}
def lpRestrictBetween (h : Ω⊆B) : Lp V 2 (volume.restrict B) →L[ℝ] Lp V 2 (volume.restrict Ω) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa using Measure.restrict_mono h (le_refl (volume : Measure X)))
lemma lpRestrictBetween_coe (h : Ω⊆B) (f : Lp V 2 (volume.restrict B)) :
    (lpRestrictBetween h f : X → V)=ᵐ[volume.restrict Ω] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f
lemma lpRestrictBetween_toLp (h : Ω⊆B) (f : X → V)
    (hf : MemLp f 2 (volume.restrict B)) (hg : MemLp f 2 (volume.restrict Ω)) :
    lpRestrictBetween h (hf.toLp f)=hg.toLp f := by
  apply Lp.ext
  exact (lpRestrictBetween_coe h (hf.toLp f)).trans
    ((Measure.absolutelyContinuous_of_le (Measure.restrict_mono h (le_refl (volume : Measure X)))).ae_eq hf.coeFn_toLp |>.trans hg.coeFn_toLp.symm)
def ambientRestrict (h : Ω⊆B) : Ambient B →L[ℝ] Ambient Ω :=
  (lpRestrictBetween h).prodMap (ContinuousLinearMap.pi
    (fun i : Fin 3 => (lpRestrictBetween h).comp (ContinuousLinearMap.proj i)))
lemma restrict_smoothJet (h : Ω⊆B) {u : Ambient B} (hu : u∈SmoothJets B) :
    ambientRestrict h u∈SmoothJets Ω := by
  obtain ⟨f,hf,hd,hsm,hval,hder⟩ := hu
  have hm : volume.restrict Ω≤volume.restrict B := Measure.restrict_mono h (le_refl (volume : Measure X))
  refine ⟨f,hf.mono_measure hm,(fun i => (hd i).mono_measure hm),hsm,?_,?_⟩
  · change lpRestrictBetween h u.1=_
    rw [hval,lpRestrictBetween_toLp]
  · funext i
    change lpRestrictBetween h (u.2 i)=_
    rw [hder,lpRestrictBetween_toLp]
lemma restrict_h1 (h : Ω⊆B) {u : Ambient B} (hu : u∈closure (SmoothJets B)) :
    ambientRestrict h u∈closure (SmoothJets Ω) := by
  exact (show MapsTo (ambientRestrict h) (SmoothJets B) (SmoothJets Ω) from
    fun _ hu => restrict_smoothJet h hu).closure (ambientRestrict h).continuous hu
def h1Restrict (h : Ω⊆B) (u : H1 B) : H1 Ω := ⟨ambientRestrict h u.val,restrict_h1 h u.property⟩
def lpExtendBetween (hΩ : MeasurableSet Ω) :
    Lp V 2 (volume.restrict Ω) →L[ℝ] Lp V 2 (volume.restrict B) :=
  (lpRestrictCLM volume B).comp (lpZeroExtendCLM volume Ω hΩ)
lemma lpExtendBetween_coe (hΩ : MeasurableSet Ω) (f : Lp V 2 (volume.restrict Ω)) :
    (lpExtendBetween (B := B) hΩ f : X → V)=ᵐ[volume.restrict B] Ω.indicator f :=
  (lpRestrict_coe volume B _).trans (ae_restrict_of_ae (lpZeroExtend_coe volume Ω hΩ f))
lemma lpExtendBetween_toLp (hΩ : MeasurableSet Ω) (f : X → V) (hf : MemLp f 2 (volume.restrict Ω))
    (hg : MemLp f 2 (volume.restrict B)) (hs : tsupport f⊆Ω) :
    lpExtendBetween hΩ (hf.toLp f)=hg.toLp f := by
  apply Lp.ext
  have hval : ∀ᵐ x ∂(volume : Measure X), x∈Ω → hf.toLp f x=f x := (ae_restrict_iff' hΩ).mp hf.coeFn_toLp
  filter_upwards [lpExtendBetween_coe (B := B) hΩ (hf.toLp f),
    ae_restrict_of_ae hval,hg.coeFn_toLp] with x h1 h2 h3
  rw [h1,h3]
  by_cases hx : x∈Ω
  · rw [indicator_of_mem hx,h2 hx]
  · rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]
def ambientExtend (hΩ : MeasurableSet Ω) : Ambient Ω →L[ℝ] Ambient B :=
  (lpExtendBetween hΩ).prodMap (ContinuousLinearMap.pi
    (fun i : Fin 3 => (lpExtendBetween hΩ).comp (ContinuousLinearMap.proj i)))
lemma extend_testJet (hΩ : MeasurableSet Ω) (h : Ω⊆B) {u : Ambient Ω} (hu : u∈TestJets Ω) :
    ambientExtend (B := B) hΩ u∈TestJets B := by
  obtain ⟨f,hf,hd,hsm,hc,hs,hval,hder⟩ := hu
  have hdf (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (coordDeriv f i) :=
    (hsm.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hcd (i : Fin 3) : HasCompactSupport (coordDeriv f i) := hc.fderiv_apply ℝ _
  have hsd (i : Fin 3) : tsupport (coordDeriv f i)⊆Ω :=
    (tsupport_fderiv_apply_subset ℝ (coordVector i)).trans hs
  have hfg : MemLp f 2 (volume.restrict B) := (hsm.continuous.memLp_of_hasCompactSupport hc).restrict B
  have hdg (i : Fin 3) : MemLp (coordDeriv f i) 2 (volume.restrict B) :=
    ((hdf i).continuous.memLp_of_hasCompactSupport (hcd i)).restrict B
  refine ⟨f,hfg,hdg,hsm,hc,hs.trans h,?_,?_⟩
  · change lpExtendBetween hΩ u.1=_
    rw [hval,lpExtendBetween_toLp hΩ f hf hfg hs]
  · funext i
    change lpExtendBetween hΩ (u.2 i)=_
    rw [hder,lpExtendBetween_toLp hΩ _ (hd i) (hdg i) (hsd i)]
lemma extend_h10 (hΩ : MeasurableSet Ω) (h : Ω⊆B) {u : Ambient Ω} (hu : u∈closure (TestJets Ω)) :
    ambientExtend (B := B) hΩ u∈closure (TestJets B) := by
  exact (show MapsTo (ambientExtend (B := B) hΩ) (TestJets Ω) (TestJets B) from
    fun _ hu => extend_testJet hΩ h hu).closure (ambientExtend hΩ).continuous hu
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω B : Set X}
def gradient (u : Ambient Ω) (x : X) : Fin 3 → V := fun i => u.2 i x
def elasticDensity (lam mu : ℝ) (P Q : Fin 3 → V) : ℝ :=
  lam*(∑ i, P i i)*(∑ i, Q i i)+2*mu*∑ i, ∑ j,
    ((P j i+P i j)/2)*((Q j i+Q i j)/2)
def ambientDensity (lam mu : X → ℝ) (u v : Ambient Ω) (x : X) : ℝ :=
  elasticDensity (lam x) (mu x) (gradient u x) (gradient v x)
def ambientEnergy (lam mu : X → ℝ) (u v : Ambient Ω) : ℝ :=
  ∫ x, ambientDensity lam mu u v x ∂(volume.restrict Ω)
lemma energy_eq_ambient (lam mu : X → ℝ) (u v : H1 Ω) :
    energy Ω lam mu u v=ambientEnergy lam mu u.val v.val := rfl
lemma elasticDensity_symm (a b : ℝ) (P Q : Fin 3 → V) :
    elasticDensity a b P Q=elasticDensity a b Q P := by
  unfold elasticDensity
  have hs : (∑ i, ∑ j, ((P j i+P i j)/2)*((Q j i+Q i j)/2))=
      ∑ i, ∑ j, ((Q j i+Q i j)/2)*((P j i+P i j)/2) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hs]
  ring
@[simp] lemma elasticDensity_zero_right (a b : ℝ) (P : Fin 3 → V) :
    elasticDensity a b P 0=0 := by simp [elasticDensity]
lemma gradient_restrict (h : Ω⊆B) (u : Ambient B) :
    (fun x => gradient (ambientRestrict h u) x)=ᵐ[volume.restrict Ω] gradient u := by
  have he := Filter.eventually_all.mpr (fun i : Fin 3 => lpRestrictBetween_coe h (u.2 i))
  filter_upwards [he] with x hx
  exact funext hx
lemma gradient_extend (hΩ : MeasurableSet Ω) (u : Ambient Ω) :
    (fun x => gradient (ambientExtend (B := B) hΩ u) x)=ᵐ[volume.restrict B] Ω.indicator (gradient u) := by
  have he := Filter.eventually_all.mpr (fun i : Fin 3 => lpExtendBetween_coe (B := B) hΩ (u.2 i))
  filter_upwards [he] with x hx
  by_cases hm : x∈Ω
  · rw [indicator_of_mem hm]
    funext i
    exact (hx i).trans (indicator_of_mem hm _)
  · rw [indicator_of_notMem hm]
    funext i
    exact (hx i).trans (indicator_of_notMem hm _)
lemma entry_memLp (u : Ambient Ω) (i j : Fin 3) :
    MemLp (fun x => u.2 j x i) 2 (volume.restrict Ω) :=
  (EuclideanSpace.proj i : V →L[ℝ] ℝ).comp_memLp (u.2 j)
lemma BoundedCoefficient.mul_memLp_fun {a f : X → ℝ} (ha : BoundedCoefficient Ω a)
    (hf : MemLp f 2 (volume.restrict Ω)) : MemLp (fun x => a x*f x) 2 (volume.restrict Ω) := by
  obtain ⟨C,hC⟩ := ha.bound
  apply hf.of_le_mul (c := C) (ha.measurable.mul hf.aestronglyMeasurable)
  filter_upwards [hC] with x hx
  simpa only [Pi.mul_apply,norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))
lemma ambientDensity_integrable {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) (u v : Ambient Ω) :
    Integrable (ambientDensity lam mu u v) (volume.restrict Ω) := by
  have hd (w : Ambient Ω) : MemLp (fun x => ∑ i, w.2 i x i) 2 (volume.restrict Ω) :=
    memLp_finsetSum _ (fun i _ => entry_memLp w i i)
  have hs (w : Ambient Ω) (i j : Fin 3) :
      MemLp (fun x => (w.2 j x i+w.2 i x j)/2) 2 (volume.restrict Ω) :=
    by simpa only [div_eq_mul_inv,Pi.add_apply] using
      ((entry_memLp w i j).add (entry_memLp w j i)).mul_const (2 : ℝ)⁻¹
  have hL := (hl.mul_memLp_fun (hd u)).integrable_mul (hd v)
  have hS (i j) := (hm.mul_memLp_fun (hs u i j)).integrable_mul (hs v i j)
  have hsum := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hS i j))
  apply (hL.add (hsum.const_mul 2)).congr
  exact Filter.Eventually.of_forall (fun x => by
    simp only [ambientDensity,elasticDensity,gradient,Pi.mul_apply,Pi.add_apply,Finset.mul_sum,mul_assoc])
lemma ambientEnergy_symm (lam mu : X → ℝ) (u v : Ambient Ω) :
    ambientEnergy lam mu u v=ambientEnergy lam mu v u := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => elasticDensity_symm _ _ _ _)
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω B : Set X}
lemma ambientEnergy_extend_right (hΩ : MeasurableSet Ω) (h : Ω⊆B)
    (lam mu : X → ℝ) (u : Ambient B) (v : Ambient Ω) :
    ambientEnergy lam mu u (ambientExtend hΩ v)=
      ambientEnergy lam mu (ambientRestrict h u) v := by
  let f := fun x => elasticDensity (lam x) (mu x) (gradient u x) (gradient v x)
  calc
    _ = ∫ x, Ω.indicator f x ∂(volume.restrict B) := by
      apply integral_congr_ae
      filter_upwards [gradient_extend (B := B) hΩ v] with x hx
      change elasticDensity _ _ _ _=_
      rw [hx]
      by_cases hm : x∈Ω
      · simp only [indicator_of_mem hm]
        rfl
      · simp only [indicator_of_notMem hm,elasticDensity_zero_right]
    _ = ∫ x, f x ∂(volume.restrict Ω) := by
      rw [integral_indicator hΩ,Measure.restrict_restrict hΩ,inter_eq_left.mpr h]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [gradient_restrict h u] with x hx
      exact congrArg (fun P => elasticDensity (lam x) (mu x) P (gradient v x)) hx.symm
lemma ambientEnergy_extend_left (hΩ : MeasurableSet Ω) (h : Ω⊆B)
    (lam mu : X → ℝ) (u : Ambient Ω) (v : Ambient B) :
    ambientEnergy lam mu (ambientExtend hΩ u) v=
      ambientEnergy lam mu u (ambientRestrict h v) := by
  rw [ambientEnergy_symm,ambientEnergy_extend_right hΩ h,ambientEnergy_symm]
lemma BoundedCoefficient.restrict {a : X → ℝ} (ha : BoundedCoefficient B a) (h : Ω⊆B) :
    BoundedCoefficient Ω a := by
  have hm : volume.restrict Ω≤volume.restrict B := Measure.restrict_mono h (le_refl (volume : Measure X))
  refine ⟨ha.measurable.mono_measure hm,?_⟩
  obtain ⟨C,hC⟩ := ha.bound
  exact ⟨C,ae_mono hm hC⟩
lemma energy_coefficient_locality {lam₁ mu₁ lam₂ mu₂ : X → ℝ}
    (hl₁ : BoundedCoefficient B lam₁) (hm₁ : BoundedCoefficient B mu₁)
    (hl₂ : BoundedCoefficient B lam₂) (hm₂ : BoundedCoefficient B mu₂)
    (hΩ : MeasurableSet Ω) (h : Ω⊆B)
    (he : ∀ x∉Ω, lam₁ x=lam₂ x ∧ mu₁ x=mu₂ x) (u v : Ambient B) :
    ambientEnergy lam₂ mu₂ u v-ambientEnergy lam₁ mu₁ u v=
      ambientEnergy lam₂ mu₂ (ambientRestrict h u) (ambientRestrict h v)-
      ambientEnergy lam₁ mu₁ (ambientRestrict h u) (ambientRestrict h v) := by
  let f := fun x => ambientDensity lam₂ mu₂ u v x-ambientDensity lam₁ mu₁ u v x
  calc
    _ = ∫ x, f x ∂(volume.restrict B) := (integral_sub
      (ambientDensity_integrable hl₂ hm₂ u v) (ambientDensity_integrable hl₁ hm₁ u v)).symm
    _ = ∫ x, Ω.indicator f x ∂(volume.restrict B) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x∈Ω
        · rw [indicator_of_mem hx]
        · rw [indicator_of_notMem hx]
          dsimp [f,ambientDensity]
          rw [(he x hx).1,(he x hx).2,sub_self])
    _ = ∫ x, f x ∂(volume.restrict Ω) := by
      rw [integral_indicator hΩ,Measure.restrict_restrict hΩ,inter_eq_left.mpr h]
    _ = ∫ x, ambientDensity lam₂ mu₂ (ambientRestrict h u) (ambientRestrict h v) x-
        ambientDensity lam₁ mu₁ (ambientRestrict h u) (ambientRestrict h v) x ∂(volume.restrict Ω) := by
      apply integral_congr_ae
      filter_upwards [gradient_restrict h u,gradient_restrict h v] with x hu hv
      simp only [f,ambientDensity,hu,hv]
    _ = _ := integral_sub (ambientDensity_integrable (hl₂.restrict h) (hm₂.restrict h) _ _)
      (ambientDensity_integrable (hl₁.restrict h) (hm₁.restrict h) _ _)
lemma elasticDensity_add_left (a b : ℝ) (P Q R : Fin 3 → V) :
    elasticDensity a b (P+Q) R=elasticDensity a b P R+elasticDensity a b Q R := by
  simp only [elasticDensity,Pi.add_apply,PiLp.add_apply]
  have he (i j : Fin 3) : ((P j i+Q j i+(P i j+Q i j))/2)*((R j i+R i j)/2)=
      ((P j i+P i j)/2)*((R j i+R i j)/2)+((Q j i+Q i j)/2)*((R j i+R i j)/2) := by ring
  simp only [he,Finset.sum_add_distrib]
  ring
lemma gradient_add (u v : Ambient Ω) :
    gradient (u+v)=ᵐ[volume.restrict Ω] fun x => gradient u x+gradient v x := by
  have he := Filter.eventually_all.mpr (fun i : Fin 3 => Lp.coeFn_add (u.2 i) (v.2 i))
  filter_upwards [he] with x hx
  exact funext hx
lemma ambientEnergy_add_left {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) (u v w : Ambient Ω) :
    ambientEnergy lam mu (u+v) w=ambientEnergy lam mu u w+ambientEnergy lam mu v w := by
  rw [ambientEnergy,ambientEnergy,ambientEnergy,← integral_add
    (ambientDensity_integrable hl hm u w) (ambientDensity_integrable hl hm v w)]
  apply integral_congr_ae
  filter_upwards [gradient_add u v] with x hx
  change elasticDensity _ _ _ _=_
  rw [hx,elasticDensity_add_left]
  rfl
lemma ambientEnergy_sub_left {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) (u v w : Ambient Ω) :
    ambientEnergy lam mu (u-v) w=ambientEnergy lam mu u w-ambientEnergy lam mu v w := by
  have he := ambientEnergy_add_left hl hm (u-v) v w
  rw [sub_add_cancel] at he
  linarith
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
namespace Elasticity
variable {Ω B : Set X}
lemma lpRestrictBetween_extend (hΩ : MeasurableSet Ω) (h : Ω⊆B)
    (f : Lp V 2 (volume.restrict Ω)) : lpRestrictBetween h (lpExtendBetween hΩ f)=f := by
  apply Lp.ext
  have hm : volume.restrict Ω≤volume.restrict B := Measure.restrict_mono h (le_refl (volume : Measure X))
  filter_upwards [lpRestrictBetween_coe h (lpExtendBetween hΩ f),
    (Measure.absolutelyContinuous_of_le hm).ae_eq (lpExtendBetween_coe (B := B) hΩ f),
    ae_restrict_mem hΩ] with x hx hy hz
  rw [hx,hy,indicator_of_mem hz]
lemma ambientRestrict_extend (hΩ : MeasurableSet Ω) (h : Ω⊆B) (u : Ambient Ω) :
    ambientRestrict h (ambientExtend hΩ u)=u := by
  apply Prod.ext
  · exact lpRestrictBetween_extend hΩ h u.1
  · funext i
    exact lpRestrictBetween_extend hΩ h (u.2 i)
def h1Extend (hΩ : MeasurableSet Ω) (h : Ω⊆B) (u : H1 Ω) (hu : HasZeroTrace Ω u) : H1 B :=
  ⟨ambientExtend hΩ u.val,h10Submodule_le B (extend_h10 hΩ h hu)⟩
lemma weakSolution_restrict (hΩ : MeasurableSet Ω) (h : Ω⊆B) {lam mu : X → ℝ}
    {u : H1 B} (hu : WeakSolution B lam mu u) : WeakSolution Ω lam mu (h1Restrict h u) := by
  intro v hv
  have he := hu (h1Extend hΩ h v hv) (extend_h10 hΩ h hv)
  change ambientEnergy lam mu u.val (ambientExtend hΩ v.val)=0 at he
  rw [ambientEnergy_extend_right hΩ h] at he
  exact he
def gluedH1 (hΩ : MeasurableSet Ω) (h : Ω⊆B) (u : H1 B) (v : H1 Ω)
    (ht : SameTrace Ω v (h1Restrict h u)) : H1 B :=
  ⟨u.val+ambientExtend hΩ (v.val-ambientRestrict h u.val),
    (h1Submodule B).add_mem u.property (h10Submodule_le B (extend_h10 hΩ h ht))⟩
lemma gluedH1_restrict (hΩ : MeasurableSet Ω) (h : Ω⊆B) (u : H1 B) (v : H1 Ω)
    (ht : SameTrace Ω v (h1Restrict h u)) : h1Restrict h (gluedH1 hΩ h u v ht)=v := by
  apply Subtype.ext
  change ambientRestrict h (u.val+ambientExtend hΩ (v.val-ambientRestrict h u.val))=v.val
  rw [map_add,ambientRestrict_extend]
  abel
lemma gluedH1_exterior_gradient (hΩ : MeasurableSet Ω) (h : Ω⊆B) (u : H1 B) (v : H1 Ω)
    (ht : SameTrace Ω v (h1Restrict h u)) :
    ∀ᵐ x ∂(volume.restrict B), x∉Ω → gradient (gluedH1 hΩ h u v ht).val x=gradient u.val x := by
  filter_upwards [gradient_add u.val (ambientExtend (B := B) hΩ (v.val-ambientRestrict h u.val)),
    gradient_extend (B := B) hΩ (v.val-ambientRestrict h u.val)] with x ha he hx
  change gradient (u.val+ambientExtend hΩ (v.val-ambientRestrict h u.val)) x=_
  rw [ha,he,indicator_of_notMem hx,add_zero]
lemma gluedH1_exterior_value (hΩ : MeasurableSet Ω) (h : Ω⊆B) (u : H1 B) (v : H1 Ω)
    (ht : SameTrace Ω v (h1Restrict h u)) :
    ∀ᵐ x ∂(volume.restrict B), x∉Ω → (gluedH1 hΩ h u v ht).val.1 x=u.val.1 x := by
  filter_upwards [Lp.coeFn_add u.val.1 (lpExtendBetween (B := B) hΩ (v.val-ambientRestrict h u.val).1),
    lpExtendBetween_coe (B := B) hΩ (v.val-ambientRestrict h u.val).1] with x ha he hx
  change (u.val.1+lpExtendBetween hΩ (v.val-ambientRestrict h u.val).1 : Lp V 2 (volume.restrict B)) x=_
  rw [ha]
  change u.val.1 x+lpExtendBetween hΩ (v.val-ambientRestrict h u.val).1 x=_
  rw [he,indicator_of_notMem hx,add_zero]

theorem physical_weak_transfer {lam₁ mu₁ lam₂ mu₂ : X → ℝ}
    (ha₁ : Admissible Ω lam₁ mu₁) (ha₂ : Admissible Ω lam₂ mu₂)
    (hO : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (h : Ω⊆B)
    (hl₁ : BoundedCoefficient B lam₁) (hm₁ : BoundedCoefficient B mu₁)
    (hl₂ : BoundedCoefficient B lam₂) (hm₂ : BoundedCoefficient B mu₂)
    (he : ∀ x∉Ω, lam₁ x=lam₂ x ∧ mu₁ x=mu₂ x)
    (hDN : DN Ω lam₁ mu₁=DN Ω lam₂ mu₂)
    {u : H1 B} (hu : WeakSolution B lam₁ mu₁ u) :
    ∃ v : H1 B, WeakSolution B lam₂ mu₂ v ∧
      (∀ᵐ x ∂(volume.restrict B), x∉Ω → v.val.1 x=u.val.1 x) ∧
      (∀ᵐ x ∂(volume.restrict B), x∉Ω → gradient v.val x=gradient u.val x) := by
  obtain ⟨v,hv,ht,hpair⟩ := interior_physical_transfer ha₁ ha₂ hO hOB hDN
    (weakSolution_restrict hO.measurableSet h hu)
  have ht' : SameTrace Ω v (h1Restrict h u) := (trace_eq_iff _ _).mp ht
  refine ⟨gluedH1 hO.measurableSet h u v ht',?_,
    gluedH1_exterior_value hO.measurableSet h u v ht',
    gluedH1_exterior_gradient hO.measurableSet h u v ht'⟩
  intro w hw
  have hw0 := hu w hw
  have hp := hpair (h1Restrict h w)
  simp only [energy_eq_ambient] at hp hw0 ⊢
  change ambientEnergy lam₂ mu₂ (u.val+ambientExtend hO.measurableSet
    (v.val-ambientRestrict h u.val)) w.val=0
  rw [ambientEnergy_add_left hl₂ hm₂,ambientEnergy_extend_left hO.measurableSet h,
    ambientEnergy_sub_left (hl₂.restrict h) (hm₂.restrict h)]
  have hc := energy_coefficient_locality hl₁ hm₁ hl₂ hm₂ hO.measurableSet h he u.val w.val
  change ambientEnergy lam₂ mu₂ v.val (ambientRestrict h w.val)=
    ambientEnergy lam₁ mu₁ (ambientRestrict h u.val) (ambientRestrict h w.val) at hp
  linarith
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}
def ambientScalar (Ω : Set X) (k : Option (Fin 3)) (i : Fin 3) :
    Ambient Ω →L[ℝ] ScalarL2 Ω := (jetScalar Ω k i).comp (jetEquiv Ω).symm.toContinuousLinearMap
lemma ambientScalar_ae (u : Ambient Ω) (k : Option (Fin 3)) (i : Fin 3) :
    ambientScalar Ω k i u =ᵐ[volume.restrict Ω] fun x => ((jetEquiv Ω).symm u k x) i :=
  jetScalar_ae _ _ _
lemma scalar_pair_smooth {f : X → V} (hf : MemLp f 2 (volume.restrict Ω))
    (g : SchwartzMap X ℝ) (i : Fin 3) :
    inner ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) (hf.toLp f))
      (schwartzR Ω g) = ∫ x, (f x) i*g x ∂(volume.restrict Ω) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (EuclideanSpace.proj (𝕜 := ℝ) i) (hf.toLp f),
    hf.coeFn_toLp,g.coeFn_toLp 2 (volume.restrict Ω)] with x hx hy hz
  change inner ℝ (((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) (hf.toLp f)) x) (g.toLp 2 (volume.restrict Ω) x)=_
  rw [hx,hz,hy]
  exact real_inner_comm _ _
lemma smooth_ibp {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ) ⊆ Ω) (j : Fin 3) :
    (∫ x, f x*ElasticityKorn.d (coordVector j) g x ∂(volume.restrict Ω)) =
    -(∫ x, fderiv ℝ f x (coordVector j)*g x ∂(volume.restrict Ω)) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (g : X → ℝ) := g.smooth _
  have hd : Continuous (fun x => fderiv ℝ f x (coordVector j)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgd : Continuous (fun x => fderiv ℝ (g : X → ℝ) x (coordVector j)) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hz := image_eq_zero_of_notMem_tsupport (f := (ElasticityKorn.d (coordVector j) g : X → ℝ))
      (fun ht => hx (hs ((tsupport_fderiv_apply_subset ℝ (coordVector j)) ht)))
    rw [hz,mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (f := (g : X → ℝ)) (fun ht => hx (hs ht)),mul_zero])]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hd.mul hg.continuous).integrable_of_hasCompactSupport (hc.mul_left))
    ((hf.continuous.mul hgd).integrable_of_hasCompactSupport ((hc.fderiv_apply ℝ _).mul_left))
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hc.mul_left))
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x)

def weakDerivativePair (Ω : Set X) (g : SchwartzMap X ℝ) (i j : Fin 3) : Ambient Ω →L[ℝ] ℝ :=
  ((innerSL ℝ (schwartzR Ω (ElasticityKorn.d (coordVector j) g))).comp (ambientScalar Ω none i)) +
  ((innerSL ℝ (schwartzR Ω g)).comp (ambientScalar Ω (some j) i))
lemma weakDerivativePair_smooth (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ) ⊆ Ω) (i j : Fin 3) {u : Ambient Ω} (hu : u∈SmoothJets Ω) :
    weakDerivativePair Ω g i j u=0 := by
  obtain ⟨f,hf,hd,hsm,hu,huj⟩ := hu
  have he0 : ambientScalar Ω none i u=
      (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) (hf.toLp f) := by
    change (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) u.1=_
    rw [hu]
  have he1 : ambientScalar Ω (some j) i u=
      (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) ((hd j).toLp (coordDeriv f j)) := by
    change (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) (u.2 j)=_
    rw [huj]
  simp only [weakDerivativePair,add_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,he0,he1]
  rw [← real_inner_comm (schwartzR Ω (ElasticityKorn.d (coordVector j) g)),
    ← real_inner_comm (schwartzR Ω g),scalar_pair_smooth,scalar_pair_smooth]
  have hh := smooth_ibp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hsm) g hc hs j
  change (∫ x, (f x) i * ElasticityKorn.d (coordVector j) g x ∂(volume.restrict Ω)) =
    -(∫ x, fderiv ℝ (fun y => (f y) i) x (coordVector j) * g x ∂(volume.restrict Ω)) at hh
  simp only [coordDeriv_scalar f hsm] at hh
  rw [hh,neg_add_cancel]
/-- The gradient components in the closure-of-jets H1 really are weak
partial derivatives of its value. No weak-derivative property is assumed. -/
theorem h1_weak_derivative (u : H1 Ω) (g : SchwartzMap X ℝ)
    (hc : HasCompactSupport (g : X → ℝ)) (hs : tsupport (g : X → ℝ) ⊆ Ω)
    (i j : Fin 3) :
    inner ℝ (ambientScalar Ω none i u.val) (schwartzR Ω (ElasticityKorn.d (coordVector j) g)) =
      -inner ℝ (ambientScalar Ω (some j) i u.val) (schwartzR Ω g) := by
  have hm : MapsTo (weakDerivativePair Ω g i j) (SmoothJets Ω) ({0} : Set ℝ) :=
    fun _ hu => weakDerivativePair_smooth g hc hs i j hu
  have hh := hm.closure (weakDerivativePair Ω g i j).continuous u.property
  rw [closure_singleton] at hh
  change weakDerivativePair Ω g i j u.val=0 at hh
  simp only [weakDerivativePair,add_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply] at hh
  rw [← real_inner_comm (schwartzR Ω (ElasticityKorn.d (coordVector j) g)),
    ← real_inner_comm (schwartzR Ω g)] at hh
  linarith
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}
def testField (g : SchwartzMap X ℝ) (i : Fin 3) : X → V := fun x => g x • coordVector i
lemma testField_smooth (g : SchwartzMap X ℝ) (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (testField g i) :=
  (g.smooth _).smul contDiff_const
lemma testField_deriv (g : SchwartzMap X ℝ) (i j : Fin 3) :
    coordDeriv (testField g i) j=fun x => ElasticityKorn.d (coordVector j) g x • coordVector i := by
  funext x
  have h := ((ContinuousLinearMap.toSpanSingleton ℝ (coordVector i)).hasFDerivAt (x := g x)).comp x
    (g.differentiableAt (x := x)).hasFDerivAt
  change fderiv ℝ ((ContinuousLinearMap.toSpanSingleton ℝ (coordVector i)) ∘ (g : X → ℝ)) x (coordVector j)=_
  rw [h.fderiv]
  rfl
lemma testField_compact (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ)) (i : Fin 3) :
    HasCompactSupport (testField g i) := hc.comp_left (g := fun a : ℝ => a • coordVector i) (zero_smul ..)
lemma testField_support (g : SchwartzMap X ℝ) (i : Fin 3) :
    tsupport (testField g i) ⊆ tsupport (g : X → ℝ) :=
  tsupport_comp_subset (g := fun a : ℝ => a • coordVector i) (zero_smul ..) _
lemma testField_memLp (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ)) (i : Fin 3) :
    MemLp (testField g i) 2 (volume.restrict Ω) :=
  ((testField_smooth g i).continuous.memLp_of_hasCompactSupport (testField_compact g hc i)).restrict Ω
lemma testField_deriv_memLp (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ)) (i j : Fin 3) :
    MemLp (coordDeriv (testField g i) j) 2 (volume.restrict Ω) :=
  (((testField_smooth g i).continuous_fderiv (by simp)).clm_apply continuous_const
    |>.memLp_of_hasCompactSupport ((testField_compact g hc i).fderiv_apply ℝ (coordVector j))).restrict Ω
 def testFieldJet (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ)) (i : Fin 3) : Ambient Ω :=
  ((testField_memLp g hc i).toLp _,fun j => (testField_deriv_memLp g hc i j).toLp _)
lemma testFieldJet_mem (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) : testFieldJet (Ω := Ω) g hc i∈TestJets Ω := by
  refine ⟨testField g i,testField_memLp g hc i,testField_deriv_memLp g hc i,testField_smooth g i,testField_compact g hc i,
    (testField_support g i).trans hs,rfl,rfl⟩
def testH1 (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) : H1 Ω :=
  ⟨testFieldJet g hc i,h10Submodule_le Ω (subset_closure (testFieldJet_mem g hc hs i))⟩
lemma testH1_zeroTrace (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) : HasZeroTrace Ω (testH1 g hc hs i) :=
  subset_closure (testFieldJet_mem g hc hs i)
lemma testH1_gradient (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) :
    ∀ᵐ x ∂(volume.restrict Ω), gradient (testH1 g hc hs i).val x=
      fun j => ElasticityKorn.d (coordVector j) g x • coordVector i := by
  have he : ∀ᵐ x ∂(volume.restrict Ω), ∀ j, (testFieldJet (Ω := Ω) g hc i).2 j x=coordDeriv (testField g i) j x :=
    Filter.eventually_all.mpr (fun j => (testField_deriv_memLp g hc i j).coeFn_toLp)
  filter_upwards [he] with x hx
  funext j
  change (testFieldJet (Ω := Ω) g hc i).2 j x=_
  rw [hx,testField_deriv]
lemma density_single (a b : ℝ) (P : Fin 3 → V) (v : Fin 3 → ℝ) (i : Fin 3) :
    elasticDensity a b P (fun j => v j • coordVector i)=
      a*(∑ k, P k k)*v i+b*∑ j, (P j i+P i j)*v j := by
  fin_cases i <;> simp [elasticDensity,Fin.sum_univ_succ,coordVector] <;> ring
end Elasticity

end
end

end OAI
