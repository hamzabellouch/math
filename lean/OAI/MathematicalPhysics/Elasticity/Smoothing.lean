import OAI.MathematicalPhysics.Elasticity.Supported

namespace OAI

noncomputable section

namespace ElasticityCoordinates
/-! Actual Haar/L2 and tempered-distribution change of linear coordinates.
The Jacobian is derived from Haar uniqueness, not silently set equal to one. -/
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal NNReal LineDeriv
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]

omit [FiniteDimensional ℝ F] in
lemma linear_haar (L : F ≃L[ℝ] E) :
    ∃ c : ℝ≥0,0<c ∧ (volume : Measure F).map L=c • (volume : Measure E) := by
  have : Measure.IsAddHaarMeasure ((volume : Measure F).map L) := L.isAddHaarMeasure_map volume
  exact ⟨Measure.addHaarScalarFactor ((volume : Measure F).map L) (volume : Measure E),
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,
    Measure.isAddLeftInvariant_eq_smul _ _⟩

omit [FiniteDimensional ℝ F] in
lemma memLp_linear (L : F ≃L[ℝ] E) {u : E → ℂ} {p : ℝ≥0∞}
    (hu : MemLp u p volume) : MemLp (u ∘ L) p volume := by
  obtain ⟨c,_,hc⟩ := linear_haar L
  apply MemLp.comp_of_map _ L.continuous.measurable.aemeasurable
  rw [hc]
  exact hu.smul_measure ENNReal.coe_ne_top

variable [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth]

def linearPull (L : F ≃L[ℝ] E) (D : 𝓢'(E,ℂ)) : 𝓢'(F,ℂ) :=
  D.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm)
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth] in
lemma linearPull_apply (L : F ≃L[ℝ] E) (D : 𝓢'(E,ℂ)) (φ : 𝓢(F,ℂ)) :
    linearPull L D φ=D (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm φ) := rfl
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth] in
lemma linearPull_add (L : F ≃L[ℝ] E) (D T : 𝓢'(E,ℂ)) :
    linearPull L (D+T)=linearPull L D+linearPull L T := by ext φ; rfl
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth] in
lemma linearPull_smul (L : F ≃L[ℝ] E) (c : ℂ) (D : 𝓢'(E,ℂ)) :
    linearPull L (c • D)=c • linearPull L D := by ext φ; rfl
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth] in
lemma linearPull_zero (L : F ≃L[ℝ] E) : linearPull L (0 : 𝓢'(E,ℂ))=0 := by ext φ; rfl
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth] in
lemma linearPull_deriv (L : F ≃L[ℝ] E) (v : F) (D : 𝓢'(E,ℂ)) :
    linearPull L (∂_{L v} D)=∂_{v} (linearPull L D) := by
  ext φ
  simp only [linearPull_apply,TemperedDistribution.lineDerivOp_apply_apply]
  congr 1
  rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.symm_apply_apply,map_neg]

def pullLp (L : F ≃L[ℝ] E) (u : Lp ℂ 2 (volume : Measure E)) : Lp ℂ 2 (volume : Measure F) :=
  (memLp_linear L (Lp.memLp u)).toLp (u ∘ L)
omit [FiniteDimensional ℝ F] [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth] in
lemma pullLp_coe (L : F ≃L[ℝ] E) (u : Lp ℂ 2 (volume : Measure E)) :
    (pullLp L u : F → ℂ)=ᵐ[volume] (u ∘ L) := (memLp_linear L (Lp.memLp u)).coeFn_toLp

omit [FiniteDimensional ℝ F] in
lemma pullLp_distribution (L : F ≃L[ℝ] E) (c : ℝ≥0)
    (hc : (volume : Measure F).map L=c • (volume : Measure E))
    (u : Lp ℂ 2 (volume : Measure E)) :
    (pullLp L u : 𝓢'(F,ℂ))=(c : ℂ) • linearPull L (u : 𝓢'(E,ℂ)) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply,smul_apply,linearPull_apply,smul_eq_mul]
  have he : (∫ q : F,φ q*pullLp L u q)=∫ q : F,φ q*u (L q) := by
    apply integral_congr_ae
    filter_upwards [pullLp_coe L u] with q hq
    rw [hq]
    rfl
  rw [he]
  have hh := integral_map_equiv (μ := (volume : Measure F)) (L.toHomeomorph.toMeasurableEquiv)
    (fun x : E => φ (L.symm x)*u x)
  change (∫ x : E, φ (L.symm x)*u x ∂((volume : Measure F).map L))=
    ∫ q : F, φ (L.symm (L q))*u (L q) at hh
  rw [hc,integral_smul_nnreal_measure] at hh
  simpa only [ContinuousLinearEquiv.symm_apply_apply,NNReal.smul_def,Complex.real_smul,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply] using hh.symm

omit [FiniteDimensional ℝ F] in
lemma pullLp_equation (L : F ≃L[ℝ] E) (v w : F)
    (u f : Lp ℂ 2 (volume : Measure E))
    (he : ∂_{L v} (u : 𝓢'(E,ℂ))+Complex.I • ∂_{L w} (u : 𝓢'(E,ℂ))+
      (f : 𝓢'(E,ℂ))=0) :
    ∂_{v} (pullLp L u : 𝓢'(F,ℂ))+Complex.I • ∂_{w} (pullLp L u : 𝓢'(F,ℂ))+
      (pullLp L f : 𝓢'(F,ℂ))=0 := by
  obtain ⟨c,_,hc⟩ := linear_haar L
  have hh := congrArg (linearPull L) he
  simp only [linearPull_add,linearPull_smul,linearPull_deriv,linearPull_zero] at hh
  rw [pullLp_distribution L c hc u,pullLp_distribution L c hc f]
  simp only [LineDeriv.lineDerivOp_smul]
  rw [smul_comm Complex.I (c : ℂ),← smul_add,← smul_add,hh,smul_zero]

end ElasticityCoordinates
namespace ElasticityCoordinates
open MeasureTheory Set
open scoped ENNReal NNReal
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]

lemma ae_linear (L : F ≃L[ℝ] E) {p : E → Prop} (hp : ∀ᵐ x,p x) : ∀ᵐ q,p (L q) := by
  obtain ⟨c,_hc,hm⟩ := linear_haar L
  have hh : ∀ᵐ x ∂((volume : Measure F).map L),p x := by
    rw [hm]
    exact Measure.ae_smul_measure hp c
  exact ae_of_ae_map L.continuous.measurable.aemeasurable hh

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
lemma lp_integrable_supported {K : Set E} (hK : IsCompact K)
    (u : Lp ℂ 2 (volume : Measure E)) (hu : ∀ᵐ x,x∉K → u x=0) : Integrable (u : E → ℂ) := by
  have hres : MemLp (u : E → ℂ) 2 (volume.restrict K) := (Lp.memLp u).restrict K
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := (volume : Measure E))⟩
  have hi : IntegrableOn (u : E → ℂ) K := hres.integrable (by norm_num)
  have he : K.indicator (u : E → ℂ)=ᵐ[volume] (u : E → ℂ) := by
    filter_upwards [hu] with x hx
    by_cases h : x∈K
    · exact indicator_of_mem h _
    · simp only [indicator_of_notMem h,hx h]
  exact (hi.integrable_indicator hK.measurableSet).congr he
end ElasticityCoordinates
namespace ElasticityCoordinates
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E P n : Type*} [Fintype n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]

/-- Smoothness of an actual compactly supported matrix transport weak solution
in arbitrary linear transverse coordinates. The representative equals the
original L2 function almost everywhere; no exceptional planes remain. -/
theorem planar_smooth_representative (L : (P × ℂ) ≃L[ℝ] E)
    (T K : Set E) (hT : IsCompact T) (hK : IsCompact K)
    (a : n → n → E → ℂ) (ha : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (has : ∀ i j x,x∉K → a i j x=0)
    (f : n → E → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i x,x∉K → f i x=0)
    (u w : n → Lp ℂ 2 (volume : Measure E))
    (hus : ∀ i,∀ᵐ x,x∉T → u i x=0) (hws : ∀ i,∀ᵐ x,x∉T → w i x=0)
    (hc : ∀ i,∀ᵐ x,w i x=∑ j,a i j x*u j x-f i x)
    (he : ∀ i,∂_{L (0,1)} (u i : 𝓢'(E,ℂ))+
      Complex.I • ∂_{L (0,Complex.I)} (u i : 𝓢'(E,ℂ))+(w i : 𝓢'(E,ℂ))=0) :
    ∃ v : n → E → ℂ,(∀ i,ContDiff ℝ (⊤ : ℕ∞) (v i)) ∧
      (∀ i,(u i : E → ℂ)=ᵐ[volume] v i) := by
  classical
  have : (volume : Measure (P × ℂ)).HasTemperateGrowth := by
    change (volume.prod volume).HasTemperateGrowth
    infer_instance
  have : Measure.IsAddHaarMeasure (volume : Measure (P × ℂ)) := by
    change Measure.IsAddHaarMeasure (volume.prod volume)
    infer_instance
  let S := (fun x : E => (L.symm x).2) '' T
  let Q := (fun x : E => (L.symm x).2) '' K
  have hS : IsCompact S := hT.image (continuous_snd.comp L.symm.continuous)
  have hQ : IsCompact Q := hK.image (continuous_snd.comp L.symm.continuous)
  let U := fun i => pullLp L (u i)
  let W := fun i => pullLp L (w i)
  have hsU (i) : ∀ᵐ q : P × ℂ,q.2∉S → U i q=0 := by
    filter_upwards [pullLp_coe L (u i),ae_linear L (hus i)] with q hq hqu
    intro hqs
    rw [hq]
    apply hqu
    intro hqt
    exact hqs ⟨L q,hqt,by simp⟩
  have hsW (i) : ∀ᵐ q : P × ℂ,q.2∉S → W i q=0 := by
    filter_upwards [pullLp_coe L (w i),ae_linear L (hws i)] with q hq hqw
    intro hqs
    rw [hq]
    apply hqw
    intro hqt
    exact hqs ⟨L q,hqt,by simp⟩
  have compactU (i) : ∀ᵐ q : P × ℂ,q∉L.symm '' T → U i q=0 := by
    filter_upwards [pullLp_coe L (u i),ae_linear L (hus i)] with q hq hqu
    intro hqs
    rw [hq]
    exact hqu (fun hh => hqs ⟨L q,hh,L.symm_apply_apply q⟩)
  have compactW (i) : ∀ᵐ q : P × ℂ,q∉L.symm '' T → W i q=0 := by
    filter_upwards [pullLp_coe L (w i),ae_linear L (hws i)] with q hq hqw
    intro hqs
    rw [hq]
    exact hqw (fun hh => hqs ⟨L q,hh,L.symm_apply_apply q⟩)
  have huI (i) := lp_integrable_supported (hT.image L.symm.continuous) (U i) (compactU i)
  have hwI (i) := lp_integrable_supported (hT.image L.symm.continuous) (W i) (compactW i)
  have hcc (i) : ∀ᵐ q : P × ℂ,W i q=∑ j,a i j (L q)*U j q-f i (L q) := by
    have huall : ∀ᵐ q : P × ℂ,∀ j,U j q=u j (L q) := by
      rw [ae_all_iff]
      exact fun j => pullLp_coe L (u j)
    filter_upwards [pullLp_coe L (w i),huall,ae_linear L (hc i)] with q hwq huq hq
    change W i q=w i (L q) at hwq
    rw [hwq]
    simp_rw [huq]
    exact hq
  obtain ⟨v,hv,_hvs,_hve,hvu⟩ := ElasticityGeneralSlicing.smooth_cylinder_representative S Q hS hQ
    (fun i j q => a i j (L q)) (fun i j => (ha i j).comp L.contDiff)
    (fun i j t z hz => has i j _ (fun hh => hz ⟨L (t,z),hh,by simp⟩))
    (fun i q => f i (L q)) (fun i => (hf i).comp L.contDiff)
    (fun i t z hz => hfs i _ (fun hh => hz ⟨L (t,z),hh,by simp⟩))
    U W huI hwI hsU hsW hcc (fun i => pullLp_equation L (0,1) (0,Complex.I) (u i) (w i) (he i))
  refine ⟨fun i x => v (L.symm x).1 i (L.symm x).2,
    fun i => (hv i).comp L.symm.contDiff,fun i => ?_⟩
  have hq : ∀ᵐ q : P × ℂ,u i (L q)=v q.1 i q.2 := by
    filter_upwards [pullLp_coe L (u i),hvu i] with q huq hvq
    exact huq.symm.trans hvq
  have hh := ae_linear L.symm hq
  filter_upwards [hh] with x hx
  simpa only [L.apply_symm_apply] using hx

end ElasticityCoordinates
namespace ElasticityDistribution
open Set MeasureTheory TemperedDistribution

section
open scoped SchwartzMap LineDeriv ENNReal
open ElasticityRegularity

abbrev L2Space := Lp ℂ 2 (volume : Measure X)

def compactLpMul (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (u : L2Space) : L2Space :=
  (compact_bounded_multiplier hg hc).toLp g • u
lemma compactLpMul_coe (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (u : L2Space) :
    (compactLpMul g hg hc u : X → ℂ)=ᵐ[volume] fun x => g x*u x := by
  filter_upwards [Lp.coeFn_lpSMul (r := 2) ((compact_bounded_multiplier hg hc).toLp g) u,
    (compact_bounded_multiplier hg hc).coeFn_toLp] with x hx hy
  change (((compact_bounded_multiplier hg hc).toLp g) • u) x=_
  rw [hx,Pi.smul_apply',hy,smul_eq_mul]
lemma compactLpMul_dist (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (u : L2Space) :
    (compactLpMul g hg hc u : Dist)=smulLeftCLM ℂ g (u : Dist) :=
  Lp.toTemperedDistribution_smul_eq (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) u

lemma lp_mul_eq {K : Set X} (u : L2Space) (hu : ∀ᵐ x,x∉K → u x=0)
    (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (h1 : EqOn g 1 K) : smulLeftCLM ℂ g (u : Dist)=(u : Dist) := by
  rw [← compactLpMul_dist g hg hc]
  congr 1
  apply Lp.ext
  filter_upwards [compactLpMul_coe g hg hc u,hu] with x hx hux
  rw [hx]
  by_cases h : x∈K
  · rw [h1 h,Pi.one_apply,one_mul]
  · rw [hux h,mul_zero]
lemma lp_mul_zero {K : Set X} (u : L2Space) (hu : ∀ᵐ x,x∉K → u x=0)
    (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (h0 : EqOn g 0 K) : smulLeftCLM ℂ g (u : Dist)=0 := by
  rw [← compactLpMul_dist g hg hc]
  have he : compactLpMul g hg hc u=0 := by
    apply Lp.ext
    filter_upwards [compactLpMul_coe g hg hc u,hu,Lp.coeFn_zero (E := ℂ) (p := (2 : ℝ≥0∞)) (μ := (volume : Measure X))] with x hx hux hz
    rw [hx,hz]
    change g x*u x=0
    by_cases h : x∈K
    · rw [h0 h,Pi.zero_apply,zero_mul]
    · rw [hux h,mul_zero]
  rw [he]
  exact (Lp.toTemperedDistributionCLM ℂ (volume : Measure X) 2).map_zero

lemma lp_cutoff_derivative {K B : Set X} (hB : IsOpen B) (hKB : K⊆B)
    (u : L2Space) (hu : ∀ᵐ x,x∉K → u x=0)
    (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (h1 : EqOn g 1 B) (a : X) :
    smulLeftCLM ℂ g (∂_{a} (u : Dist))=∂_{a} (u : Dist) := by
  have he := lp_mul_eq u hu g hg hc (h1.mono hKB)
  have h0 : EqOn (fun x => fderiv ℝ g x a) 0 K := by
    intro x hx
    have hh : g=ᶠ[nhds x] (fun _ => (1 : ℂ)) :=
      Filter.mem_of_superset (hB.mem_nhds (hKB hx)) h1
    change fderiv ℝ g x a=0
    rw [hh.fderiv_eq]
    simp only [fderiv_fun_const]
    rfl
  have hz := lp_mul_zero u hu _ (smooth_derivative hg a) (compact_derivative hc a) h0
  have hl := distribution_leibniz (hc.hasTemperateGrowth hg) a
    ((compact_derivative hc a).hasTemperateGrowth (smooth_derivative hg a)) (u : Dist)
  rw [he,hz,zero_add] at hl
  exact hl.symm

lemma continuous_supported_of_ae {K : Set X} (hK : IsClosed K)
    (u : L2Space) (hu : ∀ᵐ x,x∉K → u x=0)
    (v : X → ℂ) (hv : Continuous v) (hvu : (u : X → ℂ)=ᵐ[volume] v) :
    tsupport v⊆K := by
  have he : v=ᵐ[volume.restrict Kᶜ] 0 := by
    change ∀ᵐ x ∂volume.restrict Kᶜ,v x=0
    rw [ae_restrict_iff' hK.isOpen_compl.measurableSet]
    filter_upwards [hu,hvu] with x hx he
    intro hk
    rw [← he,hx hk]
  have hh : EqOn v 0 Kᶜ := Measure.eqOn_of_ae_eq he hv.continuousOn continuousOn_const
    (by rw [hK.isOpen_compl.interior_eq];exact subset_closure)
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  exact hx (hh hn)

end
open scoped SchwartzMap LineDeriv ENNReal BigOperators
open ElasticityRegularity
variable {n P : Type*} [Fintype n]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]

def planeDerivative (α β : X) : Dist →L[ℂ] Dist :=
  LineDeriv.lineDerivOpCLM ℂ Dist α+Complex.I • LineDeriv.lineDerivOpCLM ℂ Dist β
def planeSchwartz (α β : X) : Test →L[ℂ] Test :=
  LineDeriv.lineDerivOpCLM ℂ Test α+Complex.I • LineDeriv.lineDerivOpCLM ℂ Test β
lemma planeDerivative_schwartz (α β : X) (a : Test) :
    planeDerivative α β (a : Dist)=(planeSchwartz α β a : Dist) := by
  change ∂_{α} (a : Dist)+Complex.I • ∂_{β} (a : Dist)=
    ((∂_{α} a+Complex.I • ∂_{β} a : Test) : Dist)
  simp only [coe_schwartz_add,coe_schwartz_smul,
    lineDerivOp_toTemperedDistributionCLM_eq]

/-- Compactly supported differences of the actual weak columns are smooth,
including the transverse variable. No inverse of the transferred frame is
assumed and no ellipticity in three dimensions is asserted. -/
theorem compact_transport_smoothing (L : (P × ℂ) ≃L[ℝ] X)
    {K B B₀ : Set X} (hK : IsCompact K) (hB₀ : IsOpen B₀) (hKB : K⊆B₀)
    (A : n → n → Coeff) (W : n → L2Space) (a : n → Test)
    (hext : ∀ i,LocalEq Kᶜ (W i : Dist) (a i : Dist))
    (he : ∀ i,LocalEq B (planeDerivative (L (0,1)) (L (0,Complex.I)) (W i : Dist)+
      ∑ j,A i j • (W j : Dist)) 0)
    (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆B) (h1 : EqOn g 1 B₀) :
    ∃ v : n → Test,(∀ i,(W i : Dist)=(v i : Dist)) ∧
      ∀ i,tsupport (v i-a i : Test)⊆K := by
  classical
  let α := L (0,1)
  let β := L (0,Complex.I)
  let u := fun i => W i-(a i).toLp 2 volume
  have hu (i) : ∀ᵐ x,x∉K → u i x=0 := by
    have hh : LocalEqual Kᶜ (W i : Dist) (((a i).toLp 2 volume : L2Space) : Dist) := by
      simpa only [Lp.toTemperedDistribution_toLp_eq,LocalEqual,LocalEq] using hext i
    filter_upwards [LocalEqual.lp_ae hK.isClosed.isOpen_compl (W i) ((a i).toLp 2 volume) hh,
      Lp.coeFn_sub (W i) ((a i).toLp 2 volume)] with x hx hy
    intro hk
    change (W i-(a i).toLp 2 volume) x=0
    rw [hy,Pi.sub_apply,hx hk,sub_self]
  have ud (i) : (u i : Dist)=(W i : Dist)-(a i : Dist) := by
    change (Lp.toTemperedDistributionCLM ℂ volume 2) (W i-(a i).toLp 2 volume)=_
    rw [map_sub,Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_toLp_eq]
  let q : n → Test := fun i => planeSchwartz α β (a i)+
    ∑ j,SchwartzMap.smulLeftCLM ℂ (eval (A i j)) (a j)
  have qd (i) : (q i : Dist)=planeDerivative α β (a i : Dist)+∑ j,A i j • (a j : Dist) := by
    simp only [q,coe_schwartz_add,coe_schwartz_sum,← planeDerivative_schwartz,coeff_schwartz,ElasticityNegativeOrder.mult]
  let f : n → Test := fun i => -(SchwartzMap.smulLeftCLM ℂ g (q i))
  have fd (i) : (f i : Dist)= -(smulLeftCLM ℂ g (q i : Dist)) := by
    rw [show f i= -(SchwartzMap.smulLeftCLM ℂ g (q i)) from rfl,map_neg]
    congr 1
    exact (distribution_schwartz_product (hc.hasTemperateGrowth hg) (q i)).symm
  have fcoe (i) : (f i : X → ℂ)=fun x => -(g x*q i x) := by
    funext x
    simp only [f,neg_apply,SchwartzMap.smulLeftCLM_apply_apply (hc.hasTemperateGrowth hg),smul_eq_mul]
  have hfc (i) : HasCompactSupport (f i : X → ℂ) := by
    rw [fcoe]
    exact (hc.mul_right (f' := (q i : X → ℂ))).neg
  have hfs (i) : tsupport (f i : X → ℂ)⊆tsupport g := by
    rw [fcoe]
    change tsupport (-(fun x => g x*q i x))⊆tsupport g
    rw [tsupport_neg]
    exact tsupport_mul_subset_left
  let b := fun i j x => g x*eval (A i j) x
  have hb (i j) : ContDiff ℝ (⊤ : ℕ∞) (b i j) := hg.mul (eval_smooth (A i j))
  have hbc (i j) : HasCompactSupport (b i j) := hc.mul_right
  let w := fun i => (∑ j,compactLpMul (b i j) (hb i j) (hbc i j) (u j))-(f i).toLp 2 volume
  have wd (i) : (w i : Dist)=(∑ j,smulLeftCLM ℂ (b i j) (u j : Dist))-(f i : Dist) := by
    change (Lp.toTemperedDistributionCLM ℂ volume 2) (_-_)=_
    simp only [map_sub,map_sum,Lp.toTemperedDistributionCLM_apply,compactLpMul_dist,
      Lp.toTemperedDistribution_toLp_eq]
  have wcoe (i) : ∀ᵐ x,w i x=∑ j,b i j x*u j x-f i x := by
    have hall : ∀ᵐ x,∀ j,compactLpMul (b i j) (hb i j) (hbc i j) (u j) x=b i j x*u j x := by
      rw [ae_all_iff]
      exact fun j => compactLpMul_coe _ _ _ _
    filter_upwards [hall,Lp.coeFn_finsetSum Finset.univ (fun j => compactLpMul (b i j) (hb i j) (hbc i j) (u j)),
      Lp.coeFn_sub (∑ j,compactLpMul (b i j) (hb i j) (hbc i j) (u j)) ((f i).toLp 2 volume),
      (f i).coeFn_toLp 2 volume] with x hx hy hz hf
    change ((∑ j,compactLpMul (b i j) (hb i j) (hbc i j) (u j))-(f i).toLp 2 volume) x=_
    rw [hz,Pi.sub_apply,hy,hf]
    simp only [Finset.sum_apply,hx]
  have we (i) : planeDerivative α β (u i : Dist)+(w i : Dist)=0 := by
    have hlu : LocalEq B (planeDerivative α β (u i : Dist)+∑ j,A i j • (u j : Dist)) (-(q i : Dist)) := by
      intro φ hφ hφs
      have hhi := he i φ hφ hφs
      simp only [ud,map_sub,smul_def,map_sub,Finset.sum_sub_distrib,qd,add_apply,sub_apply,neg_apply,zero_apply] at hhi ⊢
      linear_combination hhi
    have ht := hlu.cutoff hg hc hs
    simp only [map_add,map_sum,map_neg] at ht
    have hd : smulLeftCLM ℂ g (planeDerivative α β (u i : Dist))=planeDerivative α β (u i : Dist) := by
      change smulLeftCLM ℂ g (∂_{α} (u i : Dist)+Complex.I • ∂_{β} (u i : Dist))=_
      rw [map_add,map_smul,lp_cutoff_derivative hB₀ hKB (u i) (hu i) g hg hc h1 α,
        lp_cutoff_derivative hB₀ hKB (u i) (hu i) g hg hc h1 β]
      rfl
    have hm (j) : smulLeftCLM ℂ g (A i j • (u j : Dist))=smulLeftCLM ℂ (b i j) (u j : Dist) := by
      rw [smul_def,smulLeftCLM_smulLeftCLM_apply (growth (A i j)) (hc.hasTemperateGrowth hg)]
      congr 2
      funext x
      exact mul_comm _ _
    rw [hd] at ht
    simp_rw [hm] at ht
    rw [wd,fd]
    rw [sub_neg_eq_add]
    rw [← add_assoc,ht,neg_add_cancel]
  have hw (i) : ∀ᵐ x,x∉K∪tsupport g → w i x=0 := by
    have hall : ∀ᵐ x,∀ j,x∉K → u j x=0 := by rw [ae_all_iff];exact hu
    filter_upwards [wcoe i,hall] with x hx hxu
    intro hn
    rw [hx]
    have hf : f i x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hn (Or.inr (hfs i hh)))
    simp only [hxu _ (fun hh => hn (Or.inl hh)),mul_zero,Finset.sum_const_zero,hf,sub_self]
  obtain ⟨v,hv,hvu⟩ := ElasticityCoordinates.planar_smooth_representative L
    (K∪tsupport g) (tsupport g) (hK.union hc) hc b hb
    (fun i j x hx => by simp only [b,image_eq_zero_of_notMem_tsupport hx,zero_mul])
    (fun i => (f i : X → ℂ)) (fun i => (f i).smooth ⊤)
    (fun i x hx => image_eq_zero_of_notMem_tsupport (fun hh => hx (hfs i hh)))
    u w (fun i => (hu i).mono fun x hx hn => hx (fun hh => hn (Or.inl hh))) hw wcoe we
  have hvK (i) : tsupport (v i)⊆K := continuous_supported_of_ae hK.isClosed (u i) (hu i) (v i) (hv i).continuous (hvu i)
  have hvc (i) : HasCompactSupport (v i) := hK.of_isClosed_subset (isClosed_tsupport _) (hvK i)
  let vS := fun i => (hvc i).toSchwartzMap (hv i)
  have vsd (i) : (u i : Dist)=(vS i : Dist) := by
    have hL : u i=(vS i).toLp 2 volume := by
      apply Lp.ext
      exact (hvu i).trans ((vS i).coeFn_toLp 2 volume).symm
    rw [hL,Lp.toTemperedDistribution_toLp_eq]
  refine ⟨fun i => vS i+a i,fun i => ?_,fun i => ?_⟩
  · rw [coe_schwartz_add,← vsd,ud,sub_add_cancel]
  · rw [add_sub_cancel_right]
    change tsupport (v i)⊆K
    exact hvK i
end ElasticityDistribution
namespace ElasticityDistribution
open Set TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented

def leadingPair (θ : Fin 3 → ℂ) (lam m n o : Coeff) (U : Fin 4 → Dist) : Fin 4 → Dist :=
  Fin.cons (o • (leadingSd θ lam m (fun j => U j.succ) (U 0)-
    (2 : ℂ) • (n • ∑ i, dc i m • leadingRd θ lam m (fun j => U j.succ) (U 0) i)))
    (fun i => n • leadingRd θ lam m (fun j => U j.succ) (U 0) i)

lemma lapd_null_direction (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (u : Dist) :
    lapd θ u=lapd 0 u+(2 : ℂ) • directiond θ u := by
  rw [lapd_expand,lapd_expand]
  ext φ
  simp only [hθ,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  unfold directiond
  simp [mul_smul,Finset.smul_sum]

lemma normPair_null_leading (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (lam m n o : Coeff) (U : Fin 4 → Dist) (i : Fin 4) :
    normPair θ lam m n o (fun j => U j.succ) (U 0) i=
      normPair 0 lam m n o (fun j => U j.succ) (U 0) i+leadingPair θ lam m n o U i := by
  have hr (j) : rd θ lam m (fun j => U j.succ) (U 0) j=
      rd 0 lam m (fun j => U j.succ) (U 0) j+leadingRd θ lam m (fun j => U j.succ) (U 0) j := by
    simpa only [one_smul] using rd_null_expansion θ hθ 1 lam m (fun j => U j.succ) (U 0) j
  have hs : scd θ lam m (fun j => U j.succ) (U 0)=
      scd 0 lam m (fun j => U j.succ) (U 0)+leadingSd θ lam m (fun j => U j.succ) (U 0) := by
    simpa only [one_smul] using scd_null_expansion θ hθ 1 lam m (fun j => U j.succ) (U 0)
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [normPair,leadingPair,Fin.cons_zero,hr,hs,smul_def,map_add,map_sub,map_sum,smul_add,Finset.sum_add_distrib]
    abel
  · simp only [normPair,leadingPair,Fin.cons_succ,hr,smul_def,map_add]

/-- The physical leading equations have a scalar planar principal part on all
four actual augmented entries. The constraint is retained separately. -/
theorem leadingPair_matrix (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1)
    (U : Fin 4 → Dist) (i : Fin 4) :
    leadingPair θ lam m n o U i=(2 : ℂ) • directiond θ (U i)+
      ∑ k,∑ j,θ k • (coeffA dc lam m n o k i j • U j) := by
  have hz0 (k : Fin 3) (u : Dist) : sd (0 : Fin 3 → ℂ) k u=dd k u := by
    change dd k u+(0 : ℂ) • u=dd k u
    rw [zero_smul ℂ u,add_zero]
  have hz := normalized_matrix 0 lam m n o hn ho U i
  simp only [hz0] at hz
  have ht := normalized_matrix θ lam m n o hn ho U i
  rw [normPair_null_leading θ hθ,lapd_null_direction θ hθ] at ht
  simp only [sd_apply,smul_def,map_add,map_smul,Finset.sum_add_distrib] at ht
  apply add_left_cancel (a := normPair 0 lam m n o (fun j => U j.succ) (U 0) i)
  calc
    _ = _ := ht
    _ = _ := by
      rw [hz]
      simp only [smul_def]
      abel

lemma leading_matrix_local {B : Set X} (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1) (U : Fin 4 → Dist)
    (hr : ∀ i,LocalEq B (leadingRd θ lam m (fun j => U j.succ) (U 0) i) 0)
    (hs : LocalEq B (leadingSd θ lam m (fun j => U j.succ) (U 0)) 0) (i : Fin 4) :
    LocalEq B ((2 : ℂ) • directiond θ (U i)+
      ∑ k,∑ j,θ k • (coeffA dc lam m n o k i j • U j)) 0 := by
  rw [← leadingPair_matrix θ hθ lam m n o hn ho]
  refine Fin.cases ?_ (fun j => ?_) i
  · have hh := (hs.sub ((LocalEq.sum Finset.univ (fun j _ => (hr j).coeff (dc j m))).coeff n |>.smul 2)).coeff o
    simpa only [leadingPair,Fin.cons_zero,smul_def,map_zero,smul_zero,Finset.sum_const_zero,sub_zero] using hh
  · have hh := (hr j).coeff n
    simpa only [leadingPair,Fin.cons_succ,smul_def,map_zero] using hh
end ElasticityDistribution
namespace ElasticityCoordinates
open Set MeasureTheory
open scoped ENNReal SchwartzMap LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- The actual characteristic plane and its transverse kernel are complementary.
No orthonormal-coordinate or slicing-existence premise is imposed. -/
def planeSplit (J : ℂ →L[ℝ] E) (K : E →L[ℝ] ℂ) (hK : Function.LeftInverse K J) :
    E ≃L[ℝ] LinearMap.ker K.toLinearMap × ℂ :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun x => (⟨x-J (K x),by
      change K (x-J (K x))=0
      rw [map_sub,hK,sub_self]⟩,K x)
    invFun := fun q => (q.1 : E)+J q.2
    left_inv := fun x => sub_add_cancel x (J (K x))
    right_inv := fun q => by
      have hk : K (q.1 : E)=0 := q.1.property
      apply Prod.ext
      · apply Subtype.ext
        change (q.1 : E)+J q.2-J (K ((q.1 : E)+J q.2))=(q.1 : E)
        rw [map_add,hk,zero_add,hK q.2,add_sub_cancel_right]
      · change K ((q.1 : E)+J q.2)=q.2
        rw [map_add,hk,zero_add,hK q.2]
    map_add' := fun x y => by
      apply Prod.ext
      · apply Subtype.ext
        change x+y-J (K (x+y))=(x-J (K x))+(y-J (K y))
        simp only [map_add]
        abel
      · exact map_add K x y
    map_smul' := fun c x => by
      apply Prod.ext
      · apply Subtype.ext
        change c • x-J (K (c • x))=c • (x-J (K x))
        simp only [map_smul,smul_sub]
      · exact map_smul K c x }

lemma planeSplit_symm (J : ℂ →L[ℝ] E) (K : E →L[ℝ] ℂ) (hK : Function.LeftInverse K J)
    (q : LinearMap.ker K.toLinearMap × ℂ) : (planeSplit J K hK).symm q=(q.1 : E)+J q.2 := rfl
lemma planeSplit_plane (J : ℂ →L[ℝ] E) (K : E →L[ℝ] ℂ) (hK : Function.LeftInverse K J)
    (z : ℂ) : planeSplit J K hK (J z)=(0,z) := by
  apply Prod.ext
  · apply Subtype.ext
    change J z-J (K (J z))=0
    rw [hK,sub_self]
  · exact hK z
lemma planeSplit_symm_plane (J : ℂ →L[ℝ] E) (K : E →L[ℝ] ℂ) (hK : Function.LeftInverse K J)
    (z : ℂ) : (planeSplit J K hK).symm (0,z)=J z := by
  simp only [planeSplit_symm,ZeroMemClass.coe_zero,zero_add]

end ElasticityCoordinates
namespace ElasticityDistribution

section
open TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented

lemma directiond_real_complex (α β : X) (u : Dist) :
    directiond (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) u=
      ∂_{α} u+Complex.I • ∂_{β} u := by
  have hα := ElasticityNegativeOrder.basis_expansion α
  have hβ := ElasticityNegativeOrder.basis_expansion β
  conv_rhs => rw [hα,hβ]
  ext φ
  simp only [LineDeriv.lineDerivOp_left_sum,LineDeriv.lineDerivOp_left_smul,
    directiond,dd_apply]
  simp [ElasticitySchwartzCarleman.e,e,Finset.smul_sum,add_mul,mul_assoc,Finset.sum_add_distrib,add_comm]

lemma exists_direction_coordinates (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0) :
    ∃ (J : ℂ →L[ℝ] X) (K : X →L[ℝ] ℂ),Function.LeftInverse K J ∧
      J 1=WithLp.toLp 2 (fun i => (θ i).re) ∧ J Complex.I=WithLp.toLp 2 (fun i => (θ i).im) := by
  let J := ElasticityParameter.characteristicPlane ElasticityParameter.basis θ
  have hJ := ElasticityParameter.null_plane_injective θ hθ hne
  obtain ⟨K,hK⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hJ
  refine ⟨J,K,hK,?_,?_⟩
  · rw [show J 1=∑ i,(θ i).re • ElasticityParameter.basis i from ElasticityParameter.characteristicPlane_one _ _]
    ext i
    exact ElasticityParameter.basis_sum_apply _ i
  · rw [show J Complex.I=∑ i,(θ i).im • ElasticityParameter.basis i from ElasticityParameter.characteristicPlane_I _ _]
    ext i
    exact ElasticityParameter.basis_sum_apply _ i
end
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented

lemma half_contraction (C : Fin 3 → Fin 4 → Fin 4 → Coeff) (θ : Fin 3 → ℂ)
    (U : Fin 4 → Dist) (i : Fin 4) :
    (∑ j,((1/2 : ℂ) • ∑ k,θ k • C k i j) • U j)=
      (1/2 : ℂ) • (∑ k,∑ j,θ k • (C k i j • U j)) := by
  have he (j : Fin 4) : ((1/2 : ℂ) • ∑ k,θ k • C k i j) • U j=
      (1/2 : ℂ) • ∑ k,θ k • (C k i j • U j) := by
    rw [smul_assoc]
    congr 1
    rw [@Finset.sum_smul (Fin 3) Coeff Dist _ _ _ (fun k => θ k • C k i j) Finset.univ (U j)]
    exact Finset.sum_congr rfl (fun k _ => smul_assoc (θ k) (C k i j) (U j))
  simp only [he,← Finset.smul_sum]
  congr 1
  simp only [Finset.smul_sum]
  exact Finset.sum_comm

/-- The actual weak leading augmented solution has a globally smooth
representative; the compact exterior difference is preserved exactly. -/
theorem weak_leading_smooth {K B B₀ : Set X} (hK : IsCompact K) (hB₀ : IsOpen B₀) (hKB : K⊆B₀)
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1)
    (W : Fin 4 → L2Space) (a : Fin 4 → Test)
    (hext : ∀ i,LocalEq Kᶜ (W i : Dist) (a i : Dist))
    (hr : ∀ i,LocalEq B (leadingRd θ lam m (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0)
    (hs : LocalEq B (leadingSd θ lam m (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0)
    (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hgs : tsupport g⊆B) (h1 : EqOn g 1 B₀) :
    ∃ v : Fin 4 → Test,(∀ i,(W i : Dist)=(v i : Dist)) ∧
      ∀ i,tsupport (v i-a i : Test)⊆K := by
  obtain ⟨J,Q,hQ,hα,hβ⟩ := exists_direction_coordinates θ hθ hne
  let L := (ElasticityCoordinates.planeSplit J Q hQ).symm
  let A := fun i j => (1/2 : ℂ) • ∑ k,θ k • coeffA dc lam m n o k i j
  have hD (u : Dist) : planeDerivative (L (0,1)) (L (0,Complex.I)) u=directiond θ u := by
    rw [show L (0,1)=J 1 from ElasticityCoordinates.planeSplit_symm_plane J Q hQ 1,
      show L (0,Complex.I)=J Complex.I from ElasticityCoordinates.planeSplit_symm_plane J Q hQ Complex.I,hα,hβ]
    have hh := directiond_real_complex (WithLp.toLp 2 (fun i => (θ i).re))
      (WithLp.toLp 2 (fun i => (θ i).im)) u
    have he : (fun i => ((θ i).re : ℂ)+Complex.I*((θ i).im : ℂ))=θ := by
      funext i
      simpa only [mul_comm] using (Complex.re_add_im (θ i))
    change ∂_{WithLp.toLp 2 (fun i => (θ i).re)} u+Complex.I •
      ∂_{WithLp.toLp 2 (fun i => (θ i).im)} u=directiond θ u
    simpa only [he] using hh.symm
  have hA (U : Fin 4 → Dist) (i : Fin 4) := half_contraction (coeffA dc lam m n o) θ U i
  have hE (i) : LocalEq B (planeDerivative (L (0,1)) (L (0,Complex.I)) (W i : Dist)+
      ∑ j,A i j • (W j : Dist)) 0 := by
    have hh := (leading_matrix_local θ hθ lam m n o hn ho (fun i => (W i : Dist)) hr hs i).smul (1/2)
    rw [hD,hA]
    intro φ hφ hφs
    have he := hh φ hφ hφs
    simp only [smul_apply,add_apply,smul_eq_mul,zero_apply] at he ⊢
    linear_combination he
  exact compact_transport_smoothing L hK hB₀ hKB A W a hext hE g hg hc hgs h1
end ElasticityDistribution
namespace ElasticityDistribution
open Set TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented ElasticityPhysicalAlgebra ElasticityNegativeOrder

def schwartzDirection (θ : Fin 3 → ℂ) (u : Test) : Test := ∑ i,θ i • ∂_{e i} u
def schwartzLeadingR (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Test) (b : Test) (i : Fin 3) : Test :=
  mult (eval (2*m)) (schwartzDirection θ (u i))+mult (eval (direction dc θ m)) (u i)+
    θ i • (mult (eval (lam+m)) b+∑ j,mult (eval (dc j m)) (u j))
def schwartzLeadingS (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Test) (b : Test) : Test :=
  mult (eval (2*(lam+m+m))) (schwartzDirection θ b)+mult (eval (2*direction dc θ (lam+m))) b+
    mult (eval (4 : Coeff)) (∑ i,mult (eval (dc i m)) (schwartzDirection θ (u i)))+
    mult (eval (2 : Coeff)) (∑ i,mult (eval (direction dc θ (dc i m))) (u i))
lemma schwartzDirection_dist (θ : Fin 3 → ℂ) (u : Test) :
    (schwartzDirection θ u : Dist)=directiond θ (u : Dist) := by
  simp only [schwartzDirection,directiond,coe_schwartz_sum,coe_schwartz_smul,dd_apply,
    lineDerivOp_toTemperedDistributionCLM_eq]
lemma schwartzLeadingR_dist (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Test) (b : Test) (i : Fin 3) :
    (schwartzLeadingR θ lam m u b i : Dist)=leadingRd θ lam m (fun j => (u j : Dist)) (b : Dist) i := by
  simp only [schwartzLeadingR,leadingRd,coe_schwartz_add,coe_schwartz_smul,coe_schwartz_sum,
    ← coeff_schwartz,schwartzDirection_dist]
lemma schwartzLeadingS_dist (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Test) (b : Test) :
    (schwartzLeadingS θ lam m u b : Dist)=leadingSd θ lam m (fun j => (u j : Dist)) (b : Dist) := by
  simp only [schwartzLeadingS,leadingSd,coe_schwartz_add,coe_schwartz_sum,
    ← coeff_schwartz,schwartzDirection_dist]
lemma schwartzDirection_smooth (θ : Fin 3 → ℂ) (u : Test) :
    toSmooth (schwartzDirection θ u)=direction coord θ (toSmooth u) := by
  simp only [schwartzDirection,direction,map_sum,map_smul]
  congr 1
lemma direction_coeff_val (θ : Fin 3 → ℂ) (m : Coeff) :
    (direction dc θ m).val=direction coord θ m.val := by
  apply Subtype.ext
  rfl
lemma toSmooth_coeff_mult (a : Coeff) (u : Test) :
    toSmooth (mult (eval a) u)=a.val*toSmooth u :=
  toSmooth_mult a.val (growth a) u
lemma dc_coeff_val (i : Fin 3) (m : Coeff) : (dc i m).val=coord i m.val := rfl
lemma schwartzLeadingR_smooth (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Test) (b : Test) (i : Fin 3) :
    toSmooth (schwartzLeadingR θ lam m u b i)=leadingR coord θ lam.val m.val (fun j => toSmooth (u j)) (toSmooth b) i := by
  simp only [schwartzLeadingR,map_add,map_smul,map_sum,
    toSmooth_coeff_mult,schwartzDirection_smooth,leadingR,direction_coeff_val,dc_coeff_val]
  rfl
lemma schwartzLeadingS_smooth (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Test) (b : Test) :
    toSmooth (schwartzLeadingS θ lam m u b)=leadingS coord θ lam.val m.val (fun j => toSmooth (u j)) (toSmooth b) := by
  simp only [schwartzLeadingS,map_add,map_sum,
    toSmooth_coeff_mult,schwartzDirection_smooth,leadingS,direction_coeff_val,dc_coeff_val]
  simp only [Finset.mul_sum]
  rfl
lemma leading_classical {B : Set X} (hB : IsOpen B) (θ : Fin 3 → ℂ) (lam m : Coeff)
    (u : Fin 3 → Test) (b : Test)
    (hr : ∀ i,LocalEq B (leadingRd θ lam m (fun j => (u j : Dist)) (b : Dist) i) 0)
    (hs : LocalEq B (leadingSd θ lam m (fun j => (u j : Dist)) (b : Dist)) 0) :
    (∀ i,EqOn ((leadingR coord θ lam.val m.val (fun j => toSmooth (u j)) (toSmooth b) i).val) 0 B) ∧
      EqOn ((leadingS coord θ lam.val m.val (fun j => toSmooth (u j)) (toSmooth b)).val) 0 B := by
  have h0 : ((0 : Test) : Dist)=0 := map_zero _
  constructor
  · intro i
    have hh : ElasticityRegularity.LocalEqual B (schwartzLeadingR θ lam m u b i : Dist) ((0 : Test) : Dist) := by
      simpa only [schwartzLeadingR_dist,h0,LocalEq,ElasticityRegularity.LocalEqual] using hr i
    have hh' := hh.schwartz_eqOn hB
    intro x hx
    rw [← schwartzLeadingR_smooth]
    exact hh' hx
  · have hh : ElasticityRegularity.LocalEqual B (schwartzLeadingS θ lam m u b : Dist) ((0 : Test) : Dist) := by
      simpa only [schwartzLeadingS_dist,h0,LocalEq,ElasticityRegularity.LocalEqual] using hs
    intro x hx
    rw [← schwartzLeadingS_smooth]
    exact hh.schwartz_eqOn hB hx
end ElasticityDistribution
section
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (temperate_partial)
open ElasticityNegativeOrder (mult_apply)

lemma localizedLeading_eqOn {B : Set X} (hB : IsOpen B) (R : ℝ) (hR : 1≤R)
    (hBR : B⊆Metric.ball 0 R) (a : ℕ → Amplitude Smooth) (g : Smooth)
    (hc : HasCompactSupport (g : X → ℂ)) (hg : EqOn (g : X → ℂ) 1 B) (i : Fin 4) :
    EqOn (localizedLeading R hR a g i : X → ℂ)
      ((Fin.cons (a 0).2 (a 0).1 : Fin 4 → Smooth) i : X → ℂ) B := by
  have ht := hc.hasTemperateGrowth (smooth_coe g)
  have hd (x : X) (hx : x∈B) (j : Fin 3) : fderiv ℝ (g : X → ℂ) x (e j)=0 := by
    have hh : (g : X → ℂ)=ᶠ[𝓝 x] (fun _ => (1 : ℂ)) :=
      Filter.mem_of_superset (hB.mem_nhds hx) hg
    rw [hh.fderiv_eq]
    simp only [fderiv_fun_const]
    rfl
  have hχ (x : X) (hx : x∈B) : fiveCutoff R hR 0 x=1 := fiveCutoff_initial R hR (hBR hx)
  intro x hx
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [localizedLeading,Fin.cons_zero,add_apply,sum_apply,mult_apply _ ht,
      mult_apply _ (temperate_partial _ ht _),cut_apply,hd x hx,hg hx,Pi.one_apply,hχ x hx,
      zero_mul,one_mul,Finset.sum_const_zero,add_zero]
  · simp only [localizedLeading,Fin.cons_succ,mult_apply _ ht,cut_apply,hg hx,Pi.one_apply,hχ x hx,one_mul]
end ElasticityCGO
namespace ElasticityDistribution
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth)
lemma normal_classical {B : Set X} (hB : IsOpen B) (θ : Fin 3 → ℂ) (u : Fin 3 → Test)
    (hn : LocalEq B (normald θ (fun j => (u j : Dist))) 0) :
    EqOn (normal θ (fun j => toSmooth (u j))).val 0 B := by
  let w : Test := ∑ i,θ i • u i
  have hw : (w : Dist)=normald θ (fun j => (u j : Dist)) := by
    simp only [w,normald,coe_schwartz_sum,coe_schwartz_smul]
  have hl : ElasticityRegularity.LocalEqual B (w : Dist) ((0 : Test) : Dist) := by
    simpa only [hw,map_zero,LocalEq,ElasticityRegularity.LocalEqual] using hn
  have he : toSmooth w=normal θ (fun j => toSmooth (u j)) := by
    simp only [w,normal,map_sum,map_smul]
  intro x hx
  rw [← he]
  exact hl.schwartz_eqOn hB hx
end ElasticityDistribution

end
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology
namespace ElasticityAugmented
lemma direction_eqOn {B : Set X} (hB : IsOpen B) (θ : Fin 3 → ℂ) {a b : Smooth}
    (h : EqOn (a : X → ℂ) (b : X → ℂ) B) :
    EqOn (direction (A := Smooth) coord θ a : X → ℂ) (direction (A := Smooth) coord θ b : X → ℂ) B := by
  intro x hx
  have he : (a : X → ℂ)=ᶠ[𝓝 x] (b : X → ℂ) := Filter.mem_of_superset (hB.mem_nhds hx) h
  change (∑ i,θ i*fderiv ℝ (a : X → ℂ) x (e i))=(∑ i,θ i*fderiv ℝ (b : X → ℂ) x (e i))
  rw [he.fderiv_eq]
lemma leadingR_eqOn {B : Set X} (hB : IsOpen B) (θ : Fin 3 → ℂ) (lam m : Smooth)
    {a a' : Fin 3 → Smooth} {b b' : Smooth}
    (ha : ∀ i,EqOn (a i : X → ℂ) (a' i : X → ℂ) B)
    (hb : EqOn (b : X → ℂ) (b' : X → ℂ) B) (i) :
    EqOn (leadingR (A := Smooth) coord θ lam m a b i : X → ℂ) (leadingR (A := Smooth) coord θ lam m a' b' i : X → ℂ) B := by
  intro x hx
  change ((2*m : Smooth) : X → ℂ) x*(direction (A := Smooth) coord θ (a i) : X → ℂ) x+
    (direction (A := Smooth) coord θ m : X → ℂ) x*(a i : X → ℂ) x+θ i*(((lam+m : Smooth) : X → ℂ) x*(b : X → ℂ) x+
      ∑ j,(coord j m : X → ℂ) x*(a j : X → ℂ) x)=_
  rw [direction_eqOn hB θ (ha i) hx,ha i hx,hb hx]
  have hs : (∑ j,(coord j m : X → ℂ) x*(a j : X → ℂ) x)=
      ∑ j,(coord j m : X → ℂ) x*(a' j : X → ℂ) x :=
    Finset.sum_congr rfl (fun j _ => congrArg ((coord j m : X → ℂ) x*·) (ha j hx))
  rw [hs]
  rfl
lemma leadingS_eqOn {B : Set X} (hB : IsOpen B) (θ : Fin 3 → ℂ) (lam m : Smooth)
    {a a' : Fin 3 → Smooth} {b b' : Smooth}
    (ha : ∀ i,EqOn (a i : X → ℂ) (a' i : X → ℂ) B)
    (hb : EqOn (b : X → ℂ) (b' : X → ℂ) B) :
    EqOn (leadingS (A := Smooth) coord θ lam m a b : X → ℂ) (leadingS (A := Smooth) coord θ lam m a' b' : X → ℂ) B := by
  intro x hx
  change ((2*(lam+m+m) : Smooth) : X → ℂ) x*(direction (A := Smooth) coord θ b : X → ℂ) x+
    ((2*direction (A := Smooth) coord θ (lam+m) : Smooth) : X → ℂ) x*(b : X → ℂ) x+
    4*(∑ i,(coord i m : X → ℂ) x*(direction (A := Smooth) coord θ (a i) : X → ℂ) x)+
    2*(∑ i,(direction (A := Smooth) coord θ (coord i m) : X → ℂ) x*(a i : X → ℂ) x)=_
  rw [direction_eqOn hB θ hb hx,hb hx]
  have hd := fun i => direction_eqOn hB θ (ha i) hx
  simp only [hd,fun i => ha i hx]
  rfl
end ElasticityAugmented
namespace ElasticityDistribution
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth)
/-- Patch the actual smooth representative to the original unlocalized
amplitude, without pretending the localization derivative vanishes globally. -/
theorem smooth_column_patch {K B : Set X} (hB : IsOpen B) (hKB : K⊆B)
    (θ : Fin 3 → ℂ) (lam m : Coeff) (v φ : Fin 4 → Test) (a₀ : Fin 4 → Smooth)
    (hs : ∀ i,tsupport (v i-φ i : Test)⊆K)
    (hφ : ∀ i,EqOn (φ i : X → ℂ) (a₀ i : X → ℂ) B)
    (hr : ∀ i,LocalEq B (leadingRd θ lam m (fun j => (v j.succ : Dist)) (v 0 : Dist) i) 0)
    (he : LocalEq B (leadingSd θ lam m (fun j => (v j.succ : Dist)) (v 0 : Dist)) 0)
    (hn : LocalEq B (normald θ (fun j => (v j.succ : Dist))) 0)
    (hn₀ : normal θ (fun j => a₀ j.succ)=0) :
    ∃ a : Fin 4 → Smooth,
      (∀ i,tsupport ((a i-a₀ i : Smooth) : X → ℂ)⊆K) ∧
      (∀ i,EqOn (leadingR (A := Smooth) coord θ lam.val m.val (fun j => a j.succ) (a 0) i : X → ℂ) 0 B) ∧
      EqOn (leadingS (A := Smooth) coord θ lam.val m.val (fun j => a j.succ) (a 0) : X → ℂ) 0 B ∧
      normal θ (fun j => a j.succ)=0 := by
  let a := fun i => a₀ i+toSmooth (v i-φ i)
  have ha (i) : EqOn (a i : X → ℂ) (toSmooth (v i) : X → ℂ) B := by
    intro x hx
    change (a₀ i : X → ℂ) x+(v i x-φ i x)=v i x
    rw [hφ i hx]
    ring
  have hsp (i) : tsupport ((a i-a₀ i : Smooth) : X → ℂ)⊆K := by
    have hh : ((a i-a₀ i : Smooth) : X → ℂ)=(v i-φ i : Test) := by
      funext x
      change (a₀ i : X → ℂ) x+(v i x-φ i x)-(a₀ i : X → ℂ) x=v i x-φ i x
      ring
    rw [hh]
    exact hs i
  obtain ⟨hR,hS⟩ := leading_classical hB θ lam m (fun j => v j.succ) (v 0) hr he
  refine ⟨a,hsp,fun i => (leadingR_eqOn hB θ lam.val m.val (fun j => ha j.succ) (ha 0) i).trans (hR i),
    (leadingS_eqOn hB θ lam.val m.val (fun j => ha j.succ) (ha 0)).trans hS,?_⟩
  apply Subtype.ext
  funext x
  by_cases hx : x∈B
  · have hh := normal_classical hB θ (fun j => v j.succ) hn hx
    change (∑ j,θ j*(a j.succ : X → ℂ) x)=0
    change (∑ j,θ j*v j.succ x)=0 at hh
    rw [show (∑ j,θ j*(a j.succ : X → ℂ) x)=(∑ j,θ j*v j.succ x) from
      Finset.sum_congr rfl (fun j _ => congrArg (θ j*·) (ha j.succ hx))]
    exact hh
  · have hh (i) : (a i : X → ℂ) x=(a₀ i : X → ℂ) x := by
      have hz := image_eq_zero_of_notMem_tsupport (f := ((a i-a₀ i : Smooth) : X → ℂ))
        (fun hn => hx (hKB (hsp i hn)))
      exact sub_eq_zero.mp hz
    change (∑ j,θ j*(a j.succ : X → ℂ) x)=0
    simp only [hh]
    exact congrArg (fun f : Smooth => (f : X → ℂ) x) hn₀
end ElasticityDistribution

end

end OAI
