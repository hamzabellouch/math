import OAI.MathematicalPhysics.Elasticity.Conic

namespace OAI

section
noncomputable section
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap BigOperators
namespace ElasticityPlanar
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
lemma test_equation_distribution (a : n → n → ℂ → ℂ)
    (ha : ∀ i j,(a i j).HasTemperateGrowth) (u f : n → Test)
    (he : ∀ i z,schwartzDbar (toSchwartz (u i)) z+∑ j,a i j z*u j z=f i z) (i : n) :
    planarOperator a i (embed u)=(toSchwartz (f i) : 𝓢'(ℂ,ℂ)) := by
  rw [planarOperator_test a ha]
  change (L2 (transport a (fun i j => (ha i j).1) u i) : 𝓢'(ℂ,ℂ))=_
  rw [L2_distribution]
  congr 1
  apply congrArg toSchwartz
  apply Subtype.ext
  funext z
  simp only [transport,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_add,Submodule.coe_smul,
    Submodule.coe_sum,Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  exact he i z

/-- Uniqueness identifies the independently supplied smooth slices with the
jointly smooth selection; smooth parameter dependence is a conclusion. -/
theorem classical_parameter_smooth {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z,z∉K → a i j (p,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i p z,z∉K → f i (p,z)=0)
    (u : P → n → Test) (hu : ∀ p i,tsupport (u p i : ℂ → ℂ)⊆S)
    (he : ∀ p i z,schwartzDbar (toSchwartz (u p i)) z+
      ∑ j,a i j (p,z)*u p j z=f i (p,z)) :
    ∀ i,ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => u q.1 i q.2) := by
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) p).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  let F (p : P) (i : n) : Test := ⟨fun z => f i (p,z),
    (hf i).comp (contDiff_const.prodMk contDiff_id),compact_slice hK (f i) (hfs i) p⟩
  have hdist (p : P) (i : n) := test_equation_distribution (fun i j z => a i j (p,z))
    (hat p) (u p) (F p) (he p) i
  obtain ⟨v,hv,hvs,hve⟩ := supported_parameter_inversion hS hK a ha hs f hf hfs
    (D := univ) dense_univ (fun p _ => ⟨embed (u p),fun i => ⟨hdist p i,
      test_support_distribution (u p i) (hu p i)⟩⟩)
  have huv (p : P) : embed (u p)=embed (v p) := by
    apply supported_weak_unique hS (fun i j z => a i j (p,z)) (hat p)
    · intro i
      exact (hdist p i).trans (test_equation_distribution (fun i j z => a i j (p,z))
        (hat p) (v p) (F p) (hve p) i).symm
    · intro i
      exact test_support_distribution (u p i) (hu p i)
    · intro i
      exact test_support_distribution (v p i) (hvs p i)
  have htest (p : P) (i : n) : u p i=v p i := by
    have hh := congrArg (entryInjection i) (huv p)
    change (L2 (u p i) : 𝓢'(ℂ,ℂ))=(L2 (v p i) : 𝓢'(ℂ,ℂ)) at hh
    rw [L2_distribution,L2_distribution] at hh
    have heq : LocalEqual univ (toSchwartz (u p i) : 𝓢'(ℂ,ℂ)) (toSchwartz (v p i) : 𝓢'(ℂ,ℂ)) :=
      fun φ _ _ => congrArg (fun t : 𝓢'(ℂ,ℂ) => t φ) hh
    apply Subtype.ext
    funext z
    exact heq.schwartz_eqOn isOpen_univ (mem_univ z)
  simpa only [htest] using hv
end ElasticityPlanar

end
end
section
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityCoordinates
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma compact_parameter_identity (p₀ : P) :
    ∃ τ : P → P,ContDiff ℝ (⊤ : ℕ∞) τ ∧ IsCompact (range τ) ∧ τ=ᶠ[𝓝 p₀] id := by
  obtain ⟨χ,hχ,hc,_,h1,_⟩ := ElasticityBoundary.compact_smooth_cutoff
    (K := {p₀}) (U := univ) isCompact_singleton isOpen_univ (subset_univ _)
  let u := fun p => χ p • (p-p₀)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hχ.smul (contDiff_id.sub contDiff_const)
  have huc : HasCompactSupport u := hc.smul_right
  refine ⟨fun p => p₀+u p,contDiff_const.add hu,?_,?_⟩
  · have he : range (fun p => p₀+u p)=(fun q => p₀+q) '' range u := by
      ext q
      simp only [mem_range,mem_image,exists_exists_eq_and]
    rw [he]
    exact (huc.isCompact_range hu.continuous).image (continuous_const.add continuous_id)
  · have hh : ∀ᶠ p in 𝓝 p₀,χ p=1 := by simpa only [nhdsSet_singleton] using h1
    filter_upwards [hh] with p hp
    simp only [u,hp,one_smul,id_eq]
    abel

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
/-- Uniform properness of an injective family of characteristic planes on a
compact parameter set. This supplies a fixed planar support for parameter
inversion, rather than silently treating moving planes as fixed. -/
lemma uniform_plane_support {T : Set P} (hT : IsCompact T)
    (J : P → ℂ →L[ℝ] E) (hJ : Continuous J) (hinj : ∀ p∈T,Function.Injective (J p))
    (x : P → E) (hx : Continuous x) {K : Set E} (hK : IsCompact K) :
    ∃ S : Set ℂ,IsCompact S ∧ ∀ p∈T,∀ w,x p+J p w∈K → w∈S := by
  have hc : IsCompact (T ×ˢ Metric.sphere (0 : ℂ) 1) := hT.prod (isCompact_sphere _ _)
  have hf : Continuous (fun q : P × ℂ => ‖J q.1 q.2‖) :=
    ((hJ.comp continuous_fst).clm_apply continuous_snd).norm
  have hp : ∀ q∈T ×ˢ Metric.sphere (0 : ℂ) 1,0<‖J q.1 q.2‖ := by
    rintro ⟨p,w⟩ ⟨hpt,hws⟩
    apply norm_pos_iff.mpr
    intro hz
    have hw : w=0 := hinj p hpt (hz.trans (map_zero _).symm)
    have hh : ‖w‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hws
    rw [hw,norm_zero] at hh
    norm_num at hh
  obtain ⟨c,hc0,hc⟩ := hc.exists_forall_le' hf.continuousOn hp
  have hlow (p : P) (hpt : p∈T) (w : ℂ) : c*‖w‖≤‖J p w‖ := by
    by_cases hw : w=0
    · simp only [hw,norm_zero,mul_zero,map_zero,le_refl]
    have hn : 0<‖w‖ := norm_pos_iff.mpr hw
    have hu : (‖w‖⁻¹ : ℝ) • w∈Metric.sphere (0 : ℂ) 1 := by
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn]
      exact inv_mul_cancel₀ hn.ne'
    have hh := hc (p,(‖w‖⁻¹ : ℝ) • w) ⟨hpt,hu⟩
    simp only [map_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn] at hh
    have he := mul_le_mul_of_nonneg_left hh hn.le
    calc
      c*‖w‖=‖w‖*c := mul_comm _ _
      _ ≤ ‖w‖*(‖w‖⁻¹*‖J p w‖) := he
      _ = ‖J p w‖ := by rw [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul]
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨C,hC⟩ := (hT.image hx).isBounded.exists_norm_le
  refine ⟨Metric.closedBall 0 ((R+C)/c),isCompact_closedBall _ _,fun p hpt w hw => ?_⟩
  rw [Metric.mem_closedBall,dist_zero_right,le_div_iff₀ hc0]
  have hu : ‖J p w‖≤R+C := by
    have he : J p w=(x p+J p w)-x p := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (hR _ hw) (hC _ (mem_image_of_mem x hpt)))
  have hh : ‖w‖*c≤‖J p w‖ := by simpa only [mul_comm] using hlow p hpt w
  exact hh.trans hu
end ElasticityCoordinates

end
end
section
noncomputable section
open Set Filter
open scoped Topology BigOperators SchwartzMap
namespace ElasticityPlanar
variable {n : Type*} [Fintype n]
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
/-- Joint smoothness from supported transport on moving characteristic planes.
Neither continuity nor parameter differentiability of the unknown is assumed. -/
theorem moving_plane_parameter_smooth (J : P → ℂ →L[ℝ] E)
    (hJ : ContDiff ℝ (⊤ : ℕ∞) J) (hJi : ∀ p,Function.Injective (J p))
    {S K : Set E} (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → E × P → ℂ) (ha : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (has : ∀ i j x p,x∉K → a i j (x,p)=0)
    (f : n → E × P → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i x p,x∉K → f i (x,p)=0)
    (u : P → n → E → ℂ) (hu : ∀ p i,ContDiff ℝ (⊤ : ℕ∞) (u p i))
    (hus : ∀ p i,tsupport (u p i)⊆S)
    (he : ∀ p i x,fderiv ℝ (u p i) x (J p 1)+Complex.I*fderiv ℝ (u p i) x (J p Complex.I)+
      ∑ j,a i j (x,p)*u p j x=f i (x,p)) :
    ∀ i,ContDiff ℝ (⊤ : ℕ∞) (fun q : E × P => u q.2 i q.1) := by
  intro i
  apply contDiff_iff_contDiffAt.mpr
  intro q₀
  obtain ⟨τ,hτ,hτc,hτe⟩ := ElasticityCoordinates.compact_parameter_identity q₀
  obtain ⟨W,hW,hWs⟩ := ElasticityCoordinates.uniform_plane_support hτc
    (fun q : E × P => J q.2) (hJ.continuous.comp continuous_snd)
    (fun q _ => hJi q.2) Prod.fst continuous_fst (hS.union hK)
  let F : (E × P) × ℂ → E := fun q => (τ q.1).1+J (τ q.1).2 q.2
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (hτ.fst.comp contDiff_fst).add ((hJ.comp (hτ.snd.comp contDiff_fst)).clm_apply contDiff_snd)
  let A : n → n → (E × P) × ℂ → ℂ := fun i j q => a i j (F q,(τ q.1).2)
  let b : n → (E × P) × ℂ → ℂ := fun i q => f i (F q,(τ q.1).2)
  have hA (i j) : ContDiff ℝ (⊤ : ℕ∞) (A i j) :=
    (ha i j).comp (hF.prodMk (hτ.snd.comp contDiff_fst))
  have hb (i) : ContDiff ℝ (⊤ : ℕ∞) (b i) :=
    (hf i).comp (hF.prodMk (hτ.snd.comp contDiff_fst))
  have hout (q : E × P) (z : ℂ) (hz : z∉W) : F (q,z)∉S∪K :=
    fun hh => hz (hWs (τ q) (mem_range_self q) z hh)
  have hAs (i j q z) (hz : z∉W) : A i j (q,z)=0 :=
    has i j _ _ (fun hh => hout q z hz (Or.inr hh))
  have hbs (i q z) (hz : z∉W) : b i (q,z)=0 :=
    hfs i _ _ (fun hh => hout q z hz (Or.inr hh))
  have hvu (q : E × P) (j : n) : ContDiff ℝ (⊤ : ℕ∞) (fun z => u (τ q).2 j (F (q,z))) :=
    (hu _ _).comp (hF.comp (contDiff_const.prodMk contDiff_id))
  have hvs (q : E × P) (j : n) : tsupport (fun z => u (τ q).2 j (F (q,z)))⊆W := by
    apply closure_minimal _ hW.isClosed
    intro z hz
    by_contra hn
    exact hz (image_eq_zero_of_notMem_tsupport (fun hh => hout q z hn (Or.inl (hus _ _ hh))))
  let v : (E × P) → n → Test := fun q j => ⟨fun z => u (τ q).2 j (F (q,z)),
    hvu q j,hW.of_isClosed_subset isClosed_closure (hvs q j)⟩
  have hve (q : E × P) (j : n) (z : ℂ) :
      schwartzDbar (toSchwartz (v q j)) z+∑ k,A j k (q,z)*v q k z=b j (q,z) := by
    change fderiv ℝ (u (τ q).2 j ∘ planeMap (J (τ q).2) (τ q).1) z 1+
      Complex.I*fderiv ℝ (u (τ q).2 j ∘ planeMap (J (τ q).2) (τ q).1) z Complex.I+_=_
    rw [plane_deriv _ _ ((hu _ _).differentiable (by simp)),
      plane_deriv _ _ ((hu _ _).differentiable (by simp))]
    exact he (τ q).2 j (F (q,z))
  have hv := classical_parameter_smooth hW hW A hA hAs b hb hbs v hvs hve
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun q : E × P => u (τ q).2 i (τ q).1) := by
    have hg := (hv i).comp (contDiff_id.prodMk (contDiff_const (c := (0 : ℂ))))
    simpa only [Function.comp_def,id,v,F,map_zero,add_zero] using hg
  apply hg.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hτe] with q hq
  simp only [hq,id_eq]
end ElasticityPlanar

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma characteristicPlane_smooth (θ : Fin 3 → ℂ → ℂ)
    (hθ : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (θ i)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => ElasticityParameter.characteristicPlane ElasticityParameter.basis (fun i => θ i z)) := by
  apply ContDiff.add
  · exact contDiff_const.smulRight (ContDiff.sum (fun i _ =>
      (Complex.reCLM.contDiff.comp (hθ i)).smul contDiff_const))
  · exact contDiff_const.smulRight (ContDiff.sum (fun i _ =>
      (Complex.imCLM.contDiff.comp (hθ i)).smul contDiff_const))

/-- Joint smoothness of the actual supported comparison. Continuity in the
conic parameter is not supplied as data. -/
theorem supported_matrix_smooth (θ : Fin 3 → ℂ → ℂ)
    (hθ : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (θ i))
    (hnull : ∀ z,∑ i,θ i z*θ i z=0) (hne : ∀ z,(fun i => θ i z)≠0)
    (M₀ M₁ G : ℂ → Matrix n n Smooth)
    (hM₀ : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun q : X × ℂ => (M₀ q.2 i j : X → ℂ) q.1))
    (hM₁ : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun q : X × ℂ => (M₁ q.2 i j : X → ℂ) q.1))
    {S : Set X} (hS : IsCompact S) (χ : Smooth) (hχ : HasCompactSupport (χ : X → ℂ))
    (hχ1 : ∀ x∈S,(χ : X → ℂ) x=1)
    (hs : ∀ z i j,tsupport ((G z i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆S)
    (hMe : ∀ z x,x∉S → matrixEval x (M₀ z)=matrixEval x (M₁ z))
    (he : ∀ z,matrixD (fun i => θ i z) (G z)=M₁ z*G z-G z*M₀ z) :
    ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun q : X × ℂ => (G q.2 i j : X → ℂ) q.1) := by
  let U : ℂ → Matrix n n Smooth := fun z => G z-1
  let C : (n × n) → (n × n) → X × ℂ → ℂ := fun p q y =>
    (if q.2=p.2 then (M₁ y.2 p.1 q.1 : X → ℂ) y.1 else 0)-
      (if q.1=p.1 then (M₀ y.2 q.2 p.2 : X → ℂ) y.1 else 0)
  let a : (n × n) → (n × n) → X × ℂ → ℂ := fun p q y => -(χ : X → ℂ) y.1*C p q y
  let f : (n × n) → X × ℂ → ℂ := fun p y => (M₁ y.2 p.1 p.2 : X → ℂ) y.1-(M₀ y.2 p.1 p.2 : X → ℂ) y.1
  have ha (p q : n × n) : ContDiff ℝ (⊤ : ℕ∞) (a p q) := by
    have hχs : ContDiff ℝ (⊤ : ℕ∞) (χ : X → ℂ) := χ.property
    apply ((hχs.comp contDiff_fst).neg).mul
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : X × ℂ => if q.2=p.2 then (M₁ y.2 p.1 q.1 : X → ℂ) y.1 else 0) := by
      split_ifs
      · exact hM₁ _ _
      · exact contDiff_const
    have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun y : X × ℂ => if q.1=p.1 then (M₀ y.2 q.2 p.2 : X → ℂ) y.1 else 0) := by
      split_ifs
      · exact hM₀ _ _
      · exact contDiff_const
    exact h1.sub h0
  have hf (p : n × n) : ContDiff ℝ (⊤ : ℕ∞) (f p) := (hM₁ _ _).sub (hM₀ _ _)
  let K := S∪tsupport (χ : X → ℂ)
  have hK : IsCompact K := hS.union hχ
  have has (p q : n × n) (x : X) (z : ℂ) (hx : x∉K) : a p q (x,z)=0 := by
    have hz := image_eq_zero_of_notMem_tsupport (fun hh => hx (Or.inr hh))
    change -(χ : X → ℂ) x*C p q (x,z)=0
    rw [hz,neg_zero,zero_mul]
  have hfs (p : n × n) (x : X) (z : ℂ) (hx : x∉K) : f p (x,z)=0 := by
    exact sub_eq_zero.mpr (congrArg (fun A : Matrix n n ℂ => A p.1 p.2)
      (hMe z x (fun hh => hx (Or.inl hh)))).symm
  have hUe (z : ℂ) : matrixD (fun i => θ i z) (U z)=
      M₁ z*U z-U z*M₀ z+(M₁ z-M₀ z) := by
    have hd : matrixD (fun i => θ i z) (G z-1)=matrixD (fun i => θ i z) (G z)-matrixD (fun i => θ i z) 1 := by
      funext i j; exact map_sub _ _ _
    dsimp only [U]
    rw [hd,matrixD_one,sub_zero,he]
    simp only [mul_sub,sub_mul,mul_one,one_mul]
    abel
  have hg := ElasticityPlanar.moving_plane_parameter_smooth
    (fun z => ElasticityParameter.characteristicPlane ElasticityParameter.basis (fun i => θ i z))
    (characteristicPlane_smooth θ hθ) (fun z => ElasticityParameter.null_plane_injective _ (hnull z) (hne z))
    hS hK a ha has f hf hfs
    (fun z p => (U z p.1 p.2 : X → ℂ)) (fun z p => (U z p.1 p.2).property)
    (fun z p => hs z p.1 p.2) (fun z p x => ?_)
  · intro i j
    have h := (hg (i,j)).add (contDiff_const (c := ((1 : Matrix n n Smooth) i j : X → ℂ) 0))
    have hid (x : X) : ((1 : Matrix n n Smooth) i j : X → ℂ) x=((1 : Matrix n n Smooth) i j : X → ℂ) 0 := by
      simp only [Matrix.one_apply]
      split_ifs <;> rfl
    convert h using 1
    funext q
    change (G q.2 i j : X → ℂ) q.1=(G q.2 i j : X → ℂ) q.1-((1 : Matrix n n Smooth) i j : X → ℂ) q.1+_
    rw [hid,sub_add_cancel]
  · rw [ElasticityParameter.characteristicPlane_principal]
    have hh := congrArg (fun A : Matrix n n Smooth => matrixEval x A p.1 p.2) (hUe z)
    rw [matrixD_eval] at hh
    simp only [map_add,map_sub,map_mul,Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,
      ← Finset.sum_sub_distrib] at hh
    rw [ElasticityParameter.commutator_flatten (matrixEval x (M₁ z)) (matrixEval x (M₀ z)) (matrixEval x (U z)) p.1 p.2] at hh
    change (∑ r,θ r z*fderiv ℝ (U z p.1 p.2 : X → ℂ) x (ElasticityParameter.basis r))=
      (∑ q : n × n,C p q (x,z)*(U z q.1 q.2 : X → ℂ) x)+f p (x,z) at hh
    rw [hh]
    have hc : ∑ q : n × n,a p q (x,z)*(U z q.1 q.2 : X → ℂ) x=
        -(∑ q : n × n,C p q (x,z)*(U z q.1 q.2 : X → ℂ) x) := by
      by_cases hx : x∈S
      · simp only [a,hχ1 x hx,neg_mul,one_mul,Finset.sum_neg_distrib]
      · have hu (q : n × n) : (U z q.1 q.2 : X → ℂ) x=0 :=
          image_eq_zero_of_notMem_tsupport (fun hh => hx (hs z q.1 q.2 hh))
        simp only [hu,mul_zero,Finset.sum_const_zero,neg_zero]
    rw [hc]
    ring
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

structure JointHolomorphic (f : X × ℂ → ℂ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  holo : ∀ x,Differentiable ℂ (fun z => f (x,z))
namespace JointHolomorphic
lemma fixed (f : Smooth) : JointHolomorphic (fun q : X × ℂ => (f : X → ℂ) q.1) :=
  ⟨(show ContDiff ℝ (⊤ : ℕ∞) (f : X → ℂ) from f.property).comp contDiff_fst,fun x => differentiable_const ((f : X → ℂ) x)⟩
lemma param (f : ℂ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hh : Differentiable ℂ f) :
    JointHolomorphic (fun q : X × ℂ => f q.2) := ⟨hf.comp contDiff_snd,fun _ => hh⟩
lemma const (c : ℂ) : JointHolomorphic (fun _ : X × ℂ => c) :=
  ⟨contDiff_const,fun _ => differentiable_const _⟩
lemma add {f g : X × ℂ → ℂ} (hf : JointHolomorphic f) (hg : JointHolomorphic g) :
    JointHolomorphic (fun q => f q+g q) := ⟨hf.smooth.add hg.smooth,fun x => (hf.holo x).add (hg.holo x)⟩
lemma sub {f g : X × ℂ → ℂ} (hf : JointHolomorphic f) (hg : JointHolomorphic g) :
    JointHolomorphic (fun q => f q-g q) := ⟨hf.smooth.sub hg.smooth,fun x => (hf.holo x).sub (hg.holo x)⟩
lemma mul {f g : X × ℂ → ℂ} (hf : JointHolomorphic f) (hg : JointHolomorphic g) :
    JointHolomorphic (fun q => f q*g q) := ⟨hf.smooth.mul hg.smooth,fun x => (hf.holo x).mul (hg.holo x)⟩
lemma pow {f : X × ℂ → ℂ} (hf : JointHolomorphic f) (n : ℕ) :
    JointHolomorphic (fun q => f q^n) := ⟨hf.smooth.pow n,fun x => (hf.holo x).pow n⟩
lemma sum {ι : Type*} [Fintype ι] {f : ι → X × ℂ → ℂ} (hf : ∀ i,JointHolomorphic (f i)) :
    JointHolomorphic (fun q => ∑ i,f i q) :=
  ⟨ContDiff.sum (fun i _ => (hf i).smooth),fun x => Differentiable.fun_sum (fun i _ => (hf i).holo x)⟩
end JointHolomorphic

lemma chartZ₀_regular (b : Bool) : JointHolomorphic (fun q : X × ℂ => chartZ₀ b q.2) := by
  cases b
  · exact JointHolomorphic.const 1
  · exact JointHolomorphic.param id contDiff_id differentiable_id
lemma chartZ₁_regular (b : Bool) : JointHolomorphic (fun q : X × ℂ => chartZ₁ b q.2) := by
  cases b
  · exact JointHolomorphic.param id contDiff_id differentiable_id
  · exact JointHolomorphic.const 1
lemma chartTheta_regular (b : Bool) (i : Fin 3) : JointHolomorphic (fun q : X × ℂ => chartTheta b q.2 i) := by
  fin_cases i
  · exact (chartZ₀_regular b).pow 2 |>.sub ((chartZ₁_regular b).pow 2)
  · exact (JointHolomorphic.const Complex.I).mul (((chartZ₀_regular b).pow 2).add ((chartZ₁_regular b).pow 2))
  · exact ((JointHolomorphic.const 2).mul (chartZ₀_regular b)).mul (chartZ₁_regular b)
lemma h₁_regular (b : Bool) (i : Fin 3) : JointHolomorphic (fun q : X × ℂ => h₁ (chartZ₀ b q.2) (chartZ₁ b q.2) i) := by
  fin_cases i
  · exact chartZ₀_regular b
  · exact (JointHolomorphic.const Complex.I).mul (chartZ₀_regular b)
  · exact chartZ₁_regular b
lemma h₂_regular (b : Bool) (i : Fin 3) : JointHolomorphic (fun q : X × ℂ => h₂ (chartZ₀ b q.2) (chartZ₁ b q.2) i) := by
  fin_cases i
  · simpa [h₂] using (JointHolomorphic.const (-1)).mul (chartZ₁_regular b)
  · exact (JointHolomorphic.const Complex.I).mul (chartZ₁_regular b)
  · exact chartZ₀_regular b
lemma direction_regular (b : Bool) (f : Smooth) :
    JointHolomorphic (fun q : X × ℂ => (direction (A := Smooth) coord (chartTheta b q.2) f : X → ℂ) q.1) := by
  have hh := JointHolomorphic.sum (fun i => (chartTheta_regular b i).mul (JointHolomorphic.fixed (coord i f)))
  simpa only [direction,smooth_sum_eval,Subalgebra.coe_smul,Pi.smul_apply,smul_eq_mul] using hh
lemma thetaGamma_regular (b : Bool) (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) :
    JointHolomorphic (fun q : X × ℂ => (thetaGamma (chartTheta b q.2) r hr : X → ℂ) q.1) := by
  have hh := JointHolomorphic.sum (fun i => (chartTheta_regular b i).mul (JointHolomorphic.fixed (logarithmicGrad r hr i)))
  simpa only [thetaGamma,smooth_sum_eval,Subalgebra.coe_smul,Pi.smul_apply,smul_eq_mul] using hh
lemma transportT_regular (b : Bool) (k r : Smooth) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) :
    JointHolomorphic (fun q : X × ℂ => (transportT (chartTheta b q.2) k r hk hl : X → ℂ) q.1) :=
  ((JointHolomorphic.fixed (smoothInv k hk)).mul (direction_regular b k)).sub
    ((JointHolomorphic.fixed (smoothInv (k+r*r) hl)).mul (direction_regular b (k+r*r)))
lemma transportQ_regular (b : Bool) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (i : Fin 3) :
    JointHolomorphic (fun q : X × ℂ => (transportQ (chartTheta b q.2) k r hr hk hl i : X → ℂ) q.1) :=
  (JointHolomorphic.const (1/2)).mul
    ((((JointHolomorphic.fixed (r*r*smoothInv (k+r*r) hl*smoothInv k hk)).mul (direction_regular b k)).sub
      ((JointHolomorphic.const (1/2)).mul (thetaGamma_regular b r hr))).mul
        (JointHolomorphic.fixed (logarithmicGrad r hr i)) |>.sub
      ((JointHolomorphic.fixed (r*r*smoothInv (k+r*r) hl)).mul (direction_regular b (logarithmicGrad r hr i))))

/-- These are the literal chart coefficients, jointly smooth and holomorphic
in the normalized conic direction, with the physical point fixed. -/
lemma chartMatrix_regular (b : Bool) (T : ℂ → Smooth) (Q : ℂ → Fin 3 → Smooth)
    (hT : JointHolomorphic (fun q : X × ℂ => (T q.2 : X → ℂ) q.1))
    (hQ : ∀ i,JointHolomorphic (fun q : X × ℂ => (Q q.2 i : X → ℂ) q.1)) (i j : Fin 3) :
    JointHolomorphic (fun q : X × ℂ => (chartMatrix b q.2 (T q.2) (Q q.2) i j : X → ℂ) q.1) := by
  fin_cases i <;> fin_cases j
  all_goals try first | exact JointHolomorphic.const 0 | exact hT
  · simpa [chartMatrix,smooth_sum_eval] using chartZ₀_regular b
  · simpa [chartMatrix,smooth_sum_eval] using chartZ₁_regular b
  · have hh := JointHolomorphic.sum (fun k => (h₁_regular b k).mul (hQ k))
    simpa [chartMatrix,smooth_sum_eval] using hh
  · have hh := JointHolomorphic.sum (fun k => (h₂_regular b k).mul (hQ k))
    simpa [chartMatrix,smooth_sum_eval] using hh
end ElasticityConic

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Both regularity statements are derived for a separately constructed family
from its transport equation and ONE fixed spatial support. -/
theorem supported_matrix_holomorphic (θ : Fin 3 → ℂ → ℂ)
    (hθs : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (θ i)) (hθh : ∀ i,Differentiable ℂ (θ i))
    (hnull : ∀ z,∑ i,θ i z*θ i z=0) (hne : ∀ z,(fun i => θ i z)≠0)
    (M₀ M₁ G : ℂ → Matrix n n Smooth)
    (hM₀ : ∀ i j,ElasticityConic.JointHolomorphic (fun q : X × ℂ => (M₀ q.2 i j : X → ℂ) q.1))
    (hM₁ : ∀ i j,ElasticityConic.JointHolomorphic (fun q : X × ℂ => (M₁ q.2 i j : X → ℂ) q.1))
    {S : Set X} (hS : IsCompact S) (χ : Smooth) (hχ : HasCompactSupport (χ : X → ℂ))
    (hχ1 : ∀ x∈S,(χ : X → ℂ) x=1)
    (hs : ∀ z i j,tsupport ((G z i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆S)
    (hMe : ∀ z x,x∉S → matrixEval x (M₀ z)=matrixEval x (M₁ z))
    (he : ∀ z,matrixD (fun i => θ i z) (G z)=M₁ z*G z-G z*M₀ z) :
    ∀ i j,ElasticityConic.JointHolomorphic (fun q : X × ℂ => (G q.2 i j : X → ℂ) q.1) := by
  have hgs := supported_matrix_smooth θ hθs hnull hne M₀ M₁ G
    (fun i j => (hM₀ i j).smooth) (fun i j => (hM₁ i j).smooth) hS χ hχ hχ1 hs hMe he
  let Θ : Fin 3 → ElasticityParameter.Smooth (X × ℂ) := fun i => ⟨fun q => θ i q.2,(hθs i).comp contDiff_snd⟩
  let A : n → n → ElasticityParameter.Smooth (X × ℂ) := fun i j => ⟨fun q => (M₁ q.2 i j : X → ℂ) q.1,(hM₁ i j).smooth⟩
  let B : n → n → ElasticityParameter.Smooth (X × ℂ) := fun i j => ⟨fun q => (M₀ q.2 i j : X → ℂ) q.1,(hM₀ i j).smooth⟩
  let F : n → n → ElasticityParameter.Smooth (X × ℂ) := fun i j => ⟨fun q => (G q.2 i j : X → ℂ) q.1,hgs i j⟩
  have hh := ElasticityParameter.matrix_holomorphic_of_supported_comparison Θ
    (fun _ _ _ => rfl) (fun i _ => hθh i) hnull hne A B F
    (fun i j => (hM₁ i j).holo) (fun i j => (hM₀ i j).holo) (fun i j => ?_) hS (fun i j x hx z => ?_)
  · exact fun i j => ⟨hgs i j,hh i j⟩
  · apply Subtype.ext
    funext q
    rcases q with ⟨x,z⟩
    simp only [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,Subalgebra.coe_mul,
      Subalgebra.coe_sub,Pi.sub_apply,Pi.mul_apply,ElasticityParameter.delta_apply]
    change (∑ r, θ r z * fderiv ℝ (F i j : X × ℂ → ℂ) (x,z) (ElasticityParameter.basis r,0))=
      ∑ a, ((M₁ z i a : X → ℂ) x*(G z a j : X → ℂ) x-
        (G z i a : X → ℂ) x*(M₀ z a j : X → ℂ) x)
    simp_rw [← ElasticityParameter.spatial_slice_deriv]
    have hh := congrArg (fun C : Matrix n n Smooth => matrixEval x C i j) (he z)
    rw [matrixD_eval] at hh
    simpa only [F,map_sub,map_mul,Matrix.sub_apply,Matrix.mul_apply,matrixEval_apply,smooth_sum_eval,Subalgebra.coe_sub,Subalgebra.coe_mul,Pi.sub_apply,Pi.mul_apply,Finset.sum_sub_distrib] using hh
  · have h := congrArg (fun C : Matrix n n ℂ => C i j) (supported_matrix_eq_one (G z) (hs z) x hx)
    exact h
end ElasticityAugmented

end
end

end OAI
