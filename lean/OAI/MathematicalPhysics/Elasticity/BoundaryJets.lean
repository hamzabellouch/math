import OAI.MathematicalPhysics.Elasticity.CommonExterior
import OAI.MathematicalPhysics.Elasticity.BoundaryValues

namespace OAI

section
/-! Projection-stable packet supports are constructed inside honest open charts. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundary ElasticityBoundaryNormalTaylor
  ElasticityBoundaryInverseGeometry ElasticityBoundaryGradientTransfer
lemma setup_ball_exists {Ω : Set X} (h : SourceSmoothBoundary Ω) {x : X} (hx : x∈frontier Ω) :
    ∃ s : Setup Ω x, ∃ r : ℝ, 0<r ∧ s.K=Metric.closedBall 0 r := by
  obtain ⟨e,Q,he0,hec,he,hi,hQ,hhalf⟩ := h.normalized hx
  obtain ⟨r,hr,hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (e.open_source.mem_nhds he0)
  obtain ⟨χ,hχ,hχc,hχs,hχ0,_⟩ := compact_smooth_cutoff (isCompact_singleton (x := (0:X)))
    Metric.isOpen_ball (singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  let K := Metric.closedBall (0:X) r
  have hK : IsCompact K := isCompact_closedBall 0 r
  have hχK : tsupport χ⊆K := fun z hz => Metric.ball_subset_closedBall (hχs hz)
  obtain ⟨η,Φ,Ψ,hη,hηc,hηs,hη1,hΦ,hΦe,hΨ,hΨe⟩ := compact_chart_data e he hi hK hrs
  have hηK : ∀ z∈e '' K, η z=1 := fun z hz => hη1.self_of_nhdsSet hz
  have hKη : e '' K⊆tsupport η := by
    intro z hz
    exact subset_tsupport η (show η z≠0 from by rw [hηK z hz]; exact one_ne_zero)
  let χc : Y → ℂ := fun y => (χ (WithLp.toLp 2 y):ℂ)
  have hχcs : ContDiff ℝ (⊤ : ℕ∞) χc :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp PiLp.contDiff_toLp)
  have hχcc : HasCompactSupport χc :=
    (hχc.comp_homeomorph (PiLp.homeomorph 2 (fun _ : I => ℝ)).symm).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  have hχc0 : χc =ᶠ[𝓝 (0:Y)] fun _ => 1 := by
    have hh : χ =ᶠ[𝓝 (0:X)] fun _ => 1 := by
      change ∀ᶠ z in 𝓝 (0:X), χ z=1
      simpa only [nhdsSet_singleton] using hχ0
    have ht : Tendsto (WithLp.toLp 2 : Y → X) (𝓝 (0:Y)) (𝓝 (0:X)) :=
      (PiLp.continuous_toLp 2 (fun _ : I => ℝ)).continuousAt
    filter_upwards [hh.comp_tendsto ht] with y hy
    change χ (WithLp.toLp 2 y)=1 at hy
    simp only [χc,hy,Complex.ofReal_one]
  refine ⟨{
    e := e, Q := Q, at_zero := he0, center := hec, smooth := he,
    inverse_smooth := hi, deriv := hQ, inside := hhalf, K := K, compact := hK,
    source := hrs, cutoff := χc, cutoff_smooth := hχcs, cutoff_compact := hχcc,
    cutoff_one := hχc0, cutoff_support := ?_, η := η, η_smooth := hη,
    η_compact := hηc, η_support := hηs, η_one := hηK, Φ := Φ, Ψ := Ψ,
    Φ_smooth := hΦ, Ψ_smooth := hΨ, Φ_germ := ?_, Ψ_germ := ?_ },r,hr,rfl⟩
  · intro z hz
    apply hχK
    apply subset_tsupport χ
    intro hc
    exact hz (by simp [χc,hc])
  · intro y hy
    exact hΦe.filter_mono (nhds_le_nhdsSet hy)
  · intro z hz
    exact hΨe.filter_mono (nhds_le_nhdsSet (hKη hz))

lemma projection_norm_le (y : Y) :
    ‖WithLp.toLp 2 (projection y)‖ ≤ ‖(WithLp.toLp 2 y : X)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq,projection]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i=2
  · subst i
    simp only [Pi.sub_apply,Pi.smul_apply,en,Pi.single_eq_same,smul_eq_mul,mul_one,sub_self,zero_pow (by omega : 2≠0)]
    exact sq_nonneg _
  · simp [en,hi]

lemma projection_mem {r : ℝ} {y : Y} (hy : WithLp.toLp 2 y∈Metric.closedBall (0:X) r) :
    WithLp.toLp 2 (projection y)∈Metric.closedBall (0:X) r := by
  exact Metric.mem_closedBall.mpr (by
    simpa only [dist_zero_right] using (projection_norm_le y).trans (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hy))

end ElasticityBoundaryPacket

end
end
section
/-! Flat finite jets remain flat under arbitrary honest smooth coordinates.
This is a consequence of the actual Faà di Bruno formula. -/
noncomputable section
namespace ElasticityBoundaryFlatComposition
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma comp_flat {f : F → G} {g : E → F} {x : E} (n : ℕ)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (g x)) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (hz : ∀ k≤n, iteratedFDeriv ℝ k f (g x)=0) :
    iteratedFDeriv ℝ n (f ∘ g) x=0 := by
  rw [iteratedFDeriv_comp hf hg (by exact_mod_cast le_top)]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_eq_zero
  intro c _
  ext v
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    ftaylorSeries, hz c.length c.length_le,zero_apply]

end ElasticityBoundaryFlatComposition

end
end
section
/-! The flattened zero plane consists of actual boundary points; lower
physical jets give actual normal Taylor remainders on a ball packet support. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryNormalTaylor ElasticityBoundaryFlatComposition
variable {Ω : Set X} {x : X}

lemma Setup.plane_frontier (s : Setup Ω x) (hO : IsOpen Ω)
    {y : X} (hy : y∈s.e.source) (hz : y 2=0) : s.e y∈frontier Ω := by
  have hn : s.e y∉Ω := by
    rw [s.inside y hy,hz]
    exact lt_irrefl 0
  have hct : Continuous (fun t : ℝ => y+t • EuclideanSpace.single 2 (1:ℝ)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => y+t • EuclideanSpace.single 2 (1:ℝ)) (𝓝[>] 0) (𝓝 y) := by
    simpa only [zero_smul,add_zero] using hct.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have hm : ∀ᶠ t : ℝ in 𝓝[>] 0, s.e (y+t • EuclideanSpace.single 2 (1:ℝ))∈Ω := by
    filter_upwards [ht (s.e.open_source.mem_nhds hy),self_mem_nhdsWithin] with t hty htp
    rw [s.inside _ hty]
    simpa [hz,PiLp.single_apply] using htp
  have hc : s.e y∈closure Ω := mem_closure_of_tendsto
    (((s.smooth.continuousOn y hy).continuousAt (s.e.open_source.mem_nhds hy)).tendsto.comp ht) hm
  rw [hO.frontier_eq]
  exact ⟨hc,hn⟩

def Setup.chartFunction (s : Setup Ω x) (f : X → ℝ) : Y → ℝ :=
  fun y => f (s.Φ (WithLp.toLp 2 y))

lemma Setup.chartFunction_smooth (s : Setup Ω x) {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (s.chartFunction f) :=
  hf.comp (s.Φ_smooth.comp PiLp.contDiff_toLp)

lemma Setup.chart_flat (s : Setup Ω x) (hO : IsOpen Ω) {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (hz : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k f z=0)
    {y : Y} (hy : WithLp.toLp 2 y∈s.K) (hy0 : y 2=0) :
    iteratedFDeriv ℝ n (s.chartFunction f) y=0 := by
  apply comp_flat n hf.contDiffAt (s.Φ_smooth.comp PiLp.contDiff_toLp).contDiffAt
  intro k hk
  change iteratedFDeriv ℝ k f (s.Φ (WithLp.toLp 2 y))=0
  rw [(s.Φ_germ _ hy).eq_of_nhds]
  exact hz k hk _ (s.plane_frontier hO (s.source hy) hy0)

lemma Setup.chart_normal_factor (s : Setup Ω x) (hO : IsOpen Ω) {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (hz : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k f z=0)
    {r : ℝ} (hK : s.K=Metric.closedBall 0 r) {y : Y} (hy : WithLp.toLp 2 y∈s.K) :
    s.chartFunction f y=(y 2)^(n+1)*quotient n (s.chartFunction f) y := by
  apply normal_factor (s.chartFunction_smooth hf) n y
  intro k hk
  rw [normalJet,s.chart_flat hO hf k (fun j hj => hz j (hj.trans hk))]
  · rfl
  · rw [hK] at hy ⊢
    exact projection_mem hy
  · exact projection_two y

end ElasticityBoundaryPacket

end
end
section
/-! Pointwise linearity of the literal pulled energy tensor in the two
scalar Lamé values. Geometric coefficients are not frozen off-center. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryPhysicalMass ElasticityBoundaryChartOperator
  ElasticityBoundaryPullback ElasticityBoundaryFrameOperator ElasticityBoundaryPhysicalStrong
  ElasticityBoundaryLayerOperator
variable {Ω : Set X} {x : X}

lemma elasticityTensor_decomp (l m : ℂ) (i α j β : I) :
    elasticityTensor l m i α j β=l*elasticityTensor 1 0 i α j β+
      m*elasticityTensor 0 1 i α j β := by
  unfold elasticityTensor
  ring

lemma Setup.rawCoeff_decomp (s : Setup Ω x) (l m : X → ℂ) (i α j β : I) (y : Y) :
    s.rawCoeff l m i α j β y=
      l (s.Φ (WithLp.toLp 2 y))*s.rawCoeff (fun _ => 1) (fun _ => 0) i α j β y+
      m (s.Φ (WithLp.toLp 2 y))*s.rawCoeff (fun _ => 0) (fun _ => 1) i α j β y := by
  unfold Setup.rawCoeff ElasticityBoundaryPhysicalMass.principal chartPrincipal principalPull mixedTensor coeff
  simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro v _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [elasticityTensor_decomp (l _) (m _)]
  ring

def Setup.linearCoeff (s : Setup Ω x) (l m : Y → ℂ) (i α j β : I) (y : Y) : ℂ :=
  l y*s.rawCoeff (fun _ => 1) (fun _ => 0) i α j β y+
  m y*s.rawCoeff (fun _ => 0) (fun _ => 1) i α j β y

lemma Setup.linearCoeff_continuous (s : Setup Ω x) {l m : Y → ℂ}
    (hl : Continuous l) (hm : Continuous m) (i α j β : I) :
    Continuous (s.linearCoeff l m i α j β) :=
  (hl.mul (s.rawCoeff_continuous contDiff_const contDiff_const i α j β)).add
    (hm.mul (s.rawCoeff_continuous contDiff_const contDiff_const i α j β))

lemma Setup.linearCoeff_zero (s : Setup Ω x) (l m : Y → ℂ) (i α j β : I) :
    s.linearCoeff l m i α j β 0=(s.jacobian 0:ℂ)*elasticityTensor (l 0) (m 0) i α j β := by
  rw [Setup.linearCoeff,s.rawCoeff_zero,s.rawCoeff_zero,elasticityTensor_decomp (l 0) (m 0)]
  ring

lemma Setup.localize_linearCoeff (s : Setup Ω x) {l m : Y → ℂ}
    (hl : Continuous l) (hm : Continuous m) :
    ∃ H : I → I → I → I → Y → ℂ,
      (∀ i α j β, Continuous (H i α j β)) ∧
      (∀ i α j β, HasCompactSupport (H i α j β)) ∧
      (∀ i α j β y, WithLp.toLp 2 y∈s.K → H i α j β y=s.linearCoeff l m i α j β y) := by
  obtain ⟨ρ,hρ,hρc,_,hρ1,_⟩ := ElasticityBoundary.compact_smooth_cutoff
    s.compact isOpen_univ (subset_univ s.K)
  let ρc : Y → ℂ := fun y => (ρ (WithLp.toLp 2 y):ℂ)
  have hρcc : HasCompactSupport ρc :=
    (hρc.comp_homeomorph (PiLp.homeomorph 2 (fun _ : I => ℝ)).symm).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  refine ⟨fun i α j β y => ρc y*s.linearCoeff l m i α j β y,?_,?_,?_⟩
  · intro i α j β
    exact (Complex.continuous_ofReal.comp (hρ.continuous.comp
      (PiLp.continuous_toLp 2 (fun _ : I => ℝ)))).mul (s.linearCoeff_continuous hl hm i α j β)
  · intro i α j β
    exact hρcc.mul_right
  · intro i α j β y hy
    simp only [ρc,hρ1.self_of_nhdsSet _ hy,Complex.ofReal_one,one_mul]

end ElasticityBoundaryPacket

end
end
section
/-! Actual normal jet induction step from the physical DN map. The quotient
is the concrete Taylor integral; no pseudodifferential symbol or jet conclusion
is postulated. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryNormalTaylor
variable {Ω : Set X} {x : X}

lemma Setup.boundary_normal_step (s : Setup Ω x) {l₁ m₁ l₂ m₂ : X → ℝ}
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω) (hx : x∈closure Ω)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂)
    (n : ℕ) (hzl : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k (l₁-l₂) z=0)
    (hzm : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k (m₁-m₂) z=0)
    {r : ℝ} (hK : s.K=Metric.closedBall 0 r) :
    normalJet (n+1) (s.chartFunction (l₁-l₂)) 0=0 ∧
      normalJet (n+1) (s.chartFunction (m₁-m₂)) 0=0 := by
  let L := quotient n (s.chartFunction (l₁-l₂))
  let M := quotient n (s.chartFunction (m₁-m₂))
  have hLc : Continuous (fun y => (L y:ℂ)) := Complex.continuous_ofReal.comp
    (quotient_continuous (s.chartFunction_smooth (hl₁.sub hl₂)) n)
  have hMc : Continuous (fun y => (M y:ℂ)) := Complex.continuous_ofReal.comp
    (quotient_continuous (s.chartFunction_smooth (hm₁.sub hm₂)) n)
  obtain ⟨H,hHc,hHs,hHe⟩ := s.localize_linearCoeff hLc hMc
  have hH (i α j β : I) (y : Y) (hy : WithLp.toLp 2 y∈s.K) :
      s.rawCoeff (fun z => (l₁ z:ℂ)) (fun z => (m₁ z:ℂ)) i α j β y-
      s.rawCoeff (fun z => (l₂ z:ℂ)) (fun z => (m₂ z:ℂ)) i α j β y=(y 2:ℂ)^(n+1)*H i α j β y := by
    rw [hHe i α j β y hy,Setup.linearCoeff,
      s.rawCoeff_decomp (fun z => (l₁ z:ℂ)) (fun z => (m₁ z:ℂ)),
      s.rawCoeff_decomp (fun z => (l₂ z:ℂ)) (fun z => (m₂ z:ℂ))]
    have hl := s.chart_normal_factor hO (hl₁.sub hl₂) n hzl hK hy
    have hm := s.chart_normal_factor hO (hm₁.sub hm₂) n hzm hK hy
    change l₁ (s.Φ (WithLp.toLp 2 y))-l₂ (s.Φ (WithLp.toLp 2 y))=(y 2)^(n+1)*L y at hl
    change m₁ (s.Φ (WithLp.toLp 2 y))-m₂ (s.Φ (WithLp.toLp 2 y))=(y 2)^(n+1)*M y at hm
    have hlc : (l₁ (s.Φ (WithLp.toLp 2 y)):ℂ)-(l₂ (s.Φ (WithLp.toLp 2 y)):ℂ)=
        (y 2:ℂ)^(n+1)*(L y:ℂ) := by exact_mod_cast hl
    have hmc : (m₁ (s.Φ (WithLp.toLp 2 y)):ℂ)-(m₂ (s.Φ (WithLp.toLp 2 y)):ℂ)=
        (y 2:ℂ)^(n+1)*(M y:ℂ) := by exact_mod_cast hm
    linear_combination hlc*s.rawCoeff (fun _ => 1) (fun _ => 0) i α j β y +
      hmc*s.rawCoeff (fun _ => 0) (fun _ => 1) i α j β y
  have hH0 : (fun i α j β => H i α j β 0)=
      (fun i α j β => (s.jacobian 0:ℂ)*ElasticityBoundaryLayerOperator.elasticityTensor
        (L 0) (M 0) i α j β) := by
    funext i α j β
    rw [hHe i α j β 0 (by simpa using s.zero_mem),s.linearCoeff_zero]
  have hpair := pair_separates (n+1) (l₁ x) (m₁ x) (l₂ x) (m₂ x) (s.jacobian 0)
    (L 0) (M 0)
    (admissible_frozen_ne ha₁ hx).1 (admissible_frozen_ne ha₂ hx).1
    (admissible_frozen_ne ha₁ hx).2 (admissible_frozen_ne ha₂ hx).2
    (Complex.ofReal_ne_zero.mpr s.jacobian_pos.ne') (by
      intro p q hp hq
      rw [← hH0]
      exact s.extract_normal hl₁ hm₁ hl₂ hm₂ ha₁ ha₂ hO hB hx hDN (n+1) H hHc hHs hH p q hp hq)
  have hL : L 0=0 := Complex.ofReal_eq_zero.mp hpair.1
  have hM : M 0=0 := Complex.ofReal_eq_zero.mp hpair.2
  have hfac : ((n+1).factorial:ℝ)⁻¹≠0 := inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  dsimp only [L] at hL
  dsimp only [M] at hM
  rw [quotient_zero] at hL hM
  exact ⟨(smul_eq_zero.mp hL).resolve_left hfac,(smul_eq_zero.mp hM).resolve_left hfac⟩

end ElasticityBoundaryPacket

end
end
section
/-! Schwarz symmetry at every finite order for real C-infinity functions.
The analytic-only generic-field theorem is not used. -/
noncomputable section
namespace ElasticityBoundaryJetSymmetry
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def dir (v : E) (f : E → F) : E → F := fun x => fderiv ℝ f x v

def word : List E → (E → F) → E → F
  | [], f => f
  | v::vs, f => dir v (word vs f)

lemma dir_smooth {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (dir v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma word_smooth {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (vs : List E) :
    ContDiff ℝ (⊤ : ℕ∞) (word vs f) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact dir_smooth ih v

lemma dir_comm {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v w : E) :
    dir v (dir w f)=dir w (dir v f) := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)).differentiableAt
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact (WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top)))
  have he (z : E) : fderiv ℝ (dir z f) x=(fderiv ℝ (fderiv ℝ f) x).flip z := by
    unfold dir
    rw [fderiv_clm_apply hd (differentiableAt_const z)]
    simp
  change fderiv ℝ (dir w f) x v=fderiv ℝ (dir v f) x w
  rw [he,he]
  exact hs v w

lemma word_perm {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {vs ws : List E}
    (h : vs.Perm ws) : word vs f=word ws f := by
  induction h with
  | nil => rfl
  | cons v h ih => simp only [word,ih]
  | swap v w vs => exact dir_comm (word_smooth hf vs) w v
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

lemma word_ofFn {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (v : Fin n → E) (x : E) :
    word (List.ofFn v) f x=iteratedFDeriv ℝ n f x v := by
  induction n generalizing x with
  | zero => simp [word]
  | succ n ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (word (List.ofFn (fun i => v i.succ)) f) x (v 0)=_
    have he : word (List.ofFn (fun i => v i.succ)) f=
        (fun y => iteratedFDeriv ℝ n f y (fun i => v i.succ)) := by
      funext y
      exact ih _ y
    rw [he,fderiv_continuousMultilinear_apply_const
      (hf.differentiable_iteratedFDeriv (by exact_mod_cast (WithTop.coe_lt_top n))).differentiableAt]
    rfl

lemma iterated_perm {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → E) (x : E) :
    iteratedFDeriv ℝ n f x (fun i => v (σ i))=iteratedFDeriv ℝ n f x v := by
  rw [← word_ofFn hf,← word_ofFn hf]
  exact congrFun (word_perm hf (σ.ofFn_comp_perm v)) x

end ElasticityBoundaryJetSymmetry

end
end
section
/-! Lower full jets vanish on a hypersurface, and the next pure-normal jet
then determines the entire next tensor. No analyticity is used. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryFlatHyperplane
open ElasticityBoundaryJetSymmetry ElasticityBoundaryNormalTaylor
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma tangent_deriv_zero {g : Y → F} (hg : DifferentiableAt ℝ g 0)
    {r : ℝ} (hr : 0<r) (hz : ∀ y∈Metric.ball (0:Y) r, y 2=0 → g y=0)
    {v : Y} (hv : v 2=0) : fderiv ℝ g 0 v=0 := by
  have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0:Y)) := by
    simpa only [zero_smul] using hc.continuousAt.tendsto (x := (0:ℝ))
  have he : (fun t : ℝ => g (t • v)) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [ht (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] with t ht
    exact hz _ ht (by simp [hv])
  have hd := (show DifferentiableAt ℝ g ((0:Y)+(0:ℝ) • v) by simpa using hg).deriv_comp_add_smul
  simp only [zero_add,zero_smul] at hd
  rw [← hd,he.deriv_eq,deriv_const]

lemma flat_step {f : Y → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    {r : ℝ} (hr : 0<r)
    (hz : ∀ y∈Metric.ball (0:Y) r, y 2=0 → iteratedFDeriv ℝ n f y=0)
    (hn : normalJet (n+1) f 0=0) : iteratedFDeriv ℝ (n+1) f 0=0 := by
  classical
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) 0 :=
    (hf.differentiable_iteratedFDeriv (by exact_mod_cast (WithTop.coe_lt_top n))).differentiableAt
  have hfirst (u : Fin (n+1) → Y) (hu : u 0 2=0) : iteratedFDeriv ℝ (n+1) f 0 u=0 := by
    rw [iteratedFDeriv_succ_apply_left, tangent_deriv_zero hd hr hz hu]
    rfl
  have hany (u : Fin (n+1) → Y) (i : Fin (n+1)) (hu : u i 2=0) :
      iteratedFDeriv ℝ (n+1) f 0 u=0 := by
    rw [← iterated_perm hf (n+1) (Equiv.swap 0 i) u 0]
    exact hfirst _ (by simpa using hu)
  ext u
  have he : u=(fun k => ∑ i : Fin 3, u k i • Pi.single i (1:ℝ)) := by
    funext k i
    simp [Pi.single_apply]
  rw [he]
  change (iteratedFDeriv ℝ (n+1) f 0).toMultilinearMap (fun k => ∑ i : Fin 3, u k i • Pi.single i (1:ℝ))=0
  rw [MultilinearMap.map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [MultilinearMap.map_smul_univ]
  suffices (iteratedFDeriv ℝ (n+1) f 0) (fun k => Pi.single (j k) (1:ℝ))=0 by
    change (∏ i, u i (j i)) • (iteratedFDeriv ℝ (n+1) f 0) (fun i => Pi.single (j i) (1:ℝ))=0
    rw [this,smul_zero]
  by_cases h : ∀ k, j k=2
  · simpa only [h,en,normalJet] using hn
  · push Not at h
    obtain ⟨k,hk⟩ := h
    exact hany _ k (by simp [Ne.symm hk])

end ElasticityBoundaryFlatHyperplane

end
end
section
/-! Full jet flatness in honest boundary coordinates and back in the fixed
physical Euclidean coordinates. No jet transformation is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryNormalTaylor ElasticityBoundaryFlatComposition
  ElasticityBoundaryFlatHyperplane
variable {Ω : Set X} {x : X}

lemma Setup.chart_full_step (s : Setup Ω x) (hO : IsOpen Ω) {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (hz : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k f z=0)
    {r : ℝ} (hr : 0<r) (hK : s.K=Metric.closedBall 0 r)
    (hn : normalJet (n+1) (s.chartFunction f) 0=0) :
    iteratedFDeriv ℝ (n+1) (s.chartFunction f) 0=0 := by
  have ht : Tendsto (WithLp.toLp 2 : Y → X) (𝓝 (0:Y)) (𝓝 (0:X)) :=
    (PiLp.continuous_toLp 2 (fun _ : I => ℝ)).continuousAt
  obtain ⟨ε,hε,hE⟩ := Metric.mem_nhds_iff.mp
    (ht (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)))
  apply flat_step (s.chartFunction_smooth hf) n hε _ hn
  intro y hy hy0
  exact s.chart_flat hO hf n hz (by rw [hK]; exact Metric.ball_subset_closedBall (hE hy)) hy0

lemma Setup.Ψ_zero (s : Setup Ω x) : s.Ψ x=0 := by
  have hx : x∈s.e '' s.K := ⟨0,s.zero_mem,s.center⟩
  exact (s.Ψ_germ x hx).eq_of_nhds.trans
    ((congrArg s.e.symm s.center).symm.trans (s.e.left_inv s.at_zero))

lemma Setup.inverse_germ (s : Setup Ω x) :
    (fun z => s.Φ (s.Ψ z)) =ᶠ[𝓝 x] fun z => z := by
  have hx : x∈s.e '' s.K := ⟨0,s.zero_mem,s.center⟩
  have ht : Tendsto s.Ψ (𝓝 x) (𝓝 (0:X)) := by
    simpa only [s.Ψ_zero] using s.Ψ_smooth.continuous.continuousAt.tendsto (x := x)
  have hxt : x∈s.e.target := by simpa only [s.center] using s.e.map_source s.at_zero
  filter_upwards [(s.Φ_germ 0 s.zero_mem).comp_tendsto ht,s.Ψ_germ x hx,
    s.e.open_target.mem_nhds hxt] with z hΦ hΨ hz
  change s.Φ (s.Ψ z)=s.e (s.Ψ z) at hΦ
  rw [hΦ,hΨ,s.e.right_inv hz]

lemma Setup.physical_flat_of_chart (s : Setup Ω x) {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (hz : ∀ k≤n, iteratedFDeriv ℝ k (s.chartFunction f) 0=0) :
    iteratedFDeriv ℝ n f x=0 := by
  let g : X → Y := fun z => (s.Ψ z).ofLp
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := PiLp.contDiff_ofLp.comp s.Ψ_smooth
  have hg0 : g x=0 := by simp only [g,s.Ψ_zero,WithLp.ofLp_zero]
  have hcomp : iteratedFDeriv ℝ n (s.chartFunction f ∘ g) x=0 := by
    apply comp_flat n (s.chartFunction_smooth hf).contDiffAt hg.contDiffAt
    intro k hk
    rw [hg0]
    exact hz k hk
  have he : (s.chartFunction f ∘ g) =ᶠ[𝓝 x] f := by
    filter_upwards [s.inverse_germ] with z hz
    change f (s.Φ (s.Ψ z))=f z
    rw [hz]
  rw [← (he.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hcomp

end ElasticityBoundaryPacket

end
end
section
/-! All actual Frechet boundary jets from the physical DN map. Induction is
global along the boundary, so tangential derivatives of lower jets are zero;
only the pure normal step uses oscillatory solutions. -/
noncomputable section
open Set
open scoped Topology
namespace ElasticityBoundaryPacket
open Elasticity
variable {Ω : Set X}

lemma boundary_flat_difference_global {l₁ m₁ l₂ m₂ : X → ℝ}
    (hS : SourceSmoothBoundary Ω) (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) :
    ∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n (l₁-l₂) x=0 ∧
      iteratedFDeriv ℝ n (m₁-m₂) x=0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      intro x hx
      have hv := boundary_values_global hS hO hB hl₁ hm₁ hl₂ hm₂ ha₁ ha₂ hDN hx
      constructor
      · ext v
        simp only [iteratedFDeriv_zero_apply,Pi.sub_apply,hv.1,sub_self,zero_apply]
      · ext v
        simp only [iteratedFDeriv_zero_apply,Pi.sub_apply,hv.2,sub_self,zero_apply]
    | succ n =>
      intro x hx
      obtain ⟨s,r,hr,hK⟩ := setup_ball_exists hS hx
      have hzl : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k (l₁-l₂) z=0 :=
        fun k hk z hz => (ih k (Nat.lt_succ_of_le hk) z hz).1
      have hzm : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k (m₁-m₂) z=0 :=
        fun k hk z hz => (ih k (Nat.lt_succ_of_le hk) z hz).2
      have hn := s.boundary_normal_step hl₁ hm₁ hl₂ hm₂ ha₁ ha₂ hO hB
        (frontier_subset_closure hx) hDN n hzl hzm hK
      have hlf := s.chart_full_step hO (hl₁.sub hl₂) n hzl hr hK hn.1
      have hmf := s.chart_full_step hO (hm₁.sub hm₂) n hzm hr hK hn.2
      constructor
      · apply s.physical_flat_of_chart (hl₁.sub hl₂) (n+1)
        intro k hk
        obtain hk|hk := lt_or_eq_of_le hk
        · exact s.chart_flat hO (hl₁.sub hl₂) k
            (fun j hj => hzl j (hj.trans (Nat.le_of_lt_succ hk)))
            (by simpa using s.zero_mem) rfl
        · subst k
          exact hlf
      · apply s.physical_flat_of_chart (hm₁.sub hm₂) (n+1)
        intro k hk
        obtain hk|hk := lt_or_eq_of_le hk
        · exact s.chart_flat hO (hm₁.sub hm₂) k
            (fun j hj => hzm j (hj.trans (Nat.le_of_lt_succ hk)))
            (by simpa using s.zero_mem) rfl
        · subst k
          exact hmf

lemma boundary_jets_global {l₁ m₁ l₂ m₂ : X → ℝ}
    (hS : SourceSmoothBoundary Ω) (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) :
    (∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n l₂ x=iteratedFDeriv ℝ n l₁ x) ∧
      (∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n m₂ x=iteratedFDeriv ℝ n m₁ x) := by
  have h := boundary_flat_difference_global hS hO hB hl₁ hm₁ hl₂ hm₂ ha₁ ha₂ hDN
  constructor
  · intro n x hx
    have hz := (h n x hx).1
    rw [iteratedFDeriv_sub (hl₁.of_le (by exact_mod_cast le_top))
      (hl₂.of_le (by exact_mod_cast le_top))] at hz
    exact (sub_eq_zero.mp hz).symm
  · intro n x hx
    have hz := (h n x hx).2
    rw [iteratedFDeriv_sub (hm₁.of_le (by exact_mod_cast le_top))
      (hm₂.of_le (by exact_mod_cast le_top))] at hz
    exact (sub_eq_zero.mp hz).symm

end ElasticityBoundaryPacket

end
end
section
/- The exact physical DN localization proofs are reused, not duplicated. -/

end
section
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundary
variable {Ω : Set X}

lemma admissible_boundary_values (hD : SourceDomain Ω) (l₁ m₁ l₂ m₂ : X → ℝ)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) :
    ∀ x∈frontier Ω, l₁ x=l₂ x ∧ m₁ x=m₂ x := by
  obtain ⟨U₁,hU₁,hs₁,hl₁,hm₁⟩ := ha₁.common_neighborhood
  obtain ⟨U₂,hU₂,hs₂,hl₂,hm₂⟩ := ha₂.common_neighborhood
  obtain ⟨L₁,M₁,hL₁,hM₁,heL₁,heM₁,hp₁,_,_⟩ :=
    admissible_global_extension hD.2.2.1.isCompact_closure hU₁ hs₁ l₁ m₁ hl₁ hm₁ ha₁.2.2
  obtain ⟨L₂,M₂,hL₂,hM₂,heL₂,heM₂,hp₂,_,_⟩ :=
    admissible_global_extension hD.2.2.1.isCompact_closure hU₂ hs₂ l₂ m₂ hl₂ hm₂ ha₂.2.2
  have hd : DN Ω L₁ M₁=DN Ω L₂ M₂ :=
    (DN_coeff_congr hD.1.measurableSet
      (fun x hx => heL₁.self_of_nhdsSet (subset_closure hx))
      (fun x hx => heM₁.self_of_nhdsSet (subset_closure hx))).trans
      (hDN.trans (DN_coeff_congr hD.1.measurableSet
        (fun x hx => heL₂.self_of_nhdsSet (subset_closure hx))
        (fun x hx => heM₂.self_of_nhdsSet (subset_closure hx))).symm)
  intro x hx
  have hc := frontier_subset_closure hx
  have h := boundary_values_global hD.2.2.2 hD.1 hD.2.2.1 hL₁ hM₁ hL₂ hM₂
    (admissible_of_global hL₁ hM₁ hp₁) (admissible_of_global hL₂ hM₂ hp₂) hd hx
  simpa only [heL₁.self_of_nhdsSet hc,heM₁.self_of_nhdsSet hc,
    heL₂.self_of_nhdsSet hc,heM₂.self_of_nhdsSet hc] using h

end ElasticityBoundaryPacket

end
end
section
/-! Smooth-on-closure all-jet determination from the actual real physical DN
map, for every bounded connected domain with honest C-infinity boundary. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundary
variable {Ω : Set X}

theorem admissible_boundary_jets (hD : SourceDomain Ω) (l₁ m₁ l₂ m₂ : X → ℝ)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) :
    (∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n l₂ x=iteratedFDeriv ℝ n l₁ x) ∧
      (∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n m₂ x=iteratedFDeriv ℝ n m₁ x) := by
  obtain ⟨U₁,hU₁,hs₁,hl₁,hm₁⟩ := ha₁.common_neighborhood
  obtain ⟨U₂,hU₂,hs₂,hl₂,hm₂⟩ := ha₂.common_neighborhood
  obtain ⟨L₁,M₁,hL₁,hM₁,heL₁,heM₁,hp₁,_,_⟩ :=
    admissible_global_extension hD.2.2.1.isCompact_closure hU₁ hs₁ l₁ m₁ hl₁ hm₁ ha₁.2.2
  obtain ⟨L₂,M₂,hL₂,hM₂,heL₂,heM₂,hp₂,_,_⟩ :=
    admissible_global_extension hD.2.2.1.isCompact_closure hU₂ hs₂ l₂ m₂ hl₂ hm₂ ha₂.2.2
  have hd : DN Ω L₁ M₁=DN Ω L₂ M₂ :=
    (DN_coeff_congr hD.1.measurableSet
      (fun x hx => heL₁.self_of_nhdsSet (subset_closure hx))
      (fun x hx => heM₁.self_of_nhdsSet (subset_closure hx))).trans
      (hDN.trans (DN_coeff_congr hD.1.measurableSet
        (fun x hx => heL₂.self_of_nhdsSet (subset_closure hx))
        (fun x hx => heM₂.self_of_nhdsSet (subset_closure hx))).symm)
  have h := boundary_jets_global hD.2.2.2 hD.1 hD.2.2.1 hL₁ hM₁ hL₂ hM₂
    (admissible_of_global hL₁ hM₁ hp₁) (admissible_of_global hL₂ hM₂ hp₂) hd
  have je {f g : X → ℝ} (he : f =ᶠ[𝓝ˢ (closure Ω)] g) (n : ℕ) (x : X) (hx : x∈frontier Ω) :
      iteratedFDeriv ℝ n f x=iteratedFDeriv ℝ n g x :=
    ((he.filter_mono (nhds_le_nhdsSet (frontier_subset_closure hx))).iteratedFDeriv ℝ n).eq_of_nhds
  constructor
  · intro n x hx
    simpa only [je heL₁ n x hx,je heL₂ n x hx] using h.1 n x hx
  · intro n x hx
    simpa only [je heM₁ n x hx,je heM₂ n x hx] using h.2 n x hx

end ElasticityBoundaryPacket

end
end

end OAI
