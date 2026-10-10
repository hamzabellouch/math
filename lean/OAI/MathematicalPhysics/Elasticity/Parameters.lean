import OAI.MathematicalPhysics.Elasticity.Planar

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
abbrev PL2 := Lp ℂ 2 (volume : Measure ℂ)

lemma lp_dist_add (f g : PL2) : ((f+g : PL2) : 𝓢'(ℂ,ℂ))=(f : 𝓢'(ℂ,ℂ))+(g : 𝓢'(ℂ,ℂ)) :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℂ) 2).map_add f g
lemma lp_dist_smul (c : ℝ) (f : PL2) : ((c • f : PL2) : 𝓢'(ℂ,ℂ))=c • (f : 𝓢'(ℂ,ℂ)) := by
  change (((c : ℂ) • f : PL2) : 𝓢'(ℂ,ℂ))=(c : ℂ) • (f : 𝓢'(ℂ,ℂ))
  exact (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℂ) 2).map_smul (c : ℂ) f
lemma lp_dist_sum (f : n → PL2) : ((∑ j, f j : PL2) : 𝓢'(ℂ,ℂ))=∑ j, (f j : 𝓢'(ℂ,ℂ)) :=
  map_sum (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℂ) 2) f _

/-- The matrix multiplication here acts on genuine L2 classes and agrees with
multiplication on distributions; it is not a formal bounded-operator model. -/
theorem exists_matrix_multiplier (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hc : ∀ i j, HasCompactSupport (a i j)) :
    ∃ M : Hilbert n →L[ℂ] Hilbert n, ∀ (f : Hilbert n) (i : n),
      (M f i : 𝓢'(ℂ,ℂ))=∑ j, smulLeftCLM ℂ (a i j) (f j : 𝓢'(ℂ,ℂ)) := by
  choose L hL using fun i j => exists_bounded_nat_multiplier 0 (ha i j) (hc i j)
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)
  let M' : (n → PL2) →L[ℂ] (n → PL2) :=
    ContinuousLinearMap.pi (fun i => ∑ j, (L i j).comp (ContinuousLinearMap.proj j))
  refine ⟨e.symm.toContinuousLinearMap.comp (M'.comp e.toContinuousLinearMap),fun f i => ?_⟩
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,e,
    PiLp.continuousLinearEquiv_apply,PiLp.continuousLinearEquiv_symm_apply,WithLp.ofLp_toLp,
    M',ContinuousLinearMap.pi_apply,sum_apply,ContinuousLinearMap.proj_apply]
  rw [lp_dist_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Nat.cast_zero,sobolevInjection,neg_zero,besselPotential_zero,ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply] using hL i j (f j)

 theorem exists_planar_distribution_inverse {S Ω : Set ℂ} (hS : IsCompact S)
    (hΩ : Ω ⊆ S) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, (a i j).HasTemperateGrowth) :
    ∃ T : Hilbert n →L[ℂ] Hilbert n, ∀ f : Hilbert n, ∀ i,
      LocalEqual Ω (ElasticityPlanarDistribution.dbar (T f i : 𝓢'(ℂ,ℂ))+
        ∑ j, smulLeftCLM ℂ (a i j) (T f j : 𝓢'(ℂ,ℂ))) (f i : 𝓢'(ℂ,ℂ)) := by
  obtain ⟨C,hC,T,hT,heq⟩ := exists_planar_weak_inverse hS a (fun i j => (ha i j).1)
  exact ⟨T,fun f => weak_to_local_equation Ω S hΩ a ha (T f) f (heq f)⟩

/-- Local smooth dependence of an actual distributional planar inverse along
the coefficient homotopy s*a. This supplies the parameter ingredient for frame
construction without invoking holomorphic bundle triviality. -/
theorem local_homotopy_inverse {S Ω : Set ℂ} (hS : IsCompact S) (hΩ : Ω ⊆ S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hc : ∀ i j, HasCompactSupport (a i j)) (s₀ : ℝ) :
    ∃ (U : Set ℝ) (T : ℝ → Hilbert n →L[ℂ] Hilbert n),
      IsOpen U ∧ s₀ ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) T U ∧
      ∀ s ∈ U, ∀ f : Hilbert n, ∀ i,
        LocalEqual Ω (ElasticityPlanarDistribution.dbar (T s f i : 𝓢'(ℂ,ℂ))+
          ∑ j, smulLeftCLM ℂ (fun z => (s : ℂ)*a i j z)
            (T s f j : 𝓢'(ℂ,ℂ))) (f i : 𝓢'(ℂ,ℂ)) := by
  have hat (i j : n) : (a i j).HasTemperateGrowth := (hc i j).hasTemperateGrowth (ha i j)
  have hscaled (c : ℂ) (i j : n) : (fun z => c*a i j z).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const c).mul (hat i j)
  obtain ⟨M,hM⟩ := exists_matrix_multiplier a ha hc
  obtain ⟨T₀,hT₀⟩ := exists_planar_distribution_inverse hS hΩ
    (fun i j z => (s₀ : ℂ)*a i j z) (fun i j => (Function.HasTemperateGrowth.const _).mul (hat i j))
  let B : ℝ → Hilbert n →L[ℂ] Hilbert n := fun s => (s-s₀) • M
  let T : ℝ → Hilbert n →L[ℂ] Hilbert n := fun s => T₀*Ring.inverse (1+B s*T₀)
  let U : Set ℝ := {s | ‖B s*T₀‖<1}
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := (contDiff_id.sub contDiff_const).smul contDiff_const
  have hopen : IsOpen U := isOpen_lt (hB.continuous.mul continuous_const).norm continuous_const
  have hBzero : B s₀=0 := by
    simpa only [B,sub_self] using zero_smul ℝ M
  have hmem : s₀∈U := by
    change ‖B s₀*T₀‖<1
    rw [hBzero,zero_mul,norm_zero]
    exact zero_lt_one
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) T U := fun s hs =>
    (ElasticityDualSolvability.smooth_local_weak_inverse T₀ B hB.contDiffAt hs).contDiffWithinAt
  refine ⟨U,T,hopen,hmem,hsmooth,fun s hs f i => ?_⟩
  change ‖B s*T₀‖<1 at hs
  have hu : IsUnit (1+B s*T₀) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one
      (by simpa only [norm_neg] using hs : ‖-(B s*T₀)‖<1)
  let q := Ring.inverse (1+B s*T₀) f
  have heq := hT₀ q i
  have htot : q+B s (T₀ q)=f := by
    have h := congrArg (fun L : Hilbert n →L[ℂ] Hilbert n => L f)
      (Ring.mul_inverse_cancel (1+B s*T₀) hu)
    simpa only [mul_apply_eq_comp,add_apply,one_apply_eq_self] using h
  have hprod : ((B s (T₀ q)) i : 𝓢'(ℂ,ℂ))=
      ∑ j, smulLeftCLM ℂ (fun z => (((s-s₀ : ℝ) : ℂ))*a i j z) (T₀ q j : 𝓢'(ℂ,ℂ)) := by
    change (((s-s₀) • M (T₀ q) : Hilbert n) i : 𝓢'(ℂ,ℂ))=_
    simp only [PiLp.smul_apply,lp_dist_smul,hM,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ext φ
    simp only [smul_apply,smulLeftCLM_apply_apply]
    change (s-s₀) • ((T₀ q j : 𝓢'(ℂ,ℂ)) (SchwartzMap.smulLeftCLM ℂ (a i j) φ))=_
    change (((s-s₀ : ℝ) : ℂ)) • ((T₀ q j : 𝓢'(ℂ,ℂ)) (SchwartzMap.smulLeftCLM ℂ (a i j) φ))=_
    rw [← map_smul]
    congr 1
    ext z
    simp only [SchwartzMap.smulLeftCLM_apply_apply (hat i j),
      SchwartzMap.smulLeftCLM_apply_apply (hscaled ((s-s₀ : ℝ) : ℂ) i j),
      smul_eq_mul,smul_apply]
    ring
  intro φ hφ hφs
  have he := heq φ hφ hφs
  have ht := congrArg (fun v : Hilbert n => (v i : 𝓢'(ℂ,ℂ)) φ) htot
  rw [PiLp.add_apply,lp_dist_add,hprod] at ht
  change _= _ at he
  change ((ElasticityPlanarDistribution.dbar (T₀ q i : 𝓢'(ℂ,ℂ)))+
    ∑ j, smulLeftCLM ℂ (fun z => (s : ℂ)*a i j z) (T₀ q j : 𝓢'(ℂ,ℂ))) φ=_
  have hc' (j : n) : smulLeftCLM ℂ (fun z => (s : ℂ)*a i j z) (T₀ q j : 𝓢'(ℂ,ℂ))=
      smulLeftCLM ℂ (fun z => (s₀ : ℂ)*a i j z) (T₀ q j : 𝓢'(ℂ,ℂ))+
      smulLeftCLM ℂ (fun z => (((s-s₀ : ℝ) : ℂ))*a i j z) (T₀ q j : 𝓢'(ℂ,ℂ)) := by
    ext ψ
    simp only [smulLeftCLM_apply_apply,add_apply]
    rw [← map_add]
    congr 1
    ext z
    simp only [SchwartzMap.smulLeftCLM_apply_apply (hscaled (s : ℂ) i j),
      SchwartzMap.smulLeftCLM_apply_apply (hscaled (s₀ : ℂ) i j),
      SchwartzMap.smulLeftCLM_apply_apply (hscaled ((s-s₀ : ℝ) : ℂ) i j),
      add_apply,smul_eq_mul]
    rw [Complex.ofReal_sub]
    ring
  simp only [hc',Finset.sum_add_distrib,add_apply] at he ht ⊢
  linear_combination he+ht
end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators LineDeriv Manifold
open ElasticityRegularity
variable {n : Type*} [Fintype n]

def entryInjection (i : n) : Hilbert n →L[ℂ] 𝓢'(ℂ,ℂ) :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℂ) 2).comp
    ((ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)).toContinuousLinearMap)
omit [Fintype n] in
lemma entryInjection_apply (i : n) (f : Hilbert n) : entryInjection i f=(f i : 𝓢'(ℂ,ℂ)) := rfl

def planarOperator (a : n → n → ℂ → ℂ) (i : n) : Hilbert n →L[ℂ] 𝓢'(ℂ,ℂ) :=
  ((LineDeriv.lineDerivOpCLM ℂ 𝓢'(ℂ,ℂ) (1 : ℂ))+
    Complex.I • (LineDeriv.lineDerivOpCLM ℂ 𝓢'(ℂ,ℂ) Complex.I)).comp (entryInjection i)+
    ∑ j, (smulLeftCLM ℂ (a i j)).comp (entryInjection j)
lemma planarOperator_apply (a : n → n → ℂ → ℂ) (i : n) (f : Hilbert n) :
    planarOperator a i f=ElasticityPlanarDistribution.dbar (f i : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (a i j) (f j : 𝓢'(ℂ,ℂ)) := by
  simp only [planarOperator,ContinuousLinearMap.comp_apply,add_apply,smul_apply,sum_apply,
    entryInjection_apply,LineDeriv.lineDerivOpCLM_apply,ElasticityPlanarDistribution.dbar]

/-- A genuine smooth bounded weak inverse along the entire real homotopy.
The patching uses a proved smooth convex selection theorem from Mathlib;
it adds no global frame or invertibility assumption to the PDE. -/
theorem global_homotopy_inverse {S Ω : Set ℂ} (hS : IsCompact S) (hΩ : Ω ⊆ S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hc : ∀ i j, HasCompactSupport (a i j)) :
    ∃ T : ℝ → Hilbert n →L[ℂ] Hilbert n,
      ContDiff ℝ (⊤ : ℕ∞) T ∧ ∀ s, ∀ f : Hilbert n, ∀ i,
      LocalEqual Ω (ElasticityPlanarDistribution.dbar (T s f i : 𝓢'(ℂ,ℂ))+
        ∑ j, smulLeftCLM ℂ (fun z => (s : ℂ)*a i j z) (T s f j : 𝓢'(ℂ,ℂ)))
        (f i : 𝓢'(ℂ,ℂ)) := by
  let P : ℝ → Set (Hilbert n →L[ℂ] Hilbert n) := fun s => {T | ∀ f i,
    LocalEqual Ω (planarOperator (fun i j z => (s : ℂ)*a i j z) i (T f)) (f i : 𝓢'(ℂ,ℂ))}
  have hconv : ∀ s, Convex ℝ (P s) := by
    intro s T₁ hT₁ T₂ hT₂ b c _ _ hbc f i φ hφ hs
    have h₁ := hT₁ f i φ hφ hs
    have h₂ := hT₂ f i φ hφ hs
    change (planarOperator (fun i j z => (s : ℂ)*a i j z) i
      ((b : ℂ) • (T₁ f)+(c : ℂ) • (T₂ f))) φ=_
    simp only [map_add,map_smul,add_apply,smul_apply,h₁,h₂,smul_eq_mul]
    have hh : (b : ℂ)+(c : ℂ)=1 := by exact_mod_cast hbc
    rw [← add_mul,hh,one_mul]
  have hlocal : ∀ s : ℝ, ∃ U ∈ nhds s, ∃ T : ℝ → Hilbert n →L[ℂ] Hilbert n,
      ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,Hilbert n →L[ℂ] Hilbert n) (⊤ : ℕ∞) T U ∧
      ∀ t ∈ U, T t∈P t := by
    intro s
    obtain ⟨U,T,hU,hs,hT,heq⟩ := local_homotopy_inverse hS hΩ a ha hc s
    refine ⟨U,hU.mem_nhds hs,T,hT.contMDiffOn,fun t ht f i => ?_⟩
    simp only [planarOperator_apply]
    exact heq t ht f i
  obtain ⟨T,hT⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ,ℝ) hconv hlocal
  refine ⟨T,T.contMDiff.contDiff,fun s f i => ?_⟩
  simpa only [planarOperator_apply] using hT s f i
end ElasticityPlanar
section
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators Manifold
namespace ElasticityRegularity
variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
lemma complex_clm_apply_smooth {f : P → E →L[ℂ] F} {g : P → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => f p (g p)) :=
  ((ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).contDiff.comp hf).clm_apply hg
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
lemma complex_clm_comp_smooth {f : P → F →L[ℂ] G} {g : P → E →L[ℂ] F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => (f p).comp (g p)) := by
  let C := ContinuousLinearMap.compL ℂ E F G
  exact complex_clm_apply_smooth ((C.restrictScalars ℝ).contDiff.comp hf) hg
end ElasticityRegularity
namespace ElasticityPlanar
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
theorem exists_smooth_matrix_multiplier {K : Set ℂ} (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0) :
    ∃ M : P → Hilbert n →L[ℂ] Hilbert n,
      ContDiff ℝ (⊤ : ℕ∞) M ∧ ∀ p (f : Hilbert n) i,
        (M p f i : 𝓢'(ℂ,ℂ))=∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (f j : 𝓢'(ℂ,ℂ)) := by
  choose L hL hLe using fun i j => exists_smooth_lp_multiplier hK (a i j) (ha i j) (hs i j)
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)
  let M' : P → (n → PL2) →L[ℂ] (n → PL2) := fun p =>
    ContinuousLinearMap.pi (fun i => ∑ j, (L i j p).comp (ContinuousLinearMap.proj j))
  have hM' : ContDiff ℝ (⊤ : ℕ∞) M' := by
    apply (ContinuousLinearMap.piEquivL ℂ (n → PL2) (fun _ : n => PL2)).toContinuousLinearMap.restrictScalars ℝ |>.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    exact ContDiff.sum (fun j _ => complex_clm_comp_smooth (hL i j) contDiff_const)
  refine ⟨fun p => e.symm.toContinuousLinearMap.comp ((M' p).comp e.toContinuousLinearMap),
    complex_clm_comp_smooth contDiff_const (complex_clm_comp_smooth hM' contDiff_const),fun p f i => ?_⟩
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,e,
    PiLp.continuousLinearEquiv_apply,PiLp.continuousLinearEquiv_symm_apply,WithLp.ofLp_toLp,
    M',ContinuousLinearMap.pi_apply,sum_apply,ContinuousLinearMap.proj_apply]
  rw [lp_dist_sum]
  exact Finset.sum_congr rfl (fun j _ => hLe i j p (f j))

/-- Local inversion for an arbitrary joint smooth compact coefficient family,
not merely scalar multiples of one coefficient. -/
theorem local_variable_inverse {S Ω K : Set ℂ} (hS : IsCompact S) (hΩ : Ω ⊆ S)
    (hK : IsCompact K) (a : n → n → P × ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0) (p₀ : P) :
    ∃ (U : Set P) (T : P → Hilbert n →L[ℂ] Hilbert n),
      IsOpen U ∧ p₀∈U ∧ ContDiffOn ℝ (⊤ : ℕ∞) T U ∧
      ∀ p∈U, ∀ (f : Hilbert n) i,
        LocalEqual Ω (planarOperator (fun i j z => a i j (p,z)) i (T p f)) (f i : 𝓢'(ℂ,ℂ)) := by
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth := by
    have hc : HasCompactSupport (fun z => a i j (p,z)) := by
      apply hK.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ hK.isClosed
      intro z hz
      contrapose! hz
      simpa only [Function.mem_support,not_not] using hs i j p z hz
    exact hc.hasTemperateGrowth ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  obtain ⟨M,hM,hMe⟩ := exists_smooth_matrix_multiplier hK a ha hs
  obtain ⟨T₀,hT₀⟩ := exists_planar_distribution_inverse hS hΩ
    (fun i j z => a i j (p₀,z)) (hat p₀)
  let B : P → Hilbert n →L[ℂ] Hilbert n := fun p => M p-M p₀
  let T : P → Hilbert n →L[ℂ] Hilbert n := fun p => T₀*Ring.inverse (1+B p*T₀)
  let U : Set P := {p | ‖B p*T₀‖<1}
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hM.sub contDiff_const
  have hopen : IsOpen U := isOpen_lt (hB.continuous.mul continuous_const).norm continuous_const
  have hmem : p₀∈U := by simp only [U,B,mem_ofPred_eq,sub_self,zero_mul,norm_zero,zero_lt_one]
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) T U := fun p hp =>
    (ElasticityDualSolvability.smooth_local_weak_inverse T₀ B hB.contDiffAt hp).contDiffWithinAt
  refine ⟨U,T,hopen,hmem,hsmooth,fun p hp f i => ?_⟩
  change ‖B p*T₀‖<1 at hp
  have hu : IsUnit (1+B p*T₀) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one
      (by simpa only [norm_neg] using hp : ‖-(B p*T₀)‖<1)
  let q := Ring.inverse (1+B p*T₀) f
  have htot : q+B p (T₀ q)=f := by
    have h := congrArg (fun L : Hilbert n →L[ℂ] Hilbert n => L f)
      (Ring.mul_inverse_cancel (1+B p*T₀) hu)
    simpa only [mul_apply_eq_comp,add_apply,one_apply_eq_self] using h
  have hprod : ((B p (T₀ q)) i : 𝓢'(ℂ,ℂ))=
      (∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (T₀ q j : 𝓢'(ℂ,ℂ)))-
      (∑ j, smulLeftCLM ℂ (fun z => a i j (p₀,z)) (T₀ q j : 𝓢'(ℂ,ℂ))) := by
    change (((M p (T₀ q)-M p₀ (T₀ q) : Hilbert n)) i : 𝓢'(ℂ,ℂ))=_
    rw [PiLp.sub_apply]
    change (Lp.toTemperedDistributionCLM ℂ volume 2) (_-_) = _
    rw [map_sub]
    exact congrArg₂ (·-·) (hMe p (T₀ q) i) (hMe p₀ (T₀ q) i)
  intro φ hφ hφs
  have he := hT₀ q i φ hφ hφs
  have ht := congrArg (fun v : Hilbert n => (v i : 𝓢'(ℂ,ℂ)) φ) htot
  rw [PiLp.add_apply,lp_dist_add,hprod] at ht
  simp only [planarOperator_apply]
  change (ElasticityPlanarDistribution.dbar (T₀ q i : 𝓢'(ℂ,ℂ))+
    ∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (T₀ q j : 𝓢'(ℂ,ℂ))) φ=_
  simp only [add_apply,sub_apply] at he ht ⊢
  linear_combination he+ht
end ElasticityPlanar

end
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators Manifold
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
/-- A global smooth weak right inverse for actual smooth compactly supported
matrix coefficients over any finite-dimensional real parameter space. -/
theorem global_variable_inverse {S Ω K : Set ℂ} (hS : IsCompact S) (hΩ : Ω ⊆ S)
    (hK : IsCompact K) (a : n → n → P × ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0) :
    ∃ T : P → Hilbert n →L[ℂ] Hilbert n,
      ContDiff ℝ (⊤ : ℕ∞) T ∧ ∀ p, ∀ f : Hilbert n, ∀ i,
      LocalEqual Ω (planarOperator (fun i j z => a i j (p,z)) i (T p f)) (f i : 𝓢'(ℂ,ℂ)) := by
  let Q : P → Set (Hilbert n →L[ℂ] Hilbert n) := fun p => {T | ∀ f i,
    LocalEqual Ω (planarOperator (fun i j z => a i j (p,z)) i (T f)) (f i : 𝓢'(ℂ,ℂ))}
  have hconv : ∀ p, Convex ℝ (Q p) := by
    intro p T₁ hT₁ T₂ hT₂ b c _ _ hbc f i φ hφ hφs
    have h₁ := hT₁ f i φ hφ hφs
    have h₂ := hT₂ f i φ hφ hφs
    change (planarOperator (fun i j z => a i j (p,z)) i
      ((b : ℂ) • (T₁ f)+(c : ℂ) • (T₂ f))) φ=_
    simp only [map_add,map_smul,add_apply,smul_apply,h₁,h₂,smul_eq_mul]
    have hh : (b : ℂ)+(c : ℂ)=1 := by exact_mod_cast hbc
    rw [← add_mul,hh,one_mul]
  have hlocal : ∀ p : P, ∃ U ∈ nhds p, ∃ T : P → Hilbert n →L[ℂ] Hilbert n,
      ContMDiffOn 𝓘(ℝ,P) 𝓘(ℝ,Hilbert n →L[ℂ] Hilbert n) (⊤ : ℕ∞) T U ∧
      ∀ t ∈ U, T t∈Q t := by
    intro p
    obtain ⟨U,T,hU,hp,hT,heq⟩ := local_variable_inverse hS hΩ hK a ha hs p
    exact ⟨U,hU.mem_nhds hp,T,hT.contMDiffOn,heq⟩
  obtain ⟨T,hT⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ,P) hconv hlocal
  exact ⟨T,T.contMDiff.contDiff,hT⟩
end ElasticityPlanar
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual whole-space Laplacian gain has a uniform norm estimate. Its
constant does not depend on any conjugation parameter or on the unknown. -/
theorem quantitative_laplacian_gain (s : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ f g : Lp ℂ 2 (volume : Measure E),
      Δ (sobolevInjection s f)=sobolevInjection (s-1) g →
      ∃ q : Lp ℂ 2 (volume : Measure E),
        sobolevInjection (s+1) q=sobolevInjection s f ∧
        ‖q‖ ≤ C*(‖f‖+‖g‖) := by
  let H := Lp ℂ 2 (volume : Measure E)
  let D : 𝓢'(E,ℂ) →L[ℂ] 𝓢'(E,ℂ) := LineDeriv.laplacianCLM ℂ E _
  let T : H × H →L[ℂ] 𝓢'(E,ℂ) := (sobolevInjection s).comp (ContinuousLinearMap.fst ℂ H H)
  let A : H × H →L[ℂ] 𝓢'(E,ℂ) := D.comp T-
    (sobolevInjection (s-1)).comp (ContinuousLinearMap.snd ℂ H H)
  let G : Submodule ℂ (H × H) := A.ker
  have hclosed : IsClosed (G : Set (H × H)) := A.isClosed_ker
  let : CompleteSpace G := hclosed.completeSpace_coe
  have he (p : G) : Δ (sobolevInjection s p.1.1)=sobolevInjection (s-1) p.1.2 := by
    have hp := p.2
    change A p.1=0 at hp
    apply sub_eq_zero.mp
    simpa only [A,D,T,sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',laplacianCLM_apply] using hp
  obtain ⟨L,hL⟩ := exists_continuous_lift (sobolevInjection (E := E) (s+1))
    (sobolevInjection_injective (s+1)) (T.comp G.subtypeL) (fun p => by
      apply (memSobolev_iff_range (s+1) _).mp
      change MemSobolev (s+1) 2 (sobolevInjection s p.1.1)
      have hΔ : MemSobolev (s-1) 2 (Δ (sobolevInjection s p.1.1)) := by
        rw [he]
        exact sobolevInjection_mem _ _
      have h := laplacian_gain ((sobolevInjection_mem s p.1.1).mono (by linarith : s-1 ≤ s)) hΔ
      rw [show s-1+2=s+1 by ring] at h
      exact h)
  refine ⟨‖L‖+1,by positivity,fun f g hfg => ?_⟩
  have hG : (f,g) ∈ G := by
    change A (f,g)=0
    simpa only [A,D,T,sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',laplacianCLM_apply] using
      (sub_eq_zero.mpr hfg)
  let p : G := ⟨(f,g),hG⟩
  refine ⟨L p,hL p,?_⟩
  have hp : ‖p‖ ≤ ‖f‖+‖g‖ := by
    change max ‖f‖ ‖g‖ ≤ ‖f‖+‖g‖
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  calc
    ‖L p‖ ≤ ‖L‖*‖p‖ := L.le_opNorm p
    _ ≤ (‖L‖+1)*(‖f‖+‖g‖) := by gcongr; linarith


/-- A bounded realization of the actual Laplacian graph gain, extended by
orthogonal projection only off its graph. On the graph it is the unique actual
Sobolev representative. This is used for strong parameter regularity. -/
theorem bounded_laplacian_graph_gain (s : ℝ) :
    ∃ L : (Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E)) →L[ℂ]
        Lp ℂ 2 (volume : Measure E),
      ∀ f g, Δ (sobolevInjection s f)=sobolevInjection (s-1) g →
        sobolevInjection (s+1) (L (f,g))=sobolevInjection s f := by
  let H := Lp ℂ 2 (volume : Measure E)
  let X := WithLp 2 (H × H)
  let e : X ≃L[ℂ] H × H := WithLp.prodContinuousLinearEquiv 2 ℂ H H
  let D : 𝓢'(E,ℂ) →L[ℂ] 𝓢'(E,ℂ) := LineDeriv.laplacianCLM ℂ E _
  let T : X →L[ℂ] 𝓢'(E,ℂ) := (sobolevInjection s).comp
    ((ContinuousLinearMap.fst ℂ H H).comp e.toContinuousLinearMap)
  let A : X →L[ℂ] 𝓢'(E,ℂ) := D.comp T-
    (sobolevInjection (s-1)).comp ((ContinuousLinearMap.snd ℂ H H).comp e.toContinuousLinearMap)
  let G : Submodule ℂ X := A.ker
  have hclosed : IsClosed (G : Set X) := A.isClosed_ker
  let : CompleteSpace G := hclosed.completeSpace_coe
  have he (p : G) : Δ (sobolevInjection s (e p.1).1)=sobolevInjection (s-1) (e p.1).2 := by
    have hp := p.2
    change A p.1=0 at hp
    apply sub_eq_zero.mp
    simpa only [A,D,T,sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',laplacianCLM_apply,
      ContinuousLinearEquiv.coe_coe] using hp
  obtain ⟨L,hL⟩ := exists_continuous_lift (sobolevInjection (E := E) (s+1))
    (sobolevInjection_injective (s+1)) (T.comp G.subtypeL) (fun p => by
      apply (memSobolev_iff_range (s+1) _).mp
      change MemSobolev (s+1) 2 (sobolevInjection s (e p.1).1)
      have hΔ : MemSobolev (s-1) 2 (Δ (sobolevInjection s (e p.1).1)) := by
        rw [he]
        exact sobolevInjection_mem _ _
      have h := laplacian_gain ((sobolevInjection_mem s (e p.1).1).mono (by linarith : s-1 ≤ s)) hΔ
      rw [show s-1+2=s+1 by ring] at h
      exact h)
  refine ⟨(L.comp G.orthogonalProjectionOnto).comp e.symm.toContinuousLinearMap,fun f g hfg => ?_⟩
  have hG : e.symm (f,g) ∈ G := by
    change A (e.symm (f,g))=0
    simpa only [A,D,T,sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',laplacianCLM_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using
      (sub_eq_zero.mpr hfg)
  let p : G := ⟨e.symm (f,g),hG⟩
  have hp : G.orthogonalProjectionOnto (e.symm (f,g))=p :=
    G.orthogonalProjectionOnto_mem_subspace_eq_self p
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,hp,hL]
  change sobolevInjection s (e p.1).1=sobolevInjection s f
  simp only [p,ContinuousLinearEquiv.apply_symm_apply]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem smooth_laplacian_gain (s : ℝ)
    (f g : P → Lp ℂ 2 (volume : Measure E))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (heq : ∀ p, Δ (sobolevInjection s (f p))=sobolevInjection (s-1) (g p)) :
    ∃ q : P → Lp ℂ 2 (volume : Measure E), ContDiff ℝ (⊤ : ℕ∞) q ∧
      ∀ p, sobolevInjection (s+1) (q p)=sobolevInjection s (f p) := by
  obtain ⟨L,hL⟩ := bounded_laplacian_graph_gain (E := E) s
  exact ⟨fun p => L (f p,g p),(L.restrictScalars ℝ).contDiff.comp (hf.prodMk hg),
    fun p => hL (f p) (g p) (heq p)⟩
end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Smooth dependence in the genuine Hilbert Sobolev topology, with the
representative tied to the given distribution family. -/
def SmoothSobolev (s : ℝ) (u : P → 𝓢'(E,ℂ)) : Prop :=
  ∃ f : P → Lp ℂ 2 (volume : Measure E), ContDiff ℝ (⊤ : ℕ∞) f ∧
    ∀ p, sobolevInjection s (f p)=u p

def SmoothLocalSobolev (Ω : Set E) (s : ℝ) (u : P → 𝓢'(E,ℂ)) : Prop :=
  ∀ g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ Ω →
    SmoothSobolev s (fun p => smulLeftCLM ℂ g (u p))

namespace SmoothSobolev
variable {s t : ℝ} {u v : P → 𝓢'(E,ℂ)}
lemma add (hu : SmoothSobolev s u) (hv : SmoothSobolev s v) :
    SmoothSobolev s (fun p => u p+v p) := by
  obtain ⟨f,hf,he⟩ := hu
  obtain ⟨g,hg,hg'⟩ := hv
  exact ⟨fun p => f p+g p,hf.add hg,fun p => by rw [map_add,he,hg']⟩
lemma sub (hu : SmoothSobolev s u) (hv : SmoothSobolev s v) :
    SmoothSobolev s (fun p => u p-v p) := by
  obtain ⟨f,hf,he⟩ := hu
  obtain ⟨g,hg,hg'⟩ := hv
  exact ⟨fun p => f p-g p,hf.sub hg,fun p => by rw [map_sub,he,hg']⟩
lemma smul (hu : SmoothSobolev s u) (c : P → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    SmoothSobolev s (fun p => c p • u p) := by
  obtain ⟨f,hf,he⟩ := hu
  exact ⟨fun p => c p • f p,hc.smul hf,fun p => by rw [map_smul,he]⟩
lemma zero : SmoothSobolev s (fun _ : P => (0 : 𝓢'(E,ℂ))) :=
  ⟨fun _ => 0,contDiff_const,fun _ => map_zero _⟩
lemma sum {ι : Type*} (S : Finset ι) (u : ι → P → 𝓢'(E,ℂ))
    (hu : ∀ i ∈ S, SmoothSobolev s (u i)) :
    SmoothSobolev s (fun p => ∑ i ∈ S, u i p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (zero (s := s) (P := P) (E := E))
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hu i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))
lemma mono (hu : SmoothSobolev s u) (hst : t ≤ s) : SmoothSobolev t u := by
  obtain ⟨L,hL⟩ := exists_bounded_sobolev_inclusion (E := E) hst
  obtain ⟨f,hf,he⟩ := hu
  exact ⟨fun p => L (f p),(L.restrictScalars ℝ).contDiff.comp hf,fun p => (hL _).trans (he p)⟩
lemma derivative (hu : SmoothSobolev s u) (a : E) :
    SmoothSobolev (s-1) (fun p => ∂_{a} (u p)) := by
  obtain ⟨L,hL⟩ := exists_bounded_sobolev_derivative (E := E) s a
  obtain ⟨f,hf,he⟩ := hu
  exact ⟨fun p => L (f p),(L.restrictScalars ℝ).contDiff.comp hf,fun p => by rw [hL,he]⟩
lemma laplacian_gain (hu : SmoothSobolev s u)
    (hΔ : SmoothSobolev (s-1) (fun p => Δ (u p))) : SmoothSobolev (s+1) u := by
  obtain ⟨f,hf,he⟩ := hu
  obtain ⟨g,hg,hg'⟩ := hΔ
  obtain ⟨q,hq,hq'⟩ := smooth_laplacian_gain s f g hf hg (fun p => by rw [he,hg'])
  exact ⟨q,hq,fun p => (hq' p).trans (he p)⟩
end SmoothSobolev

namespace SmoothLocalSobolev
variable {Ω : Set E} {s t : ℝ} {u v : P → 𝓢'(E,ℂ)}
lemma add (hu : SmoothLocalSobolev Ω s u) (hv : SmoothLocalSobolev Ω s v) :
    SmoothLocalSobolev Ω s (fun p => u p+v p) := by
  intro g hg hc hs
  simpa only [map_add] using (hu g hg hc hs).add (hv g hg hc hs)
lemma sub (hu : SmoothLocalSobolev Ω s u) (hv : SmoothLocalSobolev Ω s v) :
    SmoothLocalSobolev Ω s (fun p => u p-v p) := by
  intro g hg hc hs
  simpa only [map_sub] using (hu g hg hc hs).sub (hv g hg hc hs)
lemma smul (hu : SmoothLocalSobolev Ω s u) (c : P → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    SmoothLocalSobolev Ω s (fun p => c p • u p) := by
  intro g hg hcg hs
  simpa only [map_smul] using (hu g hg hcg hs).smul c hc
lemma sum {ι : Type*} (S : Finset ι) (u : ι → P → 𝓢'(E,ℂ))
    (hu : ∀ i ∈ S, SmoothLocalSobolev Ω s (u i)) :
    SmoothLocalSobolev Ω s (fun p => ∑ i ∈ S, u i p) := by
  intro g hg hc hs
  simpa only [map_sum] using SmoothSobolev.sum S
    (fun i p => smulLeftCLM ℂ g (u i p)) (fun i hi => hu i hi g hg hc hs)
lemma mono (hu : SmoothLocalSobolev Ω s u) (hst : t ≤ s) : SmoothLocalSobolev Ω t u :=
  fun g hg hc hs => (hu g hg hc hs).mono hst
lemma coeff (hu : SmoothLocalSobolev Ω s u) {a : E → ℂ} (ha : a.HasTemperateGrowth) :
    SmoothLocalSobolev Ω s (fun p => smulLeftCLM ℂ a (u p)) := by
  intro g hg hc hs
  simp only [smulLeftCLM_smulLeftCLM_apply ha (hc.hasTemperateGrowth hg),mul_comm a g]
  exact hu (g*a) (hg.mul ha.1) hc.mul_right (tsupport_mul_subset_left.trans hs)
lemma product_derivative (hu : SmoothLocalSobolev Ω s u) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (a : E) :
    SmoothSobolev (s-1) (fun p => smulLeftCLM ℂ g (∂_{a} (u p))) := by
  have hd := smooth_derivative hg a
  have hdc := compact_derivative hc a
  have hds := (derivative_support_subset g a).trans hs
  have h := ((hu g hg hc hs).derivative a).sub
    ((hu _ hd hdc hds).mono (by linarith : s-1 ≤ s))
  simpa only [distribution_leibniz (hc.hasTemperateGrowth hg) a (hdc.hasTemperateGrowth hd),
    add_sub_cancel_left] using h
lemma derivative (hu : SmoothLocalSobolev Ω s u) (a : E) :
    SmoothLocalSobolev Ω (s-1) (fun p => ∂_{a} (u p)) :=
  fun _ hg hc hs => hu.product_derivative hg hc hs a
lemma congr (hu : SmoothLocalSobolev Ω s u) (he : ∀ p, LocalEqual Ω (v p) (u p)) :
    SmoothLocalSobolev Ω s v := by
  intro g hg hc hs
  have h : (fun p => smulLeftCLM ℂ g (v p))=(fun p => smulLeftCLM ℂ g (u p)) :=
    funext (fun p => (he p).cutoff hg hc hs)
  rw [h]
  exact hu g hg hc hs

/-- Strong smooth parameter regularity is gained for the actual distribution
family; the proof uses fixed bounded Laplacian graph operators. -/
lemma laplacian_gain (hu : SmoothLocalSobolev Ω s u)
    (hΔ : SmoothLocalSobolev Ω (s-1) (fun p => Δ (u p))) :
    SmoothLocalSobolev Ω (s+1) u := by
  let b := stdOrthonormalBasis ℝ E
  intro g hg hc hs
  have hbase := hu g hg hc hs
  apply SmoothSobolev.laplacian_gain hbase
  simp only [laplacian_product b hg hc]
  apply (hΔ g hg hc hs).add
  apply SmoothSobolev.sum Finset.univ
  intro i _
  have hgd := smooth_derivative hg (b i)
  have hcd := compact_derivative hc (b i)
  have hsd := (derivative_support_subset g (b i)).trans hs
  exact ((hu _ (smooth_derivative hgd (b i)) (compact_derivative hcd (b i))
    ((derivative_support_subset _ (b i)).trans hsd)).mono (by linarith)).add
    ((hu.product_derivative hgd hcd hsd (b i)).smul (fun _ => 2) contDiff_const)
end SmoothLocalSobolev
end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
lemma smooth_spatial_derivative {a : P × E → ℂ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => fderiv ℝ (fun x => a (q.1,x)) q.2 v) := by
  have he : (fun q : P × E => fderiv ℝ (fun x => a (q.1,x)) q.2 v)=
      (fun q : P × E => fderiv ℝ a q (0,v)) := by
    funext q
    have hg : HasFDerivAt (fun x : E => (q.1,x)) (ContinuousLinearMap.inr ℝ P E) q.2 :=
      (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
    have hh := (ha.differentiable (by simp) (q.1,q.2)).hasFDerivAt.comp q.2 hg
    change fderiv ℝ (a ∘ Prod.mk q.1) q.2 v=_
    rw [hh.fderiv]
    rfl
  rw [he]
  exact (ha.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
omit [InnerProductSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma compact_slice {S : Set E} (hS : IsCompact S) (a : P × E → ℂ)
    (hs : ∀ p x, x∉S → a (p,x)=0) (p : P) : HasCompactSupport (fun x => a (p,x)) := by
  apply hS.of_isClosed_subset (isClosed_tsupport _)
  exact closure_minimal (fun x hx => by contrapose! hx; simpa only [Function.mem_support,not_not] using hs p x hx) hS.isClosed

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma spatial_derivative_outside {S : Set E} (hS : IsClosed S) (a : P × E → ℂ)
    (hs : ∀ p x, x∉S → a (p,x)=0) (v : E) :
    ∀ p x, x∉S → fderiv ℝ (fun y => a (p,y)) x v=0 := by
  intro p x hx
  apply image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ (fun z => a (p,z)) y v)
  intro hh
  have ht : tsupport (fun y => a (p,y)) ⊆ S :=
    closure_minimal (fun y hy => by contrapose! hy; simpa only [Function.mem_support,not_not] using hs p y hy) hS
  exact hx (ht (derivative_support_subset (fun y => a (p,y)) v hh))

omit [FiniteDimensional ℝ P] in
lemma SmoothSobolev.coordinate_gain {s : ℝ} {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothSobolev s u)
    (hd : ∀ v : E, SmoothSobolev s (fun p => ∂_{v} (u p))) :
    SmoothSobolev (s+1) u := by
  apply hu.laplacian_gain
  let b := stdOrthonormalBasis ℝ E
  have h := SmoothSobolev.sum Finset.univ (fun i p => ∂_{b i} (∂_{b i} (u p)))
    (fun i _ => (hd (b i)).derivative (b i))
  simpa only [laplacian_eq_sum b] using h

lemma SmoothSobolev.variable_zero {S : Set E} (hS : IsCompact S)
    (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉S → a (p,x)=0) {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothSobolev 0 u) :
    SmoothSobolev 0 (fun p => smulLeftCLM ℂ (fun x => a (p,x)) (u p)) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨b,hb,hbe⟩ := ElasticityCompact.exists_smooth_linf_family hS.measurableSet
    (volume : Measure E) a ha hs
  obtain ⟨v,hv,he⟩ := hu
  simp only [sobolevInjection,neg_zero,besselPotential_zero,ContinuousLinearMap.id_comp,
    Lp.toTemperedDistributionCLM_apply] at he
  let B := (ContinuousLinearMap.mul ℝ ℂ).holderL (volume : Measure E) ∞ 2 2
  refine ⟨fun p => B (b p) (v p),(B.contDiff.comp hb).clm_apply hv,fun p => ?_⟩
  simp only [sobolevInjection,neg_zero,besselPotential_zero,ContinuousLinearMap.id_comp,
    Lp.toTemperedDistributionCLM_apply]
  have ha' : ContDiff ℝ (⊤ : ℕ∞) (fun x => a (p,x)) :=
    ha.comp (contDiff_const.prodMk contDiff_id)
  have hc := compact_slice hS a hs p
  have hm := compact_bounded_multiplier ha' hc
  have hprod : B (b p) (v p)=(hm.toLp (fun x => a (p,x))) • v p := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.mul ℝ ℂ).coeFn_holder (r := 2) (b p) (v p),
      Lp.coeFn_lpSMul (r := 2) (hm.toLp _) (v p),hm.coeFn_toLp,hbe p] with x h₁ h₂ h₃ h₄
    change ((ContinuousLinearMap.mul ℝ ℂ).holder 2 (b p) (v p)) x=_
    rw [h₁,h₂]
    simp only [Pi.smul_apply',h₃,h₄]
    rfl
  rw [hprod,Lp.toTemperedDistribution_smul_eq (hc.hasTemperateGrowth ha') hm,he]

/-- Joint smooth coefficient multiplication in the strong Hilbert Sobolev
parameter topology, for each actual nonnegative integral order. -/
theorem SmoothSobolev.variable_nat {S : Set E} (hS : IsCompact S)
    (N : ℕ) (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉S → a (p,x)=0) {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothSobolev N u) :
    SmoothSobolev N (fun p => smulLeftCLM ℂ (fun x => a (p,x)) (u p)) := by
  induction N generalizing a u with
  | zero =>
    rw [Nat.cast_zero] at hu ⊢
    exact SmoothSobolev.variable_zero hS a ha hs hu
  | succ N ih =>
    rw [Nat.cast_add,Nat.cast_one] at hu ⊢
    have hu' := hu.mono (by norm_num : (N : ℝ) ≤ N+1)
    apply (ih a ha hs hu').coordinate_gain
    intro v
    have hd : SmoothSobolev (N : ℝ) (fun p => ∂_{v} (u p)) := by
      simpa only [add_sub_cancel_right] using hu.derivative v
    have hsum := (ih _ (smooth_spatial_derivative ha v)
      (spatial_derivative_outside hS.isClosed a hs v) hu').add (ih a ha hs hd)
    convert hsum using 1
    funext p
    have ha' : ContDiff ℝ (⊤ : ℕ∞) (fun x => a (p,x)) :=
      ha.comp (contDiff_const.prodMk contDiff_id)
    have hc := compact_slice hS a hs p
    exact distribution_leibniz (hc.hasTemperateGrowth ha') v
      ((compact_derivative hc v).hasTemperateGrowth (smooth_derivative ha' v)) (u p)
end ElasticityRegularity
namespace ElasticityPlanarDistribution
open MeasureTheory TemperedDistribution Complex
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityRegularity
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {n : Type*} [Fintype n]
lemma SmoothLocalSobolev.dhol {Ω : Set ℂ} {s : ℝ} {u : P → Dist}
    (h : ElasticityRegularity.SmoothLocalSobolev Ω s u) :
    ElasticityRegularity.SmoothLocalSobolev Ω (s-1) (fun p => dhol (u p)) :=
  (h.derivative 1).sub ((h.derivative I).smul (fun _ => I) contDiff_const)

/-- Actual smooth parameter-dependent elliptic gain for the planar system. -/
theorem smooth_local_gain {Ω : Set ℂ} {s : ℝ}
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (c : P → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (u f : P → n → Dist)
    (heq : ∀ p i, LocalEqual Ω (dbar (u p i))
      (f p i+c p • ∑ j, smulLeftCLM ℂ (a i j) (u p j)))
    (hu : ∀ i, ElasticityRegularity.SmoothLocalSobolev Ω s (fun p => u p i))
    (hf : ∀ i, ElasticityRegularity.SmoothLocalSobolev Ω s (fun p => f p i)) :
    ∀ i, ElasticityRegularity.SmoothLocalSobolev Ω (s+1) (fun p => u p i) := by
  intro i
  apply (hu i).laplacian_gain
  have H := SmoothLocalSobolev.dhol ((hf i).add
    ((ElasticityRegularity.SmoothLocalSobolev.sum Finset.univ
      (fun j p => smulLeftCLM ℂ (a i j) (u p j))
      (fun j _ => (hu j).coeff (ha i j))).smul c hc))
  apply H.congr
  intro p
  simpa only [dhol_dbar] using LocalEqual.dhol (heq p i)

theorem smooth_local_all_orders {Ω : Set ℂ}
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (c : P → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (u f : P → n → Dist)
    (heq : ∀ p i, LocalEqual Ω (dbar (u p i))
      (f p i+c p • ∑ j, smulLeftCLM ℂ (a i j) (u p j)))
    (hu : ∀ i, ElasticityRegularity.SmoothLocalSobolev Ω 0 (fun p => u p i))
    (hf : ∀ N : ℕ, ∀ i, ElasticityRegularity.SmoothLocalSobolev Ω N (fun p => f p i)) :
    ∀ N : ℕ, ∀ i, ElasticityRegularity.SmoothLocalSobolev Ω N (fun p => u p i) := by
  intro N
  induction N with
  | zero => simpa only [Nat.cast_zero] using hu
  | succ N hN =>
    rw [Nat.cast_add,Nat.cast_one]
    exact smooth_local_gain a ha c hc u f heq hN (hf N)
end ElasticityPlanarDistribution
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The continuous Sobolev embedding is a genuinely bounded operator, obtained
from the actual Fourier representative and the closed graph theorem. -/
theorem exists_bounded_continuous_embedding {s : ℝ} (hs : Module.finrank ℝ E < 2*s) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] BoundedContinuousFunction E ℂ,
      ∀ f, sobolevInjection s f=
        (((L f).memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E,ℂ)) := by
  let J := Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 1
  have hJ : Function.Injective J :=
    LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
  obtain ⟨T,hT⟩ := exists_continuous_lift J hJ
    ((fourierCLM ℂ 𝓢'(E,ℂ)).comp (sobolevInjection s)) (fun f => by
      obtain ⟨v,hv⟩ := (sobolevInjection_mem s f).fourier_memL1 hs
      exact ⟨v,hv.symm⟩)
  let R : Lp ℂ 1 (volume : Measure E) →L[ℂ] BoundedContinuousFunction E ℂ :=
    (BoundedContinuousFunction.compContinuousCLM ℂ ℂ (-ContinuousMap.id E)).comp
      (Real.Lp.fourierTransformCLM E ℂ)
  refine ⟨R.comp T,fun f => ?_⟩
  change sobolevInjection s f=
    (((Real.Lp.fourierTransformInv (T f)).memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E,ℂ))
  rw [l1_inverse_fourier_distribution]
  have h := hT f
  change (T f : 𝓢'(E,ℂ))=𝓕 (sobolevInjection s f) at h
  rw [h,fourierInv_fourier_eq]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
lemma SmoothSobolev.continuous_representative {s : ℝ} {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothSobolev s u) (hs : Module.finrank ℝ E < 2*s) :
    ∃ g : P → BoundedContinuousFunction E ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      ∀ p, u p=(((g p).memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E,ℂ)) := by
  obtain ⟨f,hf,he⟩ := hu
  obtain ⟨L,hL⟩ := exists_bounded_continuous_embedding hs
  exact ⟨fun p => L (f p),(L.restrictScalars ℝ).contDiff.comp hf,fun p => (he p).symm.trans (hL _)⟩

lemma SmoothSobolev.joint_continuous_representative {s : ℝ} {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothSobolev s u) (hs : Module.finrank ℝ E < 2*s) :
    ∃ g : P → BoundedContinuousFunction E ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ Continuous (fun q : P × E => g q.1 q.2) ∧
      ∀ p, u p=(((g p).memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E,ℂ)) := by
  obtain ⟨g,hg,he⟩ := hu.continuous_representative hs
  exact ⟨g,hg,(hg.continuous.comp continuous_fst).eval continuous_snd,he⟩
end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
def bcfToLinfty : BoundedContinuousFunction E ℂ →L[ℂ] Lp ℂ ∞ (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := fun g => g.memLp_top.toLp _
      map_add' := fun f g => by exact f.memLp_top.toLp_add g.memLp_top
      map_smul' := fun c f => by exact f.memLp_top.toLp_const_smul c } 1 (fun g => by
        change ‖(g.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E))‖ ≤ 1*‖g‖
        rw [one_mul,Lp.norm_toLp,eLpNorm_exponent_top g.memLp_top.aestronglyMeasurable]
        exact (ENNReal.toReal_mono (by simp)
          (eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall g.norm_coe_le_norm))).trans_eq
            (ENNReal.toReal_ofReal (norm_nonneg g)))
def bcfToDist : BoundedContinuousFunction E ℂ →L[ℂ] 𝓢'(E,ℂ) :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) ∞).comp bcfToLinfty
lemma bcfToDist_apply (g : BoundedContinuousFunction E ℂ) :
    bcfToDist g=(((g.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E))) : 𝓢'(E,ℂ)) := rfl
lemma bcfToDist_injective : Function.Injective (bcfToDist (E := E)) := by
  intro f g h
  have hh : (f.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E))=g.memLp_top.toLp _ :=
    LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)) h
  have ha : (f : E → ℂ)=ᵐ[volume] (g : E → ℂ) :=
    f.memLp_top.coeFn_toLp.symm.trans (hh ▸ g.memLp_top.coeFn_toLp)
  exact DFunLike.coe_injective ((f.continuous.ae_eq_iff_eq volume g.continuous).mp ha)
lemma bcf_smooth_of_all_orders (g : BoundedContinuousFunction E ℂ)
    (hg : ∀ n : ℕ, MemSobolev n 2 (bcfToDist g)) :
    ContDiff ℝ (⊤ : ℕ∞) (g : E → ℂ) := by
  obtain ⟨h,hh,he⟩ := all_orders_smooth_representative hg
  have : g=h := bcfToDist_injective he
  rwa [this]

/-- Distributional and classical derivatives agree for the actual bounded smooth
representatives. A compact smooth multiplier makes every term Schwartz. -/
lemma bcf_derivative (g h : BoundedContinuousFunction E ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) (g : E → ℂ))
    (hh : ContDiff ℝ (⊤ : ℕ∞) (h : E → ℂ)) (a x : E)
    (he : ∂_{a} (bcfToDist g)=bcfToDist h) :
    fderiv ℝ (g : E → ℂ) x a=h x := by
  obtain ⟨q,_,hc,hq,_,h1⟩ := exists_contDiff_tsupport_subset (x := x) (n := (⊤ : ℕ∞))
    (s := Set.univ) Filter.univ_mem
  let c : E → ℂ := fun y => (q y : ℂ)
  have hcg : ContDiff ℝ (⊤ : ℕ∞) c := Complex.ofRealCLM.contDiff.comp hq
  have hcc : HasCompactSupport c := hc.comp_left Complex.ofReal_zero
  have hdg := smooth_derivative hcg a
  have hdc := compact_derivative hcc a
  let cg : 𝓢(E,ℂ) := (hcc.mul_right : HasCompactSupport (c*(g : E → ℂ))).toSchwartzMap (hcg.mul hg)
  let ch : 𝓢(E,ℂ) := (hcc.mul_right : HasCompactSupport (c*(h : E → ℂ))).toSchwartzMap (hcg.mul hh)
  let cdg : 𝓢(E,ℂ) := (hdc.mul_right : HasCompactSupport ((fun y => fderiv ℝ c y a)*(g : E → ℂ))).toSchwartzMap (hdg.mul hg)
  have hd := distribution_leibniz (hcc.hasTemperateGrowth hcg) a
    (hdc.hasTemperateGrowth hdg) (bcfToDist g)
  rw [he,bcfToDist_apply,bcfToDist_apply,smooth_Linfty_product hcg hcc g hg,
    smooth_Linfty_product hcg hcc h hh,smooth_Linfty_product hdg hdc g hg] at hd
  have hdist : ((∂_{a} cg : 𝓢(E,ℂ)) : 𝓢'(E,ℂ))=((cdg+ch : 𝓢(E,ℂ)) : 𝓢'(E,ℂ)) := by
    simpa only [← lineDerivOp_toTemperedDistributionCLM_eq,map_add] using hd
  have hv := congrArg (fun f : 𝓢(E,ℂ) => f x) (schwartz_dist_injective hdist)
  change fderiv ℝ (c*(g : E → ℂ)) x a=fderiv ℝ c x a*g x+c x*h x at hv
  rw [fderiv_mul (hcg.differentiable (by simp) x) (hg.differentiable (by simp) x)] at hv
  have hx : c x=1 := by simp only [c,h1,Complex.ofReal_one]
  simp only [add_apply,smul_apply,smul_eq_mul,hx,one_mul] at hv
  linear_combination hv
end ElasticityRegularity
namespace ElasticityRegularity

section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma bcf_family_spatial_smooth (g : P → BoundedContinuousFunction E ℂ)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) (p : P) :
    ContDiff ℝ (⊤ : ℕ∞) (g p : E → ℂ) := by
  apply bcf_smooth_of_all_orders
  intro n
  obtain ⟨f,_,he⟩ := hu n
  dsimp only at he
  rw [← he p]
  exact sobolevInjection_mem _ _

lemma bcf_parameter_derivative (g : P → BoundedContinuousFunction E ℂ)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) (a : P) :
    ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (fderiv ℝ g p a)) := by
  intro n
  let t : ℕ := n+Module.finrank ℝ E+1
  have ht : Module.finrank ℝ E < 2*(t : ℝ) := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)]
  obtain ⟨f,hf,he⟩ := hu t
  obtain ⟨T,hT⟩ := exists_bounded_continuous_embedding ht
  have hge : g=fun p => T (f p) := by
    funext p
    apply bcfToDist_injective
    exact (he p).symm.trans (hT _)
  have hd (p : P) : fderiv ℝ g p a=T (fderiv ℝ f p a) := by
    have h := (T.restrictScalars ℝ).hasFDerivAt.comp p (hf.differentiable (by simp) p).hasFDerivAt
    change HasFDerivAt (fun p => T (f p)) _ p at h
    rw [← hge] at h
    exact congrArg (fun L : P →L[ℝ] BoundedContinuousFunction E ℂ => L a) h.fderiv
  have h : SmoothSobolev (t : ℝ) (fun p => bcfToDist (fderiv ℝ g p a)) := by
    refine ⟨fun p => fderiv ℝ f p a,?_,fun p => ?_⟩
    · exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
    · dsimp only
      rw [hd]
      exact hT _
  exact h.mono (by dsimp [t]; norm_cast; omega)

/-- Actual spatial derivatives have smoothly parameter-dependent bounded
representatives in every Sobolev order. -/
lemma bcf_spatial_derivative (g : P → BoundedContinuousFunction E ℂ)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) (a : E) :
    ∃ h : P → BoundedContinuousFunction E ℂ,
      ContDiff ℝ (⊤ : ℕ∞) h ∧
      (∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (h p))) ∧
      ∀ p x, fderiv ℝ (g p : E → ℂ) x a=h p x := by
  have hd (n : ℕ) : SmoothSobolev n (fun p => ∂_{a} (bcfToDist (g p))) := by
    have h := (hu (n+1)).derivative a
    convert h using 1; push_cast; ring
  let t : ℕ := Module.finrank ℝ E+1
  obtain ⟨h,hh,he⟩ := (hd t).continuous_representative (by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)])
  change ∀ p, ∂_{a} (bcfToDist (g p))=bcfToDist (h p) at he
  have hs (n : ℕ) : SmoothSobolev n (fun p => bcfToDist (h p)) := by
    simpa only [he] using hd n
  refine ⟨h,hh,hs,fun p x => ?_⟩
  exact bcf_derivative (g p) (h p) (bcf_family_spatial_smooth g hu p)
    (bcf_family_spatial_smooth h hs p) a x (he p)
end
open MeasureTheory TemperedDistribution Filter Topology
open scoped SchwartzMap ENNReal LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma bcf_joint_hasFDerivAt (g : P → BoundedContinuousFunction E ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) (q : P × E) :
    HasFDerivAt (fun q : P × E => g q.1 q.2)
      (((BoundedContinuousFunction.evalCLM ℝ q.2).comp (fderiv ℝ g q.1)).coprod
        (fderiv ℝ (g q.1 : E → ℂ) q.2)) q := by
  let A : P → E → P →L[ℝ] ℂ := fun p x =>
    (BoundedContinuousFunction.evalCLM ℝ x).comp (fderiv ℝ g p)
  let B : P → E → E →L[ℝ] ℂ := fun p x => fderiv ℝ (g p : E → ℂ) x
  have hA : Continuous (fun q : P × E => A q.1 q.2) := by
    apply continuous_clm_apply.mpr
    intro a
    have ht : ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ g p a) :=
      (hg.fderiv_right (by simp)).clm_apply contDiff_const
    exact (ht.continuous.comp continuous_fst).eval continuous_snd
  have hB : Continuous (fun q : P × E => B q.1 q.2) := by
    apply continuous_clm_apply.mpr
    intro a
    obtain ⟨h,hh,_,he⟩ := bcf_spatial_derivative g hu a
    change Continuous (fun q : P × E => fderiv ℝ (g q.1 : E → ℂ) q.2 a)
    simp only [he]
    exact (hh.continuous.comp continuous_fst).eval continuous_snd
  apply (hasStrictFDerivAt_uncurry_coprod (f := fun p x => g p x)
    (f₁ := A) (f₂ := B) ?_ ?_ hA.continuousAt hB.continuousAt).hasFDerivAt
  · apply Filter.Eventually.of_forall
    intro v
    exact (BoundedContinuousFunction.evalCLM ℝ v.2).hasFDerivAt.comp v.1
      (hg.differentiable (by simp) v.1).hasFDerivAt
  · apply Filter.Eventually.of_forall
    intro v
    exact ((bcf_family_spatial_smooth g hu v.1).differentiable (by simp) v.2).hasFDerivAt

/-- Strong smoothness in every Sobolev order yields actual joint smoothness,
including mixed parameter and spatial derivatives. -/
theorem bcf_joint_smooth (g : P → BoundedContinuousFunction E ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => g q.1 q.2) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing g with
  | zero =>
    simp only [Nat.cast_zero,contDiff_zero]
    exact (hg.continuous.comp continuous_fst).eval continuous_snd
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv_apply]
    refine ⟨fun q => (bcf_joint_hasFDerivAt g hg hu q).differentiableAt,by simp,fun a => ?_⟩
    have hp : ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ g p a.1) :=
      (hg.fderiv_right (by simp)).clm_apply contDiff_const
    have hpu := bcf_parameter_derivative g hu a.1
    obtain ⟨h,hh,hs,he⟩ := bcf_spatial_derivative g hu a.2
    have hp' := ih (fun p => fderiv ℝ g p a.1) hp hpu
    have hs' := ih h hh hs
    have hf (q : P × E) :
        fderiv ℝ (fun q : P × E => g q.1 q.2) q a=
          (fderiv ℝ g q.1 a.1) q.2+h q.1 q.2 := by
      rw [(bcf_joint_hasFDerivAt g hg hu q).fderiv]
      change (fderiv ℝ g q.1 a.1) q.2+fderiv ℝ (g q.1 : E → ℂ) q.2 a.2=_
      rw [he]
    simp only [hf]
    exact hp'.add hs'

theorem SmoothSobolev.joint_smooth_representative {u : P → 𝓢'(E,ℂ)}
    (hu : ∀ n : ℕ, SmoothSobolev n u) :
    ∃ g : P → BoundedContinuousFunction E ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => g q.1 q.2) ∧
      ∀ p, u p=bcfToDist (g p) := by
  let t : ℕ := Module.finrank ℝ E+1
  obtain ⟨g,hg,he⟩ := (hu t).continuous_representative
    (by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)])
  change ∀ p, u p=bcfToDist (g p) at he
  have hs (n : ℕ) : SmoothSobolev n (fun p => bcfToDist (g p)) := by
    rw [← show u=(fun p => bcfToDist (g p)) from funext he]
    exact hu n
  exact ⟨g,hg,bcf_joint_smooth g hg hs,he⟩
end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Joint smoothness on an arbitrary smaller fixed open set. The representative
is an actual Schwartz function in space for every parameter. -/
theorem SmoothLocalSobolev.joint_schwartz_representative {Ω Ω' : Set E}
    (u : P → 𝓢'(E,ℂ)) (hu : ∀ N : ℕ, SmoothLocalSobolev Ω N u)
    {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ f : P → 𝓢(E,ℂ), ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => f q.1 q.2) ∧
      ∀ p, LocalEqual Ω' (u p) (f p : 𝓢'(E,ℂ)) := by
  obtain ⟨v,_,hv,he⟩ := SmoothSobolev.joint_smooth_representative
    (fun N => hu N g hg hc hs)
  have hvs (p : P) : ContDiff ℝ (⊤ : ℕ∞) (v p : E → ℂ) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  let f : P → 𝓢(E,ℂ) := fun p =>
    (hc.mul_right : HasCompactSupport (g*(v p : E → ℂ))).toSchwartzMap (hg.mul (hvs p))
  refine ⟨f,?_,fun p => ?_⟩
  · change ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => g q.2*v q.1 q.2)
    exact (hg.comp contDiff_snd).mul hv
  · have he' := smooth_Linfty_product hg hc (v p) (hvs p)
    have hl := (LocalEqual.cutoff_one (u p) (hc.hasTemperateGrowth hg) h1).symm
    have hl' := (LocalEqual.cutoff_one (smulLeftCLM ℂ g (u p)) (hc.hasTemperateGrowth hg) h1).symm
    have h := hl.trans hl'
    rw [he p] at h
    exact h.trans (by intro φ _ _; exact congrArg (fun T : 𝓢'(E,ℂ) => T φ) he')
end ElasticityRegularity
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Complex
open scoped SchwartzMap ENNReal LineDeriv BigOperators
variable {n : Type*} [Fintype n]
open ElasticityRegularity

def schwartzDbar (v : 𝓢(ℂ,ℂ)) : 𝓢(ℂ,ℂ) := ∂_{(1 : ℂ)} v+I • ∂_{I} v
lemma dbar_schwartz (v : 𝓢(ℂ,ℂ)) :
    ElasticityPlanarDistribution.dbar (v : 𝓢'(ℂ,ℂ))=(schwartzDbar v : 𝓢'(ℂ,ℂ)) := by
  simp only [ElasticityPlanarDistribution.dbar,schwartzDbar,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]
  rw [map_add,map_smul]
lemma LocalEqual.dbar {Ω : Set ℂ} {u v : 𝓢'(ℂ,ℂ)} (h : LocalEqual Ω u v) :
    LocalEqual Ω (ElasticityPlanarDistribution.dbar u) (ElasticityPlanarDistribution.dbar v) :=
  (h.derivative 1).add ((h.derivative I).smul I)

lemma LocalEqual.coeff {Ω : Set ℂ} {u v : 𝓢'(ℂ,ℂ)} (h : LocalEqual Ω u v)
    {a : ℂ → ℂ} (ha : a.HasTemperateGrowth) :
    LocalEqual Ω (smulLeftCLM ℂ a u) (smulLeftCLM ℂ a v) := by
  intro φ hc hs
  change u (SchwartzMap.smulLeftCLM ℂ a φ)=v (SchwartzMap.smulLeftCLM ℂ a φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply ha,Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_left : HasCompactSupport (a*(φ : ℂ → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply ha,Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_right (f := a) (g := (φ : ℂ → ℂ))).trans hs

/-- The actual matrix Cauchy--Riemann equation is solvable smoothly on every
smaller open set. The unknown is produced by the supported estimate and Hilbert
space duality, and the smooth solution is the same L2 solution almost everywhere.
No pre-existing local or global frame is used. -/
theorem exists_planar_classical_solution {S Ω Ω' : Set ℂ} (hS : IsCompact S)
    (hΩS : Ω ⊆ S) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (f : n → 𝓢(ℂ,ℂ)) {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ w : Hilbert n, ∃ v : n → 𝓢(ℂ,ℂ),
      (∀ i, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω' → w i z=v i z) ∧
      ∀ i, Set.EqOn (fun z => schwartzDbar (v i) z+∑ j, a i j z*v j z) (f i) Ω' := by
  obtain ⟨C,hC,T,hT,heq⟩ := exists_planar_weak_inverse hS a (fun i j => (ha i j).1)
  let f' : Hilbert n := WithLp.toLp 2 (fun i => (f i).toLp 2 volume)
  let w : Hilbert n := T f'
  have he : ∀ i, LocalEqual Ω (ElasticityPlanarDistribution.dbar (w i : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (a i j) (w j : 𝓢'(ℂ,ℂ))) (f i : 𝓢'(ℂ,ℂ)) := by
    intro i
    have hh := weak_to_local_equation Ω S hΩS a ha w f' (heq f') i
    simpa only [f',WithLp.ofLp_toLp,Lp.toTemperedDistribution_toLp_eq] using hh
  have he' : ElasticityPlanarDistribution.Equation Ω (fun i j z => -a i j z)
      (fun j => (w j : 𝓢'(ℂ,ℂ))) (fun j => (f j : 𝓢'(ℂ,ℂ))) := by
    intro i φ hφ hφs
    have hh := he i φ hφ hφs
    simp only [add_apply,sum_apply,smulLeftCLM_apply_apply] at hh ⊢
    have hn (j : n) : SchwartzMap.smulLeftCLM ℂ (fun z => -a i j z) φ =
        -SchwartzMap.smulLeftCLM ℂ (a i j) φ := by
      ext z
      change (SchwartzMap.smulLeftCLM ℂ (-(a i j)) φ) z = _
      simp only [SchwartzMap.smulLeftCLM_apply_apply ((ha i j).neg),
        SchwartzMap.smulLeftCLM_apply_apply (ha i j),neg_apply,Pi.neg_apply,smul_eq_mul,neg_mul]
    simp only [hn,map_neg,Finset.sum_neg_distrib]
    linear_combination hh
  have hall := ElasticityPlanarDistribution.local_all_orders (fun i j z => -a i j z)
    (fun i j => (ha i j).neg) (fun j => (w j : 𝓢'(ℂ,ℂ))) (fun j => (f j : 𝓢'(ℂ,ℂ))) he'
    (fun j => MemSobolev.local_zero (memSobolev_zero_iff.mpr ⟨w j,rfl⟩) Ω)
    (fun N j g hg hc _ => sobolev_nat_product Complex.orthonormalBasisOneI N hg hc (f j).memSobolev)
  have hv : ∀ i : n, ∃ v : 𝓢(ℂ,ℂ), LocalEqual Ω' (w i : 𝓢'(ℂ,ℂ)) (v : 𝓢'(ℂ,ℂ)) ∧
      ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω' → w i z=v z := by
    intro i
    exact local_schwartz_l2_representative hΩ' (w i) (fun N => hall N i) hg hc hs h1
  choose v hv hev using hv
  refine ⟨w,v,hev,fun i => ?_⟩
  let q : 𝓢(ℂ,ℂ) := schwartzDbar (v i)+∑ j, SchwartzMap.smulLeftCLM ℂ (a i j) (v j)
  have hq : (q : 𝓢'(ℂ,ℂ))=ElasticityPlanarDistribution.dbar (v i : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (a i j) (v j : 𝓢'(ℂ,ℂ)) := by
    simp only [q,map_add,map_sum,← dbar_schwartz]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => (distribution_schwartz_product (ha i j) (v j)).symm)
  have hqq : LocalEqual Ω' (q : 𝓢'(ℂ,ℂ)) (f i : 𝓢'(ℂ,ℂ)) := by
    rw [hq]
    have hh := (LocalEqual.dbar (hv i)).add (LocalEqual.sum Finset.univ (fun j _ => LocalEqual.coeff (hv j) (ha i j)))
    exact fun φ hφ hφs => (hh φ hφ hφs).symm.trans (he i φ hφ (hφs.trans hsub))
  have hpoint := hqq.schwartz_eqOn hΩ'
  intro z hz
  have hp := hpoint hz
  simpa only [q,add_apply,sum_apply,SchwartzMap.smulLeftCLM_apply_apply (ha i _),smul_eq_mul] using hp
end ElasticityPlanar
section
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal BigOperators
namespace ElasticityRegularity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
lemma SmoothSobolev.local_nat {N : ℕ} {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothSobolev N u) (Ω : Set E) : SmoothLocalSobolev Ω N u := by
  intro g hg hc _
  obtain ⟨u,hu,he⟩ := hu
  obtain ⟨L,hL⟩ := exists_bounded_nat_multiplier N hg hc
  exact ⟨fun p => L (u p),(L.restrictScalars ℝ).contDiff.comp hu,fun p => by rw [hL,he]⟩
lemma smoothSobolev_schwartz_const (N : ℕ) (f : 𝓢(E,ℂ)) :
    SmoothSobolev N (fun _ : P => (f : 𝓢'(E,ℂ))) := by
  obtain ⟨v,hv⟩ := (memSobolev_iff_range (N:ℝ) (f : 𝓢'(E,ℂ))).mp f.memSobolev
  exact ⟨fun _ => v,contDiff_const,fun _ => hv⟩
end ElasticityRegularity

namespace ElasticityPlanar
open ElasticityRegularity
variable {n : Type*} [Fintype n]
/-- The weak inverse along the entire coefficient homotopy has actual joint smooth
classical representatives with the exact prescribed source. This is the linear
PDE input to the frame homotopy, not an assumed family of invertible frames. -/
theorem exists_classical_homotopy {S Ω Ω' : Set ℂ} (hS : IsCompact S)
    (hΩS : Ω ⊆ S) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hac : ∀ i j, HasCompactSupport (a i j)) (f : n → 𝓢(ℂ,ℂ))
    {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : ℝ → n → 𝓢(ℂ,ℂ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℂ => v q.1 i q.2)) ∧
      ∀ s i, Set.EqOn (fun z => schwartzDbar (v s i) z+∑ j, (s:ℂ)*a i j z*v s j z) (f i) Ω' := by
  obtain ⟨T,hT,heq⟩ := global_homotopy_inverse hS hΩS a ha hac
  let f' : Hilbert n := WithLp.toLp 2 (fun i => (f i).toLp 2 volume)
  let w : ℝ → Hilbert n := fun s => T s f'
  let u : ℝ → n → 𝓢'(ℂ,ℂ) := fun s i => (w s i : 𝓢'(ℂ,ℂ))
  have hw : ContDiff ℝ (⊤ : ℕ∞) w :=
    ((ContinuousLinearMap.apply ℂ (Hilbert n) f').restrictScalars ℝ).contDiff.comp hT
  have hat (i j : n) : (a i j).HasTemperateGrowth := (hac i j).hasTemperateGrowth (ha i j)
  have hscaled (s : ℝ) (i j : n) : (fun z => (s:ℂ)*a i j z).HasTemperateGrowth :=
    Function.HasTemperateGrowth.mul (Function.HasTemperateGrowth.const (s:ℂ)) (hat i j)
  have he (s : ℝ) (i : n) : LocalEqual Ω
      (ElasticityPlanarDistribution.dbar (u s i)+
        ∑ j, smulLeftCLM ℂ (fun z => (s:ℂ)*a i j z) (u s j)) (f i : 𝓢'(ℂ,ℂ)) := by
    simpa only [f',WithLp.ofLp_toLp,Lp.toTemperedDistribution_toLp_eq] using heq s f' i
  have hm (s : ℝ) (i j : n) : smulLeftCLM ℂ (fun z => (s:ℂ)*a i j z) (u s j)=
      (s:ℂ) • smulLeftCLM ℂ (a i j) (u s j) := by
    change smulLeftCLM ℂ ((s:ℂ) • (a i j)) (u s j) = _
    rw [smulLeftCLM_smul (hat i j),smul_apply]
  have he' (s : ℝ) (i : n) : LocalEqual Ω (ElasticityPlanarDistribution.dbar (u s i))
      ((f i : 𝓢'(ℂ,ℂ))+(-(s:ℂ)) • ∑ j, smulLeftCLM ℂ (a i j) (u s j)) := by
    intro φ hφ hφs
    have h := he s i φ hφ hφs
    simp only [hm,← Finset.smul_sum,add_apply,smul_apply,smul_eq_mul,neg_mul] at h ⊢
    linear_combination h
  have hu (i : n) : SmoothLocalSobolev Ω 0 (fun s => u s i) := by
    have hzero : SmoothSobolev 0 (fun s => u s i) := by
      let L : Hilbert n →L[ℂ] PL2 := (ContinuousLinearMap.proj i).comp
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)).toContinuousLinearMap
      refine ⟨fun s => L (w s),(L.restrictScalars ℝ).contDiff.comp hw,fun s => ?_⟩
      simp only [sobolevInjection,neg_zero,besselPotential_zero,ContinuousLinearMap.id_comp,
        Lp.toTemperedDistributionCLM_apply]
      rfl
    simpa only [Nat.cast_zero] using
      (SmoothSobolev.local_nat (N := 0) (u := fun s => u s i)
        (by simpa only [Nat.cast_zero] using hzero) Ω)
  have hall := ElasticityPlanarDistribution.smooth_local_all_orders a hat
    (fun s : ℝ => -(s:ℂ)) (Complex.ofRealCLM.contDiff.neg)
    u (fun _ i => (f i : 𝓢'(ℂ,ℂ))) he' hu
    (fun N i => (smoothSobolev_schwartz_const (P := ℝ) N (f i)).local_nat Ω)
  have hv (i : n) : ∃ v : ℝ → 𝓢(ℂ,ℂ),
      ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℂ => v q.1 q.2) ∧
      ∀ s, LocalEqual Ω' (u s i) (v s : 𝓢'(ℂ,ℂ)) :=
    SmoothLocalSobolev.joint_schwartz_representative (fun s => u s i)
      (fun N => hall N i) hg hc hs h1
  choose v hv hv' using hv
  refine ⟨fun s i => v i s,hv,fun s i => ?_⟩
  let q : 𝓢(ℂ,ℂ) := schwartzDbar (v i s)+
    ∑ j, SchwartzMap.smulLeftCLM ℂ (fun z => (s:ℂ)*a i j z) (v j s)
  have hq : (q : 𝓢'(ℂ,ℂ))=ElasticityPlanarDistribution.dbar (v i s : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (fun z => (s:ℂ)*a i j z) (v j s : 𝓢'(ℂ,ℂ)) := by
    simp only [q,map_add,map_sum,← dbar_schwartz]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => (distribution_schwartz_product (hscaled s i j) (v j s)).symm)
  have hqq : LocalEqual Ω' (q : 𝓢'(ℂ,ℂ)) (f i : 𝓢'(ℂ,ℂ)) := by
    rw [hq]
    have hh := (LocalEqual.dbar (hv' i s)).add (LocalEqual.sum Finset.univ
      (fun j _ => LocalEqual.coeff (hv' j s) (hscaled s i j)))
    exact fun φ hφ hφs => (hh φ hφ hφs).symm.trans (he s i φ hφ (hφs.trans hsub))
  intro z hz
  have hp := hqq.schwartz_eqOn hΩ' hz
  simpa only [q,add_apply,sum_apply,SchwartzMap.smulLeftCLM_apply_apply (hscaled s i _),smul_eq_mul] using hp
end ElasticityPlanar

end
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
omit [MeasurableSpace E] [BorelSpace E] in
lemma exists_schwartz_one_on_compact {K : Set E} (hK : IsCompact K) :
    ∃ g : 𝓢(E,ℂ), Set.EqOn g 1 K := by
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0 : E) := ⟨R,R+1,hR,by simp⟩
  have hc : HasCompactSupport (fun x : E => (b x : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => (b x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨hc.toSchwartzMap hg,fun x hx => ?_⟩
  change (b x : ℂ)=1
  rw [b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hKR x hx)]
  rfl
/-- The actual Schwartz representatives of joint smooth uniform-compact-support
families vary smoothly in every nonnegative Hilbert Sobolev norm. -/
theorem compact_smooth_sobolev {K : Set E} (hK : IsCompact K)
    (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉K → a (p,x)=0) :
    ∃ f : P → 𝓢(E,ℂ), (∀ p x, f p x=a (p,x)) ∧
      ∀ N : ℕ, SmoothSobolev N (fun p => (f p : 𝓢'(E,ℂ))) := by
  obtain ⟨g,hg⟩ := exists_schwartz_one_on_compact hK
  have hat (p : P) : (fun x => a (p,x)).HasTemperateGrowth :=
    (compact_slice hK a hs p).hasTemperateGrowth (ha.comp (contDiff_const.prodMk contDiff_id))
  let f : P → 𝓢(E,ℂ) := fun p => SchwartzMap.smulLeftCLM ℂ (fun x => a (p,x)) g
  refine ⟨f,fun p x => ?_,fun N => ?_⟩
  · change SchwartzMap.smulLeftCLM ℂ (fun x => a (p,x)) g x=_
    rw [SchwartzMap.smulLeftCLM_apply_apply (hat p),smul_eq_mul]
    by_cases hx : x∈K
    · rw [hg hx,Pi.one_apply,mul_one]
    · rw [hs p x hx,zero_mul]
  · have H := (smoothSobolev_schwartz_const (P := P) N g).variable_nat hK N a ha hs
    convert H using 1
    funext p
    exact (distribution_schwartz_product (hat p) g).symm
end ElasticityRegularity
section
open MeasureTheory TemperedDistribution Set Complex
open scoped SchwartzMap LineDeriv Laplacian BigOperators
namespace ElasticityRegularity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
lemma SmoothLocalSobolev.variable_nat {Ω S : Set E} (hS : IsCompact S)
    (N : ℕ) (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉S → a (p,x)=0) {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothLocalSobolev Ω N u) :
    SmoothLocalSobolev Ω N (fun p => smulLeftCLM ℂ (fun x => a (p,x)) (u p)) := by
  intro g hg hc hgs
  have H := (hu g hg hc hgs).variable_nat hS N a ha hs
  convert H using 1
  funext p
  have hat : (fun x => a (p,x)).HasTemperateGrowth :=
    (compact_slice hS a hs p).hasTemperateGrowth (ha.comp (contDiff_const.prodMk contDiff_id))
  rw [smulLeftCLM_smulLeftCLM_apply (hc.hasTemperateGrowth hg) hat,
    smulLeftCLM_smulLeftCLM_apply hat (hc.hasTemperateGrowth hg),mul_comm g]
end ElasticityRegularity
namespace ElasticityPlanarDistribution
open ElasticityRegularity
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable {n : Type*} [Fintype n]
/-- The full variable-coefficient planar weak equation has strong smooth
parameter regularity at every spatial order. -/
theorem smooth_variable_all_orders {Ω S : Set ℂ} (hS : IsCompact S)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉S → a i j (p,z)=0)
    (u f : P → n → Dist)
    (heq : ∀ p i, LocalEqual Ω (dbar (u p i))
      (f p i+∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (u p j)))
    (hu : ∀ i, ElasticityRegularity.SmoothLocalSobolev Ω 0 (fun p => u p i))
    (hf : ∀ N : ℕ, ∀ i, ElasticityRegularity.SmoothLocalSobolev Ω N (fun p => f p i)) :
    ∀ N : ℕ, ∀ i, ElasticityRegularity.SmoothLocalSobolev Ω N (fun p => u p i) := by
  intro N
  induction N with
  | zero => simpa only [Nat.cast_zero] using hu
  | succ N ih =>
    rw [Nat.cast_add,Nat.cast_one]
    intro i
    apply (ih i).laplacian_gain
    have H := SmoothLocalSobolev.dhol ((hf N i).add
      (ElasticityRegularity.SmoothLocalSobolev.sum Finset.univ
        (fun j p => smulLeftCLM ℂ (fun z => a i j (p,z)) (u p j))
        (fun j _ => (ih j).variable_nat hS N (a i j) (ha i j) (hs i j))))
    apply H.congr
    intro p
    simpa only [dhol_dbar] using LocalEqual.dhol (heq p i)
end ElasticityPlanarDistribution

end
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
/-- Actual smooth classical solutions for arbitrary joint smooth compactly
supported planar coefficient and source families. -/
theorem exists_classical_variable {S Ω Ω' K : Set ℂ} (hS : IsCompact S)
    (hΩS : Ω ⊆ S) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hac : ∀ i j p z, z∉K → a i j (p,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfc : ∀ i p z, z∉K → f i (p,z)=0)
    {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : P → n → 𝓢(ℂ,ℂ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 i q.2)) ∧
      ∀ p i, Set.EqOn (fun z => schwartzDbar (v p i) z+∑ j, a i j (p,z)*v p j z)
        (fun z => f i (p,z)) Ω' := by
  choose F hFe hF using fun i => compact_smooth_sobolev hK (f i) (hf i) (hfc i)
  have hF₀ (i : n) : ∃ w : P → PL2, ContDiff ℝ (⊤ : ℕ∞) w ∧
      ∀ p, (w p : 𝓢'(ℂ,ℂ))=(F i p : 𝓢'(ℂ,ℂ)) := by
    obtain ⟨w,hw,he⟩ := hF i 0
    simp only [Nat.cast_zero,sobolevInjection,neg_zero,besselPotential_zero,
      ContinuousLinearMap.id_comp,Lp.toTemperedDistributionCLM_apply] at he
    exact ⟨w,hw,he⟩
  choose W hW hWe using hF₀
  let rhs : P → Hilbert n := fun p => WithLp.toLp 2 (fun i => W i p)
  have hrhs : ContDiff ℝ (⊤ : ℕ∞) rhs :=
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
      (contDiff_pi.mpr hW)
  obtain ⟨T,hT,heq⟩ := global_variable_inverse hS hΩS hK a ha hac
  let w : P → Hilbert n := fun p => T p (rhs p)
  let u : P → n → 𝓢'(ℂ,ℂ) := fun p i => (w p i : 𝓢'(ℂ,ℂ))
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := complex_clm_apply_smooth hT hrhs
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hac i j) p).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  have he (p : P) (i : n) : LocalEqual Ω
      (ElasticityPlanarDistribution.dbar (u p i)+
        ∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (u p j)) (F i p : 𝓢'(ℂ,ℂ)) := by
    simpa only [planarOperator_apply,rhs,WithLp.ofLp_toLp,hWe] using heq p (rhs p) i
  have he' (p : P) (i : n) : LocalEqual Ω (ElasticityPlanarDistribution.dbar (u p i))
      ((F i p : 𝓢'(ℂ,ℂ))+∑ j, smulLeftCLM ℂ (fun z => -(a i j (p,z))) (u p j)) := by
    intro φ hφ hφs
    have h := he p i φ hφ hφs
    have hn (j : n) : smulLeftCLM ℂ (fun z => -(a i j (p,z))) (u p j)=
        -smulLeftCLM ℂ (fun z => a i j (p,z)) (u p j) := by
      change smulLeftCLM ℂ (-(fun z => a i j (p,z))) (u p j)=_
      rw [smulLeftCLM_neg (hat p i j),neg_apply]
    simp only [hn,Finset.sum_neg_distrib,add_apply,neg_apply] at h ⊢
    linear_combination h
  have hu (i : n) : SmoothLocalSobolev Ω 0 (fun p => u p i) := by
    have hz : SmoothSobolev 0 (fun p => u p i) := by
      let L : Hilbert n →L[ℂ] PL2 := (ContinuousLinearMap.proj i).comp
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)).toContinuousLinearMap
      refine ⟨fun p => L (w p),(L.restrictScalars ℝ).contDiff.comp hw,fun p => ?_⟩
      simp only [sobolevInjection,neg_zero,besselPotential_zero,ContinuousLinearMap.id_comp,
        Lp.toTemperedDistributionCLM_apply]
      rfl
    simpa only [Nat.cast_zero] using (SmoothSobolev.local_nat (N := 0) (by simpa only [Nat.cast_zero] using hz) Ω)
  have hall := ElasticityPlanarDistribution.smooth_variable_all_orders hK
    (fun i j q => -(a i j q)) (fun i j => (ha i j).neg)
    (fun i j p z hz => by rw [hac i j p z hz,neg_zero])
    u (fun p i => (F i p : 𝓢'(ℂ,ℂ))) he' hu
    (fun N i => (hF i N).local_nat Ω)
  have hv (i : n) : ∃ v : P → 𝓢(ℂ,ℂ),
      ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 q.2) ∧
      ∀ p, LocalEqual Ω' (u p i) (v p : 𝓢'(ℂ,ℂ)) :=
    SmoothLocalSobolev.joint_schwartz_representative (fun p => u p i)
      (fun N => hall N i) hg hc hs h1
  choose v hv hv' using hv
  refine ⟨fun p i => v i p,hv,fun p i => ?_⟩
  let q : 𝓢(ℂ,ℂ) := schwartzDbar (v i p)+
    ∑ j, SchwartzMap.smulLeftCLM ℂ (fun z => a i j (p,z)) (v j p)
  have hq : (q : 𝓢'(ℂ,ℂ))=ElasticityPlanarDistribution.dbar (v i p : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (v j p : 𝓢'(ℂ,ℂ)) := by
    simp only [q,map_add,map_sum,← dbar_schwartz]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => (distribution_schwartz_product (hat p i j) (v j p)).symm)
  have hqq : LocalEqual Ω' (q : 𝓢'(ℂ,ℂ)) (F i p : 𝓢'(ℂ,ℂ)) := by
    rw [hq]
    have hh := (LocalEqual.dbar (hv' i p)).add (LocalEqual.sum Finset.univ
      (fun j _ => LocalEqual.coeff (hv' j p) (hat p i j)))
    exact fun φ hφ hφs => (hh φ hφ hφs).symm.trans (he p i φ hφ (hφs.trans hsub))
  intro z hz
  have hp := hqq.schwartz_eqOn hΩ' hz
  simpa only [q,add_apply,sum_apply,SchwartzMap.smulLeftCLM_apply_apply (hat p i _),smul_eq_mul,hFe] using hp
end ElasticityPlanar

end

end OAI
