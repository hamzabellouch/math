import Mathlib
import OAI.Analysis.SymmetricDomains.CocompactScaling
import OAI.Analysis.SymmetricDomains.LocalInverseSupportScaled
import OAI.Analysis.SymmetricDomains.ScaledLocal
import OAI.Analysis.SymmetricDomains.NormalizedLocalInverse
import OAI.Analysis.SymmetricDomains.CompactSupportRates

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology
open scoped Classical

theorem support_rates_imply_scaled_localization
    {N r k : ℕ} {U V Ω : Set (Affine N)} (hUV : U ⊆ V)
    (Φ : Affine r × Affine k → Affine N) (Ψ : Affine N → Affine r × Affine k)
    {p : Affine N} (hΦ : AnalyticAt ℂ Φ 0) (hΦ0 : Φ 0=p)
    (hΨ : DifferentiableAt ℂ Ψ p) (hΨ0 : Ψ p=0)
    (hinv : ∀ᶠ z in 𝓝 (0 : Affine r × Affine k), Ψ (Φ z)=z)
    (hΩ : Ω ∈ 𝓝[V] p) (hfg : ∀ y ∈ Ω, Φ (Ψ y)=y)
    (h : Fin k → Affine N → ℂ)
    (hh : ∀ i, AnalyticAt ℂ (h i) p) (hh0 : ∀ i, h i p=1)
    (i₀ : Fin k) (hpeak : ∀ y ∈ U, ‖h i₀ y‖ ≤ Real.exp (-(‖y-p‖^2)))
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β)
    (hder : ∀ i z, fderiv ℂ (fun y => Complex.log (h i (Φ y))) 0 z =
      Complex.I*∑ j, (β i j : ℂ)*z.2 j)
    (f : ℕ → U → U) (t : ℕ → ℝ) (htp : ∀ j, 0 < t j)
    (ht : Tendsto t atTop (𝓝 0)) (E : Set (Affine N))
    {A : ℝ} (hA : 0 < A)
    (hrate : ∀ᶠ j in atTop, ∀ y : U, y.val ∈ E →
      ‖fun i => 1-h i (f j y).val‖ ≤ A*t j) :
    ∃ M > 0, ∀ᶠ j in atTop, ∀ y : U, y.val ∈ E →
      (f j y).val ∈ Ω ∧ ‖weightedUnscale (t j) (Ψ (f j y).val)‖ ≤ M := by
  obtain ⟨C,hC,W,hW,hscale⟩ := local_inverse_support_scaled_bound Φ Ψ hΦ hΦ0
    hΨ hΨ0 hinv U h hh hh0 i₀ hpeak β hβ hder
  obtain ⟨WΩ,hWΩ,hinc⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hΩ
  have hWΨ : Ψ ⁻¹' W ∈ 𝓝 p := hΨ.continuousAt.preimage_mem_nhds (hΨ0.symm ▸ hW)
  have hl := gaussian_peak_eventually_mem (h i₀) U p hpeak
    (fun j (y : U) => (f j y).val) {y : U | y.val ∈ E} t ht
    (C := A) (hrate.mono fun j hj y hy =>
      ⟨(f j y).property,(norm_le_pi_norm (fun i => (1 : ℂ)-h i (f j y).val) i₀).trans (hj y hy)⟩) (inter_mem hWΩ hWΨ)
  let M := max (Real.sqrt (C*A)) (C*A)
  refine ⟨M+1,by dsimp only [M]; positivity,?_⟩
  filter_upwards [hl,hrate] with j hj hr y hy
  have hym := hj y hy
  have hyΩ : (f j y).val ∈ Ω := hinc ⟨hym.1,hUV (f j y).property⟩
  have hb := hscale A hA.le (t j) (htp j) (Ψ (f j y).val) hym.2
    (by rw [hfg _ hyΩ]; exact (f j y).property)
    (by rw [hfg _ hyΩ]; exact hr y hy)
  exact ⟨hyΩ,hb.trans (by dsimp only [M]; linarith)⟩

end

open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

theorem global_from_two_sided (s : NashBoundaryScalingChart c x)
    (hgood : c.GoodAt x) (hcut : s.HasCutoffs)
    (hUV : U ⊆ V) (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    (hconn : IsConnected U) (hbounded : Bornology.IsBounded U) (hsmooth : IsSmooth U)
    [LocallyCompactSpace U] (Γ : Type*) [Group Γ] [TopologicalSpace Γ]
    [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun y => (γ • y : U).val))
    (Ω : Set (Affine N)) (hΩV : Ω ⊆ V)
    (hΩo : IsOpen ((Subtype.val : V → Affine N) ⁻¹' Ω)) (hpΩ : q x ∈ Ω)
    (hfΩ : MapsTo s.forward s.offsets.source Ω)
    (hgS : MapsTo s.backward Ω s.offsets.source)
    (hfg : ∀ y ∈ Ω, s.forward (s.backward y)=y)
    (h : Fin s.normalDim → Affine N → ℂ)
    (hh : ∀ i, Differentiable ℂ (h i)) (hh0 : ∀ i, h i (q x)=1)
    (hb : ∀ i y, y ∈ U → ‖h i y‖ ≤ 1)
    (i₀ : Fin s.normalDim)
    (hpeak : ∀ y ∈ U, ‖h i₀ y‖ ≤ Real.exp (-(‖y-q x‖^2)))
    (β : Fin s.normalDim → Fin s.normalDim → ℝ) (hβ : LinearIndependent ℝ β)
    (hder : ∀ i z, fderiv ℂ (fun y => Complex.log (h i (s.forward y))) 0 z =
      Complex.I*∑ j, (β i j : ℂ)*z.2 j)
    (O : Set (Affine s.tangentDim × Affine s.normalDim)) (hO : IsOpen O)
    (w : Affine s.normalDim) (hw : (0,w) ∈ O)
    (hcover : ∀ K : Set (Affine s.tangentDim × Affine s.normalDim),
      IsCompact K → K ⊆ O → ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ s.domain t)
    (hexclude : ∀ z ∉ O, ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
      ∃ a : ℕ → Affine s.tangentDim × Affine s.normalDim,
        Tendsto a atTop (𝓝 z) ∧ ∀ᶠ j in atTop, a j ∉ s.domain (t j)) :
    Nonempty (Biholomorph U (connectedComponentIn
      ((affineProductCoordinates s.tangentDim s.normalDim) '' O)
      ((affineProductCoordinates s.tangentDim s.normalDim) (0,w)))) := by
  let : ContinuousConstSMul Γ U := ⟨fun γ => ((hhol γ).continuous).subtype_mk _⟩
  let : Nonempty U := hconn.nonempty.to_subtype
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn.isPreconnected
  let e := affineProductCoordinates s.tangentDim s.normalDim
  have hsf := s.forward_analytic hcut 0 s.source_zero
  have hsg := (s.backward_analytic (q x) (mem_univ _)).differentiableAt
  have hs0 := s.forward_zero hgood
  have hg0 := s.backward_center hgood
  have hinv : ∀ᶠ z in 𝓝 (0 : Affine s.tangentDim × Affine s.normalDim),
      s.backward (s.forward z)=z := by
    filter_upwards [s.offsets.open_source.mem_nhds s.source_zero] with z hz
    exact s.backward_forward hcut hz
  have hΩn : Ω ∈ 𝓝[V] (q x) := by
    rw [nhdsWithin_eq_map_subtype_coe (hΩV hpΩ)]
    exact hΩo.mem_nhds hpΩ
  have hha : ∀ i, AnalyticAt ℂ (h i) (q x) := fun i => analyticOnNhd_of_differentiableOn_finite isOpen_univ (hh i).differentiableOn _ (mem_univ _)
  obtain ⟨A,hA,τ,hτ,hanchor⟩ := support_normal_ray_bound s.forward hsf hs0 h hha hh0 w
  have hbaseD : ∀ᶠ t : ℝ in 𝓝[>] 0, (0,w) ∈ s.domain t :=
    (hcover {(0,w)} isCompact_singleton (singleton_subset_iff.mpr hw)).mono
      fun t ht => ht (mem_singleton _)
  obtain ⟨δ,hδ,hδD⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbaseD
  obtain ⟨t,_htanti,htmem,ht⟩ := exists_seq_strictAnti_tendsto' (lt_min hδ hτ)
  have htp : ∀ j, 0 < t j := fun j => (htmem j).1
  have htD : ∀ j, (0,w) ∈ s.domain (t j) :=
    fun j => hδD ⟨(htmem j).1,lt_of_lt_of_le (htmem j).2 (min_le_left _ _)⟩
  let p : ℕ → U := fun j => ⟨s.forward (weightedScale (t j) (0,w)),(htD j).2⟩
  obtain ⟨K,hK,hrep⟩ := exists_compact_orbit_representatives (X := U) (Γ := Γ)
  choose a ha γ hγ using fun j => hrep (p j)
  have hanchor' : ∀ᶠ j in atTop, ‖fun i => 1-h i (γ j • a j : U).val‖ ≤ A*t j := by
    apply Eventually.of_forall
    intro j
    rw [hγ j]
    exact hanchor (t j) (htp j) (lt_of_lt_of_le (htmem j).2 (min_le_right _ _))
  have hest : ∀ E : Set (Affine N), IsCompact E → E ⊆ U →
      ∃ M > 0, ∀ᶠ j in atTop, ∀ y : U, y.val ∈ E →
        (γ j • y : U).val ∈ Ω ∧
        ‖weightedUnscale (t j) (s.backward (γ j • y : U).val)‖ ≤ M := by
    intro E hE hEU
    obtain ⟨C,hC,hrate⟩ := hsmooth.compact_support_rates hK h hh hb
      (fun j y => γ j • y) (fun j => hhol (γ j)) a ha t htp hA hanchor' hE hEU
    exact support_rates_imply_scaled_localization hUV s.forward s.backward hsf hs0
      hsg hg0 hinv hΩn hfg h hha hh0 i₀ hpeak β hβ hder
      (fun j y => γ j • y) t htp ht E hC hrate
  let D : ℕ → Set (Affine (s.tangentDim+s.normalDim)) := fun j => e '' s.domain (t j)
  let Aset : ℕ → Set (Affine N) := fun j => actionLocalSet U Γ (γ j) Ω
  let b : ∀ j, Biholomorph (Aset j) (D j) := fun j =>
    normalizedLocalBiholomorph hhol (γ j)
      (s.scaled_local_biholomorph hcut Ω hfΩ hgS hfg (htp j))
  let F : ℕ → Affine N → Affine (s.tangentDim+s.normalDim) :=
    fun j y => e (weightedUnscale (t j) (s.backward (ambientAction U Γ (γ j) y)))
  let G : ℕ → Affine (s.tangentDim+s.normalDim) → Affine N :=
    fun j z => ambientAction U Γ (γ j)⁻¹ (s.forward (weightedScale (t j) (e.symm z)))
  have hAo : ∀ j, IsOpen ((Subtype.val : U → Affine N) ⁻¹' Aset j) := by
    intro j
    apply actionLocalSet_open (γ j)
    exact hΩo.preimage (Topology.IsEmbedding.inclusion hUV).continuous
  have hDo : ∀ j, IsOpen (D j) := fun j =>
    e.toHomeomorph.isOpenMap _ (s.domain_open hcut hU (t j))
  have hbf : ∀ j (y : Aset j), F j y.val=((b j).toHomeomorph y).val := by
    intro j y
    exact normalizedLocalBiholomorph_forward hhol (γ j)
      (s.scaled_local_biholomorph hcut Ω hfΩ hgS hfg (htp j))
      (fun y => e (weightedUnscale (t j) (s.backward y))) (by intro y; rfl) y
  have hbg : ∀ j (z : D j), G j z.val=((b j).toHomeomorph.symm z).val := by
    intro j z
    exact normalizedLocalBiholomorph_inverse hhol (γ j)
      (s.scaled_local_biholomorph hcut Ω hfΩ hgS hfg (htp j))
      (fun z => s.forward (weightedScale (t j) (e.symm z))) (by intro z; rfl) z
  have hcoverA : ∀ E, IsCompact E → E ⊆ U → ∀ᶠ j in atTop, E ⊆ Aset j := by
    intro E hE hEU
    obtain ⟨M,_hM,he⟩ := hest E hE hEU
    filter_upwards [he] with j hj y hy
    refine ⟨hEU hy,?_⟩
    change ambientAction U Γ (γ j) y ∈ Ω
    rw [show ambientAction U Γ (γ j) y=(γ j • (⟨y,hEU hy⟩ : U)).val from
      ambientAction_subtype (γ j) ⟨y,hEU hy⟩]
    exact (hj ⟨y,hEU hy⟩ hy).1
  have hbound : ∀ E, IsCompact E → E ⊆ U →
      ∃ M > 0, ∀ᶠ j in atTop, ∀ y ∈ E, ‖F j y‖ ≤ M := by
    intro E hE hEU
    obtain ⟨M,hM,he⟩ := hest E hE hEU
    refine ⟨‖e.toContinuousLinearMap‖*M+1,by positivity,?_⟩
    filter_upwards [he] with j hj y hy
    have hb' := (hj ⟨y,hEU hy⟩ hy).2
    change ‖e (weightedUnscale (t j) (s.backward (ambientAction U Γ (γ j) y)))‖ ≤ _
    rw [show ambientAction U Γ (γ j) y=(γ j • (⟨y,hEU hy⟩ : U)).val from
      ambientAction_subtype (γ j) ⟨y,hEU hy⟩]
    exact ((e.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hb' (norm_nonneg _))).trans (by linarith)
  have htGT : Tendsto t atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall htp⟩
  have hcoverD : ∀ C : Set (Affine (s.tangentDim+s.normalDim)), IsCompact C →
      C ⊆ connectedComponentIn (e '' O) (e (0,w)) → ∀ᶠ j in atTop, C ⊆ D j := by
    intro C hC hCD
    have hCsub : e.symm '' C ⊆ O := by
      rintro _ ⟨y,hy,rfl⟩
      obtain ⟨z,hz,hzy⟩ := connectedComponentIn_subset (e '' O) (e (0,w)) (hCD hy)
      simpa only [← hzy,e.symm_apply_apply] using hz
    filter_upwards [htGT (hcover (e.symm '' C) (hC.image e.symm.continuous) hCsub)] with j hj y hy
    exact ⟨e.symm y,hj ⟨y,hy,rfl⟩,e.apply_symm_apply y⟩
  have hbaseG : ∃ C : Set U, IsCompact C ∧ ∀ᶠ j in atTop, G j (e (0,w)) ∈ Subtype.val '' C := by
    refine ⟨K,hK,Eventually.of_forall fun j => ?_⟩
    have he : G j (e (0,w))=(a j).val := by
      change ambientAction U Γ (γ j)⁻¹ (s.forward (weightedScale (t j) (e.symm (e (0,w)))))=_
      rw [e.symm_apply_apply]
      change ambientAction U Γ (γ j)⁻¹ (p j).val=_
      rw [ambientAction_subtype,← hγ j,inv_smul_smul]
    exact ⟨a j,ha j,he.symm⟩
  have hxa : ∀ z ∉ e '' O, ∃ a : ℕ → Affine (s.tangentDim+s.normalDim),
      Tendsto a atTop (𝓝 z) ∧ ∀ᶠ j in atTop, a j ∉ D j := by
    intro z hz
    have hz' : e.symm z ∉ O := fun he => hz ⟨e.symm z,he,e.apply_symm_apply z⟩
    obtain ⟨a,ha,hex⟩ := hexclude (e.symm z) hz' t ht htp
    refine ⟨fun j => e (a j),?_,?_⟩
    · simpa only [e.apply_symm_apply,Function.comp_def] using e.continuous.continuousAt.tendsto.comp ha
    · filter_upwards [hex] with j hj
      rintro ⟨y,hy,he⟩
      exact hj (e.injective he ▸ hy)
  exact cocompact_scaling_biholomorph hconn.isPreconnected hbounded hhol
    (e.toHomeomorph.isOpenMap _ hO) ⟨(0,w),hw,rfl⟩ Aset D
    (fun j => actionLocalSet_subset (γ j) Ω) hAo hDo b F G hbf hbg
    hcoverA hcoverD hbound hbaseG hxa

end NashBoundaryScalingChart
end Release061

end

end OAI
