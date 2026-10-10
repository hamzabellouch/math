import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCoordinateRetraction
import OAI.Geometry.TamingCompatibility.Hodge.HodgeVolterraKernel

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open MeasureTheory Set

lemma polynomial_bound (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1+x)^n ≤ 2^n*(1+x^(2*n)) := by
  by_cases h : x ≤ 1
  · calc
      _ ≤ (2 : ℝ)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (pow_nonneg hx _))
  · have h1 : 1 ≤ x := (lt_of_not_ge h).le
    calc
      _ ≤ (2*x)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2^n*x^n := mul_pow _ _ _
      _ ≤ 2^n*x^(2*n) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)

lemma weighted_heat_bound (n : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (z : V) :
    (1+‖z‖/Real.sqrt t)^n * heat (a*t) z ≤
      (2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))*heat (2*a*t) z := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h0 := gaussian_weight_absorption (mul_pos ha ht) z 0
  norm_num only [Nat.mul_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,one_mul] at h0
  have hn := gaussian_weight_absorption (mul_pos ha ht) z n
  have he : (‖z‖/Real.sqrt t)^(2*n) = ‖z‖^(2*n)/t^n := by
    rw [div_pow,pow_mul (Real.sqrt t),Real.sq_sqrt ht.le]
  have hh : (‖z‖/Real.sqrt t)^(2*n)*heat (a*t) z ≤
      (4*(8*a)^n*(n.factorial : ℝ))*heat (2*a*t) z := by
    rw [he,div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos ht n)).mpr
    convert hn using 1; first | rfl | (simp only [mul_assoc,mul_pow]; ring)
  calc
    _ ≤ (2^n*(1+(‖z‖/Real.sqrt t)^(2*n)))*heat (a*t) z :=
      mul_le_mul_of_nonneg_right (polynomial_bound n (div_nonneg (norm_nonneg z) hs.le)) (heat_nonneg _ _)
    _ = 2^n*(heat (a*t) z+(‖z‖/Real.sqrt t)^(2*n)*heat (a*t) z) := by ring
    _ ≤ 2^n*(4*heat (2*a*t) z+(4*(8*a)^n*(n.factorial : ℝ))*heat (2*a*t) z) := by
      apply mul_le_mul_of_nonneg_left (add_le_add _ hh) (by positivity)
      simpa only [mul_assoc] using h0
    _ = _ := by ring

lemma gaussian_weighted_schur {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : V → V → F) (hK : Continuous (Function.uncurry K)) (n : ℕ) {a t C : ℝ}
    (ha : 0 < a) (ht : 0 < t) (hC : 0 ≤ C)
    (hbound : ∀ q y, ‖K q y‖ ≤ C*heat (a*t) (y-q)) :
    let A := C*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))
    (∀ q, Integrable (fun y => VolterraBounds.weight n t q y * ‖K q y‖) ∧
      (∫ y, VolterraBounds.weight n t q y * ‖K q y‖) ≤ A) ∧
    (∀ y, Integrable (fun q => VolterraBounds.weight n t q y * ‖K q y‖) ∧
      (∫ q, VolterraBounds.weight n t q y * ‖K q y‖) ≤ A) := by
  let A := C*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint (q y : V) : VolterraBounds.weight n t q y * ‖K q y‖ ≤ A*heat (2*a*t) (y-q) := by
    have hw : 0 ≤ VolterraBounds.weight n t q y := (VolterraBounds.weight_pos n ht q y).le
    calc
      _ ≤ VolterraBounds.weight n t q y * (C*heat (a*t) (y-q)) := mul_le_mul_of_nonneg_left (hbound q y) hw
      _ = C*((1+‖y-q‖/Real.sqrt t)^n*heat (a*t) (y-q)) := by
        rw [VolterraBounds.weight,dist_eq_norm,norm_sub_rev q y]
        ring
      _ ≤ _ := by simpa only [A,mul_assoc] using
        mul_le_mul_of_nonneg_left (weighted_heat_bound n ha ht (y-q)) hC
  constructor
  · intro q
    have hh : Integrable (fun y : V => A*heat (2*a*t) (y-q)) :=
      ((heat_integrable (by positivity : 0 < 2*a*t)).comp_sub_right q).const_mul A
    have hm : Integrable (fun y => VolterraBounds.weight n t q y * ‖K q y‖) := by
      apply hh.mono' (((VolterraBounds.weight_continuous n t q).mul (hK.comp (continuous_const.prodMk continuous_id)).norm).aestronglyMeasurable)
      filter_upwards [] with y
      change ‖VolterraBounds.weight n t q y * ‖K q y‖‖ ≤ A*heat (2*a*t) (y-q)
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (VolterraBounds.weight_pos n ht q y).le (norm_nonneg _))]
      exact hpoint q y
    refine ⟨hm,?_⟩
    calc
      _ ≤ ∫ y : V, A*heat (2*a*t) (y-q) := integral_mono hm hh (hpoint q)
      _ = A := by rw [integral_const_mul,integral_sub_right_eq_self,heat_integral (by positivity),mul_one]
  · intro y
    have hh : Integrable (fun q : V => A*heat (2*a*t) (y-q)) :=
      ((heat_integrable (by positivity : 0 < 2*a*t)).comp_sub_left y).const_mul A
    have hw : Continuous (fun q : V => VolterraBounds.weight n t q y) := by
      unfold VolterraBounds.weight
      fun_prop
    have hm : Integrable (fun q => VolterraBounds.weight n t q y * ‖K q y‖) := by
      have hk : Continuous (fun q => K q y) := hK.comp (continuous_id.prodMk continuous_const)
      apply hh.mono' ((hw.mul hk.norm).aestronglyMeasurable)
      filter_upwards [] with q
      change ‖VolterraBounds.weight n t q y * ‖K q y‖‖ ≤ A*heat (2*a*t) (y-q)
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (VolterraBounds.weight_pos n ht q y).le (norm_nonneg _))]
      exact hpoint q y
    refine ⟨hm,?_⟩
    calc
      _ ≤ ∫ q : V, A*heat (2*a*t) (y-q) := integral_mono hm hh (fun q => hpoint q y)
      _ = A := by rw [integral_const_mul,integral_sub_left_eq_self,heat_integral (by positivity),mul_one]

end TamingCompatibility.GeometricHilbert.FlatHeat

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

def coordinateMatrix (p : A.centers) (K : Space × Space → W →L[ℝ] W) (z : Space × Space) :
    FrameSpace A →L[ℝ] FrameSpace A :=
  coordinateEncode J α ht A D p z.2 ∘L K z ∘L coordinateDecode J α ht A D p z.1

omit [T2Space X] [CompactSpace X] in
lemma coordinateMatrix_support (p : A.centers) (K : Space × Space → W →L[ℝ] W) :
    Function.support (coordinateMatrix J α ht A D p K) ⊆ Function.support K := by
  intro z hz hK
  apply hz
  simp only [coordinateMatrix,hK,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]

include hD in
lemma coordinateMatrix_joint_smooth (hs : IsSmooth α) (p : A.centers)
    (K : ℝ → Space × Space → W →L[ℝ] W)
    (hKs : ∀ t, Function.support (K t) ⊆ (D p).physicalCompact)
    {t : ℝ} {z : Space × Space}
    (hK : ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => K v.1 v.2) (t,z)) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => coordinateMatrix J α ht A D p (K v.1) v.2) (t,z) := by
  by_cases hz : z ∈ (D p).physicalCompact
  · have hd := (D p).physicalCompact_domain hz
    have he := ((coordinateEncode_smooth J α ht A D hD hs p) _ hd.2).contDiffAt
      ((D p).chart.domain_open.mem_nhds hd.2)
    have hd' := ((coordinateDecode_smooth J α ht A D hD hs p) _ hd.1).contDiffAt
      ((D p).chart.domain_open.mem_nhds hd.1)
    exact ((he.comp (t,z) contDiffAt_snd.snd).clm_comp hK).clm_comp
      (hd'.comp (t,z) contDiffAt_snd.fst)
  · apply contDiffAt_const.congr_of_eventuallyEq
    have hn : {v : ℝ × (Space × Space) | v.2 ∉ (D p).physicalCompact} ∈ 𝓝 (t,z) :=
      (continuous_snd : Continuous (Prod.snd : ℝ × (Space × Space) → Space × Space)).continuousAt (x := (t,z)) |>.preimage_mem_nhds
        ((D p).physicalCompact_compact.isClosed.isOpen_compl.mem_nhds hz)
    filter_upwards [hn] with v hv
    apply Function.notMem_support.mp
    exact fun h => hv (hKs v.1 (coordinateMatrix_support J α ht A D p (K v.1) h))

include hD in
lemma coordinateMatrix_uniform_bound (hs : IsSmooth α) (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : Space × Space → W →L[ℝ] W,
      Function.support K ⊆ (D p).physicalCompact → ∀ z,
      ‖coordinateMatrix J α ht A D p K z‖ ≤ C*‖K z‖ := by
  have he : ContinuousOn (fun z : Space × Space => coordinateEncode J α ht A D p z.2)
      (D p).physicalCompact :=
    (coordinateEncode_smooth J α ht A D hD hs p).continuousOn.comp continuousOn_snd
      (fun z hz => ((D p).physicalCompact_domain hz).2)
  have hd' : ContinuousOn (fun z : Space × Space => coordinateDecode J α ht A D p z.1)
      (D p).physicalCompact :=
    (coordinateDecode_smooth J α ht A D hD hs p).continuousOn.comp continuousOn_fst
      (fun z hz => ((D p).physicalCompact_domain hz).1)
  obtain ⟨Ce,hCe⟩ := (D p).physicalCompact_compact.exists_bound_of_continuousOn he
  obtain ⟨Cd,hCd⟩ := (D p).physicalCompact_compact.exists_bound_of_continuousOn hd'
  refine ⟨max Ce 0*max Cd 0,mul_nonneg (le_max_right _ _) (le_max_right _ _),fun K hK z => ?_⟩
  by_cases hz : z ∈ (D p).physicalCompact
  · have hbE : ‖coordinateEncode J α ht A D p z.2‖ ≤ max Ce 0 := (hCe z hz).trans (le_max_left _ _)
    have hbD : ‖coordinateDecode J α ht A D p z.1‖ ≤ max Cd 0 := (hCd z hz).trans (le_max_left _ _)
    calc
      _ ≤ (‖coordinateEncode J α ht A D p z.2‖*‖K z‖)*‖coordinateDecode J α ht A D p z.1‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ (max Ce 0*‖K z‖)*max Cd 0 := mul_le_mul
        (mul_le_mul_of_nonneg_right hbE (norm_nonneg _)) hbD (norm_nonneg _)
        (mul_nonneg (le_max_right _ _) (norm_nonneg _))
      _ = _ := by ring
  · have hzero : K z = 0 := Function.notMem_support.mp (fun h => hz (hK h))
    simp only [coordinateMatrix,hzero,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp,norm_zero,mul_zero,le_refl]

def leadingMatrix (p : A.centers) (t : ℝ) : Space × Space → FrameSpace A →L[ℝ] FrameSpace A :=
  coordinateMatrix J α ht A D p (partitionLeading J α ht A D p t)

def residualMatrix (p : A.centers) (t : ℝ) : Space × Space → FrameSpace A →L[ℝ] FrameSpace A :=
  coordinateMatrix J α ht A D p (partitionResidual J α ht A D p t)

include hD in
lemma leadingMatrix_smooth (hs : IsSmooth α) (p : A.centers) {t : ℝ} (htp : 0 < t) (z : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => leadingMatrix J α ht A D p v.1 v.2) (t,z) :=
  coordinateMatrix_joint_smooth J α ht A D hD hs p _
    (fun t => (subset_tsupport _).trans (partitionLeading_tsupport J α ht A D hD p t))
    (partitionLeading_smooth J α ht A D hD hs p htp z)

include hD in
lemma residualMatrix_smooth (hs : IsSmooth α) (p : A.centers) {t : ℝ} (htp : 0 < t) (z : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => residualMatrix J α ht A D p v.1 v.2) (t,z) :=
  coordinateMatrix_joint_smooth J α ht A D hD hs p _
    (fun t => (subset_tsupport _).trans (partitionResidual_tsupport J α ht A D hD p t))
    (partitionResidual_smooth J α ht A D hD hs p htp z)

include hD in
lemma leadingMatrix_gaussian (hs : IsSmooth α) (p : A.centers) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 < L ∧ ∀ t : ℝ, 0 < t → ∀ q y : Space,
      ‖leadingMatrix J α ht A D p t (q,y)‖ ≤ M*FlatHeat.heat (L*t) (y-q) := by
  obtain ⟨L,hL,hb⟩ := partitionLeading_gaussian J α ht A D hD hs p
  obtain ⟨C,hC,hc⟩ := coordinateMatrix_uniform_bound J α ht A D hD hs p
  refine ⟨C*L^4,L^2,by positivity,by positivity,fun t htpos q y => ?_⟩
  refine (hc _ ((subset_tsupport _).trans (partitionLeading_tsupport J α ht A D hD p t)) (q,y)).trans ?_
  exact (mul_le_mul_of_nonneg_left (hb t htpos q y) hC).trans_eq (by ring)

include hD in
lemma residualFrameMatrix_gaussian (hs : IsSmooth α) (p : A.centers) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 < L ∧ ∀ t : ℝ, 0 < t → ∀ q y : Space,
      ‖residualMatrix J α ht A D p t (q,y)‖ ≤ M*FlatHeat.heat (L*t) (y-q) := by
  obtain ⟨M,L,hM,hL,hb⟩ := partitionResidual_gaussian J α ht A D hD hs p
  obtain ⟨C,hC,hc⟩ := coordinateMatrix_uniform_bound J α ht A D hD hs p
  refine ⟨C*M,L,mul_nonneg hC hM,hL,fun t htpos q y => ?_⟩
  refine (hc _ ((subset_tsupport _).trans (partitionResidual_tsupport J α ht A D hD p t)) (q,y)).trans ?_
  exact (mul_le_mul_of_nonneg_left (hb t htpos q y) hC).trans_eq (by ring)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
