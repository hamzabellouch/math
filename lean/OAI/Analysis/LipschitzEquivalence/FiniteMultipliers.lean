import OAI.Analysis.LipschitzEquivalence.FiniteReduction

namespace OAI

universe uM uE

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem maps_agree_of_points {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T U : Space M →L[ℝ] E) {K : Set M} (he : ∀ x ∈ K, T (point x) = U (point x))
    {μ : Space M} (hμ : μ ∈ supported K) : T μ = U μ := by
  have hk : supported K ≤ (T-U).ker := by
    apply Submodule.topologicalClosure_minimal _ _ (ContinuousLinearMap.isClosed_ker _)
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    change T (point x)-U (point x) = 0
    exact sub_eq_zero.mpr (he x hx)
  exact sub_eq_zero.mp (hk hμ)

theorem norm_sub_apply_le_of_agree {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T U : Space M →L[ℝ] E) (μ ν : Space M) (he : T ν = U ν) :
    ‖T μ-U μ‖ ≤ (‖T‖+‖U‖)*‖μ-ν‖ := by
  have hid : T μ-U μ = T (μ-ν)-U (μ-ν) := by
    rw [map_sub,map_sub,he]
    abel
  rw [hid,add_mul]
  exact (_root_.norm_sub_le _ _).trans (add_le_add (T.le_opNorm _) (U.le_opNorm _))

def outerRadius (R : ℝ≥0) : ℝ≥0 := 2*R+2

theorem outerRadius_pos (R : ℝ≥0) : 0 < outerRadius R := by dsimp [outerRadius]; positivity

def radialMultiplier (R : ℝ≥0) : Space M →L[ℝ] Space M :=
  multiplier (cutoff 0 (outerRadius R))

theorem cutoff_abs_le_one (R : ℝ≥0) (x : M) : |cutoff 0 (outerRadius R) x| ≤ (1 : ℝ≥0) := by
  rw [abs_of_nonneg (cutoff_nonneg _ _ _)]
  exact cutoff_le_one _ _ _

theorem cutoff_radius_bound (R : ℝ≥0) (x : M) (hx : cutoff 0 (outerRadius R) x ≠ 0) :
    dist x 0 ≤ outerRadius R := by
  by_contra h
  exact hx (cutoff_zero 0 (outerRadius_pos R) (le_of_lt (lt_of_not_ge h)))

theorem radialMultiplier_point (R : ℝ≥0) (x : M) :
    radialMultiplier R (point x) = cutoff 0 (outerRadius R) x • point x :=
  multiplier_point _ (cutoff_lipschitz _ _) (cutoff_abs_le_one R) (cutoff_radius_bound R) x

theorem norm_radialMultiplier_le (R : ℝ≥0) : ‖radialMultiplier (M := M) R‖ ≤ 3 := by
  have h := norm_multiplier_le _ (cutoff_lipschitz (0 : M) (outerRadius R))
    (cutoff_abs_le_one R) (cutoff_radius_bound R)
  have hs : (outerRadius R : ℝ) ≠ 0 := ne_of_gt (outerRadius_pos R)
  change ‖radialMultiplier (M := M) R‖ ≤ (1 : ℝ)+((2 : ℝ)/(outerRadius R))*(outerRadius R) at h
  rw [div_mul_cancel₀ _ hs] at h
  norm_num at h
  exact h

theorem radialMultiplier_identity (R : ℝ≥0) {μ : Space M}
    (hμ : μ ∈ supported (Metric.closedBall 0 (R : ℝ))) : radialMultiplier R μ = μ := by
  apply multiplier_identity_on _ (cutoff_lipschitz _ _) (cutoff_abs_le_one R) (cutoff_radius_bound R) ?_ hμ
  intro x hx
  apply cutoff_one 0 (outerRadius_pos R)
  change dist x 0 ≤ (R : ℝ) at hx
  dsimp [outerRadius]
  linarith

theorem radialMultiplier_supported (R : ℝ≥0) (μ : Space M) :
    radialMultiplier R μ ∈ supported (Metric.closedBall 0 (outerRadius R : ℝ)) := by
  apply multiplier_supported _ (cutoff_lipschitz _ _) (cutoff_abs_le_one R) (cutoff_radius_bound R)
    (K := Set.univ) (fun x _ hx => cutoff_radius_bound R x hx)
  rw [supported_univ]
  trivial

theorem bounded_weak_approx {μ : ℕ → Space M} (hw : WeakSequences.WeakNull μ)
    {ε : ℝ} (hε : 0 < ε) : ∃ R : ℝ≥0, ∃ v : ℕ → Space M,
      WeakSequences.WeakNull v ∧ (∀ i, v i ∈ supported (Metric.closedBall 0 (R : ℝ))) ∧
      ∀ i, ‖μ i-v i‖ < ε := by
  obtain ⟨r,hr,happrox⟩ := uniform_radius_approx hw (show 0 < ε/8 by positivity)
  let R : ℝ≥0 := ⟨r,hr.le⟩
  let T : Space M →L[ℝ] Space M := radialMultiplier R
  refine ⟨outerRadius R,(fun i => T (μ i)),hw.map T,fun i => radialMultiplier_supported R (μ i),?_⟩
  intro i
  obtain ⟨ν,hν,herr⟩ := happrox i
  have he : (ContinuousLinearMap.id ℝ (Space M)) ν = T ν := (radialMultiplier_identity R hν).symm
  have hbound := norm_sub_apply_le_of_agree (ContinuousLinearMap.id ℝ (Space M)) T (μ i) ν he
  have hT := norm_radialMultiplier_le (M := M) R
  have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Space M)
  have hn := norm_nonneg (μ i-ν)
  change ‖μ i-T (μ i)‖ ≤ _ at hbound
  have hc : ‖ContinuousLinearMap.id ℝ (Space M)‖+‖T‖ ≤ 4 := by dsimp [T]; linarith
  exact (hbound.trans (mul_le_mul_of_nonneg_right hc hn)).trans_lt (by linarith)

def finiteCutoff (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) (x : M) : ℝ :=
  setCutoff (A : Set M) (2*δ) x * cutoff 0 (outerRadius R) x

def finiteCutoffLip (R δ : ℝ≥0) : ℝ≥0 := 2/(outerRadius R)+2/(2*δ)

def finiteMultiplier (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) : Space M →L[ℝ] Space M :=
  multiplier (finiteCutoff R A δ)

theorem finiteCutoff_lipschitz (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) :
    LipschitzWith (finiteCutoffLip R δ) (finiteCutoff R A δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := lipschitz_effective_smul (cutoff (0 : M) (outerRadius R)) (setCutoff (A : Set M) (2*δ))
      (cutoff_lipschitz _ _) (setCutoff_lipschitz _ _) (A := 1) (P := 1)
      (fun x => by rw [abs_of_nonneg (setCutoff_nonneg _ _ _)]; exact setCutoff_le_one _ _ _)
      (fun x _ => cutoff_abs_le_one R x)
  simpa only [finiteCutoffLip,finiteCutoff,one_mul,mul_one,smul_eq_mul] using h.dist_le_mul x y

theorem finiteCutoff_abs_le_one (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) (x : M) :
    |finiteCutoff R A δ x| ≤ (1 : ℝ≥0) := by
  rw [finiteCutoff,abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _)
    (by rw [abs_of_nonneg (setCutoff_nonneg _ _ _)]; exact setCutoff_le_one _ _ _)).trans
      (cutoff_abs_le_one R x)

theorem finiteCutoff_radius_bound (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) (x : M)
    (hx : finiteCutoff R A δ x ≠ 0) : dist x 0 ≤ outerRadius R :=
  cutoff_radius_bound R x (fun h => hx (by simp [finiteCutoff,h]))

theorem finiteMultiplier_point (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) (x : M) :
    finiteMultiplier R A δ (point x) = finiteCutoff R A δ x • point x :=
  multiplier_point _ (finiteCutoff_lipschitz R A δ) (finiteCutoff_abs_le_one R A δ)
    (finiteCutoff_radius_bound R A δ) x

def finiteMultiplierBound (R δ : ℝ≥0) : ℝ≥0 := 1+finiteCutoffLip R δ * outerRadius R

theorem norm_finiteMultiplier_le (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) :
    ‖finiteMultiplier R A δ‖ ≤ finiteMultiplierBound R δ :=
  norm_multiplier_le _ (finiteCutoff_lipschitz R A δ) (finiteCutoff_abs_le_one R A δ)
    (finiteCutoff_radius_bound R A δ)

theorem finiteMultiplier_agree (R : ℝ≥0) (A : Finset M) {δ : ℝ≥0} (hδ : 0 < δ)
    {ν : Space M} (hν : ν ∈ supported (Near A δ)) :
    finiteMultiplier R A δ ν = radialMultiplier R ν := by
  apply maps_agree_of_points _ _ ?_ hν
  rintro x ⟨a,ha,hxa⟩
  rw [finiteMultiplier_point,radialMultiplier_point]
  have hdist : Metric.infDist x (A : Set M) ≤ ((2*δ : ℝ≥0) : ℝ)/2 := by
    have h := (Metric.infDist_le_dist_of_mem ha).trans hxa
    simpa using h
  have hone := setCutoff_one (show 0 < 2*δ by positivity) hdist
  simp [finiteCutoff,hone]

theorem finiteMultiplier_support (R : ℝ≥0) (A : Finset M) (hA : (0 : M) ∈ A)
    {δ : ℝ≥0} (hδ : 0 < δ) {K : Set M} {μ : Space M} (hμ : μ ∈ supported K) :
    finiteMultiplier R A δ μ ∈ supported (K ∩ Near A (2*δ)) := by
  apply multiplier_supported _ (finiteCutoff_lipschitz R A δ) (finiteCutoff_abs_le_one R A δ)
    (finiteCutoff_radius_bound R A δ) ?_ hμ
  intro x hx hφ
  constructor
  · exact hx
  · have hnz : setCutoff (A : Set M) (2*δ) x ≠ 0 := fun h => hφ (by simp [finiteCutoff,h])
    obtain ⟨a,ha,hxa⟩ := (Metric.infDist_lt_iff (show (A : Set M).Nonempty from ⟨0,hA⟩)).mp
      (setCutoff_nonzero (show 0 < 2*δ by positivity) hnz)
    exact ⟨a,ha,hxa.le⟩

theorem finiteMultiplier_error (R : ℝ≥0) (A : Finset M) {δ : ℝ≥0} (hδ : 0 < δ)
    {μ ν : Space M} (hμ : μ ∈ supported (Metric.closedBall 0 (R : ℝ)))
    (hν : ν ∈ supported (Near A δ)) :
    ‖μ-finiteMultiplier R A δ μ‖ ≤ (3+finiteMultiplierBound R δ)*‖μ-ν‖ := by
  have h := norm_sub_apply_le_of_agree (radialMultiplier R) (finiteMultiplier R A δ) μ ν
    (finiteMultiplier_agree R A hδ hν).symm
  rw [radialMultiplier_identity R hμ] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (add_le_add (norm_radialMultiplier_le R) (norm_finiteMultiplier_le R A δ)) (norm_nonneg _))

end LipschitzCounterexample.FreeSpace

end

end OAI
