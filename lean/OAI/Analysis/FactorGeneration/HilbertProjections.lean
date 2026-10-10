import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Semicontinuity.Basic

namespace OAI

noncomputable section

namespace Generator

/-! Baire continuity points from rational sublevel boundaries, without a global boundedness assumption. -/
section
open Set Filter Topology
variable {X : Type*} [TopologicalSpace X]

/-- An explicit countable intersection of open sets of continuity points. -/
def continuityCore (f : X → ℝ) : Set X :=
  ⋂ q : ℚ, (frontier {x | f x ≤ (q : ℝ)})ᶜ

theorem continuityCore_isGδ (f : X → ℝ) : IsGδ (continuityCore f) :=
  IsGδ.iInter_of_isOpen fun _ => isClosed_frontier.isOpen_compl

theorem continuityCore_dense [BaireSpace X] {f : X → ℝ}
    (hf : LowerSemicontinuous f) : Dense (continuityCore f) := by
  apply dense_iInter_of_isOpen (fun _ => isClosed_frontier.isOpen_compl)
  intro q
  exact interior_eq_empty_iff_dense_compl.mp (interior_frontier (hf.isClosed_preimage q))

theorem continuousAt_of_mem_continuityCore {f : X → ℝ}
    (hf : LowerSemicontinuous f) {x : X} (hx : x ∈ continuityCore f) :
    ContinuousAt f x := by
  apply continuousAt_iff_lower_upperSemicontinuousAt.mpr
  refine ⟨hf x, ?_⟩
  intro b hb
  obtain ⟨q, hxq, hqb⟩ := exists_rat_btwn hb
  have hnot : x ∉ frontier {y | f y ≤ (q : ℝ)} := Set.mem_iInter.mp hx q
  have hint : x ∈ interior {y | f y ≤ (q : ℝ)} :=
    (mem_interior_iff_notMem_frontier (show x ∈ {y | f y ≤ (q : ℝ)} from hxq.le)).mpr hnot
  have hnhds : {y | f y ≤ (q : ℝ)} ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hint
  exact Filter.mem_of_superset hnhds fun y hy => lt_of_le_of_lt hy hqb

/-- The common continuity set for a countable family, as used before
extending the projection-norm conclusion to all L2 vectors. -/
theorem common_continuity_core [BaireSpace X] (f : ℕ → X → ℝ)
    (hf : ∀ n, LowerSemicontinuous (f n)) :
    ∃ C : Set X, IsGδ C ∧ Dense C ∧ ∀ x ∈ C, ∀ n, ContinuousAt (f n) x := by
  refine ⟨⋂ n, continuityCore (f n), IsGδ.iInter (fun n => continuityCore_isGδ (f n)),
    dense_iInter_of_Gδ (fun n => continuityCore_isGδ (f n))
      (fun n => continuityCore_dense (hf n)), ?_⟩
  intro x hx n
  exact continuousAt_of_mem_continuityCore (hf n) (Set.mem_iInter.mp hx n)

/-- The uniform Lipschitz estimate in the vector variable extends continuity
from a dense sequence to every vector (eq:projection-vector-lipschitz). -/
theorem continuousAt_of_dense_lipschitz {E : Type*} [PseudoMetricSpace E]
    (F : E → X → ℝ) (e : ℕ → E) (he : DenseRange e)
    (hLip : ∀ x a b, dist (F a x) (F b x) ≤ dist a b)
    {x : X} (hcont : ∀ n, ContinuousAt (F (e n)) x) (a : E) :
    ContinuousAt (F a) x := by
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨n, hn⟩ := he.exists_dist_lt a (show 0 < ε / 3 by linarith)
  have hncont := Metric.continuousAt_iff'.mp (hcont n) (ε / 3) (by linarith)
  filter_upwards [hncont] with y hy
  have hleft := hLip y a (e n)
  have hright := hLip x (e n) a
  rw [dist_comm (e n) a] at hright
  calc
    dist (F a y) (F a x) ≤ dist (F a y) (F (e n) y) +
        dist (F (e n) y) (F a x) := dist_triangle _ _ _
    _ ≤ dist (F a y) (F (e n) y) +
        (dist (F (e n) y) (F (e n) x) + dist (F (e n) x) (F a x)) :=
      by linarith [dist_triangle (F (e n) y) (F (e n) x) (F a x)]
    _ < ε := by linarith

/-- Baire continuity of a family of Hilbert-space projections. -/
theorem common_continuity_of_lipschitz [BaireSpace X]
    {E : Type*} [PseudoMetricSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]
    (F : E → X → ℝ) (hf : ∀ a, LowerSemicontinuous (F a))
    (hLip : ∀ x a b, dist (F a x) (F b x) ≤ dist a b) :
    ∃ C : Set X, IsGδ C ∧ Dense C ∧ ∀ x ∈ C, ∀ a, ContinuousAt (F a) x := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq (α := E)
  obtain ⟨C, hG, hd, hC⟩ := common_continuity_core (fun n => F (e n)) (fun n => hf (e n))
  exact ⟨C, hG, hd, fun x hx a => continuousAt_of_dense_lipschitz F e he hLip (hC x hx) a⟩

end

/-! Hilbert-space projection and correlation identities. The inner product is conjugate-linear in its first argument, so `inner ℂ ξ W` represents τ(ξ* W). -/
section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (K : Submodule ℂ E) [K.HasOrthogonalProjection]

def projectionNorm (ξ : E) : ℝ := ‖K.starProjection ξ‖

theorem projectionNorm_bounds (ξ : E) :
    0 ≤ projectionNorm K ξ ∧ projectionNorm K ξ ≤ ‖ξ‖ :=
  ⟨norm_nonneg _, K.norm_starProjection_apply_le ξ⟩

theorem projectionNorm_lipschitz (ξ η : E) :
    dist (projectionNorm K ξ) (projectionNorm K η) ≤ dist ξ η := by
  calc
    dist (projectionNorm K ξ) (projectionNorm K η) ≤
        dist (K.starProjection ξ) (K.starProjection η) := by
      simpa only [projectionNorm, dist_eq_norm] using
        dist_norm_norm_le (K.starProjection ξ) (K.starProjection η)
    _ ≤ dist ξ η := by
      simp only [dist_eq_norm, ← map_sub]
      exact K.norm_starProjection_apply_le (ξ - η)

theorem correlation_le_projectionNorm (ξ W : E) (hW : W ∈ K) (hunit : ‖W‖ = 1) :
    ‖inner ℂ ξ W‖ ≤ projectionNorm K ξ := by
  have hfix : K.starProjection W = W := K.starProjection_eq_self_iff.mpr hW
  have hi : inner ℂ (K.starProjection ξ) W = inner ℂ ξ W := by
    rw [K.inner_starProjection_left_eq_right, hfix]
  rw [← hi]
  simpa [projectionNorm, hunit] using norm_inner_le_norm (K.starProjection ξ) W

def residual (z : E) : E := z - K.starProjection z

theorem residual_projection_zero (z : E) : K.starProjection (residual K z) = 0 := by
  apply K.starProjection_apply_eq_zero_iff.mpr
  exact K.sub_starProjection_mem_orthogonal z

theorem residual_norm_pos {z : E} (hz : z ∉ K) : 0 < ‖residual K z‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have heq : z = K.starProjection z := sub_eq_zero.mp hzero
  exact hz (heq.symm ▸ K.starProjection_apply_mem z)

theorem residual_correlation (z : E) :
    inner ℂ (residual K z) z = (‖residual K z‖ : ℂ) ^ 2 := by
  have horth : inner ℂ (residual K z) (K.starProjection z) = 0 :=
    K.starProjection_inner_eq_zero z _ (K.starProjection_apply_mem z)
  have hself := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (residual K z)
  calc
    inner ℂ (residual K z) z =
        inner ℂ (residual K z) (residual K z + K.starProjection z) := by
      simp only [residual, sub_add_cancel]
    _ = inner ℂ (residual K z) (residual K z) := by rw [inner_add_right, horth, add_zero]
    _ = _ := hself

/-- Instantiation of the topological theorem with actual orthogonal projections.
Lower semicontinuity remains an explicit prerequisite to prove for W*(P,u). -/
theorem common_projectionNorm_continuity {X : Type*} [TopologicalSpace X] [BaireSpace X]
    [TopologicalSpace.SeparableSpace E] (L : X → Submodule ℂ E)
    [∀ x, (L x).HasOrthogonalProjection]
    (hsemi : ∀ ξ, LowerSemicontinuous (fun x => projectionNorm (L x) ξ)) :
    ∃ C : Set X, IsGδ C ∧ Dense C ∧
      ∀ x ∈ C, ∀ ξ, ContinuousAt (fun y => projectionNorm (L y) ξ) x :=
  common_continuity_of_lipschitz (fun ξ x => projectionNorm (L x) ξ) hsemi
    (fun x ξ η => projectionNorm_lipschitz (L x) ξ η)

end

/-! Lower semicontinuity from a continuous family dense in each projected subspace. -/
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def normalizedCorrelation (ξ w : E) : ℝ := ‖inner ℂ ξ w‖ / ‖w‖

theorem normalizedCorrelation_continuousAt (ξ : E) {w : E} (hw : w ≠ 0) :
    ContinuousAt (normalizedCorrelation ξ) w := by
  exact (continuous_const.inner continuous_id).norm.continuousAt.div
    continuous_norm.continuousAt (norm_ne_zero_iff.mpr hw)

theorem normalizedCorrelation_le_projectionNorm (K : Submodule ℂ E)
    [K.HasOrthogonalProjection] (ξ w : E) (hw : w ∈ K) :
    normalizedCorrelation ξ w ≤ projectionNorm K ξ := by
  by_cases hzero : w = 0
  · simpa [normalizedCorrelation, hzero] using (projectionNorm_bounds K ξ).1
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hzero
  apply (div_le_iff₀ hnorm).mpr
  have hfix : K.starProjection w = w := K.starProjection_eq_self_iff.mpr hw
  have hi : inner ℂ (K.starProjection ξ) w = inner ℂ ξ w := by
    rw [K.inner_starProjection_left_eq_right, hfix]
  rw [← hi]
  exact norm_inner_le_norm _ _

theorem normalizedCorrelation_starProjection (K : Submodule ℂ E)
    [K.HasOrthogonalProjection] (ξ : E) :
    normalizedCorrelation ξ (K.starProjection ξ) = projectionNorm K ξ := by
  by_cases hz : K.starProjection ξ = 0
  · simp [normalizedCorrelation, projectionNorm, hz]
  have hfix : K.starProjection (K.starProjection ξ) = K.starProjection ξ :=
    K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem ξ)
  have hi : inner ℂ (K.starProjection ξ) (K.starProjection ξ) =
      inner ℂ ξ (K.starProjection ξ) := by
    rw [K.inner_starProjection_left_eq_right, hfix]
  rw [normalizedCorrelation, ← hi, inner_self_eq_norm_sq_to_K]
  simp [projectionNorm, Complex.norm_real, pow_two, norm_ne_zero_iff.mpr hz]

/-- Dense continuous sections imply lower semicontinuity of every projection norm.
The index type need not be countable, matching the P-coefficient polynomials. -/
theorem projectionNorm_lowerSemicontinuous {X I : Type*} [TopologicalSpace X]
    (L : X → Submodule ℂ E) [∀ x, (L x).HasOrthogonalProjection]
    (b : I → X → E) (hb : ∀ i x, b i x ∈ L x) (hc : ∀ i, Continuous (b i))
    (hd : ∀ x, DenseRange (fun i => (⟨b i x, hb i x⟩ : L x))) (ξ : E) :
    LowerSemicontinuous (fun x => projectionNorm (L x) ξ) := by
  intro x r hr
  by_cases hneg : r < 0
  · exact Filter.Eventually.of_forall fun y => hneg.trans_le (projectionNorm_bounds (L y) ξ).1
  have hr0 : 0 ≤ r := le_of_not_gt hneg
  have hp : 0 < projectionNorm (L x) ξ := lt_of_le_of_lt hr0 hr
  have hv : (L x).starProjection ξ ≠ 0 := norm_pos_iff.mp hp
  have hqcont := normalizedCorrelation_continuousAt ξ hv
  have hqvalue := normalizedCorrelation_starProjection (L x) ξ
  obtain ⟨δ, hδ, hδprop⟩ := Metric.continuousAt_iff.mp hqcont
    ((projectionNorm (L x) ξ - r) / 2) (by linarith)
  obtain ⟨i, hi⟩ := (hd x).exists_dist_lt ((L x).orthogonalProjectionOnto ξ) hδ
  have hidist : dist (b i x) ((L x).starProjection ξ) < δ := by
    simpa only [Submodule.starProjection_apply, Subtype.dist_eq, dist_comm] using hi
  have hiq : r < normalizedCorrelation ξ (b i x) := by
    have ht := hδprop hidist
    rw [hqvalue, Real.dist_eq] at ht
    have hl := (abs_lt.mp ht).1
    linarith
  have hbinz : b i x ≠ 0 := by
    intro hz
    simp [normalizedCorrelation, hz] at hiq
    linarith
  have hbq : ContinuousAt (fun y => normalizedCorrelation ξ (b i y)) x :=
    (normalizedCorrelation_continuousAt ξ hbinz).comp (hc i).continuousAt
  have hevent : ∀ᶠ y in 𝓝 x, r < normalizedCorrelation ξ (b i y) :=
    hbq (Ioi_mem_nhds hiq)
  exact hevent.mono fun y hy =>
    hy.trans_le (normalizedCorrelation_le_projectionNorm (L y) ξ (b i y) (hb i y))

/-- The generic Hilbert-space content of lem:projection-continuity, with
semicontinuity proved from dense continuous sections rather than assumed. -/
theorem common_projectionNorm_continuity_of_denseSections
    {X I : Type*} [TopologicalSpace X] [BaireSpace X]
    [TopologicalSpace.SeparableSpace E]
    (L : X → Submodule ℂ E) [∀ x, (L x).HasOrthogonalProjection]
    (b : I → X → E) (hb : ∀ i x, b i x ∈ L x) (hc : ∀ i, Continuous (b i))
    (hd : ∀ x, DenseRange (fun i => (⟨b i x, hb i x⟩ : L x))) :
    ∃ C : Set X, IsGδ C ∧ Dense C ∧
      ∀ x ∈ C, ∀ ξ, ContinuousAt (fun y => projectionNorm (L y) ξ) x :=
  common_projectionNorm_continuity L (projectionNorm_lowerSemicontinuous L b hb hc hd)

end Generator

end

end OAI
