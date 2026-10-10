import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.Filters
import OAI.MathematicalPhysics.PEPSSubvolume.SpectralPowers

namespace OAI

/-! Attained positive Schatten-filter maxima by compactness. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.OptimizerExistence
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open Matrix PolynomialPEPS.Subvolume.SpectralCurve
variable {L q m : ℕ}

lemma compact_unitary (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    IsCompact (unitary (Matrix ι ι ℂ) : Set (Matrix ι ι ℂ)) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_unitary,?_⟩
  apply (Metric.isBounded_closedBall (x := (0 : Matrix ι ι ℂ)) (r := 1)).subset
  intro U hU
  simpa only [Metric.mem_closedBall,dist_zero_right,CStarRing.norm_of_mem_unitary hU] using (le_refl (1:ℝ))

abbrev Parameters (X : Finset (Vertex L)) :=
  unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ) ×
    Convexity.StdSimplex ℝ (RegionConfiguration q X)

lemma parameters_compact (hq : 0<q) (X : Finset (Vertex L)) :
    CompactSpace (Parameters (q := q) X) := by
  let : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  let : CompactSpace (unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)) :=
    isCompact_iff_compactSpace.mp (compact_unitary (RegionConfiguration q X))
  infer_instance

lemma parameters_nonempty (hq : 0<q) (X : Finset (Vertex L)) :
    Nonempty (Parameters (q := q) X) := by
  exact ⟨1,Convexity.StdSimplex.single (fun _ => (⟨0,hq⟩ : Fin q))⟩

lemma spectral_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) :
    (spectralHom U (fun i => (e i:ℂ))).PosSemidef := by
  exact (Matrix.PosSemidef.diagonal (fun i => Complex.nonneg_iff.mpr ⟨he i,rfl⟩)).mul_mul_conjTranspose_same
    (U : Matrix ι ι ℂ)

def fromParameters (X : Finset (Vertex L)) (a : ℝ) (t : Parameters (q := q) X) :
    LocalPositiveFilter q X where
  matrix := spectralHom t.1 (fun i => (((t.2.weights i)^(a/2):ℝ):ℂ))
  positive := spectral_positive t.1 _ (fun i => Real.rpow_nonneg (t.2.weights_nonneg i) _)

lemma fromParameters_feasible (X : Finset (Vertex L)) (a : ℝ) (ha : 0<a)
    (t : Parameters (q := q) X) : filterTracePower (fromParameters X a t) (2/a)=1 := by
  unfold filterTracePower
  have hs := sum_eigenvalues_spectralHom t.1 (fun i => (t.2.weights i)^(a/2))
    (fromParameters X a t).positive.isHermitian (fun r => r^(2/a))
  have hpow (i : RegionConfiguration q X) : ((t.2.weights i)^(a/2))^(2/a)=t.2.weights i := by
    rw [← Real.rpow_mul (t.2.weights_nonneg i)]
    have he : (a/2)*(2/a)=1 := by field_simp
    rw [he,Real.rpow_one]
  exact hs.trans (by simpa only [hpow] using t.2.total_of_fintype)

lemma fromParameters_continuous (X : Finset (Vertex L)) (a : ℝ) (ha : 0≤a) :
    Continuous (fun t : Parameters (q := q) X => (fromParameters X a t).matrix) := by
  unfold fromParameters spectralHom
  change Continuous (fun t : Parameters (q := q) X =>
    t.1.val * Matrix.diagonal (fun i => (((t.2.weights i)^(a/2):ℝ):ℂ)) * star t.1.val)
  apply Continuous.mul (Continuous.mul (continuous_subtype_val.comp continuous_fst) ?_)
    (continuous_subtype_val.comp continuous_fst).star
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by positivity)).comp
    ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp continuous_snd))

lemma represent_filter (X : Finset (Vertex L)) (a : ℝ) (ha : 0<a)
    (F : LocalPositiveFilter q X) (hF : filterTracePower F (2/a)=1) :
    ∃ t : Parameters (q := q) X, (fromParameters X a t).matrix=F.matrix := by
  let U := F.positive.isHermitian.eigenvectorUnitary
  let e := F.positive.isHermitian.eigenvalues
  let p := fun i => (e i)^(2/a)
  have hpos : ∀ i, 0≤e i := F.positive.eigenvalues_nonneg
  let simplex : Convexity.StdSimplex ℝ (RegionConfiguration q X) :=
    { weights := Finsupp.equivFunOnFinite.symm p
      nonneg := fun i => Real.rpow_nonneg (hpos i) _
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        exact hF }
  let t : Parameters (q := q) X := (U,simplex)
  refine ⟨t,?_⟩
  have hre (i : RegionConfiguration q X) : (p i)^(a/2)=e i := by
    change ((e i)^(2/a))^(a/2)=e i
    rw [← Real.rpow_mul (hpos i)]
    have he : (2/a)*(a/2)=1 := by field_simp
    rw [he,Real.rpow_one]
  change spectralHom U (fun i => (((p i)^(a/2):ℝ):ℂ))=F.matrix
  simp only [hre]
  exact F.positive.isHermitian.spectral_theorem.symm

lemma filter_ext {X : Finset (Vertex L)} (F G : LocalPositiveFilter q X)
    (h : F.matrix=G.matrix) : F=G := by
  cases F
  cases G
  cases h
  rfl

lemma continuous_liftLocal (X : Finset (Vertex L)) :
    Continuous (liftLocal (q := q) X) := by
  classical
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  unfold liftLocal
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const

lemma continuous_filtered_parameters {X : Fin m → Finset (Vertex L)}
    (a : Fin m → ℝ) (ha : ∀ j, 0≤a j) (ψ : State L q) :
    Continuous (fun t : (j : Fin m) → Parameters (q := q) (X j) =>
      ‖filteredVector (fun j => fromParameters (X j) (a j) (t j)) ψ‖) := by
  let T := (j : Fin m) → Parameters (q := q) (X j)
  let F (t : T) : FilterFamily q m X := fun j => fromParameters (X j) (a j) (t j)
  have hj (j : Fin m) : Continuous (fun t : T => liftLocal (X j) (F t j).matrix) :=
    (continuous_liftLocal (X j)).comp ((fromParameters_continuous (X j) (a j) (ha j)).comp
      (continuous_apply j))
  have hfold (l : List (Fin m)) : ∀ g : T → Operator L q, Continuous g →
      Continuous (fun t => l.foldl (fun P j => liftLocal (X j) (F t j).matrix*P) (g t)) := by
    induction l with
    | nil => intro g hg; exact hg
    | cons j l ih =>
      intro g hg
      exact ih (fun t => liftLocal (X j) (F t j).matrix*g t) ((hj j).mul hg)
  have hprod : Continuous (fun t : T => orderedFilterProduct (F t)) :=
    hfold (List.finRange m) (fun _ => 1) continuous_const
  have hmap : Continuous (fun A : Operator L q => asMap A ψ) :=
    ((Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional).clm_apply continuous_const
  exact (hmap.comp hprod).norm

theorem exists_optimizer (hq : 0<q) {X : Fin m → Finset (Vertex L)}
    (a : Fin m → ℝ) (ha : ∀ j, 0<a j) (ψ : State L q) :
    ∃ F : FilterFamily q m X, IsFilterOptimizer ψ a F := by
  classical
  let (j : Fin m) : CompactSpace (Parameters (q := q) (X j)) := parameters_compact hq (X j)
  let (j : Fin m) : Nonempty (Parameters (q := q) (X j)) := parameters_nonempty hq (X j)
  let T := (j : Fin m) → Parameters (q := q) (X j)
  let F (t : T) : FilterFamily q m X := fun j => fromParameters (X j) (a j) (t j)
  have hc := continuous_filtered_parameters (X := X) a (fun j => (ha j).le) ψ
  obtain ⟨t,ht,hmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set T).Nonempty)
    hc.continuousOn
  refine ⟨F t,fun j => fromParameters_feasible (X j) (a j) (ha j) (t j),?_⟩
  intro G hG
  choose s hs using fun j => represent_filter (X j) (a j) (ha j) (G j) (hG j)
  have heq : F s=G := by
    funext j
    exact filter_ext _ _ (hs j)
  have hb := hmax (Set.mem_univ s)
  change ‖filteredVector (F s) ψ‖≤‖filteredVector (F t) ψ‖ at hb
  rwa [heq] at hb

end PolynomialPEPS.Subvolume.OptimizerExistence

end

end OAI
