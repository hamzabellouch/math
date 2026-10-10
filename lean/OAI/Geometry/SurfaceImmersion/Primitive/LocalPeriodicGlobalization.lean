import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicFamilies
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicFamilies
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicTriangularRecursion
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicFiniteAnsatz

namespace OAI

/-! Compactly supported local periodic coefficients extend smoothly by zero. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Closed support lying inside the admissible domain suffices for smooth
extension; there is no regularity requirement on the domain boundary. -/
lemma contDiff_of_zero_off_closed {F : A × ℝ → E} {O K : Set A}
    (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F (O ×ˢ Set.univ))
    (hK : IsClosed K) (hKO : K ⊆ O) (hz : ∀ p ∉ K, ∀ t, F (p, t) = 0) :
    ContDiff ℝ ∞ F := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hp : z.1 ∈ O
  · exact hF.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ z.2⟩)
  · have hpK : z.1 ∉ K := fun hk => hp (hKO hk)
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(continuous_fst.continuousAt :
      Filter.Tendsto Prod.fst (𝓝 z) (𝓝 z.1)).eventually (hK.isOpen_compl.mem_nhds hpK)] with w hw
    exact hz w.1 hw w.2

namespace Family
variable {O : TopologicalSpace.Opens A}

lemma smooth_global (F : Family O E) {K : Set A} (hK : IsClosed K) (hKO : K ⊆ O)
    (hz : ∀ p ∈ O, p ∉ K → F.val p = 0) :
    ContDiff ℝ ∞ (fun z : A × ℝ => F.val z.1 (z.2 : Period)) := by
  apply contDiff_of_zero_off_closed O.isOpen F.smooth hK hKO
  intro p hp t
  by_cases hpO : p ∈ O
  · rw [hz p hpO hp]
    rfl
  · rw [F.outside hpO]
    rfl

def global (F : Family O E) {K : Set A} (hK : IsClosed K) (hKO : K ⊆ O)
    (hz : ∀ p ∈ O, p ∉ K → F.val p = 0) : PeriodicExpansion.Family A E :=
  ⟨F.val, F.smooth_global hK hKO hz⟩

@[simp] lemma global_apply (F : Family O E) {K : Set A} (hK : IsClosed K) (hKO : K ⊆ O)
    (hz : ∀ p ∈ O, p ∉ K → F.val p = 0) (p : A) (t : Period) :
    (F.global hK hKO hz).val p t = F.val p t := rfl

end Family

variable [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

/-- The local recursion gives globally smooth coefficients when its initial
input is supported in a closed subset of the admissible domain. -/
theorem Geometry.exists_supported_coefficients {v : A} (g : Geometry (E := E) O v)
    (dx : A) (n : ℕ) {K : Set A} (hK : IsClosed K) (hKO : K ⊆ O)
    (hz : ∀ p ∈ O, p ∉ K → g.initial.val p = 0) :
    ∃ U : ℕ → Family O E,
      U 0 = g.initial ∧ (∀ i p, p ∈ O → average ((U i).val p) = 0) ∧
      (∀ i, ContDiff ℝ ∞ (fun z : A × ℝ => (U i).val z.1 (z.2 : Period))) ∧
      (∀ i p, p ∉ K → (U i).val p = 0) ∧
      (g.yyCoefficient U 1).fluct = 0 ∧
      ∀ r, 1 ≤ r → r ≤ n →
        (g.xxCoefficient dx U r).fluct = 0 ∧
        (g.xyCoefficient dx U r).fluct = 0 ∧
        (g.yyCoefficient U (r + 1)).fluct = 0 := by
  obtain ⟨U, hinit, hmean, hy, hs, hc⟩ := g.exists_coefficients dx n
  have hzero : ∀ i p, p ∈ O → p ∉ K → (U i).val p = 0 := by
    intro i p hp hk
    exact hs ((O : Set A) ∩ Kᶜ) (O.isOpen.inter hK.isOpen_compl)
      Set.inter_subset_left (fun q hq => hz q hq.1 hq.2) i p ⟨hp, hk⟩
  refine ⟨U, hinit, hmean, ?_, ?_, hy, hc⟩
  · intro i
    exact (U i).smooth_global hK hKO (hzero i)
  · intro i p hp
    by_cases hpO : p ∈ O
    · exact hzero i p hpO hp
    · exact (U i).outside hpO

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma finiteAnsatz_smooth_global {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family O E) {K : Set A} (hK : IsClosed K) (hKO : K ⊆ O)
    (hz : ∀ i p, p ∈ O → p ∉ K → (U i).val p = 0)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    ContDiff ℝ ∞ (finiteAnsatz F U ℓ L z) := by
  apply hF.add
  apply ContDiff.sum
  intro i _
  exact contDiff_const.smul (((U i).smooth_global hK hKO (hz i)).comp
    (contDiff_id.prodMk (ℓ.contDiff.div_const z)))

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma finiteAnsatz_eq_off_support (F : A → E) (U : ℕ → Family O E)
    {K : Set A} (hz : ∀ i p, p ∉ K → (U i).val p = 0)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) {p : A} (hp : p ∉ K) :
    finiteAnsatz F U ℓ L z p = F p := by
  simp only [finiteAnsatz, Family.fastValue, hz _ p hp, ContinuousMap.zero_apply,
    smul_zero, Finset.sum_const_zero, add_zero]

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
