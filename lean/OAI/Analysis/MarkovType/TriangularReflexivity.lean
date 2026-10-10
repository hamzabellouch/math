import OAI.Analysis.MarkovType.TriangularBasic
import OAI.Analysis.MarkovType.FiniteAnnihilator
import OAI.Analysis.MarkovType.FiniteMatching
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem exists_exact_triangular_with_value
    (v : StrongDual ℝ (StrongDual ℝ Y)) (hv : ‖v‖ ≤ 1)
    {d : ℝ} (hd : 0 < d)
    (hgap : d < Metric.infDist v
      (Set.range (NormedSpace.inclusionInDoubleDual ℝ Y))) (n : ℕ) :
    ∃ s : TriangularSystem Y n (d / 2), ∀ j, v (s.functionals j) = d := by
  classical
  induction n with
  | zero =>
      refine ⟨{
        vectors := Fin.elim0
        functionals := Fin.elim0
        vectors_bound := fun i => Fin.elim0 i
        functionals_bound := fun j => Fin.elim0 j
        pairing := fun i => Fin.elim0 i }, ?_⟩
      intro j
      exact Fin.elim0 j
  | succ n ih =>
      obtain ⟨s, hs⟩ := ih
      let E : Submodule ℝ Y := Submodule.span ℝ (Set.range s.vectors)
      let : FiniteDimensional ℝ E :=
        FiniteDimensional.span_of_finite ℝ (Set.finite_range s.vectors)
      obtain ⟨g, hg, hzero, hvalue⟩ := exists_annihilating_functional E v hd hgap
      have hg_old (i : Fin n) : g (s.vectors i) = 0 :=
        hzero ⟨s.vectors i, Submodule.subset_span ⟨i, rfl⟩⟩
      let f : Fin (n + 1) → StrongDual ℝ Y := Fin.snoc s.functionals g
      have hf_value (j : Fin (n + 1)) : v (f j) = d := by
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa only [f, Fin.snoc_last] using hvalue
        · simpa only [f, Fin.snoc_castSucc] using hs j
      have hf_bound (j : Fin (n + 1)) : ‖f j‖ ≤ 1 := by
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa only [f, Fin.snoc_last] using hg
        · simpa only [f, Fin.snoc_castSucc] using s.functionals_bound j
      obtain ⟨z, hz, hz_pair⟩ := finite_matching_unit v hv f (by norm_num : (0 : ℝ) < 1)
      have hz_bound : ‖(1 / 2 : ℝ) • z‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith
      have hz_value (j : Fin (n + 1)) : f j ((1 / 2 : ℝ) • z) = d / 2 := by
        rw [map_smul, hz_pair, hf_value, smul_eq_mul]
        ring
      refine ⟨{
        vectors := Fin.snoc s.vectors ((1 / 2 : ℝ) • z)
        functionals := f
        vectors_bound := ?_
        functionals_bound := hf_bound
        pairing := ?_ }, hf_value⟩
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa only [Fin.snoc_last] using hz_bound
        · simpa only [Fin.snoc_castSucc] using s.vectors_bound i
      · intro i j
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa only [Fin.snoc_last, ite_eq_left (Fin.le_last j)] using hz_value j
        · refine Fin.lastCases ?_ (fun j => ?_) j
          · simpa only [f, Fin.snoc_last, Fin.snoc_castSucc,
              ite_eq_right (not_le_of_gt (Fin.castSucc_lt_last i))] using hg_old i
          · simpa only [f, Fin.snoc_castSucc, Fin.castSucc_le_castSucc_iff] using
              s.pairing i j

theorem exists_exact_triangular_system_of_gap
    (v : StrongDual ℝ (StrongDual ℝ Y)) (hv : ‖v‖ ≤ 1)
    {d : ℝ} (hd : 0 < d)
    (hgap : d < Metric.infDist v
      (Set.range (NormedSpace.inclusionInDoubleDual ℝ Y))) (n : ℕ) :
    Nonempty (TriangularSystem Y n (d / 2)) := by
  obtain ⟨s, _⟩ := exists_exact_triangular_with_value v hv hd hgap n
  exact ⟨s⟩

theorem exists_uniform_exact_triangular_systems [CompleteSpace Y]
    (hNR : ¬ CanonicallyReflexive Y) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ n : ℕ, Nonempty (TriangularSystem Y n θ) := by
  obtain ⟨v, d, hv, hd, hgap⟩ := exists_bidual_gap hNR
  have hdist : Metric.infDist v
      (Set.range (NormedSpace.inclusionInDoubleDual ℝ Y)) ≤ ‖v‖ := by
    have hzero : (0 : StrongDual ℝ (StrongDual ℝ Y)) ∈
        Set.range (NormedSpace.inclusionInDoubleDual ℝ Y) := ⟨0, by simp⟩
    simpa only [dist_zero_right v] using Metric.infDist_le_dist_of_mem (x := v) hzero
  have hd1 : d < 1 := hgap.trans_le (hdist.trans hv)
  refine ⟨d / 2, by positivity, by linarith, ?_⟩
  exact fun n => exists_exact_triangular_system_of_gap v hv hd hgap n

namespace TriangularSystem

def mapFinitelyRepresentable {n : ℕ} {θ : ℝ}
    (s : TriangularSystem Y n θ) (hYX : FinitelyRepresentable Y X) :
    TriangularSystem X n (θ / 2) := by
  classical
  let E : Submodule ℝ Y := Submodule.span ℝ (Set.range s.vectors)
  letI : FiniteDimensional ℝ E :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range s.vectors)
  let x : Fin n → E := fun i => ⟨s.vectors i, Submodule.subset_span ⟨i, rfl⟩⟩
  let T : E →ₗ[ℝ] X := Classical.choose (hYX E 1 (by norm_num))
  have hT : ∀ z : E, ‖z‖ ≤ ‖T z‖ ∧ ‖T z‖ ≤ (1 + 1) * ‖z‖ :=
    Classical.choose_spec (hYX E 1 (by norm_num))
  have hTinj : Function.Injective T :=
    FinitelyRepresentable.injective_of_lower_bound T (fun z => (hT z).1)
  let R : Submodule ℝ X := LinearMap.range T
  let e : E ≃ₗ[ℝ] R := LinearEquiv.ofInjective T hTinj
  have hinv (z : R) : ‖e.symm z‖ ≤ ‖z‖ := by
    have heq : T (e.symm z) = (z : X) := LinearEquiv.ofInjective_symm_apply T z
    simpa only [heq, Submodule.norm_coe] using (hT (e.symm z)).1
  let inverse : R →L[ℝ] E := e.symm.toLinearMap.mkContinuous 1
    (fun z => by simpa only [one_mul, LinearEquiv.coe_toLinearMap, Submodule.norm_coe] using hinv z)
  let restricted (j : Fin n) : R →L[ℝ] ℝ :=
    (s.functionals j).comp (E.subtypeL.comp inverse)
  have hbound (j : Fin n) : ‖restricted j‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖s.functionals j (e.symm z : Y)‖ ≤ 1 * ‖z‖
    calc
      ‖s.functionals j (e.symm z : Y)‖ ≤
          ‖s.functionals j‖ * ‖(e.symm z : Y)‖ := (s.functionals j).le_opNorm _
      _ ≤ 1 * ‖e.symm z‖ :=
        mul_le_mul_of_nonneg_right (s.functionals_bound j) (norm_nonneg _)
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_left (hinv z) zero_le_one
  have hext (j : Fin n) : ∃ F : StrongDual ℝ X,
      (∀ z : R, F (z : X) = restricted j z) ∧ ‖F‖ ≤ 1 := by
    obtain ⟨F, hF, hnorm⟩ := exists_extension_norm_eq R (restricted j)
    exact ⟨F, hF, hnorm.trans_le (hbound j)⟩
  let F : Fin n → StrongDual ℝ X := fun j => Classical.choose (hext j)
  have hF (j : Fin n) : ∀ z : R, F j (z : X) = restricted j z :=
    (Classical.choose_spec (hext j)).1
  have hFnorm (j : Fin n) : ‖F j‖ ≤ 1 := (Classical.choose_spec (hext j)).2
  have hFpair (i j : Fin n) : F j (T (x i)) = s.functionals j (s.vectors i) := by
    have hz := hF j (e (x i))
    change F j (T (x i)) = s.functionals j (e.symm (e (x i)) : Y) at hz
    simpa only [e.symm_apply_apply] using hz
  refine {
    vectors := fun i => (1 / 2 : ℝ) • T (x i)
    functionals := F
    vectors_bound := ?_
    functionals_bound := hFnorm
    pairing := ?_ }
  · intro i
    have hxi : ‖x i‖ ≤ 1 := s.vectors_bound i
    have hTi := (hT (x i)).2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  · intro i j
    rw [map_smul, hFpair, s.pairing]
    by_cases hji : j ≤ i
    · simp only [ite_eq_left hji, smul_eq_mul]
      ring
    · simp only [ite_eq_right hji, smul_zero]

end TriangularSystem

theorem exists_uniform_triangular_systems_of_finitelyRepresentable
    [CompleteSpace Y] (hNR : ¬ CanonicallyReflexive Y)
    (hYX : FinitelyRepresentable Y X) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ n : ℕ, Nonempty (TriangularSystem X n θ) := by
  obtain ⟨θ, hθ, hθ1, hs⟩ := exists_uniform_exact_triangular_systems hNR
  refine ⟨θ / 2, by positivity, by linarith, ?_⟩
  intro n
  obtain ⟨s⟩ := hs n
  exact ⟨s.mapFinitelyRepresentable hYX⟩

theorem canonicallyReflexive_of_finitelyRepresentable_of_triangularObstruction
    [CompleteSpace Y] (hX : FiniteTriangularObstruction X)
    (hYX : FinitelyRepresentable Y X) : CanonicallyReflexive Y := by
  by_contra hNR
  obtain ⟨θ, hθ, hθ1, hs⟩ :=
    exists_uniform_triangular_systems_of_finitelyRepresentable hNR hYX
  obtain ⟨n, _, hn⟩ := hX θ hθ hθ1
  exact hn (hs n)

end MarkovSuperreflexivity

end

end OAI
