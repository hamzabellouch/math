import OAI.Geometry.Kahler.BaseProjective

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def ProjectivelySeparated (ρ : ℝ) (P : Finset Sphere) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ρ ≤ projectiveDistance p q

def ProjectiveCover (ρ : ℝ) (P : Finset Sphere) : Prop :=
  ∀ ξ : Sphere, ∃ p ∈ P, projectiveDistance ξ p < ρ

def projectiveCap (p : Sphere) (s : ℝ) : Set Sphere := {ξ | projectiveDistance ξ p < s}

lemma projectiveCap_measurable (p : Sphere) (s : ℝ) : MeasurableSet (projectiveCap p s) :=
  (projectiveDistance_continuous p).measurable measurableSet_Iio

lemma projectiveCap_real (p : Sphere) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    sigma.real (projectiveCap p s) = s^2 := by
  rw [measureReal_def,projectiveCap,projective_cap_measure p hs hs1,ENNReal.toReal_ofReal (sq_nonneg _)]

lemma separated_caps_disjoint {ρ : ℝ} {P : Finset Sphere} (hP : ProjectivelySeparated ρ P) :
    (P : Set Sphere).PairwiseDisjoint (fun p => projectiveCap p (ρ/2)) := by
  intro p hp q hq hpq
  apply disjoint_left.mpr
  intro ξ hξp hξq
  have ht := projectiveDistance_triangle p ξ q
  rw [projectiveDistance_symm p ξ] at ht
  have hs := hP p hp q hq hpq
  change projectiveDistance ξ p < ρ/2 at hξp
  change projectiveDistance ξ q < ρ/2 at hξq
  linarith

lemma separated_card_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {P : Finset Sphere} (hP : ProjectivelySeparated ρ P) :
    (P.card:ℝ) ≤ 4/ρ^2 := by
  have hu := measureReal_mono (μ := sigma) (subset_univ (⋃ p ∈ P, projectiveCap p (ρ/2)))
  rw [measureReal_biUnion_finset (separated_caps_disjoint hP) (fun p _ => projectiveCap_measurable p _)] at hu
  simp_rw [projectiveCap_real _ (by linarith : 0 ≤ ρ/2) (by linarith : ρ/2 ≤ 1)] at hu
  simp only [Finset.sum_const,nsmul_eq_mul] at hu
  have hu1 : sigma.real univ = 1 := by simp [measureReal_def]
  rw [hu1] at hu
  apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
  nlinarith

lemma covering_card_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {P : Finset Sphere} (hP : ProjectiveCover ρ P) :
    1 ≤ (P.card:ℝ)*ρ^2 := by
  have he : (⋃ p ∈ P, projectiveCap p ρ) = univ := by
    ext ξ
    constructor
    · exact fun _ => mem_univ _
    · intro _
      obtain ⟨p,hp,hd⟩ := hP ξ
      exact mem_iUnion₂.mpr ⟨p,hp,hd⟩
  have hu := measureReal_biUnion_finset_le (μ := sigma) P (fun p => projectiveCap p ρ)
  rw [he] at hu
  have hu1 : sigma.real univ = 1 := by simp [measureReal_def]
  rw [hu1] at hu
  simpa only [projectiveCap_real _ hρ hρ1,Finset.sum_const,nsmul_eq_mul] using hu

lemma exists_separated_cover {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ P : Finset Sphere, ProjectivelySeparated ρ P ∧ ProjectiveCover ρ P := by
  classical
  let N := ⌈4/ρ^2⌉₊
  let B (n : ℕ) := ∃ P : Finset Sphere, ProjectivelySeparated ρ P ∧ P.card = n
  have hbound : ∀ P : Finset Sphere, ProjectivelySeparated ρ P → P.card ≤ N := by
    intro P hP
    exact_mod_cast (separated_card_bound hρ hρ1 hP).trans (Nat.le_ceil _)
  have hzero : B 0 := ⟨∅,by simp [ProjectivelySeparated],rfl⟩
  obtain ⟨P,hP,hcard⟩ := Nat.findGreatest_spec (Nat.zero_le N) hzero
  refine ⟨P,hP,?_⟩
  intro ξ
  by_contra hn
  push Not at hn
  have hξ : ξ ∉ P := by
    intro h
    have := hn ξ h
    rw [projectiveDistance_self] at this
    linarith
  have hi : ProjectivelySeparated ρ (insert ξ P) := by
    intro p hp q hq hpq
    rcases Finset.mem_insert.mp hp with he|hpp
    · subst p
      rcases Finset.mem_insert.mp hq with he|hqq
      · exact (hpq he.symm).elim
      · exact hn q hqq
    · rcases Finset.mem_insert.mp hq with he|hqq
      · subst q; rw [projectiveDistance_symm]; exact hn p hpp
      · exact hP p hpp q hqq hpq

  have hb : B (P.card+1) := ⟨insert ξ P,hi,Finset.card_insert_of_notMem hξ⟩
  have hle : P.card+1 ≤ N := by simpa only [Finset.card_insert_of_notMem hξ] using hbound (insert ξ P) hi
  have := Nat.le_findGreatest hle hb
  omega

lemma peak_count {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : D^2 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    (hcover : ProjectiveCover (D/Real.sqrt k) P) :
    (k:ℝ)/D^2 ≤ P.card ∧ (P.card:ℝ) ≤ 4*k/D^2 := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hk0 : (0:ℝ) < k := lt_of_lt_of_le (sq_pos_of_pos hD0) hk
  have hs : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr hk0
  have hρ : 0 < D/Real.sqrt (k:ℝ) := div_pos hD0 hs
  have hρ1 : D/Real.sqrt (k:ℝ) ≤ 1 := by
    apply (div_le_one hs).mpr
    exact (Real.le_sqrt hD0.le hk0.le).mpr hk
  have hu := separated_card_bound hρ hρ1 hP
  have hl := covering_card_bound hρ.le hρ1 hcover
  have he : (D/Real.sqrt (k:ℝ))^2 = D^2/k := by rw [div_pow,Real.sq_sqrt hk0.le]
  rw [he] at hu hl
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hD0)).mpr
    have := (le_div_iff₀ hk0).mp (show 1 ≤ (P.card:ℝ)*D^2/k by simpa only [mul_div_assoc] using hl)
    nlinarith
  · convert hu using 1
    field_simp

end PinchedHartogs.BaseConstruction

end

end OAI
