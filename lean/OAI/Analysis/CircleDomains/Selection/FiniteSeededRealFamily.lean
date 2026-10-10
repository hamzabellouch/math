import OAI.Analysis.CircleDomains.Selection.SeededGradedRealSelection
import OAI.Analysis.CircleDomains.Selection.SelectedRealFamily
import OAI.Analysis.CircleDomains.Selection.RealTestLevelData

namespace OAI

/-! Enumerate a prescribed finite prefix before the greedily selected tests,
retaining the actual functions and their ordered level compatibility. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

def finiteSeededRealFamily
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    {m : ℕ} (seed : Fin (m + 1) → UngatedRealTest d π EStar)
    (q : ℕ → Option (GradedRealTest d π EStar)) (n : ℕ) : UngatedRealTest d π EStar :=
  if h : n < m + 1 then seed ⟨n, h⟩
  else (q (n - (m + 1))).elim (seed 0) GradedRealTest.toUngatedRealTest

theorem finiteSeededRealFamily_prefix
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    {m : ℕ} (seed : Fin (m + 1) → UngatedRealTest d π EStar)
    (q : ℕ → Option (GradedRealTest d π EStar)) (i : Fin (m + 1)) :
    finiteSeededRealFamily seed q i.val = seed i := by
  simp only [finiteSeededRealFamily, dite_eq_left i.isLt]

theorem finiteSeededRealFamily_tail
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    {m : ℕ} (seed : Fin (m + 1) → UngatedRealTest d π EStar)
    (q : ℕ → Option (GradedRealTest d π EStar)) (n : ℕ) :
    finiteSeededRealFamily seed q (n + (m + 1)) =
      (q n).elim (seed 0) GradedRealTest.toUngatedRealTest := by
  simp only [finiteSeededRealFamily, show ¬n + (m + 1) < m + 1 by omega,
    dite_false, Nat.add_sub_cancel]

theorem exists_finite_seeded_real_family
    (d : PathCodeData Sphere Sphere) {π : Sphere → Sphere} {EStar : Set Sphere}
    {m : ℕ} (seed : Fin (m + 1) → UngatedRealTest d π EStar)
    (hzero : seed 0 = UngatedRealTest.zeroTest d π EStar)
    (hseed : ∀ (j : Fin (m + 1)) (n : ℕ) (labels : Fin n → Fin (m + 1)),
      (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ i, (seed i).exclusions)
          (circleBandGraph d.quotientDomain (seed j).coordinate.quotient)
          (fun i => circleBandGraph d.quotientDomain (seed i).coordinate.quotient) labels) = 0)
    (A : ℕ → Set (GradedRealTest d π EStar)) (hA0 : A 0 = ∅)
    (hmono : Monotone A) (hsingle : ∀ n, (A (n + 1) \ A n).Subsingleton)
    (hnew : ∀ n b, b ∈ A (n + 1) \ A n →
      GradedRealTest.AllowedWith (range seed) (A n) b) :
    ∃ (c : ℕ → UngatedRealTest d π EStar) (M : Set Sphere),
      M.Countable ∧ M ⊆ d.dust ∧ c 0 = UngatedRealTest.zeroTest d π EStar ∧
      (∀ i : Fin (m + 1), c i.val = seed i) ∧
      (∀ i, (c i).exclusions ∩ d.dust ⊆ M) ∧
      (∀ b ∈ ⋃ n, A n, ∃ k, c k = b.toUngatedRealTest) ∧
      range c ⊆ range seed ∪ GradedRealTest.toUngatedRealTest '' (⋃ n, A n) ∧
      OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M) := by
  classical
  obtain ⟨q, hq, hpref⟩ := exists_ordered_selection_slots A hA0 hmono hsingle
  let c := finiteSeededRealFamily seed q
  have hpre (i : Fin (m + 1)) : c i.val = seed i := finiteSeededRealFamily_prefix seed q i
  have htail (n : ℕ) : c (n + (m + 1)) =
      (q n).elim (seed 0) GradedRealTest.toUngatedRealTest :=
    finiteSeededRealFamily_tail seed q n
  let M : Set Sphere := (⋃ n, (c n).exclusions) ∩ d.dust
  have hM (i : ℕ) : (c i).exclusions ∩ d.dust ⊆ M :=
    fun _ hx => ⟨mem_iUnion.mpr ⟨i, hx.1⟩, hx.2⟩
  have hprevious {j i : ℕ} (hi : i < j + (m + 1)) :
      c i ∈ range seed ∪ GradedRealTest.toUngatedRealTest '' A j := by
    by_cases hip : i < m + 1
    · exact Or.inl ⟨⟨i, hip⟩, (hpre ⟨i, hip⟩).symm⟩
    · have hie : i = (i - (m + 1)) + (m + 1) := by omega
      rw [hie, htail]
      cases he : q (i - (m + 1)) with
      | none => exact Or.inl ⟨0, rfl⟩
      | some b =>
        exact Or.inr ⟨b, (hpref j b).mpr ⟨i - (m + 1), by omega, he⟩, rfl⟩
  refine ⟨c, M, (countable_iUnion fun i => (c i).exclusions_countable).mono
    inter_subset_left, inter_subset_right, (hpre 0).trans hzero, hpre, hM, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨n, hn⟩ := mem_iUnion.mp hb
    obtain ⟨k, _, hk⟩ := (hpref n b).mp hn
    exact ⟨k + (m + 1), (htail k).trans (by rw [hk]; rfl)⟩
  · rintro a ⟨i, rfl⟩
    have hp := hprevious (j := i) (i := i) (by omega)
    exact (union_subset_union_right _ (image_mono (subset_iUnion A i))) hp
  · intro j n labels hlt
    simp only [realTestLevelData.level_relation]
    by_cases hj : j < m + 1
    · let labels' (i : Fin n) : Fin (m + 1) := ⟨labels i, lt_trans (hlt i) hj⟩
      have hz := hseed ⟨j, hj⟩ n labels' (fun i => hlt i)
      rw [UngatedRealTest.freeComponentFailure_congr_selected
        (d.dust \ ⋃ i, (seed i).exclusions)
        (circleBandGraph d.quotientDomain (seed ⟨j, hj⟩).coordinate.quotient)
        (fun i : Fin (m + 1) => circleBandGraph d.quotientDomain (seed i).coordinate.quotient)
        (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient)
        labels' labels (fun i => congrArg (fun a : UngatedRealTest d π EStar =>
          circleBandGraph d.quotientDomain a.coordinate.quotient) (hpre (labels' i)).symm)] at hz
      rw [hpre ⟨j, hj⟩]
      apply measure_mono_null _ hz
      rintro _ ⟨⟨x, t, θ⟩, hx, rfl⟩
      refine ⟨(x, t, θ), ⟨⟨hx.1.1, ?_⟩, hx.2⟩, rfl⟩
      intro hxseed
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxseed
      exact hx.1.2 (hM i.val ⟨(hpre i).symm ▸ hi, hx.1.1⟩)
    · have hjr : j = (j - (m + 1)) + (m + 1) := by omega
      have hcj := htail (j - (m + 1))
      rw [← hjr] at hcj
      cases he : q (j - (m + 1)) with
      | none =>
        rw [he] at hcj
        rw [hcj, hzero]
        exact zero_coordinate_compatibility d.quotientDomain (d.dust \ M)
          (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient) n labels
      | some b =>
        rw [he] at hcj
        have hb := hnew (j - (m + 1)) b ((hq _ b).mp he)
        have hz := hb.2 n (fun i => c (labels i)) (fun i => hprevious (by have hi := hlt i; omega))
        rw [UngatedRealTest.freeComponentFailure_congr_selected
          (d.dust \ b.exclusions) (circleBandGraph d.quotientDomain b.coordinate.quotient)
          (fun i : Fin n => circleBandGraph d.quotientDomain (c (labels i)).coordinate.quotient)
          (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient)
          id labels (fun _ => rfl)] at hz
        rw [hcj]
        apply measure_mono_null _ hz
        rintro _ ⟨⟨x, t, θ⟩, hx, rfl⟩
        exact ⟨(x, t, θ), ⟨⟨hx.1.1, fun h => hx.1.2
          (hM j ⟨hcj.symm ▸ h, hx.1.1⟩)⟩, hx.2⟩, rfl⟩

end CircleDomainRigidity

end

end OAI
