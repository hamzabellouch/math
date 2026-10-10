import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.FamilyMetric

namespace OAI

namespace MetricKMedianRecovery.FreshLeafTransfer
open PhaseHistoryTransfer FreshCopyEndpoints
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] in
lemma swap_original (u s : ℝ) (x : X) :
    Equiv.swap (Sum.inr u) (Sum.inr s) (incl x) = incl x := by
  classical
  apply Equiv.swap_apply_of_ne_of_ne <;> simp [incl]

omit [Fintype D] [PseudoMetricSpace X] in
lemma image_original (u s : ℝ) (B : Finset X) :
    (B.image incl).image (Equiv.swap (Sum.inr u) (Sum.inr s)) = B.image incl := by
  classical
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x _
  exact swap_original u s x

omit [Fintype D] [PseudoMetricSpace X] in
lemma image_copy (u s : ℝ) (B : Finset X) :
    (insert (Sum.inr u) (B.image incl)).image (Equiv.swap (Sum.inr u) (Sum.inr s)) =
      insert (Sum.inr s) (B.image incl) := by
  classical
  rw [Finset.image_insert,Equiv.swap_apply_left,image_original]

omit [Fintype D] in
lemma shortening (i x : X) (F B : Finset X) (u s : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
    ∀ y ∈ F.image incl ∪ insert (Sum.inr u) (B.image incl),
      dist (incl x) (Equiv.swap (Sum.inr u) (Sum.inr s) y) ≤ dist (incl x) y ∧
      dist (incl x) y ≤ dist (incl x) (Equiv.swap (Sum.inr u) (Sum.inr s) y)+(u-s) := by
  classical
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
  intro y hy
  rcases Finset.mem_union.mp hy with hy|hy
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
    rw [swap_original]
    exact ⟨le_rfl,le_add_of_nonneg_right (sub_nonneg.mpr hsu)⟩
  · rcases Finset.mem_insert.mp hy with rfl|hy
    · rw [Equiv.swap_apply_left,leaf_dist i,leaf_dist i,
        max_eq_left (hs.trans hsu),max_eq_left hs]
      constructor <;> linarith only [hsu]
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
      rw [swap_original]
      exact ⟨le_rfl,le_add_of_nonneg_right (sub_nonneg.mpr hsu)⟩

theorem terminal_transfer (loc : D → X) (F B : Finset X) (i : X)
    (u s v lam lam' eta zEnd : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*(u-s)) ≤ (Fintype.card D:ℝ)*eta)
    (hfar : ∀ j, ∀ x ∈ F, 1 ≤ dist x (loc j)) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
    ∀ T : List (List (X ⊕ ℝ)),
      History (fun j => incl (loc j)) (F.image incl) (insert (Sum.inr u) (B.image incl))
        v lam 0 0 ∅ T →
      (∀ j, ¬activeAt (fun j => incl (loc j)) (1-3*v) zEnd (after ∅ T) j) →
      ∃ T' : List (List (X ⊕ ℝ)), T'.length = T.length ∧
        History (fun j => incl (loc j)) (F.image incl) (insert (Sum.inr s) (B.image incl))
          v lam' eta 0 ∅ T' ∧
        (∀ j, ¬activeAt (fun j => incl (loc j)) (1-3*v) zEnd (after ∅ T') j) ∧
        ((after ∅ T') ∩ F.image incl).card = ((after ∅ T) ∩ F.image incl).card ∧
        ∀ H ∈ T, ((H.map (Equiv.swap (Sum.inr u) (Sum.inr s))).toFinset \ F.image incl).card =
          (H.toFinset \ F.image incl).card := by
  classical
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
  intro T hh hterm
  have hfix : ∀ x ∈ F.image (incl : X ↪ X ⊕ ℝ),
      Equiv.swap (Sum.inr u) (Sum.inr s) x = x := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact swap_original u s a
  have hfar' : ∀ j, ∀ x ∈ F.image (incl : X ↪ X ⊕ ℝ), 1 ≤ dist x (incl (loc j)) := by
    intro j x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [original_dist i]
    exact hfar j a ha
  obtain ⟨hvalid,hterm',hpaid,hfree⟩ := terminal_history_map (fun j => incl (loc j))
    (F.image incl) (insert (Sum.inr u) (B.image incl)) T (Equiv.swap (Sum.inr u) (Sum.inr s))
    v lam lam' eta (u-s) zEnd hv hvsmall hlam (sub_nonneg.mpr hsu) hprice herror
    (Equiv.swap _ _).injective hfix
    (fun j y hy => (shortening i (loc j) F B u s hs hsu y hy).1)
    (fun j y hy => (shortening i (loc j) F B u s hs hsu y hy).2)
    hfar' hh hterm
  rw [image_copy] at hvalid
  exact ⟨T.map (List.map (Equiv.swap (Sum.inr u) (Sum.inr s))),by simp only [List.length_map],
    hvalid,hterm',hpaid,hfree⟩

end MetricKMedianRecovery.FreshLeafTransfer

end OAI
