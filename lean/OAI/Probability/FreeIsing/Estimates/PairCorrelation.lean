import OAI.Probability.FreeIsing.Estimates.FreeLawStationarity
import OAI.Probability.FreeIsing.Trees.RootCorrelation
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

def reducedWordDistance {α : Type*} [DecidableEq α] : List α → List α → ℕ
  | [], v => v.length
  | u, [] => u.length
  | a :: u, b :: v => if a = b then reducedWordDistance u v else u.length + v.length + 2

@[simp] theorem reducedWordDistance_nil_left {α : Type*} [DecidableEq α] (v : List α) :
    reducedWordDistance [] v = v.length := rfl

@[simp] theorem reducedWordDistance_nil_right {α : Type*} [DecidableEq α] (u : List α) :
    reducedWordDistance u [] = u.length := by cases u <;> rfl

@[simp] theorem reducedWordDistance_cons_same {α : Type*} [DecidableEq α]
    (a : α) (u v : List α) :
    reducedWordDistance (a::u) (a::v) = reducedWordDistance u v := by
  simp [reducedWordDistance]

theorem reducedWordDistance_cons_ne {α : Type*} [DecidableEq α]
    {a b : α} (hab : a ≠ b) (u v : List α) :
    reducedWordDistance (a::u) (b::v) = u.length + v.length + 2 := by
  simp only [reducedWordDistance, ite_eq_right hab]

theorem reducedWordDistance_symm {α : Type*} [DecidableEq α] (u v : List α) :
    reducedWordDistance u v = reducedWordDistance v u := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    cases v with
    | nil => simp
    | cons b v =>
      by_cases hab : a=b
      · subst b
        simpa using ih v
      · simp [reducedWordDistance, hab, Ne.symm hab, Nat.add_comm]

@[simp] theorem reducedWordDistance_self {α : Type*} [DecidableEq α] (u : List α) :
    reducedWordDistance u u = 0 := by
  induction u with
  | nil => rfl
  | cons a u ih => simpa using ih

theorem reducedWordDistance_move_head {α : Type*} [DecidableEq α]
    (a b : α) (u v : List α) (hab : a ≠ b)
    (hu : List.IsChain (fun x y : α => x ≠ y) (a::u)) :
    reducedWordDistance u (a::b::v) = reducedWordDistance (a::u) (b::v) := by
  rw [reducedWordDistance_cons_ne hab]
  cases u with
  | nil => simp
  | cons c u =>
    have hac : a ≠ c := (List.isChain_cons_cons.mp hu).1
    rw [reducedWordDistance_cons_ne hac.symm]
    simp only [List.length_cons]
    omega

private theorem freeLaw_correlation_lists {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (u v : List (Fin d))
    (hu : List.IsChain (fun a b : Fin d => a ≠ b) u)
    (hv : List.IsChain (fun a b : Fin d => a ≠ b) v) :
    ∫ x, spinSign (x ⟨u,hu⟩) * spinSign (x ⟨v,hv⟩) ∂mu =
      theta ^ reducedWordDistance u v := by
  induction u generalizing v with
  | nil =>
    exact hmu.root_correlation hlo hhi ⟨v,hv⟩
  | cons a u ih =>
    cases v with
    | nil =>
      simpa [reducedWordDistance_nil_right, ConnectedHull.root, mul_comm] using
        hmu.root_correlation hlo hhi ⟨a::u,hu⟩
    | cons b v =>
      have huFlip : prefixFlip a (⟨a::u,hu⟩ : TreeVertex d) = ⟨u,hu.tail⟩ := by
        apply Subtype.ext
        simp [prefixFlip, prefixFlipWord]
      have hshift := hmu.integral_pair_image (prefixTreeAut a)
        (fun s t => spinSign s * spinSign t) ⟨a::u,hu⟩ ⟨b::v,hv⟩
      change (∫ x, spinSign (x (prefixFlip a ⟨a::u,hu⟩)) *
        spinSign (x (prefixFlip a ⟨b::v,hv⟩)) ∂mu) = _ at hshift
      rw [huFlip] at hshift
      rw [←hshift]
      by_cases hab : a=b
      · subst b
        have hvFlip : prefixFlip a (⟨a::v,hv⟩ : TreeVertex d) = ⟨v,hv.tail⟩ := by
          apply Subtype.ext
          simp [prefixFlip, prefixFlipWord]
        rw [hvFlip, reducedWordDistance_cons_same]
        exact ih v hu.tail hv.tail
      · have hv' : List.IsChain (fun c e : Fin d => c ≠ e) (a::b::v) :=
          List.IsChain.cons_cons hab hv
        have hvFlip : prefixFlip a (⟨b::v,hv⟩ : TreeVertex d) = ⟨a::b::v,hv'⟩ := by
          apply Subtype.ext
          simp only [prefixFlip, prefixFlipWord, ite_eq_right hab]
        rw [hvFlip]
        have h := ih (a::b::v) hu.tail hv'
        rw [reducedWordDistance_move_head a b u v hab hu] at h
        exact h

theorem HasFreeIsingLaw.pair_correlation {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (u v : TreeVertex d) :
    ∫ x, spinSign (x u) * spinSign (x v) ∂mu =
      theta ^ reducedWordDistance u.1 v.1 :=
  freeLaw_correlation_lists hmu hlo hhi u.1 v.1 u.2 v.2

end Problem367

end

end OAI
