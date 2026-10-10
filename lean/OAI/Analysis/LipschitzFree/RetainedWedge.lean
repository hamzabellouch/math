import OAI.Analysis.LipschitzFree.Wedge

namespace OAI

/-!
# Separated metric wedges and bounded finite-component retracts
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricWedge
open scoped Classical BigOperators
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

theorem separated (sep : ∀ n (x y : M n), x ≠ y → 1 ≤ dist x y)
    (x y : Point M o) (hxy : x ≠ y) : 1 ≤ dist x y := by
  change 1 ≤ distance M o x y
  rcases x with _ | ⟨n,x⟩ <;> rcases y with _ | ⟨m,y⟩
  · exact False.elim (hxy rfl)
  · exact sep m y.val (o m) y.property
  · exact sep n x.val (o n) x.property
  · by_cases h : n = m
    · subst m
      simp only [distance,dite_true]
      apply sep n x.val y.val
      intro h
      exact hxy (congrArg (fun t : {x : M n // x ≠ o n} => (some ⟨n,t⟩ : Point M o)) (Subtype.ext h))
    · simp only [distance,dite_eq_right h]
      linarith [sep n x.val (o n) x.property,sep m y.val (o m) y.property]

theorem discrete (sep : ∀ n (x y : M n), x ≠ y → 1 ≤ dist x y) :
    DiscreteTopology (Point M o) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  have hball : Metric.ball x 1 = {x} := by
    ext y
    constructor
    · intro hy
      apply Set.mem_singleton_iff.mpr
      by_contra h
      have hh := separated M o sep y x h
      exact (not_lt_of_ge hh) hy
    · rintro rfl
      simp
  rw [← hball]
  exact Metric.isOpen_ball

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem retain_idempotent (F : Finset ℕ) (x : Point M o) :
    retain M o F (retain M o F x) = retain M o F x := by
  rcases x with _ | ⟨n,x⟩
  · rfl
  · by_cases hn : n ∈ F <;> simp [retain,hn] <;> rfl

def Retained (F : Finset ℕ) := {x : Point M o // retain M o F x = x}

instance (F : Finset ℕ) : MetricSpace (Retained M o F) :=
  inferInstanceAs (MetricSpace {x : Point M o // retain M o F x = x})

def retainedBase (F : Finset ℕ) : Retained M o F := ⟨base M o,rfl⟩

def collapse (F : Finset ℕ) (x : Point M o) : Retained M o F :=
  ⟨retain M o F x,retain_idempotent M o F x⟩

def embed (F : Finset ℕ) (x : Retained M o F) : Point M o := x.val

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem collapse_base (F : Finset ℕ) :
    collapse M o F (base M o) = retainedBase M o F := rfl

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem embed_base (F : Finset ℕ) :
    embed M o F (retainedBase M o F) = base M o := rfl

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem embed_collapse (F : Finset ℕ) (x : Point M o) :
    embed M o F (collapse M o F x) = retain M o F x := rfl

theorem embed_isometry (F : Finset ℕ) : Isometry (embed M o F) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rfl

theorem collapse_lipschitz (F : Finset ℕ) : LipschitzWith 1 (collapse M o F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (retain_lipschitz M o F).dist_le_mul x y

theorem retained_separated (F : Finset ℕ)
    (sep : ∀ n (x y : M n), x ≠ y → 1 ≤ dist x y)
    (x y : Retained M o F) (hxy : x ≠ y) : 1 ≤ dist x y :=
  separated M o sep x.val y.val (fun h => hxy (Subtype.ext h))

theorem retained_radius (F : Finset ℕ) (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n (x : M n), dist x (o n) ≤ B n) (x : Retained M o F) :
    dist x (retainedBase M o F) ≤ ∑ n ∈ F, B n := by
  rcases x with ⟨(_ | ⟨n,x⟩),hx⟩
  · change (0 : ℝ) ≤ ∑ n ∈ F, B n
    exact Finset.sum_nonneg (fun n _ => hB n)
  · have hn : n ∈ F := by
      by_contra hn
      simp [retain,hn] at hx
    change dist x.val (o n) ≤ ∑ i ∈ F, B i
    exact (hb n x.val).trans (Finset.single_le_sum (fun i _ => hB i) hn)

end DiscreteFree.MetricWedge
end

end

end OAI
