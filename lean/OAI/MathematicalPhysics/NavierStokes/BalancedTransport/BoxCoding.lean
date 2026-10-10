import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.PrefixCoding

namespace OAI

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem disjoint_of_first_difference {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (p u v : List S) (a b : S) (hab : digit a + 1 < digit b) :
    Disjoint (interval r digit (p ++ a :: u)) (interval r digit (p ++ b :: v)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := prefix_gap hr digit hd₀ hd₁ p u v a b hx hy
  have hp : 0 < r ^ (p.length + 1) * (digit b - digit a - 1) :=
    mul_pos (pow_pos hr _) (by linarith)
  linarith

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder.Instruction
variable {Q Γ : Type*}

def sourcePrefixes (r : Instruction Q Γ) : Fin 3 → List (Letter Q Γ) :=
  ![r.sourceLeft, r.sourceRight, r.sourceHistory]

def targetPrefixes (r : Instruction Q Γ) : Fin 3 → List (Letter Q Γ) :=
  ![r.targetLeft, r.targetRight, r.targetHistory]

theorem balanced_determinant (inst : Instruction Q Γ) (h : inst.Balanced)
    {r : ℝ} (hr : r ≠ 0) :
    Matrix.det (Matrix.diagonal (Coding.scales r inst.sourcePrefixes inst.targetPrefixes)) = 1 := by
  apply Coding.determinant_one hr
  simpa [sourcePrefixes, targetPrefixes, Fin.sum_univ_succ, Instruction.Balanced,
    add_assoc] using h

end BalancedTransport.Recorder.Instruction
end

noncomputable section
namespace BalancedTransport

theorem Recorder.Row.determinant_one {Q Γ : Type*} (M : Recorder.Machine Q Γ)
    (row : Recorder.Row Q Γ) {r : ℝ} (hr : r ≠ 0) :
    Matrix.det (Matrix.diagonal (Coding.scales r
      (row.instruction M).sourcePrefixes (row.instruction M).targetPrefixes)) = 1 :=
  (row.instruction M).balanced_determinant (row.balanced M) hr

theorem residual_zero_pressure_solution (ν : ℝ) (U : Velocity)
    (hU : Smooth U) (hzero : ∀ x, U 0 x = 0)
    (hdiv : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    ZeroDataSolution ν (affineForce (inertialCoefficient U) (viscousCoefficient U) ν)
      U (fun _ _ => 0) := by
  refine ⟨hU, contDiffOn_const, hzero, hdiv, ?_⟩
  intro t ht x
  have hp : gradient (fun _ _ => 0) t x = 0 := by
    ext i
    simp [gradient, spaceD]
  rw [hp]
  simp only [affineForce, inertialCoefficient, viscousCoefficient, smul_neg, neg_zero, zero_add]
  abel

end BalancedTransport
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

theorem first_difference {u v : List S} (hu : ¬ u.IsPrefix v) (hv : ¬ v.IsPrefix u) :
    ∃ p a b u' v', u = p ++ a :: u' ∧ v = p ++ b :: v' ∧ a ≠ b := by
  classical
  induction u generalizing v with
  | nil => exact False.elim (hu ⟨v, by simp⟩)
  | cons a u ih =>
      cases v with
      | nil => exact False.elim (hv ⟨a :: u, by simp⟩)
      | cons b v =>
          by_cases hab : a = b
          · subst b
            have hu' : ¬u.IsPrefix v := by
              rintro ⟨w, hw⟩
              exact hu ⟨w, by simpa using congrArg (List.cons a) hw⟩
            have hv' : ¬v.IsPrefix u := by
              rintro ⟨w, hw⟩
              exact hv ⟨w, by simpa using congrArg (List.cons a) hw⟩
            obtain ⟨p, b, c, u', v', hu'', hv'', hbc⟩ := ih hu' hv'
            exact ⟨a :: p, b, c, u', v', by simp [hu''], by simp [hv''], hbc⟩
          · exact ⟨[], a, b, u, v, rfl, rfl, hab⟩

theorem incompatible_intervals_disjoint {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (hgap : ∀ a b, a ≠ b → digit a + 1 < digit b ∨ digit b + 1 < digit a)
    {u v : List S} (hu : ¬u.IsPrefix v) (hv : ¬v.IsPrefix u) :
    Disjoint (interval r digit u) (interval r digit v) := by
  obtain ⟨p, a, b, u', v', rfl, rfl, hab⟩ := first_difference hu hv
  rcases hgap a b hab with hab' | hba'
  · exact disjoint_of_first_difference hr digit hd₀ hd₁ p u' v' a b hab'
  · exact (disjoint_of_first_difference hr digit hd₀ hd₁ p v' u' b a hba').symm

theorem comparable_of_intersection {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (hgap : ∀ a b, a ≠ b → digit a + 1 < digit b ∨ digit b + 1 < digit a)
    {u v : List S} {x : ℝ} (hu : x ∈ interval r digit u) (hv : x ∈ interval r digit v) :
    u.IsPrefix v ∨ v.IsPrefix u := by
  by_contra h
  push Not at h
  exact Set.disjoint_left.mp (incompatible_intervals_disjoint hr digit hd₀ hd₁ hgap h.1 h.2)
    hu hv

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem common_extensions (filler : S) {u v : List S}
    (h : u.IsPrefix v ∨ v.IsPrefix u) :
    ∃ s t : Stream' S, u ++ₛ s = v ++ₛ t := by
  rcases h with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · exact ⟨w ++ₛ Stream'.const filler, Stream'.const filler,
      (Stream'.append_append_stream _ _ _).symm⟩
  · exact ⟨Stream'.const filler, w ++ₛ Stream'.const filler,
      Stream'.append_append_stream _ _ _⟩

def oddDigit {n : ℕ} (a : Fin n) : Fin (2 * n + 1) :=
  ⟨2 * a.val + 1, by omega⟩

theorem oddDigit_pos {n : ℕ} (a : Fin n) : 0 < (oddDigit a : ℝ) := by
  dsimp [oddDigit]
  positivity

theorem oddDigit_upper {n : ℕ} (a : Fin n) :
    (oddDigit a : ℝ) + 1 < (2 * n + 1 : ℕ) := by
  have hh : (2 * a.val + 1) + 1 < 2 * n + 1 := by omega
  exact_mod_cast hh

theorem oddDigit_gap {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (oddDigit a : ℝ) + 1 < (oddDigit b : ℝ) ∨
      (oddDigit b : ℝ) + 1 < (oddDigit a : ℝ) := by
  have hv : a.val ≠ b.val := fun hh => hab (Fin.ext hh)
  rcases lt_or_gt_of_ne hv with h | h
  · left
    have hh : (2 * a.val + 1) + 1 < 2 * b.val + 1 := by omega
    exact_mod_cast hh
  · right
    have hh : (2 * b.val + 1) + 1 < 2 * a.val + 1 := by omega
    exact_mod_cast hh

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

def box (r : ℝ) (digit : S → ℝ) (o : Space) (u : Fin 3 → List S) : Set Space :=
  {x | ∀ i, x i - o i ∈ interval r digit (u i)}

def boxMap (r : ℝ) (digit : S → ℝ) (o o' : Space)
    (u v : Fin 3 → List S) (x : Space) : Space :=
  fun i => o' i + replacement r digit (u i) (v i) (x i - o i)

theorem boxMap_image {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (o o' : Space) (u v : Fin 3 → List S) :
    boxMap r digit o o' u v '' box r digit o u = box r digit o' v := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    have hi : replacement r digit (u i) (v i) (x i - o i) ∈ interval r digit (v i) := by
      rw [← replacement_interval hr digit (u i) (v i)]
      exact ⟨x i - o i, hx i, rfl⟩
    simpa only [boxMap, add_sub_cancel_left] using hi
  · intro hy
    have hex : ∀ i, ∃ z : ℝ, z ∈ interval r digit (u i) ∧
        replacement r digit (u i) (v i) z = y i - o' i := by
      intro i
      have hi := hy i
      rw [← replacement_interval hr digit (u i) (v i)] at hi
      exact hi
    choose z hz he using hex
    refine ⟨fun i => o i + z i, ?_, ?_⟩
    · intro i
      simpa only [add_sub_cancel_left] using hz i
    · funext i
      simp only [boxMap, add_sub_cancel_left, he]
      ring

theorem boxMap_sub (r : ℝ) (digit : S → ℝ) (o o' : Space)
    (u v : Fin 3 → List S) (x y : Space) (i : Fin 3) :
    boxMap r digit o o' u v x i - boxMap r digit o o' u v y i =
      scales r u v i * (x i - y i) := by
  dsimp [boxMap, replacement, scales]
  ring

def codedPoint {B : ℕ} (digit : S → Fin B) (o : Space) (s : Fin 3 → Stream' S) : Space :=
  fun i => o i + stream digit (s i)

theorem codedPoint_mem_box {B : ℕ} (digit : S → Fin B) (o : Space)
    (u : Fin 3 → List S) (s : Fin 3 → Stream' S) :
    codedPoint digit o (fun i => u i ++ₛ s i) ∈
      box (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) o u := by
  intro i
  simpa only [codedPoint, add_sub_cancel_left] using
    stream_append_mem_interval digit (u i) (s i)

theorem boxMap_codedPoint {B : ℕ} (hB : B ≠ 0) (digit : S → Fin B) (o o' : Space)
    (u v : Fin 3 → List S) (s : Fin 3 → Stream' S) :
    boxMap (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) o o' u v
      (codedPoint digit o (fun i => u i ++ₛ s i)) =
      codedPoint digit o' (fun i => v i ++ₛ s i) := by
  funext i
  simp only [boxMap, codedPoint, add_sub_cancel_left]
  rw [replacement_stream hB]

def origin (k : ℕ) : Space := ![4 * (k : ℝ), 0, 0]

theorem control_eq_of_box_intersection {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    {k l : ℕ} {u v : Fin 3 → List S} {x : Space}
    (hu : x ∈ box r digit (origin k) u) (hv : x ∈ box r digit (origin l) v) : k = l := by
  have hu' := interval_subset_unit hr digit hd₀ hd₁ (u 0) (hu 0)
  have hv' := interval_subset_unit hr digit hd₀ hd₁ (v 0) (hv 0)
  simp only [origin, Matrix.cons_val_zero, Set.mem_Icc] at hu' hv'
  rcases lt_trichotomy k l with h | h | h
  · have h' : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast h
    linarith [hu'.2, hv'.1]
  · exact h
  · have h' : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h
    linarith [hv'.2, hu'.1]

theorem box_compact (r : ℝ) (digit : S → ℝ) (o : Space) (u : Fin 3 → List S) :
    IsCompact (box r digit o u) := by
  have he : box r digit o u = Set.pi Set.univ
      (fun i => Set.Icc (o i + word r digit (u i))
        (o i + word r digit (u i) + r ^ (u i).length)) := by
    ext x
    simp only [box, Set.mem_ofPred_eq, Set.mem_univ_pi, interval, Set.mem_Icc]
    congr! 1 with i
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [he]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}

def placement [Fintype Q] [DecidableEq Q] (M : Machine Q Γ) (s : Control Q) : ℕ :=
  if s = .ready M.halt then 0 else (Fintype.equivFin (Control Q) s).val + 1

@[simp] theorem placement_halt [Fintype Q] [DecidableEq Q] (M : Machine Q Γ) :
    placement M (.ready M.halt) = 0 := by simp [placement]

theorem placement_positive [Fintype Q] [DecidableEq Q] (M : Machine Q Γ)
    (s : Control Q) (hs : s ≠ .ready M.halt) : 0 < placement M s := by simp [placement, hs]

theorem placement_injective [Fintype Q] [DecidableEq Q] (M : Machine Q Γ) :
    Function.Injective (placement M) := by
  intro s t h
  by_cases hs : s = .ready M.halt <;> by_cases ht : t = .ready M.halt
  · exact hs.trans ht.symm
  · simp [placement, hs, ht] at h
  · simp [placement, hs, ht] at h
  · simp only [placement, hs, ht, ↓reduceIte, Nat.add_right_cancel_iff] at h
    exact (Fintype.equivFin (Control Q)).injective (Fin.ext h)

def Instruction.sourceBox (inst : Instruction Q Γ) (r : ℝ) (digit : Letter Q Γ → ℝ)
    (id : Control Q → ℕ) : Set Space :=
  Coding.box r digit (Coding.origin (id inst.sourceControl)) inst.sourcePrefixes

def Instruction.targetBox (inst : Instruction Q Γ) (r : ℝ) (digit : Letter Q Γ → ℝ)
    (id : Control Q → ℕ) : Set Space :=
  Coding.box r digit (Coding.origin (id inst.targetControl)) inst.targetPrefixes

theorem source_boxes_disjoint [DecidableEq Q] [DecidableEq Γ] (M : Machine Q Γ)
    {r : ℝ} (hr : 0 < r) (digit : Letter Q Γ → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (hgap : ∀ a b, a ≠ b → digit a + 1 < digit b ∨ digit b + 1 < digit a)
    (id : Control Q → ℕ) (hid : Function.Injective id)
    {a b : Row Q Γ} (ha : a.valid M) (hb : b.valid M) (hab : a ≠ b) :
    Disjoint ((a.instruction M).sourceBox r digit id)
      ((b.instruction M).sourceBox r digit id) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hcontrol : (a.instruction M).sourceControl = (b.instruction M).sourceControl :=
    hid (Coding.control_eq_of_box_intersection hr digit hd₀ hd₁ hx hy)
  have hi : ∀ i : Fin 3,
      ((a.instruction M).sourcePrefixes i).IsPrefix ((b.instruction M).sourcePrefixes i) ∨
      ((b.instruction M).sourcePrefixes i).IsPrefix ((a.instruction M).sourcePrefixes i) := by
    intro i
    apply Coding.comparable_of_intersection hr digit hd₀ hd₁ hgap (hx i)
    simpa only [Instruction.sourceBox, hcontrol] using hy i
  choose s t he using fun i => Coding.common_extensions (Letter.boundary : Letter Q Γ) (hi i)
  have heq : (a.instruction M).source ⟨s 0, s 1, s 2⟩ =
      (b.instruction M).source ⟨t 0, t 1, t 2⟩ := by
    dsimp [Instruction.source]
    congr 1
    · exact he 0
    · exact he 1
    · exact he 2
  exact hab (source_separation M ha hb heq).1

theorem target_boxes_disjoint (M : Machine Q Γ)
    {r : ℝ} (hr : 0 < r) (digit : Letter Q Γ → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (hgap : ∀ a b, a ≠ b → digit a + 1 < digit b ∨ digit b + 1 < digit a)
    (id : Control Q → ℕ) (hid : Function.Injective id)
    {a b : Row Q Γ} (hab : a ≠ b) :
    Disjoint ((a.instruction M).targetBox r digit id)
      ((b.instruction M).targetBox r digit id) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hcontrol : (a.instruction M).targetControl = (b.instruction M).targetControl :=
    hid (Coding.control_eq_of_box_intersection hr digit hd₀ hd₁ hx hy)
  have hi : ∀ i : Fin 3,
      ((a.instruction M).targetPrefixes i).IsPrefix ((b.instruction M).targetPrefixes i) ∨
      ((b.instruction M).targetPrefixes i).IsPrefix ((a.instruction M).targetPrefixes i) := by
    intro i
    apply Coding.comparable_of_intersection hr digit hd₀ hd₁ hgap (hx i)
    simpa only [Instruction.targetBox, hcontrol] using hy i
  choose s t he using fun i => Coding.common_extensions (Letter.boundary : Letter Q Γ) (hi i)
  have heq : (a.instruction M).target ⟨s 0, s 1, s 2⟩ =
      (b.instruction M).target ⟨t 0, t 1, t 2⟩ := by
    dsimp [Instruction.target]
    congr 1
    · exact he 0
    · exact he 1
    · exact he 2
  exact hab (target_separation M heq).1

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

def base (Q Γ : Type*) [Fintype Q] [Fintype Γ] : ℕ :=
  2 * Fintype.card (Letter Q Γ) + 1

def digit (a : Letter Q Γ) : Fin (base Q Γ) :=
  Coding.oddDigit (Fintype.equivFin (Letter Q Γ) a)

theorem base_pos : 0 < base Q Γ := by simp [base]

theorem digit_pos (a : Letter Q Γ) : 0 < (digit a : ℝ) :=
  Coding.oddDigit_pos _

theorem digit_upper (a : Letter Q Γ) : (digit a : ℝ) + 1 < base Q Γ :=
  Coding.oddDigit_upper _

theorem digit_gap (a b : Letter Q Γ) (hab : a ≠ b) :
    (digit a : ℝ) + 1 < (digit b : ℝ) ∨ (digit b : ℝ) + 1 < (digit a : ℝ) :=
  Coding.oddDigit_gap _ _ (fun he => hab ((Fintype.equivFin _).injective he))

end BalancedTransport.Recorder
end

end OAI
