import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Bridge
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Routing
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MotionField

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma BoxLayout.lower_mem {A : BoxLayout ι} (hp : A.Positive) (i : ι) :
    A.center i - A.width i ∈ A.solid i := by
  rw [BoxLayout.mem_solid]
  intro k
  exact ⟨le_rfl, by dsimp; linarith [hp i k]⟩

omit [Fintype ι] in
lemma BoxLayout.separated_of_disjoint {A : BoxLayout ι} (hp : A.Positive)
    (hs : Pairwise fun i j => Disjoint (A.solid i) (A.solid j)) : A.Separated 0 := by
  intro i j hij
  by_contra! h
  let x : Space := fun k => max (A.center i k - A.width i k) (A.center j k - A.width j k)
  have hh (k : Fin 3) :
      -(A.width i k + A.width j k) ≤ A.center i k - A.center j k ∧
      A.center i k - A.center j k ≤ A.width i k + A.width j k := by
    have := h k
    simp only [mul_zero, add_zero] at this
    exact abs_le.mp this
  have hi : x ∈ A.solid i := by
    rw [BoxLayout.mem_solid]
    intro k
    refine ⟨le_max_left _ _, max_le ?_ ?_⟩
    · linarith [hp i k]
    · linarith [(hh k).1]
  have hj : x ∈ A.solid j := by
    rw [BoxLayout.mem_solid]
    intro k
    refine ⟨le_max_right _ _, max_le ?_ ?_⟩
    · linarith [(hh k).2]
    · linarith [hp j k]
  exact Set.disjoint_left.mp (hs hij) hi hj

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Coding
open BalancedTransport.Geometry
variable {S ι : Type*}

def layout (r : ℝ) (digit : S → ℝ) (o : ι → Space) (u : ι → Fin 3 → List S) :
    BoxLayout ι where
  center i k := o i k + word r digit (u i k) + r ^ (u i k).length / 2
  width i k := r ^ (u i k).length / 2

lemma layout_positive {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (o : ι → Space) (u : ι → Fin 3 → List S) : (layout r digit o u).Positive := by
  intro i k
  exact div_pos (pow_pos hr _) (by norm_num)

lemma layout_solid [Fintype ι] (r : ℝ) (digit : S → ℝ) (o : ι → Space)
    (u : ι → Fin 3 → List S) (i : ι) :
    (layout r digit o u).solid i = box r digit (o i) (u i) := by
  ext x
  rw [BoxLayout.mem_solid]
  change (∀ k, o i k + word r digit (u i k) + r ^ (u i k).length / 2 -
      r ^ (u i k).length / 2 ≤ x k ∧
      x k ≤ o i k + word r digit (u i k) + r ^ (u i k).length / 2 +
      r ^ (u i k).length / 2) ↔
    ∀ k, word r digit (u i k) ≤ x k - o i k ∧
      x k - o i k ≤ word r digit (u i k) + r ^ (u i k).length
  constructor <;> intro h k <;> have := h k <;> constructor <;> linarith

lemma layout_affineMap {r : ℝ} (hr : r ≠ 0) (digit : S → ℝ) (o p : ι → Space)
    (u v : ι → Fin 3 → List S) (i : ι) (x : Space) :
    (layout r digit o u).affineMap (layout r digit p v) i x =
      boxMap r digit (o i) (p i) (u i) (v i) x := by
  ext k
  dsimp [BoxLayout.affineMap, layout, boxMap, replacement]
  field_simp
  ring

lemma layout_volume (r : ℝ) (digit : S → ℝ) (o p : ι → Space)
    (u v : ι → Fin 3 → List S) (i : ι)
    (h : ∑ k, (u i k).length = ∑ k, (v i k).length) :
    ∏ k, (layout r digit o u).width i k = ∏ k, (layout r digit p v).width i k := by
  simp only [layout, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, h]

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder
open BalancedTransport.Geometry
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

abbrev ActiveRow (M : Machine Q Γ) := {r : Row Q Γ // r ∈ table M}

def sourceLayout (M : Machine Q Γ) : BoxLayout (ActiveRow M) :=
  Coding.layout (base Q Γ : ℝ)⁻¹ (fun a : Letter Q Γ => (digit a : ℝ))
    (fun i => Coding.origin (placement M (i.val.instruction M).sourceControl))
    (fun i => (i.val.instruction M).sourcePrefixes)

def targetLayout (M : Machine Q Γ) : BoxLayout (ActiveRow M) :=
  Coding.layout (base Q Γ : ℝ)⁻¹ (fun a : Letter Q Γ => (digit a : ℝ))
    (fun i => Coding.origin (placement M (i.val.instruction M).targetControl))
    (fun i => (i.val.instruction M).targetPrefixes)

def safeRows (M : Machine Q Γ) : Set (ActiveRow M) :=
  {i | (i.val.instruction M).targetControl ≠ .ready M.halt}

omit [DecidableEq Γ] in
lemma sourceLayout_solid (M : Machine Q Γ) (i : ActiveRow M) :
    (sourceLayout M).solid i = (i.val.instruction M).sourceBox
      (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ)) (placement M) :=
  Coding.layout_solid _ _ _ _ _

omit [DecidableEq Γ] in
lemma targetLayout_solid (M : Machine Q Γ) (i : ActiveRow M) :
    (targetLayout M).solid i = (i.val.instruction M).targetBox
      (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ)) (placement M) :=
  Coding.layout_solid _ _ _ _ _

omit [DecidableEq Γ] in
lemma sourceLayout_positive (M : Machine Q Γ) : (sourceLayout M).Positive :=
  Coding.layout_positive inverse_base_pos _ _ _

omit [DecidableEq Γ] in
lemma targetLayout_positive (M : Machine Q Γ) : (targetLayout M).Positive :=
  Coding.layout_positive inverse_base_pos _ _ _

lemma sourceLayout_separated (M : Machine Q Γ) : (sourceLayout M).Separated 0 := by
  apply BoxLayout.separated_of_disjoint (sourceLayout_positive M)
  intro i j hij
  rw [sourceLayout_solid, sourceLayout_solid]
  exact (compiled_boxes_disjoint M).1 i.property j.property (fun h => hij (Subtype.ext h))

lemma targetLayout_separated (M : Machine Q Γ) : (targetLayout M).Separated 0 := by
  apply BoxLayout.separated_of_disjoint (targetLayout_positive M)
  intro i j hij
  rw [targetLayout_solid, targetLayout_solid]
  exact (compiled_boxes_disjoint M).2 i.property j.property (fun h => hij (Subtype.ext h))

omit [DecidableEq Γ] in
lemma layouts_equal_volume (M : Machine Q Γ) (i : ActiveRow M) :
    ∏ k, (sourceLayout M).width i k = ∏ k, (targetLayout M).width i k := by
  apply Coding.layout_volume
  simpa [Instruction.sourcePrefixes, Instruction.targetPrefixes, Fin.sum_univ_succ,
    Instruction.Balanced, Nat.add_assoc] using i.val.balanced M

omit [DecidableEq Γ] in
lemma sourceLayout_guard (M : Machine Q Γ) : (sourceLayout M).Guarded (safeRows M) := by
  intro i _
  have hh := BoxLayout.lower_mem (sourceLayout_positive M) i
  rw [sourceLayout_solid] at hh
  have hn := source_box_guard M i.val ((mem_table M _).mp i.property) hh
  change 2 < (sourceLayout M).center i 0 - (sourceLayout M).width i 0
  change 4 ≤ (sourceLayout M).center i 0 - (sourceLayout M).width i 0 at hn
  linarith

omit [DecidableEq Γ] in
lemma targetLayout_guard (M : Machine Q Γ) : (targetLayout M).Guarded (safeRows M) := by
  intro i hi
  have hh := BoxLayout.lower_mem (targetLayout_positive M) i
  rw [targetLayout_solid] at hh
  have hn := nonhalt_box_guard M _ hi _ hh
  change 2 < (targetLayout M).center i 0 - (targetLayout M).width i 0
  change 4 ≤ (targetLayout M).center i 0 - (targetLayout M).width i 0 at hn
  linarith

omit [DecidableEq Γ] in
lemma layouts_affineMap (M : Machine Q Γ) (i : ActiveRow M) (x : Space) :
    (sourceLayout M).affineMap (targetLayout M) i x = (i.val.instruction M).fullMap M x :=
  Coding.layout_affineMap inverse_base_pos.ne' _ _ _ _ _ _ _

theorem exists_guarded_template (M : Machine Q Γ) :
    ∃ (v : Velocity) (K : Set Space), IsCompact K ∧ JointSmooth v ∧ TimeCollars v ∧
      SpatiallySupported K v ∧ (∀ t x, div v t x = 0) ∧ GuardedTemplate M v := by
  obtain ⟨η, hη, ⟨m⟩⟩ := guarded_solid_box_motion (sourceLayout M) (targetLayout M)
    (safeRows M) (sourceLayout_positive M) (targetLayout_positive M)
    (sourceLayout_separated M) (targetLayout_separated M) (layouts_equal_volume M)
    (sourceLayout_guard M) (targetLayout_guard M)
  obtain ⟨K, hK, hs⟩ := m.velocity_compact_support hη
  refine ⟨m.velocity, K, hK, m.velocity_jointSmooth, m.velocity_collars, hs,
    m.velocity_divergence, ?_⟩
  intro r hr x hx
  let i : ActiveRow M := ⟨r, (mem_table M r).mpr hr⟩
  have hm : x ∈ (sourceLayout M).solid i := by rwa [sourceLayout_solid]
  refine ⟨m.path i x, m.path_start i x, ?_, ?_, ?_⟩
  · rw [m.path_end, layouts_affineMap]
  · intro t _
    exact (m.path_hasDerivAt hη hm t).hasDerivWithinAt
  · intro hsafe t _
    exact m.path_guarded hsafe hm t

end BalancedTransport.Recorder
end

end OAI
