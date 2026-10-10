import OAI.Analysis.LiebThirring.BoundState

namespace OAI

universe u37 u38

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


end
end
end

/-! Equivariant cubical barycentric flags. A codimension-one face of a full
flag has one canonical neighboring flag; this avoids any orientation choices. -/
noncomputable section
open Finset
namespace SharpLiebThirring.CubeFlags

/-- A maximal flag in the barycentric subdivision of an integer cube. -/
@[ext] structure Flag (n : ℕ) where
  base : Fin n → ℤ
  corner : Fin n → Bool
  order : Equiv.Perm (Fin n)

/-- Twice the barycenter of the `k`th cubical face in a maximal flag. -/
def Flag.vertex {n : ℕ} (F : Flag n) (k : Fin (n + 1)) (i : Fin n) : ℤ :=
  2 * F.base i + if (F.order.symm i).val < k.val then 1 else if F.corner i then 2 else 0

/-- The real vertex obtained by rescaling the half-integer grid. -/
def Flag.point {n : ℕ} (F : Flag n) (k : Fin (n + 1)) : Fin n → ℝ :=
  fun i ↦ (F.vertex k i : ℝ) / 2

lemma Flag.vertex_bounds {n : ℕ} (F : Flag n) (k : Fin (n + 1)) (i : Fin n) :
    2 * F.base i ≤ F.vertex k i ∧ F.vertex k i ≤ 2 * F.base i + 2 := by
  simp only [vertex]
  split_ifs <;> omega

lemma Flag.point_bounds {n : ℕ} (F : Flag n) (k : Fin (n + 1)) (i : Fin n) :
    (F.base i : ℝ) ≤ F.point k i ∧ F.point k i ≤ F.base i + 1 := by
  obtain ⟨h₁, h₂⟩ := F.vertex_bounds k i
  have h₁r : (2 : ℝ) * F.base i ≤ F.vertex k i := by exact_mod_cast h₁
  have h₂r : (F.vertex k i : ℝ) ≤ 2 * F.base i + 2 := by exact_mod_cast h₂
  dsimp [point]
  constructor <;> linarith

/-- Toggle the endpoint chosen in coordinate `i`. -/
def Flag.flip {n : ℕ} (F : Flag n) (i : Fin n) : Flag n :=
  { F with corner := Function.update F.corner i (!(F.corner i)) }

@[simp] lemma Flag.flip_base {n : ℕ} (F : Flag n) (i : Fin n) : (F.flip i).base = F.base := rfl
@[simp] lemma Flag.flip_order {n : ℕ} (F : Flag n) (i : Fin n) : (F.flip i).order = F.order := rfl

lemma Flag.flip_flip {n : ℕ} (F : Flag n) (i : Fin n) : (F.flip i).flip i = F := by
  ext j <;> simp [flip]

/-- Across the final facet, pass to the neighboring cube and toggle its endpoint. -/
def Flag.cross {n : ℕ} (F : Flag n) (i : Fin n) : Flag n :=
  { F.flip i with base := Function.update F.base i (F.base i + if F.corner i then 1 else -1) }

@[simp] lemma Flag.cross_order {n : ℕ} (F : Flag n) (i : Fin n) : (F.cross i).order = F.order := rfl

lemma Flag.cross_cross {n : ℕ} (F : Flag n) (i : Fin n) : (F.cross i).cross i = F := by
  ext j <;> simp [cross, flip, Function.update_apply]
  split_ifs <;> simp_all

/-- Swap the order of two successive face expansions. -/
def Flag.swap {n : ℕ} (F : Flag n) (i j : Fin n) : Flag n :=
  { F with order := (Equiv.swap i j).trans F.order }

lemma Flag.swap_swap {n : ℕ} (F : Flag n) (i j : Fin n) :
    (F.swap i j).swap i j = F := by
  ext k <;> simp [swap]

lemma Flag.flip_vertex {n : ℕ} (F : Flag n) (i : Fin n) (k : Fin (n + 1))
    (hik : (F.order.symm i).val < k.val) : (F.flip i).vertex k = F.vertex k := by
  funext j
  by_cases hj : j = i
  · subst j; simp [vertex, flip, hik]
  · simp [vertex, flip, Function.update_of_ne hj]

lemma Flag.cross_vertex {n : ℕ} (F : Flag n) (i : Fin n) (k : Fin (n + 1))
    (hik : k.val ≤ (F.order.symm i).val) : (F.cross i).vertex k = F.vertex k := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [vertex, cross, flip, Function.update_self]
    have h : ¬ (F.order.symm i).val < k.val := by omega
    simp only [h, ↓reduceIte]
    cases F.corner i <;> norm_num <;> ring
  · simp [vertex, cross, flip, Function.update_of_ne hj]

lemma Flag.swap_vertex {n : ℕ} (F : Flag n) (i j : Fin n) (k : Fin (n + 1))
    (hik : i.val < k.val ↔ j.val < k.val) : (F.swap i j).vertex k = F.vertex k := by
  funext a
  simp only [vertex, swap, Equiv.symm_trans, Equiv.symm_swap, Equiv.trans_apply]
  congr 1
  have h : ((Equiv.swap i j) (F.order.symm a)).val < k.val ↔ (F.order.symm a).val < k.val := by
    by_cases hi : F.order.symm a = i
    · simp [hi, hik]
    by_cases hj : F.order.symm a = j
    · simp [hj, hik]
    · simp [Equiv.swap_apply_of_ne_of_ne hi hj]
  simp only [h]
  split_ifs <;> simp_all

/-- The other maximal flag sharing the facet obtained by deleting vertex `j`. -/
def Flag.neighbor {n : ℕ} [NeZero n] (F : Flag n) (j : Fin (n + 1)) : Flag n :=
  if h₀ : j.val = 0 then F.flip (F.order ⟨0, NeZero.pos n⟩)
  else if hₙ : j.val = n then F.cross (F.order ⟨n - 1, by omega⟩)
  else F.swap ⟨j.val - 1, by omega⟩ ⟨j.val, by omega⟩

lemma Flag.neighbor_neighbor {n : ℕ} [NeZero n] (F : Flag n) (j : Fin (n + 1)) :
    (F.neighbor j).neighbor j = F := by
  by_cases h₀ : j.val = 0
  · simp only [neighbor, dite_eq_left h₀, flip_order]
    exact flip_flip F _
  by_cases hₙ : j.val = n
  · simp only [neighbor, dite_eq_right h₀, dite_eq_left hₙ, cross_order]
    exact cross_cross F _
  · simp only [neighbor, dite_eq_right h₀, dite_eq_right hₙ]
    exact swap_swap F _ _

lemma Flag.neighbor_vertex {n : ℕ} [NeZero n] (F : Flag n) (j k : Fin (n + 1))
    (hjk : k ≠ j) : (F.neighbor j).vertex k = F.vertex k := by
  have hval : k.val ≠ j.val := fun h ↦ hjk (Fin.ext h)
  by_cases h₀ : j.val = 0
  · simp only [neighbor, dite_eq_left h₀]
    apply flip_vertex
    simp only [Equiv.symm_apply_apply]
    omega
  by_cases hₙ : j.val = n
  · simp only [neighbor, dite_eq_right h₀, dite_eq_left hₙ]
    apply cross_vertex
    simp only [Equiv.symm_apply_apply]
    omega
  · simp only [neighbor, dite_eq_right h₀, dite_eq_right hₙ]
    apply swap_vertex
    simp only
    omega

lemma Flag.flip_ne {n : ℕ} (F : Flag n) (i : Fin n) : F.flip i ≠ F := by
  intro he
  have h := congrArg (fun G : Flag n ↦ G.corner i) he
  simp only [flip, Function.update_self] at h
  exact (Bool.not_eq_self (F.corner i)).mp h

lemma Flag.cross_ne {n : ℕ} (F : Flag n) (i : Fin n) : F.cross i ≠ F := by
  intro he
  have h := congrArg (fun G : Flag n ↦ G.base i) he
  simp only [cross, Function.update_self] at h
  split_ifs at h <;> omega

lemma Flag.swap_ne {n : ℕ} (F : Flag n) (i j : Fin n) (hij : i ≠ j) : F.swap i j ≠ F := by
  intro he
  have h := congrArg (fun G : Flag n ↦ G.order i) he
  simp only [swap, Equiv.trans_apply, Equiv.swap_apply_left] at h
  exact hij (F.order.injective h).symm

lemma Flag.neighbor_ne {n : ℕ} [NeZero n] (F : Flag n) (j : Fin (n + 1)) :
    F.neighbor j ≠ F := by
  by_cases h₀ : j.val = 0
  · simp only [neighbor, dite_eq_left h₀]
    exact flip_ne F _
  by_cases hₙ : j.val = n
  · simp only [neighbor, dite_eq_right h₀, dite_eq_left hₙ]
    exact cross_ne F _
  · simp only [neighbor, dite_eq_right h₀, dite_eq_right hₙ]
    apply swap_ne
    intro h
    have hf := congrArg Fin.val h
    simp only at hf
    omega

section Consecutive
variable {V : Type u37} [AddCommGroup V] [Module ℝ V]

lemma span_consecutive {n : ℕ} (v : Fin (n + 1) → V) :
    Submodule.span ℝ (Set.range (Fin.cons (v 0) (fun i ↦ v i.succ - v i.castSucc))) =
    Submodule.span ℝ (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.sub_mem _ (Submodule.subset_span ⟨j.succ, rfl⟩)
        (Submodule.subset_span ⟨j.castSucc, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.induction ?_ (fun j hj ↦ ?_) i
    · exact Submodule.subset_span ⟨0, rfl⟩
    · have hd : v j.succ - v j.castSucc ∈
          Submodule.span ℝ (Set.range (Fin.cons (v 0) (fun i ↦ v i.succ - v i.castSucc))) :=
        Submodule.subset_span ⟨j.succ, rfl⟩
      have hsum := Submodule.add_mem _ hd hj
      rw [sub_add_cancel] at hsum
      exact hsum

lemma linearIndependent_consecutive_iff {n : ℕ} (v : Fin (n + 1) → V) :
    LinearIndependent ℝ (Fin.cons (v 0) (fun i ↦ v i.succ - v i.castSucc)) ↔
    LinearIndependent ℝ v := by
  rw [linearIndependent_iff_card_eq_finrank_span, linearIndependent_iff_card_eq_finrank_span]
  change _ = Module.finrank ℝ (Submodule.span ℝ _) ↔ _ = Module.finrank ℝ (Submodule.span ℝ _)
  rw [span_consecutive]
end Consecutive

def Flag.step {n : ℕ} (F : Flag n) (i : Fin n) : ℝ :=
  if F.corner (F.order i) then -1 / 2 else 1 / 2

lemma Flag.step_ne_zero {n : ℕ} (F : Flag n) (i : Fin n) : F.step i ≠ 0 := by
  dsimp [step]
  split_ifs <;> norm_num

lemma Flag.point_succ_sub {n : ℕ} (F : Flag n) (k : Fin n) :
    F.point k.succ - F.point k.castSucc = Pi.single (F.order k) (F.step k) := by
  ext i
  by_cases hi : i = F.order k
  · subst i
    simp only [Pi.sub_apply, point, vertex, Equiv.symm_apply_apply,
      Fin.val_succ, Fin.val_castSucc, Nat.lt_succ_self, ↓reduceIte, lt_self_iff_false,
      Pi.single_eq_same, step]
    split_ifs <;> push_cast <;> ring
  · have hik : F.order.symm i ≠ k := by
      intro h
      apply hi
      simpa using congrArg F.order h
    have hval : (F.order.symm i).val ≠ k.val := fun h ↦ hik (Fin.ext h)
    have hlt : (F.order.symm i).val < k.val + 1 ↔ (F.order.symm i).val < k.val := by omega
    simp [hi, point, vertex, hlt]

lemma Flag.linearIndependent_steps {n : ℕ} (F : Flag n) :
    LinearIndependent ℝ (fun k : Fin n ↦ F.point k.succ - F.point k.castSucc) := by
  classical
  have hb := (Pi.basisFun ℝ (Fin n)).linearIndependent.comp F.order F.order.injective
  have hs := hb.units_smul (fun k ↦ Units.mk0 (F.step k) (F.step_ne_zero k))
  have he : (fun k : Fin n ↦ F.point k.succ - F.point k.castSucc) =
      (fun k ↦ Units.mk0 (F.step k) (F.step_ne_zero k)) •
        ((Pi.basisFun ℝ (Fin n)) ∘ F.order) := by
    funext k
    rw [F.point_succ_sub k]
    ext i
    simp [Pi.basisFun_apply, Pi.single_apply, Units.smul_def]
  rw [he]
  exact hs

lemma Flag.augmented_linearIndependent {n : ℕ} (F : Flag n) :
    LinearIndependent ℝ (fun k ↦ ((1 : ℝ), F.point k)) := by
  apply (linearIndependent_consecutive_iff _).mp
  apply linearIndependent_finCons.mpr
  constructor
  · have h := F.linearIndependent_steps.map' (LinearMap.inr ℝ ℝ (Fin n → ℝ))
      (LinearMap.ker_eq_bot.mpr LinearMap.inr_injective)
    simpa only [LinearMap.inr_apply, Function.comp_def, Prod.mk_sub_mk, sub_self] using h
  · have hspan : Submodule.span ℝ
        (Set.range (fun i : Fin n ↦ ((1 : ℝ), F.point i.succ) - (1, F.point i.castSucc))) ≤
        LinearMap.ker (LinearMap.fst ℝ ℝ (Fin n → ℝ)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      simp
    intro hmem
    have h := hspan hmem
    simp at h

/-- Coordinate reflections preserve the entire flag subdivision. -/
def Flag.reflect {n : ℕ} (s : Fin n → Bool) (F : Flag n) : Flag n where
  base i := if s i then -F.base i - 1 else F.base i
  corner i := xor (s i) (F.corner i)
  order := F.order

lemma Flag.reflect_false {n : ℕ} (F : Flag n) : F.reflect (fun _ ↦ false) = F := by
  ext i <;> simp [reflect]

lemma Flag.reflect_reflect {n : ℕ} (s t : Fin n → Bool) (F : Flag n) :
    (F.reflect t).reflect s = F.reflect (fun i ↦ xor (s i) (t i)) := by
  ext i <;> simp only [reflect]
  · rcases Bool.eq_false_or_eq_true (s i) with hs | hs <;>
      rcases Bool.eq_false_or_eq_true (t i) with ht | ht <;> simp [hs, ht]
  · exact (Bool.xor_assoc _ _ _).symm

lemma Flag.reflect_vertex {n : ℕ} (s : Fin n → Bool) (F : Flag n)
    (k : Fin (n + 1)) (i : Fin n) :
    (F.reflect s).vertex k i = if s i then -F.vertex k i else F.vertex k i := by
  simp only [vertex, reflect]
  rcases Bool.eq_false_or_eq_true (s i) with hs | hs <;>
    rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
    simp [hs, hc] <;> split_ifs <;> omega

lemma Flag.reflect_point {n : ℕ} (s : Fin n → Bool) (F : Flag n)
    (k : Fin (n + 1)) (i : Fin n) :
    (F.reflect s).point k i = if s i then -F.point k i else F.point k i := by
  dsimp [point]
  rw [reflect_vertex]
  rcases Bool.eq_false_or_eq_true (s i) with hs | hs <;> simp [hs]
  ring

lemma Flag.reflect_flip {n : ℕ} (s : Fin n → Bool) (F : Flag n) (i : Fin n) :
    (F.flip i).reflect s = (F.reflect s).flip i := by
  ext j <;> simp only [reflect, flip]
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
    cases s i <;> cases F.corner i <;> rfl
  · simp [Function.update_of_ne hji]

lemma Flag.reflect_cross {n : ℕ} (s : Fin n → Bool) (F : Flag n) (i : Fin n) :
    (F.cross i).reflect s = (F.reflect s).cross i := by
  ext j <;> simp only [reflect, cross, flip]
  · by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      rcases Bool.eq_false_or_eq_true (s i) with hs | hs <;>
        rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
        simp [hs, hc]
      omega
    · simp [Function.update_of_ne hji]
  · by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      cases s i <;> cases F.corner i <;> rfl
    · simp [Function.update_of_ne hji]

lemma Flag.reflect_swap {n : ℕ} (s : Fin n → Bool) (F : Flag n) (i j : Fin n) :
    (F.swap i j).reflect s = (F.reflect s).swap i j := rfl

lemma Flag.reflect_neighbor {n : ℕ} [NeZero n] (s : Fin n → Bool)
    (F : Flag n) (j : Fin (n + 1)) :
    (F.neighbor j).reflect s = (F.reflect s).neighbor j := by
  by_cases h₀ : j.val = 0
  · simp only [neighbor, dite_eq_left h₀, reflect]
    exact reflect_flip s F _
  by_cases hₙ : j.val = n
  · simp only [neighbor, dite_eq_right h₀, dite_eq_left hₙ, reflect]
    exact reflect_cross s F _
  · simp only [neighbor, dite_eq_right h₀, dite_eq_right hₙ]
    exact reflect_swap s F _ _

/-- Coordinate reflections form an elementary two-group. -/
@[ext] structure Signs (n : ℕ) where
  val : Fin n → Bool

def Signs.equiv (n : ℕ) : Signs n ≃ (Fin n → Bool) where
  toFun := Signs.val
  invFun := Signs.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance {n : ℕ} : Fintype (Signs n) := Fintype.ofEquiv _ (Signs.equiv n).symm
instance {n : ℕ} : DecidableEq (Signs n) := Classical.decEq _

instance {n : ℕ} : CommGroup (Signs n) where
  mul s t := ⟨fun i ↦ xor (s.val i) (t.val i)⟩
  one := ⟨fun _ ↦ false⟩
  inv s := s
  mul_assoc s t u := by ext i; exact Bool.xor_assoc _ _ _
  one_mul s := by ext i; exact Bool.false_xor _
  mul_one s := by ext i; exact Bool.xor_false _
  inv_mul_cancel s := by ext i; exact Bool.xor_self _
  mul_comm s t := by ext i; exact Bool.xor_comm _ _

@[simp] lemma Signs.mul_val {n : ℕ} (s t : Signs n) (i : Fin n) :
    (s * t).val i = xor (s.val i) (t.val i) := rfl
@[simp] lemma Signs.one_val {n : ℕ} (i : Fin n) : (1 : Signs n).val i = false := rfl
@[simp] lemma Signs.inv_eq {n : ℕ} (s : Signs n) : s⁻¹ = s := rfl

instance {n : ℕ} : MulAction (Signs n) (Flag n) where
  smul s F := F.reflect s.val
  one_smul := Flag.reflect_false
  mul_smul s t F := (F.reflect_reflect s.val t.val).symm

lemma Flag.smul_def {n : ℕ} (s : Signs n) (F : Flag n) : s • F = F.reflect s.val := rfl

instance {n : ℕ} : IsCancelSMul (Signs n) (Flag n) where
  right_cancel' s t F he := by
    ext i
    have hb := congrArg (fun G : Flag n ↦ G.base i) he
    change (if s.val i then -F.base i - 1 else F.base i) =
      (if t.val i then -F.base i - 1 else F.base i) at hb
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;>
      rcases Bool.eq_false_or_eq_true (t.val i) with ht | ht <;>
      simp_all <;> omega

lemma Flag.smul_neighbor {n : ℕ} [NeZero n] (s : Signs n)
    (F : Flag n) (j : Fin (n + 1)) :
    s • F.neighbor j = (s • F).neighbor j := F.reflect_neighbor s.val j

/-- No two vertices of a flag belong to the same coordinate-reflection orbit.
Parity records the order in which coordinates become barycenters. -/
lemma Flag.vertex_orbits_distinct {n : ℕ} (F : Flag n)
    (j k : Fin (n + 1)) (s : Signs n)
    (he : ∀ i, F.vertex j i = if s.val i then -F.vertex k i else F.vertex k i) : j = k := by
  apply Fin.ext
  by_contra h
  have hlt : j.val < k.val ∨ k.val < j.val := lt_or_gt_of_ne h
  have hbad (a b : Fin (n + 1)) (hab : a.val < b.val)
      (hh : ∀ i, F.vertex a i = if s.val i then -F.vertex b i else F.vertex b i) : False := by
    let i : Fin n := F.order ⟨a.val, by omega⟩
    have hi : (F.order.symm i).val = a.val := by simp [i]
    have hh' := hh i
    simp only [vertex, hi, lt_self_iff_false, ↓reduceIte, hab] at hh'
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;>
      rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
      simp [hs, hc] at hh' <;> omega
  rcases hlt with hlt | hlt
  · exact hbad j k hlt he
  · apply hbad k j hlt
    intro i
    have hi := he i
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;>
      simp_all

/-- Distance, with the corner sign, from the chosen endpoint of a coordinate. -/
def Flag.depth {n : ℕ} (F : Flag n) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  if F.corner i then (F.base i : ℝ) + 1 - x i else x i - F.base i

lemma Flag.depth_point {n : ℕ} (F : Flag n) (i : Fin n) (k : Fin (n + 1)) :
    F.depth i (F.point k) = if (F.order.symm i).val < k.val then 1 / 2 else 0 := by
  simp only [depth, point, vertex]
  rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
    simp only [hc, Bool.false_eq_true, ↓reduceIte, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat] <;> split_ifs <;> norm_num <;> ring

lemma Flag.depth_combination {n : ℕ} (F : Flag n) (i : Fin n)
    {ι : Type u38} [Fintype ι] (w : ι → ℝ) (x : ι → Fin n → ℝ) (hw : ∑ k, w k = 1) :
    F.depth i (∑ k, w k • x k) = ∑ k, w k * F.depth i (x k) := by
  simp only [depth, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
    simp only [hc, Bool.false_eq_true, ↓reduceIte, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hw, one_mul]

lemma Flag.depth_nonneg {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (i : Fin n) :
    0 ≤ F.depth i (∑ k, w k • F.point k) := by
  rw [F.depth_combination i w F.point hs]
  apply Finset.sum_nonneg
  intro k _
  have hk := hw k
  rw [F.depth_point]
  split_ifs <;> positivity

lemma Flag.depth_le_half {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (i : Fin n) :
    F.depth i (∑ k, w k • F.point k) ≤ 1 / 2 := by
  rw [F.depth_combination i w F.point hs]
  calc
    _ ≤ ∑ k, w k * (1 / 2) := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (hw k)
      rw [F.depth_point]
      split_ifs <;> norm_num
    _ = 1 / 2 := by rw [← Finset.sum_mul, hs, one_mul]

lemma Flag.depth_pos {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 < w k) (hs : ∑ k, w k = 1) (i : Fin n) :
    0 < F.depth i (∑ k, w k • F.point k) := by
  rw [F.depth_combination i w F.point hs]
  apply Finset.sum_pos'
  · intro k _
    have hk := (hw k).le
    rw [F.depth_point]
    split_ifs <;> positivity
  · refine ⟨Fin.last n, Finset.mem_univ _, ?_⟩
    rw [F.depth_point]
    simp only [Fin.val_last, (F.order.symm i).isLt, ↓reduceIte]
    exact mul_pos (hw _) (by norm_num)

lemma Flag.depth_lt_half {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 < w k) (hs : ∑ k, w k = 1) (i : Fin n) :
    F.depth i (∑ k, w k • F.point k) < 1 / 2 := by
  rw [F.depth_combination i w F.point hs]
  calc
    _ < ∑ k, w k * (1 / 2) := by
      apply Finset.sum_lt_sum
      · intro k _
        apply mul_le_mul_of_nonneg_left _ (hw k).le
        rw [F.depth_point]
        split_ifs <;> norm_num
      · refine ⟨0, Finset.mem_univ _, ?_⟩
        rw [F.depth_point]
        simp only [Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, mul_zero]
        exact mul_pos (hw _) (by norm_num)
    _ = 1 / 2 := by rw [← Finset.sum_mul, hs, one_mul]

lemma Flag.depth_antitone {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (i j : Fin n) (hij : F.order.symm i ≤ F.order.symm j) :
    F.depth j (∑ k, w k • F.point k) ≤ F.depth i (∑ k, w k • F.point k) := by
  rw [F.depth_combination i w F.point hs, F.depth_combination j w F.point hs]
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (hw k)
  rw [F.depth_point, F.depth_point]
  split_ifs <;> try norm_num
  exact False.elim (by omega)

lemma Flag.depth_strictAnti {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 < w k) (hs : ∑ k, w k = 1)
    (i j : Fin n) (hij : F.order.symm i < F.order.symm j) :
    F.depth j (∑ k, w k • F.point k) < F.depth i (∑ k, w k • F.point k) := by
  rw [F.depth_combination i w F.point hs, F.depth_combination j w F.point hs]
  apply Finset.sum_lt_sum
  · intro k _
    apply mul_le_mul_of_nonneg_left _ (hw k).le
    rw [F.depth_point, F.depth_point]
    split_ifs <;> try norm_num
    exact False.elim (by omega)
  · refine ⟨(F.order.symm i).succ, Finset.mem_univ _, ?_⟩
    rw [F.depth_point, F.depth_point]
    simp only [Fin.val_succ]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    nlinarith [hw (F.order.symm i).succ]

lemma Flag.combination_bounds {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (i : Fin n) :
    (F.base i : ℝ) ≤ (∑ k, w k • F.point k) i ∧
      (∑ k, w k • F.point k) i ≤ F.base i + 1 := by
  have h₀ := F.depth_nonneg w hw hs i
  have h₁ := F.depth_le_half w hw hs i
  rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
    simp only [depth, hc, Bool.false_eq_true, ↓reduceIte] at h₀ h₁ <;>
    constructor <;> linarith

lemma Flag.combination_strict_bounds {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 < w k) (hs : ∑ k, w k = 1) (i : Fin n) :
    (F.base i : ℝ) < (∑ k, w k • F.point k) i ∧
      (∑ k, w k • F.point k) i < F.base i + 1 := by
  have h₀ := F.depth_pos w hw hs i
  have h₁ := F.depth_lt_half w hw hs i
  rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
    simp only [depth, hc, Bool.false_eq_true, ↓reduceIte] at h₀ h₁ <;>
    constructor <;> linarith

/-- Relative interiors of the maximal flag simplices are disjoint, even across
neighboring integer cubes. This is the only uniqueness fact needed to count
an initial affine zero. -/
lemma Flag.eq_of_strict_combination {n : ℕ} (F G : Flag n)
    (w z : Fin (n + 1) → ℝ) (hw : ∀ k, 0 < w k) (hz : ∀ k, 0 ≤ z k)
    (hsw : ∑ k, w k = 1) (hsz : ∑ k, z k = 1)
    (he : ∑ k, w k • F.point k = ∑ k, z k • G.point k) : F = G := by
  have hb : F.base = G.base := by
    funext i
    have hF := F.combination_strict_bounds w hw hsw i
    have hG := G.combination_bounds z hz hsz i
    rw [← he] at hG
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hc : (F.base i : ℝ) + 1 ≤ G.base i := by
        exact_mod_cast (show F.base i + 1 ≤ G.base i by omega)
      linarith
    · have hc : (G.base i : ℝ) + 1 ≤ F.base i := by
        exact_mod_cast (show G.base i + 1 ≤ F.base i by omega)
      linarith
  have hc : F.corner = G.corner := by
    funext i
    have hF := F.depth_lt_half w hw hsw i
    have hG := G.depth_le_half z hz hsz i
    rw [← he] at hG
    cases hf : F.corner i <;> cases hg : G.corner i <;> try rfl
    all_goals
      simp only [depth, ← hb, hf, hg, Bool.false_eq_true, ↓reduceIte] at hF hG
      linarith
  have hd (i : Fin n) (x : Fin n → ℝ) : F.depth i x = G.depth i x := by
    simp only [depth, hb, hc]
  have hm : StrictMono (fun i : Fin n ↦ G.order.symm (F.order i)) := by
    intro i j hij
    by_contra hnot
    have hle : G.order.symm (F.order j) ≤ G.order.symm (F.order i) := le_of_not_gt hnot
    have hG := G.depth_antitone z hz hsz (F.order j) (F.order i) hle
    have hF := F.depth_strictAnti w hw hsw (F.order i) (F.order j) (by simpa using hij)
    rw [← he, ← hd, ← hd] at hG
    linarith
  have ho : F.order = G.order := by
    ext i
    have hh := congrFun hm.eq_id i
    have ha := congrArg G.order hh
    exact congrArg Fin.val (by simpa only [Equiv.apply_symm_apply, id_eq] using ha)
  exact Flag.ext hb hc ho


/-- The corner vertex controls strict distance from the midplanes. -/
lemma Flag.depth_lt_half_of_pos_zero {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (h₀ : 0 < w 0)
    (hs : ∑ k, w k = 1) (i : Fin n) :
    F.depth i (∑ k, w k • F.point k) < 1 / 2 := by
  rw [F.depth_combination i w F.point hs]
  calc
    _ < ∑ k, w k * (1 / 2) := by
      apply Finset.sum_lt_sum
      · intro k _
        apply mul_le_mul_of_nonneg_left _ (hw k)
        rw [F.depth_point]
        split_ifs <;> norm_num
      · refine ⟨0, Finset.mem_univ _, ?_⟩
        rw [F.depth_point]
        simp only [Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, mul_zero]
        exact mul_pos h₀ (by norm_num)
    _ = 1 / 2 := by rw [← Finset.sum_mul, hs, one_mul]

lemma Flag.depth_pos_of_weight {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (i : Fin n) (k : Fin (n + 1)) (hk : (F.order.symm i).val < k.val) (hkw : 0 < w k) :
    0 < F.depth i (∑ k, w k • F.point k) := by
  rw [F.depth_combination i w F.point hs]
  apply Finset.sum_pos'
  · intro l _
    have hl := hw l
    rw [F.depth_point]
    split_ifs <;> positivity
  · refine ⟨k, Finset.mem_univ _, ?_⟩
    rw [F.depth_point, ite_eq_left hk]
    exact mul_pos hkw (by norm_num)

lemma Flag.depth_strictAnti_of_weight {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (i j : Fin n) (hij : F.order.symm i < F.order.symm j)
    (hpos : 0 < w (F.order.symm i).succ) :
    F.depth j (∑ k, w k • F.point k) < F.depth i (∑ k, w k • F.point k) := by
  rw [F.depth_combination i w F.point hs, F.depth_combination j w F.point hs]
  apply Finset.sum_lt_sum
  · intro k _
    apply mul_le_mul_of_nonneg_left _ (hw k)
    rw [F.depth_point, F.depth_point]
    split_ifs <;> try norm_num
    exact False.elim (by omega)
  · refine ⟨(F.order.symm i).succ, Finset.mem_univ _, ?_⟩
    rw [F.depth_point, F.depth_point]
    simp only [Fin.val_succ]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    nlinarith

/-- Bottom-facet interiors are disjoint among flags on the same side of the
bottom hyperplane. The last coordinate expanded is the time coordinate `t`. -/
lemma Flag.eq_of_facet_combination {n : ℕ} [NeZero n] (F G : Flag n)
    (t : Fin n) (ht : (F.order.symm t).val = n - 1)
    (hbt : F.base t = G.base t) (hct : F.corner t = G.corner t)
    (w z : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hwp : ∀ k, k ≠ Fin.last n → 0 < w k) (hz : ∀ k, 0 ≤ z k)
    (hsw : ∑ k, w k = 1) (hsz : ∑ k, z k = 1)
    (he : ∑ k, w k • F.point k = ∑ k, z k • G.point k) : F = G := by
  have hn : n ≠ 0 := NeZero.ne n
  have hw₀ : 0 < w 0 := hwp 0 (by intro h; have hh := congrArg Fin.val h; simp at hh; omega)
  have hdep (i : Fin n) (hi : i ≠ t) : 0 < F.depth i (∑ k, w k • F.point k) := by
    have hp : (F.order.symm i).val < n - 1 := by
      have hne : F.order.symm i ≠ F.order.symm t := fun h ↦ hi (F.order.symm.injective h)
      have hval : (F.order.symm i).val ≠ (F.order.symm t).val := fun h ↦ hne (Fin.ext h)
      have := (F.order.symm i).isLt
      omega
    apply F.depth_pos_of_weight w hw hsw i (F.order.symm i).succ (by simp)
    apply hwp
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_succ, Fin.val_last] at hv
    omega
  have hb : F.base = G.base := by
    funext i
    by_cases hi : i = t
    · simpa only [hi] using hbt
    have h₀ := hdep i hi
    have h₁ := F.depth_lt_half_of_pos_zero w hw hw₀ hsw i
    have hF : (F.base i : ℝ) < (∑ k, w k • F.point k) i ∧
        (∑ k, w k • F.point k) i < F.base i + 1 := by
      rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
        simp only [depth, hc, Bool.false_eq_true, ↓reduceIte] at h₀ h₁ <;>
        constructor <;> linarith
    have hG := G.combination_bounds z hz hsz i
    rw [← he] at hG
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hc : (F.base i : ℝ) + 1 ≤ G.base i := by
        exact_mod_cast (show F.base i + 1 ≤ G.base i by omega)
      linarith
    · have hc : (G.base i : ℝ) + 1 ≤ F.base i := by
        exact_mod_cast (show G.base i + 1 ≤ F.base i by omega)
      linarith
  have hc : F.corner = G.corner := by
    funext i
    by_cases hi : i = t
    · simpa only [hi] using hct
    have hF := F.depth_lt_half_of_pos_zero w hw hw₀ hsw i
    have hG := G.depth_le_half z hz hsz i
    rw [← he] at hG
    cases hf : F.corner i <;> cases hg : G.corner i <;> try rfl
    all_goals
      simp only [depth, ← hb, hf, hg, Bool.false_eq_true, ↓reduceIte] at hF hG
      linarith
  have hd (i : Fin n) (x : Fin n → ℝ) : F.depth i x = G.depth i x := by
    simp only [depth, hb, hc]
  have hm : StrictMono (fun i : Fin n ↦ G.order.symm (F.order i)) := by
    intro i j hij
    by_contra hnot
    have hle : G.order.symm (F.order j) ≤ G.order.symm (F.order i) := le_of_not_gt hnot
    have hG := G.depth_antitone z hz hsz (F.order j) (F.order i) hle
    have hF := F.depth_strictAnti_of_weight w hw hsw (F.order i) (F.order j)
      (by simpa using hij) (by
        apply hwp
        intro h
        have hh := congrArg Fin.val h
        simp only [Equiv.symm_apply_apply, Fin.val_succ, Fin.val_last] at hh
        have := j.isLt
        have : i.val < j.val := hij
        omega)
    rw [← he, ← hd, ← hd] at hG
    linarith
  have ho : F.order = G.order := by
    ext i
    have hh := congrFun hm.eq_id i
    have ha := congrArg G.order hh
    exact congrArg Fin.val (by simpa only [Equiv.apply_symm_apply, id_eq] using ha)
  exact Flag.ext hb hc ho

/-- A shared facet whose vertices have trivial stabilizers cannot identify its
two incident flags under a reflection action. The hypothesis will be supplied
by the positive distance from zero-row strata. -/
lemma Flag.neighbor_ne_reflect_of_free {n : ℕ} [NeZero n] (F : Flag n)
    (j : Fin (n + 1)) (s : Signs n)
    (hfree : ∀ k : Fin (n + 1),
      (∀ i, (if s.val i then -F.vertex k i else F.vertex k i) = F.vertex k i) → s = 1) :
    F.neighbor j ≠ s • F := by
  intro he
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1), k ≠ j := by
    by_cases hj : j.val = 0
    · exact ⟨⟨n, by omega⟩, by intro h; have hh := congrArg Fin.val h; simp at hh; omega⟩
    · exact ⟨0, by intro h; have hh := congrArg Fin.val h; simp at hh; omega⟩
  have hs : s = 1 := by
    apply hfree k
    intro i
    have hv := congrArg (fun G : Flag n ↦ G.vertex k i) he
    rw [F.neighbor_vertex j k hk] at hv
    simpa only [smul_def, reflect_vertex] using hv.symm
  rw [hs, one_smul] at he
  exact F.neighbor_ne j he

end SharpLiebThirring.CubeFlags

end

end OAI
