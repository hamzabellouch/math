import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Total

namespace OAI

namespace LargeIndependentSets
namespace ShortestPaths
open scoped ENNReal

def circleCost {D : ℕ} (x y : ZMod D) : ℕ :=
  min (x-y).val (D-(x-y).val)

lemma circleCost_dist {D : ℕ} [NeZero D] (x y : ZMod D) :
    dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) = (circleCost x y : ℝ)/D := by
  rw [dist_eq_norm,← map_sub,ZMod.toAddCircle_apply]
  have hh := AddCircle.norm_div_natCast (p:=(1:ℝ)) (m:=(x-y).val) (n:=D)
  simpa only [mul_one,one_mul,Nat.mod_eq_of_lt (ZMod.val_lt _),circleCost] using hh

lemma circleCost_edist {D : ℕ} [NeZero D] (x y : ZMod D) :
    edist (ZMod.toAddCircle x) (ZMod.toAddCircle y) = (circleCost x y : ℝ≥0∞)/D := by
  have hd : 0 < (D:ℝ) := by exact_mod_cast (NeZero.pos D)
  rw [edist_dist,circleCost_dist,ENNReal.ofReal_div_of_pos hd]
  simp only [ENNReal.ofReal_natCast]

lemma natSupCast {α : Type*} (s : Finset α) (f : α → ℕ) :
    ((s.sup f : ℕ) : ℝ≥0∞) = s.sup (fun a => (f a : ℝ≥0∞)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sup_insert,Finset.sup_insert,← ih]
    by_cases h : f a ≤ s.sup f
    · have hc : (f a : ℝ≥0∞) ≤ ((s.sup f : ℕ) : ℝ≥0∞) := by exact_mod_cast h
      simp only [max_eq_right h,max_eq_right hc]
    · have h' := le_of_lt (lt_of_not_ge h)
      have hc : ((s.sup f : ℕ) : ℝ≥0∞) ≤ (f a : ℝ≥0∞) := by exact_mod_cast h'
      simp only [max_eq_left h',max_eq_left hc]

def copyCost {Q : Type*} [DecidableEq Q] {M : Q → Type*} [∀ q, Fintype (M q)]
    {D : ℕ} (x y : GridLocation M D) : ℕ∞ :=
  if h : x.1 = y.1 then
    (Finset.univ.sup (fun k : M x.1 => circleCost (x.2 k) (y.2 (h ▸ k))) : ℕ)
  else ⊤

lemma copyCost_exact {Q : Type*} [DecidableEq Q] {M : Q → Type*} [∀ q, Fintype (M q)]
    {D : ℕ} [NeZero D] (x y : GridLocation M D) :
    (copyCost x y : ℝ≥0∞)/(D:ℝ≥0∞) = copyLength x y := by
  unfold copyCost copyLength
  split_ifs with h
  · simp only [ENat.toENNReal_coe,natSupCast,Finset.sup_eq_iSup,Finset.mem_univ,
      iSup_pos,ENNReal.iSup_div,circleCost_edist]
  · exact ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top D)

lemma forwardZero_iff {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} (x y : GridLocation M D) :
    S.ForwardZero D x y ↔ ∃ π : M x.1 → M y.1, S.imposed x.1 y.1 π ∧ x.2 = y.2 ∘ π := by
  constructor
  · intro h
    cases h with
    | link q q' π h v => exact ⟨π,h,rfl⟩
  · rintro ⟨π,hπ,h⟩
    rcases x with ⟨q,x⟩
    rcases y with ⟨q',y⟩
    dsimp at *
    rw [h]
    exact .link q q' π hπ y

instance forwardZero_decidable {Q : Type*} {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] (x y : GridLocation M D) : Decidable (S.ForwardZero D x y) :=
  decidable_of_iff _ (forwardZero_iff S x y).symm

instance zeroLink_decidable {Q : Type*} {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] (x y : GridLocation M D) : Decidable (S.ZeroLink D x y) :=
  inferInstanceAs (Decidable (S.ForwardZero D x y ∨ S.ForwardZero D y x))

def linkCost {Q : Type*} [DecidableEq Q] {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] (x y : GridLocation M D) : ℕ∞ :=
  if S.ZeroLink D x y then 0 else copyCost x y

lemma linkCost_exact {Q : Type*} [DecidableEq Q] {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] (x y : GridLocation M D) :
    (linkCost S x y : ℝ≥0∞)/(D:ℝ≥0∞) = S.linkLength x y := by
  unfold linkCost ProjectionSystem.linkLength
  split_ifs
  · simp
  · exact copyCost_exact x y

lemma scaled_min (d : ℝ≥0∞) (a b : ℕ∞) :
    ((min a b : ℕ∞) : ℝ≥0∞)/d = min ((a:ℝ≥0∞)/d) ((b:ℝ≥0∞)/d) := by
  rcases le_total a b with h | h
  · have hh := ENNReal.div_le_div_right (ENat.toENNReal_le.mpr h) d
    simp only [min_eq_left h,min_eq_left hh]
  · have hh := ENNReal.div_le_div_right (ENat.toENNReal_le.mpr h) d
    simp only [min_eq_right h,min_eq_right hh]

lemma Matrix.scaled_allPairs_exact {n : ℕ} (a : Matrix n) (D : ℕ) (i j : Fin n) :
    (a.allPairs.get i j : ℝ≥0∞)/(D:ℝ≥0∞) =
      pathDistance (fun x y => (a.get x y : ℝ≥0∞)/(D:ℝ≥0∞)) i j := by
  rw [Matrix.allPairs,Matrix.run_get]
  have hm := congrFun (congrFun (closure_map (fun z : ℕ∞ => (z:ℝ≥0∞)/(D:ℝ≥0∞))
    (scaled_min _) (fun a b => by rw [ENat.toENNReal_add,ENNReal.add_div])
    a.get (List.finRange n)) i) j
  rw [hm]
  exact closure_eq_distance _ _ (fun z => List.mem_finRange z) i j

lemma walkLength_reindex {X Y : Type*} (e : X → Y) (w : Y → Y → ℝ≥0∞) (x : X)
    (zs : List X) (y : X) :
    walkLength (fun x y => w (e x) (e y)) x zs y = walkLength w (e x) (zs.map e) (e y) := by
  induction zs generalizing x with
  | nil => rfl
  | cons z zs ih => simp only [walkLength,List.map_cons,ih]

lemma pathDistance_reindex {X Y : Type*} (e : X ≃ Y) (w : Y → Y → ℝ≥0∞) (x y : X) :
    pathDistance (fun x y => w (e x) (e y)) x y = pathDistance w (e x) (e y) := by
  unfold pathDistance
  apply le_antisymm
  · apply le_iInf
    intro zs
    apply iInf_le_of_le (zs.map e.symm)
    rw [walkLength_reindex]
    simp
  · apply le_iInf
    intro zs
    rw [walkLength_reindex]
    exact iInf_le_of_le (zs.map e) le_rfl

def gridMatrix {Q : Type*} [DecidableEq Q] {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] {n : ℕ} (e : Fin n ≃ GridLocation M D) : Matrix n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => linkCost S (e i) (e j)))

theorem grid_allPairs_exact {Q : Type*} [DecidableEq Q] {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] {n : ℕ} (e : Fin n ≃ GridLocation M D) (i j : Fin n) :
    ((gridMatrix S e).allPairs.get i j : ℝ≥0∞)/(D:ℝ≥0∞) =
      pathDistance S.linkLength (e i) (e j) := by
  rw [Matrix.scaled_allPairs_exact]
  have hh : (fun x y => ((gridMatrix S e).get x y : ℝ≥0∞)/(D:ℝ≥0∞)) =
      (fun x y => S.linkLength (e x) (e y)) := by
    funext x y
    simpa only [gridMatrix,Matrix.get,Vector.getElem_ofFn] using linkCost_exact S (e x) (e y)
  rw [hh,pathDistance_reindex]

end ShortestPaths
end LargeIndependentSets

end OAI
