import OAI.Probability.SATComputability.RationalHierarchy
import OAI.Probability.SATComputability.ArithmeticConstructors

namespace OAI

namespace FixedClauseThreshold.Computability

open Encodable Denumerable Nat.Partrec FiniteArithmetic
open scoped BigOperators
local instance hierarchyEncodingRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def branchEntry : Code → ℚ × Code
  | .comp w c => (decodedRational w, c)
  | _ => (0, .zero)

noncomputable def rawBranches : Code → List (ℚ × Code)
  | .pair c rest => branchEntry c :: rawBranches rest
  | _ => []

noncomputable def encodeBranches (bs : List (ℚ × Code)) : Code :=
  bs.foldr (fun b rest => .pair (.comp (ofNat Code (encode b.1)) b.2) rest) .zero

theorem rawBranches_encode (bs : List (ℚ × Code)) : rawBranches (encodeBranches bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [encodeBranches, List.foldr_cons, rawBranches, branchEntry, decodedRational,
      encode_ofNat, encodek, Option.getD_some]
    exact congrArg (b :: ·) ih

noncomputable def normalizedBranches (c : Code) : List (ℚ × Code) :=
  let bs := rawBranches c
  let s := (bs.map (fun b => |b.1|)).sum
  if s = 0 then [(1, .zero)] else bs.map (fun b => (|b.1|/s, b.2))

theorem normalizedBranches_nonneg (c : Code) :
    ∀ b ∈ normalizedBranches c, 0 ≤ b.1 := by
  dsimp only [normalizedBranches]
  split_ifs with hs
  · simp
  · intro b hb
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
    exact div_nonneg (abs_nonneg _) (List.sum_nonneg (fun _ hx => by
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact abs_nonneg _))

theorem normalizedBranches_sum (c : Code) :
    ((normalizedBranches c).map Prod.fst).sum = 1 := by
  dsimp only [normalizedBranches]
  split_ifs with hs
  · simp
  · simp only [List.map_map, Function.comp_def]
    simp only [div_eq_mul_inv]
    rw [List.sum_map_mul_right]
    exact mul_inv_cancel₀ hs

theorem normalizedBranches_encode {bs : List (ℚ × Code)}
    (hpos : ∀ b ∈ bs, 0 ≤ b.1) (hs : (bs.map Prod.fst).sum = 1) :
    normalizedBranches (encodeBranches bs) = bs := by
  have ha : bs.map (fun b => |b.1|) = bs.map Prod.fst := by
    apply List.map_congr_left
    intro b hb
    exact abs_of_nonneg (hpos b hb)
  simp only [normalizedBranches, rawBranches_encode, ha, hs, one_ne_zero, ite_false, div_one]
  conv_rhs => rw [← List.map_id bs]
  apply List.map_congr_left
  intro b hb
  exact Prod.ext (abs_of_nonneg (hpos b hb)) rfl

noncomputable def branchWeights (c : Code) :
    RationalWeights (Fin (normalizedBranches c).length) :=
  ⟨fun i => ((normalizedBranches c).get i).1, by
    constructor
    · intro i
      exact normalizedBranches_nonneg c _ (List.get_mem _ _)
    · have h : (List.ofFn (fun i : Fin (normalizedBranches c).length =>
          ((normalizedBranches c).get i).1)).sum = 1 := by
        simp only [List.get_eq_getElem]
        rw [List.ofFn_getElem_eq_map, normalizedBranches_sum]
      simpa only [List.sum_ofFn] using h⟩

noncomputable def decodeTree : (r : ℕ) → Code → RationalTree r
  | 0, c => decodedRational c
  | r+1, c => ⟨(normalizedBranches c).length, branchWeights c,
      fun i => decodeTree r ((normalizedBranches c).get i).2⟩

noncomputable def encodeTree : (r : ℕ) → RationalTree r → Code
  | 0, q => ofNat Code (@encode ℚ Rat.instEncodable q)
  | r+1, t => encodeBranches (List.ofFn (fun i : Fin t.1 =>
      (t.2.1.val i, encodeTree r (t.2.2 i))))

theorem normalizedBranches_encodeTree (r : ℕ) (t : RationalTree (r+1)) :
    normalizedBranches (encodeTree (r+1) t) =
      List.ofFn (fun i : Fin t.1 => (t.2.1.val i, encodeTree r (t.2.2 i))) := by
  apply normalizedBranches_encode
  · intro b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact t.2.1.property.1 i
  · rw [List.map_ofFn, List.sum_ofFn]
    exact t.2.1.property.2

theorem rationalTree_node_ext {r n k : ℕ} (hn : n = k)
    (w : RationalWeights (Fin n)) (v : RationalWeights (Fin k))
    (x : Fin n → RationalTree r) (y : Fin k → RationalTree r)
    (hw : ∀ i, w.val i = v.val (Fin.cast hn i))
    (hx : ∀ i, x i = y (Fin.cast hn i)) :
    (⟨n, w, x⟩ : RationalTree (r+1)) = ⟨k, v, y⟩ := by
  subst k
  apply congrArg (Sigma.mk n)
  apply Prod.ext
  · exact Subtype.ext (funext hw)
  · exact funext hx

theorem decodeTree_encodeTree (r : ℕ) (t : RationalTree r) :
    decodeTree r (encodeTree r t) = t := by
  induction r with
  | zero =>
    change decodedRational (ofNat Code (@encode ℚ Rat.instEncodable t)) = t
    simp only [decodedRational, encode_ofNat]
    exact congrArg (fun o : Option ℚ => o.getD 0) (@Encodable.encodek ℚ Rat.instEncodable t)
  | succ r ih =>
    obtain ⟨n, w, x⟩ := t
    let c := encodeTree (r+1) ⟨n, w, x⟩
    have he : normalizedBranches c =
        List.ofFn (fun i : Fin n => (w.val i, encodeTree r (x i))) :=
      normalizedBranches_encodeTree r ⟨n, w, x⟩
    change (⟨(normalizedBranches c).length, branchWeights c,
      fun i => decodeTree r ((normalizedBranches c).get i).2⟩ :
        Σ k : ℕ, RationalWeights (Fin k) × (Fin k → RationalTree r)) = ⟨n, w, x⟩
    have hn : (normalizedBranches c).length = n := by rw [he, List.length_ofFn]
    apply rationalTree_node_ext hn
    · intro i
      change ((normalizedBranches c).get i).1 = w.val (Fin.cast hn i)
      simp only [List.get_eq_getElem, he, List.getElem_ofFn]
      rfl
    · intro i
      simp only [List.get_eq_getElem, he, List.getElem_ofFn]
      exact ih (x (Fin.cast hn i))

theorem decodeTree_surjective (r : ℕ) : Function.Surjective (decodeTree r) :=
  fun t => ⟨encodeTree r t, decodeTree_encodeTree r t⟩

end FixedClauseThreshold.Computability

end OAI
