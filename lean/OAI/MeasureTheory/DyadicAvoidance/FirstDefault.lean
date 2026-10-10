import Mathlib

namespace OAI

universe u_Ω

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.FirstDefault

abbrev Address (M : ℕ) := List (Fin (M + 1)) × Fin M
abbrev Path (M d : ℕ) := Fin d → Fin M
abbrev Tests {M d : ℕ} (f : Path M d) := (k : Fin d) × Fin ((f k).val + 1)

/-- The node immediately before the `k`th decision along a nondefault path. -/
def pathPrefix {M d : ℕ} (f : Path M d) (k : Fin d) : List (Fin (M + 1)) :=
  List.ofFn fun j : Fin k.val => (f ⟨j.val, lt_trans j.isLt k.isLt⟩).castSucc

lemma pathPrefix_eq_take_ofFn {M d : ℕ} (f : Path M d) (k : Fin d) :
    pathPrefix f k = (List.ofFn fun j => (f j).castSucc).take k.val := by
  exact Fin.ofFn_take_eq_take_ofFn k.isLt.le (fun j => (f j).castSucc)

/-- Every earlier rejected selector and the selected selector are tested. -/
def address {M d : ℕ} (f : Path M d) (i : Tests f) : Address M :=
  (pathPrefix f i.1, ⟨i.2.val, lt_of_lt_of_le i.2.isLt (Nat.succ_le_of_lt (f i.1).isLt)⟩)

def requiredBit {M d : ℕ} (f : Path M d) (i : Tests f) : Bool :=
  decide (i.2.val = (f i.1).val)

/-- The selector cylinder expressing that a prescribed path is followed. -/
def cylinder {M d : ℕ} {Ω : Type u_Ω} (S : Address M → Ω → Bool)
    (f : Path M d) : Set Ω :=
  {ω | ∀ i : Tests f, S (address f i) ω = requiredBit f i}

lemma address_injective {M d : ℕ} (f : Path M d) :
    Function.Injective (address f) := by
  rintro ⟨k, i⟩ ⟨l, j⟩ h
  have hlen := congrArg (fun a : Address M => a.1.length) h
  simp only [address, pathPrefix, List.length_ofFn] at hlen
  have hkl : k = l := Fin.ext hlen
  subst l
  have hij := congrArg (fun a : Address M => a.2.val) h
  simp only [address] at hij
  have : i = j := Fin.ext hij
  subst j
  rfl

lemma measure_cylinder_of_local {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Address M → Ω → Bool) (f : Path M d)
    (hi : iIndepFun (fun i : Tests f => S (address f i)) μ)
    (hfair : ∀ i : Tests f, ∀ b, μ (S (address f i) ⁻¹' {b}) = (2 : ENNReal)⁻¹) :
    μ (cylinder S f) = ∏ k : Fin d, ((2 : ENNReal)⁻¹) ^ ((f k).val + 1) := by
  classical
  have h := hi.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i : Tests f => {requiredBit f i}) (by intro i _; exact measurableSet_singleton _)
  have heq : (⋂ i : Tests f, ⋂ (_ : i ∈ Finset.univ),
      S (address f i) ⁻¹' {requiredBit f i}) = cylinder S f := by
    ext ω
    simp [cylinder]
  rw [heq] at h
  rw [h]
  simp only [hfair]
  rw [Fintype.prod_sigma]
  simp

lemma measure_cylinder {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Address M → Ω → Bool)
    (hIndep : iIndepFun S μ)
    (hfair : ∀ a b, μ (S a ⁻¹' {b}) = (2 : ENNReal)⁻¹)
    (f : Path M d) :
    μ (cylinder S f) = ∏ k : Fin d, ((2 : ENNReal)⁻¹) ^ ((f k).val + 1) :=
  measure_cylinder_of_local μ S f (hIndep.precomp (address_injective f))
    (fun _ b => hfair _ b)

lemma cylinder_disjoint_of_prefix {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (f g : Path M d) (k : Fin d)
    (hprefix : pathPrefix f k = pathPrefix g k) (hlt : f k < g k) :
    Disjoint (cylinder S f) (cylinder S g) := by
  apply Set.disjoint_left.mpr
  intro ω hf hg
  have h1 := hf ⟨k, ⟨(f k).val, Nat.lt_succ_self _⟩⟩
  have h2 := hg ⟨k, ⟨(f k).val, lt_trans hlt (Nat.lt_succ_self _)⟩⟩
  have ha : (address f ⟨k, ⟨(f k).val, Nat.lt_succ_self _⟩⟩) =
      address g ⟨k, ⟨(f k).val, lt_trans hlt (Nat.lt_succ_self _)⟩⟩ := by
    simp only [address, hprefix]
  have hb1 : requiredBit f ⟨k, ⟨(f k).val, Nat.lt_succ_self _⟩⟩ = true := by
    simp [requiredBit]
  have hb2 : requiredBit g
      ⟨k, ⟨(f k).val, lt_trans hlt (Nat.lt_succ_self _)⟩⟩ = false := by
    have hne : (f k).val ≠ (g k).val := Nat.ne_of_lt hlt
    simp [requiredBit, hne]
  rw [hb1, ha] at h1
  rw [hb2, h1] at h2
  cases h2

lemma cylinders_pairwiseDisjoint {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) : Pairwise (fun f g : Path M d => Disjoint (cylinder S f) (cylinder S g)) := by
  classical
  intro f g hfg
  have hex : ∃ k, f k ≠ g k := by
    by_contra! h
    exact hfg (funext h)
  let T : Finset (Fin d) := Finset.univ.filter fun k => f k ≠ g k
  have hT : T.Nonempty := by
    obtain ⟨k, hk⟩ := hex
    exact ⟨k, by simp [T, hk]⟩
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image T (fun i => i) hT
  have hkne : f k ≠ g k := (Finset.mem_filter.mp hk).2
  have hearlier : ∀ j : Fin d, j < k → f j = g j := by
    intro j hj
    by_contra hne
    exact (not_le_of_gt hj) (hmin j (by simp [T, hne]))
  have hprefix : pathPrefix f k = pathPrefix g k := by
    unfold pathPrefix
    congr 1
    funext j
    rw [hearlier ⟨j.val, lt_trans j.isLt k.isLt⟩ j.isLt]
  rcases lt_or_gt_of_ne hkne with hlt | hgt
  · exact cylinder_disjoint_of_prefix S f g k hprefix hlt
  · exact (cylinder_disjoint_of_prefix S g f k hprefix.symm hgt).symm

lemma measurableSet_cylinder {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (S : Address M → Ω → Bool) (hS : ∀ a, Measurable (S a)) (f : Path M d) :
    MeasurableSet (cylinder S f) := by
  simp only [cylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => (hS _) (measurableSet_singleton _)

lemma sum_geometric_weights (M : ℕ) :
    (∑ i : Fin M, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) =
      1 - ((2 : ENNReal)⁻¹) ^ M := by
  have hadd (n : ℕ) :
      (∑ i : Fin n, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) +
        ((2 : ENNReal)⁻¹) ^ n = 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hq : (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1 := ENNReal.inv_two_add_inv_two
      calc
        (∑ i : Fin n, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) +
            ((2 : ENNReal)⁻¹) ^ (n + 1) + ((2 : ENNReal)⁻¹) ^ (n + 1) =
          (∑ i : Fin n, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) +
            ((2 : ENNReal)⁻¹) ^ n * ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹) := by
              rw [pow_succ]
              ring
        _ = 1 := by rw [hq, mul_one]; exact ih
  exact ENNReal.eq_sub_of_add_eq (by finiteness) (hadd M)

/-- Probability that a full depth-`d` center path never chooses the default child.
The event is expressed as the union of its explicit nondefault path cylinders. -/
theorem measure_no_default {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Address M → Ω → Bool)
    (hS : ∀ a, Measurable (S a)) (hIndep : iIndepFun S μ)
    (hfair : ∀ a b, μ (S a ⁻¹' {b}) = (2 : ENNReal)⁻¹) :
    μ (⋃ f : Path M d, cylinder S f) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  classical
  rw [measure_iUnion (cylinders_pairwiseDisjoint S) (measurableSet_cylinder S hS),
    tsum_fintype]
  simp_rw [measure_cylinder μ S hIndep hfair]
  calc
    _ = (∑ i : Fin M, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) ^ d :=
      (Fintype.sum_pow (fun i : Fin M => ((2 : ENNReal)⁻¹) ^ (i.val + 1)) d).symm
    _ = _ := by rw [sum_geometric_weights]

/-- Local independence suffices: only the finitely many addresses on each
prescribed path are required to be independent and fair. -/
theorem measure_no_default_of_local {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Address M → Ω → Bool)
    (hS : ∀ a, Measurable (S a))
    (hIndep : ∀ f : Path M d, iIndepFun (fun i : Tests f => S (address f i)) μ)
    (hfair : ∀ f : Path M d, ∀ i : Tests f, ∀ b,
      μ (S (address f i) ⁻¹' {b}) = (2 : ENNReal)⁻¹) :
    μ (⋃ f : Path M d, cylinder S f) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  classical
  rw [measure_iUnion (cylinders_pairwiseDisjoint S) (measurableSet_cylinder S hS),
    tsum_fintype]
  simp_rw [measure_cylinder_of_local μ S _ (hIndep _) (hfair _)]
  calc
    _ = (∑ i : Fin M, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) ^ d :=
      (Fintype.sum_pow (fun i : Fin M => ((2 : ENNReal)⁻¹) ^ (i.val + 1)) d).symm
    _ = _ := by rw [sum_geometric_weights]

abbrev BoundedAddress (M d : ℕ) := {a : Address M // a.1.length < d}

lemma address_length_lt {M d : ℕ} (f : Path M d) (i : Tests f) :
    (address f i).1.length < d := by
  simpa only [address, pathPrefix, List.length_ofFn] using i.1.isLt

def boundedAddress {M d : ℕ} (f : Path M d) (i : Tests f) : BoundedAddress M d :=
  ⟨address f i, address_length_lt f i⟩

lemma boundedAddress_injective {M d : ℕ} (f : Path M d) :
    Function.Injective (boundedAddress f) := by
  intro i j h
  exact address_injective f (congrArg Subtype.val h)

/-- Finite-tree version: no randomness outside nodes of depth less than `d`
is assumed. This is the interface for the actual finite table model. -/
theorem measure_no_default_bounded {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : BoundedAddress M d → Ω → Bool)
    (hS : ∀ a, Measurable (S a)) (hIndep : iIndepFun S μ)
    (hfair : ∀ a b, μ (S a ⁻¹' {b}) = (2 : ENNReal)⁻¹) :
    μ (⋃ f : Path M d,
      {ω | ∀ i : Tests f, S (boundedAddress f i) ω = requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  classical
  let S' : Address M → Ω → Bool := fun a ω =>
    if h : a.1.length < d then S ⟨a, h⟩ ω else false
  have heval (f : Path M d) (i : Tests f) :
      S' (address f i) = S (boundedAddress f i) := by
    funext ω
    simp only [S', dite_eq_left (address_length_lt f i), boundedAddress]
  have hS' : ∀ a, Measurable (S' a) := by
    intro a
    dsimp only [S']
    split
    · exact hS _
    · exact measurable_const
  have hi : ∀ f : Path M d, iIndepFun (fun i : Tests f => S' (address f i)) μ := by
    intro f
    simp_rw [heval]
    exact hIndep.precomp (boundedAddress_injective f)
  have hf : ∀ f : Path M d, ∀ i : Tests f, ∀ b,
      μ (S' (address f i) ⁻¹' {b}) = (2 : ENNReal)⁻¹ := by
    intro f i b
    rw [heval]
    exact hfair _ b
  have h := measure_no_default_of_local μ S' hS' hi hf
  simpa only [cylinder, heval] using h

end Problem310.FirstDefault

end

end OAI
