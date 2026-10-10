import OAI.NumberTheory.ShortEgyptian.Model

namespace OAI

namespace ShortEgyptian

def unitSum (ns : List ℕ) : ℚ :=
  (ns.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum

theorem isExpansion_iff (a b : ℕ) (ns : List ℕ) :
    IsExpansion a b ns ↔ ns.Pairwise (· < ·) ∧
      (∀ n ∈ ns, 2 ≤ n) ∧ unitSum ns = (a : ℚ) / b := by
  have heq : (ns.map (fun n => (1 : ℚ) / (n : ℚ))).sum = unitSum ns := by
    induction ns with
    | nil => rfl
    | cons n ns ih => simpa [unitSum] using congrArg ((1 : ℚ) / (n : ℚ) + ·) ih
  simp only [IsExpansion, heq]

def IsUnitSum (x : ℚ) (ns : List ℕ) : Prop :=
  (∀ n ∈ ns, 2 ≤ n) ∧ unitSum ns = x

noncomputable def quotient (v u : ℕ) : ℕ := ⌈(v : ℚ) / (u : ℚ)⌉₊

def residue (v u z : ℕ) : ℕ := u * z - v

theorem quotient_spec {v u : ℕ} (hv : 0 < v) (hu : 0 < u) :
    0 < quotient v u ∧ v ≤ u * quotient v u ∧
      u * quotient v u < v + u := by
  have hvq : (0 : ℚ) < v := by exact_mod_cast hv
  have huq : (0 : ℚ) < u := by exact_mod_cast hu
  have hlo := (div_le_iff₀ huq).mp (Nat.le_ceil ((v : ℚ) / u))
  have hhi := Nat.ceil_lt_add_one (le_of_lt (div_pos hvq huq))
  have hhi' := mul_lt_mul_of_pos_right hhi huq
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt huq), one_mul] at hhi'
  refine ⟨Nat.ceil_pos.mpr (div_pos hvq huq), ?_, ?_⟩
  · change v ≤ u * ⌈(v : ℚ) / u⌉₊
    exact_mod_cast (show (v : ℚ) ≤ u * (⌈(v : ℚ) / u⌉₊ : ℚ) by nlinarith [hlo])
  · change u * ⌈(v : ℚ) / u⌉₊ < v + u
    exact_mod_cast (show (u : ℚ) * (⌈(v : ℚ) / u⌉₊ : ℚ) < v + u by nlinarith [hhi'])

theorem residue_spec {v u : ℕ} (hv : 0 < v) (hu : 0 < u) :
    residue v u (quotient v u) < u ∧
      v + residue v u (quotient v u) = u * quotient v u := by
  obtain ⟨_, hlo, hhi⟩ := quotient_spec hv hu
  unfold residue
  omega

theorem residue_identity {M Q u t : ℕ} (hM : 0 < M) (hQ : 0 < Q)
    (hu : 0 < u) (ht : 0 < t) (htM : t ∣ M) :
    let z := quotient (Q * t) u
    let h := residue (Q * t) u z
    (u : ℚ) / (M * Q) =
      1 / ((M / t : ℕ) * (z : ℚ)) + (h : ℚ) / (M * Q * z) := by
  dsimp
  let z := quotient (Q * t) u
  let h := residue (Q * t) u z
  change (u : ℚ) / (M * Q) = 1 / ((M / t : ℕ) * (z : ℚ)) + h / (M * Q * z)
  have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  have hQQ : (Q : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hQ
  have hz : 0 < z := (quotient_spec (Nat.mul_pos hQ ht) hu).1
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hz
  have hdNat : M / t * t = M := Nat.div_mul_cancel htM
  have hdpos : 0 < M / t := by nlinarith
  have hdQ : ((M / t : ℕ) : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hdpos
  have hd : ((M / t : ℕ) : ℚ) * t = M := by exact_mod_cast hdNat
  have hh : (Q : ℚ) * t + h = u * z := by
    exact_mod_cast (residue_spec (Nat.mul_pos hQ ht) hu).2
  field_simp
  nlinarith [congrArg (fun x : ℚ => x * (((M / t : ℕ) : ℚ) * Q)) hh]

theorem predecessor_dvd {v u z h : ℕ} (heq : v + h = u * z) : u ∣ v + h := by
  rw [heq]
  exact Nat.dvd_mul_right _ _

@[simp] theorem unitSum_nil : unitSum [] = 0 := rfl

@[simp] theorem unitSum_cons (n : ℕ) (ns : List ℕ) :
    unitSum (n :: ns) = (1 : ℚ) / n + unitSum ns := rfl

@[simp] theorem unitSum_append (xs ys : List ℕ) :
    unitSum (xs ++ ys) = unitSum xs + unitSum ys := by
  simp [unitSum]

theorem unitSum_nonneg (ns : List ℕ) : 0 ≤ unitSum ns := by
  unfold unitSum
  apply List.sum_nonneg
  intro x hx
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hx
  positivity

theorem unit_le_sum {n : ℕ} {ns : List ℕ} (hn : n ∈ ns) :
    (1 : ℚ) / n ≤ unitSum ns := by
  unfold unitSum
  apply List.single_le_sum _ _ (List.mem_map.mpr ⟨n, hn, rfl⟩)
  intro x hx
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
  positivity

theorem unitSum_scale (g : ℕ) (ns : List ℕ) :
    unitSum (ns.map (g * ·)) = unitSum ns / (g : ℚ) := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, unitSum_cons, ih, Nat.cast_mul]
    rw [add_div]
    congr 1
    simp [div_eq_mul_inv, mul_comm]

end ShortEgyptian

end OAI
