import OAI.Geometry.HeilbronnTriangle.DigitUniqueness
import OAI.Geometry.HeilbronnTriangle.DivisorMoment

namespace OAI


namespace Problem355.ConditionalDigits

open scoped BigOperators

theorem encoded_digits_injective {B j m : ℕ} (hB : 1 < B)
    (digit : Fin j → Fin m → ℕ)
    (hdigit : ∀ u a, digit u a < B)
    (hinj : ∀ u, Function.Injective (digit u)) :
    Function.Injective (fun a : Fin j → Fin m =>
      Nat.ofDigits B (List.ofFn (fun u => digit u (a u))) % B ^ j) := by
  intro a c hac
  have hlist := Digits.take_eq_of_ofDigits_mod_eq hB
    (A := List.ofFn (fun u => digit u (a u)))
    (B := List.ofFn (fun u => digit u (c u)))
    (by simp)
    (by simpa only [List.mem_ofFn] using fun x ⟨u, hu⟩ => hu ▸ hdigit u (a u))
    (by simpa only [List.mem_ofFn] using fun x ⟨u, hu⟩ => hu ▸ hdigit u (c u))
    hac
  have hfun : (fun u => digit u (a u)) = (fun u => digit u (c u)) :=
    by
      rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)] at hlist
      exact List.ofFn_injective hlist
  funext u
  exact hinj u (congrFun hfun u)

theorem card_prefix_event_le {α ι : Type*} [Fintype α] [Fintype ι]
    {B j m : ℕ} (hB : 1 < B)
    (digit : ι → Fin j → Fin m → ℕ)
    (hdigit : ∀ i u a, digit i u a < B)
    (hinj : ∀ i u, Function.Injective (digit i u))
    (target : α → ι → ℕ)
    (bad : Finset (α × (ι → Fin j → Fin m)))
    (hbad : ∀ z ∈ bad, ∀ i,
      Nat.ofDigits B (List.ofFn (fun u => digit i u (z.2 i u))) % B ^ j =
        target z.1 i) :
    bad.card ≤ Fintype.card α := by
  classical
  calc
    bad.card ≤ (Finset.univ : Finset α).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro z hz
        exact Finset.mem_univ z.1
      · intro z hz z' hz' hzz'
        apply Prod.ext hzz'
        funext i
        apply encoded_digits_injective hB (digit i) (hdigit i) (hinj i)
        dsimp only
        rw [hbad z hz i, hbad z' hz' i, hzz']
    _ = Fintype.card α := Finset.card_univ

theorem prefix_probability_le {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι]
    {B j m : ℕ} (hB : 1 < B) (hm : 0 < m)
    (digit : ι → Fin j → Fin m → ℕ)
    (hdigit : ∀ i u a, digit i u a < B)
    (hinj : ∀ i u, Function.Injective (digit i u))
    (target : α → ι → ℕ)
    (bad : Finset (α × (ι → Fin j → Fin m)))
    (hbad : ∀ z ∈ bad, ∀ i,
      Nat.ofDigits B (List.ofFn (fun u => digit i u (z.2 i u))) % B ^ j =
        target z.1 i) :
    (bad.card : ℝ) / Fintype.card (α × (ι → Fin j → Fin m)) ≤
      (1 / (m : ℝ)) ^ (Fintype.card ι * j) := by
  have hcard := card_prefix_event_le hB digit hdigit hinj target bad hbad
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : (Fintype.card (α × (ι → Fin j → Fin m)) : ℝ) =
      (Fintype.card α : ℝ) * (m : ℝ) ^ (Fintype.card ι * j) := by
    simp [← pow_mul, Nat.mul_comm]
  rw [hden]
  calc
    (bad.card : ℝ) / ((Fintype.card α : ℝ) * (m : ℝ) ^ (Fintype.card ι * j)) ≤
        (Fintype.card α : ℝ) /
          ((Fintype.card α : ℝ) * (m : ℝ) ^ (Fintype.card ι * j)) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = (1 / (m : ℝ)) ^ (Fintype.card ι * j) := by
      rw [one_div_pow]
      field_simp

theorem card_residue_event_le {α ι X : Type*} [Fintype α] [Fintype ι] [Fintype X]
    {B j k : ℕ} (hB : 1 < B) (hj : j ≤ k)
    (digit : ι → Fin k → X → Fin B)
    (hinj : ∀ i u, Function.Injective (digit i u))
    (target : α → ι → ℕ)
    (bad : Finset (α × (ι → Fin k → X)))
    (hbad : ∀ z ∈ bad, ∀ i,
      (∑ u : Fin k, (digit i u (z.2 i u)).val * B ^ u.val) % B ^ j =
        target z.1 i) :
    bad.card ≤ Fintype.card α * Fintype.card X ^ (Fintype.card ι * (k - j)) := by
  classical
  let lift : Fin (k - j) → Fin k := fun u => ⟨j + u.val, by omega⟩
  let tail : (α × (ι → Fin k → X)) → (α × (ι → Fin (k - j) → X)) :=
    fun z => (z.1, fun i u => z.2 i (lift u))
  have hcard := Finset.card_le_card_of_injOn
    (s := bad) (t := Finset.univ) tail
    (by intro z hz; exact Finset.mem_univ _)
  have htail : Set.InjOn tail (bad : Set (α × (ι → Fin k → X))) := by
    intro z hz z' hz' hzz'
    have hfst : z.1 = z'.1 :=
      congrArg (fun y : α × (ι → Fin (k - j) → X) => y.1) hzz'
    have hsnd := congrArg (fun y : α × (ι → Fin (k - j) → X) => y.2) hzz'
    apply Prod.ext hfst
    funext i
    have hmod :
        (∑ u : Fin k, (digit i u (z.2 i u)).val * B ^ u.val) % B ^ j =
        (∑ u : Fin k, (digit i u (z'.2 i u)).val * B ^ u.val) % B ^ j := by
      rw [hbad z hz i, hbad z' hz' i, hfst]
    have hfirst := Digits.initial_digits_eq_of_sum_mod_eq hB
      (fun u => (digit i u (z.2 i u)).isLt)
      (fun u => (digit i u (z'.2 i u)).isLt) hmod
    funext u
    by_cases hu : u.val < j
    · apply hinj i u
      apply Fin.ext
      exact hfirst u hu
    · let v : Fin (k - j) := ⟨u.val - j, by omega⟩
      have hlift : lift v = u := by
        apply Fin.ext
        dsimp [lift, v]
        omega
      have hv := congrFun (congrFun hsnd i) v
      change z.2 i (lift v) = z'.2 i (lift v) at hv
      simpa only [hlift] using hv
  simpa [← pow_mul, Nat.mul_comm] using hcard htail

theorem residue_event_probability_le {α ι X : Type*}
    [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    {B j k : ℕ} (hB : 1 < B) (hj : j ≤ k)
    (digit : ι → Fin k → X → Fin B)
    (hinj : ∀ i u, Function.Injective (digit i u))
    (target : α → ι → ℕ)
    (bad : Finset (α × (ι → Fin k → X)))
    (hbad : ∀ z ∈ bad, ∀ i,
      (∑ u : Fin k, (digit i u (z.2 i u)).val * B ^ u.val) % B ^ j =
        target z.1 i) :
    (bad.card : ℝ) / Fintype.card (α × (ι → Fin k → X)) ≤
      1 / (Fintype.card X : ℝ) ^ (Fintype.card ι * j) := by
  have hcard := card_residue_event_le hB hj digit hinj target bad hbad
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hden : (Fintype.card (α × (ι → Fin k → X)) : ℝ) =
      (Fintype.card α : ℝ) * (Fintype.card X : ℝ) ^ (Fintype.card ι * k) := by
    simp [← pow_mul, Nat.mul_comm]
  rw [hden]
  apply (div_le_div_iff₀ (by positivity) (pow_pos hX _)).mpr
  simp only [one_mul]
  calc
    (bad.card : ℝ) * (Fintype.card X : ℝ) ^ (Fintype.card ι * j) ≤
        ((Fintype.card α : ℝ) *
          (Fintype.card X : ℝ) ^ (Fintype.card ι * (k - j))) *
            (Fintype.card X : ℝ) ^ (Fintype.card ι * j) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = (Fintype.card α : ℝ) * (Fintype.card X : ℝ) ^ (Fintype.card ι * k) := by
      rw [mul_assoc, ← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hj]

theorem unit_equation_event_probability_le {α ι X : Type*}
    [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    {B j k : ℕ} (hB : 1 < B) (hj : j ≤ k)
    (digit : ι → Fin k → X → Fin B)
    (hinj : ∀ i v, Function.Injective (digit i v))
    (pivot : α → (ZMod (B ^ j))ˣ) (rhs : α → ι → ZMod (B ^ j))
    (bad : Finset (α × (ι → Fin k → X)))
    (hbad : ∀ z ∈ bad, ∀ i,
      (pivot z.1 : ZMod (B ^ j)) *
        ((∑ v : Fin k, (digit i v (z.2 i v)).val * B ^ v.val : ℕ) : ZMod (B ^ j)) =
          rhs z.1 i) :
    (bad.card : ℝ) / Fintype.card (α × (ι → Fin k → X)) ≤
      1 / (Fintype.card X : ℝ) ^ (Fintype.card ι * j) := by
  apply residue_event_probability_le hB hj digit hinj
    (fun a i => ((↑((pivot a)⁻¹) : ZMod (B ^ j)) * rhs a i).val) bad
  intro z hz i
  have heq :
      ((∑ v : Fin k, (digit i v (z.2 i v)).val * B ^ v.val : ℕ) : ZMod (B ^ j)) =
        (↑((pivot z.1)⁻¹) : ZMod (B ^ j)) * rhs z.1 i := by
    calc
      _ = (↑((pivot z.1)⁻¹) : ZMod (B ^ j)) *
          ((pivot z.1 : ZMod (B ^ j)) *
            ((∑ v : Fin k, (digit i v (z.2 i v)).val * B ^ v.val : ℕ) : ZMod (B ^ j))) := by
        simp
      _ = _ := by rw [hbad z hz i]
  simpa only [ZMod.val_natCast] using congrArg ZMod.val heq

theorem conditional_divisor_moment_le_two {α ι X : Type*}
    [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : 1 < B)
    (digit : ι → Fin k → X → Fin B)
    (hinj : ∀ i v, Function.Injective (digit i v))
    (b : (α × (ι → Fin k → X)) → ℕ) (hb : ∀ z, b z ≤ k)
    (hconstraints : ∀ j, 1 ≤ j → j ≤ k →
      ∃ pivot : α → (ZMod (B ^ j))ˣ, ∃ rhs : α → ι → ZMod (B ^ j),
        ∀ z, j ≤ b z → ∀ i,
          (pivot z.1 : ZMod (B ^ j)) *
            ((∑ v : Fin k, (digit i v (z.2 i v)).val * B ^ v.val : ℕ) : ZMod (B ^ j)) =
              rhs z.1 i)
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ Fintype.card ι ≤ 1 / 2) :
    (∑ z : α × (ι → Fin k → X),
      (1 / (Fintype.card (α × (ι → Fin k → X)) : ℝ)) * (B : ℝ) ^ b z) ≤ 2 := by
  classical
  have hcard : (0 : ℝ) < Fintype.card (α × (ι → Fin k → X)) := by
    exact_mod_cast Fintype.card_pos
  apply DivisorMoment.normalized_power_moment_le_two
    (fun _ : α × (ι → Fin k → X) => 1 / (Fintype.card (α × (ι → Fin k → X)) : ℝ))
    b (B : ℝ) ((1 / (Fintype.card X : ℝ)) ^ Fintype.card ι) k
  · intro z
    positivity
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel hcard.ne'
  · positivity
  · positivity
  · exact hb
  · intro j hjpos hj
    obtain ⟨pivot, rhs, hequations⟩ := hconstraints j hjpos hj
    let bad : Finset (α × (ι → Fin k → X)) := Finset.univ.filter (fun z => j ≤ b z)
    have hprob := unit_equation_event_probability_le hB hj digit hinj pivot rhs bad
      (by intro z hz; exact hequations z (Finset.mem_filter.mp hz).2)
    have hsum :
        (∑ z : α × (ι → Fin k → X),
          if j ≤ b z then 1 / (Fintype.card (α × (ι → Fin k → X)) : ℝ) else 0) =
        (bad.card : ℝ) / Fintype.card (α × (ι → Fin k → X)) := by
      rw [← Finset.sum_filter]
      simp [bad, div_eq_mul_inv]
    rw [hsum]
    simpa only [← pow_mul, one_div_pow] using hprob
  · exact hsmall

end Problem355.ConditionalDigits

end OAI
