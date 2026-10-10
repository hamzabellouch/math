import OAI.NumberTheory.Ostmann.Construction.TransferTupleCoordinates
import OAI.NumberTheory.Ostmann.Characters.NormalizedResidueIndicator
import OAI.NumberTheory.Ostmann.Characters.PivotKeyReduction

namespace OAI

/-! # The surviving regular Fourier transform in the giant-only transfer -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

private theorem transfer_quotient {K : Type*} [Field K]
    (P R D v s : K) (hP : P ≠ 0) (hR : R ≠ 0) (hD : D ≠ 0)
    (h : v * R = s * P) : v / (P * D) = s / (R * D) := by
  apply (div_eq_div_iff (mul_ne_zero hP hD) (mul_ne_zero hR hD)).mpr
  calc
    v * (R * D) = (v * R) * D := by ring
    _ = (s * P) * D := by rw [h]
    _ = s * (P * D) := by ring

/-- The local left transform keeps its function; only the denominator changes. -/
theorem moving_regular_left_transfer {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (L R M D : ℕ) (v w s : ℤ)
    (hpL : p ∣ L) (hM : M.Coprime p) (hR : R.Coprime p) (hD : D.Coprime p)
    (hrel : v * R - w * L = s * M) :
    g ((v : ZMod p) / ((M * D : ℕ) : ZMod p)) =
      g ((s : ZMod p) / ((R * D : ℕ) : ZMod p)) := by
  congr 1
  simp only [Nat.cast_mul]
  exact transfer_quotient _ _ _ _ _
    (zmod_natCast_ne_zero_of_coprime M hM)
    (zmod_natCast_ne_zero_of_coprime R hR)
    (zmod_natCast_ne_zero_of_coprime D hD)
    (transfer_equation_mod_left p L R M v w s hpL hrel)

/-- The conjugated right transform has the same new argument, because the
underlying physical residue function is real. -/
theorem moving_regular_right_transfer {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : ∀ x, g (-x) = conj (g x))
    (L R M D : ℕ) (v w s : ℤ)
    (hpR : p ∣ R) (hM : M.Coprime p) (hL : L.Coprime p) (hD : D.Coprime p)
    (hrel : v * R - w * L = s * M) :
    conj (g ((w : ZMod p) / ((M * D : ℕ) : ZMod p))) =
      g ((s : ZMod p) / ((L * D : ℕ) : ZMod p)) := by
  rw [← hg]
  congr 1
  simp only [Nat.cast_mul, ← neg_div]
  exact transfer_quotient _ _ _ _ _
    (zmod_natCast_ne_zero_of_coprime M hM)
    (zmod_natCast_ne_zero_of_coprime L hL)
    (zmod_natCast_ne_zero_of_coprime D hD)
    (transfer_equation_mod_right p L R M v w s hpR hrel)

/-- Product of the actual local transforms, with their CRT cofactors. -/
noncomputable def movingRegularTransform {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)]
    (g : ∀ i, ZMod (p i) → ℂ) (D : ℕ) (s : ℤ) : ℂ :=
  ∏ i, g i ((s : ZMod (p i)) * ((D * tupleCofactor p i : ℕ) : ZMod (p i))⁻¹)

local instance sumElim_neZero {H K : Type*} (L : H → ℕ) (R : K → ℕ)
    [∀ i, NeZero (L i)] [∀ i, NeZero (R i)] (i : H ⊕ K) :
    NeZero (Sum.elim L R i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

/-- Splitting the actual prime list extracts exactly the pivot row and
retains the old regular transform at the composite pivot denominator. -/
theorem moving_regular_transform_split {H K : Type*} [Fintype H] [Fintype K]
    (L : H → ℕ) (R : K → ℕ) [∀ i, NeZero (L i)] [∀ i, NeZero (R i)]
    (gL : ∀ i, ZMod (L i) → ℂ) (gR : ∀ i, ZMod (R i) → ℂ)
    (D : ℕ) (s : ℤ) :
    movingRegularTransform (Sum.elim L R)
      (fun i => match i with | .inl j => gL j | .inr j => gR j) D s =
    movingRegularTransform L gL (D * ∏ i, R i) s *
      movingRegularTransform R gR (D * ∏ i, L i) s := by
  unfold movingRegularTransform
  rw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [tupleCofactor_sum_left L R i (NeZero.ne (L i))]
    simp only [mul_assoc, mul_comm]
    rfl
  · apply Finset.prod_congr rfl
    intro i _
    rw [tupleCofactor_sum_right L R i (NeZero.ne (R i))]
    simp only [mul_assoc]
    rfl

/-- The extracted row depends only on the grouped key `v/H mod P`, with
the original outside denominator and every local cofactor unchanged. -/
theorem moving_regular_transform_grouped_key {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (g : ∀ j, ZMod (p j) → ℂ) (H D : ℕ) (v : ℤ)
    (hH : H.Coprime (∏ j, p j)) :
    movingRegularTransform p g D
      ((positiveIntegerPivotKey (∏ j, p j)
        (Finset.prod_pos (fun j _ => (Fact.out : (p j).Prime).pos)) H v).val : ℤ) =
      movingRegularTransform p g (D * H) v := by
  unfold movingRegularTransform
  apply Finset.prod_congr rfl
  intro j _
  have hd := Finset.dvd_prod_of_mem p (Finset.mem_univ j)
  have hHj := zmod_natCast_ne_zero_of_coprime H (hH.of_dvd_right hd)
  have he := positiveIntegerPivotKey_mul_at_divisor (∏ j, p j)
    (Finset.prod_pos (fun j _ => (Fact.out : (p j).Prime).pos)) H v hd hH
  have heq := (eq_div_iff hHj).mpr he
  simp only [Int.cast_natCast, heq, div_eq_mul_inv, Nat.cast_mul, mul_inv_rev]
  congr 1
  ring

/-- The full current transform factors through the precise grouped row
used by the Cauchy step, before the giant is extended to integers. -/
theorem moving_full_transform_grouped {J K : Type*} [Fintype J] [Fintype K]
    (p : J → ℕ) (q : K → ℕ)
    [∀ j, Fact (p j).Prime] [∀ k, Fact (q k).Prime]
    (g : ∀ j, ZMod (p j) → ℂ) (h : ∀ k, ZMod (q k) → ℂ)
    (D : ℕ) (v : ℤ) (hqp : (∏ k, q k).Coprime (∏ j, p j)) :
    movingRegularTransform (Sum.elim p q)
      (fun i => match i with | .inl j => g j | .inr k => h k) D v =
    movingRegularTransform p g D
      ((positiveIntegerPivotKey (∏ j, p j)
        (Finset.prod_pos (fun j _ => (Fact.out : (p j).Prime).pos)) (∏ k, q k) v).val : ℤ) *
      movingRegularTransform q h (D * ∏ j, p j) v := by
  rw [moving_regular_transform_grouped_key p g (∏ k, q k) D v hqp]
  exact moving_regular_transform_split p q g h D v

/-- No averaging or approximation occurs when the two surviving transforms
combine. The extracted pivot and compensation product disappear together. -/
theorem moving_regular_transform_transfer {H K : Type*} [Fintype H] [Fintype K]
    (L : H → ℕ) (R : K → ℕ)
    [∀ i, Fact (L i).Prime] [∀ i, Fact (R i).Prime]
    (gL : ∀ i, ZMod (L i) → ℂ) (gR : ∀ i, ZMod (R i) → ℂ)
    (hgR : ∀ i x, gR i (-x) = conj (gR i x))
    (M D : ℕ) (v w s : ℤ)
    (hc : Pairwise (fun i j => (Sum.elim L R i).Coprime (Sum.elim L R j)))
    (hM : ∀ i, M.Coprime (Sum.elim L R i))
    (hD : ∀ i, D.Coprime (Sum.elim L R i))
    (hrel : v * (∏ i, R i) - w * (∏ i, L i) = s * M) :
    movingRegularTransform L gL (M * D) v *
      conj (movingRegularTransform R gR (M * D) w) =
    movingRegularTransform (Sum.elim L R)
      (fun i => match i with | .inl j => gL j | .inr j => gR j) D s := by
  have hLc : Pairwise (fun i j => (L i).Coprime (L j)) := by
    intro i j hij
    exact hc (by simpa using hij : Sum.inl i ≠ Sum.inl j)
  have hRc : Pairwise (fun i j => (R i).Coprime (R j)) := by
    intro i j hij
    exact hc (by simpa using hij : Sum.inr i ≠ Sum.inr j)
  have hleft (i : H) :
      gL i ((v : ZMod (L i)) / ((M * D * tupleCofactor L i : ℕ) : ZMod (L i))) =
      gL i ((s : ZMod (L i)) /
        ((D * tupleCofactor (Sum.elim L R) (.inl i) : ℕ) : ZMod (L i))) := by
    have hRi : (∏ j, R j).Coprime (L i) := Nat.coprime_prod_left_iff.mpr (by
      intro j _
      exact hc (by simp : Sum.inr j ≠ Sum.inl i))
    have hh := moving_regular_left_transfer (gL i) (∏ j, L j) (∏ j, R j) M
      (D * tupleCofactor L i) v w s (Finset.dvd_prod_of_mem L (Finset.mem_univ i))
      (hM (.inl i)) hRi ((hD (.inl i)).mul_left (tupleCofactor_coprime L hLc i)) hrel
    simpa only [tupleCofactor_sum_left L R i (Fact.out : (L i).Prime).ne_zero,
      mul_assoc, mul_left_comm, mul_comm] using hh
  have hright (i : K) :
      conj (gR i ((w : ZMod (R i)) / ((M * D * tupleCofactor R i : ℕ) : ZMod (R i)))) =
      gR i ((s : ZMod (R i)) /
        ((D * tupleCofactor (Sum.elim L R) (.inr i) : ℕ) : ZMod (R i))) := by
    have hLi : (∏ j, L j).Coprime (R i) := Nat.coprime_prod_left_iff.mpr (by
      intro j _
      exact hc (by simp : Sum.inl j ≠ Sum.inr i))
    have hh := moving_regular_right_transfer (gR i) (hgR i) (∏ j, L j) (∏ j, R j) M
      (D * tupleCofactor R i) v w s (Finset.dvd_prod_of_mem R (Finset.mem_univ i))
      (hM (.inr i)) hLi ((hD (.inr i)).mul_left (tupleCofactor_coprime R hRc i)) hrel
    simpa only [tupleCofactor_sum_right L R i (Fact.out : (R i).Prime).ne_zero,
      mul_assoc, mul_left_comm, mul_comm] using hh
  unfold movingRegularTransform
  rw [map_prod, Fintype.prod_sum_type]
  simp only [div_eq_mul_inv] at hleft hright
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl (fun i _ => hleft i))
    (Finset.prod_congr rfl (fun i _ => hright i))

end Ostmann

end OAI
