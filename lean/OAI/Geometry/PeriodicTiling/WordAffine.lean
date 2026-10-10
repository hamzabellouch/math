import OAI.Geometry.PeriodicTiling.WordAffineAlgebra
import OAI.Geometry.PeriodicTiling.WordAffineCount
import OAI.Geometry.PeriodicTiling.WordAffineGeometry
import Mathlib.Tactic.Push

namespace OAI

noncomputable section

namespace PeriodicTilingThree

theorem allowed_affine {p : ℕ} {w : Word p} (hw : Allowed p w) :
    ∃ a b : ZMod p, (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ n : Column p, a * (n.val : ZMod p) + b ≠ 0 →
        (w n : ZMod p) = a * (n.val : ZMod p) + b := by
  obtain ⟨a, b, hab, hw⟩ := hw
  refine ⟨(a : ZMod p), (b : ZMod p), ?_, ?_⟩
  · simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hab
  · intro n hn
    have hnd : ¬ (p : ℤ) ∣ a * (n.val : ℤ) + b := by
      intro hd
      apply hn
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
        (a * (n.val : ℤ) + b) p).mpr hd
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using h
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using (hw n).1 hnd

private def intColumn {p : ℕ} (n : ℤ) (hn : 0 ≤ n ∧ n < (p ^ 2 : ℕ)) :
    Column p := ⟨n.toNat, by omega⟩

private theorem intColumn_val {p : ℕ} (n : ℤ)
    (hn : 0 ≤ n ∧ n < (p ^ 2 : ℕ)) :
    ((intColumn n hn).val : ℤ) = n := Int.toNat_of_nonneg hn.1

private theorem intColumn_cast {p : ℕ} (n : ℤ)
    (hn : 0 ≤ n ∧ n < (p ^ 2 : ℕ)) :
    ((intColumn n hn).val : ZMod p) = (n : ZMod p) := by
  simpa only [Int.cast_natCast] using
    congrArg (fun x : ℤ => (x : ZMod p)) (intColumn_val n hn)

private def rawArray {p : ℕ} (W : WordArray p) (n m : ℤ) : ZMod p :=
  if hn : 0 ≤ n ∧ n < (p ^ 2 : ℕ) then (W (intColumn n hn) m : ZMod p) else 1

private theorem rawArray_column {p : ℕ} (W : WordArray p) (n : Column p) (m : ℤ) :
    rawArray W n.val m = (W n m : ZMod p) := by
  have hn : (0 : ℤ) ≤ n.val ∧ (n.val : ℤ) < (p ^ 2 : ℕ) := by
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast n.isLt⟩
  have hc : intColumn (n.val : ℤ) hn = n := by
    apply Fin.ext
    simp [intColumn]
  rw [rawArray, dite_eq_left hn, hc]

private theorem rawArray_ne_zero {p : ℕ} [Fact p.Prime] (W : WordArray p)
    (n m : ℤ) (hn : 0 ≤ n ∧ n < (p ^ 2 : ℕ)) : rawArray W n m ≠ 0 := by
  rw [rawArray, dite_eq_left hn]
  exact Units.ne_zero _

private structure LineAffine {p : ℕ} (W : WordArray p) (d e : ℤ) where
  a : ZMod p
  b : ZMod p
  nonzero : a ≠ 0 ∨ b ≠ 0
  agrees : ∀ n : Column p, a * (n.val : ZMod p) + b ≠ 0 →
    (W n (d * (n.val : ℤ) + e) : ZMod p) = a * (n.val : ZMod p) + b

private def chooseLine {p : ℕ} {W : WordArray p} (hW : LineRule p W)
    (d e : ℤ) : LineAffine W d e := by
  let h := allowed_affine (hW d e)
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2⟩

private theorem LineAffine.raw_agrees {p : ℕ} {W : WordArray p} {d e : ℤ}
    (L : LineAffine W d e) (n : ℤ) (hn : 0 ≤ n ∧ n < (p ^ 2 : ℕ))
    (hz : L.a * (n : ZMod p) + L.b ≠ 0) :
    rawArray W n (d * n + e) = L.a * (n : ZMod p) + L.b := by
  have h := L.agrees (intColumn n hn) (by simpa only [intColumn_cast] using hz)
  rw [intColumn_val, intColumn_cast] at h
  simpa only [rawArray, dite_eq_left hn] using h

private theorem clean_second_difference {p : ℕ} {W : WordArray p}
    (hW : LineRule p W) (r q : ℤ)
    (hc : ∀ i j : Fin 4, ∀ d : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
      rawArray W (r + i.val) (q + j.val) =
        (chooseLine hW d ((q + j.val) - d * (r + i.val))).a *
          ((r + i.val : ℤ) : ZMod p) +
        (chooseLine hW d ((q + j.val) - d * (r + i.val))).b)
    (x₀ y₀ x₁ y₁ x₂ y₂ : Fin 4) (d : ℤ)
    (hd : d = -1 ∨ d = 0 ∨ d = 1)
    (h₁ : (y₁.val : ℤ) - y₀.val = d * ((x₁.val : ℤ) - x₀.val))
    (h₂ : (y₂.val : ℤ) - y₀.val = d * ((x₂.val : ℤ) - x₀.val))
    (hx : (x₂.val : ℤ) - 2 * x₁.val + x₀.val = 0) :
    rawArray W (r + x₂.val) (q + y₂.val) -
      2 * rawArray W (r + x₁.val) (q + y₁.val) +
      rawArray W (r + x₀.val) (q + y₀.val) = 0 := by
  let e := (q + y₀.val) - d * (r + x₀.val)
  have he₁ : (q + y₁.val) - d * (r + x₁.val) = e := by
    dsimp [e]
    linear_combination h₁
  have he₂ : (q + y₂.val) - d * (r + x₂.val) = e := by
    dsimp [e]
    linear_combination h₂
  have h₀' := hc x₀ y₀ d hd
  have h₁' := hc x₁ y₁ d hd
  have h₂' := hc x₂ y₂ d hd
  change rawArray W (r + x₀.val) (q + y₀.val) =
    (chooseLine hW d e).a * ((r + x₀.val : ℤ) : ZMod p) +
      (chooseLine hW d e).b at h₀'
  rw [he₁] at h₁'
  rw [he₂] at h₂'
  have hx' : (x₂.val : ZMod p) - 2 * x₁.val + x₀.val = 0 := by
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast, Int.cast_zero] using
      congrArg (fun z : ℤ => (z : ZMod p)) hx
  rw [h₀', h₁', h₂']
  push_cast
  linear_combination (chooseLine hW d e).a * hx'

private theorem affine_four_line_closure {p : ℕ} (hp : p.Prime) (hlarge : 200 < p)
    {W : WordArray p} (hW : LineRule p W) (A B C : ZMod p) :
    FourLineClosure (p ^ 2 : ℕ)
      (fun n m => A * (n : ZMod p) + B * (m : ZMod p) + C = 0 ∨
        rawArray W n m = A * (n : ZMod p) + B * (m : ZMod p) + C) := by
  let : Fact p.Prime := ⟨hp⟩
  intro d e hd r hr₀ hr₃ hgood n hn₀ hn
  let a : ZMod p := A + B * (d : ZMod p)
  let b : ZMod p := B * (e : ZMod p) + C
  let L := chooseLine hW d e
  have hrest (k : ℤ) : A * (k : ZMod p) + B * ((d * k + e : ℤ) : ZMod p) + C =
      a * (k : ZMod p) + b := by
    dsimp [a, b]
    push_cast
    ring
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · left
      rw [hrest, ha, hb]
      simp
    · have hab : a ≠ 0 ∨ b ≠ 0 := Or.inr hb
      obtain ⟨i, j, hij, hiA, hiL, hjA, hjL⟩ := two_common_nonzero_of_four
        (fun k : Fin 4 => ((r + k.val : ℤ) : ZMod p))
        (four_residues_injective (by omega) r) a b L.a L.b hab L.nonzero
      have heq (k : Fin 4) (hkA : a * ((r + k.val : ℤ) : ZMod p) + b ≠ 0)
          (hkL : L.a * ((r + k.val : ℤ) : ZMod p) + L.b ≠ 0) :
          a * ((r + k.val : ℤ) : ZMod p) + b =
            L.a * ((r + k.val : ℤ) : ZMod p) + L.b := by
        have hk := hgood k
        dsimp only at hk
        rw [hrest] at hk
        have hk' := hk.resolve_left hkA
        have hbound : 0 ≤ r + k.val ∧ r + k.val < (p ^ 2 : ℕ) := by
          have := k.isLt
          omega
        exact hk'.symm.trans (L.raw_agrees _ hbound hkL)
      have hcoef := affine_coefficients_eq_of_two
        (fun h => hij ((four_residues_injective (by omega) r) h))
        (heq i hiA hiL) (heq j hjA hjL)
      by_cases hz : a * (n : ZMod p) + b = 0
      · left
        rw [hrest]
        exact hz
      · right
        rw [hrest]
        rw [hcoef.1, hcoef.2] at hz ⊢
        exact L.raw_agrees n ⟨hn₀, hn⟩ hz
  · have hab : a ≠ 0 ∨ b ≠ 0 := Or.inl ha
    obtain ⟨i, j, hij, hiA, hiL, hjA, hjL⟩ := two_common_nonzero_of_four
      (fun k : Fin 4 => ((r + k.val : ℤ) : ZMod p))
      (four_residues_injective (by omega) r) a b L.a L.b hab L.nonzero
    have heq (k : Fin 4) (hkA : a * ((r + k.val : ℤ) : ZMod p) + b ≠ 0)
        (hkL : L.a * ((r + k.val : ℤ) : ZMod p) + L.b ≠ 0) :
        a * ((r + k.val : ℤ) : ZMod p) + b =
          L.a * ((r + k.val : ℤ) : ZMod p) + L.b := by
      have hk := hgood k
      dsimp only at hk
      rw [hrest] at hk
      have hk' := hk.resolve_left hkA
      have hbound : 0 ≤ r + k.val ∧ r + k.val < (p ^ 2 : ℕ) := by
        have := k.isLt
        omega
      exact hk'.symm.trans (L.raw_agrees _ hbound hkL)
    have hcoef := affine_coefficients_eq_of_two
      (fun h => hij ((four_residues_injective (by omega) r) h))
      (heq i hiA hiL) (heq j hjA hjL)
    by_cases hz : a * (n : ZMod p) + b = 0
    · left
      rw [hrest]
      exact hz
    · right
      rw [hrest]
      rw [hcoef.1, hcoef.2] at hz ⊢
      exact L.raw_agrees n ⟨hn₀, hn⟩ hz

theorem global_affine_approximation {p : ℕ} (hp : p.Prime) (hlarge : 200 < p)
    {W : WordArray p} (hW : LineRule p W) :
    ∃ A B C : ZMod p, AffineApproximation W A B C := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let bad : ℤ → ℤ → ℤ → Prop := fun d e n =>
    (chooseLine hW d e).a * (n : ZMod p) + (chooseLine hW d e).b = 0
  have hbad : ∀ d e, d = -1 ∨ d = 0 ∨ d = 1 →
      ((Finset.Ico (0 : ℤ) (p ^ 2 : ℕ)).filter (bad d e)).card ≤ p := by
    intro d e _
    exact affine_int_roots_card_le hp _ _ (chooseLine hW d e).nonzero
  obtain ⟨r, q, hr₀, hr₃, _, _, hclean⟩ :=
    exists_clean_four_square p hlarge bad
      (by
        intro d e hd
        have hfilter := @Finset.filter_congr_decidable ℤ
          (Finset.Ico (0 : ℤ) (p ^ 2 : ℕ)) (bad d e)
          (fun n => Classical.propDecidable (bad d e n))
          (fun n => ZMod.decidableEq p
            ((chooseLine hW d e).a * (n : ZMod p) + (chooseLine hW d e).b) 0)
        exact (congrArg (fun s : Finset ℤ => s.card ≤ p) hfilter).mpr (hbad d e hd))
  have hcell : ∀ i j : Fin 4, ∀ d : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
      rawArray W (r + i.val) (q + j.val) =
        (chooseLine hW d ((q + j.val) - d * (r + i.val))).a *
          ((r + i.val : ℤ) : ZMod p) +
        (chooseLine hW d ((q + j.val) - d * (r + i.val))).b := by
    intro i j d hd
    have hn : 0 ≤ r + i.val ∧ r + i.val < (p ^ 2 : ℕ) := by
      have := i.isLt
      omega
    have h := (chooseLine hW d ((q + j.val) - d * (r + i.val))).raw_agrees
      (r + i.val) hn (hclean i j d hd)
    have he : d * (r + i.val) + ((q + j.val) - d * (r + i.val)) = q + j.val := by ring
    simpa only [he] using h
  let U : Fin 4 → ZMod p := fun j => (chooseLine hW 0 (q + j.val)).a
  let V : Fin 4 → ZMod p := fun j => U j * (r : ZMod p) +
    (chooseLine hW 0 (q + j.val)).b
  have hrow (i j : Fin 4) : rawArray W (r + i.val) (q + j.val) =
      U j * (i.val : ZMod p) + V j := by
    have h := hcell i j 0 (Or.inr (Or.inl rfl))
    have he : (q + j.val) - (0 : ℤ) * (r + i.val) = q + j.val := by ring
    rw [he] at h
    rw [h]
    dsimp [V, U]
    push_cast
    ring
  have hv0 : (0 : Fin 4).val = 0 := rfl
  have hv1 : (1 : Fin 4).val = 1 := rfl
  have hv2 : (2 : Fin 4).val = 2 := rfl
  have hv3 : (3 : Fin 4).val = 3 := rfl
  have hp₀ := clean_second_difference hW r q hcell 0 0 1 1 2 2 1
    (Or.inr (Or.inr rfl))
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
  have hp₀' := clean_second_difference hW r q hcell 1 0 2 1 3 2 1
    (Or.inr (Or.inr rfl))
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
  have hm₀ := clean_second_difference hW r q hcell 2 0 1 1 0 2 (-1)
    (Or.inl rfl)
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
  have hp₁ := clean_second_difference hW r q hcell 0 1 1 2 2 3 1
    (Or.inr (Or.inr rfl))
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
  have hp₁' := clean_second_difference hW r q hcell 1 1 2 2 3 3 1
    (Or.inr (Or.inr rfl))
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
  have hm₁ := clean_second_difference hW r q hcell 2 1 1 2 0 3 (-1)
    (Or.inl rfl)
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    have hlt : 2 < p := by omega
    have hv₂ : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt hlt
    rw [hv₂, ZMod.val_zero] at hv
    omega
  have hpatch := four_rows_affine htwo U V
    (by
      have h := hp₀
      simp only [hrow] at h
      simp only [hv0, hv1, hv2, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h
      linear_combination h)
    (by
      have h := hp₀'
      simp only [hrow] at h
      simp only [hv1, hv2, hv3, Nat.cast_one, Nat.cast_ofNat] at h
      linear_combination h)
    (by
      have h := hm₀
      simp only [hrow] at h
      simp only [hv0, hv1, hv2, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h
      linear_combination h)
    (by
      have h := hp₁
      simp only [hrow] at h
      simp only [hv0, hv1, hv2, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h
      linear_combination h)
    (by
      have h := hp₁'
      simp only [hrow] at h
      simp only [hv1, hv2, hv3, Nat.cast_one, Nat.cast_ofNat] at h
      linear_combination h)
    (by
      have h := hm₁
      simp only [hrow] at h
      simp only [hv0, hv1, hv2, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h
      linear_combination h)
  let A := U 0
  let B := V 1 - V 0
  let C := V 0 - A * (r : ZMod p) - B * (q : ZMod p)
  have hsquare (i j : Fin 4) : rawArray W (r + i.val) (q + j.val) =
      A * ((r + i.val : ℤ) : ZMod p) +
        B * ((q + j.val : ℤ) : ZMod p) + C := by
    rw [hrow, hpatch]
    dsimp [A, B, C]
    push_cast
    ring
  have hnonzero : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0 := by
    by_cases hA : A = 0
    · by_cases hB : B = 0
      · refine Or.inr (Or.inr ?_)
        intro hC
        have hz := hsquare 0 0
        simp only [Fin.val_zero, Nat.cast_zero, add_zero, hA, hB, hC,
          zero_mul] at hz
        exact rawArray_ne_zero W r q ⟨hr₀, by omega⟩ hz
      · exact Or.inr (Or.inl hB)
    · exact Or.inl hA
  have hN : (8 : ℤ) ≤ (p ^ 2 : ℕ) := by
    have hp' : 201 ≤ p := by omega
    have hsq : 201 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp' 2
    exact_mod_cast (show 8 ≤ p ^ 2 by omega)
  have hglobal := good_everywhere_of_four_square (p ^ 2 : ℕ) hN
    (fun n m => A * (n : ZMod p) + B * (m : ZMod p) + C = 0 ∨
      rawArray W n m = A * (n : ZMod p) + B * (m : ZMod p) + C)
    (affine_four_line_closure hp hlarge hW A B C) r q hr₀ hr₃
    (fun i j => Or.inr (hsquare i j))
  refine ⟨A, B, C, hnonzero, ?_⟩
  intro n m hn
  have h := hglobal (n.val : ℤ) m (Int.natCast_nonneg _)
    (by exact_mod_cast n.isLt)
  rw [rawArray_column] at h
  simpa only [affineValue, Int.cast_natCast] using
    (h.resolve_left (by simpa only [affineValue, Int.cast_natCast] using hn))

end PeriodicTilingThree

end

end OAI
