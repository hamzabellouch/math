import Mathlib

namespace OAI


namespace Problem355.CRT

abbrev ResidueLift (M L a : ℕ) := {x : Fin (L * M) // x.val % M = a}

def residueLiftEquiv (M L a : ℕ) (hM : 0 < M) (ha : a < M) :
    ResidueLift M L a ≃ Fin L where
  toFun x := ⟨x.val.val / M, (Nat.div_lt_iff_lt_mul hM).2 x.val.isLt⟩
  invFun j := ⟨⟨a + M * j.val, by
    have hj := j.isLt
    nlinarith⟩, by
    change (a + M * j.val) % M = a
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]⟩
  left_inv x := by
    apply Subtype.ext
    apply Fin.ext
    change a + M * (x.val.val / M) = x.val.val
    calc
      a + M * (x.val.val / M) = x.val.val % M + M * (x.val.val / M) := by
        exact congrArg (fun z => z + M * (x.val.val / M)) x.property.symm
      _ = x.val.val := Nat.mod_add_div _ _
  right_inv j := by
    apply Fin.ext
    change (a + M * j.val) / M = j.val
    rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt ha, zero_add]

theorem card_residueLift (M L a : ℕ) (hM : 0 < M) (ha : a < M) :
    Fintype.card (ResidueLift M L a) = L := by
  simpa using Fintype.card_congr (residueLiftEquiv M L a hM ha)

abbrev DoubleResidueLift (h q L a b : ℕ) :=
  {x : Fin (L * (h * q)) // x.val % h = a ∧ x.val % q = b}

def crtRepresentative (h q : ℕ) (hc : h.Coprime q) (a b : ℕ) : ℕ :=
  Nat.chineseRemainder hc a b

 theorem doubleResidue_iff (h q a b x : ℕ) (hh : 0 < h) (hq : 0 < q)
    (hc : h.Coprime q) (ha : a < h) (hb : b < q) :
    (x % h = a ∧ x % q = b) ↔
      x % (h * q) = crtRepresentative h q hc a b := by
  have hr : crtRepresentative h q hc a b < h * q :=
    Nat.chineseRemainder_lt_mul hc a b (Nat.ne_of_gt hh) (Nat.ne_of_gt hq)
  have hrep := (Nat.chineseRemainder hc a b).property
  change (x % h = a ∧ x % q = b) ↔
    x % (h * q) = (Nat.chineseRemainder hc a b).val
  change (Nat.chineseRemainder hc a b).val < h * q at hr
  rw [← Nat.mod_eq_of_lt hr]
  change (x % h = a ∧ x % q = b) ↔
    Nat.ModEq (h * q) x (Nat.chineseRemainder hc a b).val
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hc]
  constructor
  · rintro ⟨hxa, hxb⟩
    constructor
    · exact (show Nat.ModEq h x a from by simpa [Nat.ModEq, Nat.mod_eq_of_lt ha] using hxa).trans hrep.1.symm
    · exact (show Nat.ModEq q x b from by simpa [Nat.ModEq, Nat.mod_eq_of_lt hb] using hxb).trans hrep.2.symm
  · rintro ⟨hxa, hxb⟩
    constructor
    · simpa [Nat.ModEq, Nat.mod_eq_of_lt ha] using hxa.trans hrep.1
    · simpa [Nat.ModEq, Nat.mod_eq_of_lt hb] using hxb.trans hrep.2

def doubleResidueLiftEquiv (h q L a b : ℕ) (hh : 0 < h) (hq : 0 < q)
    (hc : h.Coprime q) (ha : a < h) (hb : b < q) :
    DoubleResidueLift h q L a b ≃ Fin L :=
  (Equiv.subtypeEquivRight fun (x : Fin (L * (h * q))) => doubleResidue_iff h q a b x.val hh hq hc ha hb).trans
    (residueLiftEquiv (h * q) L (crtRepresentative h q hc a b)
      (Nat.mul_pos hh hq)
      (Nat.chineseRemainder_lt_mul hc a b (Nat.ne_of_gt hh) (Nat.ne_of_gt hq)))

theorem card_doubleResidueLift (h q L a b : ℕ) (hh : 0 < h) (hq : 0 < q)
    (hc : h.Coprime q) (ha : a < h) (hb : b < q) :
    Fintype.card (DoubleResidueLift h q L a b) = L := by
  simpa using Fintype.card_congr (doubleResidueLiftEquiv h q L a b hh hq hc ha hb)

abbrev ResidueBox (h q L d : ℕ) (a b : Fin d → ℕ) :=
  {u : Fin d → Fin (L * (h * q)) //
    ∀ i, (u i).val % h = a i ∧ (u i).val % q = b i}

theorem card_residueBox (h q L d : ℕ) (hh : 0 < h) (hq : 0 < q)
    (hc : h.Coprime q) (a b : Fin d → ℕ)
    (ha : ∀ i, a i < h) (hb : ∀ i, b i < q) :
    Fintype.card (ResidueBox h q L d a b) = L ^ d := by
  calc
    Fintype.card (ResidueBox h q L d a b) =
        Fintype.card (∀ i : Fin d, DoubleResidueLift h q L (a i) (b i)) :=
      Fintype.card_congr (Equiv.subtypePiEquivPi
        (β := fun _ : Fin d => Fin (L * (h * q)))
        (p := fun i x => x.val % h = a i ∧ x.val % q = b i))
    _ = ∏ i : Fin d, Fintype.card (DoubleResidueLift h q L (a i) (b i)) :=
      Fintype.card_pi
    _ = L ^ d := by
      simp [card_doubleResidueLift h q L _ _ hh hq hc, ha, hb]

theorem card_column_lifts (h q L : ℕ) (hh : 0 < h) (hq : 0 < q)
    (hc : h.Coprime q) (a b : Fin 3 → ℕ)
    (ha : ∀ i, a i < h) (hb : ∀ i, b i < q) :
    Fintype.card (ResidueBox h q L 3 a b) = L ^ 3 :=
  card_residueBox h q L 3 hh hq hc a b ha hb

theorem translate_box_length (h q L x : ℕ) :
    (L * (h * q) + x) % h = x % h ∧
    (L * (h * q) + x) % q = x % q := by
  constructor <;> simp [Nat.add_mod, Nat.mul_mod]

def intervalEquiv (N : ℕ) (t : ℤ) : Fin N ≃ Set.Ico t (t + N) where
  toFun j := ⟨t + j.val, by constructor <;> omega⟩
  invFun x := ⟨(x.val - t).toNat, by
    have hx : t ≤ x.val ∧ x.val < t + N := x.property
    omega⟩
  left_inv j := by
    apply Fin.ext
    simp
  right_inv x := by
    apply Subtype.ext
    have hx : t ≤ x.val ∧ x.val < t + N := x.property
    change t + ↑(x.val - t).toNat = x.val
    omega

abbrev IntegerDoubleResidueLift (h q L a b : ℕ) (t : ℤ) :=
  {x : Set.Ico t (t + (L * (h * q) : ℕ)) //
    x.val % (h : ℤ) = (a : ℤ) ∧ x.val % (q : ℤ) = (b : ℤ)}

def integerDoubleResidueLiftEquiv (h q L a b : ℕ) (t : ℤ)
    (htH : t % (h : ℤ) = 0) (htQ : t % (q : ℤ) = 0) :
    DoubleResidueLift h q L a b ≃ IntegerDoubleResidueLift h q L a b t :=
  Equiv.subtypeEquiv (intervalEquiv (L * (h * q)) t) (by
    intro x
    change (x.val % h = a ∧ x.val % q = b) ↔
      ((t + (x.val : ℤ)) % (h : ℤ) = (a : ℤ) ∧
       (t + (x.val : ℤ)) % (q : ℤ) = (b : ℤ))
    simp only [Int.add_emod, htH, htQ, zero_add, Nat.mod_mod,
      ← Int.natCast_mod, Int.natCast_inj])

theorem card_integerDoubleResidueLift (h q L a b : ℕ) (hh : 0 < h) (hq : 0 < q)
    (hc : h.Coprime q) (ha : a < h) (hb : b < q) (t : ℤ)
    (htH : t % (h : ℤ) = 0) (htQ : t % (q : ℤ) = 0) :
    Fintype.card (IntegerDoubleResidueLift h q L a b t) = L := by
  rw [← Fintype.card_congr (integerDoubleResidueLiftEquiv h q L a b t htH htQ)]
  exact card_doubleResidueLift h q L a b hh hq hc ha hb

abbrev IntegerResidueBox (h q L d : ℕ) (a b : Fin d → ℕ) (t : Fin d → ℤ) :=
  ∀ i, IntegerDoubleResidueLift h q L (a i) (b i) (t i)

theorem card_integerResidueBox (h q L d : ℕ) (hh : 0 < h) (hq : 0 < q)
    (hc : h.Coprime q) (a b : Fin d → ℕ)
    (ha : ∀ i, a i < h) (hb : ∀ i, b i < q) (t : Fin d → ℤ)
    (htH : ∀ i, t i % (h : ℤ) = 0) (htQ : ∀ i, t i % (q : ℤ) = 0) :
    Fintype.card (IntegerResidueBox h q L d a b t) = L ^ d := by
  change Fintype.card (∀ i, IntegerDoubleResidueLift h q L (a i) (b i) (t i)) = _
  rw [Fintype.card_pi]
  simp [card_integerDoubleResidueLift h q L _ _ hh hq hc, ha, hb, htH, htQ]

def integerBoxColumn {h q L d : ℕ} {a b : Fin d → ℕ} {t : Fin d → ℤ}
    (u : IntegerResidueBox h q L d a b t) : Fin d → ℤ :=
  fun i => (u i).val.val

theorem integerBoxColumn_injective {h q L d : ℕ} {a b : Fin d → ℕ} {t : Fin d → ℤ} :
    Function.Injective (@integerBoxColumn h q L d a b t) := by
  intro u v huv
  funext i
  apply Subtype.ext
  apply Subtype.ext
  exact congrFun huv i

noncomputable def integerColumnLifts (h q L d : ℕ) (a b : Fin d → ℕ) (t : Fin d → ℤ) :
    Finset (Fin d → ℤ) := by
  classical
  exact Finset.univ.image (@integerBoxColumn h q L d a b t)

 theorem mem_integerColumnLifts_iff (h q L d : ℕ) (a b : Fin d → ℕ) (t v : Fin d → ℤ) :
    v ∈ integerColumnLifts h q L d a b t ↔
      ∀ i, (t i ≤ v i ∧ v i < t i + (L * (h * q) : ℕ)) ∧
        v i % (h : ℤ) = (a i : ℤ) ∧ v i % (q : ℤ) = (b i : ℤ) := by
  classical
  simp only [integerColumnLifts, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, rfl⟩ i
    exact ⟨(u i).val.property, (u i).property⟩
  · intro hv
    exact ⟨fun i => ⟨⟨v i, (hv i).1⟩, (hv i).2⟩, rfl⟩

theorem card_integerColumnLifts (h q L d : ℕ) (hh : 0 < h) (hq : 0 < q)
    (hc : h.Coprime q) (a b : Fin d → ℕ)
    (ha : ∀ i, a i < h) (hb : ∀ i, b i < q) (t : Fin d → ℤ)
    (htH : ∀ i, t i % (h : ℤ) = 0) (htQ : ∀ i, t i % (q : ℤ) = 0) :
    (integerColumnLifts h q L d a b t).card = L ^ d := by
  classical
  rw [integerColumnLifts, Finset.card_image_of_injective _ integerBoxColumn_injective,
    Finset.card_univ]
  exact card_integerResidueBox h q L d hh hq hc a b ha hb t htH htQ

end Problem355.CRT

noncomputable section

namespace Problem355.CRT

def zmodResidueLiftEquiv (m t : ℕ) [NeZero m] (r : ZMod m) :
    {x : Fin (t * m) // (x.val : ZMod m) = r} ≃ Fin t where
  toFun x := x.val.divNat
  invFun y := ⟨finProdFinEquiv (y, ⟨r.val, r.val_lt⟩), by
    change ((r.val + m * y.val : ℕ) : ZMod m) = r
    simp⟩
  left_inv x := by
    apply Subtype.ext
    apply Fin.ext
    change r.val + m * (x.val.val / m) = x.val.val
    have hr : x.val.val % m = r.val := by
      simpa using congrArg ZMod.val x.property
    rw [← hr]
    exact Nat.mod_add_div _ _
  right_inv y := by
    apply Fin.ext
    change (r.val + m * y.val) / m = y.val
    rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero (NeZero.ne m)),
      Nat.div_eq_of_lt r.val_lt, Nat.zero_add]

theorem card_residue_lifts (m t : ℕ) [NeZero m] (r : ZMod m) :
    Fintype.card {x : Fin (t * m) // (x.val : ZMod m) = r} = t := by
  rw [Fintype.card_congr (zmodResidueLiftEquiv m t r), Fintype.card_fin]

theorem crt_residue_iff (h q : ℕ) (hc : h.Coprime q)
    (a : ZMod h) (b : ZMod q) (x : ℕ) :
    ((x : ZMod h) = a ∧ (x : ZMod q) = b) ↔
      (x : ZMod (h * q)) = (ZMod.chineseRemainder hc).symm (a, b) := by
  constructor
  · intro hx
    apply (ZMod.chineseRemainder hc).injective
    simpa only [map_natCast, RingEquiv.apply_symm_apply, Prod.ext_iff, Prod.fst_natCast, Prod.snd_natCast] using hx
  · intro hx
    have hh := congrArg (ZMod.chineseRemainder hc) hx
    simpa only [map_natCast, RingEquiv.apply_symm_apply, Prod.ext_iff, Prod.fst_natCast, Prod.snd_natCast] using hh

def crtLiftEquiv (h q t : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (a : ZMod h) (b : ZMod q) :
    {x : Fin (t * (h * q)) //
      (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b} ≃ Fin t :=
  (Equiv.subtypeEquivRight fun (x : Fin (t * (h * q))) => crt_residue_iff h q hc a b x.val).trans
    (zmodResidueLiftEquiv (h * q) t ((ZMod.chineseRemainder hc).symm (a, b)))

theorem card_crt_lifts (h q t : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (a : ZMod h) (b : ZMod q) :
    Fintype.card {x : Fin (t * (h * q)) //
      (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b} = t := by
  rw [Fintype.card_congr (crtLiftEquiv h q t hc a b), Fintype.card_fin]

def crtVectorLiftEquiv (h q t d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    {x : Fin d → Fin (t * (h * q)) // ∀ i,
      ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} ≃
      (Fin d → Fin t) :=
  Equiv.subtypePiEquivPi.trans
    (Equiv.piCongrRight fun i => crtLiftEquiv h q t hc (a i) (b i))

theorem card_crt_vector_lifts (h q t d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    Fintype.card {x : Fin d → Fin (t * (h * q)) // ∀ i,
      ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} = t ^ d := by
  rw [Fintype.card_congr (crtVectorLiftEquiv h q t d hc a b)]
  simp

def intIntervalEquiv (N : ℕ) (s : ℤ) : Fin N ≃ Set.Ico s (s + N) where
  toFun x := ⟨s + x.val, by
    constructor
    · omega
    · have hx := x.is_lt
      omega⟩
  invFun x := ⟨(x.val - s).toNat, by
    rcases x.property with ⟨hx0, hx1⟩
    omega⟩
  left_inv x := by
    apply Fin.ext
    simp
  right_inv x := by
    apply Subtype.ext
    rcases x.property with ⟨hx0, hx1⟩
    dsimp
    omega

def intCRTLiftEquiv (h q t : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (s : ℤ) (a : ZMod h) (b : ZMod q) :
    {x : Set.Ico s (s + (t * (h * q) : ℕ)) //
      (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b} ≃ Fin t := by
  let e := (intIntervalEquiv (t * (h * q)) s).subtypeEquiv
    (p := fun x => (x.val : ZMod h) = a - (s : ZMod h) ∧
      (x.val : ZMod q) = b - (s : ZMod q))
    (q := fun x => (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b)
    (by
      intro x
      change ((x.val : ZMod h) = a - (s : ZMod h) ∧
        (x.val : ZMod q) = b - (s : ZMod q)) ↔
        (((s + x.val : ℤ) : ZMod h) = a ∧ ((s + x.val : ℤ) : ZMod q) = b)
      simp only [eq_sub_iff_add_eq, Int.cast_add, Int.cast_natCast]
      simp only [add_comm])
  exact e.symm.trans (crtLiftEquiv h q t hc (a - (s : ZMod h)) (b - (s : ZMod q)))

theorem card_int_crt_lifts (h q t : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (s : ℤ) (a : ZMod h) (b : ZMod q) :
    Fintype.card {x : Set.Ico s (s + (t * (h * q) : ℕ)) //
      (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b} = t := by
  rw [Fintype.card_congr (intCRTLiftEquiv h q t hc s a b), Fintype.card_fin]

def intCRTVectorLiftEquiv (h q t d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (s : Fin d → ℤ)
    (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    {x : (i : Fin d) → Set.Ico (s i) (s i + (t * (h * q) : ℕ)) // ∀ i,
      ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} ≃
      (Fin d → Fin t) :=
  Equiv.subtypePiEquivPi.trans
    (Equiv.piCongrRight fun i => intCRTLiftEquiv h q t hc (s i) (a i) (b i))

theorem card_int_crt_vector_lifts (h q t d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (s : Fin d → ℤ)
    (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    Fintype.card
      {x : (i : Fin d) → Set.Ico (s i) (s i + (t * (h * q) : ℕ)) // ∀ i,
        ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} = t ^ d := by
  rw [Fintype.card_congr (intCRTVectorLiftEquiv h q t d hc s a b)]
  simp

theorem card_int_crt_vector_lifts_of_dvd (h q N d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hN : h * q ∣ N) (s : Fin d → ℤ)
    (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    Fintype.card
      {x : (i : Fin d) → Set.Ico (s i) (s i + N) // ∀ i,
        ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} =
      (N / (h * q)) ^ d := by
  have heq : N / (h * q) * (h * q) = N := Nat.div_mul_cancel hN
  have H := card_int_crt_vector_lifts h q (N / (h * q)) d hc s a b
  rw [heq] at H
  exact H

theorem int_crt_vector_lifts_nonempty (h q t d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (ht : 0 < t) (s : Fin d → ℤ)
    (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    Nonempty
      {x : (i : Fin d) → Set.Ico (s i) (s i + (t * (h * q) : ℕ)) // ∀ i,
        ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} :=
  ⟨(intCRTVectorLiftEquiv h q t d hc s a b).symm (fun _ => ⟨0, ht⟩)⟩

end Problem355.CRT

end

end OAI
