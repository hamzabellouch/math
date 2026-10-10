import OAI.MathematicalPhysics.AlternatingFlow.ConstructiveBounds

namespace OAI

section InitialNamesDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

def ratCode (b : ℕ) (ds : List ℕ) : ℚ :=
  ds.foldr (fun (d : ℕ) (q : ℚ) => ((d : ℚ) + q) / b) 0

lemma ratCode_cast (b : ℕ) (ds : List ℕ) :
    (ratCode b ds : ℝ) = Encoding.code b ds := by
  induction ds with
  | nil => simp [ratCode, Encoding.code]
  | cons d ds ih => simp only [ratCode, List.foldr_cons, Rat.cast_div, Rat.cast_add,
      Rat.cast_natCast, Encoding.code] at *; rw [ih]

lemma ratCode_primrec : Primrec₂ ratCode :=
  Primrec.list_foldr Primrec.snd (Primrec.const 0)
    ((Arithmetic.rat_div.comp (Arithmetic.rat_add.comp
      (Arithmetic.rat_natCast.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
      (Arithmetic.rat_natCast.comp (Primrec.fst.comp Primrec.fst)))).to₂

lemma digits_eq_map (K : ℕ) (f : ℕ → ℕ) :
    Encoding.digits K f = (List.range K).map f := by
  induction K generalizing f with
  | zero => simp [Encoding.digits]
  | succ K ih => rw [Encoding.digits_succ, ih, List.range_succ_eq_map]; simp only [List.map_cons,
      List.map_map, Function.comp_def, Nat.succ_eq_add_one]

lemma initial_digits_primrec : Primrec (fun z : Machine × List ℕ => z.1.recordedDigits z.2 0) := by
  have hK : Primrec (fun z : Machine × List ℕ => Scales.K z.2.length 0) :=
    capacity.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 0)
  have hL : Primrec (fun z : Machine × List ℕ => (List.range (Scales.K z.2.length 0)).map (fun _ : ℕ => 0)) := Primrec.list_map (Primrec.list_range.comp hK) (Primrec.const (0 : ℕ)).to₂
  have hR : Primrec (fun z : Machine × List ℕ => (List.range (Scales.K z.2.length 0)).map (fun j : ℕ => 2 * z.2[j]?.getD 0)) := Primrec.list_map (Primrec.list_range.comp hK)
    ((Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst)
        Primrec.snd) (Primrec.const 0)))).to₂
  refine (Primrec.list_cons.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (initialState.comp Primrec.fst))
    (Primrec.list_append.comp hL hR)).of_eq ?_
  intro z
  simp only [Machine.recordedDigits, Machine.run, Function.iterate_zero, id_eq, Machine.initial,
    digits_eq_map]
  congr 1
  apply congrArg₂ List.append
  · apply List.map_congr_left; intro j hj
    have h : ¬ (0 : ℤ) ≤ 0 - ((j : ℤ) + 1) := by omega
    simp [Machine.leftDigits]; omega
  · apply List.map_congr_left; intro j hj
    simp [Machine.rightDigits]

def initialBlock (M : Machine) (w : List ℕ) : ℚ := ratCode M.base (M.recordedDigits w 0)

lemma initialBlock_primrec : Primrec₂ initialBlock :=
  ratCode_primrec.comp (base.comp Primrec.fst) initial_digits_primrec

lemma initialBlock_cast (M : Machine) (w : List ℕ) :
    (initialBlock M w : ℝ) = M.recordedBlock w 0 := ratCode_cast _ _

lemma epsilon_named : Named (fun z : (Machine × ℕ) × ℕ => Scales.ε z.1.1.base z.1.2 z.2) := by
  have h := Named.rational (Arithmetic.rat_inv.to_comp.comp
    (Arithmetic.rat_pow.to_comp.comp
      (Arithmetic.rat_natCast.to_comp.comp (base.to_comp.comp (Computable.fst.comp Computable.fst)))
      (exponent.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)))
  exact h.congr (by intros; simp only [Scales.ε, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast])

lemma loadingPotential_scaled : Scaled (fun _ : Machine × List ℕ => fun _ => 1)
    (fun z _ (x : Space) => Spatial.cutoff x *
      Spatial.shearPotential 2 1 0 (fun _ => Scales.ε z.1.base z.2.length 0 * z.1.recordedBlock z.2 0)
        (fun _ => 1 - Scales.ε z.1.base z.2.length 0) x) := by
  let B := fun z : Machine × List ℕ => (initialBlock z.1 z.2).num.natAbs
  have hB : Computable B := Arithmetic.int_abs.to_comp.comp
    (Arithmetic.rat_num.to_comp.comp initialBlock_primrec.to_comp)
  have he (z : Machine × List ℕ) : 0 ≤ Scales.ε z.1.base z.2.length 0 ∧
      Scales.ε z.1.base z.2.length 0 ≤ 1 := by
    refine ⟨Scales.ε_nonneg _ _ _ (by have := z.1.base_ge_four; omega), ?_⟩
    simpa [Scales.ε] using (Bounds.inverse_power_bound z.1 (Scales.s z.2.length 0))
  have h₁ := (cutoff_coordinate_scaled (fun _ : Machine × List ℕ => fun _ => (0 : Fin 3))).smul
    (fun _ _ => zero_le_one)
    (fun z _ => Scales.ε z.1.base z.2.length 0 * z.1.recordedBlock z.2 0) B hB (by
      intro z n
      rw [abs_mul, abs_of_nonneg (he z).1, ← initialBlock_cast]
      exact (mul_le_mul_of_nonneg_right (he z).2 (abs_nonneg _)).trans (by
        simpa [B] using abs_rat_cast_le_num (initialBlock z.1 z.2)))
  have h₂ := (cutoff_coordinate_scaled (fun _ : Machine × List ℕ => fun _ => (1 : Fin 3))).smul
    (fun _ _ => zero_le_one) (fun z _ => 1 - Scales.ε z.1.base z.2.length 0)
    (fun _ => 1) (Computable.const 1) (by
      intro z n
      rw [abs_of_nonneg (sub_nonneg.mpr (he z).2)]
      simpa using sub_le_self (1 : ℝ) (he z).1)
  exact (h₁.sub h₂).congr (by intros; dsimp [Spatial.shearPotential]; ring)
end AlternatingNS.Effective

end InitialNamesDevelopment

end OAI
