import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawOutputBounds

namespace OAI

/-! A natural polynomial envelope for the actual rational raw compiler.
Only the raw term count, coefficient magnitude and unary precision enter it. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange

def budgetNat (m B : ℕ) : ℕ := 1+2000000*(m+m*B)+(7056*(m+m*B))^2
def scaleNat (m B N : ℕ) : ℕ := 9*(budgetNat m B)^3*N
def outputNat (n m B N : ℕ) : ℕ :=
  let R := scaleNat m B N
  (6*n+1)*R^2+3920*R*(1+B)+(685600*m+26000)*B+1

theorem mass_nonneg (xs : List Raw) : 0 ≤ mass xs := by
  exact List.sum_nonneg (by intro q hq; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hq; exact abs_nonneg _)

theorem mass_bound (xs : List Raw) {B : ℝ} (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B) :
    (mass xs:ℝ) ≤ xs.length*B := by
  induction xs with
  | nil => simp [mass]
  | cons t xs ih =>
    have ht := hw t (by simp)
    have hs := ih (by intro u hu; exact hw u (by simp [hu]))
    simp only [mass,List.map_cons,List.sum_cons,Rat.cast_add,Rat.cast_abs,
      List.length_cons,Nat.cast_add,Nat.cast_one]
    change |(t.2.2.2:ℝ)|+(mass xs:ℝ) ≤ _
    nlinarith

theorem scale_nat_bound (N : ℕ) (xs : List Raw) (B : ℕ)
    (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B) :
    |(scale N xs:ℝ)| ≤ scaleNat xs.length B N := by
  have hm := mass_bound xs hw
  have hm0 : (0:ℝ) ≤ mass xs := by exact_mod_cast mass_nonneg xs
  have hb0 : (0:ℝ) ≤ budget xs := by
    simp only [budget,size,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat]
    positivity
  have hb : (budget xs:ℝ) ≤ budgetNat xs.length B := by
    simp only [budget,size,budgetNat,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,
      Rat.cast_ofNat,Rat.cast_one,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    gcongr
  simp only [scale,scaleNat,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [abs_of_nonneg (by positivity)]
  gcongr

theorem outputNat_cast (n m B N : ℕ) :
    (outputNat n m B N:ℝ)=outputBound n m (scaleNat m B N) B := by
  simp only [outputNat,outputBound,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_ofNat,Nat.cast_one]

theorem compile_bond_bound (n N B : ℕ) (xs : List Raw)
    (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B)
    (e : MediatorListProgram.Bond) (he : e ∈ (compile (n,N,xs)).1) :
    |(e.2.2:ℝ)| ≤ outputNat n xs.length B N := by
  rw [outputNat_cast]
  exact fullBonds_abs n (bits (n,N,xs)) (scale N xs) xs
    (scale_nat_bound N xs B hw) (Nat.cast_nonneg B) hw e he

theorem compile_scalar_bound (n N B : ℕ) (xs : List Raw)
    (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B) :
    |((compile (n,N,xs)).2:ℝ)| ≤ outputNat n xs.length B N := by
  rw [outputNat_cast]
  exact fullScalar_abs n (bits (n,N,xs)) (scale N xs) xs
    (scale_nat_bound N xs B hw) (Nat.cast_nonneg B) hw

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
