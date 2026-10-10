import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScaleSup

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic
abbrev PrimeIdeal := SmoothMobiusCorrection.PrimeIdeal

def primeRowMap (p : FreeRow×PrimeIdeal) : NonzeroElement :=
  amplifiedElement ⟨p.1.val,p.1.property.1⟩ ⟨p.2.val,p.2.property.ne_zero⟩

theorem primeRowMap_injective : Function.Injective primeRowMap := by
  intro p q hpq
  have he : rowMap (p.1,⟨p.2.val,p.2.property.ne_zero⟩)=
      rowMap (q.1,⟨q.2.val,q.2.property.ne_zero⟩) := congrArg Subtype.val hpq
  have hh := rowMap_injective he
  apply Prod.ext
  · exact congrArg (fun r : FreeRow×NonzeroIdeal => r.1) hh
  · apply Subtype.ext
    exact congrArg (fun r : FreeRow×NonzeroIdeal => r.2.val) hh

theorem primeRowMap_norm_bound (p : FreeRow×PrimeIdeal) (U V : ℝ)
    (hU : (Ideal.span {p.1.val}).absNorm≤U) (hV : (p.2.val.absNorm : ℝ)≤V) :
    ((Ideal.span {((primeRowMap p).val)}).absNorm : ℝ)≤U*V^6 := by
  have hn := rowMap_norm (p.1,⟨p.2.val,p.2.property.ne_zero⟩)
  change ((Ideal.span {rowMap (p.1,⟨p.2.val,p.2.property.ne_zero⟩)}).absNorm : ℝ)≤_
  rw [hn,Nat.cast_mul,Nat.cast_pow]
  exact mul_le_mul hU (pow_le_pow_left₀ (Nat.cast_nonneg _) hV 6)
    (by positivity) ((Nat.cast_nonneg _).trans hU)

theorem averaged_energy (data : RowData) (rows : Finset FreeRow) (primes : Finset PrimeIdeal)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D U V E : ℝ) (hD : 0<D) (hV : 1≤V)
    (hrows : ∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U)
    (hprimes : ∀ P∈primes, (P.val.absNorm : ℝ)≤V)
    (hraw0 : ∀ R : Finset NonzeroElement,
      (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
      ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true W (Real.exp l) 0 0‖^2≤E)
    (hraw1 : ∀ R : Finset NonzeroElement,
      (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
      ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true (scaleProfile W) (Real.exp l) 0 0‖^2≤E) :
    (primes.card : ℝ)*∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤
      4*(1+2*Real.log V)*E := by
  let R := (rows×ˢprimes).image primeRowMap
  have hR : ∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6 := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hu,hP⟩ := Finset.mem_product.mp hp
    exact primeRowMap_norm_bound p U V (hrows p.1 hu) (hprimes p.2 hP)
  have hl : Real.log D-Real.log V≤Real.log D := by linarith [Real.log_nonneg hV]
  obtain ⟨B,hB,hmajor,henergy⟩ := exists_scale_majorant R data.character W a b hb hWs hW
    (Real.log D-Real.log V) (Real.log D) E hl (hraw0 R hR) (hraw1 R hR)
  have hamp (u : FreeRow) (hu : u∈rows) (P : PrimeIdeal) (hP : P∈primes) :
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤4*B (primeRowMap (u,P)) := by
    have hN : (1 : ℝ)≤P.val.absNorm := by
      exact_mod_cast (show 1≤P.val.absNorm from (SmoothMobiusCorrection.prime_norm_two_le P).trans' (by norm_num))
    have hNp : (0 : ℝ)<P.val.absNorm := by linarith
    have hlog : Real.log (P.val.absNorm : ℝ)≤Real.log V :=
      Real.log_le_log hNp (hprimes P hP)
    have hDV : Real.log (D/(P.val.absNorm : ℝ))∈Icc (Real.log D-Real.log V) (Real.log D) := by
      rw [Real.log_div hD.ne' hNp.ne']
      constructor <;> linarith [Real.log_nonneg hN]
    have hbase := hmajor (primeRowMap (u,P)) (Real.log D) ⟨hl,le_refl _⟩
    have hlow := hmajor (primeRowMap (u,P)) (Real.log (D/(P.val.absNorm : ℝ))) hDV
    rw [Real.exp_log hD] at hbase
    rw [Real.exp_log (div_pos hD hNp)] at hlow
    have hh := data.prime_energy ⟨u.val,u.property.1⟩ P W a b ha hWs hW D 0 0 hD
    change ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤
      2*(‖polynomial (data.character (primeRowMap (u,P))) true W D 0 0‖^2+
        ‖polynomial (data.character (primeRowMap (u,P))) true W (D/(P.val.absNorm : ℝ)) 0 0‖^2) at hh
    linarith
  have hs : (primes.card : ℝ)*∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤4*∑ v∈R, B v := by
    calc
      _ = ∑ p∈rows×ˢprimes,
          ‖polynomial (data.character ⟨p.1.val,p.1.property.1⟩) true W D 0 0‖^2 := by
        rw [Finset.sum_product]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        change (primes.card : ℝ) *
          ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2 =
          ∑ _P∈primes, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p∈rows×ˢprimes, 4*B (primeRowMap p) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hu,hP⟩ := Finset.mem_product.mp hp
        exact hamp p.1 hu p.2 hP
      _ = _ := by
        dsimp [R]
        rw [Finset.mul_sum,Finset.sum_image]
        exact fun p hp q hq h => primeRowMap_injective h
  have hh := mul_le_mul_of_nonneg_left henergy (by norm_num : (0 : ℝ)≤4)
  nlinarith

end SevenEighths.HeckeInverseAmplification

end

end OAI
