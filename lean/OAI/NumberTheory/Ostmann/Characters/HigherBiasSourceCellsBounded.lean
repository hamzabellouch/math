import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCells
import OAI.NumberTheory.Ostmann.Characters.ShellPrior

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open scoped BigOperators
open Construction Preliminaries

def boundedRawLogCell {Q : ℕ} (E : Finset (PrimeUpTo Q)) (h : ℤ) : Finset (PrimeUpTo Q) :=
  E.filter (fun p => (h:ℝ) ≤ Real.log p.val ∧ Real.log p.val < (h:ℝ)+1)

def naturalPrimeSet {Q : ℕ} (E : Finset (PrimeUpTo Q)) : Finset ℕ := E.image Subtype.val

def extendPrimeTest {Q : ℕ} (f : PrimeUpTo Q → ℂ) (p : ℕ) : ℂ :=
  if hp : p∈Q.primesLE then f ⟨p,hp⟩ else 0

@[simp] theorem extendPrimeTest_val {Q : ℕ} (f : PrimeUpTo Q → ℂ) (p : PrimeUpTo Q) :
    extendPrimeTest f p.val=f p := by simp only [extendPrimeTest,p.property,dite_eq_left]

theorem sum_naturalPrimeSet {Q : ℕ} {A : Type*} [AddCommMonoid A]
    (E : Finset (PrimeUpTo Q)) (g : ℕ → A) :
    (∑ p∈naturalPrimeSet E,g p)=∑ p∈E,g p.val := by
  rw [naturalPrimeSet,Finset.sum_image]
  intro p hp q hq he
  exact Subtype.ext he

theorem naturalPrimeSet_mass {Q : ℕ} (E : Finset (PrimeUpTo Q)) :
    harmonicPrimeMass (naturalPrimeSet E)=primeShellMass E := by
  unfold harmonicPrimeMass primeShellMass
  rw [sum_naturalPrimeSet]
  simp only [one_div]

theorem naturalPrimeSet_cell {Q : ℕ} (E : Finset (PrimeUpTo Q)) (h : ℤ) :
    rawLogCell (naturalPrimeSet E) h=naturalPrimeSet (boundedRawLogCell E h) := by
  ext p
  simp only [rawLogCell,boundedRawLogCell,naturalPrimeSet,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨q,hq,rfl⟩,hh⟩
    exact ⟨q,⟨hq,hh⟩,rfl⟩
  · rintro ⟨q,⟨hq,hh⟩,rfl⟩
    exact ⟨⟨q,hq,rfl⟩,hh⟩

theorem rawCellMeanReal_bounded {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (f : PrimeUpTo Q → ℂ) (h : ℤ) :
    rawCellMeanReal (naturalPrimeSet E) (extendPrimeTest f) h =
      (∑ p∈boundedRawLogCell E h,(p.val:ℝ)⁻¹*(f p).re)/
        primeShellMass (boundedRawLogCell E h) := by
  unfold rawCellMeanReal rawCellRealSum
  rw [naturalPrimeSet_cell,naturalPrimeSet_mass,sum_naturalPrimeSet]
  simp only [extendPrimeTest_val,one_div]

theorem primeShellPrior_real_mean {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (hE : 0 < primeShellMass E) (f : PrimeUpTo Q → ℂ) :
    (primeShellPrior E hE).mean (fun p => (f p).re)=
      (∑ p∈E,(p.val:ℝ)⁻¹*(f p).re)/primeShellMass E := by
  unfold FinitePrior.mean
  simp_rw [primeShellPrior_mass,div_mul_eq_mul_div]
  rw [←Finset.sum_div]
  congr 1
  simp only [ite_mul,zero_mul,Finset.sum_ite_mem,Finset.univ_inter]

theorem exists_many_good_bounded_prime_cells (c₀ δ : ℝ) (hc₀ : 0 < c₀) (hδ : 0 < δ) :
    ∃ c b₀ : ℝ, 0 < c ∧ 2 ≤ b₀ ∧ ∀ (Q : ℕ) (E : Finset (PrimeUpTo Q))
      (f : PrimeUpTo Q → ℂ) (b : ℝ), b₀ ≤ b →
      (∀ p∈E,b ≤ Real.log p.val ∧ Real.log p.val ≤ Real.exp 1*b) →
      c₀ ≤ primeShellMass E → (∀ p∈E,‖f p‖ ≤ 1) →
      δ/2 ≤ (∑ p∈E,(p.val:ℝ)⁻¹*(f p).re)/primeShellMass E →
      ∃ I : Finset ℤ, c*b ≤ (I.card:ℝ) ∧ ∀ h∈I,
        b ≤ (h:ℝ) ∧ (h:ℝ) ≤ Real.exp 1*b ∧
        c/b ≤ primeShellMass (boundedRawLogCell E h) ∧
        δ/4 ≤ (∑ p∈boundedRawLogCell E h,(p.val:ℝ)⁻¹*(f p).re)/
          primeShellMass (boundedRawLogCell E h) := by
  obtain ⟨c,b₀,hc,hb₀,h⟩ := exists_many_good_prime_cells c₀ δ hc₀ hδ
  refine ⟨c,b₀,hc,hb₀,?_⟩
  intro Q E f b hb hband hmass hf hmean
  have hn (p : ℕ) (hp : p∈naturalPrimeSet E) : ∃ q∈E,q.val=p := Finset.mem_image.mp hp
  have hmpos : 0 < primeShellMass E := hc₀.trans_le hmass
  have he := h (naturalPrimeSet E) (extendPrimeTest f) b hb
    (fun p hp => by obtain ⟨q,hq,rfl⟩ := hn p hp; exact primeUpTo_prime q)
    (fun p hp => by obtain ⟨q,hq,rfl⟩ := hn p hp; exact hband q hq)
    (by rw [naturalPrimeSet_mass]; exact hmass)
    (fun p hp => by obtain ⟨q,hq,rfl⟩ := hn p hp; simpa only [extendPrimeTest_val] using hf q hq)
    (by
      rw [naturalPrimeSet_mass,sum_naturalPrimeSet]
      simp only [extendPrimeTest_val,one_div]
      exact (le_div_iff₀ hmpos).mp hmean)
  obtain ⟨I,hI,hcells⟩ := he
  refine ⟨I,hI,?_⟩
  intro j hj
  obtain ⟨hlo,hhi,hcell,htest⟩ := hcells j hj
  rw [naturalPrimeSet_cell,naturalPrimeSet_mass] at hcell
  rw [rawCellMeanReal_bounded] at htest
  exact ⟨hlo,hhi,hcell,htest⟩

end Ostmann.Characters.HigherBiasSource

end

end OAI
