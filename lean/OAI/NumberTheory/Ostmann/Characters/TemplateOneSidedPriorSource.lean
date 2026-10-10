import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPriorDyadic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedPrior
open Construction Preliminaries PrimeDyadicCover
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sourceNaturals {A : ℕ} (E : Finset (PrimeUpTo A)) : Finset ℕ := E.image Subtype.val

theorem sum_sourceNaturals {A : ℕ} {B : Type*} [AddCommMonoid B]
    (E : Finset (PrimeUpTo A)) (f : ℕ→B) :
    (∑p∈sourceNaturals E,f p)=∑p∈E,f p.val := by
  rw [sourceNaturals,Finset.sum_image]
  intro p hp q hq he
  exact Subtype.ext he

theorem sourceNaturals_mass {A : ℕ} (E : Finset (PrimeUpTo A)) :
    (∑p∈sourceNaturals E,(p:ℝ)⁻¹)=primeShellMass E :=
  sum_sourceNaturals E _

theorem sourceNaturals_property {A : ℕ} (E : Finset (PrimeUpTo A)) (P : ℕ→Prop)
    (h : ∀p∈E,P p.val) : ∀p∈sourceNaturals E,P p := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  exact h q hq

def sourceRowMass {A : ℕ} (Q U : ℕ) (E : Finset (PrimeUpTo A)) (i : Index U) :
    Fin Q × Fin (2*lower Q U i+1) → ℝ :=
  rowMass Q (lower Q U i) (block Q U (sourceNaturals E) i) (primeShellMass E)

theorem sourceRowMass_nonneg {A : ℕ} (Q U : ℕ) (E : Finset (PrimeUpTo A))
    (hE : 0<primeShellMass E) (i : Index U)
    (x : Fin Q × Fin (2*lower Q U i+1)) : 0 ≤ sourceRowMass Q U E i x :=
  rowMass_nonneg _ _ _ hE x

theorem sourceRowMass_total_le_one {A : ℕ} (Q U : ℕ) (hQ : 0<Q)
    (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E)
    (hmin : ∀p∈E,Q≤p.val) (i : Index U) :
    (∑x,sourceRowMass Q U E i x)≤1 := by
  unfold sourceRowMass
  rw [sum_rowMass Q _ hQ _ (fun p hp=>(block_bounds hQ _
    (sourceNaturals_property E _ hmin) i hp).2)]
  calc
    _ ≤ ∑p∈sourceNaturals E,(p:ℝ)⁻¹/primeShellMass E := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (block_subset Q U _ i)
      intro p hp hn
      positivity
    _ = 1 := by rw [←Finset.sum_div,sourceNaturals_mass,div_self hE.ne']

theorem sourceRowMass_majorant {A : ℕ} (Q U : ℕ) (hQ : 0<Q)
    (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E)
    (hmin : ∀p∈E,Q≤p.val) (i : Index U)
    (x : Fin Q × Fin (2*lower Q U i+1)) :
    sourceRowMass Q U E i x ≤ longProgressionMajorant (1/primeShellMass E)
      (lower Q U i) Q x.1.val x.2.val :=
  rowMass_majorant _ _ _ hE (block_lower_pos hQ i)
    (fun _p hp=>block_bounds hQ _ (sourceNaturals_property E _ hmin) i hp) x

theorem source_cmean_eq {A : ℕ} (E : Finset (PrimeUpTo A))
    (hE : 0<primeShellMass E) (f : ℕ→ℂ) :
    (primeShellPrior E hE).cmean (fun p=>f p.val)=
      ∑p∈sourceNaturals E,((p:ℝ)⁻¹/primeShellMass E:ℂ)*f p := by
  rw [sum_sourceNaturals]
  unfold FinitePrior.cmean
  simp only [primeShellPrior_mass,ite_div,zero_div,apply_ite,Complex.ofReal_zero,
    ite_mul,zero_mul,Finset.sum_ite_mem,Finset.univ_inter,
    Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_natCast]

theorem source_cmean_eq_rows {A : ℕ} (Q U : ℕ) (hQ : 0<Q)
    (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E)
    (hmin : ∀p∈E,Q≤p.val) (hmax : ∀p∈E,p.val≤U) (f : ℕ→ℂ) :
    (primeShellPrior E hE).cmean (fun p=>f p.val)=
      ∑i:Index U,∑x:Fin Q × Fin (2*lower Q U i+1),
        (sourceRowMass Q U E i x:ℂ)*f (rowValue Q (2*lower Q U i+1) x) := by
  rw [source_cmean_eq]
  rw [←sum_block_rows_eq Q U hQ (sourceNaturals E)
    (sourceNaturals_property E _ hmin) (sourceNaturals_property E _ hmax)]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hmem : rowValue Q (2*lower Q U i+1) x∈block Q U (sourceNaturals E) i
  · simp [sourceRowMass,rowMass,hmem]
  · simp [sourceRowMass,rowMass,hmem]

def sourceTest {A : ℕ} (f : PrimeUpTo A→ℂ) (p : ℕ) : ℂ :=
  if hp : p∈A.primesLE then f ⟨p,hp⟩ else 0

@[simp] theorem sourceTest_val {A : ℕ} (f : PrimeUpTo A→ℂ) (p : PrimeUpTo A) :
    sourceTest f p.val=f p := by simp only [sourceTest,p.property,dite_eq_left]

theorem source_cmean_eq_rows_actual {A : ℕ} (Q U : ℕ) (hQ : 0<Q)
    (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E)
    (hmin : ∀p∈E,Q≤p.val) (hmax : ∀p∈E,p.val≤U) (f : PrimeUpTo A→ℂ) :
    (primeShellPrior E hE).cmean f=
      ∑i:Index U,∑x:Fin Q × Fin (2*lower Q U i+1),
        (sourceRowMass Q U E i x:ℂ)*sourceTest f (rowValue Q (2*lower Q U i+1) x) := by
  simpa only [sourceTest_val] using source_cmean_eq_rows Q U hQ E hE hmin hmax (sourceTest f)

end Ostmann.Characters.TemplateOneSidedPrior

end

end OAI
