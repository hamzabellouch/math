import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ScalarSamplerCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationResidueDraws
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationExtraDraw

namespace OAI

/-! # Stored-width scalar preparation with explicit sampler memory

These wrappers transport the seed types of the preparation program.
Their live-storage annotations preserve the returned values and work counters.
-/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationScalarCells

variable {n : ℕ}

def nested (n : ℕ) (widths : Vector ℕ 4) (s : RepresentationScalarDraws.Seed n widths) :=
  ScalarSamplerCells.nested n widths[0] widths[1] widths[2] s

theorem nested_value (n : ℕ) (widths : Vector ℕ 4) (s : RepresentationScalarDraws.Seed n widths) :
    (nested n widths s).1 = RepresentationScalarDraws.nested n widths s :=
  ScalarSamplerCells.nested_value n widths[0] widths[1] widths[2] s

def draw (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (widths : Vector ℕ 4) (h : ∀ j : Fin 4, widths[j.val] = R.samplerPrimeWidths z j)
    (s : (R.nestedCoupling z).Seed) :=
  nested n widths (RepresentationScalarDraws.transport
    (RepresentationScalarDraws.widths_eq R z widths h) s)

theorem draw_value (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (widths : Vector ℕ 4) (h : ∀ j : Fin 4, widths[j.val] = R.samplerPrimeWidths z j)
    (s : (R.nestedCoupling z).Seed) :
    (draw R z widths h s).1 = RepresentationScalarDraws.draw R z widths h s :=
  nested_value _ _ _

theorem draw_cells (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (widths : Vector ℕ 4) (h : ∀ j : Fin 4, widths[j.val] = R.samplerPrimeWidths z j)
    (s : (R.nestedCoupling z).Seed) : (draw R z widths h s).2 ≤ 9*n^3+320 :=
  ScalarSamplerCells.nested_cells _ _ _ _ _

def residues (n : ℕ) (m : Vector ℕ 3) (hm : ∀ i : Fin 3, 0 < m[i.val])
    (s : RepresentationResidueDraws.Seed n m hm) : (Option (Vector ℕ 3) × ℕ) × ℕ := by
  letI : NeZero m[0] := ⟨(hm 0).ne'⟩
  letI : NeZero m[1] := ⟨(hm 1).ne'⟩
  letI : NeZero m[2] := ⟨(hm 2).ne'⟩
  exact ScalarSamplerCells.residues n m[0] m[1] m[2] s

theorem residues_value (n : ℕ) (m : Vector ℕ 3) (hm : ∀ i : Fin 3, 0 < m[i.val])
    (s : RepresentationResidueDraws.Seed n m hm) :
    (residues n m hm s).1 = RepresentationResidueDraws.run n m hm s := by
  let : NeZero m[0] := ⟨(hm 0).ne'⟩
  let : NeZero m[1] := ⟨(hm 1).ne'⟩
  let : NeZero m[2] := ⟨(hm 2).ne'⟩
  exact ScalarSamplerCells.residues_value n m[0] m[1] m[2] s

theorem residues_cells (n : ℕ) (m : Vector ℕ 3) (hm : ∀ i : Fin 3, 0 < m[i.val])
    (s : RepresentationResidueDraws.Seed n m hm) : (residues n m hm s).2 ≤ 9*n^3+288 := by
  let : NeZero m[0] := ⟨(hm 0).ne'⟩
  let : NeZero m[1] := ⟨(hm 1).ne'⟩
  let : NeZero m[2] := ⟨(hm 2).ne'⟩
  exact ScalarSamplerCells.residues_cells n m[0] m[1] m[2] s

def drawResidues (R : RepresentationSetup n) {z : RepresentationSetup.Layout n} (p : R.PrimeSpace z)
    (m : Vector ℕ 3) (hm : ∀ i : Fin 3, 0 < m[i.val])
    (h : ∀ i : Fin 3, m[i.val] = prefixModulus p.val i) (s : (R.residuesCoupling p).Seed) :=
  residues n m hm (RepresentationResidueDraws.transport
    (hm' := RepresentationResidueDraws.sourcePos p) (RepresentationResidueDraws.moduli_eq m p.val h) s)

theorem drawResidues_value (R : RepresentationSetup n) {z : RepresentationSetup.Layout n}
    (p : R.PrimeSpace z) (m : Vector ℕ 3) (hm : ∀ i : Fin 3, 0 < m[i.val])
    (h : ∀ i : Fin 3, m[i.val] = prefixModulus p.val i) (s : (R.residuesCoupling p).Seed) :
    (drawResidues R p m hm h s).1 = RepresentationResidueDraws.draw R p m hm h s :=
  residues_value _ _ _ _

theorem drawResidues_cells (R : RepresentationSetup n) {z : RepresentationSetup.Layout n}
    (p : R.PrimeSpace z) (m : Vector ℕ 3) (hm : ∀ i : Fin 3, 0 < m[i.val])
    (h : ∀ i : Fin 3, m[i.val] = prefixModulus p.val i) (s : (R.residuesCoupling p).Seed) :
    (drawResidues R p m hm h s).2 ≤ 9*n^3+288 := residues_cells _ _ _ _

def extra (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (hn : 100 ≤ n)
    (ell : ℕ) (he : ell = R.extraPrimeParameter z) (s : (R.extraPrimeCoupling z hn).Seed) :=
  ScalarSamplerCells.extra (he.symm ▸ (R.extraPrimeParameter_range z hn).1) n
    (RepresentationExtraDraw.transport he s)

theorem extra_value (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (hn : 100 ≤ n)
    (ell : ℕ) (he : ell = R.extraPrimeParameter z) (s : (R.extraPrimeCoupling z hn).Seed) :
    (extra R z hn ell he s).1 = RepresentationExtraDraw.draw R z hn ell he s :=
  ScalarSamplerCells.extra_value _ _ _

theorem extra_cells (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (hn : 100 ≤ n)
    (ell : ℕ) (he : ell = R.extraPrimeParameter z) (s : (R.extraPrimeCoupling z hn).Seed) :
    (extra R z hn ell he s).2 ≤ 3*n^3+96 := ScalarSamplerCells.extra_cells _ _ _

end LowSpaceSubsetSum.RepresentationScalarCells

end

end OAI
