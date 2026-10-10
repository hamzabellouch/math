import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ScalarSamplerArrays

namespace OAI

/-! # Three bounded residue draws at the stored integer moduli -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationResidueDraws

variable {n : ℕ}

def Seed (n : ℕ) (m : Vector ℕ 3) (hm : ∀ i : Fin 3, 0 < m[i.val]) : Type := by
  letI : NeZero m[0] := ⟨(hm 0).ne'⟩
  letI : NeZero m[1] := ⟨(hm 1).ne'⟩
  letI : NeZero m[2] := ⟨(hm 2).ne'⟩
  exact (ScalarSamplerArrays.residueCoupling n m[0] m[1] m[2]).Seed

def run (n : ℕ) (m : Vector ℕ 3) (hm : ∀ i : Fin 3, 0 < m[i.val])
    (s : Seed n m hm) : Option (Vector ℕ 3) × ℕ := by
  letI : NeZero m[0] := ⟨(hm 0).ne'⟩
  letI : NeZero m[1] := ⟨(hm 1).ne'⟩
  letI : NeZero m[2] := ⟨(hm 2).ne'⟩
  exact ScalarSamplerArrays.residues n m[0] m[1] m[2] s

def transport {m m' : Vector ℕ 3} {hm : ∀ i : Fin 3, 0 < m[i.val]}
    {hm' : ∀ i : Fin 3, 0 < m'[i.val]} (h : m = m') (s : Seed n m' hm') : Seed n m hm := by
  subst m'
  exact s

theorem run_transport {m m' : Vector ℕ 3} {hm : ∀ i : Fin 3, 0 < m[i.val]}
    {hm' : ∀ i : Fin 3, 0 < m'[i.val]} (h : m = m') (s : Seed n m' hm') :
    run n m hm (transport h s) = run n m' hm' s := by
  subst m'
  rfl

def sourceModuli (p : (ℕ × ℕ) × ℕ) : Vector ℕ 3 := Vector.ofFn (prefixModulus p)

theorem sourcePos {a b c : ℕ} (p : ↥(tripleRange a b c)) (i : Fin 3) :
    0 < (sourceModuli p.val)[i.val] := by
  simpa only [sourceModuli, Vector.getElem_ofFn] using prefixModulus_pos p i

theorem moduli_eq (m : Vector ℕ 3) (p : (ℕ × ℕ) × ℕ)
    (h : ∀ i : Fin 3, m[i.val] = prefixModulus p i) : m = sourceModuli p := by
  apply Vector.ext
  intro i hi
  simpa only [sourceModuli, Vector.getElem_ofFn] using h ⟨i, hi⟩

def draw (R : RepresentationSetup n) {z : RepresentationSetup.Layout n} (p : R.PrimeSpace z)
    (m : Vector ℕ 3) (hm : ∀ i : Fin 3, 0 < m[i.val])
    (h : ∀ i : Fin 3, m[i.val] = prefixModulus p.val i) (s : (R.residuesCoupling p).Seed) :
    Option (Vector ℕ 3) × ℕ :=
  run n m hm (transport (hm' := sourcePos p) (moduli_eq m p.val h) s)

theorem draw_value (R : RepresentationSetup n) {z : RepresentationSetup.Layout n} (p : R.PrimeSpace z)
    (m : Vector ℕ 3) (hm : ∀ i : Fin 3, 0 < m[i.val])
    (h : ∀ i : Fin 3, m[i.val] = prefixModulus p.val i) (s : (R.residuesCoupling p).Seed) :
    (draw R p m hm h s).1 = ((R.residuesCoupling p).bounded s).map ScalarSamplerArrays.residueValues := by
  let : NeZero (prefixModulus p.val 0) := ⟨(prefixModulus_pos p 0).ne'⟩
  let : NeZero (prefixModulus p.val 1) := ⟨(prefixModulus_pos p 1).ne'⟩
  let : NeZero (prefixModulus p.val 2) := ⟨(prefixModulus_pos p 2).ne'⟩
  exact (congrArg Prod.fst (run_transport (n := n) (hm := hm) (hm' := sourcePos p)
    (moduli_eq m p.val h) (show Seed n (sourceModuli p.val) (sourcePos p) from s))).trans
    (ScalarSamplerArrays.residues_value n (prefixModulus p.val 0)
      (prefixModulus p.val 1) (prefixModulus p.val 2) s)

theorem draw_work (R : RepresentationSetup n) {z : RepresentationSetup.Layout n} (p : R.PrimeSpace z)
    (m : Vector ℕ 3) (hm : ∀ i : Fin 3, 0 < m[i.val])
    (h : ∀ i : Fin 3, m[i.val] = prefixModulus p.val i) (s : (R.residuesCoupling p).Seed) :
    (draw R p m hm h s).2 ≤ 3 * n ^ 3 + 7 := by
  let : NeZero (prefixModulus p.val 0) := ⟨(prefixModulus_pos p 0).ne'⟩
  let : NeZero (prefixModulus p.val 1) := ⟨(prefixModulus_pos p 1).ne'⟩
  let : NeZero (prefixModulus p.val 2) := ⟨(prefixModulus_pos p 2).ne'⟩
  calc
    _ = (run n (sourceModuli p.val) (sourcePos p)
        (show Seed n (sourceModuli p.val) (sourcePos p) from s)).2 :=
      congrArg Prod.snd (run_transport (n := n) (hm := hm) (hm' := sourcePos p)
        (moduli_eq m p.val h) (show Seed n (sourceModuli p.val) (sourcePos p) from s))
    _ ≤ _ := ScalarSamplerArrays.residues_work n (prefixModulus p.val 0)
      (prefixModulus p.val 1) (prefixModulus p.val 2) s

end LowSpaceSubsetSum.RepresentationResidueDraws

end

end OAI
