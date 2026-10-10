import OAI.Algebra.AuslanderReiten.Cocycles.CocycleData

namespace OAI

namespace ArExplicit.CocycleData

structure QuadMonomial where
  first : TIndex
  second : TIndex
  third : TIndex
  fourth : TIndex
  output : TIndex
  degree : ℕ
  deriving DecidableEq

def QuadMonomial.number (a : QuadMonomial) : ℕ :=
  a.first.number + 20 * (a.second.number + 20 * (a.third.number +
    20 * (a.fourth.number + 20 * (a.output.number + 20 * a.degree))))

def contributions (p : TripleMonomial) (m : MulMonomial) : List QuadMonomial :=
  (if m.second = p.output then
    [⟨m.first, p.first, p.second, p.third, m.output, p.degree + m.degree⟩] else []) ++
  (if m.output = p.first then
    [⟨m.first, m.second, p.second, p.third, p.output, p.degree + m.degree⟩] else []) ++
  (if m.output = p.second then
    [⟨p.first, m.first, m.second, p.third, p.output, p.degree + m.degree⟩] else []) ++
  (if m.output = p.third then
    [⟨p.first, p.second, m.first, m.second, p.output, p.degree + m.degree⟩] else []) ++
  (if m.first = p.output then
    [⟨p.first, p.second, p.third, m.second, m.output, p.degree + m.degree⟩] else [])

def differentialTerms : List QuadMonomial :=
  cochain.flatMap fun p => multiplication.flatMap (contributions p)

def differentialBlock (a : TIndex) : List QuadMonomial :=
  cochain.flatMap fun p => multiplication.flatMap fun m =>
    (contributions p m).filter fun x => decide (x.first = a)

theorem differentialBlock_eq (a : TIndex) :
    differentialBlock a = differentialTerms.filter (fun x => decide (x.first = a)) := by
  simp [differentialBlock, differentialTerms, List.filter_flatMap]

end ArExplicit.CocycleData

end OAI
