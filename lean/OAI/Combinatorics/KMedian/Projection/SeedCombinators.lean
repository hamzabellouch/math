import Mathlib
import OAI.Combinatorics.KMedian.Machines.FiniteCoordinates

namespace OAI

section Inline_PCPSeedCombinators
namespace MetricKMedian.PCP.Compiler.SeedCombinators
open Binary Binary.Automatic

variable {T D A : Type} [Coding T] [Coding D] [Coding A]
noncomputable def source (r : T→ℕ→D→ℕ×D) (t : T) (v : ℕ) (s : D×Bool) : ℕ×D :=
  if s.2 then r t v s.1 else (v,s.1)
lemma poly_source (r : T→ℕ→D→ℕ×D) (hr : Poly (fun z : (T×ℕ)×D=>r z.1.1 z.1.2 z.2)) :
    Poly (fun z : (T×ℕ)×(D×Bool)=>source r z.1.1 z.1.2 z.2) := by
  exact Poly.ite (Poly.snd.comp Poly.snd)
    (hr.comp (Poly.pair Poly.fst (Poly.fst.comp Poly.snd)))
    (Poly.pair (Poly.snd.comp Poly.fst) (Poly.fst.comp Poly.snd))
variable [Fintype A] [Inhabited A] [Hardcoded A]
noncomputable def project (r : T→ℕ→D→ℕ×D) (fix : T→ℕ→D→(A×A)→A×A) (t : T) (v : ℕ) (s : D×Bool) : (A×A)→A := fun a =>
  let q := source r t v s
  let b := fix t q.1 q.2 a
  if s.2 then b.2 else b.1
lemma poly_project (r : T→ℕ→D→ℕ×D) (fix : T→ℕ→D→(A×A)→A×A)
    (hr : Poly (fun z : (T×ℕ)×D=>r z.1.1 z.1.2 z.2))
    (hf : Poly (fun z : ((T×ℕ)×D)×(A×A)=>fix z.1.1.1 z.1.1.2 z.1.2 z.2)) :
    Poly (fun z : (T×ℕ)×(D×Bool)=>project r fix z.1.1 z.1.2 z.2) := by
  apply poly_coordinates
  intro a
  have hs := poly_source r hr
  have hh := hf.comp (Poly.pair (Poly.pair (Poly.pair (Poly.fst.comp (Poly.fst : Poly (fun z : (T×ℕ)×(D×Bool)=>z.1)))
    (Poly.fst.comp hs)) (Poly.snd.comp hs)) (Automatic.Poly.const a))
  exact Poly.ite (Poly.snd.comp Poly.snd) (Poly.snd.comp hh) (Poly.fst.comp hh)
noncomputable def numbered (r : T→ℕ→D→ℕ×D) (fix : T→ℕ→D→(A×A)→A×A)
    (index : D→ℕ) (n : ℕ) (t : T) (v : ℕ) (s : D×Bool) : ℕ×((A×A)→A) :=
  let q := source r t v s
  (index q.2+n*q.1,project r fix t v s)
lemma poly_numbered (r : T→ℕ→D→ℕ×D) (fix : T→ℕ→D→(A×A)→A×A)
    (index : D→ℕ) (n : ℕ)
    (hr : Poly (fun z : (T×ℕ)×D=>r z.1.1 z.1.2 z.2))
    (hf : Poly (fun z : ((T×ℕ)×D)×(A×A)=>fix z.1.1.1 z.1.1.2 z.1.2 z.2))
    (hi : Poly index) : Poly (fun z : (T×ℕ)×(D×Bool)=>numbered r fix index n z.1.1 z.1.2 z.2) := by
  have hs := poly_source r hr
  exact Poly.pair (Poly.nat_add.comp (Poly.pair (hi.comp (Poly.snd.comp hs))
    (Poly.nat_mul.comp (Poly.pair (Automatic.Poly.const n) (Poly.fst.comp hs))))) (poly_project r fix hr hf)
end MetricKMedian.PCP.Compiler.SeedCombinators

end Inline_PCPSeedCombinators

end OAI
