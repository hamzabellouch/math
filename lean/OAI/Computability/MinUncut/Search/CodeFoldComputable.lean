import Mathlib
import OAI.Computability.MinUncut.Estimates.CodeComputability

namespace OAI

section
namespace MinUncut.CodeEffective
open Turing.ToPartrec
variable {σ : Type*} [Primcodable σ]
def fold (z s t : σ) (b3 b4 b5 : σ → σ → σ) (f6 : σ → σ) : Code → σ
  | .zero' => z
  | .succ => s
  | .tail => t
  | .cons f g => b3 (fold z s t b3 b4 b5 f6 f) (fold z s t b3 b4 b5 f6 g)
  | .comp f g => b4 (fold z s t b3 b4 b5 f6 f) (fold z s t b3 b4 b5 f6 g)
  | .case f g => b5 (fold z s t b3 b4 b5 f6 f) (fold z s t b3 b4 b5 f6 g)
  | .fix f => f6 (fold z s t b3 b4 b5 f6 f)
lemma primrec_fold (z s t : σ) {b3 b4 b5 : σ → σ → σ} {f6 : σ → σ}
    (h3 : Primrec₂ b3) (h4 : Primrec₂ b4) (h5 : Primrec₂ b5) (h6 : Primrec f6) :
    Primrec (fold z s t b3 b4 b5 f6) := by
  have h := Nat.Partrec.Code.primrec_recOn (α:=Code) (σ:=σ) primrec_embed
    (z:=fun _=>z) (Primrec.const _) (s:=fun _=>s) (Primrec.const _)
    (l:=fun _=>t) (Primrec.const _) (r:=fun _=>t) (Primrec.const _)
    (pr:=fun _ _ _ x y=>b3 x y)
    (h3.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (co:=fun _ _ _ x y=>b4 x y)
    (h4.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (pc:=fun _ _ _ x y=>b5 x y)
    (h5.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (rf:=fun _ _ x=>f6 x) (h6.comp (Primrec.snd.comp Primrec.snd))
  apply h.of_eq
  intro c
  induction c <;> simp_all [fold,embed]
end MinUncut.CodeEffective

end

end OAI
