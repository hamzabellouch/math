import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformRestrict
import OAI.Computability.MinUncut.Estimates.AlgebraicSigns

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncut.FiniteGaussian
lemma c_algebraicNonneg : Computable (fun p : ℚ × ℚ × ℕ=>algebraicNonneg p.1 p.2.1 p.2.2) := by
  have ha : Computable (fun p : ℚ × ℚ × ℕ=>p.1) := Computable.fst
  have hb : Computable (fun p : ℚ × ℚ × ℕ=>p.2.1) := Computable.fst.comp Computable.snd
  have hn : Computable (fun p : ℚ × ℚ × ℕ=>p.2.2) := Computable.snd.comp Computable.snd
  exact (Computable.cond (ca_ratLe (ca_const 0) hb).decide
    (Computable.cond (ca_ratLe (ca_const 0) ha).decide (ca_const true)
      (ca_ratLe (ca_ratPow ha (ca_const 2)) (ca_ratMul (ca_ratCast hn) (ca_ratPow hb (ca_const 2)))).decide)
    (Computable.cond (ca_ratLt ha (ca_const 0)).decide (ca_const false)
      (ca_ratLe (ca_ratMul (ca_ratCast hn) (ca_ratPow hb (ca_const 2))) (ca_ratPow ha (ca_const 2))).decide)).of_eq
    (by intro p; simp only [algebraicNonneg,Bool.cond_decide])
namespace UEncoding
variable {P : Type} [Primcodable P] {A : P → Type} {a : UEncoding P A}
variable {f g : ∀p,A p → ℚ}
lemma Out.ratAdd (hf : a.Out f) (hg : a.Out g) : a.Out (fun p x=>f p x+g p x) :=
  hf.map₂ hg computable_ratAdd
lemma Out.ratSub (hf : a.Out f) (hg : a.Out g) : a.Out (fun p x=>f p x-g p x) :=
  hf.map₂ hg computable_ratSub
lemma Out.ratMul (hf : a.Out f) (hg : a.Out g) : a.Out (fun p x=>f p x*g p x) :=
  hf.map₂ hg computable_ratMul
lemma Out.ratDiv (hf : a.Out f) (hg : a.Out g) : a.Out (fun p x=>f p x/g p x) :=
  hf.map₂ hg computable_ratDiv
lemma Out.ratInv (hf : a.Out f) : a.Out (fun p x=>(f p x)⁻¹) := hf.map computable_ratInv
lemma Out.ratNeg (hf : a.Out f) : a.Out (fun p x=>-f p x) := hf.map computable_ratNeg
lemma Out.ratNat {f : ∀p,A p → ℕ} (hf : a.Out f) : a.Out (fun p x=>(f p x:ℚ)) :=
  hf.map computable_ratNat
lemma Out.ratPow (hf : a.Out f) {g : ∀p,A p → ℕ} (hg : a.Out g) :
    a.Out (fun p x=>f p x^g p x) := hf.map₂ hg computable_ratPow
lemma Out.algebraicNonneg (hf : a.Out f) (hg : a.Out g) {n : ∀p,A p → ℕ} (hn : a.Out n) :
    a.Map bool (fun p x=>algebraicNonneg (f p x) (g p x) (n p x)) :=
  ((hf.pair (hg.pair hn)).map c_algebraicNonneg).toBool
lemma Out.eqBool {X : Type} [Primcodable X] [DecidableEq X]
    {f g : ∀p,A p → X} (hf : a.Out f) (hg : a.Out g) :
    a.Map bool (fun p x=>decide (f p x=g p x)) :=
  (hf.map₂ hg Primrec.eq.computablePred.decide.to₂).toBool
lemma Out.natAdd {f g : ∀p,A p → ℕ} (hf : a.Out f) (hg : a.Out g) :
    a.Out (fun p x=>f p x+g p x) := hf.map₂ hg Primrec.nat_add.to_comp
lemma Out.natMul {f g : ∀p,A p → ℕ} (hf : a.Out f) (hg : a.Out g) :
    a.Out (fun p x=>f p x*g p x) := hf.map₂ hg Primrec.nat_mul.to_comp
lemma Out.natPow {f g : ∀p,A p → ℕ} (hf : a.Out f) (hg : a.Out g) :
    a.Out (fun p x=>f p x^g p x) := hf.map₂ hg primrec_pow.to_comp
end UEncoding
end MinUncut.Preprocess

end

end OAI
