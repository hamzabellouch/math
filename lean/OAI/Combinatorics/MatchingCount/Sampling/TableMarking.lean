import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.ProductBits

namespace OAI

namespace MatchingFPRAS.TableMarking

open Finset Transport Variation

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

variable (inc : E → V → Prop)

abbrev Marked := Σ M : PM inc, (↥M.val → I)

def reveal (M : PM inc) (marks : E → I) : Marked (I:=I) inc := ⟨M,fun e=>marks e.val⟩

variable {A : Type*} [Fintype A] [Nonempty A]

def draw (f : A → PM inc) (c : E → WeightedOptions I) (k : ℕ)
    (bits : A×(E → Fin k → Bool)) : Marked (I:=I) inc :=
  reveal inc (f bits.1) (fun e=>(c e).draw k (bits.2 e))

noncomputable def portion (c : E → WeightedOptions I) (e : E) (i : I) : ℝ := (c e).law i

noncomputable def law (w : E → ℝ) (c : E → WeightedOptions I) : Marked (I:=I) inc → ℝ :=
  sigmaLift (gibbs w) (fun M=>product (fun e : M.val=>portion c e.val))

lemma reveal_law (p : PM inc → ℝ) (c : E → WeightedOptions I) :
    push (tensor p (product (portion c))) (fun x : PM inc×(E → I)=>reveal inc x.1 x.2)=
      sigmaLift p (fun M=>product (fun e : M.val=>portion c e.val)) := by
  calc
    _ = sigmaLift p (fun M=>push (product (portion c)) (fun m=>fun e : M.val=>m e.val)) := by
      exact push_tensor_sigma p (product (portion c)) (fun M m=>fun e : M.val=>m e.val)
    _ = _ := ?_
  congr 1
  funext M
  apply product_restrict
  intro e
  exact WeightedOptions.real_law_sum (c e)

lemma draw_tv (f : A → PM inc) (w : E → ℝ) (c : E → WeightedOptions I) (k : ℕ) :
    tv (imageLaw (draw inc f c k)) (law inc w c)≤
      tv (imageLaw f) (gibbs w)+(∑ e : E,(2:ℝ)*(c e).size)/(2:ℝ)^k := by
  let mark : (E → Fin k → Bool) → E → I := fun bits e=>(c e).draw k (bits e)
  have hs (e : E) : ∑ b,portion c e b=1 := WeightedOptions.real_law_sum _
  have hn (e : E) (b : I) : 0≤portion c e b := (Rat.cast_nonneg (K:=ℝ)).mpr ((c e).law_nonneg b)
  have hm : tv (imageLaw mark) (product (portion c))≤(∑ e : E,(2:ℝ)*(c e).size)/(2:ℝ)^k := by
    rw [show mark=(fun bits : E → Fin k → Bool=>fun e=>(c e).draw k (bits e)) from rfl,
      imageLaw_componentwise]
    have hh:=product_tv (fun e=>imageLaw ((c e).draw k)) (portion c)
      (fun e=>imageLaw_nonneg _) (fun e=>imageLaw_sum _) hn hs
    refine hh.trans ?_
    rw [sum_div]
    apply sum_le_sum
    intro e _
    exact (c e).draw_tv k
  have htv:=tensor_tv (imageLaw f) (gibbs w) (imageLaw mark) (product (portion c))
    (imageLaw_nonneg f) (imageLaw_sum f) (product_nonneg _ hn) (product_sum _ hs)
  have hc:=push_contraction (tensor (imageLaw f) (imageLaw mark))
    (tensor (gibbs w) (product (portion c))) (fun x : PM inc×(E → I)=>reveal inc x.1 x.2)
  rw [reveal_law inc _ c,←imageLaw_tensor f mark,←imageLaw_comp] at hc
  change tv (imageLaw (draw inc f c k)) (law inc w c)≤_ at hc
  rw [imageLaw_tensor f mark] at hc
  exact hc.trans (htv.trans (add_le_add_right hm _))

lemma draw_tv_size (f : A → PM inc) (w : E → ℝ) (c : E → WeightedOptions I) (k s : ℕ)
    (h : ∀ e,(c e).size=s) :
    tv (imageLaw (draw inc f c k)) (law inc w c)≤
      tv (imageLaw f) (gibbs w)+2*s*Fintype.card E/(2:ℝ)^k := by
  have hh:=draw_tv inc f w c k
  simpa [h,mul_comm,mul_left_comm,mul_assoc] using hh

end MatchingFPRAS.TableMarking

end OAI
