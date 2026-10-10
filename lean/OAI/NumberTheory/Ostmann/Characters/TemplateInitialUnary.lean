import OAI.NumberTheory.Ostmann.Characters.TemplateInitialPhase

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template

def initialKappa {p:ℕ} [Fact p.Prime] (χ:MulChar (ZMod p) ℂ) : ℂ :=
  (gaussSum χ ZMod.stdAddChar/(Real.sqrt p:ℂ))*χ⁻¹ (-1)

theorem norm_initialKappa {p:ℕ} [Fact p.Prime] (χ:MulChar (ZMod p) ℂ)
    (hχ:χ≠1) : ‖initialKappa χ‖=1 := by
  have hp : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  simp only [initialKappa,norm_mul,norm_div,
    norm_gaussSum χ hχ _ (ZMod.isPrimitive_stdAddChar p),ZMod.card,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    norm_character_of_ne_zero χ⁻¹ (neg_ne_zero.mpr one_ne_zero),mul_one]
  exact div_self (Real.sqrt_pos.mpr hp).ne'

theorem initialUnary_factor {ι:Type*} [Fintype ι] [DecidableEq ι]
    (p:ι→ℕ) [∀i,Fact (p i).Prime] (χ:∀i,MulChar (ZMod (p i)) ℂ)
    (a:∀i,ZMod (p i)) (s:ℤ) (i:ι) :
    initialUnary p χ a s i =
      ZMod.stdAddChar (-(a i*Construction.crtFrequency p s i))*
        (initialKappa (χ i)*(χ i (s:ZMod (p i)))^(-1:ℤ)) := by
  unfold initialUnary initialKappa
  rw [show -(s:ZMod (p i))=(-1)*(s:ZMod (p i)) by ring,map_mul]
  simp only [MulChar.inv_apply_eq_inv',zpow_neg_one]
  ring

theorem initialPhase_separate {ι:Type*} [Fintype ι] [DecidableEq ι]
    (p:ι→ℕ) [∀i,Fact (p i).Prime] (χ:∀i,MulChar (ZMod (p i)) ℂ)
    (a:∀i,ZMod (p i)) (s:ℤ) :
    initialPhase p χ a s =
      (∏i,ZMod.stdAddChar (-(a i*Construction.crtFrequency p s i)))*
        primeGraphPhase (fun i j => if i=j then 0 else 1) p χ
          (fun i => initialKappa (χ i)*(χ i (s:ZMod (p i)))^(-1:ℤ)) := by
  unfold initialPhase primeGraphPhase
  simp_rw [initialUnary_factor,complete_graph_row]
  simp only [← mul_assoc,← Finset.prod_mul_distrib]

end Ostmann.Characters.Template

end

end OAI
