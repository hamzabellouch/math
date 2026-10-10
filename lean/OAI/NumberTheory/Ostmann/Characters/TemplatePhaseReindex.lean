import OAI.NumberTheory.Ostmann.Characters.TemplatePhasePivotSplit

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template

theorem otherProduct_equiv {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e:κ≃ι) (p:ι→ℕ) (i:κ) (hp:p (e i)≠0) :
    Construction.otherProduct (fun j => p (e j)) i=Construction.otherProduct p (e i) := by
  apply mul_right_cancel₀ hp
  rw [Construction.otherProduct,Construction.otherProduct,
    Finset.prod_erase_mul _ _ (Finset.mem_univ _),Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  exact e.prod_comp p

theorem completePrimePhase_reindex {ι κ:Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e:κ≃ι)
    (p:ι→ℕ) [∀i,Fact (p i).Prime] (χ:∀i,MulChar (ZMod (p i)) ℂ)
    (a:∀i,ZMod (p i)) (ν:ι→ℂ) (B:ι→ι→ℤ) (v:ℤ) :
    completePrimePhase (fun i => p (e i)) (fun i => χ (e i)) (fun i => a (e i))
      (fun i => ν (e i)) (fun i j => B (e i) (e j)) v =
    completePrimePhase p χ a ν B v := by
  have hd (i:κ) := otherProduct_equiv e p i (Fact.out : (p (e i)).Prime).ne_zero
  have hr (i:κ) : (∏j:κ,χ (e i) (p (e j))^B (e i) (e j))=
      ∏j:ι,χ (e i) (p j)^B (e i) j :=
    e.prod_comp (fun j => χ (e i) (p j)^B (e i) j)
  unfold completePrimePhase primeGraphPhase Construction.crtFrequency
  simp_rw [hd,hr]
  rw [e.prod_comp (fun i => ZMod.stdAddChar (-(a i*((v:ZMod (p i))*
      (Construction.otherProduct p i:ZMod (p i))⁻¹)))),
    e.prod_comp (fun i => ν i*∏j:ι,χ i (p j)^B i j)]

end Ostmann.Characters.Template

end

end OAI
