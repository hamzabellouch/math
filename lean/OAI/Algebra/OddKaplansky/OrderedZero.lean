import OAI.Algebra.OddKaplansky.CyclicCoset

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4

section
namespace OddKaplansky.OrderedZero
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {A : Type portUniverse2} {B : Type portUniverse3} {G : Type portUniverse4} [Field K] [Group A] [Group B] [Group G] [Fintype A]
variable (p ell : ℕ) [Fact p.Prime] [CharP K p]
lemma product_zero (hell : ell ≤ p-ell)
    (i : CyclicAlgebra.C p →* A) (hi : Function.Injective i)
    (j : CyclicAlgebra.C p →* B) (φ : A →* G) (ψ : B →* G)
    (hij : φ (i (CyclicAlgebra.gen p)) = ψ (j (CyclicAlgebra.gen p)))
    (a : MonoidAlgebra K A) (b : MonoidAlgebra K B)
    (ha : a*(MonoidAlgebra.single (i (CyclicAlgebra.gen p)) 1-1)^ell=0)
    (hb : (MonoidAlgebra.single (j (CyclicAlgebra.gen p)) 1-1)^ell*b=0) :
    MonoidAlgebra.mapDomainAlgHom K K φ a * MonoidAlgebra.mapDomainAlgHom K K ψ b=0 := by
  let Φ := MonoidAlgebra.mapDomainAlgHom K K φ
  let Ψ := MonoidAlgebra.mapDomainAlgHom K K ψ
  let X : MonoidAlgebra K G := MonoidAlgebra.single (φ (i (CyclicAlgebra.gen p))) 1-1
  obtain ⟨c,hc⟩ := CyclicAlgebra.embedded_right_divisible p i hi ell (by omega) a ha
  have hm : Φ (MonoidAlgebra.single (i (CyclicAlgebra.gen p)) 1-1)=X := by rw [map_sub,map_one]; simp only [Φ,X,MonoidAlgebra.mapDomainAlgHom_apply,MonoidAlgebra.mapDomain_single]
  have hn : Ψ (MonoidAlgebra.single (j (CyclicAlgebra.gen p)) 1-1)=X := by rw [map_sub,map_one]; simp only [Ψ,X,MonoidAlgebra.mapDomainAlgHom_apply,MonoidAlgebra.mapDomain_single,hij]
  have hb' : X^ell*Ψ b=0 := by
    have hh := congrArg Ψ hb
    simpa only [map_mul,map_pow,hn,map_zero] using hh
  change Φ a*Ψ b=0
  rw [hc,map_mul,map_pow,hm,mul_assoc]
  have hp : p-ell = (p-ell-ell)+ell := by omega
  rw [hp,pow_add,mul_assoc,hb',mul_zero,mul_zero]
end
end OddKaplansky.OrderedZero

end

end OAI
