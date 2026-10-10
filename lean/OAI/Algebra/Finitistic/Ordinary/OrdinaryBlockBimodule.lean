import OAI.Algebra.Finitistic.Ordinary.OrdinaryTerminal

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k L R O T : Type u} [Field k] [Ring L] [Ring R]
  [AddCommGroup O] [AddCommGroup T]

/-- The off-diagonal ordinary bimodule O ⊕ T over L × R. -/
def OffDiagonal (O T : Type u) := O × T
namespace OffDiagonal
instance : AddCommGroup (OffDiagonal O T) := inferInstanceAs (AddCommGroup (O × T))
instance [Module k O] [Module k T] : Module k (OffDiagonal O T) :=
  inferInstanceAs (Module k (O × T))

instance leftModule [Module R O] [Module L T] : Module (L × R) (OffDiagonal O T) := by
  let : Module (L × R) O := Module.compHom O (RingHom.snd L R)
  let : Module (L × R) T := Module.compHom T (RingHom.fst L R)
  exact inferInstanceAs (Module (L × R) (O × T))

instance rightModule [Module Lᵐᵒᵖ O] [Module Rᵐᵒᵖ T] :
    Module (L × R)ᵐᵒᵖ (OffDiagonal O T) := by
  let : Module (L × R)ᵐᵒᵖ O := Module.compHom O (RingHom.fst L R).op
  let : Module (L × R)ᵐᵒᵖ T := Module.compHom T (RingHom.snd L R).op
  exact inferInstanceAs (Module (L × R)ᵐᵒᵖ (O × T))

instance commuteActions [Module R O] [Module L T] [Module Lᵐᵒᵖ O] [Module Rᵐᵒᵖ T]
    [SMulCommClass R Lᵐᵒᵖ O] [SMulCommClass L Rᵐᵒᵖ T] :
    SMulCommClass (L × R) (L × R)ᵐᵒᵖ (OffDiagonal O T) where
  smul_comm x y z := by
    apply Prod.ext
    · change x.2 • (MulOpposite.op y.unop.1 • z.1) = MulOpposite.op y.unop.1 • (x.2 • z.1)
      exact smul_comm _ _ _
    · change x.1 • (MulOpposite.op y.unop.2 • z.2) = MulOpposite.op y.unop.2 • (x.1 • z.2)
      exact smul_comm _ _ _

instance towerLeft [Algebra k L] [Algebra k R] [Module k O] [Module k T]
    [Module R O] [Module L T] [IsScalarTower k R O] [IsScalarTower k L T] :
    IsScalarTower k (L × R) (OffDiagonal O T) where
  smul_assoc c x z := Prod.ext (smul_assoc c x.2 z.1) (smul_assoc c x.1 z.2)

instance towerRight [Algebra k L] [Algebra k R] [Module k O] [Module k T]
    [Module Lᵐᵒᵖ O] [Module Rᵐᵒᵖ T] [IsScalarTower k Lᵐᵒᵖ O] [IsScalarTower k Rᵐᵒᵖ T] :
    IsScalarTower k (L × R)ᵐᵒᵖ (OffDiagonal O T) where
  smul_assoc c x z := Prod.ext (smul_assoc c (MulOpposite.op x.unop.1) z.1)
    (smul_assoc c (MulOpposite.op x.unop.2) z.2)

instance finiteDimensional [Module k O] [Module k T]
    [FiniteDimensional k O] [FiniteDimensional k T] : FiniteDimensional k (OffDiagonal O T) :=
  inferInstanceAs (FiniteDimensional k (O × T))

/-- The first left block selects precisely T. -/
theorem first_left [Module R O] [Module L T] (x : OffDiagonal O T) :
    ((1,0) : L × R) • x = (0,x.2) := by
  apply Prod.ext
  · exact zero_smul _ _
  · exact one_smul _ _

/-- The first right block selects precisely O. -/
theorem first_right [Module Lᵐᵒᵖ O] [Module Rᵐᵒᵖ T] (x : OffDiagonal O T) :
    MulOpposite.op ((1,0) : L × R) • x = (x.1,0) := by
  apply Prod.ext
  · exact one_smul _ _
  · exact zero_smul _ _
end OffDiagonal

open CategoryTheory
open scoped TensorProduct
variable {B : Type u} [Ring B] [Algebra k B]

/-- The actual ordinary Section 5 bimodule X over D=B×(B tensor C). -/
abbrev BimoduleX (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ) :=
  OffDiagonal (BimoduleO P a l) (TerminalTensor B)

theorem ordinary_bimodule (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ)
    (a : ℤ) (l : ℕ) :
    SMulCommClass (AlgebraD k l B) (AlgebraD k l B)ᵐᵒᵖ (BimoduleX P a l) := inferInstance

theorem ordinary_finite (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ)
    (a : ℤ) (l : ℕ) [FiniteDimensional k B]
    [∀ n, FiniteDimensional k ((underlyingComplex (k := k) P).X n)] :
    FiniteDimensional k (BimoduleX P a l) := inferInstance
end LittleFinitistic.OrdinarySimulation

end

end OAI
