import OAI.Algebra.AuslanderReiten.Modules.CoinducedModule
import OAI.Algebra.AuslanderReiten.Complete.FiniteCompleteResolution
import OAI.Algebra.AuslanderReiten.Homology.RestrictionProjective

namespace OAI

noncomputable section

namespace ArExplicit.FiniteLeftModule

open CategoryTheory

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

def canonicalEnvelope (M : FiniteLeftModule k R) : ModuleCat.{u} R :=
  ModuleCat.of R (CoinducedModule k R M.carrier)

def canonicalEmbedding (M : FiniteLeftModule k R) : M.carrier ⟶ M.canonicalEnvelope :=
  ModuleCat.ofHom CoinducedModule.embedding

def canonicalCosyzygy (M : FiniteLeftModule k R) : FiniteLeftModule k R where
  carrier := cokernelObject M.canonicalEmbedding
  scalar := inferInstanceAs (Module k (CoinducedModule k R M.carrier ⧸ LinearMap.range (CoinducedModule.embedding (k := k) (R := R) (M := M.carrier))))
  tower := inferInstanceAs (IsScalarTower k R
    (CoinducedModule k R M.carrier ⧸ LinearMap.range (CoinducedModule.embedding (k := k) (R := R) (M := M.carrier))))
  finite := inferInstanceAs (Module.Finite k
    (CoinducedModule k R M.carrier ⧸ LinearMap.range (CoinducedModule.embedding (k := k) (R := R) (M := M.carrier))))

def canonicalCosyzygies (M : FiniteLeftModule k R) : ℕ → FiniteLeftModule k R
  | 0 => M
  | n + 1 => (canonicalCosyzygies M n).canonicalCosyzygy

variable {S : Type u} [Ring S] (j : S →+* R)
variable [Module.Injective S S]
variable [Module.Finite S ((ModuleCat.restrictScalars j).obj (ModuleCat.of R R))]
variable [Module.Projective S ((ModuleCat.restrictScalars j).obj (ModuleCat.of R R))]

omit [Module.Injective S S] in
theorem canonicalEnvelope_side (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    Module.Finite S ((ModuleCat.restrictScalars j).obj M.canonicalEnvelope) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj M.canonicalEnvelope) := by
  let : Module.Finite R M.canonicalEnvelope := CoinducedModule.finite (M := M.carrier) τ
  let : Module.Projective R M.canonicalEnvelope := CoinducedModule.projective (M := M.carrier) τ
  exact ⟨restrict_finite j M.canonicalEnvelope, restrict_projective j M.canonicalEnvelope⟩

theorem canonicalCosyzygy_side (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)
    [Module.Finite S ((ModuleCat.restrictScalars j).obj M.carrier)]
    [Module.Projective S ((ModuleCat.restrictScalars j).obj M.carrier)] :
    Module.Finite S ((ModuleCat.restrictScalars j).obj M.canonicalCosyzygy.carrier) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj M.canonicalCosyzygy.carrier) := by
  obtain ⟨hfin, hproj⟩ := canonicalEnvelope_side j τ M
  let := hfin
  let := hproj
  let := finiteProjective_injective (R := S) (M := (ModuleCat.restrictScalars j).obj M.carrier)
  constructor
  · exact Module.Finite.equiv (restrictCokernelEquiv j M.canonicalEmbedding).symm
  · exact cokernel_restrict_projective j M.canonicalEmbedding CoinducedModule.embedding_injective

theorem canonicalCosyzygies_side (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)
    [Module.Finite S ((ModuleCat.restrictScalars j).obj M.carrier)]
    [Module.Projective S ((ModuleCat.restrictScalars j).obj M.carrier)] (n : ℕ) :
    Module.Finite S ((ModuleCat.restrictScalars j).obj (M.canonicalCosyzygies n).carrier) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj (M.canonicalCosyzygies n).carrier) := by
  induction n with
  | zero =>
    change Module.Finite S ((ModuleCat.restrictScalars j).obj M.carrier) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj M.carrier)
    exact ⟨inferInstance, inferInstance⟩
  | succ n ih =>
    let := ih.1
    let := ih.2
    exact canonicalCosyzygy_side j τ (M.canonicalCosyzygies n)

end ArExplicit.FiniteLeftModule

end

end OAI
