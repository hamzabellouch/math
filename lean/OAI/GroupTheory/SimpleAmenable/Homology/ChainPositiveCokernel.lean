import Mathlib

namespace OAI

section
open CategoryTheory Limits HomologicalComplex
namespace ChainComplex
open scoped _root_.ChainComplex

variable {R:Type} [CommRing R] (K:ChainComplex (ModuleCat.{0} R) ℕ)
variable (n:ℕ) (hn:K.d (n+1) n=0)
noncomputable def positiveπ : K.X (n+1) ⟶ K.homology (n+1) :=
  K.pOpcycles (n+1) ≫ (K.isoHomologyι (n+1) n (by simp) hn).inv
instance : Epi (positiveπ K n hn) := by dsimp only [positiveπ]; infer_instance
@[reassoc (attr:=simp)] lemma d_positiveπ : K.d (n+2) (n+1) ≫ positiveπ K n hn=0 := by
  simp [positiveπ]
noncomputable def positiveDesc {V:ModuleCat.{0} R} (f:K.X (n+1) ⟶ V)
    (hf:K.d (n+2) (n+1) ≫ f=0) : K.homology (n+1) ⟶ V :=
  (K.isoHomologyι (n+1) n (by simp) hn).hom ≫
    K.descOpcycles f (n+2) (by simp) hf
@[reassoc (attr:=simp)] lemma positiveπ_desc {V:ModuleCat.{0} R} (f:K.X (n+1) ⟶ V)
    (hf:K.d (n+2) (n+1) ≫ f=0) : positiveπ K n hn ≫ positiveDesc K n hn f hf=f := by
  simp [positiveπ,positiveDesc]
end ChainComplex

end

end OAI
