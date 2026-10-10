import Mathlib

namespace OAI

noncomputable section
namespace BogomolovPop

def proEllKernel (ell : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Subgroup G :=
  ⨅ (H : OpenNormalSubgroup G) (_ : IsPGroup ell (G ⧸ H.toSubgroup)), H.toSubgroup

instance proEllKernel_normal (ell : ℕ) (G : Type*) [Group G] [TopologicalSpace G] :
    (proEllKernel ell G).Normal := by
  unfold proEllKernel
  exact Subgroup.normal_iInf_normal fun H =>
    Subgroup.normal_iInf_normal fun _ => H.isNormal'

abbrev ProEll (ell : ℕ) (F : Type*) [Field F] :=
  Field.absoluteGaloisGroup F ⧸ proEllKernel ell (Field.absoluteGaloisGroup F)

def closedGammaThree (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Subgroup G :=
  (⁅(commutator G).topologicalClosure, (⊤ : Subgroup G)⁆).topologicalClosure

instance closedGammaThree_normal (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : (closedGammaThree G).Normal := by
  unfold closedGammaThree
  exact Subgroup.is_normal_topologicalClosure _

abbrev PiA (ell : ℕ) (F : Type*) [Field F] := TopologicalAbelianization (ProEll ell F)

abbrev PiC (ell : ℕ) (F : Type*) [Field F] := ProEll ell F ⧸ closedGammaThree (ProEll ell F)

theorem closedGammaThree_le (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : closedGammaThree G ≤ (commutator G).topologicalClosure := by
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.commutator_le_left _ _)
    (Subgroup.isClosed_topologicalClosure _)

def centralProjection (ell : ℕ) (F : Type*) [Field F] : PiC ell F →* PiA ell F :=
  QuotientGroup.map _ _ (MonoidHom.id _) (closedGammaThree_le _)

abbrev Delta (ell : ℕ) (F : Type*) [Field F] := (centralProjection ell F).ker

def sourceCommutator {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

def abelianLift (ell : ℕ) (F : Type*) [Field F] (x : PiA ell F) : ProEll ell F :=
  Quotient.out x

theorem abelianLift_spec (ell : ℕ) (F : Type*) [Field F] (x : PiA ell F) :
    QuotientGroup.mk' _ (abelianLift ell F x) = x := Quotient.out_eq x

def bracket (ell : ℕ) (F : Type*) [Field F] (x y : PiA ell F) : Delta ell F :=
  ⟨QuotientGroup.mk' _ (sourceCommutator (abelianLift ell F x) (abelianLift ell F y)), by
    change centralProjection ell F _ = 1
    simp only [centralProjection, sourceCommutator, map_mul, map_inv]
    simp [mul_comm]⟩

def BracketCompatible {ell : ℕ} {K L : Type*} [Field K] [Field L]
    (φ : PiA ell L ≃ₜ* PiA ell K) : Prop :=
  ∃ ψ : Delta ell L ≃ₜ* Delta ell K,
    ∀ σ τ, ψ (bracket ell L σ τ) = bracket ell K (φ σ) (φ τ)

abbrev PerfectFieldClosure (F : Type*) [Field F] := perfectClosure F (AlgebraicClosure F)

def PerfectIsom (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] :=
  { α : PerfectFieldClosure K ≃+* PerfectFieldClosure L //
    α '' Set.range (algebraMap k (PerfectFieldClosure K)) =
      Set.range (algebraMap l (PerfectFieldClosure L)) }

def FrobeniusStep {k K l L : Type*} [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] (α β : PerfectIsom k K l L) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p : L) = 0 ∧
    ∀ x : PerfectFieldClosure K, β.1 x = (α.1 x) ^ p

abbrev IsomF (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] :=
  Quotient (Relation.EqvGen.setoid (FrobeniusStep (k := k) (K := K) (l := l) (L := L)))

abbrev IsomC (ell : ℕ) (K L : Type*) [Field K] [Field L] :=
  {φ : PiA ell L ≃ₜ* PiA ell K // BracketCompatible φ}

def ScalarStep {ell : ℕ} [Fact ell.Prime] {K L : Type*} [Field K] [Field L]
    (φ χ : IsomC ell K L) : Prop :=
  ∃ u : (PadicInt ell)ˣ, ∀ x : PiA ell L,
    Filter.Tendsto (fun n : ℕ => (φ.1 x) ^ PadicInt.appr (u : PadicInt ell) n)
      Filter.atTop (nhds (χ.1 x))

abbrev IsomCUnits (ell : ℕ) [Fact ell.Prime] (K L : Type*) [Field K] [Field L] :=
  Quotient (Relation.EqvGen.setoid (ScalarStep (ell := ell) (K := K) (L := L)))

def absoluteToPiA (ell : ℕ) (F : Type*) [Field F] :
    Field.absoluteGaloisGroup F →* PiA ell F :=
  (QuotientGroup.mk' _).comp (QuotientGroup.mk' _)

def absoluteAction {F : Type*} [Field F] (σ : Field.absoluteGaloisGroup F)
    (x : AlgebraicClosure F) : AlgebraicClosure F := by
  change AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F at σ
  exact σ x

def PullbackGraph {ell : ℕ} {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) (φ : IsomC ell K L) : Prop :=
  ∃ β : AlgebraicClosure K ≃+* AlgebraicClosure L,
    (∀ x : PerfectFieldClosure K, β x = ((α.1 x : PerfectFieldClosure L) :
      AlgebraicClosure L)) ∧
    ∀ σ : Field.absoluteGaloisGroup L, ∃ τ : Field.absoluteGaloisGroup K,
      (∀ x : AlgebraicClosure K,
        β (absoluteAction τ x) = absoluteAction σ (β x)) ∧
      φ.1 (absoluteToPiA ell L σ) = absoluteToPiA ell K τ

def PhiGraph {ell : ℕ} [Fact ell.Prime] {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (a : IsomF k K l L) (b : IsomCUnits ell K L) : Prop :=
  ∃ α : PerfectIsom k K l L, ∃ φ : IsomC ell K L,
    Quotient.mk _ α = a ∧ Quotient.mk _ φ = b ∧ PullbackGraph α φ

theorem main_graph_injective (ell : ℕ) [Fact ell.Prime]
    (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [IsAlgClosed k] [IsAlgClosed l] [Algebra k K] [Algebra l L]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType l L]
    (hk : (ell : k) ≠ 0) (hl : (ell : l) ≠ 0)
    (hK : 2 ≤ Algebra.trdeg k K) (hL : 2 ≤ Algebra.trdeg l L) :
    ∀ (a a' : IsomF k K l L) (b : IsomCUnits ell K L),
      PhiGraph a b → PhiGraph a' b → a = a'  := by
  sorry

end BogomolovPop

end

end OAI
