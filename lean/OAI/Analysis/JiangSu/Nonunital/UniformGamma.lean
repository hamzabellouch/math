import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.FamilyDyadicApproximation
import OAI.Analysis.JiangSu.Nonunital.QuotientSurjective

namespace OAI

noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain Filter FamilyComparison DirectComparison
open scoped Topology ComplexOrder

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
local notation "τ" => (fun t : NormalizedTrace A => NormalizedTrace.unitized t)

variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A] [CompactSpace (NormalizedTrace A)]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
variable (hsimple : NonunitalGamma.TopologicallySimple A) (hproj : Projectionless A)
variable (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
variable (hnuc : Pureness.IsNuclear (Unitization ℂ A))
local notation "D" => FamilyUltrapower τ U
local notation "Λ" => familyLimitTrace τ U

include hfree hsimple hproj hcone hcmp hnuc in

theorem uniform_gamma_partition_of_nuclear_unitization (m : ℕ) (hm : 0 < m) :
    ∃ p : Fin m → D, (∀ i, IsStarProjection (p i)) ∧
      Pairwise (fun i j => p i*p j=0) ∧ (∑ i, p i)=1 ∧
      ∀ i (a : A), Commute (p i) (familyUltrapowerMap τ U (Unitization.inr a)) ∧
      ∀ s : ℕ → NormalizedTrace A, (Λ s).functional (familyUltrapowerMap τ U (Unitization.inr a)*p i)=
        (1/(m:ℂ))*(Λ s).functional (familyUltrapowerMap τ U (Unitization.inr a)) := by
  classical
  obtain ⟨x,hx⟩ := TopologicalSpace.exists_dense_seq A
  let ι := (familyUltrapowerMap τ U).toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hι : Continuous ι := by
    apply LipschitzWith.continuous (K := 1)
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [dist_eq_norm,←map_sub,NNReal.coe_one,one_mul] using
      NonUnitalStarAlgHom.norm_apply_le ι (a-b)
  let S := Set.range (fun n => ι (x n))
  have hsupply : SpectralProjectionSupply Λ := projection_supply U hfree hsimple hproj hcone hcmp
  obtain ⟨p,hp,horth,hsum,hpt⟩ := FamilyComparison.comparison_relative_partition τ U hfree hsupply hnuc
    S (Set.countable_range _) m hm (IsStarProjection.one _) (fun a _ => Commute.one_left a)
  refine ⟨p,fun i => (hp i).1,horth,hsum,?_⟩
  intro i a
  have hcomm : (fun b : A => p i*ι b)=(fun b : A => ι b*p i) :=
    hx.equalizer (continuous_const.mul hι) (hι.mul continuous_const)
      (funext fun n => (hpt i (ι (x n)) (Set.mem_range_self n)).1.eq)
  refine ⟨congrFun hcomm a,?_⟩
  intro s
  have hσ : Continuous (Λ s).functional := map_continuous (Λ s).functional
  have he : (fun b : A => (Λ s).functional (p i*ι b))=
      (fun b : A => (1/(m:ℂ))*(Λ s).functional (ι b)) :=
    hx.equalizer (hσ.comp (continuous_const.mul hι)) (continuous_const.mul (hσ.comp hι))
      (funext fun n => by
        change (Λ s).functional (p i*ι (x n))=(1/(m:ℂ))*(Λ s).functional (ι (x n))
        simpa only [one_mul] using (hpt i (ι (x n)) (Set.mem_range_self n)).2 s)
  rw [←(Λ s).tracial]
  exact congrFun he a

include hfree hsimple hproj hcone hcmp hnuc in

theorem uniform_gamma_of_nuclear_unitization : UniformGamma A U := by
  intro m hm
  obtain ⟨p,hp,_,hsum,hpt⟩ := uniform_gamma_partition_of_nuclear_unitization U hfree hsimple hproj hcone hcmp hnuc m hm
  exact ⟨p,hp,hsum,fun i a => (hpt i a).1,fun i a s => (hpt i a).2 s⟩

end NonunitalGamma

namespace NonunitalGamma
open TraceCone Pureness CurrentMain Filter
open scoped ComplexOrder

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma StablyProjectionless.projectionless (h : StablyProjectionless A) : Projectionless A := by
  intro p hp
  have hz := h (matrixLimitStage 1 (scalarOne p)) ((hp.map scalarOne).map (matrixLimitStage 1))
  have hm : scalarOne p=0 := (matrixLimitStage_isometry 1).injective (by simpa only [map_zero] using hz)
  exact congrArg (fun M : FinMatrix A 1 => M 0 0) hm

variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable [CompactSpace (NormalizedTrace A)]

theorem stably_projectionless_uniform_gamma_of_nuclear_unitization
    (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
    (hsimple : NonunitalGamma.TopologicallySimple A) (hstable : StablyProjectionless A)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (hnuc : Pureness.IsNuclear (Unitization ℂ A)) : UniformGamma A U :=
  uniform_gamma_of_nuclear_unitization U hfree hsimple hstable.projectionless hcone hcmp hnuc

end NonunitalGamma

end

end OAI
