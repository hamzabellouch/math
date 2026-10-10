import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropRelations2

namespace OAI

section

noncomputable section
namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma Filter Topology NormUltra
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "C" => normCentralizer (A := A) U
local notation "Fω" => CentralSequenceAlgebra (A := A) U
local notation "π" => centralSequenceQuotient (A := A) U
local notation "mk" => NormUltra.QuotientAlgebra.mk U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U

omit [PartialOrder A] [StarOrderedRing A] in
 theorem central_bounded_representative (z : Fω) (hz : ‖z‖≤1) :
    ∃ (x : lp (fun _ : ℕ => A) ∞) (X : C),
      (∀ n,‖x n‖≤2) ∧ mk x=(X:N) ∧ π X=z ∧
      ∀ a : A,Tendsto (fun n => ‖x n*a-a*x n‖) (U : Filter ℕ) (𝓝 0) := by
  obtain ⟨X,hX,hXn⟩ := NonunitalClosedIdeal.QuotientAlgebra.exists_norm_mk_lt
    (normAnnihilator U) z (by norm_num : (0:ℝ)<1/2)
  obtain ⟨x,hx,hxn⟩ := NormUltra.QuotientAlgebra.exists_norm_mk_lt (X:N) (by norm_num : (0:ℝ)<1/2)
  refine ⟨x,X,fun n => ?_,hx,hX,fun a => ?_⟩
  · have hh := BoundedFamilies.norm_coordinate_le x n
    change ‖x‖<‖X‖+1/2 at hxn
    linarith
  · apply (NormUltra.QuotientAlgebra.mk_eq_mk_iff (x*boundedConstant (A := A) a) (boundedConstant (A := A) a*x)).mp
    rw [NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_mul,hx]
    exact X.property a

omit [PartialOrder A] [StarOrderedRing A] in
 theorem quotient_eq_iff_two_sided_errors
    (x y : lp (fun _ : ℕ => A) ∞) (X Y : C) (hx : mk x=(X:N)) (hy : mk y=(Y:N)) :
    π X=π Y ↔ ∀ a : A,
      Tendsto (fun n => ‖(x n-y n)*a‖) (U : Filter ℕ) (𝓝 0) ∧
      Tendsto (fun n => ‖a*(x n-y n)‖) (U : Filter ℕ) (𝓝 0) := by
  constructor
  · intro h a
    have hJ := (NonunitalClosedIdeal.QuotientAlgebra.mk_eq_mk_iff (normAnnihilator U) X Y).mp h
    have hJa := hJ a
    constructor
    · have he : mk ((x-y)*boundedConstant (A := A) a)=mk 0 := by
        rw [NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_sub,hx,hy,
          NormUltra.QuotientAlgebra.mk_zero]
        exact hJa.1
      have hv := (NormUltra.QuotientAlgebra.mk_eq_mk_iff ((x-y)*boundedConstant (A := A) a) 0).mp he
      simpa only [NormUltra.BoundedFamilies.mem_vanishing, sub_zero, lp.infty_coeFn_mul, lp.coeFn_sub, Pi.mul_apply, Pi.sub_apply, boundedConstant_apply] using hv
    · have he : mk (boundedConstant (A := A) a*(x-y))=mk 0 := by
        rw [NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_sub,hx,hy,
          NormUltra.QuotientAlgebra.mk_zero]
        exact hJa.2
      have hv := (NormUltra.QuotientAlgebra.mk_eq_mk_iff (boundedConstant (A := A) a*(x-y)) 0).mp he
      simpa only [NormUltra.BoundedFamilies.mem_vanishing, sub_zero, lp.infty_coeFn_mul, lp.coeFn_sub, Pi.mul_apply, Pi.sub_apply, boundedConstant_apply] using hv
  · intro h
    apply (NonunitalClosedIdeal.QuotientAlgebra.mk_eq_mk_iff (normAnnihilator U) X Y).mpr
    intro a
    constructor
    · have hv : (x-y)*boundedConstant (A := A) a-0∈BoundedFamilies.vanishing (A := fun _ : ℕ => A) U := by
        simpa only [NormUltra.BoundedFamilies.mem_vanishing, sub_zero, lp.infty_coeFn_mul, lp.coeFn_sub, Pi.mul_apply, Pi.sub_apply, boundedConstant_apply] using (h a).1
      have he := (NormUltra.QuotientAlgebra.mk_eq_mk_iff ((x-y)*boundedConstant (A := A) a) 0).mpr hv
      rw [NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_sub,hx,hy,
        NormUltra.QuotientAlgebra.mk_zero] at he
      exact he
    · have hv : boundedConstant (A := A) a*(x-y)-0∈BoundedFamilies.vanishing (A := fun _ : ℕ => A) U := by
        simpa only [NormUltra.BoundedFamilies.mem_vanishing, sub_zero, lp.infty_coeFn_mul, lp.coeFn_sub, Pi.mul_apply, Pi.sub_apply, boundedConstant_apply] using (h a).2
      have he := (NormUltra.QuotientAlgebra.mk_eq_mk_iff (boundedConstant (A := A) a*(x-y)) 0).mpr hv
      rw [NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_sub,hx,hy,
        NormUltra.QuotientAlgebra.mk_zero] at he
      exact he

variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)]
variable [TopologicalSpace.SeparableSpace A] [Fact ((U : Filter ℕ) ≤ atTop)]

 theorem comparison_dimension_drop_bounded_witness
    (hnuc : NuclearUnitization.IsNuclear.{0,0} A) (hsimple : NonunitalGamma.TopologicallySimple A)
    (hstable : StablyProjectionless A)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (n : ℕ) (hn : 0<n) :
    ∃ (φ : CStarMatrix (Fin n) (Fin n) ℂ →CP Fω)
      (x : lp (fun _ : ℕ => A) ∞) (X : C),
      (∀ M,‖φ M‖≤‖M‖) ∧ (∀ M P,φ M*φ P=φ (M*P)*φ 1) ∧
      (∀ k,‖x k‖≤2) ∧ mk x=(X:N) ∧
      (∀ a : A,Tendsto (fun k => ‖x k*a-a*x k‖) (U : Filter ℕ) (𝓝 0)) ∧
      star (π X)*π X=1-φ 1 ∧ φ (CompletelyPositiveOperations.matrixUnit ⟨0,hn⟩ ⟨0,hn⟩)*π X=π X ∧
      centralSequenceToTracial U (φ 1)=1 := by
  obtain ⟨φ,z,hφn,hφrel,hzn,hze,hzf,hφ1⟩ := comparison_dimension_drop_relations U
    hnuc hsimple hstable hcone hcmp n hn
  obtain ⟨x,X,hxn,hx,hX,hxc⟩ := central_bounded_representative U z hzn
  exact ⟨φ,x,X,hφn,hφrel,hxn,hx,hxc,by rwa [hX],by rwa [hX],hφ1⟩

end NonunitalSI

end
end

end OAI
