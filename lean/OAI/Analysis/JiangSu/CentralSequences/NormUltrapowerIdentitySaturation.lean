import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Excision.FiniteNuclearIdentityExcision

namespace OAI

section

noncomputable section
namespace NormUltra
open Filter Topology CStarAlgebra DirectComparison
open scoped ComplexOrder ComplexStarModule ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [TopologicalSpace.SeparableSpace A] (U : Ultrafilter ℕ)
local notation "N" => QuotientAlgebra (fun _ : ℕ => A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U

omit [PartialOrder A] [StarOrderedRing A] in
 theorem identity_excision_saturation (hfree : (U : Filter ℕ) ≤ atTop)
    (E F : N) (hen : ‖E‖≤1)
    (hsupply : ∀ (m : ℕ) (a : Fin (m+1) → selfAdjoint A) (ε : ℝ),0<ε →
      ∃ v : N,‖v‖≤2 ∧ F*v=v ∧ ‖star v*v-E‖<ε ∧
        ∀ i,‖star v*ι (a i : A)*v-ι (a i : A)*E‖<ε) :
    ∃ z : N,‖z‖≤1 ∧ star z*z=E ∧ F*z=z ∧
      (∀ a : A,star z*ι a*z=ι a*E) ∧ (∀ a : A,Commute z (ι a)) := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq (selfAdjoint A)
  obtain ⟨e,heq⟩ := QuotientAlgebra.mk_surjective E
  obtain ⟨f,hfq⟩ := QuotientAlgebra.mk_surjective F
  let g : ℕ → ℕ → A → ℝ
    | 0,k,z => ‖star z*z-e k‖
    | 1,k,z => ‖f k*z-z‖
    | j+2,k,z => ‖star z*(a j : A)*z-(a j : A)*e k‖
  have hg (j k : ℕ) (z : A) : 0≤g j k z := by
    rcases j with _|(_|j) <;> exact norm_nonneg _
  have hs (m : ℕ) (ε : ℝ) (hε : 0<ε) : ∀ᶠ k in (U : Filter ℕ),
      ∃ z : A,‖z‖≤3 ∧ ∀ j ≤ m,g j k z<ε := by
    obtain ⟨v,hvn,hvF,hve,hva⟩ := hsupply m (fun i => a i) (ε/2) (by positivity)
    obtain ⟨x,hx,hxn⟩ := QuotientAlgebra.exists_norm_mk_lt v zero_lt_one
    have hxe : ‖QuotientAlgebra.mk U (star x*x-e)‖<ε := by
      rw [QuotientAlgebra.mk_sub,QuotientAlgebra.mk_mul,QuotientAlgebra.mk_star,hx,heq]
      exact hve.trans (by linarith)
    have hxf : ‖QuotientAlgebra.mk U (f*x-x)‖<ε := by
      rw [QuotientAlgebra.mk_sub,QuotientAlgebra.mk_mul,hfq,hx,hvF,sub_self,norm_zero]
      exact hε
    have hxa (i : Fin (m+1)) :
        ‖QuotientAlgebra.mk U (star x*boundedDiagonal (a i : A)*x-boundedDiagonal (a i : A)*e)‖<ε := by
      change ‖star (QuotientAlgebra.mk U x)*ι (a i : A)*QuotientAlgebra.mk U x-
        ι (a i : A)*QuotientAlgebra.mk U e‖<ε
      rw [hx,heq]
      exact (hva i).trans (by linarith)
    have h0 := NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ hxe
    have h1 := NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ hxf
    have h2 : ∀ᶠ k in (U : Filter ℕ),∀ i : Fin (m+1),
        ‖star (x k)*(a i : A)*x k-(a i : A)*e k‖<ε := by
      exact Filter.eventually_all.2 (fun i =>
        NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ (hxa i))
    filter_upwards [h0,h1,h2] with k h0 h1 h2
    refine ⟨x k,((NormUltra.BoundedFamilies.norm_coordinate_le x k).trans hxn.le).trans (by linarith),?_⟩
    intro j hj
    rcases j with _|(_|j)
    · exact h0
    · exact h1
    · exact h2 ⟨j,by omega⟩
  obtain ⟨x,_hxn,hx⟩ := bounded_epsilon_test U hfree 3 (by norm_num) g hg hs
  let z := QuotientAlgebra.mk U x
  have hze : star z*z=E := by
    rw [←heq]
    exact (QuotientAlgebra.mk_eq_mk_iff (star x*x) e).mpr (hx 0)
  have hzf : F*z=z := by
    rw [←hfq]
    exact (QuotientAlgebra.mk_eq_mk_iff (f*x) x).mpr (hx 1)
  have hza (i : ℕ) : star z*ι (a i : A)*z=ι (a i : A)*E := by
    rw [←heq]
    exact (QuotientAlgebra.mk_eq_mk_iff (star x*boundedDiagonal (a i : A)*x)
      (boundedDiagonal (a i : A)*e)).mpr (hx (i+2))
  have hzn : ‖z‖≤1 := by
    have hsq : ‖star z*z‖=‖z‖*‖z‖ := CStarRing.norm_star_mul_self
    rw [hze] at hsq
    nlinarith [norm_nonneg z]
  have hc1 : Continuous (fun b : selfAdjoint A => star z*ι (b:A)*z) := by fun_prop
  have hc2 : Continuous (fun b : selfAdjoint A => ι (b:A)*E) := by fun_prop
  have hsa (b : selfAdjoint A) : star z*ι (b:A)*z=ι (b:A)*E :=
    congrFun (ha.equalizer hc1 hc2 (funext hza)) b
  have hz (b : A) : star z*ι b*z=ι b*E := by
    conv_lhs => rw [←realPart_add_I_smul_imaginaryPart b]
    rw [map_add,map_smul,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,hsa,hsa]
    rw [←smul_mul_assoc,←add_mul,←map_smul,←map_add,realPart_add_I_smul_imaginaryPart]
  refine ⟨z,hzn,hze,hzf,hz,fun b => ?_⟩
  apply CStarExcision.commute_of_excision z E (ι b) hze (hz b)
  · simpa only [map_star] using hz (star b)
  · simpa only [map_mul,map_star] using hz (star b*b)

end NormUltra

end
end

end OAI
