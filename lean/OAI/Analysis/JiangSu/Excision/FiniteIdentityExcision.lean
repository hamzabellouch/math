import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nuclearity.NuclearUnitization
import OAI.Analysis.JiangSu.Excision.OrthogonalExcision

namespace OAI

section

noncomputable section
namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma PureStateExcision Filter Topology CStarAlgebra NuclearNorm
open scoped ComplexOrder ENNReal

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "D" => Unitization ℂ N
local notation "B" => Unitization ℂ A
local notation "q" => NonunitalGamma.normToTracial (A := A) U
local notation "ρ" => unitizedNormInclusion (A := A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U
local notation "L" => familyLimitTrace (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ) U

 theorem finite_nuclear_identity_excision
    (hnuc : NuclearUnitization.IsNuclear.{0,0} A) (hsimple : NonunitalGamma.TopologicallySimple A)
    (hprojectionless : ∀ p : A,IsStarProjection p → p=0)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (E F : N) (he : 0≤E) (hen : ‖E‖≤1) (hsmall : q E=0)
    (hec : ∀ a : A,Commute E (ι a))
    (hf : 0≤F) (hfn : ‖F‖≤1) (hfc : ∀ a : A,Commute F (ι a))
    (hprojection : IsStarProjection (q F))
    {t : ℝ} (ht : 0<t) (hlarge : ∀ s : ℕ → NormalizedTrace A,2*t ≤ ((L s).functional (q F)).re)
    {I : Type} [Fintype I] (a : I → selfAdjoint A) {ε : ℝ} (hε : 0<ε) :
    ∃ v : N,‖v‖≤2 ∧ F*v=v ∧ ‖star v*v-E‖<ε ∧
      ∀ i,‖star v*ι (a i : A)*v-ι (a i : A)*E‖<ε := by
  classical
  let : TopologicalSpace.SeparableSpace B :=
    (Unitization.uniformEquivProd (𝕜 := ℂ) (A := A)).symm.surjective.denseRange.separableSpace
      (Unitization.uniformEquivProd (𝕜 := ℂ) (A := A)).symm.continuous
  obtain ⟨φ,hφ1,hpure,hfaith⟩ := exists_faithful_pure_unitized_state hsimple hprojectionless
  let b : Option I → selfAdjoint B
    | none => 1
    | some i => ⟨Unitization.inr (a i : A),(a i).property.map (Unitization.inrNonUnitalStarAlgHom ℂ A)⟩
  let δ := min ε 1
  have hδ : 0<δ := lt_min hε zero_lt_one
  obtain ⟨R,hR⟩ := nuclear_state_coefficient_approximation
    (NuclearUnitization.nuclear_unitization hnuc) φ hfaith b hδ
  obtain ⟨v,_hvq,hvF,hv⟩ := nuclear_list_excision U hsimple hprojectionless hcone hcmp hfree
    E F he hen hsmall hec hf hfn hfc hprojection ht hlarge φ hφ1 hpure R
  have herr (i : Option I) :
      ‖star (Unitization.inr v)*ρ (b i : B)*Unitization.inr v-ρ (b i : B)*Unitization.inr E‖<δ := by
    rw [hv,←sub_mul,←map_sub]
    calc
      _≤‖ρ ((stateRowSum φ R (b i) : B)-(b i :B))‖*‖(Unitization.inr E : D)‖ := norm_mul_le _ _
      _≤‖(stateRowSum φ R (b i) : B)-(b i :B)‖*1 :=
        mul_le_mul (NonUnitalStarAlgHom.norm_apply_le (ρ).toNonUnitalStarAlgHom _) (by simpa only [Unitization.norm_inr] using hen)
          (norm_nonneg _) (norm_nonneg _)
      _=‖b i-stateRowSum φ R (b i)‖ := by rw [mul_one,norm_sub_rev]; rfl
      _≤‖b-fun i => stateRowSum φ R (b i)‖ := norm_le_pi_norm (b-fun i => stateRowSum φ R (b i)) i
      _<δ := hR
  have hsq : ‖star v*v-E‖<δ := by
    have hh := herr none
    simpa only [b,selfAdjoint.val_one,map_one,mul_one,one_mul,←Unitization.inr_star,
      ←Unitization.inr_mul,←Unitization.inr_sub,Unitization.norm_inr] using hh
  have hnorm : ‖v‖≤2 := by
    have ht := norm_add_le (star v*v-E) E
    rw [sub_add_cancel] at ht
    have hvsq : ‖star v*v‖=‖v‖*‖v‖ := CStarRing.norm_star_mul_self
    have hδ1 : δ≤1 := min_le_right _ _
    nlinarith [norm_nonneg v]
  refine ⟨v,hnorm,hvF,hsq.trans_le (min_le_left _ _),fun i => ?_⟩
  have hh := (herr (some i)).trans_le (min_le_left _ _)
  simpa only [b,unitizedNormInclusion_inr,←Unitization.inr_star,←Unitization.inr_mul,
    ←Unitization.inr_sub,Unitization.norm_inr] using hh

end NonunitalSI

end
end

end OAI
