import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Excision.PureStateOrthogonalExtension

namespace OAI

noncomputable section


namespace DirectComparison
open Pureness CurrentMain PureStateExcision Filter Topology CStarAlgebra NuclearNorm
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "q" => normToTracial (A := A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U
local notation "L" => familyLimitTrace (fun τ : TracialState A => τ) U

 theorem finite_nuclear_identity_excision
    (hA : IsNuclear.{0,0} A) (hsimple : TopologicallySimple A) (hcmp : StrictComparison A)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (E F : N) (he : 0≤E) (hen : ‖E‖≤1) (hsmall : q E=0)
    (hec : ∀ a : A,Commute E (ι a))
    (hf : 0≤F) (hfn : ‖F‖≤1) (hfc : ∀ a : A,Commute F (ι a))
    (hprojection : IsStarProjection (q F))
    {t : ℝ} (ht : 0<t) (hlarge : ∀ s : ℕ → TracialState A,2*t ≤ ((L s).functional (q F)).re)
    {I : Type} [Fintype I] (a : I → selfAdjoint A) {ε : ℝ} (hε : 0<ε) :
    ∃ v : N,‖v‖≤2 ∧ F*v=v ∧ ‖star v*v-E‖<ε ∧
      ∀ i,‖star v*ι (a i : A)*v-ι (a i : A)*E‖<ε := by
  classical
  obtain ⟨φ,hφ1,hpure⟩ := exists_pure_positive_state (A := A)
  let b : Option I → selfAdjoint A | none => 1 | some i => a i
  let δ := min ε 1
  have hδ : 0<δ := lt_min hε zero_lt_one
  obtain ⟨R,hR⟩ := simple_nuclear_state_coefficient_approximation hA hsimple φ hφ1 b hδ
  obtain ⟨v,_hvq,hvF,hv⟩ := nuclear_list_excision U hsimple hcmp hfree E F he hen hsmall hec
    hf hfn hfc hprojection ht hlarge φ hφ1 hpure R
  have herr (i : Option I) : ‖star v*ι (b i : A)*v-ι (b i : A)*E‖<δ := by
    rw [hv,←sub_mul,←map_sub]
    calc
      _≤‖ι ((stateRowSum φ R (b i) : A)-(b i :A))‖*‖E‖ := norm_mul_le _ _
      _≤‖(stateRowSum φ R (b i) : A)-(b i :A)‖*1 :=
        mul_le_mul (NonUnitalStarAlgHom.norm_apply_le ι _) hen (norm_nonneg _) (norm_nonneg _)
      _=‖b i-stateRowSum φ R (b i)‖ := by rw [mul_one,norm_sub_rev]; rfl
      _≤‖b-fun i => stateRowSum φ R (b i)‖ := norm_le_pi_norm (b-fun i => stateRowSum φ R (b i)) i
      _<δ := hR
  have hsq : ‖star v*v-E‖<δ := by
    simpa only [b,selfAdjoint.val_one,normInclusion_one,mul_one,one_mul] using herr none
  have hnorm : ‖v‖≤2 := by
    have ht := norm_add_le (star v*v-E) E
    rw [sub_add_cancel] at ht
    have hvsq : ‖star v*v‖=‖v‖*‖v‖ := CStarRing.norm_star_mul_self
    have hδ1 : δ≤1 := min_le_right _ _
    nlinarith [norm_nonneg v]
  exact ⟨v,hnorm,hvF,hsq.trans_le (min_le_left _ _),
    fun i => (herr (some i)).trans_le (min_le_left _ _)⟩

end DirectComparison


namespace CStarExcision
variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma commutator_square_identity (s e a : A) :
    star (s*a-a*s)*(s*a-a*s) =
      star a*(star s*s-e)*a-star a*(star s*a*s-a*e)-
        (star s*star a*s-star a*e)*a+(star s*(star a*a)*s-(star a*a)*e) := by
  simp only [star_sub,star_mul]
  noncomm_ring

theorem commutator_sq_le (s e a : A) :
    ‖s*a-a*s‖^2 ≤
      ‖a‖^2*‖star s*s-e‖+‖a‖*‖star s*a*s-a*e‖+
      ‖star s*star a*s-star a*e‖*‖a‖+
      ‖star s*(star a*a)*s-(star a*a)*e‖ := by
  rw [pow_two,←CStarRing.norm_star_mul_self,commutator_square_identity]
  have h1 : ‖star a*(star s*s-e)*a‖≤‖a‖^2*‖star s*s-e‖ := by
    calc
      ‖star a*(star s*s-e)*a‖≤‖star a*(star s*s-e)‖*‖a‖ := norm_mul_le _ _
      _≤(‖star a‖*‖star s*s-e‖)*‖a‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _=‖a‖^2*‖star s*s-e‖ := by rw [norm_star]; ring
  have h2 : ‖star a*(star s*a*s-a*e)‖≤‖a‖*‖star s*a*s-a*e‖ := by
    simpa only [norm_star] using norm_mul_le (star a) (star s*a*s-a*e)
  have h3 := norm_mul_le (star s*star a*s-star a*e) a
  have ht := norm_add_le
    (star a*(star s*s-e)*a-star a*(star s*a*s-a*e)-(star s*star a*s-star a*e)*a)
    (star s*(star a*a)*s-(star a*a)*e)
  have hu := norm_sub_le
    (star a*(star s*s-e)*a-star a*(star s*a*s-a*e))
    ((star s*star a*s-star a*e)*a)
  have hv := norm_sub_le (star a*(star s*s-e)*a) (star a*(star s*a*s-a*e))
  linarith

theorem commutator_le_of_excision_errors (s e a : A) (ε : ℝ) (hε : 0≤ε)
    (h0 : ‖star s*s-e‖≤ε)
    (h1 : ‖star s*a*s-a*e‖≤ε)
    (h2 : ‖star s*star a*s-star a*e‖≤ε)
    (h3 : ‖star s*(star a*a)*s-(star a*a)*e‖≤ε) :
    ‖s*a-a*s‖≤(‖a‖+1)*Real.sqrt ε := by
  have hb := commutator_sq_le s e a
  have hn := norm_nonneg a
  have hsq : ‖s*a-a*s‖^2≤(‖a‖+1)^2*ε := by
    have h0' := mul_le_mul_of_nonneg_left h0 (sq_nonneg ‖a‖)
    have h1' := mul_le_mul_of_nonneg_left h1 hn
    have h2' := mul_le_mul_of_nonneg_right h2 hn
    nlinarith
  have hs := Real.sq_sqrt hε
  have hs0 := Real.sqrt_nonneg ε
  have hsn := norm_nonneg (s*a-a*s)
  have heq : ((‖a‖+1)*Real.sqrt ε)^2=(‖a‖+1)^2*ε := by
    rw [mul_pow,hs]
  have htarget : 0≤(‖a‖+1)*Real.sqrt ε := mul_nonneg (by linarith) hs0
  nlinarith

theorem commute_of_excision (s e a : A) (h0 : star s*s=e)
    (h1 : star s*a*s=a*e) (h2 : star s*star a*s=star a*e)
    (h3 : star s*(star a*a)*s=(star a*a)*e) : s*a=a*s := by
  apply sub_eq_zero.mp
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  rw [commutator_square_identity,h0,h1,h2,h3]
  noncomm_ring

end CStarExcision

end

end OAI
