import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerBasic
import OAI.Analysis.JiangSu.Nonunital.LimitTraceRestriction

namespace OAI

noncomputable section


namespace NonunitalGamma
open Pureness CurrentMain Filter Topology NormUltra
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nonempty (NormalizedTrace A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

lemma normNull_uniformNull (x : lp (fun _ : ℕ => A) ∞)
    (hx : x ∈ NormUltra.BoundedFamilies.vanishing (A := fun _ : ℕ => A) U) :
    sequenceQuotientMap (A := A) U x=0 := by
  rw [sequenceQuotientMap_apply,familyQuotientMap_eq_zero]
  change Tendsto (fun n => familyTwoNorm T (Unitization.inr (x n))) (U : Filter ℕ) (𝓝 0)
  apply squeeze_zero (fun n => familyTwoNorm_nonneg T _) (fun n => ?_) hx
  simpa only [Unitization.norm_inr] using familyTwoNorm_le_norm T (Unitization.inr (x n))

def normToTracial : N →⋆ₙₐ[ℂ] FamilyUltrapower T U where
  toFun := Quotient.lift (sequenceQuotientMap (A := A) U) (by
    intro x y h
    change (NormUltra.BoundedFamilies.vanishing (A := fun _ : ℕ => A) U).quotientRel x y at h
    rw [Submodule.quotientRel_def] at h
    have he := normNull_uniformNull U (x-y) h
    rw [map_sub,sub_eq_zero] at he
    exact he)
  map_zero' := map_zero (sequenceQuotientMap (A := A) U)
  map_add' x y := by
    obtain ⟨x,rfl⟩ := NormUltra.QuotientAlgebra.mk_surjective x
    obtain ⟨y,rfl⟩ := NormUltra.QuotientAlgebra.mk_surjective y
    exact map_add (sequenceQuotientMap (A := A) U) x y
  map_mul' x y := by
    obtain ⟨x,rfl⟩ := NormUltra.QuotientAlgebra.mk_surjective x
    obtain ⟨y,rfl⟩ := NormUltra.QuotientAlgebra.mk_surjective y
    exact map_mul (sequenceQuotientMap (A := A) U) x y
  map_smul' c x := by
    obtain ⟨x,rfl⟩ := NormUltra.QuotientAlgebra.mk_surjective x
    exact map_smul (sequenceQuotientMap (A := A) U) c x
  map_star' x := by
    obtain ⟨x,rfl⟩ := NormUltra.QuotientAlgebra.mk_surjective x
    exact map_star (sequenceQuotientMap (A := A) U) x

@[simp] lemma normToTracial_mk (x : lp (fun _ : ℕ => A) ∞) :
    normToTracial U (NormUltra.QuotientAlgebra.mk U x)=sequenceQuotientMap (A := A) U x := rfl

lemma normToTracial_surjective [CompactSpace (NormalizedTrace A)]
    (hfree : (U : Filter ℕ) ≤ atTop) : Function.Surjective (normToTracial (A := A) U) := by
  intro x
  obtain ⟨y,rfl⟩ := sequenceQuotientMap_surjective U hfree x
  exact ⟨NormUltra.QuotientAlgebra.mk U y,rfl⟩

def boundedConstant : A →⋆ₙₐ[ℂ] lp (fun _ : ℕ => A) ∞ where
  toFun a := ⟨fun _ => a,memℓp_infty ⟨‖a‖,by simp⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

omit [PartialOrder A] [StarOrderedRing A] [Nonempty (NormalizedTrace A)] in
@[simp] lemma boundedConstant_apply (a : A) (n : ℕ) : boundedConstant (A := A) a n=a := rfl

def normInclusion : A →⋆ₙₐ[ℂ] N := (NormUltra.QuotientAlgebra.mkHom (A := fun _ : ℕ => A) (U := U)).comp boundedConstant

@[simp] lemma normToTracial_inclusion (a : A) :
    normToTracial U (normInclusion U a)=quotientInclusion U a := rfl

end NonunitalGamma


namespace Quasicentral
open Filter Topology
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def conjugate (u : unitary A) : A →L[ℝ] A :=
  ((Unitary.mulLeft ℝ A u).trans (Unitary.mulRight ℝ (star u))).toContinuousLinearEquiv.toContinuousLinearMap

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma conjugate_apply (u : unitary A) (a : A) :
    conjugate u a=(u:A)*a*star (u:A) := rfl
lemma conjugate_nonneg (u : unitary A) {a : A} (ha : 0 ≤ a) : 0 ≤ conjugate u a :=
  star_right_conjugate_nonneg ha _
omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_conjugate (u : unitary A) (a : A) : ‖conjugate u a‖=‖a‖ := by
  exact ((Unitary.mulLeft ℝ A u).trans (Unitary.mulRight ℝ (star u))).norm_map a

variable (K : Finset (unitary A))
def expansionConstant : ℝ := 2*((K.card:ℝ)+1)
omit [PartialOrder A] [StarOrderedRing A] in
lemma expansionConstant_pos : 0 < expansionConstant K := by unfold expansionConstant; positivity
omit [PartialOrder A] [StarOrderedRing A] in
lemma expansionConstant_ne_zero : expansionConstant K≠0 := ne_of_gt (expansionConstant_pos K)
def averageMap : A →L[ℝ] A := (expansionConstant K)⁻¹ • ∑ u ∈ K, conjugate u
omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma averageMap_apply (a : A) :
    averageMap K a=(expansionConstant K)⁻¹ • ∑ u ∈ K, conjugate u a := by simp [averageMap]
lemma averageMap_nonneg {a : A} (ha : 0 ≤ a) : 0 ≤ averageMap K a := by
  rw [averageMap_apply]
  exact smul_nonneg (inv_nonneg.mpr (expansionConstant_pos K).le)
    (Finset.sum_nonneg fun u _ => conjugate_nonneg u ha)
omit [PartialOrder A] [StarOrderedRing A] in
lemma averageMap_norm_le (a : A) : ‖averageMap K a‖ ≤ (1/2:ℝ)*‖a‖ := by
  rw [averageMap_apply,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (expansionConstant_pos K).le)]
  calc
    _ ≤ (expansionConstant K)⁻¹ * ∑ u ∈ K, ‖conjugate u a‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (expansionConstant_pos K).le)
    _ = ((K.card:ℝ)/expansionConstant K)*‖a‖ := by simp only [norm_conjugate,Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ (1/2:ℝ)*‖a‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg a)
      apply (div_le_iff₀ (expansionConstant_pos K)).mpr
      unfold expansionConstant
      nlinarith

lemma iterate_nonneg {h₀ : A} (hpos : 0 ≤ h₀) (n : ℕ) :
    0 ≤ ((averageMap K)^[n]) h₀ := by
  induction n with
  | zero => exact hpos
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact averageMap_nonneg K ih
omit [PartialOrder A] [StarOrderedRing A] in
lemma iterate_norm_le (h₀ : A) (n : ℕ) :
    ‖((averageMap K)^[n]) h₀‖ ≤ (1/2:ℝ)^n*‖h₀‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ (1/2:ℝ)*‖((averageMap K)^[n]) h₀‖ := averageMap_norm_le K _
      _ ≤ (1/2:ℝ)*((1/2:ℝ)^n*‖h₀‖) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1/2:ℝ)^(n+1)*‖h₀‖ := by rw [pow_succ]; ring
omit [PartialOrder A] [StarOrderedRing A] in
lemma iterate_summable (h₀ : A) : Summable (fun n => ((averageMap K)^[n]) h₀) := by
  apply Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_right ‖h₀‖)
  exact iterate_norm_le K h₀

theorem exists_invariant_domination (J : Submodule ℝ A) (hJ : IsClosed (J : Set A))
    (hJK : ∀ u ∈ K, ∀ a ∈ J, conjugate u a ∈ J)
    (h₀ : A) (hh₀ : h₀ ∈ J) (hpos : 0 ≤ h₀) :
    ∃ h : A, h ∈ J ∧ 0 ≤ h ∧ h₀ ≤ h ∧
      ∀ u ∈ K, conjugate u h ≤ expansionConstant K • h := by
  let f := fun n => ((averageMap K)^[n]) h₀
  have hf : Summable f := iterate_summable K h₀
  let h := ∑' n, f n
  have hfp (n : ℕ) : 0 ≤ f n := iterate_nonneg K hpos n
  have hfm (n : ℕ) : f n ∈ J := by
    induction n with
    | zero => exact hh₀
    | succ n ih =>
      change ((averageMap K)^[n+1]) h₀ ∈ J
      rw [Function.iterate_succ_apply']
      change averageMap K (f n) ∈ J
      rw [averageMap_apply]
      exact J.smul_mem _ (J.sum_mem fun u hu => hJK u hu (f n) ih)
  have hh : h ∈ J := hJ.mem_of_tendsto hf.hasSum.tendsto_sum_nat
    (Eventually.of_forall fun n => J.sum_mem fun i _ => hfm i)
  have hp : 0 ≤ h := tsum_nonneg hfp
  have he : h₀+averageMap K h=h := by
    rw [(averageMap K).map_tsum hf]
    simpa only [h,f,Function.iterate_succ_apply',Function.iterate_zero,Function.id_def] using hf.tsum_eq_zero_add.symm
  have hQ : averageMap K h ≤ h := (le_add_of_nonneg_left hpos).trans_eq he
  refine ⟨h,hh,hp,?_,?_⟩
  · exact (le_add_of_nonneg_right (averageMap_nonneg K hp)).trans_eq he
  · intro u hu
    have hs : conjugate u h ≤ ∑ v ∈ K, conjugate v h :=
      Finset.single_le_sum (fun v _ => conjugate_nonneg v hp) hu
    have hqs := smul_le_smul_of_nonneg_left hQ (expansionConstant_pos K).le
    rw [averageMap_apply,smul_smul,mul_inv_cancel₀ (expansionConstant_ne_zero K),one_smul] at hqs
    exact hs.trans hqs

end Quasicentral

end

end OAI
