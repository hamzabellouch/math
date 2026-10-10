import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.QuotientSurjective
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixUnitsHom
import OAI.Analysis.JiangSu.CStarAlgebras.ContractionLift

namespace OAI

noncomputable section


namespace NonunitalGamma
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nonempty (NormalizedTrace A)]
local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)

structure ApproximateCentralMatrixUnits (m : ℕ) (F : Finset A) (ε : ℝ) where
  entry : Fin m → Fin m → A
  norm_entry : ∀ i j,‖entry i j‖≤1
  star_error : ∀ i j,familyTwoNorm T (Unitization.inr (star (entry i j)-entry j i))<ε
  mul_error : ∀ i j k l,familyTwoNorm T
    (Unitization.inr (entry i j*entry k l-(if j=k then entry i l else 0)))<ε
  unit_error : familyTwoNorm T ((∑ i,Unitization.inr (entry i i))-1)<ε
  commutator_error : ∀ i j a,a∈F → familyTwoNorm T
    (Unitization.inr (entry i j*a-a*entry i j))<ε

variable (U : Ultrafilter ℕ)
local notation "J" => familyNullIdeal T (U : Filter ℕ)
local notation "q" => Pureness.ClosedStarIdeal.quotientStarHom (familyNullIdeal T (U : Filter ℕ))
local notation "D" => FamilyUltrapower T U

lemma family_quotient_zero_of_domination
    (x : lp (fun _ : ℕ => Unitization ℂ A) ∞) (δ : ℕ → ℝ)
    (hδ : Tendsto δ (U : Filter ℕ) (𝓝 0))
    (hx : ∀ᶠ k in (U : Filter ℕ),familyTwoNorm T (x k)≤δ k) : q x=0 := by
  apply (familyQuotientMap_eq_zero T U x).mpr
  exact squeeze_zero' (Eventually.of_forall (fun k => familyTwoNorm_nonneg _ _)) hx hδ

variable {m : ℕ} (F : ℕ → Finset A) (δ : ℕ → ℝ)
  (v : (k : ℕ) → ApproximateCentralMatrixUnits m (F k) (δ k))

def modelSequenceEntry (i j : Fin m) : lp (fun _ : ℕ => Unitization ℂ A) ∞ :=
  ⟨fun k => Unitization.inr ((v k).entry i j),memℓp_infty_iff.mpr ⟨1,by
    rintro _ ⟨k,rfl⟩
    simpa only [Unitization.norm_inr] using (v k).norm_entry i j⟩⟩

omit [Nonempty (NormalizedTrace A)] in
@[simp] lemma modelSequenceEntry_apply (i j : Fin m) (k : ℕ) :
    modelSequenceEntry F δ v i j k=Unitization.inr ((v k).entry i j) := rfl

local notation "x" => modelSequenceEntry F δ v

lemma modelSequence_star (hδ : Tendsto δ (U : Filter ℕ) (𝓝 0)) (i j : Fin m) :
    star (q (x i j))=q (x j i) := by
  apply sub_eq_zero.mp
  rw [←map_star,←map_sub]
  apply family_quotient_zero_of_domination U _ δ hδ
  apply Eventually.of_forall
  intro k
  change familyTwoNorm T (star (x i j k)-x j i k)≤δ k
  rw [modelSequenceEntry_apply,modelSequenceEntry_apply]
  simpa only [Unitization.inr_star,Unitization.inr_sub] using ((v k).star_error i j).le

lemma modelSequence_mul (hδ : Tendsto δ (U : Filter ℕ) (𝓝 0)) (i j k l : Fin m) :
    q (x i j)*q (x k l)=if j=k then q (x i l) else 0 := by
  by_cases hjk : j=k
  · subst k
    simp only [ite_true]
    apply sub_eq_zero.mp
    rw [←map_mul,←map_sub]
    apply family_quotient_zero_of_domination U _ δ hδ
    apply Eventually.of_forall
    intro t
    change familyTwoNorm T (x i j t*x j l t-x i l t)≤δ t
    simp only [modelSequenceEntry_apply]
    simpa only [ite_true,Unitization.inr_mul,Unitization.inr_sub] using ((v t).mul_error i j j l).le
  · simp only [hjk,ite_false]
    rw [←map_mul]
    apply family_quotient_zero_of_domination U _ δ hδ
    apply Eventually.of_forall
    intro t
    change familyTwoNorm T (x i j t*x k l t)≤δ t
    simp only [modelSequenceEntry_apply]
    simpa only [hjk,ite_false,sub_zero,Unitization.inr_mul] using ((v t).mul_error i j k l).le

lemma modelSequence_sum (hδ : Tendsto δ (U : Filter ℕ) (𝓝 0)) : ∑ i,q (x i i)=1 := by
  apply sub_eq_zero.mp
  rw [←map_sum,←map_one q,←map_sub]
  apply family_quotient_zero_of_domination U _ δ hδ
  apply Eventually.of_forall
  intro k
  have he : ((∑ i,x i i)-1) k=(∑ i,Unitization.inr ((v k).entry i i))-1 := by
    change (∑ i,x i i) k-1=_
    simp only [lp.coeFn_sum,Finset.sum_apply]
    rfl
  rw [he]
  exact (v k).unit_error.le

lemma modelSequence_commute (hδ : Tendsto δ (U : Filter ℕ) (𝓝 0))
    (i j : Fin m) (a : A) (ha : ∀ᶠ k in (U : Filter ℕ),a∈F k) :
    Commute (q (x i j)) (familyUltrapowerMap T U (Unitization.inr a)) := by
  apply commute_of_null_sequence T U (x i j) (Unitization.inr a)
  apply squeeze_zero' (Eventually.of_forall (fun k => familyTwoNorm_nonneg _ _)) _ hδ
  filter_upwards [ha] with k hk
  simp only [modelSequenceEntry_apply]
  exact le_of_lt (by simpa only [Unitization.inr_mul,Unitization.inr_sub] using (v k).commutator_error i j a hk)

theorem central_matrix_of_finite_models [TopologicalSpace.SeparableSpace A]
    (hfree : (U : Filter ℕ)≤atTop) (m : ℕ)
    (hmodel : ∀ (F : Finset A) (ε : ℝ),0<ε → Nonempty (ApproximateCentralMatrixUnits m F ε)) :
    ∃ η : CStarMatrix (Fin m) (Fin m) ℂ →⋆ₐ[ℂ] D,
      ∀ M (a : A),Commute (η M) (familyUltrapowerMap T U (Unitization.inr a)) := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  let F (k : ℕ) : Finset A := (Finset.range k).image a
  let δ (k : ℕ) : ℝ := 1/((k:ℝ)+1)
  have hδpos k : 0<δ k := by dsimp [δ]; positivity
  let v (k : ℕ) := Classical.choice (hmodel (F k) (δ k) (hδpos k))
  have hδ : Tendsto δ (U : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hfree
  let e : ConcreteMatrixUnits.System (Fin m) D :=
    ⟨fun i j => q (modelSequenceEntry F δ v i j),modelSequence_mul U F δ v hδ,
      modelSequence_star U F δ v hδ,modelSequence_sum U F δ v hδ⟩
  refine ⟨e.hom,?_⟩
  intro M b
  apply e.hom_commute
  intro i j
  have hdense (n : ℕ) : Commute (e.entry i j) (familyUltrapowerMap T U (Unitization.inr (a n))) := by
    apply modelSequence_commute U F δ v hδ
    have hev : ∀ᶠ k in (U : Filter ℕ),n<k := (eventually_gt_atTop n).filter_mono hfree
    filter_upwards [hev] with k hk
    exact Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr hk,rfl⟩
  let ι : A →⋆ₙₐ[ℂ] D := (familyUltrapowerMap T U).toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hι : Continuous ι := map_continuous ι
  have he := ha.equalizer (continuous_const.mul hι) (hι.mul continuous_const) (funext fun n => (hdense n).eq)
  exact congrFun he b

end NonunitalGamma


namespace NonunitalGamma
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)]
variable (U : Ultrafilter ℕ)
local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)
local notation "D" => FamilyUltrapower T U
local notation "q" => Pureness.ClosedStarIdeal.quotientStarHom (familyNullIdeal T (U : Filter ℕ))

lemma contractive_sequence_lift (hfree : (U : Filter ℕ)≤atTop) (b : D) (hb : ‖b‖≤1) :
    ∃ x : lp (fun _ : ℕ => A) ∞,‖x‖≤1 ∧ q (boundedInr (A := A) x)=b := by
  obtain ⟨y,hy,hyn⟩ := CStarLift.exists_contraction q
    (familyNullIdeal T (U : Filter ℕ)).quotientMap_surjective hb
  obtain ⟨x,hxn,hx⟩ := sequenceQuotientMap_bounded_lift U hfree y
  exact ⟨x,hxn.trans hyn,hx.trans hy⟩

omit [CompactSpace (NormalizedTrace A)] in
lemma family_quotient_zero_eventually (x : lp (fun _ : ℕ => Unitization ℂ A) ∞)
    (hx : q x=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k in (U : Filter ℕ),familyTwoNorm T (x k)<ε :=
  ((familyQuotientMap_eq_zero T U x).mp hx).eventually_lt_const hε

omit [CompactSpace (NormalizedTrace A)] in
lemma star_lifts_eventually {m : ℕ} (x : Fin m → Fin m → lp (fun _ : ℕ => A) ∞)
    (i j : Fin m)
    (hs : star (q (boundedInr (A := A) (x i j)))=q (boundedInr (A := A) (x j i))) {ε : ℝ} (hε : 0<ε) : ∀ᶠ k in (U : Filter ℕ),
    familyTwoNorm T (Unitization.inr (star (x i j k)-x j i k))<ε := by
  have hz : q (star (boundedInr (A := A) (x i j))-boundedInr (A := A) (x j i))=0 := by
    rw [map_sub,map_star,hs,sub_self]
  have he := family_quotient_zero_eventually U _ hz hε
  simpa only [lp.coeFn_sub,Pi.sub_apply,lp.coeFn_star,Pi.star_apply,boundedInr_apply,
    ←Unitization.inr_star,←Unitization.inr_sub] using he

omit [CompactSpace (NormalizedTrace A)] in
lemma mul_lifts_eventually {m : ℕ} (x : Fin m → Fin m → lp (fun _ : ℕ => A) ∞)
    (i j k l : Fin m)
    (hm : q (boundedInr (A := A) (x i j))*q (boundedInr (A := A) (x k l))=
      if j=k then q (boundedInr (A := A) (x i l)) else 0) {ε : ℝ} (hε : 0<ε) : ∀ᶠ t in (U : Filter ℕ),
    familyTwoNorm T (Unitization.inr (x i j t*x k l t-(if j=k then x i l t else 0)))<ε := by
  let b := if j=k then boundedInr (A := A) (x i l) else 0
  have hb : q b=if j=k then q (boundedInr (A := A) (x i l)) else 0 := by
    by_cases hindex : j=k <;> simp [b,hindex]
  have hz : q (boundedInr (A := A) (x i j)*boundedInr (A := A) (x k l)-b)=0 := by
    rw [map_sub,map_mul,hm,hb,sub_self]
  have he := family_quotient_zero_eventually U _ hz hε
  filter_upwards [he] with t ht
  by_cases hjk : j=k
  · simpa only [b,hjk,ite_true,lp.coeFn_sub,Pi.sub_apply,lp.infty_coeFn_mul,Pi.mul_apply,
    boundedInr_apply,←Unitization.inr_mul,←Unitization.inr_sub] using ht
  · simpa only [b,hjk,ite_false,sub_zero,lp.coeFn_sub,Pi.sub_apply,lp.infty_coeFn_mul,Pi.mul_apply,
    boundedInr_apply,←Unitization.inr_mul,Unitization.inr_zero] using ht

omit [CompactSpace (NormalizedTrace A)] in
lemma unit_lifts_eventually {m : ℕ} (x : Fin m → Fin m → lp (fun _ : ℕ => A) ∞)
    (hu : ∑ i,q (boundedInr (A := A) (x i i))=1) {ε : ℝ} (hε : 0<ε) : ∀ᶠ k in (U : Filter ℕ),
    familyTwoNorm T ((∑ i,Unitization.inr (x i i k))-1)<ε := by
  have hz : q ((∑ i,boundedInr (A := A) (x i i))-1)=0 := by rw [map_sub,map_sum,map_one,hu,sub_self]
  have he := family_quotient_zero_eventually U _ hz hε
  simpa only [lp.coeFn_sub,Pi.sub_apply,lp.coeFn_sum,Finset.sum_apply,boundedInr_apply,
    lp.infty_coeFn_one,Pi.one_apply] using he

omit [CompactSpace (NormalizedTrace A)] in
lemma commutator_lifts_eventually {m : ℕ} (x : Fin m → Fin m → lp (fun _ : ℕ => A) ∞)
    (i j : Fin m) (a : A)
    (hc : Commute (q (boundedInr (A := A) (x i j))) (familyUltrapowerMap T U (Unitization.inr a))) {ε : ℝ} (hε : 0<ε) : ∀ᶠ k in (U : Filter ℕ),
    familyTwoNorm T (Unitization.inr (x i j k*a-a*x i j k))<ε := by
  let c : lp (fun _ : ℕ => Unitization ℂ A) ∞ := boundedFamilyConstant (Unitization.inr a)
  have hz : q (boundedInr (A := A) (x i j)*c-c*boundedInr (A := A) (x i j))=0 := by
    rw [map_sub,map_mul,map_mul]
    exact sub_eq_zero.mpr (hc).eq
  have he := family_quotient_zero_eventually U _ hz hε
  filter_upwards [he] with k hk
  simpa only [lp.coeFn_sub,Pi.sub_apply,lp.infty_coeFn_mul,Pi.mul_apply,
    boundedInr_apply,c,boundedFamilyConstant_apply,←Unitization.inr_mul,←Unitization.inr_sub] using hk

omit [CompactSpace (NormalizedTrace A)] in
lemma finite_models_of_matrix_lifts {m : ℕ} (x : Fin m → Fin m → lp (fun _ : ℕ => A) ∞)
    (hn : ∀ i j,‖x i j‖≤1)
    (hs : ∀ i j,star (q (boundedInr (A := A) (x i j)))=q (boundedInr (A := A) (x j i)))
    (hm : ∀ i j k l,q (boundedInr (A := A) (x i j))*q (boundedInr (A := A) (x k l))=
      if j=k then q (boundedInr (A := A) (x i l)) else 0)
    (hu : ∑ i,q (boundedInr (A := A) (x i i))=1)
    (hc : ∀ i j a,Commute (q (boundedInr (A := A) (x i j))) (familyUltrapowerMap T U (Unitization.inr a)))
    (F : Finset A) {ε : ℝ} (hε : 0<ε) : Nonempty (ApproximateCentralMatrixUnits m F ε) := by

  classical
  have hsall := (eventually_all.mpr fun i => eventually_all.mpr fun j => star_lifts_eventually U x i j (hs i j) hε)
  have hmall := (eventually_all.mpr fun i => eventually_all.mpr fun j =>
    eventually_all.mpr fun k => eventually_all.mpr fun l => mul_lifts_eventually U x i j k l (hm i j k l) hε)
  have hcall := (eventually_all.mpr fun i => eventually_all.mpr fun j =>
    eventually_all.mpr fun (a : F) => commutator_lifts_eventually U x i j (a:A) (hc i j a) hε)
  obtain ⟨k,hks,hkm,hku,hkc⟩ := (hsall.and (hmall.and ((unit_lifts_eventually U x hu hε).and hcall))).exists
  refine ⟨⟨fun i j => x i j k,fun i j => (lp.norm_apply_le_norm ENNReal.top_ne_zero (x i j) k).trans (hn i j),
    hks,hkm,hku,?_⟩⟩
  intro i j a ha
  exact hkc i j ⟨a,ha⟩

theorem finite_models_of_central_matrix (hfree : (U : Filter ℕ)≤atTop) {m : ℕ}
    (η : CStarMatrix (Fin m) (Fin m) ℂ →⋆ₐ[ℂ] D)
    (hη : ∀ M (a : A),Commute (η M) (familyUltrapowerMap T U (Unitization.inr a)))
    (F : Finset A) {ε : ℝ} (hε : 0<ε) : Nonempty (ApproximateCentralMatrixUnits m F ε) := by
  classical
  have hn (i j : Fin m) : ‖η (ConcreteMatrixUnits.unit i j)‖≤1 :=
    (NonUnitalStarAlgHom.norm_apply_le η _).trans (ConcreteMatrixUnits.unit_norm_le_one i j)
  choose x hxn hx using fun i j => contractive_sequence_lift U hfree
    (η (ConcreteMatrixUnits.unit i j)) (hn i j)
  apply finite_models_of_matrix_lifts U x hxn _ _ _ _ F hε
  · intro i j
    rw [hx,hx,←map_star,ConcreteMatrixUnits.unit_star]
  · intro i j k l
    rw [hx,hx,←map_mul,ConcreteMatrixUnits.unit_mul]
    by_cases hindex : j=k <;> simp [hindex,hx]
  · simp only [hx,←map_sum,ConcreteMatrixUnits.unit_sum_diag,map_one]
  · intro i j a
    rw [hx]
    exact hη _ a

end NonunitalGamma

end

end OAI
