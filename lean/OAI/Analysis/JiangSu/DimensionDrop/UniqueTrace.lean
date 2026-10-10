import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.ConnectingTraces

namespace OAI


noncomputable section
namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

variable {p q : ℕ} [NeZero p] [NeZero q]

lemma scalarDrop_norm_le (z : C(Interval,ℂ)) :
    ‖scalarDrop (p:=p) (q:=q) z‖≤‖z‖ := by
  change ‖scalarMatrixPath (I:=Fin p×Fin q) z‖≤‖z‖
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  change ‖z t • (1:TensorMat p q)‖≤‖z‖
  simpa only [norm_smul,norm_one,mul_one] using z.norm_coe_le_norm t

omit [NeZero p] [NeZero q] in
lemma scalarDrop_sub (z w : C(Interval,ℂ)) :
    scalarDrop (p:=p) (q:=q) (z-w)=scalarDrop z-scalarDrop w := by
  apply Subtype.ext
  exact scalarMatrixPath_sub z w

omit [NeZero p] [NeZero q] in
lemma scalarDrop_const (c : ℂ) :
    scalarDrop (p:=p) (q:=q) (ContinuousMap.const Interval c)=c • 1 := by
  apply Subtype.ext
  rfl

lemma dimensionDrop_trace_oscillation (τ : DimensionDrop p q →ₗ[ℂ] ℂ)
    (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
    (hbound : ∀ a, ‖τ a‖≤‖a‖) (f : DimensionDrop p q)
    (t : Interval) {ε : ℝ} (hε : 0≤ε)
    (hf : ∀ s, ‖normalizedTracePath f.val s-normalizedTracePath f.val t‖≤ε) :
    ‖τ f-normalizedTracePath f.val t‖≤ε := by
  have hb : ‖normalizedTracePath f.val-ContinuousMap.const Interval (normalizedTracePath f.val t)‖≤ε :=
    (ContinuousMap.norm_le _ hε).mpr hf
  calc
    _ = ‖τ (scalarDrop (normalizedTracePath f.val-ContinuousMap.const Interval (normalizedTracePath f.val t)))‖ := by
      rw [scalarDrop_sub,map_sub,scalarDrop_const,map_smul,h1,smul_eq_mul,mul_one]
      rw [dimensionDrop_trace_factorization τ hτ f]
    _ ≤ _ := hbound _
    _ ≤ _ := scalarDrop_norm_le _
    _ ≤ ε := hb

attribute [local instance] stagePNeZero stageQNeZero

lemma primeDropLimit_trace_stage_unique
    (τ σ : PrimeDropLimit →L[ℂ] ℂ)
    (hτ : ∀ a b,τ (a*b)=τ (b*a)) (hσ : ∀ a b,σ (a*b)=σ (b*a))
    (hτ1 : τ 1=1) (hσ1 : σ 1=1) (hτn : ‖τ‖≤1) (hσn : ‖σ‖≤1)
    (n : ℕ) (f : StageAlgebra n) :
    τ (concreteSystem.inclusion n f)=σ (concreteSystem.inclusion n f) := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k,hk⟩ := scalarIterates_oscillation n (normalizedTracePath f.val) (half_pos hε)
  let g : StageAlgebra (n+k) := concreteSystem.map (Nat.le_add_right n k) f
  have hg (s : Interval) :
      ‖normalizedTracePath g.val s-normalizedTracePath g.val leftEndpoint‖≤ε/2 := by
    dsimp [g]
    rw [normalizedTrace_sequence]
    exact (hk s leftEndpoint).le
  let T : StageAlgebra (n+k) →ₗ[ℂ] ℂ := τ.toLinearMap.comp (concreteSystem.inclusion (n+k)).toLinearMap
  let S : StageAlgebra (n+k) →ₗ[ℂ] ℂ := σ.toLinearMap.comp (concreteSystem.inclusion (n+k)).toLinearMap
  have hT : ∀ a b,T (a*b)=T (b*a) := by
    intro a b
    change τ (concreteSystem.inclusion (n+k) (a*b))=τ (concreteSystem.inclusion (n+k) (b*a))
    rw [map_mul (concreteSystem.inclusion (n+k)),map_mul (concreteSystem.inclusion (n+k)),hτ]
  have hS : ∀ a b,S (a*b)=S (b*a) := by
    intro a b
    change σ (concreteSystem.inclusion (n+k) (a*b))=σ (concreteSystem.inclusion (n+k) (b*a))
    rw [map_mul (concreteSystem.inclusion (n+k)),map_mul (concreteSystem.inclusion (n+k)),hσ]
  have hT1 : T 1=1 := by change τ (concreteSystem.inclusion (n+k) 1)=1; rw [map_one,hτ1]
  have hS1 : S 1=1 := by change σ (concreteSystem.inclusion (n+k) 1)=1; rw [map_one,hσ1]
  have hTb (a) : ‖T a‖≤‖a‖ := by
    calc _ ≤ ‖τ‖*‖concreteSystem.inclusion (n+k) a‖ := τ.le_opNorm _
         _ ≤ 1*‖concreteSystem.inclusion (n+k) a‖ := mul_le_mul_of_nonneg_right hτn (norm_nonneg _)
         _ = ‖a‖ := by rw [one_mul,concreteSystem.inclusion_norm]
  have hSb (a) : ‖S a‖≤‖a‖ := by
    calc _ ≤ ‖σ‖*‖concreteSystem.inclusion (n+k) a‖ := σ.le_opNorm _
         _ ≤ 1*‖concreteSystem.inclusion (n+k) a‖ := mul_le_mul_of_nonneg_right hσn (norm_nonneg _)
         _ = ‖a‖ := by rw [one_mul,concreteSystem.inclusion_norm]
  have ht := dimensionDrop_trace_oscillation T hT hT1 hTb g leftEndpoint (half_pos hε).le hg
  have hs := dimensionDrop_trace_oscillation S hS hS1 hSb g leftEndpoint (half_pos hε).le hg
  have hinc : concreteSystem.inclusion (n+k) g=concreteSystem.inclusion n f :=
    concreteSystem.inclusion_compatible _ _
  have ht' : T g=τ (concreteSystem.inclusion n f) := congrArg τ hinc
  have hs' : S g=σ (concreteSystem.inclusion n f) := congrArg σ hinc
  rw [ht'] at ht
  rw [hs'] at hs
  have hh := norm_sub_le (τ (concreteSystem.inclusion n f)-normalizedTracePath g.val leftEndpoint)
    (σ (concreteSystem.inclusion n f)-normalizedTracePath g.val leftEndpoint)
  simp only [sub_sub_sub_cancel_right] at hh
  linarith

theorem primeDropLimit_trace_unique
    (τ σ : PrimeDropLimit →L[ℂ] ℂ)
    (hτ : ∀ a b,τ (a*b)=τ (b*a)) (hσ : ∀ a b,σ (a*b)=σ (b*a))
    (hτ1 : τ 1=1) (hσ1 : σ 1=1) (hτn : ‖τ‖≤1) (hσn : ‖σ‖≤1) : τ=σ := by
  ext x
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n,f,hf⟩ := primeDropLimit_finite_stage x (half_pos hε)
  have he := primeDropLimit_trace_stage_unique τ σ hτ hσ hτ1 hσ1 hτn hσn n f
  have ht : ‖τ x-τ (concreteSystem.inclusion n f)‖<ε/2 := by
    rw [←map_sub]
    exact (τ.le_opNorm _).trans_lt ((mul_le_mul_of_nonneg_right hτn (norm_nonneg _)).trans_lt (by simpa using hf))
  have hs : ‖σ x-σ (concreteSystem.inclusion n f)‖<ε/2 := by
    rw [←map_sub]
    exact (σ.le_opNorm _).trans_lt ((mul_le_mul_of_nonneg_right hσn (norm_nonneg _)).trans_lt (by simpa using hf))
  have hh := norm_sub_le (τ x-τ (concreteSystem.inclusion n f)) (σ x-σ (concreteSystem.inclusion n f))
  rw [he,sub_sub_sub_cancel_right] at hh
  rw [he] at ht
  linarith

end JiangSuConstruction

end


noncomputable section
namespace SequentialCStar
open TraceCone Filter
open scoped Topology ENNReal

variable {C : ℕ → Type*} [∀ n, CStarAlgebra (C n)] [∀ n, Nontrivial (C n)]
variable (τ : ∀ n, C n →ₗ[ℂ] ℂ) (hτ : ∀ n a, ‖τ n a‖≤‖a‖)

lemma bounded_scalar_ultrafilter_tendsto {X : Type*} (U : Ultrafilter X) (f : X → ℂ)
    (M : ℝ) (hM : ∀ n, ‖f n‖≤M) :
    Tendsto f (U:Filter X) (𝓝 (limUnder (U:Filter X) f)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨r,_,hr⟩ := (isCompact_closedBall (0:ℂ) M).ultrafilter_le_nhds' (U.map f)
    (show Metric.closedBall (0:ℂ) M∈U.map f from by
      change {n | f n∈Metric.closedBall (0:ℂ) M}∈U
      exact Eventually.of_forall (fun n => by simpa using hM n))
  exact ⟨r,hr⟩

def familyTraceValue (x : BoundedFamilies C) : ℂ :=
  limUnder (hyperfilter ℕ:Filter ℕ) (fun n => τ n (x n))

include hτ in
omit [∀ n, Nontrivial (C n)] in
lemma familyTraceValue_tendsto (x : BoundedFamilies C) :
    Tendsto (fun n => τ n (x n)) (hyperfilter ℕ:Filter ℕ) (𝓝 (familyTraceValue τ x)) :=
  bounded_scalar_ultrafilter_tendsto _ _ ‖x‖ (fun n => (hτ n _).trans (BoundedFamilies.norm_coordinate_le x n))

def familyTraceLinear : BoundedFamilies C →ₗ[ℂ] ℂ where
  toFun := familyTraceValue τ
  map_add' x y := by
    apply tendsto_nhds_unique (familyTraceValue_tendsto τ hτ (x+y))
    simpa only [lp.coeFn_add,Pi.add_apply,map_add] using
      (familyTraceValue_tendsto τ hτ x).add (familyTraceValue_tendsto τ hτ y)
  map_smul' c x := by
    apply tendsto_nhds_unique (familyTraceValue_tendsto τ hτ (c • x))
    simpa only [lp.coeFn_smul,Pi.smul_apply,map_smul,smul_eq_mul,RingHom.id_apply] using
      (familyTraceValue_tendsto τ hτ x).const_mul c

lemma familyTraceLinear_norm (x : BoundedFamilies C) : ‖familyTraceLinear τ hτ x‖≤‖x‖ := by
  exact le_of_tendsto (familyTraceValue_tendsto τ hτ x).norm
    (Eventually.of_forall (fun n => (hτ n _).trans (BoundedFamilies.norm_coordinate_le x n)))

lemma familyTraceLinear_vanishing : BoundedFamilies.vanishing (A:=C)≤(familyTraceLinear τ hτ).ker := by
  intro x hx
  change familyTraceValue τ x=0
  have hz : Tendsto (fun n => τ n (x n)) (hyperfilter ℕ:Filter ℕ) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => hτ n _)
    exact hx.mono_left Nat.hyperfilter_le_atTop
  exact tendsto_nhds_unique (familyTraceValue_tendsto τ hτ x) hz

def quotientTraceLinear : FamilyQuotient C →ₗ[ℂ] ℂ :=
  (BoundedFamilies.vanishing (A:=C)).liftQ (familyTraceLinear τ hτ) (familyTraceLinear_vanishing τ hτ)

lemma quotientTraceLinear_mk (x : BoundedFamilies C) :
    quotientTraceLinear τ hτ (FamilyQuotient.mk x)=familyTraceLinear τ hτ x := rfl

lemma quotientTraceLinear_norm (x : FamilyQuotient C) : ‖quotientTraceLinear τ hτ x‖≤‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,rfl,ha⟩ := FamilyQuotient.exists_norm_mk_lt x hε
  exact (familyTraceLinear_norm τ hτ a).trans ha.le

def quotientTrace : FamilyQuotient C →L[ℂ] ℂ :=
  (quotientTraceLinear τ hτ).mkContinuous 1 (by simpa using quotientTraceLinear_norm τ hτ)

lemma quotientTrace_normalized (h1 : ∀ n,τ n 1=1) : quotientTrace τ hτ 1=1 := by
  change familyTraceValue τ (boundedOne C)=1
  apply tendsto_nhds_unique (familyTraceValue_tendsto τ hτ _)
  change Tendsto (fun n => τ n 1) (hyperfilter ℕ:Filter ℕ) (𝓝 1)
  simpa only [h1] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℂ)) (hyperfilter ℕ:Filter ℕ) (𝓝 1))

lemma quotientTrace_tracial (htr : ∀ n a b,τ n (a*b)=τ n (b*a))
    (a b : FamilyQuotient C) : quotientTrace τ hτ (a*b)=quotientTrace τ hτ (b*a) := by
  obtain ⟨a,rfl⟩ := FamilyQuotient.mk_surjective a
  obtain ⟨b,rfl⟩ := FamilyQuotient.mk_surjective b
  change familyTraceValue τ (a*b)=familyTraceValue τ (b*a)
  apply tendsto_nhds_unique (familyTraceValue_tendsto τ hτ (a*b))
  convert familyTraceValue_tendsto τ hτ (b*a) using 1
  funext n
  exact htr n _ _

variable (S : System C)

def limitTrace : S.Limit →L[ℂ] ℂ :=
  (quotientTrace τ hτ).comp (S.limitAlgebra.subtype.toLinearMap.mkContinuous 1 (by intro x; simp))

lemma limitTrace_normalized (h1 : ∀ n,τ n 1=1) : limitTrace τ hτ S 1=1 := quotientTrace_normalized τ hτ h1
lemma limitTrace_tracial (htr : ∀ n a b,τ n (a*b)=τ n (b*a))
    (a b : S.Limit) : limitTrace τ hτ S (a*b)=limitTrace τ hτ S (b*a) :=
  quotientTrace_tracial τ hτ htr a.val b.val
lemma limitTrace_norm : ‖limitTrace τ hτ S‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖quotientTraceLinear τ hτ x.val‖≤1*‖x.val‖
  simpa only [one_mul] using quotientTraceLinear_norm τ hτ x.val

end SequentialCStar

end

end OAI
