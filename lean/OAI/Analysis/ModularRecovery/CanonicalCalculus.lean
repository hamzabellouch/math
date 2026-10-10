import OAI.Analysis.ModularRecovery.CanonicalPolar

namespace OAI

/-! Interval functional calculus, logarithmic pullback, and nondegeneracy. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate ComplexOrder
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev UnitInterval := Icc (0:ℝ) 1

def intervalCoordinate : C(UnitInterval,ℂ) := ⟨fun r => (r.1:ℂ), by fun_prop⟩
def intervalWeight : C(UnitInterval,ℂ) := intervalCoordinate*(1-intervalCoordinate)

namespace CyclicSeparatingData

lemma spectrum_A_interval (S : CyclicSeparatingData H) {z : ℂ} (hz : z ∈ spectrum ℂ S.A) :
    0 ≤ z.re ∧ z.re ≤ 1 := by
  have : Nontrivial H := ⟨⟨S.xi,0,fun h => by simpa [h] using S.norm_xi⟩⟩
  exact ⟨(Complex.nonneg_iff.mp (spectrum_nonneg_of_nonneg S.A_positive hz)).1,
    (Complex.re_le_norm z).trans ((spectrum.norm_le_norm_of_mem hz).trans S.A_norm_le)⟩

def intervalCalculus (S : CyclicSeparatingData H) : C(UnitInterval,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (cfcHom (R := ℂ) S.A_selfAdjoint.isStarNormal).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ
      ⟨fun z => ⟨z.1.re,S.spectrum_A_interval z.2⟩, by fun_prop⟩)

lemma intervalCalculus_continuous (S : CyclicSeparatingData H) : Continuous S.intervalCalculus := by
  exact (cfcHom_continuous S.A_selfAdjoint.isStarNormal).comp
    (ContinuousMap.continuous_precomp _)

lemma intervalCalculus_coordinate (S : CyclicSeparatingData H) :
    S.intervalCalculus intervalCoordinate = S.A := by
  unfold intervalCalculus
  change cfcHom S.A_selfAdjoint.isStarNormal _ = _
  convert cfcHom_id (R := ℂ) S.A_selfAdjoint.isStarNormal using 2
  ext z
  exact (S.A_selfAdjoint.mem_spectrum_eq_re z.2).symm

lemma intervalCalculus_weight (S : CyclicSeparatingData H) :
    S.intervalCalculus intervalWeight = S.K := by
  simp only [intervalWeight,map_mul,map_sub,map_one,S.intervalCalculus_coordinate,S.K_eq_mul]

lemma intervalCalculus_nonneg (S : CyclicSeparatingData H) {f : C(UnitInterval,ℂ)} (hf : 0 ≤ f) :
    0 ≤ S.intervalCalculus f := by
  simpa only [map_zero] using map_rel S.intervalCalculus hf

lemma intervalCalculus_norm_le (S : CyclicSeparatingData H) (f : C(UnitInterval,ℂ)) :
    ‖S.intervalCalculus f‖ ≤ ‖f‖ := NonUnitalStarAlgHom.norm_apply_le S.intervalCalculus f

end CyclicSeparatingData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate ComplexOrder
namespace BoundedRecovery

def intervalLogit (r : ℝ) : ℝ := Real.log ((1-r)/r)

lemma intervalLogit_continuousAt {r : ℝ} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    ContinuousAt intervalLogit r := by
  apply ContinuousAt.log
  · exact (continuous_const.sub continuous_id).continuousAt.div continuousAt_id h0
  · exact div_ne_zero (sub_ne_zero.mpr (Ne.symm h1)) h0

lemma norm_weightedPullback_le (f : BoundedContinuousFunction ℝ ℂ) (r : UnitInterval) :
    ‖((r.1:ℂ)*(1-r.1))*f (intervalLogit r.1)‖ ≤ ‖intervalWeight r‖*‖f‖ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)

lemma weightedPullback_continuous (f : BoundedContinuousFunction ℝ ℂ) :
    Continuous (fun r : UnitInterval => ((r.1:ℂ)*(1-r.1))*f (intervalLogit r.1)) := by
  rw [continuous_iff_continuousAt]
  intro r
  by_cases h : r.1 = 0 ∨ r.1 = 1
  · have hw : intervalWeight r = 0 := by
      rcases h with h|h <;> simp [intervalWeight,intervalCoordinate,h]
    have hv : ((r.1:ℂ)*(1-r.1))*f (intervalLogit r.1)=0 := by
      change intervalWeight r * _ = 0
      rw [hw,zero_mul]
    change Tendsto _ (𝓝 r) (𝓝 _)
    dsimp only
    rw [hv]
    apply squeeze_zero_norm (norm_weightedPullback_le f)
    have ht := intervalWeight.continuous.norm.continuousAt.tendsto (x := r)
    simpa only [hw,norm_zero,zero_mul] using ht.mul_const ‖f‖
  · push Not at h
    exact (by fun_prop : ContinuousAt (fun r : UnitInterval => (r.1:ℂ)*(1-r.1)) r).mul
      (f.continuous.continuousAt.comp ((intervalLogit_continuousAt h.1 h.2).comp
        continuous_subtype_val.continuousAt))

def weightedPullback (f : BoundedContinuousFunction ℝ ℂ) : C(UnitInterval,ℂ) :=
  ⟨_,weightedPullback_continuous f⟩

@[simp] lemma weightedPullback_apply (f : BoundedContinuousFunction ℝ ℂ) (r : UnitInterval) :
    weightedPullback f r = intervalWeight r*f (intervalLogit r.1) := rfl

lemma weightedPullback_one : weightedPullback 1 = intervalWeight := by ext r; simp
lemma weightedPullback_zero : weightedPullback 0 = 0 := by ext r; simp
lemma weightedPullback_add (f g : BoundedContinuousFunction ℝ ℂ) :
    weightedPullback (f+g)=weightedPullback f+weightedPullback g := by ext r; simp [mul_add]
lemma weightedPullback_smul (c : ℂ) (f : BoundedContinuousFunction ℝ ℂ) :
    weightedPullback (c • f)=c • weightedPullback f := by ext r; simp [mul_left_comm]
lemma weightedPullback_mul (f g : BoundedContinuousFunction ℝ ℂ) :
    weightedPullback (f*g)*intervalWeight=weightedPullback f*weightedPullback g := by
  ext r
  simp only [ContinuousMap.mul_apply,weightedPullback_apply,BoundedContinuousFunction.mul_apply]
  ring
lemma weightedPullback_star (f : BoundedContinuousFunction ℝ ℂ) :
    weightedPullback (star f)=star (weightedPullback f) := by
  ext r
  simp [intervalWeight,intervalCoordinate,star_mul]
  ring

lemma complex_star_mul_self_le_of_norm_le {a b : ℂ} (h : ‖a‖ ≤ ‖b‖) : star a*a ≤ star b*b := by
  simp only [Complex.star_def,RCLike.conj_mul]
  norm_cast
  exact pow_le_pow_left₀ (norm_nonneg _) h _

lemma weightedPullback_square_le (f : BoundedContinuousFunction ℝ ℂ) :
    star (weightedPullback f)*weightedPullback f ≤
      star ((‖f‖:ℂ) • intervalWeight)*((‖f‖:ℂ) • intervalWeight) := by
  intro r
  apply complex_star_mul_self_le_of_norm_le
  simp only [ContinuousMap.smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg f)]
  change ‖((r.1:ℂ)*(1-r.1))*f (intervalLogit r.1)‖ ≤ _
  simpa only [mul_comm] using norm_weightedPullback_le f r

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma norm_apply_le_of_star_mul_self_le (a b : H →L[ℂ] H) (hab : star a*a ≤ star b*b) (x : H) :
    ‖a x‖ ≤ ‖b x‖ := by
  have hh := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hab)).re_inner_nonneg_right x
  change 0 ≤ (inner ℂ x (star b (b x)-star a (a x))).re at hh
  simp only [inner_sub_right,Complex.sub_re,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right] at hh
  change 0 ≤ RCLike.re (inner ℂ (b x) (b x))-RCLike.re (inner ℂ (a x) (a x)) at hh
  rw [← norm_sq_eq_re_inner,← norm_sq_eq_re_inner] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (sub_nonneg.mp hh)

namespace CyclicSeparatingData

def weightedCalculus (S : CyclicSeparatingData H) (f : BoundedContinuousFunction ℝ ℂ) : H →L[ℂ] H :=
  S.intervalCalculus (weightedPullback f)

lemma norm_weightedCalculus_apply_le (S : CyclicSeparatingData H) (f : BoundedContinuousFunction ℝ ℂ)
    (x : H) : ‖S.weightedCalculus f x‖ ≤ ‖f‖*‖S.K x‖ := by
  have hh := map_rel S.intervalCalculus (weightedPullback_square_le f)
  simp only [map_mul,map_star,map_smul,S.intervalCalculus_weight] at hh
  have he := norm_apply_le_of_star_mul_self_le _ _ hh x
  change ‖S.weightedCalculus f x‖ ≤ ‖((‖f‖:ℂ) • S.K) x‖ at he
  simpa only [smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg f)] using he

end CyclicSeparatingData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace CyclicSeparatingData

def logCalculusOp (S : CyclicSeparatingData H) (f : BoundedContinuousFunction ℝ ℂ) : H →L[ℂ] H :=
  (S.weightedCalculus f).toLinearMap.extendOfNorm S.K.toLinearMap

lemma logCalculusOp_K (S : CyclicSeparatingData H) (f : BoundedContinuousFunction ℝ ℂ) (x : H) :
    S.logCalculusOp f (S.K x)=S.weightedCalculus f x := by
  exact LinearMap.extendOfNorm_eq S.K_dense ⟨‖f‖,fun y => by
    change ‖S.weightedCalculus f y‖ ≤ ‖f‖*‖S.K y‖
    exact S.norm_weightedCalculus_apply_le f y⟩ x

lemma logCalculusOp_mul_K (S : CyclicSeparatingData H) (f : BoundedContinuousFunction ℝ ℂ) :
    S.logCalculusOp f*S.K=S.weightedCalculus f := by ext x; exact S.logCalculusOp_K f x

lemma norm_logCalculusOp_le (S : CyclicSeparatingData H) (f : BoundedContinuousFunction ℝ ℂ) :
    ‖S.logCalculusOp f‖ ≤ ‖f‖ := by
  exact LinearMap.opNorm_extendOfNorm_le S.K_dense (norm_nonneg f) (fun y => by
    change ‖S.weightedCalculus f y‖ ≤ ‖f‖*‖S.K y‖
    exact S.norm_weightedCalculus_apply_le f y)

lemma ext_of_mul_K (S : CyclicSeparatingData H) {a b : H →L[ℂ] H} (hab : a*S.K=b*S.K) : a=b := by
  ext x
  refine S.K_dense.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) x
  rintro _ ⟨y,rfl⟩
  exact congrArg (fun c : H →L[ℂ] H => c y) hab

lemma intervalCalculus_commute (S : CyclicSeparatingData H) (f g : C(UnitInterval,ℂ)) :
    Commute (S.intervalCalculus f) (S.intervalCalculus g) :=
  (Commute.all f g).map S.intervalCalculus

lemma logCalculusOp_commute_interval (S : CyclicSeparatingData H) (f : BoundedContinuousFunction ℝ ℂ)
    (g : C(UnitInterval,ℂ)) : Commute (S.logCalculusOp f) (S.intervalCalculus g) := by
  apply S.ext_of_mul_K
  have hK : Commute (S.intervalCalculus g) S.K :=
    S.intervalCalculus_weight ▸ S.intervalCalculus_commute g intervalWeight
  rw [mul_assoc,hK.eq,← mul_assoc,S.logCalculusOp_mul_K,mul_assoc,S.logCalculusOp_mul_K]
  exact (S.intervalCalculus_commute (weightedPullback f) g).eq

lemma logCalculusOp_commute_K (S : CyclicSeparatingData H) (f : BoundedContinuousFunction ℝ ℂ) :
    Commute (S.logCalculusOp f) S.K :=
  S.intervalCalculus_weight ▸ S.logCalculusOp_commute_interval f intervalWeight

lemma logCalculusOp_one (S : CyclicSeparatingData H) : S.logCalculusOp 1=1 := by
  apply S.ext_of_mul_K
  rw [S.logCalculusOp_mul_K,one_mul]
  exact congrArg S.intervalCalculus weightedPullback_one |>.trans S.intervalCalculus_weight

lemma logCalculusOp_zero (S : CyclicSeparatingData H) : S.logCalculusOp 0=0 := by
  apply S.ext_of_mul_K
  rw [S.logCalculusOp_mul_K,zero_mul]
  change S.intervalCalculus (weightedPullback 0)=0
  rw [weightedPullback_zero,map_zero]

lemma logCalculusOp_add (S : CyclicSeparatingData H) (f g : BoundedContinuousFunction ℝ ℂ) :
    S.logCalculusOp (f+g)=S.logCalculusOp f+S.logCalculusOp g := by
  apply S.ext_of_mul_K
  rw [S.logCalculusOp_mul_K,add_mul,S.logCalculusOp_mul_K,S.logCalculusOp_mul_K]
  exact congrArg S.intervalCalculus (weightedPullback_add f g) |>.trans (map_add _ _ _)

lemma logCalculusOp_smul (S : CyclicSeparatingData H) (c : ℂ) (f : BoundedContinuousFunction ℝ ℂ) :
    S.logCalculusOp (c • f)=c • S.logCalculusOp f := by
  apply S.ext_of_mul_K
  rw [S.logCalculusOp_mul_K,smul_mul_assoc,S.logCalculusOp_mul_K]
  exact congrArg S.intervalCalculus (weightedPullback_smul c f) |>.trans (map_smul _ _ _)

lemma logCalculusOp_mul (S : CyclicSeparatingData H) (f g : BoundedContinuousFunction ℝ ℂ) :
    S.logCalculusOp (f*g)=S.logCalculusOp f*S.logCalculusOp g := by
  apply S.ext_of_mul_K
  apply S.ext_of_mul_K
  rw [S.logCalculusOp_mul_K,mul_assoc _ (S.logCalculusOp g),S.logCalculusOp_mul_K]
  change S.intervalCalculus (weightedPullback (f*g))*S.K =
    S.logCalculusOp f*S.intervalCalculus (weightedPullback g)*S.K
  rw [(S.logCalculusOp_commute_interval f (weightedPullback g)).eq,mul_assoc,S.logCalculusOp_mul_K]
  change S.intervalCalculus (weightedPullback (f*g))*S.K=
    S.intervalCalculus (weightedPullback g)*S.intervalCalculus (weightedPullback f)
  rw [← S.intervalCalculus_weight,← map_mul,← map_mul,weightedPullback_mul,mul_comm]

lemma K_selfAdjoint (S : CyclicSeparatingData H) : IsSelfAdjoint S.K :=
  (ContinuousLinearMap.nonneg_iff_isPositive.mp S.K_positive).isSelfAdjoint

lemma logCalculusOp_star (S : CyclicSeparatingData H) (f : BoundedContinuousFunction ℝ ℂ) :
    S.logCalculusOp (star f)=star (S.logCalculusOp f) := by
  apply S.ext_of_mul_K
  rw [S.logCalculusOp_mul_K]
  change S.intervalCalculus (weightedPullback (star f))=star (S.logCalculusOp f)*S.K
  rw [weightedPullback_star,map_star]
  change star (S.weightedCalculus f)=_
  rw [← S.logCalculusOp_mul_K,(S.logCalculusOp_commute_K f).eq,star_mul,S.K_selfAdjoint.star_eq]

def logCalculus (S : CyclicSeparatingData H) : BoundedContinuousFunction ℝ ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := S.logCalculusOp
  map_zero' := S.logCalculusOp_zero
  map_one' := S.logCalculusOp_one
  map_add' := S.logCalculusOp_add
  map_mul' := S.logCalculusOp_mul
  commutes' c := by
    have he := S.logCalculusOp_smul c 1
    simpa only [Algebra.algebraMap_eq_smul_one,S.logCalculusOp_one] using he
  map_star' := S.logCalculusOp_star

lemma logCalculus_weighted (S : CyclicSeparatingData H) (f : BoundedContinuousFunction ℝ ℂ) (x : H) :
    S.logCalculus f (S.K x) = S.intervalCalculus (weightedPullback f) x := S.logCalculusOp_K f x

lemma logCalculus_eq_interval (S : CyclicSeparatingData H) (f : BoundedContinuousFunction ℝ ℂ)
    (g : C(UnitInterval,ℂ)) (hfg : weightedPullback f=intervalWeight*g) :
    S.logCalculus f=S.intervalCalculus g := by
  apply S.ext_of_mul_K
  change S.logCalculusOp f*S.K=_
  rw [S.logCalculusOp_mul_K]
  change S.intervalCalculus (weightedPullback f)=_
  rw [hfg,map_mul,(S.intervalCalculus_commute intervalWeight g).eq,S.intervalCalculus_weight]

end CyclicSeparatingData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

lemma intervalWeight_norm (r : UnitInterval) : ‖intervalWeight r‖=r.1*(1-r.1) := by
  change ‖(r.1:ℂ)*(1-r.1)‖ = _
  rw [norm_mul]
  have h : (1:ℂ)-(r.1:ℂ)=((1-r.1:ℝ):ℂ) := by push_cast; rfl
  rw [h,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg r.2.1,abs_of_nonneg (sub_nonneg.mpr r.2.2)]

lemma bandMultiplier_hasCompactSupport {s rho : ℝ} (hrho : 0 < rho) :
    HasCompactSupport (bandMultiplier s rho : ℝ → ℂ) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro u hu
  exact bandMultiplier_zero hrho hu

lemma exists_compact_weight_approx {eps : ℝ} (heps : 0 < eps) :
    ∃ f : BoundedContinuousFunction ℝ ℂ,
      HasCompactSupport (f : ℝ → ℂ) ∧ ‖weightedPullback f-intervalWeight‖ < eps := by
  let d := min (eps/4) (1/4)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hdle : d ≤ eps/4 := min_le_left _ _
  have hd1 : d ≤ 1/4 := min_le_right _ _
  have hc : ContinuousOn intervalLogit (Icc d (1-d)) := by
    intro r hr
    exact (intervalLogit_continuousAt (by linarith [hr.1]) (by linarith [hr.2])).continuousWithinAt
  obtain ⟨R,hRp,hR⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  let f := bandMultiplier 0 R
  have hn : ‖weightedPullback f-intervalWeight‖ ≤ 2*d := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro r
    by_cases hr : r.1 ∈ Icc d (1-d)
    · have hrR : |intervalLogit r.1| ≤ R := by
        simpa only [Real.norm_eq_abs] using hR _ (mem_image_of_mem intervalLogit hr)
      have he : f (intervalLogit r.1)=1 := bandMultiplier_one hRp (by
        simpa only [mem_Icc,zero_sub,zero_add] using abs_le.mp hrR)
      simp only [ContinuousMap.sub_apply,weightedPullback_apply,he,mul_one,sub_self,norm_zero]
      positivity
    · have hw : ‖intervalWeight r‖ ≤ d := by
        rw [intervalWeight_norm]
        by_cases hrd : d ≤ r.1
        · have hr1 : 1-d < r.1 := lt_of_not_ge (fun hh => hr ⟨hrd,hh⟩)
          calc
            r.1*(1-r.1) ≤ 1*(1-r.1) := mul_le_mul_of_nonneg_right r.2.2 (sub_nonneg.mpr r.2.2)
            _ ≤ d := by linarith
        · have hr0 : r.1 < d := lt_of_not_ge hrd
          calc
            r.1*(1-r.1) ≤ r.1*1 := mul_le_mul_of_nonneg_left (by linarith [r.2.1]) r.2.1
            _ ≤ d := by linarith
      have hf : ‖f (intervalLogit r.1)‖ ≤ 1 :=
        (f.norm_coe_le_norm _).trans (norm_bandMultiplier_le _ _)
      change ‖intervalWeight r*f (intervalLogit r.1)-intervalWeight r‖ ≤ _
      calc
        _ ≤ ‖intervalWeight r*f (intervalLogit r.1)‖+‖intervalWeight r‖ := norm_sub_le _ _
        _ ≤ ‖intervalWeight r‖*1+‖intervalWeight r‖ := by rw [norm_mul]; gcongr
        _ ≤ 2*d := by nlinarith
  exact ⟨f,bandMultiplier_hasCompactSupport hRp,hn.trans_lt (by linarith)⟩

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace CyclicSeparatingData

lemma logCalculus_nondegenerate (S : CyclicSeparatingData H) :
    Dense {h : H | ∃ f : BoundedContinuousFunction ℝ ℂ,
      HasCompactSupport (f : ℝ → ℂ) ∧ ∃ k : H, S.logCalculus f k=h} := by
  let U : Set H := {h : H | ∃ f : BoundedContinuousFunction ℝ ℂ,
    HasCompactSupport (f : ℝ → ℂ) ∧ ∃ k : H, S.logCalculus f k=h}
  have hKU : Set.range S.K ⊆ closure U := by
    rintro _ ⟨x,rfl⟩
    rw [Metric.mem_closure_iff]
    intro eps heps
    obtain ⟨f,hf,hfe⟩ := exists_compact_weight_approx (div_pos heps (by positivity : 0 < ‖x‖+1))
    refine ⟨S.logCalculus f (S.K x),⟨f,hf,S.K x,rfl⟩,?_⟩
    have hid : S.logCalculus f (S.K x)-S.K x =
        S.intervalCalculus (weightedPullback f-intervalWeight) x := by
      rw [S.logCalculus_weighted,map_sub,S.intervalCalculus_weight]
      rfl
    rw [dist_comm,dist_eq_norm,hid]
    have hbound := (S.intervalCalculus (weightedPullback f-intervalWeight)).le_opNorm x
    have hnorm := S.intervalCalculus_norm_le (weightedPullback f-intervalWeight)
    calc
      _ ≤ ‖weightedPullback f-intervalWeight‖*‖x‖ := hbound.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
      _ ≤ (eps/(‖x‖+1))*‖x‖ := mul_le_mul_of_nonneg_right hfe.le (norm_nonneg _)
      _ < eps := by
        have hp : 0 < ‖x‖+1 := by positivity
        have he : eps/(‖x‖+1)*(‖x‖+1)=eps := div_mul_cancel₀ _ hp.ne'
        have hq : 0 < eps/(‖x‖+1) := div_pos heps hp
        nlinarith
  apply dense_iff_closure_eq.mpr
  apply Set.eq_univ_of_univ_subset
  rw [← S.K_dense.closure_range]
  exact closure_minimal hKU isClosed_closure

def D (S : CyclicSeparatingData H) : RealSpectralCalculus H where
  calculus := S.logCalculus
  nondegenerate := S.logCalculus_nondegenerate

end CyclicSeparatingData
end BoundedRecovery

end
end
end
end

end OAI
