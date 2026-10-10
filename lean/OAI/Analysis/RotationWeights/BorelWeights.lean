import OAI.Analysis.RotationWeights.FunctionalCalculus

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

namespace ContinuousCircleWeight

section
open Set Filter
open scoped Topology

structure RealBorel where
  f : CircleX → ℝ
  measurable : Measurable f
  bound : ℝ≥0
  norm_le : ∀ x,‖f x‖≤bound
instance : CoeFun RealBorel (fun _ => CircleX → ℝ) := ⟨RealBorel.f⟩
namespace RealBorel
def const (c : ℝ) : RealBorel := ⟨fun _ => c,measurable_const,⟨|c|,abs_nonneg _⟩,by intro x; exact le_refl _⟩
def add (g h : RealBorel) : RealBorel :=
  ⟨fun x => g x+h x,g.measurable.add h.measurable,g.bound+h.bound,
    fun x => (norm_add_le _ _).trans (add_le_add (g.norm_le x) (h.norm_le x))⟩
def mul (g h : RealBorel) : RealBorel :=
  ⟨fun x => g x*h x,g.measurable.mul h.measurable,g.bound*h.bound,
    fun x => (norm_mul _ _).le.trans (mul_le_mul (g.norm_le x) (h.norm_le x) (norm_nonneg _) g.bound.property)⟩
def shift (θ : CircleX) (g : RealBorel) : RealBorel :=
  ⟨fun x => g (x+θ),g.measurable.comp (measurable_id.add_const θ),g.bound,fun x => g.norm_le (x+θ)⟩
def ofContinuous (g : C(CircleX,ℝ)) : RealBorel :=
  ⟨g,g.continuous.measurable,⟨‖g‖,norm_nonneg _⟩,g.norm_coe_le_norm⟩
end RealBorel

def realPi (θ : CircleX) (g : RealBorel) : CircleFiberOperator :=
  boundedPi θ (fun x => (g x:ℂ)) (Complex.measurable_ofReal.comp g.measurable) g.bound
    (fun x => by simpa using g.norm_le x)
def realPiField (θ : CircleX) (g : RealBorel) (x : CircleX) : FiberOperator :=
  boundedPiField θ (fun x => (g x:ℂ)) g.bound (fun x => by simpa using g.norm_le x) x
@[simp] lemma realPiField_apply (θ : CircleX) (g : RealBorel) (x : CircleX) (u : FiberHilbert) (k : ℤ) :
    realPiField θ g x u k=(g (x+k•θ):ℂ)*u k := rfl
lemma realPiField_bound (θ : CircleX) (g : RealBorel) (x : CircleX) : ‖realPiField θ g x‖≤g.bound :=
  boundedPiField_bound _ _ _ _ _
lemma realPi_coe (θ : CircleX) (g : RealBorel) (u : CircleFiberL2) :
    realPi θ g u =ᵐ[AddCircle.haarAddCircle] fun x => realPiField θ g x (u x) :=
  boundedPi_coe _ _ _ _ _ _
lemma realPi_norm_le (θ : CircleX) (g : RealBorel) : ‖realPi θ g‖≤g.bound := boundedPi_norm_le _ _ _ _ _
lemma realPi_congr (θ : CircleX) (g h : RealBorel) (he : (fun x => g x)=ᵐ[AddCircle.haarAddCircle] (fun x => h x)) :
    realPi θ g=realPi θ h :=
  boundedPi_congr θ _ _ _ _ _ _ _ _ (he.mono (fun _x hx => congrArg Complex.ofReal hx))
lemma realPi_continuous (θ : CircleX) (g : C(CircleX,ℝ)) :
    realPi θ (RealBorel.ofContinuous g)=continuousPi θ (complexCircleMap g) := by
  apply (boundedPi_congr θ _ (complexCircleMap g) _ _ _ _ _ _ (Eventually.of_forall (fun _ => rfl))).trans
  exact boundedPi_eq_continuousPi θ (complexCircleMap g) (RealBorel.ofContinuous g).bound (fun x => by simpa [complexCircleMap,RealBorel.ofContinuous] using (RealBorel.ofContinuous g).norm_le x)
lemma realPi_add (θ : CircleX) (g h : RealBorel) : realPi θ (g.add h)=realPi θ g+realPi θ h := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [realPi_coe θ (g.add h) u,realPi_coe θ g u,realPi_coe θ h u,Lp.coeFn_add (realPi θ g u) (realPi θ h u)] with x h1 h2 h3 h4
  change (realPi θ (g.add h) u) x=(realPi θ g u+realPi θ h u) x
  rw [h1,h4]
  ext k
  simp only [Pi.add_apply,h2,h3,realPiField_apply,RealBorel.add,lp.coeFn_add,Complex.ofReal_add]
  ring
lemma realPi_mul (θ : CircleX) (g h : RealBorel) : realPi θ (g.mul h)=realPi θ g*realPi θ h := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [realPi_coe θ (g.mul h) u,realPi_coe θ h u,realPi_coe θ g (realPi θ h u)] with x h1 h2 h3
  change (realPi θ (g.mul h) u) x=(realPi θ g (realPi θ h u)) x
  rw [h1,h3,h2]
  ext k
  simp only [realPiField_apply,RealBorel.mul,Complex.ofReal_mul,mul_assoc]
lemma realPi_one (θ : CircleX) : realPi θ (RealBorel.const 1)=1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [realPi_coe θ (RealBorel.const 1) u] with x hx
  rw [hx]
  ext k
  simp only [realPiField_apply,RealBorel.const,Complex.ofReal_one,one_mul]
  rfl
lemma realPi_commute (θ : CircleX) (g h : RealBorel) : Commute (realPi θ g) (realPi θ h) := by
  change _*_= _*_
  rw [←realPi_mul,←realPi_mul]
  apply realPi_congr
  exact Eventually.of_forall (fun x => mul_comm _ _)
lemma realPiField_symmetric (θ : CircleX) (g : RealBorel) (x : CircleX)
    (u v : FiberHilbert) : inner ℂ (realPiField θ g x u) v=inner ℂ u (realPiField θ g x v) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  simp only [realPiField_apply,RCLike.inner_apply,map_mul,Complex.conj_ofReal]
  ring
lemma realPi_selfAdjoint (θ : CircleX) (g : RealBorel) : IsSelfAdjoint (realPi θ g) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [realPi_coe θ g u,realPi_coe θ g v] with x hu hv
  change inner ℂ ((realPi θ g u) x) (v x)=inner ℂ (u x) ((realPi θ g v) x)
  rw [hu,hv]
  exact realPiField_symmetric θ g x (u x) (v x)
lemma realPi_commutes (θ : CircleX) (B : CircleFiberOperator)
    (hB : ∀ f : C(CircleX,ℝ),Commute (continuousPi θ (complexCircleMap f)) B) (g : RealBorel) :
    Commute (realPi θ g) B := commute_boundedPi_real _ _ hB _ g.measurable _ g.norm_le
lemma realPi_injective (θ : CircleX) (g : RealBorel) (hg : ∀ x,g x≠0) : Function.Injective (realPi θ g) := by
  apply (injective_iff_map_eq_zero (realPi θ g)).mpr
  intro u hu
  apply Lp.ext
  filter_upwards [realPi_coe θ g u,Lp.coeFn_zero FiberHilbert 2 AddCircle.haarAddCircle] with x hx hz
  rw [hu,hz] at hx
  rw [hz]
  ext k
  have h := congrArg (fun v : FiberHilbert => v k) hx
  change (0:ℂ)=(g (x+k•θ):ℂ)*u x k at h
  exact (mul_eq_zero.mp h.symm).resolve_left (Complex.ofReal_ne_zero.mpr (hg _))

lemma realPi_shift (θ : CircleX) (g : RealBorel) :
    realPi θ g*fiberShiftL2 1 = fiberShiftL2 1*realPi θ (g.shift θ) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [realPi_coe θ g (fiberShiftL2 1 u),fiberShiftL2_coe 1 u,
    realPi_coe θ (g.shift θ) u,fiberShiftL2_coe 1 (realPi θ (g.shift θ) u)] with x h1 h2 h3 h4
  change (realPi θ g (fiberShiftL2 1 u)) x=(fiberShiftL2 1 (realPi θ (g.shift θ) u)) x
  rw [h1,h2,h4,h3]
  ext k
  simp only [realPiField_apply,fiberShift_apply,RealBorel.shift]
  congr 3
  rw [sub_zsmul,one_zsmul]
  abel
end

open Set Filter
open scoped Topology

def realCutoff (g : RealBorel) (n : ℕ) : RealBorel where
  f x := if (1:ℝ)/(n+1) ≤ g x then 1 else 0
  measurable := Measurable.ite (measurableSet_le measurable_const g.measurable) measurable_const measurable_const
  bound := 1
  norm_le x := by split_ifs <;> norm_num

def realCutoffInv (g : RealBorel) (n : ℕ) : RealBorel where
  f x := if (1:ℝ)/(n+1) ≤ g x then (g x)⁻¹ else 0
  measurable := Measurable.ite (measurableSet_le measurable_const g.measurable) g.measurable.inv measurable_const
  bound := n+1
  norm_le x := by
    split_ifs with h
    · have hn : (0:ℝ)<n+1 := by positivity
      have hg : 0<g x := (one_div_pos.mpr hn).trans_le h
      rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hg)]
      have hh := one_div_le_one_div_of_le (one_div_pos.mpr hn) h
      simpa using hh
    · simp only [norm_zero,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]; positivity

lemma realCutoff_proj (θ : CircleX) (g : RealBorel) (n : ℕ) :
    IsStarProjection (realPi θ (realCutoff g n)) := by
  refine ⟨?_,realPi_selfAdjoint θ _⟩
  change realPi θ _*realPi θ _=realPi θ _
  rw [←realPi_mul]
  apply realPi_congr
  exact Eventually.of_forall (fun x => by change (if _ then (1:ℝ) else 0)*(if _ then 1 else 0)=(if _ then 1 else 0); split_ifs <;> norm_num)

lemma realCutoff_mul_inv (θ : CircleX) (g : RealBorel) (n : ℕ) :
    realPi θ g * realPi θ (realCutoffInv g n) = realPi θ (realCutoff g n) := by
  rw [←realPi_mul]
  apply realPi_congr
  apply Eventually.of_forall
  intro x
  change g x*(if (1:ℝ)/(n+1)≤g x then (g x)⁻¹ else 0)=(if (1:ℝ)/(n+1)≤g x then 1 else 0)
  split_ifs with h
  · apply mul_inv_cancel₀
    exact ne_of_gt ((one_div_pos.mpr (by positivity : (0:ℝ)<n+1)).trans_le h)
  · exact mul_zero _

def realCutoffRange (θ : CircleX) (g : RealBorel) (n : ℕ) : Submodule ℂ CircleFiberL2 :=
  (realPi θ (realCutoff g n)).range
instance realCutoffRange_complete (θ : CircleX) (g : RealBorel) (n : ℕ) : CompleteSpace (realCutoffRange θ g n) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range (realCutoff_proj θ g n).isIdempotentElem).completeSpace_coe
lemma realCutoffRange_projection (θ : CircleX) (g : RealBorel) (n : ℕ) :
    (realCutoffRange θ g n).starProjection=realPi θ (realCutoff g n) := by
  obtain ⟨_,h⟩ := isStarProjection_iff_eq_starProjection_range.mp (realCutoff_proj θ g n)
  exact h.symm
lemma realCutoffRange_le (θ : CircleX) (g : RealBorel) (n : ℕ) :
    realCutoffRange θ g n ≤ (realPi θ g).range := by
  rintro x ⟨u,rfl⟩
  refine ⟨realPi θ (realCutoffInv g n) u,?_⟩
  exact DFunLike.congr_fun (realCutoff_mul_inv θ g n) u

lemma realPi_tendsto (θ : CircleX) (g : ℕ → RealBorel) (h : RealBorel) (C : ℝ≥0)
    (hg : ∀ n x,‖g n x‖≤C) (hh : ∀ x,‖h x‖≤C)
    (hl : ∀ᵐ x ∂AddCircle.haarAddCircle,Tendsto (fun n => g n x) atTop (𝓝 (h x)))
    (u : CircleFiberL2) : Tendsto (fun n => realPi θ (g n) u) atTop (𝓝 (realPi θ h u)) := by
  have hg' (n : ℕ) (x : CircleX) : ‖(g n x:ℂ)‖≤C := by simpa using hg n x
  have hh' (x : CircleX) : ‖(h x:ℂ)‖≤C := by simpa using hh x
  have he (f : RealBorel) (hf : ∀ x,‖(f x:ℂ)‖≤C) :
      boundedPi θ (fun x => (f x:ℂ)) (Complex.measurable_ofReal.comp f.measurable) C hf=realPi θ f :=
    boundedPi_congr θ _ _ _ _ _ _ _ _ (EventuallyEq.rfl)
  have hhlim := boundedPi_tendsto θ (fun n x => (g n x:ℂ)) (fun x => (h x:ℂ))
    (fun n => Complex.measurable_ofReal.comp (g n).measurable)
    (Complex.measurable_ofReal.comp h.measurable) C hg' hh'
    (hl.mono (fun x hx => Complex.continuous_ofReal.continuousAt.tendsto.comp hx)) u
  simpa only [he] using hhlim

lemma realCutoffRange_tendsto (θ : CircleX) (g : RealBorel) (hg : ∀ x,0<g x) (u : CircleFiberL2) :
    Tendsto (fun n => (realCutoffRange θ g n).starProjection u) atTop (𝓝 u) := by
  simp_rw [realCutoffRange_projection]
  have hh := realPi_tendsto θ (realCutoff g) (RealBorel.const 1) 1
    (fun n x => (realCutoff g n).norm_le x) (fun _ => by norm_num [RealBorel.const]) (Eventually.of_forall (fun x => by
      have ht : Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hev : ∀ᶠ n : ℕ in atTop,(1:ℝ)/(n+1)≤g x := (ht.eventually_le_const (hg x)).mono (fun _ hn => hn)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with n hn
      exact (ite_eq_left hn).symm)) u
  simpa only [realPi_one,one_apply_eq_self] using hh
end ContinuousCircleWeight

end

end OAI
