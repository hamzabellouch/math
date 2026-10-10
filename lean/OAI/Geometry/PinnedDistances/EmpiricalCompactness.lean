import OAI.Geometry.PinnedDistances.LogBounds

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace WeakPinned.Bounded
attribute [local instance] Classical.propDecidable
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩

variable {V : Type u1} {X : Type u2} [Fintype V] [MeasurableSpace X] [MeasurableSingletonClass X]

def uniformLaw (U : V → X) : Measure X := finiteLaw (fun _ => (Fintype.card V:ℝ)⁻¹) U

omit [MeasurableSingletonClass X] in
lemma uniformLaw_probability (U : V → X) (hn : 0<Fintype.card V) : IsProbabilityMeasure (uniformLaw U) := by
  apply finiteLaw_probability
  · intro; positivity
  · simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hn.ne')

def uniformProbability (U : V → X) (hn : 0<Fintype.card V) : ProbabilityMeasure X :=
  ⟨uniformLaw U,uniformLaw_probability U hn⟩

lemma uniformLaw_apply (U : V → X) (s : Set X) [DecidablePred (fun x => U x∈s)] :
    uniformLaw U s=ENNReal.ofReal (((Finset.univ.filter (fun x => U x∈s)).card:ℝ)/(Fintype.card V:ℝ)) := by
  simp only [uniformLaw,finiteLaw,Measure.finsetSum_apply,Measure.smul_apply,
    smul_eq_mul,Measure.dirac_apply,Set.indicator_apply,Pi.one_apply,mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  rw [div_eq_mul_inv,ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]

omit [MeasurableSingletonClass X] in
lemma uniformLaw_map {Y : Type u3} [MeasurableSpace Y] (U : V → X) (f : X → Y) (hf : Measurable f) :
    (uniformLaw U).map f=uniformLaw (f ∘ U) := finiteLaw_map _ _ _ hf

variable {P : ℕ → Type u4} [∀ n,Fintype (P n)] [∀ n,DecidableEq (P n)]

lemma normalized_empirical_nonatomic (u : ∀ n,P n → ℂ) (x : ∀ n,P n)
    (hu : ∀ n,Function.Injective (u n)) (hn : ∀ n,2≤Fintype.card (P n))
    (hcard : Tendsto (fun n => (Fintype.card (P n):ℝ)) atTop atTop)
    (C : ℝ) (hC : 0≤C) (hlog : ∀ n,logAverage (u n)≤C)
    (hx : ∀ n,(∑ y,logCost (u n) (x n) y)≤C*(Fintype.card (P n):ℝ))
    (β : ProbabilityMeasure Sphere)
    (ht : Tendsto (fun n => uniformProbability (fun y => ((u n y-u n (x n)):Sphere))
      (by have := hn n; omega)) atTop (𝓝 β)) :
    NullSingletonClass (β:Measure Sphere) := by
  apply weak_limit_nonatomic ht
  · intro ε hε
    let R := Real.exp (C/ε+1)
    have hR : 1<R := by dsimp [R]; rw [Real.one_lt_exp_iff]; positivity
    refine ⟨R,Eventually.of_forall (fun n => ?_)⟩
    change uniformLaw (fun y => ((u n y-u n (x n)):Sphere)) _≤_
    rw [uniformLaw_apply]
    apply ENNReal.ofReal_le_ofReal
    have hh := normalized_tail_card (u n) C (x n) (hx n) (hn n) R hR
    have hs : (Finset.univ.filter (fun y => (((u n y-u n (x n)):Sphere))∈
        (OnePoint.some '' Metric.closedBall (0:ℂ) R)ᶜ))=
        Finset.univ.filter (fun y => R<‖u n y-u n (x n)‖) := by
      ext y
      simp [Metric.mem_closedBall,dist_eq_norm]
    change (((Finset.univ.filter (fun y => (((u n y-u n (x n)):Sphere))∈
      (OnePoint.some '' Metric.closedBall (0:ℂ) R)ᶜ)).card:ℝ)/(Fintype.card (P n):ℝ))≤ε
    rw [hs]
    apply hh.trans
    rw [show Real.log R=C/ε+1 by simp [R]]
    apply (div_le_iff₀ (by positivity : 0<C/ε+1)).mpr
    have he : ε*(C/ε+1)=C+ε := by field_simp
    rw [he]
    linarith
  · intro z ε hε
    let T := 2*C/ε^2+1
    let r := Real.exp (-T)/2
    have hT : 0<T := by dsimp [T]; positivity
    have hr : 0<r := by dsimp [r]; positivity
    have hr2 : r<1/2 := by dsimp [r]; have hh := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hT); linarith
    have hsmall : Tendsto (fun n => 1/(Fintype.card (P n):ℝ)) atTop (𝓝 0) := by simpa only [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp hcard)
    have hsmall' : ∀ᶠ n in atTop,1/(Fintype.card (P n):ℝ)≤ε^2/2 :=
      hsmall.eventually_le_const (by positivity)
    refine ⟨r,hr,hsmall'.mono (fun n hn' => ?_)⟩
    change uniformLaw (fun y => ((u n y-u n (x n)):Sphere)) _≤_
    rw [uniformLaw_apply]
    apply ENNReal.ofReal_le_ofReal
    have hs : (Finset.univ.filter (fun y => (((u n y-u n (x n)):Sphere))∈
        OnePoint.some '' Metric.ball z r))=
        Finset.univ.filter (fun y => ‖u n y-(z+u n (x n))‖<r) := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_image,OnePoint.coe_eq_coe,exists_eq_right,
        Metric.mem_ball,dist_eq_norm]
      ring_nf
    rw [hs]
    have hh := small_ball_card (u n) (hu n) C (hn n) (hlog n) (z+u n (x n)) r hr hr2
    have hl : -Real.log (2*r)=T := by
      rw [show 2*r=Real.exp (-T) by dsimp [r]; ring,Real.log_exp,neg_neg]
    rw [hl] at hh
    have hCT : C/T≤ε^2/2 := by
      apply (div_le_iff₀ hT).mpr
      have he : ε^2/2*T=C+ε^2/2 := by dsimp [T]; field_simp
      rw [he]
      linarith [sq_nonneg ε]
    nlinarith

end WeakPinned.Bounded

end
end

end OAI
