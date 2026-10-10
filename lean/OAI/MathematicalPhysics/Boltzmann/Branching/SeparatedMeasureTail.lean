import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Order.LiminfLimsup

namespace OAI

section

/-! # Compact approximation by bounded separated spacetime–velocity tests -/

noncomputable section

open Set
open scoped BoundedContinuousFunction

namespace BoltzmannNonuniqueness.SeparatedTests

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def atom (p : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) : C(X × Y,ℝ) :=
  ⟨fun z => p.1 z.1*p.2 z.2,(p.1.continuous.comp continuous_fst).mul
    (p.2.continuous.comp continuous_snd)⟩

def eval : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) → C(X × Y,ℝ)
  | [] => 0
  | p::ps => atom p+eval ps

theorem eval_append (ps qs : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ))) :
    eval (ps++qs) = eval ps+eval qs := by
  induction ps with
  | nil => simp [eval]
  | cons p ps ih => simp [eval,ih,add_assoc]

def product (ps qs : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ))) :
    List ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) :=
  ps.flatMap (fun p => qs.map (fun q => (p.1*q.1,p.2*q.2)))

theorem eval_product (ps qs : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ))) :
    eval (product ps qs) = eval ps*eval qs := by
  have hrow (p : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) :
      eval (qs.map (fun q => (p.1*q.1,p.2*q.2))) = atom p*eval qs := by
    induction qs with
    | nil => simp [eval]
    | cons q qs ih =>
      simp only [List.map_cons,eval,ih,mul_add]
      congr 1
      ext z
      change (p.1 z.1*q.1 z.1)*(p.2 z.2*q.2 z.2) =
        (p.1 z.1*p.2 z.2)*(q.1 z.1*q.2 z.2)
      ring
  induction ps with
  | nil => simp [product,eval]
  | cons p ps ih =>
    change eval ((qs.map (fun q => (p.1*q.1,p.2*q.2)))++product ps qs) = _
    rw [eval_append,hrow,ih,eval,add_mul]

def algebra : Subalgebra ℝ C(X × Y,ℝ) where
  carrier := {f | ∃ ps, eval ps = f}
  zero_mem' := ⟨[],rfl⟩
  one_mem' := ⟨[(1,1)],by ext z; simp [eval,atom]⟩
  add_mem' := by
    rintro f g ⟨ps,rfl⟩ ⟨qs,rfl⟩
    exact ⟨ps++qs,eval_append ps qs⟩
  mul_mem' := by
    rintro f g ⟨ps,rfl⟩ ⟨qs,rfl⟩
    exact ⟨product ps qs,eval_product ps qs⟩
  algebraMap_mem' := by
    intro r
    refine ⟨[(BoundedContinuousFunction.const X r,1)],?_⟩
    ext z
    simp [eval,atom]

def probe (x : X) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => min (dist x y) 1,(continuous_const.dist continuous_id).min continuous_const⟩ 1
    (by
      intro y z
      rw [Real.dist_eq]
      change |min (dist x y) 1-min (dist x z) 1| ≤ 1
      apply abs_le.mpr
      have hy : 0 ≤ min (dist x y) 1 := le_min dist_nonneg zero_le_one
      have hz : 0 ≤ min (dist x z) 1 := le_min dist_nonneg zero_le_one
      have hy1 := min_le_right (dist x y) (1:ℝ)
      have hz1 := min_le_right (dist x z) (1:ℝ)
      constructor <;> linarith)

theorem probe_self (x : X) : probe x x = 0 := by simp [probe]

theorem probe_pos {x y : X} (h : x ≠ y) : 0 < probe x y :=
  lt_min (dist_pos.mpr h) zero_lt_one

theorem algebra_separatesPoints : (algebra (X := X) (Y := Y)).SeparatesPoints := by
  intro x y hxy
  by_cases hx : x.1 = y.1
  · have hy : x.2 ≠ y.2 := by intro hy; exact hxy (Prod.ext hx hy)
    let p : (X →ᵇ ℝ) × (Y →ᵇ ℝ) := (1,probe x.2)
    refine ⟨atom p,⟨atom p,⟨[(p)],by simp [eval]⟩,rfl⟩,?_⟩
    change (1:ℝ)*probe x.2 x.2 ≠ 1*probe x.2 y.2
    rw [probe_self,one_mul,one_mul]
    exact ne_of_lt (probe_pos hy)
  · let p : (X →ᵇ ℝ) × (Y →ᵇ ℝ) := (probe x.1,1)
    refine ⟨atom p,⟨atom p,⟨[(p)],by simp [eval]⟩,rfl⟩,?_⟩
    change probe x.1 x.1*(1:ℝ) ≠ probe x.1 y.1*1
    rw [probe_self,mul_one,mul_one]
    exact ne_of_lt (probe_pos hx)

theorem exists_approximation (f : C(X × Y,ℝ)) {K : Set (X × Y)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ps : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ)), ∀ z ∈ K, |eval ps z-f z| < ε := by
  obtain ⟨g,⟨ps,rfl⟩,hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      algebra_separatesPoints f hK hε
  exact ⟨ps,fun z hz => by simpa only [Real.norm_eq_abs] using hg z hz⟩

end BoltzmannNonuniqueness.SeparatedTests

end

end

section

/-! # Globally uniform separated approximation for compactly supported tests -/

noncomputable section

open Set Metric
open scoped BoundedContinuousFunction

namespace BoltzmannNonuniqueness.SeparatedTests

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def cutoff (x : X) (R : ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => max 0 (min 1 (R+1-dist y x)),
      continuous_const.max (continuous_const.min
        (continuous_const.sub (continuous_id.dist continuous_const)))⟩ 1
    (by
      intro y z
      rw [Real.dist_eq]
      change |max 0 (min 1 (R+1-dist y x))-max 0 (min 1 (R+1-dist z x))| ≤ 1
      have hy0 : 0 ≤ max 0 (min 1 (R+1-dist y x)) := le_max_left _ _
      have hz0 : 0 ≤ max 0 (min 1 (R+1-dist z x)) := le_max_left _ _
      have hy1 : max 0 (min 1 (R+1-dist y x)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
      have hz1 : max 0 (min 1 (R+1-dist z x)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
      exact abs_le.mpr ⟨by linarith,by linarith⟩)

theorem cutoff_mem (x y : X) (R : ℝ) : cutoff x R y ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩

theorem cutoff_eq_one {x y : X} {R : ℝ} (hy : y ∈ closedBall x R) : cutoff x R y = 1 := by
  change max 0 (min 1 (R+1-dist y x)) = 1
  rw [min_eq_left (by have := mem_closedBall.mp hy; linarith),max_eq_right zero_le_one]

theorem cutoff_eq_zero {x y : X} {R : ℝ} (hy : y ∉ closedBall x (R+1)) : cutoff x R y = 0 := by
  have hd : R+1 < dist y x := lt_of_not_ge (fun h => hy (mem_closedBall.mpr h))
  change max 0 (min 1 (R+1-dist y x)) = 0
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem exists_global_approximation [ProperSpace X] [ProperSpace Y]
    (f : C(X × Y,ℝ)) (x : X) (y : Y) (R S : ℝ)
    (hf : ∀ z, z ∉ closedBall x R ×ˢ closedBall y S → f z = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ps : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ)), ∀ z, |eval ps z-f z| < ε := by
  let K := closedBall x (R+1) ×ˢ closedBall y (S+1)
  obtain ⟨ps,hps⟩ := exists_approximation f
    ((isCompact_closedBall x (R+1)).prod (isCompact_closedBall y (S+1))) hε
  let c : (X →ᵇ ℝ) × (Y →ᵇ ℝ) := (cutoff x R,cutoff y S)
  refine ⟨product [c] ps,fun z => ?_⟩
  have he : eval (product [c] ps) z = (cutoff x R z.1*cutoff y S z.2)*eval ps z := by
    rw [eval_product]
    simp [eval,atom,c]
  rw [he]
  have hc0 : 0 ≤ cutoff x R z.1*cutoff y S z.2 :=
    mul_nonneg (cutoff_mem _ _ _).1 (cutoff_mem _ _ _).1
  have hc1 : cutoff x R z.1*cutoff y S z.2 ≤ 1 := by
    nlinarith [(cutoff_mem x z.1 R).1,(cutoff_mem x z.1 R).2,
      (cutoff_mem y z.2 S).1,(cutoff_mem y z.2 S).2]
  have hcf : (cutoff x R z.1*cutoff y S z.2)*f z = f z := by
    by_cases hz : z ∈ closedBall x R ×ˢ closedBall y S
    · rw [cutoff_eq_one hz.1,cutoff_eq_one hz.2,one_mul,one_mul]
    · rw [hf z hz,mul_zero]
  by_cases hz : z ∈ K
  · calc
      _ = |(cutoff x R z.1*cutoff y S z.2)*(eval ps z-f z)| := by rw [mul_sub,hcf]
      _ ≤ |eval ps z-f z| := by
        rw [abs_mul,abs_of_nonneg hc0]
        exact mul_le_of_le_one_left (abs_nonneg _) hc1
      _ < ε := hps z hz
  · have hc : cutoff x R z.1*cutoff y S z.2 = 0 := by
      by_cases hx : z.1 ∈ closedBall x (R+1)
      · have hy : z.2 ∉ closedBall y (S+1) := fun hy => hz ⟨hx,hy⟩
        rw [cutoff_eq_zero hy,mul_zero]
      · rw [cutoff_eq_zero hx,zero_mul]
    have hfz : f z = 0 := by simpa only [hc,zero_mul] using hcf.symm
    simpa only [hc,hfz,zero_mul,sub_zero,abs_zero] using hε

end BoltzmannNonuniqueness.SeparatedTests

end

end

section

/-! # Extending separated-test convergence to compactly supported kinetic tests -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace BoltzmannNonuniqueness.SeparatedTests

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def evalBound : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) → ℝ
  | [] => 0
  | p::ps => ‖p.1‖*‖p.2‖+evalBound ps

theorem abs_eval_le (ps : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ))) (z : X × Y) :
    |eval ps z| ≤ evalBound ps := by
  induction ps with
  | nil => simp [eval,evalBound]
  | cons p ps ih =>
    calc
      _ ≤ |p.1 z.1*p.2 z.2|+|eval ps z| := abs_add_le _ _
      _ ≤ ‖p.1‖*‖p.2‖+evalBound ps := by
        apply add_le_add _ ih
        rw [abs_mul]
        exact mul_le_mul (p.1.norm_coe_le_norm _) (p.2.norm_coe_le_norm _)
          (abs_nonneg _) (norm_nonneg _)

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y]

theorem eval_integrable (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (ps : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ))) : Integrable (eval ps) μ :=
  (integrable_const (evalBound ps)).mono' (eval ps).continuous.aestronglyMeasurable
    (ae_of_all _ (fun z => abs_eval_le ps z))

theorem eval_integral_tendsto (μ : ℕ → Measure (X × Y)) (ν : Measure (X × Y))
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    (h : ∀ a : X →ᵇ ℝ, ∀ b : Y →ᵇ ℝ,
      Tendsto (fun n => ∫ z, a z.1*b z.2 ∂μ n) atTop (𝓝 (∫ z, a z.1*b z.2 ∂ν)))
    (ps : List ((X →ᵇ ℝ) × (Y →ᵇ ℝ))) :
    Tendsto (fun n => ∫ z, eval ps z ∂μ n) atTop (𝓝 (∫ z, eval ps z ∂ν)) := by
  induction ps with
  | nil => simp [eval]
  | cons p ps ih =>
    have hint (ρ : Measure (X × Y)) [IsFiniteMeasure ρ] : Integrable (atom p) ρ := by
      simpa [eval] using eval_integrable ρ [p]
    have hn (n) : (∫ z, eval (p::ps) z ∂μ n) =
        (∫ z, p.1 z.1*p.2 z.2 ∂μ n)+(∫ z, eval ps z ∂μ n) := by
      exact integral_add (hint _) (eval_integrable _ _)
    have hl : (∫ z, eval (p::ps) z ∂ν) =
        (∫ z, p.1 z.1*p.2 z.2 ∂ν)+(∫ z, eval ps z ∂ν) := by
      exact integral_add (hint _) (eval_integrable _ _)
    simp_rw [hn,hl]
    exact (h p.1 p.2).add ih

theorem compact_test_integral_tendsto [ProperSpace X] [ProperSpace Y]
    (μ : ℕ → Measure (X × Y)) (ν : Measure (X × Y))
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    {C : ℝ} (hC : 0 ≤ C) (hμ : ∀ n, (μ n).real univ ≤ C) (hν : ν.real univ ≤ C)
    (h : ∀ a : X →ᵇ ℝ, ∀ b : Y →ᵇ ℝ,
      Tendsto (fun n => ∫ z, a z.1*b z.2 ∂μ n) atTop (𝓝 (∫ z, a z.1*b z.2 ∂ν)))
    (f : C(X × Y,ℝ)) (hf : HasCompactSupport f)
    (x : X) (y : Y) (R S : ℝ)
    (hs : ∀ z, z ∉ Metric.closedBall x R ×ˢ Metric.closedBall y S → f z = 0) :
    Tendsto (fun n => ∫ z, f z ∂μ n) atTop (𝓝 (∫ z, f z ∂ν)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε/(4*(C+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ps,hps⟩ := exists_global_approximation f x y R S hs hδ
  have hb (ρ : Measure (X × Y)) [IsFiniteMeasure ρ] (hρ : ρ.real univ ≤ C) :
      |(∫ z, f z ∂ρ)-(∫ z, eval ps z ∂ρ)| ≤ δ*C := by
    rw [← integral_sub (f.continuous.integrable_of_hasCompactSupport hf) (eval_integrable ρ ps)]
    have hn : |∫ z, f z-eval ps z ∂ρ| ≤ δ*ρ.real univ := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le_const
      exact ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs,abs_sub_comm]
        exact (hps z).le)
    exact hn.trans (mul_le_mul_of_nonneg_left hρ hδ.le)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (eval_integral_tendsto μ ν h ps) (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hmid := hN n hn
  rw [Real.dist_eq] at hmid ⊢
  have hleft := hb (μ n) (hμ n)
  have hright := hb ν hν
  have htri : |(∫ z, f z ∂μ n)-(∫ z, f z ∂ν)| ≤
      |(∫ z, f z ∂μ n)-(∫ z, eval ps z ∂μ n)|+
      |(∫ z, eval ps z ∂μ n)-(∫ z, eval ps z ∂ν)|+
      |(∫ z, f z ∂ν)-(∫ z, eval ps z ∂ν)| := by
    have h₁ := abs_sub_le (∫ z, f z ∂μ n) (∫ z, eval ps z ∂μ n) (∫ z, f z ∂ν)
    have h₂ := abs_sub_le (∫ z, eval ps z ∂μ n) (∫ z, eval ps z ∂ν) (∫ z, f z ∂ν)
    rw [abs_sub_comm (∫ z, eval ps z ∂ν) (∫ z, f z ∂ν)] at h₂
    linarith
  have hδeq : δ*(4*(C+1)) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith

end BoltzmannNonuniqueness.SeparatedTests

end

end

section

/-! # Eventual finite-mass version of separated-test convergence -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace BoltzmannNonuniqueness.SeparatedTests

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] [ProperSpace X] [ProperSpace Y]

theorem compact_test_tendsto_of_eventually_finite
    (μ : ℕ → Measure (X × Y)) (ν : Measure (X × Y)) [IsFiniteMeasure ν]
    (hfin : ∀ᶠ n in atTop, IsFiniteMeasure (μ n))
    (h : ∀ a : X →ᵇ ℝ, ∀ b : Y →ᵇ ℝ,
      Tendsto (fun n => ∫ z, a z.1*b z.2 ∂μ n) atTop (𝓝 (∫ z, a z.1*b z.2 ∂ν)))
    (f : C(X × Y,ℝ)) (hf : HasCompactSupport f)
    (x : X) (y : Y) (R S : ℝ)
    (hs : ∀ z, z ∉ Metric.closedBall x R ×ˢ Metric.closedBall y S → f z = 0) :
    Tendsto (fun n => ∫ z, f z ∂μ n) atTop (𝓝 (∫ z, f z ∂ν)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hfin
  let ρ : ℕ → Measure (X × Y) := fun n => μ (n+N)
  have hρ (n) : IsFiniteMeasure (ρ n) := hN _ (Nat.le_add_left N n)
  let _ (n : ℕ) : IsFiniteMeasure (ρ n) := hρ n
  have hp (a : X →ᵇ ℝ) (b : Y →ᵇ ℝ) :
      Tendsto (fun n => ∫ z, a z.1*b z.2 ∂ρ n) atTop (𝓝 (∫ z, a z.1*b z.2 ∂ν)) :=
    (h a b).comp (tendsto_add_atTop_nat N)
  have hm : Tendsto (fun n => (ρ n).real univ) atTop (𝓝 (ν.real univ)) := by
    have ht := hp 1 1
    change Tendsto (fun n => ∫ _z : X × Y, (1:ℝ)*1 ∂ρ n) atTop
      (𝓝 (∫ _z : X × Y, (1:ℝ)*1 ∂ν)) at ht
    simpa only [one_mul,integral_const,smul_eq_mul,mul_one] using ht
  obtain ⟨M,hM⟩ := hm.bddAbove_range
  let C := max 0 (max M (ν.real univ))
  have hC : 0 ≤ C := le_max_left _ _
  have hμC (n) : (ρ n).real univ ≤ C :=
    (hM (mem_range_self n)).trans ((le_max_left M (ν.real univ)).trans (le_max_right 0 _))
  have hνC : ν.real univ ≤ C := (le_max_right M (ν.real univ)).trans (le_max_right 0 _)
  apply (tendsto_add_atTop_iff_nat N).mp
  exact compact_test_integral_tendsto ρ ν hC hμC hνC hp f hf x y R S hs

end BoltzmannNonuniqueness.SeparatedTests

end

end

end OAI
