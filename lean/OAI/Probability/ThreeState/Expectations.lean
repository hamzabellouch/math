import Mathlib
import OAI.Probability.ThreeState.Basic

namespace OAI

/-! Expectations, second moments and the regular and Poisson offspring laws. -/

namespace ThreeState
open scoped Classical

 
noncomputable def mean {α : Type*} (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑' a, mass p a * f a

def HasMean {α : Type*} (p : PMF α) (f : α → ℝ) : Prop :=
  Summable (fun a => mass p a * f a)

lemma HasMean.abs {α : Type*} {p : PMF α} {f : α → ℝ} (h : HasMean p f) :
    HasMean p (fun a => |f a|) := by
  simpa only [HasMean, abs_mul, abs_of_nonneg (mass_nonneg p _)] using Summable.abs h

lemma HasMean.of_abs {α : Type*} {p : PMF α} {f : α → ℝ}
    (h : HasMean p (fun a => |f a|)) : HasMean p f := by
  apply summable_norm_iff.mp
  simpa only [HasMean, Real.norm_eq_abs, abs_mul, abs_of_nonneg (mass_nonneg p _)] using h

lemma hasMean_const {α : Type*} (p : PMF α) (c : ℝ) : HasMean p (fun _ => c) :=
  (mass_summable p).mul_right c

lemma mean_const {α : Type*} (p : PMF α) (c : ℝ) : mean p (fun _ => c) = c := by
  rw [mean, (mass_summable p).tsum_mul_right, mass_sum, one_mul]

lemma HasMean.add {α : Type*} {p : PMF α} {f g : α → ℝ} (hf : HasMean p f) (hg : HasMean p g) :
    HasMean p (fun a => f a+g a) := by
  simpa only [HasMean, mul_add] using Summable.add hf hg

lemma mean_add {α : Type*} {p : PMF α} {f g : α → ℝ} (hf : HasMean p f) (hg : HasMean p g) :
    mean p (fun a => f a+g a) = mean p f+mean p g := by
  simp only [mean, mul_add, hf.tsum_add hg]

lemma HasMean.mul_const {α : Type*} {p : PMF α} {f : α → ℝ} (hf : HasMean p f) (c : ℝ) :
    HasMean p (fun a => f a*c) := by
  simpa only [HasMean, mul_assoc] using hf.mul_right c

lemma mean_mul_const {α : Type*} (p : PMF α) (f : α → ℝ) (c : ℝ) :
    mean p (fun a => f a*c) = mean p f*c := by
  simp only [mean, ← mul_assoc, tsum_mul_right]

lemma HasMean.const_mul {α : Type*} {p : PMF α} {f : α → ℝ} (hf : HasMean p f) (c : ℝ) :
    HasMean p (fun a => c*f a) := by
  simpa only [mul_comm c] using hf.mul_const c

lemma mean_const_mul {α : Type*} (p : PMF α) (f : α → ℝ) (c : ℝ) :
    mean p (fun a => c*f a) = c*mean p f := by
  simp only [mul_comm c, mean_mul_const]

lemma hasMean_of_square {α : Type*} {p : PMF α} {f : α → ℝ}
    (h : HasMean p (fun a => (f a)^2)) : HasMean p f := by
  apply HasMean.of_abs
  apply Summable.of_nonneg_of_le (fun a => mul_nonneg (mass_nonneg p a) (abs_nonneg _))
    (fun a => mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (|f a|-1), sq_abs (f a)])
      (mass_nonneg p a)) ((hasMean_const p 1).add h)

lemma mass_pure {α : Type*} (a b : α) : mass (PMF.pure a) b = if b=a then 1 else 0 := by
  classical
  by_cases h : b=a <;> simp [mass, PMF.pure_apply, h]

lemma mean_pure {α : Type*} (a : α) (f : α → ℝ) : mean (PMF.pure a) f = f a := by
  classical
  simp [mean, mass_pure]

lemma hasMean_pure {α : Type*} (a : α) (f : α → ℝ) : HasMean (PMF.pure a) f := by
  classical
  simp only [HasMean, mass_pure, ite_mul, one_mul, zero_mul]
  exact summable_of_ne_finset_zero (s := {a}) (fun b hb => by simp at hb; simp [hb])

lemma mean_nonneg {α : Type*} (p : PMF α) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ mean p f := tsum_nonneg (fun a => mul_nonneg (mass_nonneg p a) (hf a))

lemma HasMean.bind {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) f)
    (hp : HasMean p (fun a => mean (k a) (fun b => |f b|))) :
    HasMean (p.bind k) f := by
  have hs : Summable (Function.uncurry (fun a b => mass p a * (mass (k a) b * |f b|))) := by
    apply (summable_prod_of_nonneg (fun ab =>
      mul_nonneg (mass_nonneg p ab.1) (mul_nonneg (mass_nonneg _ _) (abs_nonneg _)))).mpr
    change (∀ a, Summable (fun b => mass p a * (mass (k a) b * |f b|))) ∧
      Summable (fun a => ∑' b, mass p a * (mass (k a) b * |f b|))
    constructor
    · intro a
      exact (hk a).abs.mul_left (mass p a)
    · simpa only [tsum_mul_left, mean, HasMean] using hp
  apply HasMean.of_abs
  apply hs.prod_symm.prod.congr
  intro b
  change (∑' a, mass p a * (mass (k a) b * |f b|)) = mass (p.bind k) b * |f b|
  rw [mass_bind, ← tsum_mul_right]
  congr 1
  funext a
  ring

lemma mean_bind {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) f)
    (hp : HasMean p (fun a => mean (k a) (fun b => |f b|))) :
    mean (p.bind k) f = mean p (fun a => mean (k a) f) := by
  have hsabs : Summable (Function.uncurry (fun a b => mass p a * (mass (k a) b * |f b|))) := by
    apply (summable_prod_of_nonneg (fun ab =>
      mul_nonneg (mass_nonneg p ab.1) (mul_nonneg (mass_nonneg _ _) (abs_nonneg _)))).mpr
    change (∀ a, Summable (fun b => mass p a * (mass (k a) b * |f b|))) ∧
      Summable (fun a => ∑' b, mass p a * (mass (k a) b * |f b|))
    constructor
    · intro a
      exact (hk a).abs.mul_left (mass p a)
    · simpa only [tsum_mul_left, mean, HasMean] using hp
  have hs : Summable (Function.uncurry (fun a b => mass p a * (mass (k a) b * f b))) := by
    apply summable_norm_iff.mp
    apply hsabs.congr
    rintro ⟨a,b⟩
    change mass p a * (mass (k a) b * |f b|) = ‖mass p a * (mass (k a) b * f b)‖
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (mass_nonneg p a),
      abs_of_nonneg (mass_nonneg (k a) b)]
  unfold mean
  simp_rw [mass_bind, ← tsum_mul_right, mul_assoc]
  rw [hs.tsum_comm]
  simp only [tsum_mul_left]

lemma HasMean.map {α β : Type*} {p : PMF α} {g : α → β} {f : β → ℝ}
    (h : HasMean p (fun a => f (g a))) : HasMean (p.map g) f := by
  change HasMean (p.bind (fun a => PMF.pure (g a))) f
  apply HasMean.bind (fun a => hasMean_pure _ _)
  simpa only [mean_pure] using h.abs

lemma mean_map {α β : Type*} {p : PMF α} {g : α → β} {f : β → ℝ}
    (h : HasMean p (fun a => f (g a))) : mean (p.map g) f = mean p (fun a => f (g a)) := by
  change mean (p.bind (fun a => PMF.pure (g a))) f = _
  rw [mean_bind (fun a => hasMean_pure _ _) (by simpa only [mean_pure] using h.abs)]
  simp only [mean_pure]

end ThreeState
namespace ThreeState
open scoped Classical

lemma HasMean.mono {α : Type*} {p : PMF α} {f g : α → ℝ} (hg : HasMean p g)
    (hf : ∀ a, 0 ≤ f a) (hle : ∀ a, f a ≤ g a) : HasMean p f := by
  exact Summable.of_nonneg_of_le (fun a => mul_nonneg (mass_nonneg p a) (hf a))
    (fun a => mul_le_mul_of_nonneg_left (hle a) (mass_nonneg p a)) hg

lemma mean_le {α : Type*} {p : PMF α} {f g : α → ℝ}
    (hf : HasMean p f) (hg : HasMean p g) (hle : ∀ a, f a ≤ g a) : mean p f ≤ mean p g := by
  exact Summable.tsum_le_tsum (fun a => mul_le_mul_of_nonneg_left (hle a) (mass_nonneg p a)) hf hg

lemma mean_abs_le_one_add_square {α : Type*} {p : PMF α} {f : α → ℝ}
    (hf : HasMean p (fun a => (f a)^2)) :
    mean p (fun a => |f a|) ≤ 1+mean p (fun a => (f a)^2) := by
  have h := mean_le (hasMean_of_square hf).abs ((hasMean_const p 1).add hf)
    (fun a => (show |f a| ≤ 1+(f a)^2 by nlinarith [sq_nonneg (|f a|-1), sq_abs (f a)]))
  simpa only [mean_add (hasMean_const p 1) hf, mean_const] using h

lemma hasMean_bind_square {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) (fun b => (f b)^2))
    (hp : HasMean p (fun a => mean (k a) (fun b => (f b)^2))) :
    HasMean (p.bind k) (fun b => (f b)^2) := by
  apply HasMean.bind hk
  simpa only [abs_sq] using hp

lemma hasMean_bind_abs_of_square {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) (fun b => (f b)^2))
    (hp : HasMean p (fun a => mean (k a) (fun b => (f b)^2))) :
    HasMean p (fun a => mean (k a) (fun b => |f b|)) := by
  exact ((hasMean_const p 1).add hp).mono
    (fun a => mean_nonneg _ (fun b => abs_nonneg _))
    (fun a => mean_abs_le_one_add_square (hk a))

lemma mean_bind_of_square {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) (fun b => (f b)^2))
    (hp : HasMean p (fun a => mean (k a) (fun b => (f b)^2))) :
    mean (p.bind k) f = mean p (fun a => mean (k a) f) :=
  mean_bind (fun a => hasMean_of_square (hk a)) (hasMean_bind_abs_of_square hk hp)

lemma mean_bind_square {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) (fun b => (f b)^2))
    (hp : HasMean p (fun a => mean (k a) (fun b => (f b)^2))) :
    mean (p.bind k) (fun b => (f b)^2) = mean p (fun a => mean (k a) (fun b => (f b)^2)) := by
  apply mean_bind hk
  simpa only [abs_sq] using hp

lemma HasMean.congr {α : Type*} {p : PMF α} {f g : α → ℝ} (hf : HasMean p f)
    (hfg : ∀ a, f a = g a) : HasMean p g := by
  exact Summable.congr hf (fun a => congrArg (fun x => mass p a*x) (hfg a))

lemma mean_congr {α : Type*} (p : PMF α) {f g : α → ℝ} (hfg : ∀ a, f a = g a) :
    mean p f = mean p g := tsum_congr (fun a => congrArg (fun x => mass p a*x) (hfg a))

lemma hasMean_shift_square {α : Type*} {p : PMF α} {f : α → ℝ}
    (hf : HasMean p (fun a => (f a)^2)) (c : ℝ) : HasMean p (fun a => (c+f a)^2) := by
  exact (((hasMean_const p (c^2)).add ((hasMean_of_square hf).const_mul (2*c))).add hf).congr
    (fun a => by ring)

lemma mean_shift_square {α : Type*} {p : PMF α} {f : α → ℝ}
    (hf : HasMean p (fun a => (f a)^2)) (c : ℝ) :
    mean p (fun a => (c+f a)^2) = c^2+2*c*mean p f+mean p (fun a => (f a)^2) := by
  rw [mean_congr p (g := fun a => c^2+(2*c)*f a+(f a)^2) (fun a => by ring),
    mean_add ((hasMean_const p (c^2)).add ((hasMean_of_square hf).const_mul (2*c))) hf,
    mean_add (hasMean_const p (c^2)) ((hasMean_of_square hf).const_mul (2*c)),
    mean_const, mean_const_mul]

lemma hasMean_fintype {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) : HasMean p f :=
  summable_of_hasFiniteSupport (Set.toFinite _)

lemma mean_fintype {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) :
    mean p f = ∑ a, mass p a * f a := tsum_fintype _

 

structure Moments {α : Type*} (p : PMF α) (f : α → ℝ) (m s : ℝ) : Prop where
  square : HasMean p (fun a => (f a)^2)
  first : mean p f = m
  second : mean p (fun a => (f a)^2) = s

lemma Moments.hasMean {α : Type*} {p : PMF α} {f : α → ℝ} {m s : ℝ}
    (h : Moments p f m s) : HasMean p f := hasMean_of_square h.square

lemma Moments.map {α β : Type*} {p : PMF α} {f : β → ℝ} {g : α → β} {m s : ℝ}
    (h : Moments p (fun a => f (g a)) m s) : Moments (p.map g) f m s := by
  refine ⟨HasMean.map (g := g) (f := fun b => (f b)^2) h.square, ?_, ?_⟩
  · exact (mean_map (g := g) (f := f) h.hasMean).trans h.first
  · exact (mean_map (g := g) (f := fun b => (f b)^2) h.square).trans h.second

lemma Moments.pure {α : Type*} (a : α) (f : α → ℝ) :
    Moments (PMF.pure a) f (f a) ((f a)^2) :=
  ⟨hasMean_pure _ _, mean_pure _ _, mean_pure _ _⟩

lemma Moments.shift {α : Type*} {p : PMF α} {f : α → ℝ} {m s : ℝ}
    (h : Moments p f m s) (c : ℝ) :
    Moments p (fun a => c+f a) (c+m) (c^2+2*c*m+s) := by
  refine ⟨hasMean_shift_square h.square c, ?_, ?_⟩
  · rw [mean_add (hasMean_const p c) h.hasMean, mean_const, h.first]
  · rw [mean_shift_square h.square, h.first, h.second]

lemma Moments.bind {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    {m s : α → ℝ} {M S : ℝ} (hk : ∀ a, Moments (k a) f (m a) (s a))
    (hs : HasMean p s) (hm : mean p m = M) (hS : mean p s = S) :
    Moments (p.bind k) f M S := by
  have hp : HasMean p (fun a => mean (k a) (fun b => (f b)^2)) :=
    hs.congr (fun a => (hk a).second.symm)
  refine ⟨hasMean_bind_square (fun a => (hk a).square) hp, ?_, ?_⟩
  · rw [mean_bind_of_square (fun a => (hk a).square) hp]
    simpa only [(hk _).first] using hm
  · rw [mean_bind_square (fun a => (hk a).square) hp]
    simpa only [(hk _).second] using hS

lemma Moments.independent_add {α β : Type*} {p : PMF α} {q : PMF β}
    {f : α → ℝ} {g : β → ℝ} {m s n t : ℝ}
    (hf : Moments p f m s) (hg : Moments q g n t) :
    Moments (p.bind (fun a => q.map (fun b => (a,b))))
      (fun ab => f ab.1+g ab.2) (m+n) (s+2*m*n+t) := by
  apply Moments.bind (m := fun a => f a+n) (s := fun a => (f a)^2+2*f a*n+t)
    (fun a => Moments.map (g := fun b => (a,b)) (f := fun ab => f ab.1+g ab.2) (hg.shift (f a)))
  · exact (hf.square.add (hf.hasMean.mul_const (2*n))).add (hasMean_const p t) |>.congr
      (fun a => by ring)
  · rw [mean_add hf.hasMean (hasMean_const p n), hf.first, mean_const]
  · have he := mean_add (hf.square.add (hf.hasMean.mul_const (2*n))) (hasMean_const p t)
    rw [mean_congr p (g := fun a => ((f a)^2+f a*(2*n))+t) (fun a => by ring), he,
      mean_add hf.square (hf.hasMean.mul_const (2*n)), mean_mul_const, hf.first, hf.second, mean_const]
    ring

end ThreeState
namespace ThreeState

lemma hasMean_bounded {α : Type*} (p : PMF α) {f : α → ℝ} (C : ℝ)
    (hf : ∀ a, |f a| ≤ C) : HasMean p f :=
  HasMean.of_abs ((hasMean_const p C).mono (fun value => abs_nonneg (f value)) hf)

lemma abs_mean_le {α : Type*} (p : PMF α) {f : α → ℝ} (C : ℝ)
    (hf : ∀ a, |f a| ≤ C) : |mean p f| ≤ C := by
  have hi := hasMean_bounded p C hf
  rw [abs_le]
  constructor
  · simpa only [mean_const] using mean_le (hasMean_const p (-C)) hi (fun a => (abs_le.mp (hf a)).1)
  · simpa only [mean_const] using mean_le hi (hasMean_const p C) (fun a => (abs_le.mp (hf a)).2)

lemma mean_bind_bounded {α β : Type*} (p : PMF α) (k : α → PMF β) (f : β → ℝ)
    (C : ℝ) (hf : ∀ b, |f b| ≤ C) :
    mean (p.bind k) f = mean p (fun a => mean (k a) f) := by
  apply mean_bind (fun a => hasMean_bounded (k a) C hf)
  exact hasMean_bounded p C (fun a => abs_mean_le (k a) C (fun b => by simpa using hf b))

lemma mean_map_bounded {α β : Type*} (p : PMF α) (g : α → β) (f : β → ℝ)
    (C : ℝ) (hf : ∀ a, |f (g a)| ≤ C) :
    mean (p.map g) f = mean p (fun a => f (g a)) :=
  mean_map (hasMean_bounded p C hf)

 
noncomputable def joint {α β : Type*} (p : PMF α) (k : α → PMF β) : PMF (α × β) :=
  p.bind (fun a => (k a).map (fun b => (a,b)))

lemma mean_joint_bounded {α β : Type*} (p : PMF α) (k : α → PMF β) (f : α × β → ℝ)
    (C : ℝ) (hf : ∀ ab, |f ab| ≤ C) :
    mean (joint p k) f = mean p (fun a => mean (k a) (fun b => f (a,b))) := by
  rw [joint, mean_bind_bounded p _ f C hf]
  apply mean_congr
  intro a
  exact mean_map_bounded (k a) _ f C (fun b => hf (a,b))

lemma mean_joint_fst {α β : Type*} (p : PMF α) (k : α → PMF β) (f : α → ℝ)
    (C : ℝ) (hf : ∀ a, |f a| ≤ C) :
    mean (joint p k) (fun ab => f ab.1) = mean p f := by
  rw [mean_joint_bounded p k _ C (fun ab => hf ab.1)]
  simp only [mean_const]

lemma mean_joint_snd {α β : Type*} (p : PMF α) (k : α → PMF β) (f : β → ℝ)
    (C : ℝ) (hf : ∀ b, |f b| ≤ C) :
    mean (joint p k) (fun ab => f ab.2) = mean (p.bind k) f := by
  rw [mean_joint_bounded p k _ C (fun ab => hf ab.2), mean_bind_bounded p k f C hf]

end ThreeState

namespace ThreeState

lemma HasMean.sub {α : Type*} {p : PMF α} {f g : α → ℝ}
    (hf : HasMean p f) (hg : HasMean p g) : HasMean p (fun a => f a-g a) := by
  simpa only [HasMean, mul_sub] using Summable.sub hf hg

lemma mean_sub {α : Type*} {p : PMF α} {f g : α → ℝ}
    (hf : HasMean p f) (hg : HasMean p g) :
    mean p (fun a => f a-g a) = mean p f-mean p g := by
  simp only [mean, mul_sub, hf.tsum_sub hg]

lemma poisson_mass (d : ℝ) (hd : 0 ≤ d) (k : ℕ) :
    mass (poissonOffspring d hd) k = Real.exp (-d)*d^k/(k.factorial : ℝ) := by
  change (ENNReal.ofReal _).toReal = _
  apply ENNReal.toReal_ofReal
  positivity

lemma poisson_mass_succ (d : ℝ) (hd : 0 ≤ d) (k : ℕ) :
    mass (poissonOffspring d hd) (k+1) * ((k+1 : ℕ) : ℝ) =
      d*mass (poissonOffspring d hd) k := by
  rw [poisson_mass, poisson_mass, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hk : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma poisson_first_hasSum (d : ℝ) (hd : 0 ≤ d) :
    HasSum (fun k : ℕ => mass (poissonOffspring d hd) k * (k : ℝ)) d := by
  have h : HasSum (fun k : ℕ => mass (poissonOffspring d hd) (k+1) * ((k+1 : ℕ) : ℝ)) d := by
    simpa only [poisson_mass_succ, mass_sum, mul_one] using
      (mass_summable (poissonOffspring d hd)).hasSum.mul_left d
  have hz : mass (poissonOffspring d hd) 0*(0:ℝ) = 0 := mul_zero _
  exact (hasSum_nat_add_iff' 1).mp (by simpa [hz, mass_sum] using h)

lemma poisson_second_factorial_hasSum (d : ℝ) (hd : 0 ≤ d) :
    HasSum (fun k : ℕ => mass (poissonOffspring d hd) k * ((k : ℝ)*((k : ℝ)-1))) (d^2) := by
  have hh (k : ℕ) :
      mass (poissonOffspring d hd) (k+2) * (((k+2 : ℕ) : ℝ)*(((k+2 : ℕ) : ℝ)-1)) =
        d*(mass (poissonOffspring d hd) (k+1) * ((k+1 : ℕ) : ℝ)) := by
    have he := poisson_mass_succ d hd (k+1)
    push_cast at he ⊢
    nlinarith [congrArg (fun x => x*((k:ℝ)+1)) he]
  have h : HasSum (fun k : ℕ =>
      mass (poissonOffspring d hd) (k+2) * (((k+2 : ℕ) : ℝ)*(((k+2 : ℕ) : ℝ)-1))) (d^2) := by
    have h1 : HasSum (fun k : ℕ => mass (poissonOffspring d hd) (k+1) * ((k+1 : ℕ) : ℝ)) d := by
      simpa only [poisson_mass_succ, mass_sum, mul_one] using
        (mass_summable (poissonOffspring d hd)).hasSum.mul_left d
    simpa only [hh, pow_two] using h1.mul_left d
  exact (hasSum_nat_add_iff' 2).mp (by simpa [Finset.sum_range_succ] using h)

 
theorem poisson_moments (d : ℝ) (hd : 0 ≤ d) :
    Moments (poissonOffspring d hd) (fun k : ℕ => (k : ℝ)) d (d^2+d) := by
  have h1 := poisson_first_hasSum d hd
  have h2 := poisson_second_factorial_hasSum d hd
  have hs : HasSum (fun k : ℕ => mass (poissonOffspring d hd) k*(k:ℝ)^2) (d^2+d) := by
    convert h2.add h1 using 1
    funext k
    ring
  exact ⟨hs.summable, h1.tsum_eq, hs.tsum_eq⟩

lemma regular_moments (b : ℕ) :
    Moments (PMF.pure b) (fun k : ℕ => (k : ℝ)) (b:ℝ) ((b:ℝ)^2) :=
  Moments.pure b _

end ThreeState

end OAI
