import Mathlib
import OAI.Probability.LogConcave.Numerics.Picard

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma centersBound_picard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d)
    {A B C W : ℝ} (_hB : 0≤B) (hC : 0≤C) (hw : ∀i,∑j,|w i j|≤B)
    (hφw : ∀i E,weight (φ i E)≤C)
    (haw : ∀i,weight (a i)≤W) (ha : ∀i,centersBound A (a i))
    (hφ : ∀i E,weight E≤W+B*C → centersBound A E → centersBound A (φ i E))
    (N : ℕ) (i : I) : centersBound A (picard w φ a N i) := by
  induction N generalizing i with
  | zero => exact ha i
  | succ N ih =>
    apply (centersBound_add _ _ _).2
    refine ⟨ha i,centersBound_sumFamily _ _ (fun j => ?_)⟩
    apply (centersBound_scale _ _ _).2
    apply hφ j _ ?_ (ih j)
    exact (weight_picard w φ a hC hw hφw N j).trans (add_le_add_left (haw j) _)

lemma probability_weights {r T h P A : ℝ} (hr : 0≤r) (hP : 0≤P) (n N : ℕ)
    (s : ProbabilityNode T h n)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hw : ∀i,∑j,|reanchorWeight (probabilityWeight T h n) s i j|≤P)
    (x y : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y)
    (hA : r*(weight y+P*r)≤A) (i : ProbabilityNode T h n) :
    weight (probability r T h n N s x y i)≤weight y+P*r ∧
      centersBound A (probability r T h n N s x y i) := by
  have hc (j : ProbabilityNode T h n) (E : MeanTree X d) :
      weight (scale (-r) (conditional r (probabilityNodeTime T h n j) x E))≤r := by
    simp [abs_of_nonneg hr]
  constructor
  · exact weight_picard _ _ _ hr hw hc N i
  · apply centersBound_picard _ _ _ hP hr hw hc (fun _ => le_rfl) (fun _ => hy) ?_ N i
    intro j E hE hEb
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx hEb
    rw [hxw,zero_add,abs_mul,abs_of_nonneg hr]
    calc
      r*|probabilityNodeTime T h n j| * weight E≤r*weight E := by
        nlinarith [weight_nonneg E,mul_le_mul_of_nonneg_left (ht j) hr]
      _≤r*(weight y+P*r) := mul_le_mul_of_nonneg_left hE hr
      _≤A := hA

lemma harmonic_weights {r ρ v H A : ℝ} (hr : 0≤r) (hρ : |ρ|≤1) (hH : 0≤H)
    (n N : ℕ) (hw : ∀i,∑j,|harmonicWeight n v i j|≤H)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+H*r)≤A) (i : Fin (n+1)) :
    weight (harmonic r ρ v n N x y g i)≤weight y+weight g+H*r ∧
      centersBound A (harmonic r ρ v n N x y g i) := by
  have hc (j : Fin (n+1)) (E : MeanTree X d) :
      weight (scale ρ (scale (-r) (conditional r ρ x E)))≤r := by
    simp only [weight_scale,weight_conditional,abs_neg,abs_of_nonneg hr,mul_one]
    nlinarith
  have ha (j : Fin (n+1)) : weight (add (scale (Real.cos (v*probabilityNodes n j)) y)
      (scale (Real.sin (v*probabilityNodes n j)) g))≤weight y+weight g := by
    simp only [weight_add,weight_scale]
    exact add_le_add
      (by nlinarith [Real.abs_cos_le_one (v*probabilityNodes n j),weight_nonneg y])
      (by nlinarith [Real.abs_sin_le_one (v*probabilityNodes n j),weight_nonneg g])
  constructor
  · exact (weight_picard _ _ _ hr hw hc N i).trans (add_le_add_left (ha i) _)
  · apply centersBound_picard _ _ _ hH hr hw hc ha
      (fun _ => (centersBound_add _ _ _).2 ⟨(centersBound_scale _ _ _).2 hy,(centersBound_scale _ _ _).2 hg⟩) ?_ N i
    intro j E hE hEb
    apply (centersBound_scale _ _ _).2
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx hEb
    rw [hxw,zero_add,abs_mul,abs_of_nonneg hr]
    calc
      r*|ρ| * weight E≤r*weight E := by nlinarith [weight_nonneg E,mul_le_mul_of_nonneg_left hρ hr]
      _≤r*(weight y+weight g+H*r) := mul_le_mul_of_nonneg_left hE hr
      _≤A := hA

lemma kernelCorrection_weights {r T h v P H A : ℝ} (hr : 0≤r) (hP : 0≤P) (hH : 0≤H)
    (n N : ℕ) (s e : ProbabilityNode T h n)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hpw : ∀s i,∑j,|reanchorWeight (probabilityWeight T h n) s i j|≤P)
    (hhw : ∀i,∑j,|harmonicWeight n v i j|≤H)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+(2*P+H)*r)≤A) :
    weight (kernelCorrection r T h v n N s e x y g)≤P*r ∧
      centersBound A (kernelCorrection r T h v n N s e x y g) := by
  have hB : r*(weight y+P*r)≤A := by
    apply le_trans _ hA
    apply mul_le_mul_of_nonneg_left _ hr
    nlinarith [weight_nonneg g]
  have hb := probability_weights hr hP n N e ht (hpw e) x y hxw hx hy hB s
  let b := probability r T h n N e x y s
  have hW : r*(weight b+weight g+H*r)≤A := by
    apply le_trans _ hA
    apply mul_le_mul_of_nonneg_left _ hr
    dsimp only [b]
    nlinarith [hb.1]
  have hw := harmonic_weights hr (ht s) hH n N hhw x b g hxw hx hb.2 hg hW (Fin.last n)
  let w := harmonic r (probabilityNodeTime T h n s) v n N x b g (Fin.last n)
  have hF : r*(weight w+P*r)≤A := by
    apply le_trans _ hA
    apply mul_le_mul_of_nonneg_left _ hr
    dsimp only [w]
    nlinarith [hw.1,hb.1]
  have hf (j : ProbabilityNode T h n) := probability_weights hr hP n N s ht (hpw s) x w hxw hx hw.2 hF j
  constructor
  · simp only [kernelCorrection,weight_sumFamily,weight_scale,weight_conditional,abs_neg,abs_of_nonneg hr,mul_one]
    rw [←Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hpw s e) hr
  · unfold kernelCorrection
    change centersBound A (sumFamily (fun j => scale (reanchorWeight (probabilityWeight T h n) s e j) (scale (-r) (conditional r (probabilityNodeTime T h n j) x (probability r T h n N s x w j)))))
    apply centersBound_sumFamily
    intro j
    apply (centersBound_scale _ _ _).2
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx (hf j).2
    rw [hxw,zero_add,abs_mul,abs_of_nonneg hr]
    apply le_trans _ hF
    calc
      r*|probabilityNodeTime T h n j| * weight (probability r T h n N s x w j)
        ≤r*weight (probability r T h n N s x w j) := by
          nlinarith [weight_nonneg (probability r T h n N s x w j),mul_le_mul_of_nonneg_left (ht j) hr]
      _≤r*(weight w+P*r) := mul_le_mul_of_nonneg_left (hf j).1 hr

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma kernelQuadrature_weights {r T h ψ P H A Q S : ℝ}
    (hr : 0≤r) (hP : 0≤P) (hH : 0≤H) (_hQ : 0≤Q) (hS : 0≤S)
    (n m N : ℕ) (e : ProbabilityNode T h n) (w : ProbabilityNode T h n → ℝ)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hpw : ∀s i,∑j,|reanchorWeight (probabilityWeight T h n) s i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight n (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|w j|≤Q) (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+(2*P+H)*r)≤A) :
    weight (kernelQuadrature r T h ψ n m N e w x y g)≤Q*S*(P*r) ∧
      centersBound A (kernelQuadrature r T h ψ n m N e w x y g) := by
  have hc (j : ProbabilityNode T h n) (k : Fin (m+1)) :=
    kernelCorrection_weights hr hP hH n N j e ht hpw (hhw k) x y g hxw hx hy hg hA
  have ha (j : ProbabilityNode T h n) : weight (kernelAction r T h ψ n m N j e x y g)≤S*(P*r) := by
    simp only [kernelAction,weight_sumFamily,weight_scale]
    calc
      _≤∑k,|derivativeWeight (angleNodes m) k/ψ| * (P*r) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hc j k).1 (abs_nonneg _))
      _=(∑k,|derivativeWeight (angleNodes m) k/ψ|)*(P*r) := (Finset.sum_mul _ _ _).symm
      _≤S*(P*r) := mul_le_mul_of_nonneg_right hsw (mul_nonneg hP hr)
  constructor
  · simp only [kernelQuadrature,weight_sumFamily,weight_scale]
    calc
      _≤∑j,|w j| * (S*(P*r)) := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (ha j) (abs_nonneg _))
      _=(∑j,|w j|)*(S*(P*r)) := (Finset.sum_mul _ _ _).symm
      _≤Q*(S*(P*r)) := mul_le_mul_of_nonneg_right hqw (by positivity)
      _=Q*S*(P*r) := by ring
  · apply centersBound_sumFamily
    intro j
    apply (centersBound_scale _ _ _).2
    apply centersBound_sumFamily
    intro k
    exact (centersBound_scale _ _ _).2 (hc j k).2

lemma velocity_weights {r T h ψ s P H A Q S : ℝ}
    (hr : 0<r) (hs : 0<s) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S)
    (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀s i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) s i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (x : MeanTree X d) (p : MeanTree X d × MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A p.1) (hg : centersBound A p.2)
    (hA : r*(weight p.1+weight p.2+(2*P+H)*r)≤A) :
    weight (velocity r T h ψ s n m N e x p).1+
      weight (velocity r T h ψ s n m N e x p).2≤(Q*S*P+2)/s ∧
    centersBound A (velocity r T h ψ s n m N e x p).1 ∧
      centersBound A (velocity r T h ψ s n m N e x p).2 := by
  have hk := kernelQuadrature_weights hr.le hP hH hQ hS n.succ m N e _ ht hpw hhw hqw hsw x p.1 p.2 hxw hx hy hg hA
  have hA0 : 0≤A := (mul_nonneg hr.le (by positivity [weight_nonneg p.1,weight_nonneg p.2])).trans hA
  constructor
  · simp only [velocity,weight_scale,weight_add,weight_conditional,weight_mean,
      abs_neg,abs_one,one_mul,abs_inv,abs_mul,abs_of_pos hr,abs_of_pos hs]
    apply le_trans (add_le_add_left (mul_le_mul_of_nonneg_left hk.1 (by positivity)) _)
    have he : (r*s)⁻¹*(Q*S*(P*r))+s⁻¹*(1+1)=(Q*S*P+2)/s := by field_simp; ring
    exact he.le
  · constructor
    · exact (centersBound_scale _ _ _).2 hk.2
    · dsimp only [velocity]
      apply (centersBound_scale _ _ _).2
      apply (centersBound_add _ _ _).2
      constructor
      · apply centersBound_conditional hx hy
        rw [hxw,zero_add,abs_mul,abs_of_pos hr]
        calc
          r*|T| * weight p.1≤r*weight p.1 := by nlinarith [weight_nonneg p.1,mul_le_mul_of_nonneg_left hT hr.le]
          _≤r*(weight p.1+weight p.2+(2*P+H)*r) := by
            apply mul_le_mul_of_nonneg_left _ hr.le
            linarith [weight_nonneg p.2,mul_nonneg (show 0≤2*P+H by positivity) hr.le]
          _≤A := hA
      · apply (centersBound_scale _ _ _).2
        exact (centersBound_mean _ _ _).2 ⟨by simpa [hxw] using hA0,hx⟩

lemma weight_velocity_input_independent (r T h ψ s : ℝ) (n m N : ℕ)
    (e : ProbabilityNode T h (n+1)) (x z : MeanTree X d)
    (p q : MeanTree X d × MeanTree X d) :
    weight (velocity r T h ψ s n m N e x p).1+weight (velocity r T h ψ s n m N e x p).2=
    weight (velocity r T h ψ s n m N e z q).1+weight (velocity r T h ψ s n m N e z q).2 := by
  simp only [velocity,weight_scale,weight_add,weight_mean,weight_conditional,
    kernelQuadrature,kernelAction,kernelCorrection,weight_sumFamily]

lemma velocity_root_weights {r T h ψ s P H Q S : ℝ}
    (hr : 0<r) (hs : 0<s) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S)
    (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀s i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) s i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (x : MeanTree X d) (p : MeanTree X d × MeanTree X d) :
    weight (velocity r T h ψ s n m N e x p).1+
      weight (velocity r T h ψ s n m N e x p).2≤(Q*S*P+2)/s := by
  rw [weight_velocity_input_independent r T h ψ s n m N e x zero p (zero,zero)]
  exact (velocity_weights (A:=r*((2*P+H)*r)) hr hs hT hP hH hQ hS n m N e ht hpw hhw hqw hsw
    zero (zero,zero) (by simp) (by simp) (by simp) (by simp) (by simp)).1

lemma pairPicard_weights {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) {B K : ℝ} (hB : 0≤B) (hK : 0≤K)
    (hw : ∀i,∑j,|w i j|≤B)
    (hφ : ∀p,weight (φ p).1+weight (φ p).2≤K) (N : ℕ) (i : I) :
    weight (pairPicard w φ a N i).1+weight (pairPicard w φ a N i).2≤
      weight a.1+weight a.2+B*K := by
  cases N with
  | zero => simpa only [pairPicard] using le_add_of_nonneg_right (a:=weight a.1+weight a.2) (mul_nonneg hB hK)
  | succ N =>
    simp only [pairPicard,weight_add,weight_sumFamily,weight_scale]
    have he : (∑j,|w i j| * weight (φ (pairPicard w φ a N j)).1)+
        (∑j,|w i j| * weight (φ (pairPicard w φ a N j)).2)≤B*K := by
      rw [←Finset.sum_add_distrib]
      calc
        _≤∑j,|w i j| * K := Finset.sum_le_sum (fun j _ => by rw [←mul_add]; exact mul_le_mul_of_nonneg_left (hφ _) (abs_nonneg _))
        _=(∑j,|w i j|)*K := (Finset.sum_mul _ _ _).symm
        _≤B*K := mul_le_mul_of_nonneg_right (hw i) hK
    linarith

lemma centersBound_pairPicard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) {A B K : ℝ} (hB : 0≤B) (hK : 0≤K)
    (hw : ∀i,∑j,|w i j|≤B)
    (hφw : ∀p,weight (φ p).1+weight (φ p).2≤K)
    (ha : centersBound A a.1 ∧ centersBound A a.2)
    (hφ : ∀p,weight p.1+weight p.2≤weight a.1+weight a.2+B*K →
      centersBound A p.1 → centersBound A p.2 →
      centersBound A (φ p).1 ∧ centersBound A (φ p).2) (N : ℕ) (i : I) :
    centersBound A (pairPicard w φ a N i).1 ∧ centersBound A (pairPicard w φ a N i).2 := by
  induction N generalizing i with
  | zero => exact ha
  | succ N ih =>
    have hstep (j : I) := hφ _ (pairPicard_weights w φ a hB hK hw hφw N j) (ih j).1 (ih j).2
    exact ⟨(centersBound_add _ _ _).2 ⟨ha.1,centersBound_sumFamily _ _ (fun j => (centersBound_scale _ _ _).2 (hstep j).1)⟩,
      (centersBound_add _ _ _).2 ⟨ha.2,centersBound_sumFamily _ _ (fun j => (centersBound_scale _ _ _).2 (hstep j).2)⟩⟩
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem centeringStates_weights {r T h ψ s P H Q S B A : ℝ}
    (hr : 0<r) (hs : 0<s) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S) (hB : 0≤B)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀a i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) a i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (hcw : ∀i,∑j,|centeringWeight nc i j|≤B)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+B*((Q*S*P+2)/s)+(2*P+H)*r)≤A)
    (i : Fin (nc+1)) :
    weight (centeringStates r T h ψ s n m N nc Nc e x y g i).1+
      weight (centeringStates r T h ψ s n m N nc Nc e x y g i).2≤
        weight y+weight g+B*((Q*S*P+2)/s) ∧
    centersBound A (centeringStates r T h ψ s n m N nc Nc e x y g i).1 ∧
      centersBound A (centeringStates r T h ψ s n m N nc Nc e x y g i).2 := by
  have hK : 0≤(Q*S*P+2)/s := by positivity
  have hφ := velocity_root_weights (X:=X) (d:=d) hr hs hT hP hH hQ hS n m N e ht hpw hhw hqw hsw x
  constructor
  · exact pairPicard_weights _ _ (y,g) hB hK hcw hφ Nc i
  · apply centersBound_pairPicard _ _ (y,g) hB hK hcw hφ ⟨hy,hg⟩ _ Nc i
    intro p hp hpy hpg
    exact (velocity_weights hr hs hT hP hH hQ hS n m N e ht hpw hhw hqw hsw x p hxw hx hpy hpg
      ((mul_le_mul_of_nonneg_left (add_le_add_left hp _) hr.le).trans hA)).2

theorem meanCircuit_weights {r T h ψ s P H Q S B A : ℝ}
    (hr : 0<r) (hs : 0<s) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S) (hB : 0≤B)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀a i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) a i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (hcw : ∀i,∑j,|centeringWeight nc i j|≤B)
    (hout : ∑j,|Quadrature.weight (probabilityNodes nc) j 0 1|≤B)
    (x y g : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y) (hg : centersBound A g)
    (hA : r*(weight y+weight g+B*((Q*S*P+2)/s)+(2*P+H)*r)≤A) :
    weight (meanCircuit r T h ψ s n m N nc Nc e x y g)≤|s| * weight g+B ∧
      centersBound A (meanCircuit r T h ψ s n m N nc Nc e x y g) := by
  have hz := centeringStates_weights hr hs hT hP hH hQ hS hB n m N nc Nc e ht hpw hhw hqw hsw hcw x y g hxw hx hy hg hA
  constructor
  · simpa only [meanCircuit,weight_add,weight_scale,weight_sumFamily,weight_conditional,mul_one]
      using add_le_add_right hout (|s| * weight g)
  · apply (centersBound_add _ _ _).2
    refine ⟨(centersBound_scale _ _ _).2 hg,centersBound_sumFamily _ _ ?_⟩
    intro j
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx (hz j).2.1
    rw [hxw,zero_add,abs_mul,abs_of_pos hr]
    calc
      r*|T| * weight (centeringStates r T h ψ s n m N nc Nc e x y g j).1
          ≤r*weight (centeringStates r T h ψ s n m N nc Nc e x y g j).1 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hr.le) (weight_nonneg (centeringStates r T h ψ s n m N nc Nc e x y g j).1)
      _≤r*(weight y+weight g+B*((Q*S*P+2)/s)+(2*P+H)*r) := by
        apply mul_le_mul_of_nonneg_left _ hr.le
        have hb := (hz j).1
        linarith [weight_nonneg (centeringStates r T h ψ s n m N nc Nc e x y g j).2,
          mul_nonneg (show 0≤2*P+H by positivity) hr.le]
      _≤A := hA
end LogConcaveSampling.MeanTree

end

end

end OAI
