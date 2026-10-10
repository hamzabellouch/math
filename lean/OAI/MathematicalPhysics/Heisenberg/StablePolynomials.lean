import OAI.MathematicalPhysics.Heisenberg.PolynomialLimits

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter Metric

namespace Heisenberg.Pin

def Upper {σ : Type*} : Set (σ → ℂ) := {z | ∀ j, 0 < (z j).im}

def Stable {σ : Type*} (p : MvPolynomial σ ℂ) : Prop :=
  ∀ z ∈ Upper, MvPolynomial.eval z p ≠ 0

lemma isOpen_upper {σ : Type*} [Finite σ] : IsOpen (Upper (σ := σ)) := by
  have he : Upper (σ := σ) = ⋂ j : σ, {z | 0 < (z j).im} := by ext; simp [Upper]
  rw [he]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const
    (Complex.continuous_im.comp (continuous_apply j))

def linePolynomial {σ : Type*} (p : MvPolynomial σ ℂ) (z v : σ → ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C (fun j => Polynomial.C (z j) +
    Polynomial.X * Polynomial.C (v j)) p

lemma linePolynomial_eval {σ : Type*} (p : MvPolynomial σ ℂ) (z v : σ → ℂ) (t : ℂ) :
    (linePolynomial p z v).eval t = MvPolynomial.eval (fun j => z j + t * v j) p := by
  unfold linePolynomial
  rw [MvPolynomial.polynomial_eval_eval₂]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by ext; simp
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, hc, MvPolynomial.eval₂_id]

lemma eval_sum_of_support_subset {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ)
    (s : Finset (σ →₀ ℕ)) (hp : p.support ⊆ s) (z : σ → ℂ) :
    MvPolynomial.eval z p = ∑ a ∈ s, p.coeff a * ∏ j, (z j) ^ (a j) := by
  rw [MvPolynomial.eval_eq']
  exact Finset.sum_subset hp fun a _ ha => by
    have hz : p.coeff a = 0 := by simpa [MvPolynomial.mem_support_iff] using ha
    rw [hz, zero_mul]

lemma locallyUniform_const {ι X : Type*} [TopologicalSpace X] (φ : Filter ι)
    (f : X → ℂ) (U : Set X) : TendstoLocallyUniformlyOn (fun _ => f) f φ U := by
  apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  exact Filter.Eventually.of_forall fun _ x _ => by simpa using hε

lemma locallyUniform_finset_sum {ι X κ : Type*} [TopologicalSpace X] (φ : Filter ι)
    (U : Set X) (s : Finset κ) (F : κ → ι → X → ℂ) (f : κ → X → ℂ)
    (h : ∀ a ∈ s, TendstoLocallyUniformlyOn (F a) (f a) φ U) :
    TendstoLocallyUniformlyOn (fun i x => ∑ a ∈ s, F a i x)
      (fun x => ∑ a ∈ s, f a x) φ U := by
  induction s using Finset.induction_on with
  | empty => simpa using locallyUniform_const φ (fun _ : X => (0 : ℂ)) U
  | @insert a s ha ih =>
    have h₁ := h a (Finset.mem_insert_self _ _)
    have h₂ := ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
    simp only [Finset.sum_insert ha]
    exact h₁.add h₂

lemma coefficient_limit_locallyUniform {ι σ X : Type*} [Fintype σ] [TopologicalSpace X]
    {φ : Filter ι} {P : ι → MvPolynomial σ ℂ} {p : MvPolynomial σ ℂ}
    (s : Finset (σ →₀ ℕ)) (hP : ∀ i, (P i).support ⊆ s) (hp : p.support ⊆ s)
    (hc : ∀ a ∈ s, Tendsto (fun i => (P i).coeff a) φ
      (𝓝 (p.coeff a))) (z : X → σ → ℂ) (hz : Continuous z) (U : Set X) :
    TendstoLocallyUniformlyOn (fun i x => MvPolynomial.eval (z x) (P i))
      (fun x => MvPolynomial.eval (z x) p) φ U := by
  simp_rw [eval_sum_of_support_subset _ s (hP _), eval_sum_of_support_subset _ s hp]
  apply locallyUniform_finset_sum
  intro a ha
  apply TendstoLocallyUniformlyOn.mul₀
  · exact ((hc a ha).tendstoUniformlyOn_const U).tendstoLocallyUniformlyOn
  · exact locallyUniform_const φ _ U
  · exact continuousOn_const
  · exact (continuous_finsetProd _ fun j _ => ((continuous_apply j).comp hz).pow _).continuousOn

theorem stable_coefficient_limit {ι σ : Type*} [Fintype σ] {φ : Filter ι} [φ.NeBot]
    {P : ι → MvPolynomial σ ℂ} {p : MvPolynomial σ ℂ} (hp0 : p ≠ 0)
    (s : Finset (σ →₀ ℕ)) (hP : ∀ i, (P i).support ⊆ s) (hp : p.support ⊆ s)
    (hc : ∀ a ∈ s, Tendsto (fun i => (P i).coeff a) φ
      (𝓝 (p.coeff a))) (hstable : ∀ᶠ i in φ, Stable (P i)) : Stable p := by
  obtain ⟨w, hw⟩ : ∃ w, MvPolynomial.eval w p ≠ 0 := by
    by_contra h
    apply hp0
    apply MvPolynomial.funext
    simpa using (not_exists.mp h)
  intro z hz
  let v : σ → ℂ := fun j => w j - z j
  let f : ℂ → σ → ℂ := fun t j => z j + t * v j
  have hf : Continuous f := by fun_prop
  let U : Set ℂ := f ⁻¹' Upper
  have hU : IsOpen U := isOpen_upper.preimage hf
  have hzero : (0 : ℂ) ∈ U := by simpa [U, f, Upper] using hz
  have hp' : linePolynomial p z v ≠ 0 := by
    intro h
    have he := congrArg (fun q : Polynomial ℂ => q.eval 1) h
    simp only [linePolynomial_eval, one_mul, Polynomial.eval_zero] at he
    have hv : (fun j => z j + v j) = w := by funext j; dsimp [v]; ring
    rw [hv] at he
    exact hw he
  have hval := polynomial_nonvanishing_limit (φ := φ)
    (F := fun i t => (linePolynomial (P i) z v).eval t) hp' hU
    (Eventually.of_forall fun i => (linePolynomial (P i) z v).differentiable.differentiableOn)
    (by
      filter_upwards [hstable] with i hi t ht
      rw [linePolynomial_eval]
      exact hi (f t) ht)
    (by
      simp_rw [linePolynomial_eval]
      exact coefficient_limit_locallyUniform s hP hp hc f hf U) 0 hzero
  simpa only [linePolynomial_eval, zero_mul, add_zero] using hval

theorem stable_locallyUniform_limit {ι σ : Type*} [Fintype σ] {φ : Filter ι} [φ.NeBot]
    {P : ι → MvPolynomial σ ℂ} {p : MvPolynomial σ ℂ} (hp0 : p ≠ 0)
    (hc : TendstoLocallyUniformlyOn (fun i z => MvPolynomial.eval z (P i))
      (fun z => MvPolynomial.eval z p) φ Upper)
    (hstable : ∀ᶠ i in φ, Stable (P i)) : Stable p := by
  obtain ⟨w, hw⟩ : ∃ w, MvPolynomial.eval w p ≠ 0 := by
    by_contra h
    apply hp0
    apply MvPolynomial.funext
    simpa using (not_exists.mp h)
  intro z hz
  let v : σ → ℂ := fun j => w j - z j
  let f : ℂ → σ → ℂ := fun t j => z j + t * v j
  have hf : Continuous f := by fun_prop
  let U : Set ℂ := f ⁻¹' Upper
  have hU : IsOpen U := isOpen_upper.preimage hf
  have hzero : (0 : ℂ) ∈ U := by simpa [U, f, Upper] using hz
  have hp' : linePolynomial p z v ≠ 0 := by
    intro h
    have he := congrArg (fun q : Polynomial ℂ => q.eval 1) h
    simp only [linePolynomial_eval, one_mul, Polynomial.eval_zero] at he
    have hv : (fun j => z j + v j) = w := by funext j; dsimp [v]; ring
    rw [hv] at he
    exact hw he
  have hval := polynomial_nonvanishing_limit (φ := φ)
    (F := fun i t => (linePolynomial (P i) z v).eval t) hp' hU
    (Eventually.of_forall fun i => (linePolynomial (P i) z v).differentiable.differentiableOn)
    (by
      filter_upwards [hstable] with i hi t ht
      rw [linePolynomial_eval]
      exact hi (f t) ht)
    (by
      simp_rw [linePolynomial_eval]
      exact hc.comp f (fun _ ht => ht) hf.continuousOn) 0 hzero
  simpa only [linePolynomial_eval, zero_mul, add_zero] using hval

lemma locallyUniform_eval {ι σ X : Type*} [TopologicalSpace X] {φ : Filter ι}
    {z : ι → X → σ → ℂ} {w : X → σ → ℂ} {U : Set X}
    (hz : ∀ j, TendstoLocallyUniformlyOn (fun i x => z i x j) (fun x => w x j) φ U)
    (hw : ContinuousOn w U) (p : MvPolynomial σ ℂ) :
    TendstoLocallyUniformlyOn (fun i x => MvPolynomial.eval (z i x) p)
      (fun x => MvPolynomial.eval (w x) p) φ U := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using locallyUniform_const φ (fun _ : X => c) U
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul₀ (hz j) (p.continuous_eval.comp_continuousOn hw)
      ((continuous_apply j).comp_continuousOn hw)

def specialize {σ : Type*} (p : MvPolynomial σ ℂ) (j : σ) (t : ℂ) : MvPolynomial σ ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C (fun k => if k = j then MvPolynomial.C t
    else MvPolynomial.X k) p

lemma eval_specialize {σ : Type*} (p : MvPolynomial σ ℂ) (j : σ) (t : ℂ) (z : σ → ℂ) :
    MvPolynomial.eval z (specialize p j t) = MvPolynomial.eval (Function.update z j t) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [specialize]
  | add p q hp hq => simpa only [specialize, MvPolynomial.eval₂_add, map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p k hp =>
    simp only [specialize, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, MvPolynomial.eval_X]
    rw [show MvPolynomial.eval₂ MvPolynomial.C
      (fun k => if k = j then MvPolynomial.C t else MvPolynomial.X k) p = specialize p j t from rfl,
      hp]
    congr 1
    by_cases h : k = j <;> simp [h, Function.update]

theorem stable_specialize_real {σ : Type*} [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : Stable p) (j : σ) (a : ℝ) :
    specialize p j (a : ℂ) = 0 ∨ Stable (specialize p j (a : ℂ)) := by
  by_cases hzero : specialize p j (a : ℂ) = 0
  · exact Or.inl hzero
  right
  let t : ℝ → ℂ := fun r => (a : ℂ) + (r : ℂ) * Complex.I
  have ht : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 (a : ℂ)) := by
    have h : Continuous t := by fun_prop
    simpa [t] using (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  apply stable_locallyUniform_limit (φ := 𝓝[>] (0 : ℝ))
    (P := fun r => specialize p j (t r)) hzero
  · simp_rw [eval_specialize]
    apply locallyUniform_eval
    · intro k
      by_cases hk : k = j
      · subst k
        simpa using (ht.tendstoUniformlyOn_const Upper).tendstoLocallyUniformlyOn
      · simpa [Function.update_of_ne hk] using
          locallyUniform_const (𝓝[>] (0 : ℝ)) (fun z : σ → ℂ => z k) Upper
    · apply Continuous.continuousOn
      apply continuous_pi
      intro k
      by_cases hk : k = j
      · subst k; simpa using (continuous_const : Continuous (fun _ : σ → ℂ => (a : ℂ)))
      · simpa [Function.update_of_ne hk] using continuous_apply k
  · filter_upwards [self_mem_nhdsWithin] with r hr z hz
    rw [eval_specialize]
    apply hp
    intro k
    by_cases hk : k = j
    · subst k
      simpa [t] using hr
    · simpa [Function.update_of_ne hk] using hz k

def variablePolynomial {σ : Type*} (p : MvPolynomial σ ℂ) (z : σ → ℂ) (j : σ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C (fun k => if k = j then Polynomial.X
    else Polynomial.C (z k)) p

lemma variablePolynomial_eval {σ : Type*} (p : MvPolynomial σ ℂ) (z : σ → ℂ)
    (j : σ) (t : ℂ) :
    (variablePolynomial p z j).eval t = MvPolynomial.eval (Function.update z j t) p := by
  unfold variablePolynomial
  rw [MvPolynomial.polynomial_eval_eval₂]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by ext; simp
  rw [hc, MvPolynomial.eval₂_id]
  congr 2
  funext k
  by_cases h : k = j <;> simp [h, Function.update]

lemma variablePolynomial_pderiv {σ : Type*} (p : MvPolynomial σ ℂ) (z : σ → ℂ) (j : σ) :
    variablePolynomial (MvPolynomial.pderiv j p) z j =
    (variablePolynomial p z j).derivative := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [variablePolynomial]
  | add p q hp hq =>
    simpa only [map_add, variablePolynomial, MvPolynomial.eval₂_add, Polynomial.derivative_add]
      using congrArg₂ (· + ·) hp hq
  | mul_X p k hp =>
    simp only [MvPolynomial.pderiv_mul, variablePolynomial, MvPolynomial.eval₂_add,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Polynomial.derivative_mul]
    rw [show MvPolynomial.eval₂ Polynomial.C
      (fun k => if k = j then Polynomial.X else Polynomial.C (z k)) (MvPolynomial.pderiv j p) =
      variablePolynomial (MvPolynomial.pderiv j p) z j from rfl, hp]
    by_cases h : k = j
    · subst k
      simp [variablePolynomial]
    · simp [h, MvPolynomial.pderiv_X_of_ne h, variablePolynomial]

lemma polynomial_logDerivative_im_nonpos {p : Polynomial ℂ}
    (hp : ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    (p.derivative.eval z / p.eval z).im ≤ 0 := by
  have hpz := hp z hz
  have hp0 : p ≠ 0 := by intro h; simp [h] at hpz
  rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hpz]
  have hterm : ∀ w ∈ p.roots, (1 / (z - w)).im ≤ 0 := by
    intro w hw
    have hw0 : p.eval w = 0 := (Polynomial.mem_roots hp0).mp hw
    have hwim : w.im ≤ 0 := by
      by_contra h
      exact hp w (lt_of_not_ge h) hw0
    rw [one_div, Complex.inv_im]
    apply div_nonpos_of_nonpos_of_nonneg
    · simp only [Complex.sub_im]
      linarith
    · exact Complex.normSq_nonneg _
  generalize p.roots = s at *
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons w s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
    exact add_nonpos (hterm w (Multiset.mem_cons_self _ _))
      (ih (fun v hv => hterm v (Multiset.mem_cons_of_mem hv)))

lemma stable_add_imaginary_derivative {σ : Type*} {p : MvPolynomial σ ℂ}
    (hp : Stable p) (j : σ) {r : ℝ} (hr : 0 < r) :
    Stable (MvPolynomial.C (r : ℂ) * p + MvPolynomial.C Complex.I * MvPolynomial.pderiv j p) := by
  intro z hz heq
  have hpz := hp z hz
  let q := variablePolynomial p z j
  have hq : ∀ t : ℂ, 0 < t.im → q.eval t ≠ 0 := by
    intro t ht
    rw [variablePolynomial_eval]
    apply hp
    intro k
    by_cases hk : k = j
    · subst k; simpa using ht
    · simpa [Function.update_of_ne hk] using hz k
  have hlog := polynomial_logDerivative_im_nonpos hq (hz j)
  have hv : Function.update z j (z j) = z := Function.update_eq_self j z
  rw [show q = variablePolynomial p z j from rfl,
    ← variablePolynomial_pderiv, variablePolynomial_eval, variablePolynomial_eval, hv] at hlog
  simp only [map_add, map_mul, MvPolynomial.eval_C] at heq
  have hdiv : (r : ℂ) + Complex.I *
      (MvPolynomial.eval z (MvPolynomial.pderiv j p) / MvPolynomial.eval z p) = 0 := by
    apply (mul_left_inj' hpz).mp
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hpz, zero_mul]
    exact heq
  have hreal := congrArg Complex.re hdiv
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub, Complex.zero_re] at hreal
  linarith

theorem stable_pderiv {σ : Type*} [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : Stable p) (j : σ) : MvPolynomial.pderiv j p = 0 ∨ Stable (MvPolynomial.pderiv j p) := by
  by_cases hzero : MvPolynomial.pderiv j p = 0
  · exact Or.inl hzero
  right
  let q := MvPolynomial.C Complex.I * MvPolynomial.pderiv j p
  have hq0 : q ≠ 0 := mul_ne_zero (MvPolynomial.C_ne_zero.mpr Complex.I_ne_zero) hzero
  have hc : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hq : Stable q := by
    apply stable_locallyUniform_limit (φ := 𝓝[>] (0 : ℝ))
      (P := fun r => MvPolynomial.C (r : ℂ) * p + q) hq0
    · have hconv := ((hc.tendstoUniformlyOn_const Upper).tendstoLocallyUniformlyOn.mul₀
        (locallyUniform_const (𝓝[>] (0 : ℝ)) (fun z => MvPolynomial.eval z p) Upper)
        continuousOn_const p.continuous_eval.continuousOn).add
        (locallyUniform_const (𝓝[>] (0 : ℝ)) (fun z => MvPolynomial.eval z q) Upper)
      change TendstoLocallyUniformlyOn
        (fun (r : ℝ) (z : σ → ℂ) => (r : ℂ) * MvPolynomial.eval z p + MvPolynomial.eval z q)
        (fun z => (0 : ℂ) * MvPolynomial.eval z p + MvPolynomial.eval z q)
        (𝓝[>] (0 : ℝ)) Upper at hconv
      simpa only [zero_mul, zero_add, map_add, map_mul, MvPolynomial.eval_C] using hconv
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact stable_add_imaginary_derivative hp j hr
  intro z hz hv
  apply hq z hz
  simp [q, hv]

end Heisenberg.Pin
end

end OAI
