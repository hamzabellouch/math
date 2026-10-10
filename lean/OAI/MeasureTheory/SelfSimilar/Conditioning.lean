import OAI.MeasureTheory.SelfSimilar.UpperBound

namespace OAI

universe uα uβ

namespace EntropyRateDimension.FairPairs
open MeasureTheory FiniteEntropy
open scoped BigOperators ENNReal

noncomputable def Law.ofObservable {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) : Law := by
  classical
  exact ⟨s.image f, mass s p f, by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.sum_pos' (fun a ha => (hp a (Finset.mem_filter.mp ha).1).le)
      ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩,hp a ha⟩,
    (mass_sum s p f).trans hp1⟩

@[simp] theorem Law.ofObservable_support {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) :
    (Law.ofObservable s p hp hp1 f).support=s.image f := rfl

@[simp] theorem Law.ofObservable_prob {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) :
    (Law.ofObservable s p hp hp1 f).prob=mass s p f := rfl

@[simp] theorem Law.ofObservable_entropy {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) :
    (Law.ofObservable s p hp hp1 f).shannonEntropy=observableEntropy s p f/Real.log 2 := rfl

@[simp] theorem Law.ofObservable_gridEntropy {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) (ρ : ℝ) :
    (Law.ofObservable s p hp hp1 f).gridEntropy ρ=
      observableEntropy s p (fun a => ⌊f a/ρ⌋)/Real.log 2 := by
  classical
  unfold Law.gridEntropy
  change observableEntropy (s.image f) (mass s p f) (fun x => ⌊x/ρ⌋)/_=_
  rw [← observableEntropy_comp]
  rfl

theorem Law.smul_sum_ofObservable {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ)
    (F : ℝ → Measure ℝ) :
    (∑ x : (Law.ofObservable s p hp hp1 f).support,
      ENNReal.ofReal ((Law.ofObservable s p hp hp1 f).prob x) • F x) =
      ∑ a ∈ s, ENNReal.ofReal (p a) • F (f a) := by
  classical
  change (∑ x : s.image f, ENNReal.ofReal (mass s p f x) • F x)=_
  rw [Finset.sum_coe_sort (s.image f) (fun x => ENNReal.ofReal (mass s p f x) • F x)]
  change (∑ x ∈ s.image f, ENNReal.ofReal (mass s p f x) • F x)=_
  simp only [mass,ENNReal.ofReal_sum_of_nonneg (fun a ha => (hp a (Finset.mem_filter.mp ha).1).le),
    Finset.sum_smul]
  calc
    _ = ∑ x ∈ s.image f, ∑ a ∈ s.filter (fun a => f a=x), ENNReal.ofReal (p a) • F (f a) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) _

end EntropyRateDimension.FairPairs

namespace EntropyRateDimension.FiniteCondition
open FiniteEntropy FairPairs MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def fiber (tag : α → β) (a : α) : Finset α :=
  Finset.univ.filter (fun v => tag v=tag a)

noncomputable def mass (p : α → ℝ) (tag : α → β) (a : α) : ℝ :=
  ∑ v ∈ fiber tag a, p v

theorem mass_pos (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α) :
    0 < mass p tag a := by
  classical
  exact Finset.sum_pos' (fun v _ => (hp v).le) ⟨a,by simp [fiber],hp a⟩

theorem mass_eq_of_tag (p : α → ℝ) (tag : α → β) {a v : α} (h : tag a=tag v) :
    mass p tag a=mass p tag v := by simp only [mass,fiber,h]

noncomputable def posterior (p : α → ℝ) (tag : α → β) (a v : α) : ℝ :=
  if tag v=tag a then p v/mass p tag a else 0

theorem posterior_nonneg (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a v : α) :
    0 ≤ posterior p tag a v := by
  unfold posterior
  split_ifs
  · exact (div_pos (hp v) (mass_pos p hp tag a)).le
  · rfl

theorem posterior_sum (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α) :
    ∑ v, posterior p tag a v=1 := by
  classical
  simp only [posterior,← Finset.sum_filter,← Finset.sum_div]
  change mass p tag a / mass p tag a=1
  exact div_self (mass_pos p hp tag a).ne'

theorem posterior_uncondition (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (v : α) :
    ∑ a, p a*posterior p tag a v=p v := by
  classical
  have he : ∀ a, p a*posterior p tag a v=
      if tag a=tag v then p a*p v/mass p tag v else 0 := by
    intro a
    by_cases h : tag a=tag v
    · simp only [posterior,ite_eq_left h.symm,ite_eq_left h,mass_eq_of_tag p tag h]
      ring
    · simp [posterior,h,Ne.symm h]
  simp_rw [he]
  rw [← Finset.sum_filter,← Finset.sum_div,← Finset.sum_mul]
  change mass p tag v*p v/mass p tag v=p v
  exact mul_div_cancel_left₀ _ (mass_pos p hp tag v).ne'

theorem posterior_expectation (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (f : α → ℝ) :
    ∑ a, p a*∑ v, posterior p tag a v*f v=∑ v, p v*f v := by
  simp only [Finset.mul_sum,← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,posterior_uncondition p hp tag]

theorem fiber_normalized_sum (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α) :
    ∑ v ∈ fiber tag a, p v/mass p tag a=1 := by
  rw [← Finset.sum_div]
  exact div_self (mass_pos p hp tag a).ne'

noncomputable def law (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α) (f : α → ℝ) : Law :=
  Law.ofObservable (fiber tag a) (fun v => p v/mass p tag a)
    (fun v _ => div_pos (hp v) (mass_pos p hp tag a)) (fiber_normalized_sum p hp tag a) f

theorem law_entropy_mean (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (f : α → ℝ) :
    (∑ a, p a*(law p hp tag a f).shannonEntropy)*Real.log 2=
      FiniteEntropy.conditionalEntropy Finset.univ p f tag := by
  classical
  simp only [law,Law.ofObservable_entropy,← mul_div_assoc,← Finset.sum_div,
    div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne']
  rw [conditionalEntropy_eq_sum _ _ _ _ (fun a _ => (hp a).le)]
  symm
  convert FiniteEntropy.sum_mass_mul Finset.univ (Finset.univ.image tag) p tag
    (fun c => observableEntropy (Finset.univ.filter (fun a => tag a=c))
      (fun a => p a/FiniteEntropy.mass Finset.univ p tag c) f)
    (fun a ha => Finset.mem_image_of_mem tag ha) using 1
  rfl

theorem law_smul_sum (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α)
    (f : α → ℝ) (F : ℝ → Measure ℝ) :
    (∑ x : (law p hp tag a f).support, ENNReal.ofReal ((law p hp tag a f).prob x) • F x)=
      ∑ v, ENNReal.ofReal (posterior p tag a v) • F (f v) := by
  classical
  rw [law,Law.smul_sum_ofObservable]
  simp only [posterior,apply_ite ENNReal.ofReal,ENNReal.ofReal_zero,ite_smul,zero_smul,
    ← Finset.sum_filter]
  rfl

theorem posterior_smul_uncondition (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β)
    (F : α → Measure ℝ) :
    (∑ a, ENNReal.ofReal (p a) • ∑ v, ENNReal.ofReal (posterior p tag a v) • F v)=
      ∑ v, ENNReal.ofReal (p v) • F v := by
  simp only [Finset.smul_sum,smul_smul,← ENNReal.ofReal_mul (hp _).le]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_smul,← ENNReal.ofReal_sum_of_nonneg
    (fun a _ => mul_nonneg (hp a).le (posterior_nonneg p hp tag a v)),posterior_uncondition p hp tag]

end EntropyRateDimension.FiniteCondition

end OAI
