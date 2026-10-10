import Mathlib
import OAI.Probability.SKGap.Posterior.History

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma pi_gaussian_add (m₁ m₂ : Fin n → ℝ) (v₁ v₂ : ℝ≥0) :
    ((Measure.pi fun i => gaussianReal (m₁ i) v₁).prod
      (Measure.pi fun i => gaussianReal (m₂ i) v₂)).map
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => fun i => z.1 i+z.2 i) =
      Measure.pi (fun i => gaussianReal (m₁ i+m₂ i) (v₁+v₂)) := by
  rw [← (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun i => gaussianReal (m₁ i) v₁) (fun i => gaussianReal (m₂ i) v₂)).map_eq]
  rw [Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  change (Measure.pi (fun i => (gaussianReal (m₁ i) v₁).prod (gaussianReal (m₂ i) v₂))).map
    (fun z i => (z i).1+(z i).2) = _
  rw [Measure.pi_map_pi (f := fun _ (z : ℝ × ℝ) => z.1+z.2) (fun _ => by fun_prop)]
  congr 1
  funext i
  exact gaussianReal_conv_gaussianReal

def field (t : ℝ) : {k : ℕ} → History n k → (Fin n → ℝ)
  | 0, _ => 0
  | _+1, h => fun i => field t h.1 i+sqrt t*h.2 i

lemma continuous_field (t : ℝ) : ∀k,Continuous (field (n := n) t (k := k))
  | 0 => continuous_const
  | k+1 => (continuous_field t k).comp continuous_fst |>.add
      (by fun_prop)

lemma map_scaled_reference {t : ℝ} (ht : 0≤t) :
    (GaussianStep.reference n).map (fun z : Fin n→ℝ => fun i => sqrt t*z i) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 (toNNReal t)) := by
  unfold GaussianStep.reference
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp [sq_sqrt ht,ht]

lemma map_field_reference {t : ℝ} (ht : 0≤t) : ∀k,
    (reference n k).map (field t (k := k)) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 (toNNReal ((k:ℝ)*t)))
  | 0 => by
    simp only [reference,field,Nat.cast_zero,zero_mul,toNNReal_zero,gaussianReal_zero_var]
    rw [Measure.map_dirac' (by fun_prop) ()]
    apply (Measure.pi_eq (μ := fun _ : Fin n => Measure.dirac (0:ℝ)) (μ' := Measure.dirac (0:Fin n→ℝ)) ?_).symm
    intro s hs
    by_cases hx : ∀i:Fin n,(0:ℝ)∈s i
    · rw [Measure.dirac_apply_of_mem (by simpa only [mem_univ_pi,Pi.zero_apply] using hx)]
      symm
      exact Finset.prod_eq_one (fun i _ => Measure.dirac_apply_of_mem (hx i))
    · push Not at hx
      obtain ⟨i,hi⟩ := hx
      rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
        Set.indicator_of_notMem (by simp only [mem_univ_pi,Pi.zero_apply]; exact not_forall.mpr ⟨i,hi⟩)]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [Measure.dirac_apply' _ (hs i),Set.indicator_of_notMem hi])
  | k+1 => by
    change ((reference n k).prod (GaussianStep.reference n)).map
      ((fun z : (Fin n→ℝ) × (Fin n→ℝ) => fun i => z.1 i+z.2 i) ∘
        Prod.map (field t) (fun z : Fin n→ℝ => fun i => sqrt t*z i)) = _
    rw [← Measure.map_map (by fun_prop) ((continuous_field t k).measurable.prodMap (by fun_prop)), ← Measure.map_prod_map
      (reference n k) (GaussianStep.reference n)
      (continuous_field t k).measurable (by fun_prop),
      map_field_reference ht k,map_scaled_reference ht,pi_gaussian_add]
    congr 1
    funext i
    simp only [zero_add]
    congr 1
    rw [←toNNReal_add (mul_nonneg (by positivity) ht) ht]
    congr 1
    push_cast
    ring

lemma likelihood_field (t : ℝ) (x : Spin n) : ∀{k : ℕ} (h : History n k),
    likelihood t x h = exp ((∑i,spinValue (x i)*field t h i)-(k:ℝ)*t*(n:ℝ)/2)
  | 0, _ => by simp [likelihood,field]
  | k+1, h => by
    rw [likelihood,likelihood_field t x h.1,GaussianStep.likelihood,←exp_add]
    congr 1
    simp only [field,Finset.sum_add_distrib,mul_add,Nat.cast_add,Nat.cast_one]
    have he : (∑i,spinValue (x i)*(sqrt t*h.2 i)) = sqrt t*∑i,spinValue (x i)*h.2 i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    ring

lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α→β) (g : β→ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs]
  rw [←lintegral_indicator (hf hs),←lintegral_indicator hs,
    lintegral_map (hg.indicator hs) hf]
  apply lintegral_congr
  intro x
  by_cases hx : f x∈s <;> simp [hx]

theorem field_law (p : Prior n) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    (law p t k).map (field t) =
      ((GaussianStep.reference n).withDensity
        (fun z => ENNReal.ofReal (GaussianStep.density p ((k:ℝ)*t) z))).map
        (fun z : Fin n→ℝ => fun i => sqrt ((k:ℝ)*t)*z i) := by
  let D : (Fin n→ℝ)→ℝ≥0∞ := fun y => ENNReal.ofReal
    (∑ x, p x*exp ((∑i,spinValue (x i)*y i)-(k:ℝ)*t*(n:ℝ)/2))
  have hD : Measurable D := by unfold D; fun_prop
  have hd : (fun h : History n k => ENNReal.ofReal (density p t h))=D ∘ field t := by
    funext h
    simp only [density,likelihood_field,Function.comp_def,D]
  have hs : (fun z => ENNReal.ofReal (GaussianStep.density p ((k:ℝ)*t) z)) =
      D ∘ (fun z : Fin n→ℝ => fun i => sqrt ((k:ℝ)*t)*z i) := by
    funext z
    unfold D GaussianStep.density GaussianStep.likelihood
    dsimp
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    congr 2
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [law,hd,hs,map_withDensity_comp _ _ _ (continuous_field t k).measurable hD,
    map_withDensity_comp _ _ _ (by fun_prop) hD,map_field_reference ht,
    map_scaled_reference (mul_nonneg (by positivity) ht)]

lemma weight_field (g : Disorder n) (h₀ y : Fin n→ℝ) (x : Spin n) :
    weight g (h₀+y) x=weight g h₀ x*exp (∑i,spinValue (x i)*y i) := by
  unfold weight hamiltonian
  rw [←exp_add]
  congr 1
  simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
  have he : (∑i,y i*spinValue (x i))=∑i,spinValue (x i)*y i :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he]
  ring

lemma posterior_gibbs_field (g : Disorder n) (h₀ : Fin n→ℝ) (t : ℝ)
    {k : ℕ} (h : History n k) : posterior (gibbsPrior g h₀) t h = gibbsPrior g (h₀+field t h) := by
  have he (x : Spin n) : gibbsPrior g h₀ x*likelihood t x h =
      (exp (-(k:ℝ)*t*(n:ℝ)/2)/partition g h₀)*weight g (h₀+field t h) x := by
    rw [likelihood_field,weight_field]
    change (weight g h₀ x/partition g h₀)*exp (_-_) = _
    rw [exp_sub]
    have hn : -(k:ℝ)*t*(n:ℝ)/2 = -((k:ℝ)*t*(n:ℝ)/2) := by ring
    rw [hn,exp_neg]
    ring
  have hd : density (gibbsPrior g h₀) t h =
      (exp (-(k:ℝ)*t*(n:ℝ)/2)/partition g h₀)*partition g (h₀+field t h) := by
    simp only [density,he,←Finset.mul_sum,partition]
  apply Prior.ext
  funext x
  change gibbsPrior g h₀ x*likelihood t x h/density (gibbsPrior g h₀) t h =
    weight g (h₀+field t h) x/partition g (h₀+field t h)
  rw [he,hd]
  exact mul_div_mul_left _ _ (div_ne_zero (exp_ne_zero _) (partition_pos _ _).ne')

end
end SKGap.GaussianHistory

end OAI
