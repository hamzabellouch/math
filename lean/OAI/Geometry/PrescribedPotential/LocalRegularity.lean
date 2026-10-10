import Mathlib
import OAI.Geometry.PrescribedPotential.SobolevLocalization
import OAI.Geometry.PrescribedPotential.VariablePoisson

namespace OAI

/-! Local Regularity. -/

section

 

noncomputable section
open Filter Topology MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Real ComplexOrder MatrixOrder

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_distribution_injective :
    Function.Injective (SchwartzMap.toTemperedDistributionCLM E ℂ volume) := by
  intro f g h
  apply SchwartzMap.injective_toLp 2 volume
  apply l2_injective
  simpa only [Lp.toTemperedDistributionCLM_apply,
    Lp.toTemperedDistribution_toLp_eq] using h

 
def schwartzCoord (s : ℝ) (f : 𝓢(E, ℂ)) : L2 E :=
  ((memSobolev_iff_realize s (f : 𝓢'(E, ℂ))).mp f.memSobolev).choose

lemma realize_schwartzCoord (s : ℝ) (f : 𝓢(E, ℂ)) :
    realize s (schwartzCoord s f) = (f : 𝓢'(E, ℂ)) :=
  ((memSobolev_iff_realize s (f : 𝓢'(E, ℂ))).mp f.memSobolev).choose_spec

lemma schwartzCoord_add (s : ℝ) (f g : 𝓢(E, ℂ)) :
    schwartzCoord s (f + g) = schwartzCoord s f + schwartzCoord s g := by
  apply realize_injective s
  simp only [map_add, realize_schwartzCoord]

lemma schwartzCoord_sum {ι : Type*} (s : ℝ) (S : Finset ι) (f : ι → 𝓢(E, ℂ)) :
    schwartzCoord s (∑ i ∈ S, f i) = ∑ i ∈ S, schwartzCoord s (f i) := by
  apply realize_injective s
  simp only [map_sum, realize_schwartzCoord]

 
lemma weak_deriv_comm (v w : E) (u : 𝓢'(E, ℂ)) :
    ∂_{v} (∂_{w} u) = ∂_{w} (∂_{v} u) := by
  rw [FrozenPoisson.second_deriv_multiplier, FrozenPoisson.second_deriv_multiplier]
  congr 2
  ext x
  ring

lemma schwartz_deriv_comm (v w : E) (u : 𝓢(E, ℂ)) :
    ∂_{v} (∂_{w} u) = ∂_{w} (∂_{v} u) := by
  apply schwartz_distribution_injective
  change ((∂_{v} (∂_{w} u) : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) = _
  rw [← lineDerivOp_toTemperedDistributionCLM_eq,
    ← lineDerivOp_toTemperedDistributionCLM_eq,
    ← lineDerivOp_toTemperedDistributionCLM_eq,
    ← lineDerivOp_toTemperedDistributionCLM_eq]
  exact weak_deriv_comm v w (u : 𝓢'(E, ℂ))

 
lemma summable_of_contracting_recurrence {a b : ℕ → ℝ} {q : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hq : q < 1)
    (hs : Summable b) (hrecur : ∀ n, a (n+1) ≤ q * a n + b n) :
    Summable a := by
  apply summable_of_sum_range_le ha (c := (a 0 + ∑' n, b n) / (1 - q))
  intro N
  have hr := Finset.sum_le_sum (s := Finset.range N) (fun n _ => hrecur n)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hr
  have he : (∑ n ∈ Finset.range N, a (n+1)) =
      (∑ n ∈ Finset.range N, a n) + a N - a 0 := by
    have h := Finset.sum_range_succ' a N
    rw [Finset.sum_range_succ] at h
    linarith
  rw [he] at hr
  have hbnd : (∑ n ∈ Finset.range N, b n) ≤ ∑' n, b n :=
    hs.sum_le_tsum (Finset.range N) (fun _ _ => hb _)
  rw [le_div_iff₀ (sub_pos.mpr hq)]
  nlinarith [ha N]

end SobolevChart

namespace FrozenPoisson
open SobolevChart EllipticKernel
variable {n : ℕ}

def schwartzResolvent (H : Matrix (Fin n) (Fin n) ℂ) :
    𝓢(EC n, ℂ) →L[ℂ] 𝓢(EC n, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ (inverseSymbol H)

lemma schwartzResolvent_distribution (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (f : 𝓢(EC n, ℂ)) :
    SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume (schwartzResolvent H f) =
      resolvent H (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume f) :=
  (fourierMultiplierCLM_toTemperedDistributionCLM_eq (inverseSymbol_temperate H hH) f).symm

lemma schwartzCoord_resolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (s : ℝ) (f : 𝓢(EC n, ℂ)) :
    schwartzCoord (s + 2) (schwartzResolvent H f) =
      hilbertResolvent H hH (schwartzCoord s f) := by
  apply realize_injective (s + 2)
  rw [realize_schwartzCoord, hilbertResolvent_realize, realize_schwartzCoord]
  exact schwartzResolvent_distribution H hH f

lemma weak_deriv_resolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : EC n) (u : 𝓢'(EC n, ℂ)) :
    ∂_{v} (resolvent H u) = resolvent H (∂_{v} u) := by
  simp only [lineDeriv_eq_fourierMultiplierCLM, resolvent, map_smul]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply
    (inverseSymbol_temperate H hH) (by fun_prop),
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop)
      (inverseSymbol_temperate H hH)]
  simp only [mul_comm]

lemma schwartz_deriv_resolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : EC n) (f : 𝓢(EC n, ℂ)) :
    ∂_{v} (schwartzResolvent H f) = schwartzResolvent H (∂_{v} f) := by
  apply schwartz_distribution_injective
  rw [← lineDerivOp_toTemperedDistributionCLM_eq, schwartzResolvent_distribution H hH,
    schwartzResolvent_distribution H hH, ← lineDerivOp_toTemperedDistributionCLM_eq]
  exact weak_deriv_resolvent H hH v (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume f)

end FrozenPoisson

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_product_distribution (a f : 𝓢(E, ℂ)) :
    ((SchwartzMap.smulLeftCLM ℂ a f : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) =
      smulLeftCLM ℂ a (f : 𝓢'(E, ℂ)) := by
  ext φ
  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply,
    smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth, smul_eq_mul]
  ring

 
def schwartzWord : List E → (𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ))
  | [] => ContinuousLinearMap.id ℂ _
  | v :: vs => lineDerivOpCLM ℂ 𝓢(E, ℂ) v ∘L schwartzWord vs

def weakWord : List E → (𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  | [] => ContinuousLinearMap.id ℂ _
  | v :: vs => lineDerivOpCLM ℂ 𝓢'(E, ℂ) v ∘L weakWord vs

lemma word_distribution (vs : List E) (f : 𝓢(E, ℂ)) :
    ((schwartzWord vs f : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) = weakWord vs (f : 𝓢'(E, ℂ)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change ((∂_{v} (schwartzWord vs f) : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) = _
    rw [← lineDerivOp_toTemperedDistributionCLM_eq, ih]
    rfl

variable {ι : Type*} [Fintype ι]
abbrev SmoothCoefficients (ι : Type*) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ι → ι → 𝓢(E, ℂ)

def coefficientBCF (a : SmoothCoefficients ι E) (i j : ι) : E →ᵇ ℂ :=
  (a i j).toBoundedContinuousFunction

def coefficientDeriv (w : E) (a : SmoothCoefficients ι E) : SmoothCoefficients ι E :=
  fun i j => ∂_{w} (a i j)

def smoothPerturbation (v : ι → E) (a : SmoothCoefficients ι E) :
    𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  ∑ i, ∑ j, SchwartzMap.smulLeftCLM ℂ (a i j) ∘L
    lineDerivOpCLM ℂ 𝓢(E, ℂ) (v i) ∘L lineDerivOpCLM ℂ 𝓢(E, ℂ) (v j)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma smoothPerturbation_apply (v : ι → E) (a : SmoothCoefficients ι E) (f : 𝓢(E, ℂ)) :
    smoothPerturbation v a f =
      ∑ i, ∑ j, SchwartzMap.smulLeftCLM ℂ (a i j) (∂_{v i} (∂_{v j} f)) := by
  simp only [smoothPerturbation, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply]

lemma smoothPerturbation_distribution (v : ι → E) (a : SmoothCoefficients ι E)
    (f : 𝓢(E, ℂ)) :
    ((smoothPerturbation v a f : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) =
      (perturbation v (coefficientBCF a) (schwartzCoord 2 f) : 𝓢'(E, ℂ)) := by
  rw [perturbation_distribution v _ (fun i j => (a i j).hasTemperateGrowth),
    realize_schwartzCoord, smoothPerturbation_apply]
  change SchwartzMap.toTemperedDistributionCLM E ℂ volume _ = _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [schwartz_product_distribution, ← lineDerivOp_toTemperedDistributionCLM_eq,
    ← lineDerivOp_toTemperedDistributionCLM_eq]
  rfl

lemma schwartzCoord_perturbation (v : ι → E) (a : SmoothCoefficients ι E)
    (f : 𝓢(E, ℂ)) :
    schwartzCoord 0 (smoothPerturbation v a f) =
      perturbation v (coefficientBCF a) (schwartzCoord 2 f) := by
  apply realize_injective 0
  rw [realize_schwartzCoord]
  simpa [realize] using smoothPerturbation_distribution v a f

lemma smoothPerturbation_bound (v : ι → E) (a : SmoothCoefficients ι E)
    (f : 𝓢(E, ℂ)) :
    ‖schwartzCoord 0 (smoothPerturbation v a f)‖ ≤
      perturbationBound v (coefficientBCF a) * ‖schwartzCoord 2 f‖ := by
  rw [schwartzCoord_perturbation]
  exact perturbation_bound _ _ _

lemma schwartz_deriv_perturbation (w : E) (v : ι → E) (a : SmoothCoefficients ι E)
    (f : 𝓢(E, ℂ)) :
    ∂_{w} (smoothPerturbation v a f) =
      smoothPerturbation v a (∂_{w} f) + smoothPerturbation v (coefficientDeriv w a) f := by
  simp only [smoothPerturbation_apply, lineDerivOp_sum, schwartz_deriv_product,
    Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [schwartz_deriv_comm w (v i), schwartz_deriv_comm w (v j)]

end SobolevChart

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

 

def commutatorTerms : List E → SmoothCoefficients ι E →
    List (SmoothCoefficients ι E × List E)
  | [], _ => []
  | w :: ws, a => (coefficientDeriv w a, ws) ::
      ((commutatorTerms ws a).map (fun t => (coefficientDeriv w t.1, t.2)) ++
       (commutatorTerms ws a).map (fun t => (t.1, w :: t.2)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] in
lemma commutatorTerms_order (ws : List E) (a : SmoothCoefficients ι E)
    (t : SmoothCoefficients ι E × List E) (ht : t ∈ commutatorTerms ws a) :
    t.2.length < ws.length := by
  induction ws generalizing t with
  | nil => simp [commutatorTerms] at ht
  | cons w ws ih =>
    simp only [commutatorTerms, List.mem_cons, List.mem_append, List.mem_map] at ht
    rcases ht with rfl | ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
    · simp
    · exact (ih b hb).trans (Nat.lt_succ_self _)
    · exact Nat.succ_lt_succ (ih b hb)

lemma list_sum_add {α M : Type*} [AddCommMonoid M] (ts : List α) (f g : α → M) :
    (ts.map (fun t => f t + g t)).sum = (ts.map f).sum + (ts.map g).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp only [List.map_cons, List.sum_cons, ih]; abel

lemma schwartz_word_perturbation (ws : List E) (v : ι → E)
    (a : SmoothCoefficients ι E) (f : 𝓢(E, ℂ)) :
    schwartzWord ws (smoothPerturbation v a f) =
      smoothPerturbation v a (schwartzWord ws f) +
        ((commutatorTerms ws a).map
          (fun t => smoothPerturbation v t.1 (schwartzWord t.2 f))).sum := by
  induction ws with
  | nil => simp [schwartzWord, commutatorTerms]
  | cons w ws ih =>
    change ∂_{w} (schwartzWord ws (smoothPerturbation v a f)) = _
    rw [ih, lineDerivOp_add, schwartz_deriv_perturbation]
    have hs : ∂_{w} (((commutatorTerms ws a).map
        (fun t => smoothPerturbation v t.1 (schwartzWord t.2 f))).sum) =
        ((commutatorTerms ws a).map
          (fun t => ∂_{w} (smoothPerturbation v t.1 (schwartzWord t.2 f)))).sum := by
      exact (List.sum_map_hom _ _ (lineDerivOpCLM ℂ 𝓢(E, ℂ) w)).symm
    rw [hs]
    simp only [schwartz_deriv_perturbation, list_sum_add, commutatorTerms,
      List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, schwartzWord, ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply]
    abel

end SobolevChart

namespace FrozenPoisson
open SobolevChart EllipticKernel
variable {n : ℕ} {ι : Type*} [Fintype ι]

lemma schwartz_word_resolvent (ws : List (EC n)) (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (f : 𝓢(EC n, ℂ)) :
    schwartzWord ws (schwartzResolvent H f) = schwartzResolvent H (schwartzWord ws f) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change ∂_{w} (schwartzWord ws (schwartzResolvent H f)) = _
    rw [ih, schwartz_deriv_resolvent H hH]
    rfl

 
def schwartzNeumann (H : Matrix (Fin n) (Fin n) ℂ) (v : ι → EC n)
    (a : SmoothCoefficients ι (EC n)) : 𝓢(EC n, ℂ) →L[ℂ] 𝓢(EC n, ℂ) :=
  schwartzResolvent H ∘L smoothPerturbation v a

lemma schwartzResolvent_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (f : 𝓢(EC n, ℂ)) :
    ‖schwartzCoord 2 (schwartzResolvent H f)‖ ≤
      ellipticBound H hH * ‖schwartzCoord 0 f‖ := by
  have hc := schwartzCoord_resolvent H hH 0 f
  norm_num at hc
  rw [hc]
  exact hilbertResolvent_bound H hH _

lemma schwartzNeumann_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : SmoothCoefficients ι (EC n)) (f : 𝓢(EC n, ℂ)) :
    ‖schwartzCoord 2 (schwartzNeumann H v a f)‖ ≤
      (ellipticBound H hH * perturbationBound v (coefficientBCF a)) *
        ‖schwartzCoord 2 f‖ := by
  calc
    _ ≤ ellipticBound H hH * ‖schwartzCoord 0 (smoothPerturbation v a f)‖ :=
      schwartzResolvent_bound H hH _
    _ ≤ ellipticBound H hH * (perturbationBound v (coefficientBCF a) *
        ‖schwartzCoord 2 f‖) :=
      mul_le_mul_of_nonneg_left (smoothPerturbation_bound v a f) (ellipticBound_pos H hH).le
    _ = _ := by ring

lemma schwartz_word_neumann (ws : List (EC n)) (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (v : ι → EC n) (a : SmoothCoefficients ι (EC n)) (f : 𝓢(EC n, ℂ)) :
    schwartzWord ws (schwartzNeumann H v a f) =
      schwartzNeumann H v a (schwartzWord ws f) +
        ((commutatorTerms ws a).map
          (fun t => schwartzNeumann H v t.1 (schwartzWord t.2 f))).sum := by
  change schwartzWord ws (schwartzResolvent H (smoothPerturbation v a f)) = _
  rw [schwartz_word_resolvent ws H hH, schwartz_word_perturbation, map_add, map_list_sum]
  simp only [List.map_map, Function.comp_def]
  rfl

end FrozenPoisson

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartzCoord_zero (s : ℝ) : schwartzCoord s (0 : 𝓢(E, ℂ)) = 0 := by
  apply realize_injective s
  simp only [map_zero, realize_schwartzCoord]

lemma schwartzCoord_list_sum (s : ℝ) (ts : List 𝓢(E, ℂ)) :
    schwartzCoord s ts.sum = (ts.map (schwartzCoord s)).sum := by
  induction ts with
  | nil => simp [schwartzCoord_zero]
  | cons t ts ih => simp only [List.sum_cons, schwartzCoord_add, ih, List.map_cons]

lemma summable_norm_schwartzCoord_list {α : Type*} (s : ℝ) (ts : List α)
    (f : α → ℕ → 𝓢(E, ℂ))
    (hf : ∀ t ∈ ts, Summable (fun n => ‖schwartzCoord s (f t n)‖)) :
    Summable (fun n => ‖schwartzCoord s ((ts.map (fun t => f t n)).sum)‖) := by
  induction ts with
  | nil => simp [schwartzCoord_zero]
  | cons t ts ih =>
    have ht := hf t (List.mem_cons_self ..)
    have hts := ih (fun t ht => hf t (List.mem_cons_of_mem _ ht))
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (ht.add hts)
    intro n
    simpa only [List.map_cons, List.sum_cons, schwartzCoord_add] using
      norm_add_le (schwartzCoord s (f t n))
        (schwartzCoord s ((ts.map (fun t => f t n)).sum))

end SobolevChart

namespace FrozenPoisson
open SobolevChart EllipticKernel
variable {n : ℕ} {ι : Type*} [Fintype ι]

def schwartzIterate (H : Matrix (Fin n) (Fin n) ℂ) (v : ι → EC n)
    (a : SmoothCoefficients ι (EC n)) (f : 𝓢(EC n, ℂ)) (N : ℕ) : 𝓢(EC n, ℂ) :=
  (schwartzNeumann H v a)^[N] f

lemma schwartzIterate_succ (H : Matrix (Fin n) (Fin n) ℂ) (v : ι → EC n)
    (a : SmoothCoefficients ι (EC n)) (f : 𝓢(EC n, ℂ)) (N : ℕ) :
    schwartzIterate H v a f (N+1) = schwartzNeumann H v a (schwartzIterate H v a f N) :=
  Function.iterate_succ_apply' _ _ _

lemma summable_norm_neumann_of (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : SmoothCoefficients ι (EC n)) (f : ℕ → 𝓢(EC n, ℂ))
    (hf : Summable (fun m => ‖schwartzCoord 2 (f m)‖)) :
    Summable (fun m => ‖schwartzCoord 2 (schwartzNeumann H v a (f m))‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => schwartzNeumann_bound H hH v a (f m))
  exact hf.mul_left _

 

theorem neumann_summable_word (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)
    (f : 𝓢(EC n, ℂ)) (ws : List (EC n)) :
    Summable (fun m => ‖schwartzCoord 2 (schwartzWord ws (schwartzIterate H v a f m))‖) := by
  induction hlen : ws.length using Nat.strong_induction_on generalizing ws with
  | h k ih =>
    let err : ℕ → 𝓢(EC n, ℂ) := fun m => ((commutatorTerms ws a).map
      (fun t => schwartzNeumann H v t.1 (schwartzWord t.2 (schwartzIterate H v a f m)))).sum
    have hs : Summable (fun m => ‖schwartzCoord 2 (err m)‖) := by
      apply summable_norm_schwartzCoord_list
      intro t ht
      apply summable_norm_neumann_of H hH
      exact ih t.2.length (hlen ▸ commutatorTerms_order ws a t ht) t.2 rfl
    apply summable_of_contracting_recurrence (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) (q := ellipticBound H hH * perturbationBound v (coefficientBCF a))
      (by simpa only [mul_comm] using hsmall) hs
    intro m
    rw [schwartzIterate_succ, schwartz_word_neumann ws H hH, schwartzCoord_add]
    exact (norm_add_le _ _).trans (add_le_add
      (schwartzNeumann_bound H hH v a _) le_rfl)

end FrozenPoisson

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma memSobolev_word_of_summable (f : ℕ → 𝓢(E, ℂ)) (ws : List E)
    (hf : Summable (fun m => ‖schwartzCoord 2 (f m)‖))
    (hw : Summable (fun m => ‖schwartzCoord 2 (schwartzWord ws (f m))‖)) :
    MemSobolev 2 2 (weakWord ws (realize 2 (∑' m, schwartzCoord 2 (f m)))) := by
  have h₁ := (hf.of_norm.hasSum.mapL (realize (E := E) 2)).mapL (weakWord ws)
  have h₂ := hw.of_norm.hasSum.mapL (realize (E := E) 2)
  simp only [realize_schwartzCoord, word_distribution] at h₁ h₂
  rw [h₁.unique h₂]
  exact realize_memSobolev _ _

lemma memSobolev_even_of_words (u : 𝓢'(E, ℂ))
    (hu : ∀ ws : List E, MemSobolev 2 2 (weakWord ws u)) (k : ℕ) :
    ∀ ws : List E, MemSobolev (2 * (k : ℝ)) 2 (weakWord ws u) := by
  induction k with
  | zero =>
    intro ws
    exact (hu ws).mono (by norm_num)
  | succ k ih =>
    intro ws
    have hs : 2 * ((k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 2 := by push_cast; ring
    rw [hs]
    apply memSobolev_of_second_basis (ih ws)
    intro j
    exact ih (stdOrthonormalBasis ℝ E j :: stdOrthonormalBasis ℝ E j :: ws)

end SobolevChart

namespace FrozenPoisson
open SobolevChart EllipticKernel
variable {n : ℕ} {ι : Type*} [Fintype ι]

 
def neumannSum (H : Matrix (Fin n) (Fin n) ℂ) (v : ι → EC n)
    (a : SmoothCoefficients ι (EC n)) (f : 𝓢(EC n, ℂ)) : L2 (EC n) :=
  ∑' m, schwartzCoord 2 (schwartzIterate H v a f m)

lemma schwartzCoord_neumann (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : SmoothCoefficients ι (EC n)) (f : 𝓢(EC n, ℂ)) :
    schwartzCoord 2 (schwartzNeumann H v a f) =
      hilbertResolvent H hH (perturbation v (coefficientBCF a) (schwartzCoord 2 f)) := by
  have he := schwartzCoord_resolvent H hH 0 (smoothPerturbation v a f)
  norm_num at he
  rw [schwartzCoord_perturbation] at he
  exact he

lemma neumannSum_fixed (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)
    (f : 𝓢(EC n, ℂ)) :
    neumannSum H v a f = schwartzCoord 2 f +
      hilbertResolvent H hH (perturbation v (coefficientBCF a) (neumannSum H v a f)) := by
  have hs := (neumann_summable_word H hH v a hsmall f []).of_norm
  change Summable (fun m => schwartzCoord 2 (schwartzIterate H v a f m)) at hs
  let T := hilbertResolvent H hH ∘L perturbation v (coefficientBCF a)
  have hmap := T.map_tsum hs
  simp only [T, ContinuousLinearMap.comp_apply, ← schwartzCoord_neumann,
    ← schwartzIterate_succ] at hmap
  change (∑' m, schwartzCoord 2 (schwartzIterate H v a f m)) = _
  rw [hs.tsum_eq_zero_add]
  change schwartzCoord 2 f + _ = schwartzCoord 2 f + _
  exact congrArg (schwartzCoord 2 f + ·) hmap.symm

lemma equation_of_fixed (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ) (u f : L2 (EC n))
    (hu : u = hilbertResolvent H hH (f + perturbation v a u)) :
    realize 2 u - frozenDifferential H (realize 2 u) -
      (perturbation v a u : 𝓢'(EC n, ℂ)) = (f : 𝓢'(EC n, ℂ)) := by
  have hr : realize 2 u = resolvent H (realize 0 (f + perturbation v a u)) := by
    conv_lhs => rw [hu]
    simpa only [zero_add] using hilbertResolvent_realize H hH 0 (f + perturbation v a u)
  rw [← shifted_eq_identity_sub H hH, hr, shifted_resolvent H hH]
  simp only [realize, neg_zero, besselPotential_zero, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.id_apply, Lp.toTemperedDistributionCLM_apply]
  change Lp.toTemperedDistributionCLM ℂ volume 2 (f + perturbation v a u) -
    Lp.toTemperedDistributionCLM ℂ volume 2 (perturbation v a u) =
    Lp.toTemperedDistributionCLM ℂ volume 2 f
  simp only [map_add, add_sub_cancel_right]

lemma neumannSum_eq_localResolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)
    (f : 𝓢(EC n, ℂ)) :
    neumannSum H v a (schwartzResolvent H f) =
      localResolvent H hH v (coefficientBCF a) hsmall (schwartzCoord 0 f) := by
  apply perturbed_unique H hH v (coefficientBCF a) hsmall
    _ _ (schwartzCoord 0 f)
  · apply equation_of_fixed H hH
    rw [map_add]
    have hr := schwartzCoord_resolvent H hH 0 f
    norm_num at hr
    rw [← hr]
    exact neumannSum_fixed H hH v a hsmall (schwartzResolvent H f)
  · exact localResolvent_equation H hH v (coefficientBCF a) hsmall _

 

theorem localResolvent_schwartz_memSobolev (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)
    (f : 𝓢(EC n, ℂ)) (k : ℕ) :
    MemSobolev (2 * (k : ℝ)) 2
      (realize 2 (localResolvent H hH v (coefficientBCF a) hsmall (schwartzCoord 0 f))) := by
  rw [← neumannSum_eq_localResolvent H hH v a hsmall f]
  apply memSobolev_even_of_words _ _ k []
  intro ws
  exact memSobolev_word_of_summable (schwartzIterate H v a (schwartzResolvent H f)) ws
    (neumann_summable_word H hH v a hsmall (schwartzResolvent H f) [])
    (neumann_summable_word H hH v a hsmall (schwartzResolvent H f) ws)

end FrozenPoisson

end
end

end OAI
