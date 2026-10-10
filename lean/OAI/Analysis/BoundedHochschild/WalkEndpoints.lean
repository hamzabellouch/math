import Mathlib
import OAI.Analysis.BoundedHochschild.Martingales

namespace OAI

/-! Reversed paths, endpoint distributions and eventual endpoint mass. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
 

lemma iid_extract {I J : Type*} [Fintype J] (index : J → I) (hi : Function.Injective index)
    (f : J → G → G) (hf : ∀ j, MeasurePreserving (f j) μ μ) :
    MeasurePreserving (fun x j => f j (x (index j)))
      (Measure.infinitePi (fun _ : I => μ)) (Measure.pi (fun _ : J => μ)) := by
  have he : MeasurePreserving (fun x j => x (index j))
      (Measure.infinitePi (fun _ : I => μ)) (Measure.pi (fun _ : J => μ)) := by
    refine ⟨Measurable.of_eval (fun coordinate => measurable_pi_apply (index coordinate)), ?_⟩
    rw [Measure.map_infinitePi_infinitePi_of_inj hi, Measure.infinitePi_eq_pi]
  exact (measurePreserving_pi _ _ hf).comp he

 
def signed (s : Bool) (g : G) : G := if s then g else g⁻¹

omit [IsProbabilityMeasure μ] in
lemma signed_preserving (hsym : μ.map (fun g => g⁻¹) = μ) (s : Bool) :
    MeasurePreserving (signed s) μ μ := by
  cases s
  · exact ⟨measurable_of_countable _, hsym⟩
  · exact MeasurePreserving.id μ

lemma iid_signed_extract {I J : Type*} [Fintype J] (hsym : μ.map (fun g => g⁻¹) = μ)
    (index : J → I) (hi : Function.Injective index) (sign : J → Bool) :
    MeasurePreserving (fun x j => signed (sign j) (x (index j)))
      (Measure.infinitePi (fun _ : I => μ)) (Measure.pi (fun _ : J => μ)) :=
  iid_extract μ index hi _ (fun j => signed_preserving μ hsym (sign j))

 
def reversePath (n : ℕ) (w : Fin n → G) : Fin n → G := fun i => (w i.rev)⁻¹

lemma reversePath_preserving (hsym : μ.map (fun g => g⁻¹) = μ) (n : ℕ) :
    MeasurePreserving (reversePath (G := G) n)
      (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => μ)) := by
  have hi : Function.Injective (Fin.rev : Fin n → Fin n) := Fin.rev_injective
  have he := iid_signed_extract μ hsym Fin.rev hi (fun _ => false)
  simp only [Measure.infinitePi_eq_pi] at he
  exact he

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma ofFn_reverse_inv (n : ℕ) (w : Fin n → G) :
    List.ofFn (reversePath n w) = ((List.ofFn w).map (fun g => g⁻¹)).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_map, List.length_ofFn,
      List.getElem_map, reversePath, Fin.rev]
    congr 2
    apply Fin.ext
    dsimp
    omega

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma reversePath_prod (n : ℕ) (w : Fin n → G) :
    (List.ofFn (reversePath n w)).prod = (List.ofFn w).prod⁻¹ := by
  rw [ofFn_reverse_inv, ← List.prod_inv_reverse]

 
def endpointIndex (n h : ℕ) (hle : 2*h ≤ n) : Fin h ⊕ Fin h → Fin n
  | Sum.inl i => ⟨i, by omega⟩
  | Sum.inr i => ⟨n-1-i, by omega⟩

omit [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma endpointIndex_injective (n h : ℕ) (hle : 2*h ≤ n) :
    Function.Injective (endpointIndex n h hle) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      apply Fin.ext
      exact congrArg (fun k : Fin n => k.val) hab
    | inr b =>
      have he := congrArg Fin.val hab
      simp only [endpointIndex] at he
      omega
  | inr a =>
    cases b with
    | inl b =>
      have he := congrArg Fin.val hab
      simp only [endpointIndex] at he
      omega
    | inr b =>
      apply congrArg Sum.inr
      apply Fin.ext
      have he := congrArg Fin.val hab
      simp only [endpointIndex] at he
      omega

lemma endpoint_prefixes_preserving (hsym : μ.map (fun g => g⁻¹) = μ)
    (n h : ℕ) (hle : 2*h ≤ n) :
    MeasurePreserving (fun w : Fin n → G =>
      ((fun i : Fin h => w ⟨i, by omega⟩), (fun i : Fin h => (w ⟨n-1-i, by omega⟩)⁻¹)))
      (Measure.pi (fun _ : Fin n => μ))
      ((Measure.pi (fun _ : Fin h => μ)).prod (Measure.pi (fun _ : Fin h => μ))) := by
  have he := iid_signed_extract μ hsym (endpointIndex n h hle)
    (endpointIndex_injective n h hle) (Sum.elim (fun _ => true) (fun _ => false))
  have hf := (measurePreserving_sumPiEquivProdPi (fun _ : Fin h ⊕ Fin h => μ)).comp he
  simp only [Measure.infinitePi_eq_pi] at hf
  exact hf

end HochschildWalk

open MeasureTheory Filter Topology
namespace HochschildProbability
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

lemma mass_transfer (S T E : Set Ω) (h : S ⊆ T ∪ E) :
    μ.real S ≤ μ.real T + μ.real E :=
  (measureReal_mono h).trans (measureReal_union_le _ _)

lemma mass_transfer_two (S T E F : Set Ω) (h : S ⊆ T ∪ (E ∪ F)) :
    μ.real S ≤ μ.real T + μ.real E + μ.real F := by
  have h₁ := mass_transfer μ S T (E∪F) h
  have h₂ := measureReal_union_le (μ := μ) E F
  linarith

omit [IsFiniteMeasure μ] in
lemma norm_error_mass {H : Type*} [NormedAddCommGroup H] (f : Ω → H)
    (hf : MemLp f 2 μ) {δ : ℝ} (hδ : 0 < δ) :
    μ.real {x | δ ≤ ‖f x‖} ≤ (∫ x, ‖f x‖^2 ∂μ) / δ^2 := by
  have he : {x | δ ≤ ‖f x‖} = {x | δ^2 ≤ ‖f x‖^2} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    exact (sq_le_sq₀ hδ.le (norm_nonneg _)).symm
  rw [he, le_div_iff₀ (sq_pos_of_pos hδ), mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) 
    (hf.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)) _

lemma ball_mass_transfer {H : Type*} [NormedAddCommGroup H] (f g : Ω → H)
    (a : H) {r δ : ℝ} (hδ : 0 < δ) (hfg : MemLp (fun x => f x-g x) 2 μ) :
    μ.real {x | ‖f x-a‖ < r} ≤ μ.real {x | ‖g x-a‖ < r+δ} +
      (∫ x, ‖f x-g x‖^2 ∂μ) / δ^2 := by
  apply (mass_transfer μ _ {x | ‖g x-a‖ < r+δ} {x | δ ≤ ‖f x-g x‖} ?_).trans
  · have hb := norm_error_mass μ (fun x => f x-g x) hfg hδ
    exact add_le_add le_rfl hb
  · intro x hx
    by_cases he : δ ≤ ‖f x-g x‖
    · exact Or.inr he
    · apply Or.inl
      have ht : ‖g x-a‖ ≤ ‖g x-f x‖ + ‖f x-a‖ := by
        simpa only [dist_eq_norm] using dist_triangle (g x) (f x) a
      rw [norm_sub_rev (g x) (f x)] at ht
      dsimp at hx ⊢
      exact ht.trans_lt (add_lt_add (lt_of_not_ge he) hx) |>.trans_eq (add_comm δ r)

lemma two_ball_mass_transfer {H : Type*} [NormedAddCommGroup H]
    (f₁ f₂ g₁ g₂ : Ω → H) (a b : H) {r δ : ℝ} (hδ : 0 < δ)
    (h₁ : MemLp (fun x => f₁ x-g₁ x) 2 μ) (h₂ : MemLp (fun x => f₂ x-g₂ x) 2 μ) :
    μ.real {x | ‖f₁ x-a‖ < r ∧ ‖f₂ x-b‖ < r} ≤
      μ.real {x | ‖g₁ x-a‖ < r+δ ∧ ‖g₂ x-b‖ < r+δ} +
      (∫ x, ‖f₁ x-g₁ x‖^2 ∂μ) / δ^2 + (∫ x, ‖f₂ x-g₂ x‖^2 ∂μ) / δ^2 := by
  have hb₁ := norm_error_mass μ (fun x => f₁ x-g₁ x) h₁ hδ
  have hb₂ := norm_error_mass μ (fun x => f₂ x-g₂ x) h₂ hδ
  have ht := mass_transfer_two μ {x | ‖f₁ x-a‖ < r ∧ ‖f₂ x-b‖ < r}
    {x | ‖g₁ x-a‖ < r+δ ∧ ‖g₂ x-b‖ < r+δ}
    {x | δ ≤ ‖f₁ x-g₁ x‖} {x | δ ≤ ‖f₂ x-g₂ x‖} (by
      intro x hx
      by_cases he₁ : δ ≤ ‖f₁ x-g₁ x‖
      · exact Or.inr (Or.inl he₁)
      by_cases he₂ : δ ≤ ‖f₂ x-g₂ x‖
      · exact Or.inr (Or.inr he₂)
      left
      constructor
      · have hr : ‖g₁ x-a‖ ≤ ‖g₁ x-f₁ x‖ + ‖f₁ x-a‖ := by
          simpa only [dist_eq_norm] using dist_triangle (g₁ x) (f₁ x) a
        rw [norm_sub_rev (g₁ x) (f₁ x)] at hr
        exact hr.trans_lt (add_lt_add (lt_of_not_ge he₁) hx.1) |>.trans_eq (add_comm δ r)
      · have hr : ‖g₂ x-b‖ ≤ ‖g₂ x-f₂ x‖ + ‖f₂ x-b‖ := by
          simpa only [dist_eq_norm] using dist_triangle (g₂ x) (f₂ x) b
        rw [norm_sub_rev (g₂ x) (f₂ x)] at hr
        exact hr.trans_lt (add_lt_add (lt_of_not_ge he₂) hx.2) |>.trans_eq (add_comm δ r))
  exact ht.trans (add_le_add (add_le_add le_rfl hb₁) hb₂)

end HochschildProbability

open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (μ : Measure G) [IsProbabilityMeasure μ]

omit [Group G] [CompleteSpace H] [InnerProductSpace ℝ H] in
lemma finite_memLp (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (n : ℕ) (f : (Fin n → G) → G) :
    MemLp (fun w => D (f w)) 2 (Measure.pi (fun _ : Fin n => μ)) :=
  MemLp.of_bound (StronglyMeasurable.of_discrete.aestronglyMeasurable) C
    (Eventually.of_forall fun _ => hD _)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma finite_ball_mass (D : G → H) (n : ℕ) (a : H) (r : ℝ) :
    (pathMeasure μ).real {ω | ‖D (walk n ω)-a‖ < r} =
      (Measure.pi (fun _ : Fin n => μ)).real {w | ‖D (word w)-a‖ < r} := by
  have hm : MeasurePreserving (takePath (G := G) n) (pathMeasure μ)
      (Measure.pi (fun _ : Fin n => μ)) := ⟨takePath_measurable n, takePath_law μ n⟩
  exact congrArg ENNReal.toReal (hm.measure_preimage (s := {w | ‖D (word w)-a‖ < r}) (Set.to_countable _).measurableSet.nullMeasurableSet)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma finite_cauchy_bound (D : G → H)
    (z : Lp H 2 (pathMeasure μ))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (k n : ℕ) (hkn : k ≤ n) :
    ∫ w : Fin n → G, ‖D (word w)-D (word (fun i : Fin k => w (Fin.castLE hkn i)))‖^2
      ∂Measure.pi (fun _ : Fin n => μ) ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ := by
  rw [← takePath_integral μ n]
  exact hc k n hkn

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma endpoint_prefix_ball_mass (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (n k : ℕ) (hkn : 2*k ≤ n) (a b : H) (r : ℝ) :
    (Measure.pi (fun _ : Fin n => μ)).real {w |
      ‖D (word (fun i : Fin k => w ⟨i, by omega⟩))-a‖ < r ∧
      ‖D (word (fun i : Fin k => (w ⟨n-1-i, by omega⟩)⁻¹))-b‖ < r} =
    (pathMeasure μ).real {ω | ‖D (walk k ω)-a‖ < r} *
      (pathMeasure μ).real {ω | ‖D (walk k ω)-b‖ < r} := by
  rw [finite_ball_mass μ D k a r, finite_ball_mass μ D k b r]
  rw [← measureReal_prod_prod]
  exact congrArg ENNReal.toReal ((endpoint_prefixes_preserving μ hsym n k hkn).measure_preimage
    (s := {w | ‖D (word w)-a‖ < r} ×ˢ {w | ‖D (word w)-b‖ < r})
    (Set.to_countable _).measurableSet.nullMeasurableSet)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma reverse_finite_cauchy_bound (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (z : Lp H 2 (pathMeasure μ))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (k n : ℕ) (hkn : k ≤ n) :
    ∫ w : Fin n → G, ‖D ((word w)⁻¹) - D (word (fun i : Fin k => (w ⟨n-1-i, by omega⟩)⁻¹))‖^2
      ∂Measure.pi (fun _ : Fin n => μ) ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ := by
  have he := (integral_map_of_stronglyMeasurable (μ := Measure.pi (fun _ : Fin n => μ)) (reversePath_preserving μ hsym n).measurable
    (StronglyMeasurable.of_discrete (f := fun w : Fin n → G =>
      ‖D (word w)-D (word (fun i : Fin k => w (Fin.castLE hkn i)))‖^2))).symm
  rw [(reversePath_preserving μ hsym n).map_eq] at he
  have hx : (fun w : Fin n → G =>
      ‖D (word (reversePath n w))-D (word (fun i : Fin k => reversePath n w (Fin.castLE hkn i)))‖^2) =
      (fun w => ‖D ((word w)⁻¹)-D (word (fun i : Fin k => (w ⟨n-1-i, by omega⟩)⁻¹))‖^2) := by
    funext w
    rw [show word (reversePath n w) = (word w)⁻¹ from reversePath_prod n w]
    have hp : (fun i : Fin k => reversePath n w (Fin.castLE hkn i)) =
        (fun i : Fin k => (w ⟨n-1-i, by omega⟩)⁻¹) := by
      funext i
      dsimp [reversePath]
      congr 2
      apply Fin.ext
      dsimp [Fin.rev]
      omega
    rw [hp]
  change (∫ w, _ ∂_) = _ at he
  rw [show (fun w : Fin n → G =>
      (fun v => ‖D (word v)-D (word (fun i : Fin k => v (Fin.castLE hkn i)))‖^2) (reversePath n w)) = _ from hx] at he
  rw [he]
  exact finite_cauchy_bound μ D z hc k n hkn

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
 

lemma two_endpoint_lower_bound (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (z : Lp H 2 (pathMeasure μ))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (k n : ℕ) (hkn : 2*k ≤ n) (a b : H) (r δ : ℝ) (hδ : 0 < δ) :
    (pathMeasure μ).real {ω | ‖D (walk k ω)-a‖ < r} *
      (pathMeasure μ).real {ω | ‖D (walk k ω)-b‖ < r} -
        2 * (∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ) / δ^2 ≤
      (Measure.pi (fun _ : Fin n => μ)).real
        {w | ‖D (word w)-a‖ < r+δ ∧ ‖D ((word w)⁻¹)-b‖ < r+δ} := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  let A : (Fin n → G) → H := fun w => D (word (fun i : Fin k => w ⟨i, by omega⟩))
  let B : (Fin n → G) → H := fun w => D (word (fun i : Fin k => (w ⟨n-1-i, by omega⟩)⁻¹))
  let X : (Fin n → G) → H := fun w => D (word w)
  let Y : (Fin n → G) → H := fun w => D ((word w)⁻¹)
  let e := ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ
  have hi₁ : (∫ w, ‖A w-X w‖^2 ∂ν) ≤ e := by
    calc
      _ = ∫ w, ‖X w-A w‖^2 ∂ν := integral_congr_ae (Eventually.of_forall fun w => by rw [norm_sub_rev])
      _ ≤ e := finite_cauchy_bound μ D z hc k n (by omega)
  have hi₂ : (∫ w, ‖B w-Y w‖^2 ∂ν) ≤ e := by
    calc
      _ = ∫ w, ‖Y w-B w‖^2 ∂ν := integral_congr_ae (Eventually.of_forall fun w => by rw [norm_sub_rev])
      _ ≤ e := reverse_finite_cauchy_bound μ hsym D z hc k n (by omega)
  have hb := HochschildProbability.two_ball_mass_transfer ν A B X Y a b (r := r) hδ
    ((finite_memLp μ D C hD n _).sub (finite_memLp μ D C hD n _))
    ((finite_memLp μ D C hD n _).sub (finite_memLp μ D C hD n _))
  have hm : ν.real {w | ‖A w-a‖ < r ∧ ‖B w-b‖ < r} =
      (pathMeasure μ).real {ω | ‖D (walk k ω)-a‖ < r} *
        (pathMeasure μ).real {ω | ‖D (walk k ω)-b‖ < r} :=
    endpoint_prefix_ball_mass μ hsym D n k hkn a b r
  rw [hm] at hb
  apply sub_le_iff_le_add.mpr
  calc
    _ ≤ ν.real {w | ‖X w-a‖ < r+δ ∧ ‖Y w-b‖ < r+δ} +
        (∫ w, ‖A w-X w‖^2 ∂ν) / δ^2 + (∫ w, ‖B w-Y w‖^2 ∂ν) / δ^2 := hb
    _ ≤ ν.real {w | ‖X w-a‖ < r+δ ∧ ‖Y w-b‖ < r+δ} + e/δ^2 + e/δ^2 :=
      add_le_add (add_le_add le_rfl (div_le_div_of_nonneg_right hi₁ (sq_nonneg _)))
        (div_le_div_of_nonneg_right hi₂ (sq_nonneg _))
    _ = _ := by change _ = _ + 2*e/δ^2; ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
 

theorem endpoint_mass_eventually (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (z : Lp H 2 (pathMeasure μ))
    (hz : Tendsto (fun k => ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ) atTop (𝓝 0))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (a b : H) (ha : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-a‖ < r})
    (hb : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-b‖ < r})
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η > 0, ∃ N : ℕ, ∀ n ≥ N,
      η ≤ (Measure.pi (fun _ : Fin n => μ)).real
        {w | ‖D (word w)-a‖ < δ ∧ ‖D ((word w)⁻¹)-b‖ < δ} := by
  let r := δ/3
  have hr : 0 < r := div_pos hδ (by norm_num)
  let pa := (pathMeasure μ).real {ω | ‖z ω-a‖ < r}
  let pb := (pathMeasure μ).real {ω | ‖z ω-b‖ < r}
  have hpa : 0 < pa := ha r hr
  have hpb : 0 < pb := hb r hr
  let q := min (pa/2) (min (pb/2) (pa*pb/16))
  have hq : 0 < q := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have het : Tendsto (fun k => (∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)/r^2)
      atTop (𝓝 0) := by simpa using hz.div_const (r^2)
  obtain ⟨k,hk⟩ := eventually_atTop.mp (het.eventually (gt_mem_nhds hq))
  let e := (∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)/r^2
  have he : e < q := hk k le_rfl
  have heal : e < pa/2 := he.trans_le (min_le_left _ _)
  have hebl : e < pb/2 := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heab : e < pa*pb/16 := he.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have ham := HochschildProbability.ball_mass_transfer (pathMeasure μ) z
    (fun ω => D (walk k ω)) a (r := r) hr ((Lp.memLp z).sub (process_memLp μ D C hD k))
  have hbm := HochschildProbability.ball_mass_transfer (pathMeasure μ) z
    (fun ω => D (walk k ω)) b (r := r) hr ((Lp.memLp z).sub (process_memLp μ D C hD k))
  change pa ≤ (pathMeasure μ).real {ω | ‖D (walk k ω)-a‖ < r+r} + e at ham
  change pb ≤ (pathMeasure μ).real {ω | ‖D (walk k ω)-b‖ < r+r} + e at hbm
  have hA : pa/2 ≤ (pathMeasure μ).real {ω | ‖D (walk k ω)-a‖ < r+r} := by linarith
  have hB : pb/2 ≤ (pathMeasure μ).real {ω | ‖D (walk k ω)-b‖ < r+r} := by linarith
  refine ⟨pa*pb/8, by positivity, 2*k, ?_⟩
  intro n hn
  have hp := mul_le_mul hA hB (by positivity : 0 ≤ pb/2) measureReal_nonneg
  have hl := two_endpoint_lower_bound μ hsym D C hD z hc k n hn a b (r+r) r hr
  have heq : r+r+r = δ := by dsimp [r]; ring
  have heq' : 2*(∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)/r^2 = 2*e := by dsimp [e]; ring
  rw [heq, heq'] at hl
  nlinarith

end HochschildWalk
end

end OAI
