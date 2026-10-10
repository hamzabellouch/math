import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.AuxiliaryJointMeasurable

namespace OAI

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set ProductAveraging Coefficient
open scoped BigOperators Classical NNReal
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ j, Fintype (M j)]
variable {κ τ : Type} [Fintype κ]

lemma full_absorption_square (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ)
    (hq : ∀ j k, q j (p j k) = r k) (a : τ → ι) {m : ℕ} (hm : 0 < m)
    (t : ι → Fin (m+1)) (ht : Full t) (F : (κ → Circle) → ℝ)
    (hFm : Measurable F) (hb : ∀ x, |F x| ≤ 1) :
    (∫ θ, ∫ z, (F (auxiliary p r a (fun j => value (t j)) θ z))^2
      ∂(volume : Measure (ι → Circle)) ∂Measure.pi (fun _ : Sigma M => rotationLaw)) =
    ∫ θ, (F (phase p (fun j => value (t j)) θ))^2
      ∂Measure.pi (fun _ : Sigma M => rotationLaw) := by
  obtain ⟨j,hj⟩ := ht
  have hi := bounded_sq_integrable (μ := (Measure.pi (fun _ : Sigma M => rotationLaw)).prod volume)
    (hFm.comp (auxiliary_joint_measurable p r a (fun j => value (t j))))
    (fun v => hb (auxiliary p r a (fun j => value (t j)) v.1 v.2))
  rw [integral_integral_swap hi]
  have h (z : ι → Circle) := absorption_integral p q r hq a j
    (fun j => value (t j)) (value_full hm _ hj) z (fun x => (F x)^2) (hFm.pow_const 2)
  simp_rw [h]
  simp

lemma continuous_full_bound (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ)
    (hq : ∀ j k, q j (p j k) = r k) (a : τ → ι) {m : ℕ} (hm : 0 < m)
    {ρ ε : ℝ} (hρ : 0 ≤ ρ) (F : (κ → Circle) → ℝ)
    (hFm : Measurable F) (hb : ∀ x, |F x| ≤ 1)
    (haux : (∑ t : ι → Fin (m+1), mass m ρ t *
      ∫ θ, ∫ z, (F (auxiliary p r a (fun j => value (t j)) θ z))^2
      ∂(volume : Measure (ι → Circle)) ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < 4*ε) :
    (∑ t ∈ Finset.univ.filter Full, mass m ρ t *
      ∫ θ, (F (phase p (fun j => value (t j)) θ))^2
        ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < 4*ε := by
  calc
    _ = ∑ t ∈ Finset.univ.filter Full, mass m ρ t *
        ∫ θ, ∫ z, (F (auxiliary p r a (fun j => value (t j)) θ z))^2
          ∂(volume : Measure (ι → Circle)) ∂Measure.pi (fun _ : Sigma M => rotationLaw) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [full_absorption_square p q r hq a hm t (Finset.mem_filter.mp ht).2 F hFm hb]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun t _ _ => mul_nonneg (mass_nonneg m hρ t)
        (integral_nonneg fun θ => integral_nonneg fun z => sq_nonneg _))
    _ < _ := haux
end LargeIndependentSets.PhaseTest

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set ProductAveraging
open scoped BigOperators Classical NNReal
variable {C : Type} [Fintype C] [DecidableEq C]

omit [DecidableEq C] in
lemma arbitrary_sampler_preserving (k : ℕ) :
    MeasurePreserving (fun v : C → Cube k × ℝ => fun c => scalarCell (v c).1 (v c).2)
      (Measure.pi (fun _ : C => seedLaw k)) (Measure.pi (fun _ : C => unitLaw)) :=
  measurePreserving_pi _ _ (fun _ => scalarSampler_preserving k)
lemma arbitrary_cells_preserving (k : ℕ) :
    MeasurePreserving (fun v : C → Cube k × ℝ => fun c => (v c).1)
      (Measure.pi (fun _ : C => seedLaw k)) (uniformLaw (C → Cube k)) := by
  rw [uniformLaw_pi]
  exact measurePreserving_pi _ _ (fun _ => measurePreserving_fst)
omit [DecidableEq C] in
lemma arbitrary_seeds_in_unit (k : ℕ) :
    ∀ᵐ v ∂Measure.pi (fun _ : C => seedLaw k), ∀ c, (v c).2 ∈ Icc (0:ℝ) 1 := by
  have hu : ∀ᵐ u ∂unitLaw, u ∈ Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have hs : ∀ᵐ p : Cube k × ℝ ∂seedLaw k, p.2 ∈ Icc (0:ℝ) 1 :=
    (measurePreserving_snd (μ:=uniformLaw (Cube k)) (ν:=unitLaw)).quasiMeasurePreserving.ae hu
  rw [ae_all_iff]
  intro c
  exact (measurePreserving_eval (fun _ : C => seedLaw k) c).quasiMeasurePreserving.ae hs
end LargeIndependentSets.BooleanJunta

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set ProductAveraging Coefficient BooleanJunta
open scoped BigOperators Classical NNReal
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ j, Fintype (M j)]
variable {κ : Type} [Fintype κ]

lemma discrete_square_le_continuous (p : ∀ j, κ → M j) (t : ι → ℝ)
    (ht : ∀ j, |t j| ≤ 1) (k : ℕ) {L : ℝ≥0}
    (F : (κ → Circle) → ℝ) (hF : LipschitzWith L F) (hb : ∀ x, |F x| ≤ 1) :
    (𝔼 v : Sigma M → Cube k,
      (F (phase p t (fun c => scalarCell (v c) 0)))^2) ≤
    (∫ θ, (F (phase p t θ))^2 ∂Measure.pi (fun _ : Sigma M => rotationLaw)) +
      2*L*Fintype.card ι*(1/2:ℝ)^k := by
  have hrot : rotationLaw = unitLaw := by
    simp only [rotationLaw, unitLaw, restrict_Ico_eq_restrict_Icc]
  have hsp := arbitrary_sampler_preserving (C:=Sigma M) k
  have hcp := arbitrary_cells_preserving (C:=Sigma M) k
  have hm : Measurable (fun θ => F (phase p t θ)) := hF.continuous.measurable.comp (phase_measurable p t)
  have hd : Measurable (fun v : Sigma M → Cube k => (F (phase p t (fun c => scalarCell (v c) 0)))^2) := measurable_of_finite _
  have hi := bounded_sq_integrable (μ:=Measure.pi (fun _ : Sigma M => seedLaw k))
    (hm.comp hsp.measurable) (fun v => hb _)
  simp only [Function.comp_def] at hi
  have hdi : Integrable (fun v : Sigma M → Cube k × ℝ =>
      (F (phase p t (fun c => scalarCell (v c).1 0)))^2)
      (Measure.pi (fun _ : Sigma M => seedLaw k)) :=
    bounded_sq_integrable (hF.continuous.measurable.comp ((phase_measurable p t).comp
      (Measurable.of_eval (fun c => (measurable_of_finite (fun q : Cube k => scalarCell q 0)).comp
        (measurable_fst.comp (measurable_pi_apply c)))))) (fun v => hb _)
  have hle : (∫ v, (F (phase p t (fun c => scalarCell (v c).1 0)))^2
      ∂Measure.pi (fun _ : Sigma M => seedLaw k)) ≤
    (∫ v, (F (phase p t (fun c => scalarCell (v c).1 (v c).2)))^2 +
      2*L*Fintype.card ι*(1/2:ℝ)^k ∂Measure.pi (fun _ : Sigma M => seedLaw k)) := by
    apply integral_mono_ae hdi (hi.add (integrable_const _))
    filter_upwards [arbitrary_seeds_in_unit (C:=Sigma M) k] with v hv
    have hdist : ∀ c, |scalarCell (v c).1 (v c).2-scalarCell (v c).1 0| ≤ (1/2:ℝ)^k := by
      intro c
      have h := (scalarCell_lipschitz (v c).1).dist_le_mul (v c).2 0
      rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg (hv c).1] at h
      exact h.trans (by simpa using mul_le_mul_of_nonneg_left (hv c).2 (by positivity : 0 ≤ (1/2:ℝ)^k))
    have he := grid_square_error p t ht (fun c => scalarCell (v c).1 (v c).2)
      (fun c => scalarCell (v c).1 0) (by positivity : 0 ≤ (1/2:ℝ)^k) hdist hF hb
    dsimp only [Pi.add_apply, Function.comp_def]
    linarith [abs_le.mp he]
  rw [integral_add hi (integrable_const _)] at hle
  rw [integral_preserving hcp hd.aestronglyMeasurable, integral_uniformLaw] at hle
  have hsample := integral_preserving hsp (hm.pow_const 2).aestronglyMeasurable
  change (∫ v, (F (phase p t (fun c => scalarCell (v c).1 (v c).2)))^2
    ∂Measure.pi (fun _ : Sigma M => seedLaw k)) = _ at hsample
  rw [hsample] at hle
  simpa only [hrot, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using hle
end LargeIndependentSets.PhaseTest

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators Classical

def gridIndex : {k : ℕ} → Cube k → ℕ
  | 0, _ => 0
  | k+1, (b,x) => (if b then 2^k else 0) + gridIndex x
lemma gridIndex_lt {k : ℕ} (x : Cube k) : gridIndex x < 2^k := by
  induction k with
  | zero => simp [gridIndex]
  | succ k ih =>
    rcases x with ⟨b,x⟩
    have hx := ih x
    have hp : 0 < 2^k := by positivity
    cases b <;> simp only [gridIndex, Bool.false_eq_true, ↓reduceIte, zero_add, pow_succ] <;> omega
lemma gridIndex_injective (k : ℕ) : Function.Injective (@gridIndex k) := by
  induction k with
  | zero => intro x y _; exact Subsingleton.elim _ _
  | succ k ih =>
    intro ⟨b,x⟩ ⟨c,y⟩ he
    have hx := gridIndex_lt x
    have hy := gridIndex_lt y
    cases b <;> cases c <;> simp only [gridIndex, Bool.false_eq_true, ↓reduceIte, zero_add] at he
    · exact Prod.ext rfl (ih he)
    · omega
    · omega
    · exact Prod.ext rfl (ih (Nat.add_left_cancel he))
lemma cube_card (k : ℕ) : Fintype.card (Cube k) = 2^k := by
  induction k with
  | zero => simp [Cube]
  | succ k ih =>
    change Fintype.card (Bool × Cube k) = _
    simp only [Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
    omega
noncomputable def gridEquiv (k : ℕ) : Cube k ≃ Fin (2^k) :=
  Equiv.ofBijective (fun x => ⟨gridIndex x, gridIndex_lt x⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y h => gridIndex_injective k (congrArg Fin.val h), by simp [cube_card]⟩)
lemma scalarCell_zero_grid {k : ℕ} (x : Cube k) :
    scalarCell x 0 = (gridEquiv k x).val / (2:ℝ)^k := by
  change scalarCell x 0 = (gridIndex x : ℝ) / (2:ℝ)^k
  induction k with
  | zero => simp [scalarCell, gridIndex]
  | succ k ih =>
    rcases x with ⟨b,x⟩
    have hp : (2:ℝ)^k ≠ 0 := by positivity
    cases b <;> simp only [scalarCell, gridIndex, Bool.false_eq_true, ↓reduceIte,
      zero_add, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, ih, pow_succ]
    · ring
    · field_simp
end LargeIndependentSets.BooleanJunta

end OAI
