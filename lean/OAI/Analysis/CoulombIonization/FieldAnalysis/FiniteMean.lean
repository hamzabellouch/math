import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators Topology

namespace CoulombNeumann

def finiteMean {ι E : Type*} [Fintype ι] [AddCommMonoid E] [Module ℝ E] (f : ι → E) : E :=
  (Fintype.card ι:ℝ)⁻¹ • ∑ i, f i

lemma finiteMean_const {ι E : Type*} [Fintype ι] [Nonempty ι]
    [AddCommMonoid E] [Module ℝ E] (x : E) : finiteMean (fun _ : ι => x) = x := by
  simp only [finiteMean,Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_smul,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]

lemma finiteMean_norm_sq_le {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ι → E) :
    ‖finiteMean f‖^2 ≤ finiteMean (fun i => ‖f i‖^2) := by
  have hc : 0 < (Fintype.card ι:ℝ) := by exact_mod_cast Fintype.card_pos
  unfold finiteMean
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hc.le),mul_pow,smul_eq_mul]
  have hn := norm_sum_le Finset.univ f
  have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖f i‖)
  simp only [Finset.card_univ] at hs
  have hsq : ‖∑ i, f i‖^2 ≤ (∑ i,‖f i‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hh := mul_le_mul_of_nonneg_left (hsq.trans hs) (sq_nonneg (Fintype.card ι:ℝ)⁻¹)
  calc
    _ ≤ (Fintype.card ι:ℝ)⁻¹^2*((Fintype.card ι:ℝ)*∑ i, ‖f i‖^2) := hh
    _ = _ := by field_simp

lemma finiteMean_tendsto {ι α E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {l : Filter α}
    {f : α → ι → E} {g : ι → E} (h : ∀ i, Filter.Tendsto (fun a => f a i) l (𝓝 (g i))) :
    Filter.Tendsto (fun a => finiteMean (f a)) l (𝓝 (finiteMean g)) := by
  exact (tendsto_finsetSum Finset.univ (fun i _ => h i)).const_smul _

lemma finiteMean_memLp {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    {μ : Measure α} {f : ι → α → ℂ} (h : ∀ i, MemLp (f i) 2 μ) :
    MemLp (fun x => finiteMean (fun i => f i x)) 2 μ := by
  exact (memLp_finsetSum Finset.univ (fun i _ => h i)).const_smul _

lemma finiteMean_integral_norm_sq_le {ι α : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace α] {μ : Measure α} {f : ι → α → ℂ} (h : ∀ i, MemLp (f i) 2 μ) :
    (∫ x, ‖finiteMean (fun i => f i x)‖^2 ∂μ) ≤ finiteMean (fun i => ∫ x, ‖f i x‖^2 ∂μ) := by
  calc
    _ ≤ ∫ x, finiteMean (fun i => ‖f i x‖^2) ∂μ := by
      apply integral_mono (finiteMean_memLp h).norm.integrable_sq
        ((integrable_finsetSum _ (fun i _ => (h i).norm.integrable_sq)).const_mul _)
      exact fun x => finiteMean_norm_sq_le (fun i => f i x)
    _ = _ := by
      unfold finiteMean
      rw [integral_smul,integral_finsetSum _ (fun i _ => (h i).norm.integrable_sq)]

lemma sum_finiteMean {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid E] [Module ℝ E] (f : κ → ι → E) :
    (∑ j, finiteMean (f j)) = finiteMean (fun i => ∑ j, f j i) := by
  unfold finiteMean
  rw [←Finset.smul_sum,Finset.sum_comm]

lemma finiteMean_mono {ι : Type*} [Fintype ι] {f g : ι → ℝ} (h : ∀ i, f i ≤ g i) :
    finiteMean f ≤ finiteMean g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) (by positivity)

end CoulombNeumann

end

end OAI
