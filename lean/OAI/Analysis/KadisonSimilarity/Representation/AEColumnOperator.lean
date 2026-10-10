import OAI.Analysis.KadisonSimilarity.Representation.DenseLinearOperator
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Sequences

namespace OAI

/-! # Recovering fiber operators from almost-everywhere column data

The common conull set is obtained from countably many additive and
`i`-linearity identities. The extension has the original norm bound;
each fixed column agrees almost everywhere with the original data.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, NormedSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]

theorem ae_exists_operator_of_countable_additive
    (S : AddSubgroup E) [Countable S] (hdense : Dense (S : Set E))
    (hIS : ∀ x ∈ S, Complex.I • x ∈ S) (C : ℝ≥0)
    (f : ∀ _x : S, ∀ a, K a)
    (hzero : ∀ᵐ a ∂μ, f 0 a = 0)
    (hadd : ∀ x y : S, ∀ᵐ a ∂μ, f (x + y) a = f x a + f y a)
    (hI : ∀ x : S, ∀ᵐ a ∂μ,
      f ⟨Complex.I • x.val, hIS x.val x.property⟩ a = Complex.I • f x a)
    (hnorm : ∀ x : S, ∀ᵐ a ∂μ, ‖f x a‖ ≤ C * ‖x‖) :
    ∀ᵐ a ∂μ, ∃ T : E →L[ℂ] K a, ‖T‖ ≤ C ∧ ∀ x : S, T x = f x a := by
  have ha : ∀ᵐ a ∂μ, ∀ x y : S, f (x + y) a = f x a + f y a :=
    eventually_countable_forall.mpr fun x => eventually_countable_forall.mpr (hadd x)
  have hi : ∀ᵐ a ∂μ, ∀ x : S,
      f ⟨Complex.I • x.val, hIS x.val x.property⟩ a = Complex.I • f x a :=
    eventually_countable_forall.mpr hI
  have hn : ∀ᵐ a ∂μ, ∀ x : S, ‖f x a‖ ≤ C * ‖x‖ :=
    eventually_countable_forall.mpr hnorm
  filter_upwards [hzero, ha, hi, hn] with a hz ha hi hn
  let g : S →+ K a := { toFun := fun x => f x a, map_zero' := hz, map_add' := ha }
  exact exists_operator_of_dense_additive S hdense hIS g C hn hi

omit [∀ a, CompleteSpace (K a)] in
theorem ae_columnOperator_agrees_at
    (S : AddSubgroup E) (hdense : Dense (S : Set E)) (C : ℝ≥0)
    (f : ∀ _x : E, ∀ a, K a)
    (hsub : ∀ x y : E, ∀ᵐ a ∂μ, f (x - y) a = f x a - f y a)
    (hnorm : ∀ x : E, ∀ᵐ a ∂μ, ‖f x a‖ ≤ C * ‖x‖) (x : E) :
    ∀ᵐ a ∂μ, ∀ T : E →L[ℂ] K a, ‖T‖ ≤ C →
      (∀ y : S, T y = f y a) → T x = f x a := by
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense x)
  have hs : ∀ᵐ a ∂μ, ∀ n : ℕ, f (x - y n) a = f x a - f (y n) a :=
    eventually_countable_forall.mpr (fun n => hsub x (y n))
  have hn : ∀ᵐ a ∂μ, ∀ n : ℕ, ‖f (x - y n) a‖ ≤ C * ‖x - y n‖ :=
    eventually_countable_forall.mpr (fun n => hnorm (x - y n))
  filter_upwards [hs, hn] with a hs hn
  intro T hT hext
  have hbound (n : ℕ) : ‖T x - f x a‖ ≤ C * ‖x - y n‖ + C * ‖x - y n‖ := by
    calc
      _ ≤ ‖T x - T (y n)‖ + ‖T (y n) - f x a‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C * ‖x - y n‖ + C * ‖x - y n‖ := add_le_add
        (by
          rw [← map_sub]
          exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _)))
        (by
          rw [hext ⟨y n, hy n⟩, norm_sub_rev, ← hs n]
          exact hn n)
  have hzero : Tendsto (fun n => ‖x - y n‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub hlim).norm
  have hC := hzero.const_mul (C : ℝ)
  have hle : ‖T x - f x a‖ ≤ 0 := by
    simpa only [mul_zero, zero_add] using ge_of_tendsto' (hC.add hC) hbound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

/-- Bounded AE column data gives a genuine bounded complex-linear operator
on every fiber of a measurable conull restriction. -/
theorem exists_conull_columnOperators
    [TopologicalSpace.SeparableSpace E] (C : ℝ≥0)
    (f : ∀ _x : E, ∀ a, K a)
    (hzero : ∀ᵐ a ∂μ, f 0 a = 0)
    (hadd : ∀ x y : E, ∀ᵐ a ∂μ, f (x + y) a = f x a + f y a)
    (hI : ∀ x : E, ∀ᵐ a ∂μ, f (Complex.I • x) a = Complex.I • f x a)
    (hnorm : ∀ x : E, ∀ᵐ a ∂μ, ‖f x a‖ ≤ C * ‖x‖) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ T : ∀ a : s, E →L[ℂ] K a,
        (∀ a, ‖T a‖ ≤ C) ∧
        ∀ x : E, ∀ᵐ a ∂Measure.comap ((↑) : s → Ω) μ, T a x = f x a := by
  classical
  obtain ⟨S, hcount, hdense, hIS⟩ := exists_countable_dense_complex_addSubgroup E
  let : Countable S := hcount.to_subtype
  have hex := ae_exists_operator_of_countable_additive μ K S hdense hIS C
    (fun x a => f x a) hzero (fun x y => hadd x y) (fun x => hI x) (fun x => hnorm x)
  obtain ⟨s, hs, hsm, hsexists⟩ := hex.exists_measurable_mem
  choose T hT hext using fun a : s => hsexists a a.property
  refine ⟨s, hsm, mem_ae_iff.mp hs, T, hT, ?_⟩
  intro x
  have hsub (u v : E) : ∀ᵐ a ∂μ, f (u - v) a = f u a - f v a := by
    filter_upwards [hadd (u - v) v] with a ha
    exact eq_sub_iff_add_eq.mpr (by simpa only [sub_add_cancel] using ha.symm)
  have h := ae_columnOperator_agrees_at μ K S hdense C f hsub hnorm x
  have hr := (ae_restrict_iff_subtype hsm).mp (ae_restrict_of_ae h)
  exact hr.mono fun a ha => ha (T a) (hT a) (hext a)

end KadisonSimilarity

end

end OAI
