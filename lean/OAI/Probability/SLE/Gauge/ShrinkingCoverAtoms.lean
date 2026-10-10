import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.Order.LiminfLimsup

namespace OAI

/-! The nonatomicity step of `mass:construction`: a squared atom is
bounded by every squared covering mass sum. Fatou therefore rules out
all atoms at once, without a countable union over points. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SLEExactGauge

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- One atom is charged to one cell in any finite cover. -/
lemma singleton_sq_le_cover_sum (μ : Measure X) (I : Finset ℕ) (C : ℕ → Set X)
    {x : X} (hcover : ∃ i ∈ I, x ∈ C i) :
    (μ {x})^2 ≤ ∑ i ∈ I, (μ (C i))^2 := by
  obtain ⟨i,hi,hxi⟩ := hcover
  have hsub : ({x} : Set X) ⊆ C i := singleton_subset_iff.mpr hxi
  exact (pow_le_pow_left' (measure_mono hsub) 2).trans
    (Finset.single_le_sum (f := fun j => (μ (C j))^2) (fun _ _ => zero_le) hi)

/-- Vanishing expected upper bounds for squared atoms exclude every atom
on a set simultaneously almost surely. -/
theorem ae_null_singletons_on_of_square_bounds (P : Measure Ω) (μ : Ω → Measure X)
    (K : Set X) (A : ℕ → Ω → ℝ≥0∞) (hA : ∀ n, Measurable (A n))
    (hbound : ∀ ω x, x ∈ K → ∀ n, (μ ω {x})^2 ≤ A n ω)
    (hlim : Tendsto (fun n => ∫⁻ ω, A n ω ∂P) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ x ∈ K, μ ω {x}=0 := by
  have hfatou : (∫⁻ ω, liminf (fun n => A n ω) atTop ∂P) ≤ 0 := by
    simpa only [hlim.liminf_eq] using lintegral_liminf_le (μ := P) (u := atTop) hA
  have hz : ∀ᵐ ω ∂P, liminf (fun n => A n ω) atTop=0 :=
    (lintegral_eq_zero_iff (Measurable.liminf hA)).mp (le_antisymm hfatou bot_le)
  filter_upwards [hz] with ω hω
  intro x hx
  have hb : (μ ω {x})^2 ≤ liminf (fun n => A n ω) atTop :=
    le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall (hbound ω x hx))
  rw [hω] at hb
  exact eq_zero_of_pow_eq_zero (le_antisymm hb bot_le)

/-- The finite-cover form used for compact exhaustion. Cover diameters
need not be named here: all geometric decay is captured in the expected
squared mass sum. -/
theorem ae_null_singletons_on_of_cover_sums (P : Measure Ω) (μ : Ω → Measure X)
    (hμ : Measurable μ) (K : Set X) (I : ℕ → Finset ℕ) (C : ℕ → ℕ → Set X)
    (hC : ∀ n i, MeasurableSet (C n i))
    (hcover : ∀ n x, x ∈ K → ∃ i ∈ I n, x ∈ C n i)
    (hlim : Tendsto (fun n => ∫⁻ ω, ∑ i ∈ I n, (μ ω (C n i))^2 ∂P) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ x ∈ K, μ ω {x}=0 := by
  apply ae_null_singletons_on_of_square_bounds P μ K
    (fun n ω => ∑ i ∈ I n, (μ ω (C n i))^2) _ _ hlim
  · intro n
    exact Finset.measurable_sum (I n) (fun i _ => ((Measure.measurable_coe (hC n i)).comp hμ).pow_const 2)
  · intro ω x hx n
    exact singleton_sq_le_cover_sum (μ ω) (I n) (C n) (hcover n x hx)

/-- A countable covering of the whole space upgrades the compact-by-compact
criterion to a nonatomic random measure. -/
theorem ae_nullSingletonClass_of_exhaustion (P : Measure Ω) (μ : Ω → Measure X)
    (K : ℕ → Set X) (hcover : ∀ x, ∃ j, x ∈ K j)
    (hK : ∀ j, ∀ᵐ ω ∂P, ∀ x ∈ K j, μ ω {x}=0) :
    ∀ᵐ ω ∂P, NullSingletonClass (μ ω) := by
  filter_upwards [ae_all_iff.mpr hK] with ω hω
  constructor
  intro x
  obtain ⟨j,hj⟩ := hcover x
  exact hω j x hj

end SLEExactGauge

end

end OAI
