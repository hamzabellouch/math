import OAI.NumberTheory.DukePrimeDegree.Dynamics.MaximalOccupation
import OAI.NumberTheory.DukePrimeDegree.Geometry.LocalInjectivityHeight

namespace OAI

/-! # Sublinear growth of a height with bounded upward increments

A high endpoint forces a long preceding interval in a high-level set.
The maximal occupation bound therefore makes every positive linear
slope an eventual upper bound. The height itself need not be integrable.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

private lemma height_iterate_le {Y : Type*} (T : Y → Y) (H : Y → ℕ)
    (hstep : ∀ x, H (T x) ≤ H x+1) (n : ℕ) (x : Y) :
    H (T^[n] x) ≤ H x+n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hstep _).trans (by omega)

private lemma height_endpoint_visit_bound {Y : Type*} (T : Y → Y) (H : Y → ℕ)
    (hstep : ∀ x, H (T x) ≤ H x+1) (x : Y) (M n : ℕ) (hx : H x ≤ M) :
    H (T^[n] x)-M ≤ visitCount T {y | M ≤ H y} n x := by
  classical
  let k := H (T^[n] x)-M
  have hkn : k ≤ n := by
    have h := height_iterate_le T H hstep n x
    dsimp [k]
    omega
  have hsub : Finset.Ico (n-k) n ⊆
      (Finset.range n).filter (fun j => M ≤ H (T^[j] x)) := by
    intro j hj
    obtain ⟨hjl,hju⟩ := Finset.mem_Ico.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hju,?_⟩
    have hb := height_iterate_le T H hstep (n-j) (T^[j] x)
    rw [←Function.iterate_add_apply,Nat.sub_add_cancel hju.le] at hb
    dsimp [k] at hjl hkn
    omega
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hc
  have hcard : ((Finset.range n).filter (fun j => M ≤ H (T^[j] x))).card =
      visitCount T {y | M ≤ H y} n x := by
    unfold visitCount
    congr 1
    ext j
    simp only [Finset.mem_filter,Set.mem_ofPred_eq]
  rw [hcard,Nat.sub_sub_self hkn] at hc
  exact hc

theorem ae_height_affine_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (H : Y → ℕ) (hH : Measurable H) (hstep : ∀ x, H (T x) ≤ H x+1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ x ∂μ, ∃ C : ℕ, ∀ n : ℕ, (H (T^[n] x) : ℝ) ≤ C+δ*n := by
  let A : ℕ → Set Y := fun m => {x | m ≤ H x}
  have hAm m : MeasurableSet (A m) :=
    hH (measurableSet_Ici : MeasurableSet (Set.Ici m))
  have hAmn : Antitone A := fun i j hij x hx => hij.trans hx
  have hempty : (⋂ m, A m) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := mem_iInter.mp hx (H x+1)
    exact Nat.not_succ_le_self _ h
  have hz : μ (⋂ m, A m)=0 := by rw [hempty,measure_empty]
  filter_upwards [ae_uniform_small_occupation_of_decreasing μ hT A hAm hAmn hz hδ]
    with x hx
  obtain ⟨m,hm⟩ := hx
  let C := max m (H x)
  have hc (n : ℕ) : visitCount T (A C) n x ≤ visitCount T (A m) n x := by
    exact visitCount_mono T (fun _ hy => (le_max_left m (H x)).trans hy) n x
  refine ⟨C,?_⟩
  intro n
  have hb := height_endpoint_visit_bound T H hstep x C n (le_max_right _ _)
  have hv : (visitCount T (A C) n x : ℝ) ≤ δ*n :=
    (Nat.cast_le.mpr (hc n)).trans (hm n)
  by_cases hCn : C ≤ H (T^[n] x)
  · have hb' : (H (T^[n] x) : ℝ)-(C:ℝ) ≤ visitCount T (A C) n x := by
      exact_mod_cast hb
    linarith
  · have hb' : (H (T^[n] x) : ℝ) ≤ C := by exact_mod_cast le_of_not_ge hCn
    exact hb'.trans (le_add_of_nonneg_right (mul_nonneg hδ.le (Nat.cast_nonneg n)))

end DukePrimeDegree

end

end OAI
