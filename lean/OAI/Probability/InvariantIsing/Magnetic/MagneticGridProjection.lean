import OAI.Probability.InvariantIsing.Magnetic.MagneticRationalCover
import OAI.Probability.InvariantIsing.Fields.SpinCountMagnetization
import OAI.Probability.InvariantIsing.Fields.SpinGroupProjectionMoment
import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupAverage

namespace OAI

/-! A rational net of magnetizations gives an actual spin projection onto
a finite union of attainable group slices. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma spinGroupCount_le_size {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (σ : Spin N) (a : A) :
    spinGroupCount group σ a ≤ spinGroupSize group a := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2.1⟩

lemma spinGroupSize_sum {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) : (∑ a, (spinGroupSize group a:ℝ))=N := by
  have h := sum_grouped_sites group (fun _ => (1:ℝ))
  simpa only [mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using h.symm

theorem magnetic_grid_projection {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) {δ : ℝ} (hδ : 0<δ)
    (Q : Finset (RationalMagnetization A))
    (hQ : ∀ x : A → ℝ, (∀ a, |x a|≤1) → ∃ q∈Q, ∀ a, |x a-(q.val a:ℝ)|<δ) :
    ∃ f : Spin N → Spin N,
      (∀ σ, f σ∈Q.biUnion (fun q => spinGroupSlice group
        (fun a => magneticRoundedCount (spinGroupSize group a) (q.val a:ℝ)))) ∧
      ∀ σ, hammingDist σ (f σ)≤⌈δ*N+Fintype.card A⌉₊ := by
  classical
  let x := fun σ a => spinCountMagnetization (spinGroupSize group a) (spinGroupCount group σ a)
  choose q hq hclose using fun σ => hQ (x σ)
    (fun a => spinCountMagnetization_bounds (spinGroupCount_le_size group σ a))
  let cnt := fun q : RationalMagnetization A => fun a =>
    magneticRoundedCount (spinGroupSize group a) (q.val a:ℝ)
  have hc q a : cnt q a≤ spinGroupSize group a := magneticRoundedCount_le _ (q.property a).le
  let f := fun σ => spinGroupProjection group (cnt (q σ)) (hc (q σ)) σ
  refine ⟨f,fun σ => Finset.mem_biUnion.mpr ⟨q σ,hq σ,spinGroupProjection_mem _ _ _ _⟩,?_⟩
  intro σ
  have hb : (hammingDist σ (f σ):ℝ) ≤ δ*N+Fintype.card A := by
    rw [show f σ=spinGroupProjection group (cnt (q σ)) (hc (q σ)) σ from rfl,
      spinGroupProjection_distance_real]
    calc
      _ ≤ ∑ a, ((spinGroupSize group a:ℝ)*δ/2+1) := by
        apply Finset.sum_le_sum
        intro a _
        exact rounded_count_distance (spinGroupCount_le_size group σ a) ((q σ).property a).le
          (hclose σ a).le
      _ = (N:ℝ)*δ/2+Fintype.card A := by
        rw [Finset.sum_add_distrib,←Finset.sum_div,←Finset.sum_mul,spinGroupSize_sum]
        simp
      _ ≤ _ := by nlinarith [(Nat.cast_nonneg N : (0:ℝ)≤N)]
  exact_mod_cast hb.trans (Nat.le_ceil (δ*N+Fintype.card A))

end InvariantIsing

end

end OAI
