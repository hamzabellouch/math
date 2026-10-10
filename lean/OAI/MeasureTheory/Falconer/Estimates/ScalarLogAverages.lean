import OAI.MeasureTheory.Falconer.Estimates.ScalarCorrelatedWeights

namespace OAI

/-! Finite coefficient averages for the multiscale porous argument. -/
namespace Falconer

noncomputable def scalarAverage {β : Type*} (B : Finset β) (f : β → ℝ) : ℝ :=
  (∑ b ∈ B, f b)/(B.card : ℝ)

 theorem scalarAverage_mono {β : Type*} (B : Finset β) {f g : β → ℝ}
    (h : ∀ b ∈ B, f b ≤ g b) : scalarAverage B f ≤ scalarAverage B g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

 theorem scalarAverage_const {β : Type*} (B : Finset β) (hB : B.Nonempty) (c : ℝ) :
    scalarAverage B (fun _ => c) = c := by
  have hn : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
  simp only [scalarAverage,Finset.sum_const,nsmul_eq_mul]
  field_simp

 theorem scalarAverage_add {β : Type*} (B : Finset β) (f g : β → ℝ) :
    scalarAverage B (fun b => f b+g b) = scalarAverage B f+scalarAverage B g := by
  simp only [scalarAverage,Finset.sum_add_distrib,add_div]

 theorem scalarAverage_sum {ι β : Type*} (I : Finset ι) (B : Finset β) (f : ι → β → ℝ) :
    scalarAverage B (fun b => ∑ i ∈ I, f i b) = ∑ i ∈ I, scalarAverage B (f i) := by
  simp only [scalarAverage,← Finset.sum_div]
  rw [Finset.sum_comm]

 theorem scalar_log_sum_ge {ι : Type*} (I : Finset ι) (hI : I.Nonempty)
    (f : ι → ℝ) (hf : ∀ i ∈ I, 0 < f i) :
    Real.log (I.card : ℝ)+scalarAverage I (fun i => Real.log (f i)) ≤
      Real.log (∑ i ∈ I, f i) := by
  have hn : 0 < (I.card : ℝ) := by exact_mod_cast hI.card_pos
  have hw : ∑ _i ∈ I, 1/(I.card : ℝ) = 1 := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_one_div_cancel hn.ne'
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (fun _i (_hi : _i ∈ I) => (div_nonneg (by norm_num : (0:ℝ) ≤ 1) hn.le))
    hw hf
  have hsum (g : ι → ℝ) : (∑ i ∈ I, (1/(I.card : ℝ))*g i) = scalarAverage I g := by
    rw [← Finset.mul_sum]
    unfold scalarAverage
    ring
  simp only [smul_eq_mul] at hj
  rw [hsum,hsum] at hj
  have hs : 0 < ∑ i ∈ I, f i := Finset.sum_pos hf hI
  have he : Real.log (scalarAverage I f) = Real.log (∑ i ∈ I, f i)-Real.log (I.card : ℝ) := by
    exact Real.log_div hs.ne' hn.ne'
  rw [he] at hj
  linarith

 theorem scalar_average_log_sum_ge {ι β : Type*} (I : Finset ι) (B : Finset β)
    (hI : I.Nonempty) (hB : B.Nonempty) (f : ι → β → ℝ)
    (hf : ∀ i ∈ I, ∀ b ∈ B, 0 < f i b) {a : ℝ}
    (ha : ∀ i ∈ I, a ≤ scalarAverage B (fun b => Real.log (f i b))) :
    Real.log (I.card : ℝ)+a ≤ scalarAverage B (fun b => Real.log (∑ i ∈ I, f i b)) := by
  have hj := scalarAverage_mono B (fun b hb =>
    scalar_log_sum_ge I hI (fun i => f i b) (fun i hi => hf i hi b hb))
  rw [scalarAverage_add,scalarAverage_const B hB] at hj
  have he : scalarAverage B (fun b => scalarAverage I (fun i => Real.log (f i b))) =
      scalarAverage I (fun i => scalarAverage B (fun b => Real.log (f i b))) := by
    unfold scalarAverage
    rw [← Finset.sum_div,← Finset.sum_div,Finset.sum_comm]
    ring
  rw [he] at hj
  have hl := scalarAverage_mono I (fun i hi => ha i hi)
  rw [scalarAverage_const I hI] at hl
  linarith

 theorem scalar_average_weighted_branch {ι β : Type*} (I : Finset ι) (B : Finset β)
    (hI : I.Nonempty) (hB : B.Nonempty)
    (f : ι → β → ℝ) (w q : β → ℝ)
    (hf : ∀ i ∈ I, ∀ b ∈ B, 0 < f i b) (hw : ∀ b ∈ B, 0 < w b)
    (hstep : ∀ b ∈ B, w b*(∑ i ∈ I, f i b) ≤ q b)
    {a ell : ℝ} (ha : ∀ i ∈ I, a ≤ scalarAverage B (fun b => Real.log (f i b)))
    (hell : ell ≤ scalarAverage B (fun b => Real.log (w b))) :
    ell+Real.log (I.card : ℝ)+a ≤ scalarAverage B (fun b => Real.log (q b)) := by
  have hs := scalar_average_log_sum_ge I B hI hB f hf ha
  have hl := scalarAverage_mono B (fun b hb =>
    Real.log_le_log (mul_pos (hw b hb) (Finset.sum_pos (fun i hi => hf i hi b hb) hI)) (hstep b hb))
  have he : scalarAverage B (fun b => Real.log (w b*(∑ i ∈ I, f i b))) =
      scalarAverage B (fun b => Real.log (w b))+
        scalarAverage B (fun b => Real.log (∑ i ∈ I, f i b)) := by
    calc
      _ = scalarAverage B (fun b => Real.log (w b)+Real.log (∑ i ∈ I, f i b)) := by
        unfold scalarAverage
        congr 1
        exact Finset.sum_congr rfl (fun b hb => Real.log_mul (hw b hb).ne'
          (Finset.sum_pos (fun i hi => hf i hi b hb) hI).ne')
      _ = _ := scalarAverage_add B _ _
  rw [he] at hl
  linarith

 theorem scalar_average_weighted_children {ι β : Type*} (I : Finset ι) (B : Finset β)
    (hI : I.Nonempty) (hB : B.Nonempty) (f w : ι → β → ℝ) (q : β → ℝ)
    (hf : ∀ i ∈ I, ∀ b ∈ B, 0 < f i b)
    (hw : ∀ i ∈ I, ∀ b ∈ B, 0 < w i b)
    (hstep : ∀ b ∈ B, (∑ i ∈ I, w i b*f i b) ≤ q b)
    {a ell : ℝ} (ha : ∀ i ∈ I, a ≤ scalarAverage B (fun b => Real.log (f i b)))
    (hell : ∀ i ∈ I, ell ≤ scalarAverage B (fun b => Real.log (w i b))) :
    Real.log (I.card : ℝ)+ell+a ≤ scalarAverage B (fun b => Real.log (q b)) := by
  have ht : ∀ i ∈ I, ell+a ≤ scalarAverage B (fun b => Real.log (w i b*f i b)) := by
    intro i hi
    have he : scalarAverage B (fun b => Real.log (w i b*f i b)) =
        scalarAverage B (fun b => Real.log (w i b))+scalarAverage B (fun b => Real.log (f i b)) := by
      calc
        _ = scalarAverage B (fun b => Real.log (w i b)+Real.log (f i b)) := by
          unfold scalarAverage
          congr 1
          exact Finset.sum_congr rfl (fun b hb => Real.log_mul (hw i hi b hb).ne' (hf i hi b hb).ne')
        _ = _ := scalarAverage_add B _ _
    rw [he]
    exact add_le_add (hell i hi) (ha i hi)
  have hs := scalar_average_log_sum_ge I B hI hB (fun i b => w i b*f i b)
    (fun i hi b hb => mul_pos (hw i hi b hb) (hf i hi b hb)) ht
  have hq := scalarAverage_mono B (fun b hb => Real.log_le_log
    (Finset.sum_pos (fun i hi => mul_pos (hw i hi b hb) (hf i hi b hb)) hI) (hstep b hb))
  linarith

 theorem scalar_exp_average_log_le {β : Type*} (B : Finset β) (hB : B.Nonempty)
    (q : β → ℝ) (hq : ∀ b ∈ B, 0 < q b) :
    Real.exp (scalarAverage B (fun b => Real.log (q b))) ≤ scalarAverage B q := by
  have hn : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
  have he : (B.card : ℝ)*scalarAverage B (fun b => Real.log (q b)) =
      ∑ b ∈ B, Real.log (q b) := by
    unfold scalarAverage
    field_simp
  have hh := finite_correlated_product_mean ({0} : Finset ℕ) B hB
    (fun _ b => q b) (fun _ => scalarAverage B (fun b => Real.log (q b)))
    (fun _ _ b hb => hq b hb) (fun _ _ => le_of_eq he)
  simpa only [Finset.sum_singleton,Finset.prod_singleton,scalarAverage] using hh

end Falconer

end OAI
