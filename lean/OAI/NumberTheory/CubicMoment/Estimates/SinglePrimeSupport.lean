import OAI.NumberTheory.CubicMoment.Estimates.GramStructuredRows

namespace OAI

/-! A prime convolution with one coordinate equals its weighted prime set,
with the same exclusions and weights in the semiprime application. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma orderedConvolutionSupport_unit (S : Finset Eisenstein) :
    orderedConvolutionSupport (fun _ : Unit => S) = S := by
  ext n
  constructor
  · intro hn
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hn
    simpa only [Fintype.prod_unique] using Fintype.mem_piFinset.mp hf ()
  · intro hn
    apply Finset.mem_image.mpr
    refine ⟨fun _ : Unit => n,Fintype.mem_piFinset.mpr (fun _ => hn),?_⟩
    simp only [Fintype.prod_unique]

lemma orderedConvolution_unit (S : Finset Eisenstein) (v : Eisenstein → ℂ)
    (n : Eisenstein) :
    orderedConvolution (fun _ : Unit => S) (fun _ => v) n = if n ∈ S then v n else 0 := by
  unfold orderedConvolution
  by_cases hn : n ∈ S
  · rw [ite_eq_left hn]
    rw [Finset.sum_eq_single (fun _ : Unit => n)]
    · simp only [Fintype.prod_unique]
    · intro f hf hne
      exfalso
      apply hne
      funext i
      cases i
      simpa only [Fintype.prod_unique] using (Finset.mem_filter.mp hf).2
    · intro hf
      exact (hf (Finset.mem_filter.mpr
        ⟨Fintype.mem_piFinset.mpr (fun _ => hn),by simp only [Fintype.prod_unique]⟩)).elim
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro f hf
    obtain ⟨hf,hprod⟩ := Finset.mem_filter.mp hf
    have hfn : f () = n := by simpa only [Fintype.prod_unique] using hprod
    exact (hn (hfn ▸ Fintype.mem_piFinset.mp hf ())).elim

lemma fullSquarefreePrimeSupport_unit (R B : ℝ) (W : ℝ → ℂ) :
    fullSquarefreePrimeSupport R (fun _ : Unit => W) (fun _ => B) 1 =
      fullPrimeSupport R (fun _ : Unit => W) (fun _ => B) () := by
  rw [fullSquarefreePrimeSupport]
  change (orderedConvolutionSupport
    (fun _ : Unit => fullPrimeSupport R (fun _ : Unit => W) (fun _ => B) ())).filter
      (fun b => Squarefree b ∧ IsCoprime b 1) = _
  rw [orderedConvolutionSupport_unit]
  apply Finset.filter_eq_self.mpr
  intro p hp
  exact ⟨(fullPrimeSupport_prime R (fun _ : Unit => W) (fun _ => B) () p hp).2.squarefree,
    isCoprime_one_right⟩

lemma fullPrimeCoefficient_unit {R B : ℝ} {W : ℝ → ℂ} {p : Eisenstein}
    (hp : p ∈ fullPrimeSupport R (fun _ : Unit => W) (fun _ => B) ()) :
    fullPrimeCoefficient R (fun _ : Unit => W) (fun _ => B) p = W (norm p/B) := by
  rw [fullPrimeCoefficient,squarefreeConvolution,
    ite_eq_left (fullPrimeSupport_prime R (fun _ : Unit => W) (fun _ => B) () p hp).2.squarefree]
  change orderedConvolution
    (fun _ : Unit => fullPrimeSupport R (fun _ : Unit => W) (fun _ => B) ())
    (fun _ => fun n => W (norm n/B)) p = _
  rw [orderedConvolution_unit,ite_eq_left hp]

end CubicFirstMoment

end

end OAI
