import Mathlib
import OAI.Probability.CriticalPercolation.Harmonic.GeneralizedGramSpectrum

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical BigOperators Matrix

namespace CriticalPercolation.HarmonicAnalysis
variable {ι : Type*} [Fintype ι]

lemma many_small_factors (μ : ι → ℝ) (hμ : ∀ i, 1 ≤ μ i)
    (C : ℝ) (hC : 1 < C) (hprod : (∏ i, μ i) ≤ C^(Fintype.card ι)) :
    Fintype.card ι ≤ 2*(Finset.univ.filter (fun i => μ i ≤ C^2)).card := by
  let I := Finset.univ.filter (fun i => μ i ≤ C^2)
  let J := Finset.univ.filter (fun i => C^2 < μ i)
  have hj (i : ι) : (if i∈J then C^2 else 1) ≤ μ i := by
    split_ifs with hi
    · exact (Finset.mem_filter.mp hi).2.le
    · exact hμ i
  have hp := Finset.prod_le_prod₀ (fun i (_ : i∈Finset.univ) => by
      split_ifs <;> positivity) (fun i (_ : i∈Finset.univ) => hj i)
  have he : (∏ i : ι, if i∈J then C^2 else 1)=(C^2)^J.card := by
    rw [←Finset.prod_filter]
    simp
  rw [he,←pow_mul] at hp
  have hcard : 2*J.card ≤ Fintype.card ι := (pow_le_pow_iff_right₀ hC).mp (hp.trans hprod)
  have hIJ : I.card+J.card=Fintype.card ι := by
    have hh := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (p := fun i => μ i ≤ C^2)
    simpa only [not_le,Finset.card_univ] using hh
  change Fintype.card ι ≤ 2*I.card
  omega

omit [Fintype ι] in
lemma basis_support_span {E : Type*} [AddCommGroup E] [Module ℝ E] (b : Basis ι ℝ E) (I : Finset ι)
    {x : E} (hx : x∈Submodule.span ℝ (Set.range (fun i:I => b i.val))) :
    ∀ i∉I, b.repr x i=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩ := hx
    intro i hi
    have hj : j.val≠i := by intro he; exact hi (he ▸ j.property)
    simp [hj]
  | zero => simp
  | add x y hx hy ix iy =>
    intro i hi
    simp only [map_add,Finsupp.add_apply,ix i hi,iy i hi,add_zero]
  | smul a x hx ix =>
    intro i hi
    simp only [map_smul,Finsupp.smul_apply,smul_eq_mul,ix i hi,mul_zero]

theorem exists_low_growth_subspace (A B : Matrix ι ι ℝ) (hA : A.PosDef)
    (hB : B.IsHermitian) (hmono : ∀ x, matrixQuadratic A x ≤ matrixQuadratic B x)
    (C : ℝ) (hC : 1 < C) (hdet : B.det ≤ C^(Fintype.card ι)*A.det) :
    ∃ V : Submodule ℝ (ι → ℝ),
      Fintype.card ι ≤ 2*Module.finrank ℝ V ∧
      ∀ x∈V, matrixQuadratic B x ≤ C^2*matrixQuadratic A x := by
  obtain ⟨μ,b,hμ,hd,hqa,hqb⟩ := generalized_gram_spectrum A B hA hB hmono
  have hp : (∏ i, μ i) ≤ C^(Fintype.card ι) := by
    rw [hd,mul_comm (C^(Fintype.card ι))] at hdet
    exact (mul_le_mul_iff_right₀ hA.det_pos).mp (by simpa only [mul_comm A.det] using hdet)
  let I := Finset.univ.filter (fun i => μ i ≤ C^2)
  let V := Submodule.span ℝ (Set.range (fun i : I => b i.val))
  have hind : LinearIndependent ℝ (fun i : I => b i.val) :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  have hvdim : Module.finrank ℝ V=I.card := by
    exact (finrank_span_eq_card hind).trans (Fintype.card_coe I)
  refine ⟨V,?_,?_⟩
  · rw [hvdim]
    simpa only [Fintype.card_fin] using many_small_factors μ hμ C hC (by simpa using hp)
  · intro x hx
    rw [hqb,hqa,Finset.mul_sum]
    have hs := basis_support_span b I hx
    apply Finset.sum_le_sum
    intro i hi
    by_cases hiI : i∈I
    · exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hiI).2 (sq_nonneg _)
    · rw [hs i hiI,pow_two,zero_mul,mul_zero,mul_zero]

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
