import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.CountableFieldEmbedding

namespace OAI

section
noncomputable section
open Set Function Cardinal
open scoped Classical

namespace CriticalPercolation.Arithmetic

lemma exists_transcendental_complex_norm_gt_one : ∃ z : ℂ, Transcendental ℚ z ∧ 1<‖z‖ := by
  have hex : ∃ y : ℝ, Transcendental ℚ y := by
    by_contra hn
    push Not at hn
    let : Algebra.IsAlgebraic ℚ ℝ := ⟨fun x => Classical.not_not.mp (hn x)⟩
    have hh := Algebra.IsAlgebraic.cardinalMk_le_max ℚ ℝ
    have hq : #(ℚ)≤ℵ₀ := mk_le_aleph0
    rw [max_eq_right hq] at hh
    exact (aleph0_lt_mk (α:=ℝ)).not_ge hh
  obtain ⟨y,hy⟩ := hex
  obtain ⟨n,hn⟩ := exists_nat_gt (‖y‖+2)
  have hpos : 1<y+(n:ℝ) := by
    have hab : -‖y‖≤y := by simpa only [Real.norm_eq_abs] using neg_abs_le y
    linarith
  have ht : Transcendental ℚ (y+(n:ℝ)) := by
    intro halg
    exact hy (by simpa only [add_sub_cancel_right] using halg.sub (isAlgebraic_natCast (R:=ℚ) n))
  refine ⟨(y+(n:ℝ):ℝ),?_,?_⟩
  · exact (transcendental_algebraMap_iff (R:=ℚ) (S:=ℝ) (A:=ℂ) (algebraMap ℝ ℂ).injective).mpr ht
  · simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (lt_trans zero_lt_one hpos)] using hpos

lemma exists_embedding_sending_transcendental {k K F : Type} [Field k] [Field K] [Field F]
    [Algebra k K] [Algebra k F] [Countable k] [Countable K] [IsAlgClosed F] [Uncountable F]
    (x : K) (hx : Transcendental k x) (y : F) (hy : Transcendental k y) :
    ∃ f : K →+* F, f x=y := by
  let v : Unit → K := fun _ => x
  let w : Unit → F := fun _ => y
  have hv : AlgebraicIndependent k v := algebraicIndependent_unique_type_iff.mpr hx
  have hw : AlgebraicIndependent k w := algebraicIndependent_unique_type_iff.mpr hy
  let A := IntermediateField.adjoin k (Set.range v)
  let φ : A →+* F := (IsFractionRing.lift
    (algebraicIndependent_iff_injective_aeval.mp hw)).comp hv.reprField.toRingHom
  let a : A := ⟨x,IntermediateField.subset_adjoin k (Set.range v) ⟨(),rfl⟩⟩
  have hφ : φ a=y := by
    let q : FractionRing (MvPolynomial Unit k) := algebraMap (MvPolynomial Unit k) _ (MvPolynomial.X ())
    have ha : hv.aevalEquivField q=a := by
      apply Subtype.ext
      rw [hv.aevalEquivField_algebraMap_apply_coe]
      simp only [MvPolynomial.aeval_X]
      rfl
    rw [←ha]
    change IsFractionRing.lift (algebraicIndependent_iff_injective_aeval.mp hw)
      (hv.aevalEquivField.symm (hv.aevalEquivField q))=y
    rw [hv.aevalEquivField.symm_apply_apply]
    simp only [q,IsFractionRing.lift_algebraMap]
    exact MvPolynomial.aeval_X w ()
  obtain ⟨f,hf⟩ := exists_extension_of_countable (k:=A) (K:=K) φ
  refine ⟨f,?_⟩
  exact (RingHom.congr_fun hf a).trans hφ

lemma exists_complex_embedding_norm_gt_one {K : Type} [Field K] [CharZero K] [Countable K]
    (x : K) (hx : Transcendental ℚ x) : ∃ f : K →+* ℂ, 1<‖f x‖ := by
  let : Uncountable ℂ := uncountable_complete_normed_field ℂ
  obtain ⟨y,hy,hyNorm⟩ := exists_transcendental_complex_norm_gt_one
  obtain ⟨f,hf⟩ := exists_embedding_sending_transcendental x hx y hy
  exact ⟨f,hf ▸ hyNorm⟩

end CriticalPercolation.Arithmetic
end
end

end OAI
