import Mathlib
import OAI.Analysis.Commutator.EqualTraceRefinement
import OAI.Analysis.Commutator.FiniteFactorMatrices
import OAI.Analysis.Commutator.SpectralStep

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.MatrixApproximation

open TracialGNS ProjectionSum

section Norm

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma vector_norm_le (hone : τ 1=1) (a : A) : ‖algebraVector τ a‖≤‖a‖ := by
  rw [algebraVector_apply,←left_vacuum]
  calc
    _≤‖τ.gnsStarAlgHom a‖*‖vacuum τ‖ := ContinuousLinearMap.le_opNorm _ _
    _≤‖a‖ := by rw [vacuum_norm τ hone,mul_one]; exact NonUnitalStarAlgHom.norm_apply_le _ a

lemma step_error {J : Type*} [Fintype J] (p s : J → A) (c : J → ℝ)
    (hp : ∀ j,IsStarProjection (p j)) (hs : ∀ j,IsStarProjection (s j))
    (hsp : ∀ j,s j ≤ p j) {d : ℝ} (hd : 0≤d)
    (ht : ∀ j,(τ (p j-s j)).re≤d^2) :
    ‖algebraVector τ ((∑ j,(c j:ℂ) • p j)-(∑ j,(c j:ℂ) • s j))‖≤(∑ j,‖c j‖)*d := by
  have hn (j : J) : ‖algebraVector τ (p j-s j)‖≤d := by
    have hproj := ((hs j).le_iff_sub (hp j)).mp (hsp j)
    have hsq := vector_projection_norm_sq τ hproj
    have hn0 := norm_nonneg (algebraVector τ (p j-s j))
    nlinarith [ht j]
  rw [←Finset.sum_sub_distrib]
  simp only [←smul_sub,map_sum,map_smul]
  calc
    _≤∑ j,‖(c j:ℂ) • algebraVector τ (p j-s j)‖ := norm_sum_le _ _
    _≤∑ j,‖c j‖*d := Finset.sum_le_sum (fun j _ => by
      rw [norm_smul,Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hn j) (norm_nonneg _))
    _=(∑ j,‖c j‖)*d := (Finset.sum_mul _ _ _).symm

end Norm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hnormal : NormalGNS.BoundedWOTContinuous M τ)
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)

include hτ hnormal hfaith hone in
theorem exists_matrix_approximation (hfac : FactorCorner.IsFactor M)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections M) (y : M) (hy : IsSelfAdjoint y)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I) (_ : Nonempty I)
      (φ : Matrix I I ℂ →⋆ₐ[ℂ] M) (x : Matrix I I ℂ),
      Function.Injective φ ∧ 2≤Fintype.card I ∧ ‖algebraVector τ (y-φ x)‖<ε := by
  classical
  obtain ⟨J,hJ,p,c,hp,ho,hpsum,he⟩ :=
    SpectralPartition.exists_spectral_step_subtype M y hy (half_pos hε)
  let : Fintype J := hJ
  let C : ℝ := ∑ j,‖c j‖
  let d : ℝ := ε/(2*(C+1))
  have hC : 0≤C := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hd : 0<d := div_pos hε (by positivity)
  obtain ⟨b,hb⟩ := exists_nat_gt (max (1:ℝ) (1/d^2))
  have hb1 : (1:ℝ)<b := (le_max_left _ _).trans_lt hb
  have hbNat : 1<b := by exact_mod_cast hb1
  have hb0 : 0<b := lt_trans Nat.zero_lt_one hbNat
  have hbR : (0:ℝ)<b := Nat.cast_pos.mpr hb0
  have hbd : 1/(b:ℝ)<d^2 := by
    have hlt : 1/d^2<(b:ℝ) := (le_max_right _ _).trans_lt hb
    have hs : 0<d^2 := sq_pos_of_pos hd
    exact (div_lt_iff₀ hbR).mpr (by
      have hh := (div_lt_iff₀ hs).mp hlt
      nlinarith)
  obtain ⟨I,hI,q,s,hq,hqo,hqs,hs⟩ :=
    NormalGNS.equal_trace_refinement M τ hτ hnormal hfaith hone hdiffuse p hp ho hpsum b hb0
  let : Fintype I := hI
  have hcard : (Fintype.card I:ℝ)/(b:ℝ)=1 := by
    have hh := congrArg (fun a : M => (τ a).re) hqs
    rw [map_sum,hone,Complex.one_re] at hh
    change Complex.reAddGroupHom (∑ i,τ (q i))=1 at hh
    rw [map_sum] at hh
    change (∑ i,(τ (q i)).re)=1 at hh
    simpa only [hq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one_div] using hh
  have hcardNat : Fintype.card I=b := by
    have hh := (div_eq_one_iff_eq (ne_of_gt hbR)).mp hcard
    exact_mod_cast hh
  have hcard0 : 0<Fintype.card I := by rw [hcardNat]; exact hb0
  let : Nonempty I := Fintype.card_pos_iff.mp hcard0
  have heq : ∀ i j,τ (q i)=τ (q j) := by
    intro i j
    apply Complex.ext
    · rw [(hq i).2,(hq j).2]
    · exact (τ.map_nonneg (hq i).1.nonneg).2.symm.trans (τ.map_nonneg (hq j).1.nonneg).2
  obtain ⟨φ,hφ⟩ := FiniteFactorMatrices.partition_representation M hfac τ hτ hfaith q
    (fun i => (hq i).1) heq hqo hqs
  have hadj : StarAlgebra.adjoin ℂ (Set.range q)≤φ.range := by
    apply StarAlgebra.adjoin_le
    rintro a ⟨i,rfl⟩
    exact ⟨Matrix.single i i 1,hφ i⟩
  have hmem : (∑ j,(c j:ℂ) • s j)∈φ.range := by
    apply φ.range.sum_mem
    intro j hj
    exact φ.range.smul_mem (hadj (hs j).2.2.2) _
  obtain ⟨x,hx⟩ := hmem
  change φ x=(∑ j,(c j:ℂ) • s j) at hx
  have hneq : (0:M)≠1 := by
    intro hz
    have ht := congrArg τ hz
    rw [map_zero,hone] at ht
    exact zero_ne_one ht
  let : Nontrivial M := ⟨⟨0,1,hneq⟩⟩
  refine ⟨I,hI,inferInstance,inferInstance,φ,x,φ.toAlgHom.toRingHom.injective,?_,?_⟩
  · rw [hcardNat]; omega
  · rw [hx]
    have herr := step_error τ p s c hp (fun j => (hs j).1) (fun j => (hs j).2.1)
      hd.le (fun j => ((hs j).2.2.1.trans hbd).le)
    have hCd : C*d<ε/2 := by
      have hh : d*(2*(C+1))=ε := div_mul_cancel₀ _ (by positivity)
      nlinarith
    calc
      _≤‖algebraVector τ (y-∑ j,(c j:ℂ) • p j)‖+
          ‖algebraVector τ ((∑ j,(c j:ℂ) • p j)-(∑ j,(c j:ℂ) • s j))‖ := by
        rw [map_sub,map_sub,map_sub]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _≤‖y-∑ j,(c j:ℂ) • p j‖+C*d := add_le_add (vector_norm_le τ hone _) herr
      _<ε := by linarith

end Kadison.MatrixApproximation

end

end
end

end OAI
