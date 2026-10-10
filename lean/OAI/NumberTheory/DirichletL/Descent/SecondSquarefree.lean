import OAI.NumberTheory.DirichletL.Descent.SecondMarkedEnergy
import OAI.NumberTheory.DirichletL.Descent.SecondWeights

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourcePrime sourceIdeal_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hcop in
omit [DecidableEq ι] in
theorem sourceIdeal_squarefree (S : Finset ι) : Squarefree (sourceIdeal p S) := by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact (hcop hij).isRelPrime
  · intro i hi
    exact (sourcePrime p i).property.squarefree

include hcop in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_coprime_of_disjoint (S T : Finset ι) (hST : Disjoint S T) :
    IsCoprime (sourceIdeal p S) (sourceIdeal p T) := by
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.prod_right
  intro j hj
  exact hcop (fun he => Finset.disjoint_left.mp hST hi (he.symm ▸ hj))

omit [DecidableEq ι] in
lemma prime_span_coprime_of_not_mem (i : ι) (c : Eis) (hc : c ∉ Ideal.span {p i}) :
    IsCoprime (Ideal.span {p i}) (Ideal.span {c} : Ideal Eis) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hne
  have he := (inferInstance : (Ideal.span {p i}).IsMaximal).eq_of_le hne le_sup_left
  apply hc
  rw [he]
  exact (show Ideal.span {c} ≤ (Ideal.span {p i} : Ideal Eis) ⊔ Ideal.span {c} from le_sup_right)
    (Ideal.subset_span (by simp))

omit [DecidableEq ι] in
theorem sourceIdeal_coprime_of_not_mem (S : Finset ι) (c : Eis)
    (hc : ∀ i ∈ S, c ∉ Ideal.span {p i}) :
    IsCoprime (sourceIdeal p S) (Ideal.span {c} : Ideal Eis) := by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  exact IsCoprime.prod_left (fun i hi => prime_span_coprime_of_not_mem p i c (hc i hi))

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem jLabel_span_dvd_source (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (Ideal.span {jLabel p B v ε₁ ε₂} : Ideal Eis) ∣ sourceIdeal p B := by
  apply span_dvd_of_element_dvd
  change (∏ i ∈ B,p i^bit (retained (parity (v i)) (ε₁ i) (ε₂ i))) ∣ ∏ i ∈ B,p i
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  cases retained (parity (v i)) (ε₁ i) (ε₂ i) <;> simp [bit]

omit [DecidableEq ι] in
theorem secondInputCoefficient_zero_of_label_mem (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S) (hc : c ∈ Ideal.span {p i}) :
    secondInputCoefficient p hg Ψ m c d H S = 0 := by
  have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S c = 0 := by
    simp only [rowCoprimeMask,ite_eq_left (show ∃ i ∈ S,c ∈ Ideal.span {p i} from ⟨i,hi,hc⟩)]
  have hr := row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S c hz
  simp only [secondInputCoefficient,hr,zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,zero_mul]

theorem secondPreColumn_zero_of_mask_label_mem (Ψ : Eis →* ℂ) (m c d e k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hc : m*c ∈ Ideal.span {p i}) : secondPreColumn p hp hcop hg Ψ m c d e k H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hc with hm|hc
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S m = 0 := by
      simp only [rowCoprimeMask,ite_eq_left (show ∃ i ∈ S,m ∈ Ideal.span {p i} from ⟨i,hi,hm⟩)]
    simp only [secondPreColumn,hz,mul_zero,zero_mul]
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S c = 0 := by
      simp only [rowCoprimeMask,ite_eq_left (show ∃ i ∈ S,c ∈ Ideal.span {p i} from ⟨i,hi,hc⟩)]
    have hr := row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S c hz
    simp only [secondPreColumn,hr,zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,zero_mul]

theorem secondSignedSourceWeight_nonzero_masks
    (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex) (x : SecondExpansionData ι)
    (hE : x.divisor ⊆ x.sourceCommon)
    (hw : secondSignedSourceWeight p hp hcop hg Ψ m c d z x ≠ 0) :
    IsCoprime (sourceIdeal p x.sourceCommon) (Ideal.span {c}) ∧
    IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.sourceCommon * Ideal.span {c}) := by
  constructor
  · apply sourceIdeal_coprime_of_not_mem p
    intro i hi hc
    have hz := secondInputCoefficient_zero_of_label_mem p hg Ψ m c d (fun _ => 1) x.sourceCommon i hi hc
    apply hw
    simp only [secondSignedSourceWeight,hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
      Complex.ofReal_zero,zero_mul]
  · change IsCoprime (sourceIdeal p x.overlap) (Ideal.span {∏ i ∈ x.sourceCommon,p i} * Ideal.span {c})
    rw [Ideal.span_singleton_mul_span_singleton]
    apply sourceIdeal_coprime_of_not_mem p
    intro i hi hc
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
    let r := secondExpansionQuotient p x
    have her : e*r = ∏ j ∈ x.sourceCommon,p j := by
      dsimp only [r]
      rw [secondExpansionQuotient_of_subset p x hE]
      exact (secondMaskQuotient_spec p _ _ hE).symm
    have hmc : (m*(e*r))*c ∈ Ideal.span {p i} := by
      rw [her,mul_assoc]
      exact Ideal.mul_mem_left _ m hc
    have hz := secondPreColumn_zero_of_mask_label_mem p hp hcop hg (secondRayPlus Ψ z)
      (m*(e*r)) c d e (-x.frequency) (fun _ => 1) x.overlap i hi hmc
    dsimp only [e,r] at hz
    apply hw
    simp only [secondSignedSourceWeight,secondCommonWeight,hz,mul_zero]

def actualSecondSignedWeight {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn) : ℂ :=
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  secondSignedSourceWeight p hp hcop hg Ψ
    (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
      x.cube.leftBit x.cube.rightBit*d) c d z x.second

theorem actualSecondSignedWeight_norm_le_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn) : ‖actualSecondSignedWeight p hp hcop hg Ψ m z x‖ ≤ 1 :=
  secondSignedSourceWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ _ _ _ z x.second

theorem actual_second_nonzero_weight_squarefree
    {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (hw : actualSecondSignedWeight p hp hcop hg Ψ m z x ≠ 0) (u v : Eisˣ) :
    Squarefree (actualSecondChild p u v x).2.1 := by
  let J : Ideal Eis := Ideal.span {jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}
  let C := sourceIdeal p x.firstCommon
  let E := sourceIdeal p x.second.divisor
  let G := sourceIdeal p x.second.sourceCommon
  let V := sourceIdeal p x.second.overlap
  have hj : J ∣ sourceIdeal p x.cube.support := jLabel_span_dvd_source p _ _ _ _
  have hJ : Squarefree J := (sourceIdeal_squarefree p hcop x.cube.support).squarefree_of_dvd hj
  have hC : Squarefree C := sourceIdeal_squarefree p hcop _
  have hG : Squarefree G := sourceIdeal_squarefree p hcop _
  have hV : Squarefree V := sourceIdeal_squarefree p hcop _
  have hJC : IsCoprime J C :=
    (sourceIdeal_coprime_of_disjoint p hcop x.cube.support x.firstCommon hCB.symm).of_isCoprime_of_dvd_left hj
  have hdg : E ∣ G := sourceIdeal_dvd p _ _ hE
  have hcspan : Ideal.span {(∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} = C*J :=
    (Ideal.span_singleton_mul_span_singleton _ _).symm
  obtain ⟨hgmask,hvmask⟩ := secondSignedSourceWeight_nonzero_masks p hp hcop hg Ψ _ _ _ z x.second hE hw
  rw [hcspan] at hgmask hvmask
  change IsCoprime G (C*J) at hgmask
  change IsCoprime V (G*(C*J)) at hvmask
  have heJC : IsCoprime E (J*C) := by
    simpa only [mul_comm] using hgmask.of_isCoprime_of_dvd_left hdg
  have hdiv : J*C*E ∣ G*(C*J) := by
    obtain ⟨r,hr⟩ := hdg
    refine ⟨r,?_⟩
    rw [hr]
    ring
  have hvJCE := hvmask.of_isCoprime_of_dvd_right hdiv
  change Squarefree (J*C*E*V)
  exact squarefree_mul_iff.mpr ⟨hvJCE.symm.isRelPrime,
    squarefree_mul_iff.mpr ⟨heJC.symm.isRelPrime,
      squarefree_mul_iff.mpr ⟨hJC.isRelPrime,hJ,hC⟩,hG.squarefree_of_dvd hdg⟩,hV⟩

end
end SevenEighths.InverseMoment

end OAI
