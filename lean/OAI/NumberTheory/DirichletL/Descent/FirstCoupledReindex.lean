import OAI.NumberTheory.DirichletL.Descent.FirstActualEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic CoprimeMobiusExtension
open RayFourExpansion MixedCrossSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem first_coprime_coupled_reindex {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i) (B : Finset ι)
    (C₁ C₂ : Finset ι → ℂ) (H : Finset ι → Finset ι → ℂ) (h : Eis) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then
      H S T * star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
        (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ D ∈ B.powerset, supportMobius P D * rowCoprimeMask P D h *
      ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
        H (D ∪ U) (D ∪ V) *
          star (supportMobius P U * C₁ (D ∪ U) * star (finiteSquarefreeRow P hg U h)) *
            (supportMobius P V * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg V h)) := by
  rw [double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← prime_product_moebius P hprime hinj D]
  change supportMobius P D * _ = _
  rw [mul_assoc]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  have hdV : Disjoint D V := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right
  have hmu (S T : Finset ι) (hd : Disjoint S T) :
      supportMobius P (S ∪ T) = supportMobius P S * supportMobius P T := by
    simp only [supportMobius,prime_product_moebius P hprime hinj,
      Finset.card_union_of_disjoint hd,pow_add]
  have hrow (S T : Finset ι) (hd : Disjoint S T) :
      finiteSquarefreeRow P hg (S ∪ T) h =
        finiteSquarefreeRow P hg S h * finiteSquarefreeRow P hg T h := Finset.prod_union hd
  rw [hmu D U hdU,hmu D V hdV,hrow D U hdU,hrow D V hdV]
  simp only [star_mul,star_star,star_supportMobius]
  have hm := supportMobius_sq P hprime hinj D
  have hz := finiteSquarefreeRow_self_pair P hg D h
  calc
    _ = (supportMobius P D * supportMobius P D) *
        (star (finiteSquarefreeRow P hg D h)*finiteSquarefreeRow P hg D h) *
        (H (D ∪ U) (D ∪ V) *
          (supportMobius P U * star (C₁ (D ∪ U)) * finiteSquarefreeRow P hg U h) *
          (supportMobius P V * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg V h))) := by ring
    _ = _ := by rw [hm,hz]; ring

theorem first_quadratic_coupled_reindex {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (B : Finset ι)
    (C₁ C₂ : Finset ι → ℂ) (H : Finset ι → Finset ι → ℂ) (h : Eis) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then
      H S T * quadraticCrossPhase p hg S T *
        star (supportMobius (fun i => Ideal.span {p i}) S * C₁ S * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S h)) *
        (supportMobius (fun i => Ideal.span {p i}) T * C₂ T * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T h)) else 0) =
    ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset, supportMobius (fun i => Ideal.span {p i}) D * rowCoprimeMask (fun i => Ideal.span {p i}) D h *
        ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
          H (D ∪ U) (D ∪ V) *
          star (supportMobius (fun i => Ideal.span {p i}) U *
            (star (supportRay p r.1 (D ∪ U))*C₁ (D ∪ U)) * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U h)) *
          (supportMobius (fun i => Ideal.span {p i}) V *
            (supportRay p r.2 (D ∪ V)*C₂ (D ∪ V)) * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V h)) := by
  let P := fun i => Ideal.span {p i}
  have hcop : Pairwise (Function.onFun IsCoprime P) := by
    intro i j hij
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hij)
  have hprime (i : ι) : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  let T := fun (r : RayCharacter × RayCharacter) (S V : Finset ι) => if Disjoint S V then
    H S V * star (supportMobius P S * (star (supportRay p r.1 S)*C₁ S) * star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P V * (supportRay p r.2 V*C₂ V) * star (finiteSquarefreeRow P hg V h)) else 0
  have he (S V : Finset ι) :
      (if Disjoint S V then H S V * quadraticCrossPhase p hg S V *
        star (supportMobius P S*C₁ S*star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P V*C₂ V*star (finiteSquarefreeRow P hg V h)) else 0) =
      ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2*T r S V := by
    by_cases hd : Disjoint S V
    · rw [ite_eq_left hd,quadraticCrossPhase_character_expansion p hp hcop hg hc S V hd]
      simp only [Fintype.sum_prod_type,T,ite_eq_left hd,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro η hη
      simp only [supportRay,star_mul,star_star]
      ring
    · simp [T,hd]
  calc
    _ = ∑ S ∈ B.powerset, ∑ V ∈ B.powerset,
        ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2*T r S V := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun V hV => he S V)
    _ = ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
        ∑ S ∈ B.powerset, ∑ V ∈ B.powerset, T r S V := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ r : RayCharacter × RayCharacter,
            ∑ V ∈ B.powerset, crossCoeff r.1 r.2*T r S V := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      exact first_coprime_coupled_reindex P hprime hinj hg B _ _ H h

end
end SevenEighths.InverseMoment

end OAI
