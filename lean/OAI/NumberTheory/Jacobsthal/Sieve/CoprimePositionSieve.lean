import OAI.NumberTheory.Jacobsthal.Estimates.ActualModelTargets

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def divisorJoint (w : ℝ) (H : ℕ) (C0 : ℤ) (beta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (m : ℤ) (k : ZMod (divisorModulus w H)) : Prop :=
  ∀ t ∈ divisorPrimes w H,∀ j ∈ S,(k.val : ZMod t)+divisorPhase C0 m t*(j : ZMod t) ≠ beta t

def coprimeJoint (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (m : ℤ) (p : (ZMod (coprimeModulus w H))ˣ) : Prop :=
  ∀ t ∈ coprimePrimes w H,∀ j ∈ S,(p.val.val : ZMod t)*(qA : ZMod t)*
    ((m : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ delta t

theorem jointCondition_coordinates (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (m : ℤ) (s : Pattern w H) :
    jointCondition w H C0 qA beta delta S (m,s) ↔
      divisorJoint w H C0 beta S m s.2 ∧ coprimeJoint w H qA delta S m s.1 :=
  jointCondition_split w H C0 qA beta delta S (m,s)

theorem divisorJoint_card (w : ℝ) (H : ℕ) (C0 : ℤ) (beta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (m : ℤ) (hC0 : Int.gcd C0 (H : ℤ) = 1) (hm : m.natAbs.Coprime H) :
    (Finset.univ.filter (divisorJoint w H C0 beta S m)).card =
      ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
  let u (t : ℕ) : (ZMod t)ˣ :=
    if ht : t ∣ H then divisorPhaseUnit H C0 m hC0 hm t ht else 1
  have hunit (t : ℕ) (ht : t ∈ divisorPrimes w H) : (u t : ZMod t) = divisorPhase C0 m t := by
    simp only [u,dite_eq_left (Finset.mem_filter.mp ht).2,divisorPhaseUnit_coe]
  have hP (t : ℕ) (ht : t ∈ divisorPrimes w H) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  let : NeZero (∏ t ∈ divisorPrimes w H,t) := ⟨(divisorModulus_pos w H).ne'⟩
  have hh := prime_unit_avoidance_card (divisorPrimes w H) S hP u beta
  have he : Finset.univ.filter (divisorJoint w H C0 beta S m) =
      Finset.univ.filter (fun k : ZMod (divisorModulus w H) =>
        ∀ t ∈ divisorPrimes w H,∀ j ∈ S,(k.val : ZMod t)+(u t : ZMod t)*(j : ZMod t) ≠ beta t) := by
    apply Finset.filter_congr
    intro k _hk
    unfold divisorJoint
    exact forall_congr' (fun t => forall_congr' (fun ht => by rw [hunit t ht]))
  rw [he]
  exact hh

theorem divisorJoint_card_real (w : ℝ) (H : ℕ) (C0 : ℤ) (beta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (m : ℤ) (hC0 : Int.gcd C0 (H : ℤ) = 1) (hm : m.natAbs.Coprime H) :
    ((Finset.univ.filter (divisorJoint w H C0 beta S m)).card : ℝ) =
      (divisorModulus w H : ℝ)*jointDensity (divisorPrimes w H) S := by
  rw [divisorJoint_card w H C0 beta S m hC0 hm]
  exact product_allowed_eq_density _ S (fun _ ht =>
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1)

theorem conditional_pattern_card (w : ℝ) (H : ℕ) (C0 : ℤ) (qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (m : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (hm : m.natAbs.Coprime H) :
    (Finset.univ.filter (fun s : Pattern w H => jointCondition w H C0 qA beta delta S (m,s))).card =
      (Finset.univ.filter (coprimeJoint w H qA delta S m)).card*
        ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
  have he : Finset.univ.filter (fun s : Pattern w H => jointCondition w H C0 qA beta delta S (m,s)) =
      (Finset.univ.filter (coprimeJoint w H qA delta S m)).product
        (Finset.univ.filter (divisorJoint w H C0 beta S m)) := by
    ext s
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.product_eq_sprod,Finset.mem_product,
      jointCondition_coordinates,and_comm]
  rw [he,Finset.product_eq_sprod,Finset.card_product,divisorJoint_card w H C0 beta S m hC0 hm]

end ErdosVarianceMoments



namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def patternPrimeUnit (w : ℝ) (H : ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (t : ℕ) (ht : t ∣ coprimeModulus w H) : (ZMod t)ˣ :=
  Units.map (ZMod.castHom ht (ZMod t)).toMonoidHom p

theorem patternPrimeUnit_coe (w : ℝ) (H : ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (t : ℕ) (ht : t ∣ coprimeModulus w H) :
    (patternPrimeUnit w H p t ht : ZMod t) = (p.val.val : ZMod t) := by
  change ZMod.castHom ht (ZMod t) p.val = _
  calc
    ZMod.castHom ht (ZMod t) p.val =
      ZMod.castHom ht (ZMod t) (p.val.val : ZMod (coprimeModulus w H)) := by rw [ZMod.natCast_zmod_val]
    _ = _ := map_natCast (ZMod.castHom ht (ZMod t)) p.val.val

theorem unit_mul_eq_iff {M : Type*} [Monoid M] (u : Mˣ) (x c : M) :
    (u : M)*x = c ↔ x = (u⁻¹ : Mˣ)*c := by
  constructor
  · intro h
    have hh := congrArg (fun y : M => (u⁻¹ : Mˣ)*y) h
    simpa only [← mul_assoc,Units.inv_mul,one_mul] using hh
  · intro h
    rw [h,← mul_assoc,Units.mul_inv,one_mul]

noncomputable def coprimeCoefficientUnit (w : ℝ) (H qA : ℕ)
    (p : (ZMod (coprimeModulus w H))ˣ) (t : ℕ)
    (ht : t ∈ coprimePrimes w H) (hqA : qA.Coprime t) : (ZMod t)ˣ :=
  patternPrimeUnit w H p t (Finset.dvd_prod_of_mem _ ht)*ZMod.unitOfCoprime qA hqA

noncomputable def coprimeShiftUnit (w : ℝ) (H t : ℕ) (ht : t ∈ coprimePrimes w H) : (ZMod t)ˣ :=
  ZMod.unitOfCoprime H ((LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.coprime_iff_not_dvd.mpr (Finset.mem_filter.mp ht).2).symm

noncomputable def coprimeForbidden (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ) (t : ℕ)
    (ht : t ∈ coprimePrimes w H) (hqA : qA.Coprime t) : Finset (ZMod t) :=
  forbiddenClasses S t (coprimeShiftUnit w H t ht)
    ((coprimeCoefficientUnit w H qA p t ht hqA)⁻¹*delta t)

theorem mem_coprimeForbidden (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ) (t : ℕ)
    (ht : t ∈ coprimePrimes w H) (hqA : qA.Coprime t) (x : ZMod t) :
    x ∈ coprimeForbidden w H qA delta S p t ht hqA ↔
      ∃ j ∈ S,(p.val.val : ZMod t)*(qA : ZMod t)*(x+(H : ZMod t)*(j : ZMod t)) = delta t := by
  rw [coprimeForbidden,mem_forbiddenClasses]
  apply exists_congr
  intro j
  apply and_congr_right
  intro _hj
  have hh := unit_mul_eq_iff (coprimeCoefficientUnit w H qA p t ht hqA)
    (x+(H : ZMod t)*(j : ZMod t)) (delta t)
  have hc : (coprimeCoefficientUnit w H qA p t ht hqA : ZMod t) =
      (p.val.val : ZMod t)*(qA : ZMod t) := by
    simpa only [coprimeCoefficientUnit,Units.val_mul,ZMod.coe_unitOfCoprime] using
      congrArg (fun v : ZMod t => v*(qA : ZMod t))
        (patternPrimeUnit_coe w H p t (Finset.dvd_prod_of_mem _ ht))
  rw [hc] at hh
  simpa only [coprimeShiftUnit,ZMod.coe_unitOfCoprime] using hh.symm

theorem coprimeForbidden_card (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ) (t : ℕ)
    (ht : t ∈ coprimePrimes w H) (hqA : qA.Coprime t) :
    (coprimeForbidden w H qA delta S p t ht hqA).card = (positionResidues S t).card :=
  forbiddenClasses_card _ _ _ _

end ErdosVarianceMoments



namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def coprimeForbiddenFamily (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (t : ℕ) : Finset (ZMod t) :=
  if ht : t ∈ coprimePrimes w H then coprimeForbidden w H qA delta S p t ht (hqA t ht) else ∅

theorem coprimeForbiddenFamily_card (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (t : ℕ) (ht : t ∈ coprimePrimes w H) :
    (coprimeForbiddenFamily w H qA delta S p hqA t).card = (positionResidues S t).card := by
  simp only [coprimeForbiddenFamily,dite_eq_left ht,coprimeForbidden_card]

theorem coprimeJoint_avoidance (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (m : ℤ) :
    coprimeJoint w H qA delta S m p ↔
      ∀ t ∈ coprimePrimes w H,(m : ZMod t) ∉ coprimeForbiddenFamily w H qA delta S p hqA t := by
  unfold coprimeJoint
  apply forall_congr'
  intro t
  apply forall_congr'
  intro ht
  simp only [coprimeForbiddenFamily,dite_eq_left ht,mem_coprimeForbidden,not_exists,not_and]

theorem nonzero_positionDensity_two (P S : Finset ℕ) (hS : S.card ≤ 2)
    (hne : jointDensity P S ≠ 0) (h2 : 2 ∈ P) : positionDensity S 2 ≤ 1/2 := by
  have hn : 1-positionDensity S 2 ≠ 0 := (Finset.prod_ne_zero_iff.mp hne) 2 h2
  have hcard := positionResidues_le_positions S 2
  have hnot : (positionResidues S 2).card ≠ 2 := by
    intro he
    apply hn
    norm_num [positionDensity,he]
  have hle : (positionResidues S 2).card ≤ 1 := by omega
  unfold positionDensity
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (by norm_num)

noncomputable def coprimePositionSurvivors (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ) (b c : ℝ) : Finset ℤ :=
  (unitIntervalIntegers H b c).filter (fun m => coprimeJoint w H qA delta S m p)

theorem coprimePositionSurvivors_sieve_sum (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p : (ZMod (coprimeModulus w H))ˣ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (b c : ℝ) :
    ((coprimePositionSurvivors w H qA delta S p b c).card : ℝ) =
      ∑ m ∈ unitIntervalIntegers H b c,(1 : ℝ)*BonferroniBlocks.survives (coprimePrimes w H)
        (fun t => (m : ZMod t) ∈ coprimeForbiddenFamily w H qA delta S p hqA t) := by
  rw [coprimePositionSurvivors,Finset.card_filter,Nat.cast_sum]
  simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero,one_mul,BonferroniBlocks.survives,
    coprimeJoint_avoidance w H qA delta S p hqA]
  apply Finset.sum_congr rfl
  intro m _hm
  split_ifs <;> rfl

theorem coprimePositionSurvivors_estimate (w : ℝ) (hw : 2 ≤ w) (s : ℝ) (hs : 480024 ≤ s)
    (H qA : ℕ) (hH : 0 < H) (delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) (hS : S.card ≤ 2)
    (p : (ZMod (coprimeModulus w H))ˣ) (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t)
    (b c : ℝ) (hbc : b ≤ c) (hne : jointDensity (coprimePrimes w H) S ≠ 0) :
    |((coprimePositionSurvivors w H qA delta S p b c).card : ℝ)-
      ((c-b)*((H.totient : ℝ)/(H : ℝ)))*jointDensity (coprimePrimes w H) S| ≤
      ((c-b)*((H.totient : ℝ)/(H : ℝ)))*jointDensity (coprimePrimes w H) S*Real.exp (-s/96)+
        4*(H.divisors.card : ℝ)*(w^s)^2 := by
  let P := coprimePrimes w H
  let E := coprimeForbiddenFamily w H qA delta S p hqA
  have hP (t : ℕ) (ht : t ∈ P) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  have hsize (t : ℕ) (ht : t ∈ P) : (t : ℝ) ≤ w :=
    (Nat.le_floor_iff (by linarith)).mp (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).2
  have hHP (t : ℕ) (ht : t ∈ P) : H.Coprime t :=
    ((hP t ht).coprime_iff_not_dvd.mpr (Finset.mem_filter.mp ht).2).symm
  have hge (t : ℕ) (ht : t ∈ P) : residueDensity E t = positionDensity S t := by
    unfold residueDensity positionDensity
    rw [coprimeForbiddenFamily_card w H qA delta S p hqA t ht]
  have hg0 (t : ℕ) (ht : t ∈ P) : 0 ≤ residueDensity E t := by
    rw [hge t ht]
    let : NeZero t := ⟨(hP t ht).ne_zero⟩
    exact (positionDensity_bounds S t).1
  have hdim (t : ℕ) (ht : t ∈ P) : residueDensity E t ≤ 2/(t : ℝ) := by
    rw [hge t ht]
    let : NeZero t := ⟨(hP t ht).ne_zero⟩
    exact positionDensity_le_two S hS t
  have htwo (h2 : 2 ∈ P) : residueDensity E 2 ≤ 1/2 := by
    rw [hge 2 h2]
    exact nonzero_positionDensity_two P S hS hne h2
  have hX : 0 ≤ (c-b)*((H.totient : ℝ)/(H : ℝ)) := mul_nonneg (sub_nonneg.mpr hbc) (by positivity)
  have hprod : (∏ t ∈ P,(1-residueDensity E t)) = jointDensity P S :=
    Finset.prod_congr rfl (fun t ht => by rw [hge t ht])
  have hf := RealFundamentalSieve.fundamental_lemma (unitIntervalIntegers H b c) (fun _ => 1)
    (fun _ _ => by norm_num) (fun t m => (m : ZMod t) ∈ E t)
    w s P ((c-b)*((H.totient : ℝ)/(H : ℝ))) (residueDensity E)
    hw hs hX hP hsize hg0 hdim htwo
  rw [hprod] at hf
  rw [coprimePositionSurvivors_sieve_sum w H qA delta S p hqA b c]
  have hD : 1 ≤ w^s := Real.one_le_rpow (by linarith) (by linarith)
  have hr := remainder_sum_bound H hH P hP hHP E b c hbc w s hD
  exact hf.trans (add_le_add le_rfl hr)

end ErdosVarianceMoments


end Erdos970

end OAI
