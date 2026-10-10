import OAI.NumberTheory.Jacobsthal.Estimates.SmallModelSourceScales

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosLargePatternLaw
open ErdosVarianceSmallModel

attribute [local instance] Classical.propDecidable

abbrev FullPattern (w : ℝ) (H : ℕ) :=
  (ZMod (divisorModulus w H))ˣ × ZMod (divisorModulus w H) ×
    (ZMod (coprimeModulus w H))ˣ × ZMod (coprimeModulus w H)

noncomputable def weight (w : ℝ) (H : ℕ) : ℝ :=
  1/(((divisorModulus w H).totient : ℝ)*(divisorModulus w H : ℝ)*
    ((coprimeModulus w H).totient : ℝ)*(coprimeModulus w H : ℝ))

noncomputable def expectation (w : ℝ) (H : ℕ) (F : FullPattern w H → ℝ) : ℝ :=
  ∑ v,weight w H*F v

def survives (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (j : ℕ) (v : FullPattern w H) : Prop :=
  (∀ t ∈ divisorPrimes w H,(v.2.1.val : ZMod t)+(v.1.val.val : ZMod t)*(j : ZMod t) ≠ beta t) ∧
  (∀ t ∈ coprimePrimes w H,(v.2.2.1.val.val : ZMod t)*(qA : ZMod t)*
    ((v.2.2.2.val : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ delta t)

def jointCondition (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (v : FullPattern w H) : Prop := ∀ j ∈ S,survives w H qA beta delta j v

noncomputable def indicator (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (j : ℕ) (v : FullPattern w H) : ℝ := if survives w H qA beta delta j v then 1 else 0

noncomputable def survivorCount (w : ℝ) (H qA J : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (v : FullPattern w H) : ℕ := ((Finset.range J).filter (fun j => survives w H qA beta delta j v)).card

theorem pattern_card (w : ℝ) (H : ℕ) : Fintype.card (FullPattern w H) =
    (divisorModulus w H).totient*divisorModulus w H*(coprimeModulus w H).totient*coprimeModulus w H := by
  simp only [FullPattern,Fintype.card_prod,ZMod.card_units_eq_totient,ZMod.card]
  ring

theorem weight_positive (w : ℝ) (H : ℕ) : 0 < weight w H := by
  have hT0 := divisorModulus_pos w H
  have hT1 := coprimeModulus_pos w H
  have hP0 := Nat.totient_pos.mpr hT0
  have hP1 := Nat.totient_pos.mpr hT1
  unfold weight
  positivity

theorem weight_sum (w : ℝ) (H : ℕ) : (∑ _v : FullPattern w H,weight w H)=1 := by
  have hT0 : (divisorModulus w H : ℝ) ≠ 0 := by exact_mod_cast (divisorModulus_pos w H).ne'
  have hT1 : (coprimeModulus w H : ℝ) ≠ 0 := by exact_mod_cast (coprimeModulus_pos w H).ne'
  have hP0 : ((divisorModulus w H).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (divisorModulus_pos w H)).ne'
  have hP1 : ((coprimeModulus w H).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (coprimeModulus_pos w H)).ne'
  simp only [Finset.sum_const,Finset.card_univ,pattern_card,nsmul_eq_mul,Nat.cast_mul,weight]
  field_simp

theorem indicator_binary (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (j : ℕ) (v : FullPattern w H) : indicator w H qA beta delta j v=0 ∨ indicator w H qA beta delta j v=1 := by
  unfold indicator
  split_ifs <;> simp

theorem count_eq_indicator_sum (w : ℝ) (H qA J : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (v : FullPattern w H) : (survivorCount w H qA J beta delta v : ℝ)=
      ∑ j ∈ Finset.range J,indicator w H qA beta delta j v := by
  simp only [survivorCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,indicator]

end ErdosLargePatternLaw



namespace ErdosLargePatternLaw
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceMoments

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def projectedUnit (M t : ℕ) [NeZero M] (ht : t ∣ M) (p : (ZMod M)ˣ) : (ZMod t)ˣ :=
  Units.map (ZMod.castHom ht (ZMod t)).toMonoidHom p

theorem projectedUnit_coe (M t : ℕ) [NeZero M] (ht : t ∣ M) (p : (ZMod M)ˣ) :
    (projectedUnit M t ht p : ZMod t) = (p.val.val : ZMod t) := by
  change ZMod.castHom ht (ZMod t) p.val = _
  calc
    ZMod.castHom ht (ZMod t) p.val =
        ZMod.castHom ht (ZMod t) (p.val.val : ZMod M) :=
      congrArg (ZMod.castHom ht (ZMod t)) (ZMod.natCast_zmod_val p.val).symm
    _ = _ := map_natCast (ZMod.castHom ht (ZMod t)) p.val.val

def divisorCondition (w : ℝ) (H : ℕ) (beta : ∀ t : ℕ,ZMod t) (S : Finset ℕ)
    (p0 : (ZMod (divisorModulus w H))ˣ) (k0 : ZMod (divisorModulus w H)) : Prop :=
  ∀ t ∈ divisorPrimes w H,∀ j ∈ S,(k0.val : ZMod t)+(p0.val.val : ZMod t)*(j : ZMod t) ≠ beta t

def coprimeCondition (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ)
    (p1 : (ZMod (coprimeModulus w H))ˣ) (m1 : ZMod (coprimeModulus w H)) : Prop :=
  ∀ t ∈ coprimePrimes w H,∀ j ∈ S,(p1.val.val : ZMod t)*(qA : ZMod t)*
    ((m1.val : ZMod t)+(H : ZMod t)*(j : ZMod t)) ≠ delta t

theorem joint_condition_split (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (S : Finset ℕ) (p0 : (ZMod (divisorModulus w H))ˣ) (k0 : ZMod (divisorModulus w H))
    (p1 : (ZMod (coprimeModulus w H))ˣ) (m1 : ZMod (coprimeModulus w H)) :
    jointCondition w H qA beta delta S (p0,k0,p1,m1) ↔
      divisorCondition w H beta S p0 k0 ∧ coprimeCondition w H qA delta S p1 m1 := by
  constructor
  · intro h
    exact ⟨fun t ht j hj => (h j hj).1 t ht,fun t ht j hj => (h j hj).2 t ht⟩
  · rintro ⟨h0,h1⟩ j hj
    exact ⟨fun t ht => h0 t ht j hj,fun t ht => h1 t ht j hj⟩

theorem divisor_condition_card (w : ℝ) (H : ℕ) (beta : ∀ t : ℕ,ZMod t) (S : Finset ℕ)
    (p0 : (ZMod (divisorModulus w H))ˣ) :
    (Finset.univ.filter (divisorCondition w H beta S p0)).card =
      ∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card) := by
  let u (t : ℕ) : (ZMod t)ˣ :=
    if ht : t ∈ divisorPrimes w H then projectedUnit (divisorModulus w H) t (Finset.dvd_prod_of_mem _ ht) p0 else 1
  have hu (t : ℕ) (ht : t ∈ divisorPrimes w H) : (u t : ZMod t)=(p0.val.val : ZMod t) := by
    dsimp only [u]
    rw [dite_eq_left ht]
    exact projectedUnit_coe (divisorModulus w H) t (Finset.dvd_prod_of_mem _ ht) p0
  have hP (t : ℕ) (ht : t ∈ divisorPrimes w H) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  let : NeZero (∏ t ∈ divisorPrimes w H,t) := ⟨(divisorModulus_pos w H).ne'⟩
  have hh := prime_unit_avoidance_card (divisorPrimes w H) S hP u beta
  have he : Finset.univ.filter (divisorCondition w H beta S p0) =
      Finset.univ.filter (fun k0 : ZMod (divisorModulus w H) =>
        ∀ t ∈ divisorPrimes w H,∀ j ∈ S,(k0.val : ZMod t)+(u t : ZMod t)*(j : ZMod t) ≠ beta t) := by
    apply Finset.filter_congr
    intro k0 _
    unfold divisorCondition
    exact forall_congr' (fun t => forall_congr' (fun ht => by rw [hu t ht]))
  rw [he]
  exact hh

theorem multiply_unit_iff (t : ℕ) (u : (ZMod t)ˣ) (x c : ZMod t) :
    (u : ZMod t)*x=c ↔ x=(↑(u⁻¹) : ZMod t)*c := by
  constructor
  · intro h
    have hh := congrArg (fun y : ZMod t => (↑(u⁻¹) : ZMod t)*y) h
    simpa only [← mul_assoc,Units.inv_mul,one_mul] using hh
  · intro h
    rw [h,← mul_assoc,Units.mul_inv,one_mul]

theorem coprime_condition_card (w : ℝ) (H qA : ℕ) (delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ)
    (p1 : (ZMod (coprimeModulus w H))ˣ) (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) :
    (Finset.univ.filter (coprimeCondition w H qA delta S p1)).card =
      ∏ t ∈ coprimePrimes w H,(t-(positionResidues S t).card) := by
  let u (t : ℕ) : (ZMod t)ˣ := if ht : t ∈ coprimePrimes w H then
      ZMod.unitOfCoprime H
        (((LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.coprime_iff_not_dvd.mpr
          (Finset.mem_filter.mp ht).2).symm) else 1
  let coeff (t : ℕ) (ht : t ∈ coprimePrimes w H) : (ZMod t)ˣ :=
    projectedUnit (coprimeModulus w H) t (Finset.dvd_prod_of_mem _ ht) p1*ZMod.unitOfCoprime qA (hqA t ht)
  let c (t : ℕ) : ZMod t := if ht : t ∈ coprimePrimes w H then (↑((coeff t ht)⁻¹) : ZMod t)*delta t else 0
  have hu (t : ℕ) (ht : t ∈ coprimePrimes w H) : (u t : ZMod t)=(H : ZMod t) := by
    simp only [u,dite_eq_left ht,ZMod.coe_unitOfCoprime]
  have hc (t : ℕ) (ht : t ∈ coprimePrimes w H) :
      (coeff t ht : ZMod t)=(p1.val.val : ZMod t)*(qA : ZMod t) := by
    simp only [coeff,Units.val_mul,ZMod.coe_unitOfCoprime]
    exact congrArg (fun v : ZMod t => v*(qA : ZMod t))
      (projectedUnit_coe (coprimeModulus w H) t (Finset.dvd_prod_of_mem _ ht) p1)
  have hP (t : ℕ) (ht : t ∈ coprimePrimes w H) : t.Prime :=
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  let : NeZero (∏ t ∈ coprimePrimes w H,t) := ⟨(coprimeModulus_pos w H).ne'⟩
  have hh := prime_unit_avoidance_card (coprimePrimes w H) S hP u c
  have he : Finset.univ.filter (coprimeCondition w H qA delta S p1) =
      Finset.univ.filter (fun m1 : ZMod (coprimeModulus w H) =>
        ∀ t ∈ coprimePrimes w H,∀ j ∈ S,(m1.val : ZMod t)+(u t : ZMod t)*(j : ZMod t) ≠ c t) := by
    apply Finset.filter_congr
    intro m1 _
    unfold coprimeCondition
    apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    rw [hu t ht]
    apply forall_congr'
    intro j
    apply forall_congr'
    intro _hj
    simp only [c,dite_eq_left ht]
    rw [← hc t ht]
    exact not_congr (multiply_unit_iff t (coeff t ht) _ _)
  rw [he]
  exact hh

end ErdosLargePatternLaw


end Erdos970

end OAI
