import OAI.NumberTheory.Jacobsthal.Paths.ActualFirstTagExistence

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PrimeBinAlignmentMass
open ErdosInversePrimeBin


noncomputable def mass (P : Finset ℕ) : ℝ := ∑ p ∈ P,(p:ℝ)⁻¹

theorem mass_nonnegative (P : Finset ℕ) : 0 ≤ mass P :=
  Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))

theorem subset_mass_bounds {R xi : ℝ} (hR : 0 < R) (hxi : 0 ≤ xi) (P : Finset ℕ)
    (hP : P ⊆ primeBin R xi) :
    (P.card:ℝ)/((1+xi)*R) ≤ mass P ∧ mass P ≤ (P.card:ℝ)/R := by
  have hden : 0 < (1+xi)*R := by positivity
  constructor
  · calc
      _ = ∑ _p ∈ P,((1+xi)*R)⁻¹ := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum (fun p hp => by
        obtain ⟨hpp,_hlo,hhi⟩ := (mem_primeBin hR.le hxi p).mp (hP hp)
        simpa only [one_div] using (one_div_le_one_div_of_le (by exact_mod_cast hpp.pos : (0:ℝ)<p) hhi))
  · calc
      _ ≤ ∑ _p ∈ P,R⁻¹ := Finset.sum_le_sum (fun p hp => by
        obtain ⟨_hpp,hlo,_hhi⟩ := (mem_primeBin hR.le hxi p).mp (hP hp)
        simpa only [one_div] using (one_div_le_one_div_of_le hR hlo.le))
      _ = _ := by simp [div_eq_mul_inv]

theorem non_nearfull_mass {R xi eta : ℝ} (hR : 0 < R) (hxi : 0 ≤ xi) (heta : 0 ≤ eta)
    (A : Finset ℕ) (hA : A ⊆ primeBin R xi)
    (hcard : (A.card:ℝ) ≤ (1-eta)*((primeBin R xi).card:ℝ)) :
    mass A ≤ (1-eta/(1+xi))*mass (primeBin R xi) := by
  let P := primeBin R xi
  let C := P \ A
  have hden : 0 < (1+xi)*R := by positivity
  have hcardC : eta*(P.card:ℝ) ≤ (C.card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card hA
    have hhr : (C.card:ℝ)+(A.card:ℝ)=(P.card:ℝ) := by exact_mod_cast hh
    change (A.card:ℝ) ≤ (1-eta)*(P.card:ℝ) at hcard
    nlinarith
  have hPmass := (subset_mass_bounds hR hxi P (fun _ h => h)).2
  have hCmass := (subset_mass_bounds hR hxi C Finset.sdiff_subset).1
  have hsum : mass C=mass P-mass A := Finset.sum_sdiff_eq_sub hA
  have hbound : eta/(1+xi)*mass P ≤ mass C := by
    calc
      _ ≤ eta/(1+xi)*((P.card:ℝ)/R) :=
        mul_le_mul_of_nonneg_left hPmass (div_nonneg heta (by positivity))
      _ = (eta*(P.card:ℝ))/((1+xi)*R) := by
        field_simp [hR.ne',(by positivity : (1+xi:ℝ) ≠ 0)]
      _ ≤ (C.card:ℝ)/((1+xi)*R) := div_le_div_of_nonneg_right hcardC hden.le
      _ ≤ _ := hCmass
  rw [hsum] at hbound
  linarith
end NumberTheoryLean.PrimeBinAlignmentMass



namespace NumberTheoryLean.PrimeChoiceBoxMass
open PrimeBinAlignmentMass ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def choices {m : ℕ} (P : Fin m → Finset ℕ) : Finset (Fin m → ℕ) := Fintype.piFinset P
noncomputable def weight {m : ℕ} (f : Fin m → ℕ) : ℝ := ∏ i,(f i:ℝ)⁻¹
noncomputable def boxMass {m : ℕ} (P : Fin m → Finset ℕ) : ℝ := ∑ f ∈ choices P,weight f

theorem boxMass_factorizes {m : ℕ} (P : Fin m → Finset ℕ) : boxMass P=∏ i,mass (P i) := by
  exact (Finset.prod_univ_sum P (fun _ p => (p:ℝ)⁻¹)).symm

noncomputable def alignedChoices {m : ℕ} (P : Fin m → Finset ℕ) (S : Finset (Fin m))
    (a : ℕ → ℤ) (q : ℚ) : Finset (Fin m → ℕ) :=
  (choices P).filter (fun f => ∀ i ∈ S,aligns a q (f i))

theorem alignedChoices_eq {m : ℕ} (P : Fin m → Finset ℕ) (S : Finset (Fin m))
    (a : ℕ → ℤ) (q : ℚ) :
    alignedChoices P S a q=choices (fun i => if i ∈ S then (P i).filter (aligns a q) else P i) := by
  ext f
  simp only [alignedChoices,choices,Finset.mem_filter,Fintype.mem_piFinset]
  constructor
  · rintro ⟨hp,ha⟩ i
    by_cases hi : i ∈ S
    · simpa only [ite_eq_left hi,Finset.mem_filter] using And.intro (hp i) (ha i hi)
    · simpa only [ite_eq_right hi] using hp i
  · intro h
    constructor
    · intro i
      by_cases hi : i ∈ S
      · have hh := h i; rw [ite_eq_left hi] at hh; exact (Finset.mem_filter.mp hh).1
      · have hh := h i; rwa [ite_eq_right hi] at hh
    · intro i hi
      have hh := h i
      rw [ite_eq_left hi] at hh
      exact (Finset.mem_filter.mp hh).2

theorem no_nearfull_box_mass {m : ℕ} (R : Fin m → ℝ) (xi eta : ℝ)
    (hR : ∀ i,0 < R i) (hxi : 0 ≤ xi) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (S : Finset (Fin m)) (a : ℕ → ℤ) (q : ℚ)
    (hd : ∀ i ∈ S,(((primeBin (R i) xi).filter (aligns a q)).card:ℝ) ≤
      (1-eta)*((primeBin (R i) xi).card:ℝ)) :
    (∑ f ∈ alignedChoices (fun i => primeBin (R i) xi) S a q,weight f) ≤
      (1-eta/(1+xi))^S.card*boxMass (fun i => primeBin (R i) xi) := by
  let c : ℝ := 1-eta/(1+xi)
  have hc : 0 ≤ c := by
    have hd : 0 < 1+xi := by linarith
    have hh : eta/(1+xi) ≤ 1 := (div_le_one hd).mpr (by linarith)
    dsimp [c]; linarith
  rw [alignedChoices_eq]
  change boxMass (fun i => if i ∈ S then (primeBin (R i) xi).filter (aligns a q) else primeBin (R i) xi) ≤ _
  rw [boxMass_factorizes,boxMass_factorizes]
  calc
    _ ≤ ∏ i : Fin m,(if i ∈ S then c else 1)*mass (primeBin (R i) xi) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact mass_nonnegative _
      · intro i _
        by_cases hi : i ∈ S
        · simp only [ite_eq_left hi]
          exact non_nearfull_mass (hR i) hxi heta0 _ (Finset.filter_subset _ _) (hd i hi)
        · simp only [ite_eq_right hi,one_mul,le_refl]
    _ = c^S.card*∏ i : Fin m,mass (primeBin (R i) xi) := by
      rw [Finset.prod_mul_distrib,Finset.prod_ite_mem_eq]
      simp
    _ = _ := rfl
end NumberTheoryLean.PrimeChoiceBoxMass



namespace NumberTheoryLean.PrimeChoiceAlignmentDecay
open PrimeChoiceBoxMass PrimeBinAlignmentMass ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem boxMass_nonnegative {m : ℕ} (P : Fin m → Finset ℕ) : 0 ≤ boxMass P := by
  rw [boxMass_factorizes]
  exact Finset.prod_nonneg (fun i _ => mass_nonnegative (P i))

theorem search_power_bound {w c eta xi : ℝ} (hw : 1 < w) (_hc : 0 < c)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (n : ℕ) (hcount : c*Real.log w ≤ (n:ℝ)) :
    (1-eta/(1+xi))^n ≤ w^(-(c*eta/2)) := by
  have hden : 0 < 1+xi := by linarith
  have hquot : eta/(1+xi) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hbase : 0 ≤ 1-eta/(1+xi) := by linarith
  have hq : eta/2 ≤ eta/(1+xi) := div_le_div_of_nonneg_left heta0.le hden (by linarith)
  have hsmall : 1-eta/(1+xi) ≤ Real.exp (-(eta/2)) :=
    (sub_le_sub_left hq 1).trans (Real.one_sub_le_exp_neg (eta/2))
  have hpow := pow_le_pow_left₀ hbase hsmall n
  apply hpow.trans
  rw [← Real.exp_nat_mul,Real.rpow_def_of_pos (zero_lt_one.trans hw)]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem no_nearfull_power_mass {m : ℕ} (R : Fin m → ℝ) (w c eta xi : ℝ)
    (hR : ∀ i,0 < R i) (hw : 1 < w) (hc : 0 < c) (heta0 : 0 < eta)
    (heta1 : eta ≤ 1) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (S : Finset (Fin m)) (hcount : c*Real.log w ≤ (S.card:ℝ)) (a : ℕ → ℤ) (q : ℚ)
    (hd : ∀ i ∈ S,(((primeBin (R i) xi).filter (aligns a q)).card:ℝ) ≤
      (1-eta)*((primeBin (R i) xi).card:ℝ)) :
    (∑ f ∈ alignedChoices (fun i => primeBin (R i) xi) S a q,weight f) ≤
      w^(-(c*eta/2))*boxMass (fun i => primeBin (R i) xi) := by
  exact (no_nearfull_box_mass R xi eta hR hxi0 heta0.le heta1 S a q hd).trans
    (mul_le_mul_of_nonneg_right (search_power_bound hw hc heta0 heta1 hxi0 hxi1 S.card hcount)
      (boxMass_nonnegative _))
end NumberTheoryLean.PrimeChoiceAlignmentDecay



namespace NumberTheoryLean.PrimeChoiceCoordinateMass
open PrimeChoiceBoxMass PrimeBinAlignmentMass

attribute [local instance] Classical.propDecidable

noncomputable def coordinateEvent {m : ℕ} (P : Fin m → Finset ℕ) (i : Fin m) (A : Finset ℕ) :
    Finset (Fin m → ℕ) := (choices P).filter (fun f => f i ∈ A)
noncomputable def someCoordinateEvent {m : ℕ} (P : Fin m → Finset ℕ) (S : Finset (Fin m))
    (A : Fin m → Finset ℕ) : Finset (Fin m → ℕ) :=
  (choices P).filter (fun f => ∃ i ∈ S,f i ∈ A i)

theorem weight_nonnegative {m : ℕ} (f : Fin m → ℕ) : 0 ≤ weight f :=
  Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg (f i)))

theorem coordinate_mass_eq {m : ℕ} (P : Fin m → Finset ℕ) (i : Fin m) (A : Finset ℕ)
    (hA : A ⊆ P i) :
    (∑ f ∈ coordinateEvent P i A,weight f)=mass A * ∏ j ∈ Finset.univ.erase i,mass (P j) := by
  have he : coordinateEvent P i A=choices (Function.update P i A) :=
    (Fintype.piFinset_update_eq_filter_piFinset_mem P i hA).symm
  rw [he]
  change boxMass (Function.update P i A)=_
  rw [boxMass_factorizes,← Finset.mul_prod_erase Finset.univ
    (fun j => mass (Function.update P i A j)) (Finset.mem_univ i),Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem coordinate_mass_bound {m : ℕ} (P : Fin m → Finset ℕ) (i : Fin m) (A : Finset ℕ)
    (hA : A ⊆ P i) (delta : ℝ) (hm : mass A ≤ delta*mass (P i)) :
    (∑ f ∈ coordinateEvent P i A,weight f) ≤ delta*boxMass P := by
  rw [coordinate_mass_eq P i A hA,boxMass_factorizes,
    ← Finset.mul_prod_erase Finset.univ (fun j => mass (P j)) (Finset.mem_univ i)]
  have hh := mul_le_mul_of_nonneg_right hm (Finset.prod_nonneg (s := Finset.univ.erase i) (fun j _ => mass_nonnegative (P j)))
  simpa only [mul_assoc] using hh

theorem union_mass_le_sum {m : ℕ} (P : Fin m → Finset ℕ) (S : Finset (Fin m))
    (A : Fin m → Finset ℕ) :
    (∑ f ∈ someCoordinateEvent P S A,weight f) ≤
      ∑ i ∈ S,∑ f ∈ coordinateEvent P i (A i),weight f := by
  simp only [someCoordinateEvent,coordinateEvent,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro f _hf
  by_cases he : ∃ i ∈ S,f i ∈ A i
  · rw [ite_eq_left he]
    obtain ⟨i,hi,hAi⟩ := he
    have hh := Finset.single_le_sum (s := S)
      (f := fun j => if f j ∈ A j then weight f else 0)
      (fun j _ => by split_ifs; exact weight_nonnegative f; rfl) hi
    simpa only [ite_eq_left hAi] using hh
  · rw [ite_eq_right he]
    exact Finset.sum_nonneg (fun i _ => by split_ifs; exact weight_nonnegative f; rfl)

theorem some_coordinate_mass_bound {m : ℕ} (P : Fin m → Finset ℕ) (S : Finset (Fin m))
    (A : Fin m → Finset ℕ) (hA : ∀ i ∈ S,A i ⊆ P i) (delta : ℝ)
    (hm : ∀ i ∈ S,mass (A i) ≤ delta*mass (P i)) :
    (∑ f ∈ someCoordinateEvent P S A,weight f) ≤ (S.card:ℝ)*delta*boxMass P := by
  apply (union_mass_le_sum P S A).trans
  calc
    _ ≤ ∑ _i ∈ S,delta*boxMass P := Finset.sum_le_sum
      (fun i hi => coordinate_mass_bound P i (A i) (hA i hi) delta (hm i hi))
    _ = _ := by simp [mul_assoc]
end NumberTheoryLean.PrimeChoiceCoordinateMass


end Erdos970

end OAI
