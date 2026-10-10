import OAI.NumberTheory.Jacobsthal.Primes.SubsetPrimeBoxMass
import OAI.NumberTheory.Jacobsthal.Sieve.ActualCofactorCellData

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SubsetBoxBookkeeping
open _root_.Filter FiniteWeightedChoiceBox SingletonSubsetMass SubsetPrimeBoxMass
open WrongOwnerBoxMass WrongOwnerBinMass ActualBinOwners ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

theorem subset_box_original_weight {n : ℕ} (f : Fin n → Finset ℕ) :
    pointWeight (fun _ => subsetWeight) f=(((∏ i,∏ p ∈ f i,p):ℕ):ℝ)⁻¹ := by
  simp [pointWeight,subsetWeight,Finset.prod_inv_distrib]

theorem search_card_le_multiplicity {n : ℕ} (mult : Fin n → ℕ) (S : Finset (Fin n))
    (hsingle : ∀ i ∈ S,mult i=1) : S.card ≤ ∑ i,mult i := by
  calc
    S.card = ∑ i ∈ S,mult i := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro i hi
      exact (hsingle i hi).symm
    _ ≤ ∑ i,mult i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.zero_le _)

theorem length_bounded_subset_wrong_mass {Cs theta A Clen : ℝ} (hCs : 0 ≤ Cs)
    (htheta : 0 < theta) (hA : 0 < A) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,∀ Y xi eta B : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) → theta ≤ xi → xi ≤ 1 →
      Real.log B ≤ 2*Real.log w → ∀ (n : ℕ) (R : Fin n → ℝ) (mult : Fin n → ℕ),
      ((∑ i,mult i):ℝ) ≤ Clen*Real.log B → ∀ (S : Finset (Fin n)),
      (∀ i ∈ S,mult i=1) → (∀ i ∈ S,w^(w^((1/4:ℝ))) ≤ R i) →
      ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      (∑ f ∈ (points (fun i => (primeBin (R i) xi).powersetCard (mult i))).filter
        (fun f => ∃ i ∈ S,∃ p ∈ f i,p ∈ wrongOwnerPrimes Y w Cs eta (R i) xi a q),
        pointWeight (fun _ => subsetWeight) f) ≤
      w^(-A)*boxMass (fun i => (primeBin (R i) xi).powersetCard (mult i))
        (fun _ => subsetWeight) := by
  filter_upwards [wrong_owner_subset_mass hCs htheta (show 0 < A+1 by linarith),
    logarithmic_positions_le_w Clen hC,eventually_gt_atTop (1:ℝ)] with w hw hlength hw1
  intro Y xi eta B hY hYup hxi hxi1 hB n R mult hm S hsingle hsearch a q hq
  have hraw := hw Y xi eta hY hYup hxi hxi1 n R mult S hsingle hsearch a q hq
  have hcard : (S.card:ℝ) ≤ w := by
    have hsmr : (S.card:ℝ) ≤ ∑ i,(mult i:ℝ) := by exact_mod_cast search_card_le_multiplicity mult S hsingle
    have hmul := mul_le_mul_of_nonneg_left hB hC
    nlinarith
  have hw0 : 0 < w := zero_lt_one.trans hw1
  have hmul := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hw0.le (-(A+1)))
  have he : w*w^(-(A+1))=w^(-A) := by
    calc
      _ = w^(1:ℝ)*w^(-(A+1)) := by rw [Real.rpow_one]
      _ = w^((1:ℝ)+(-(A+1))) := (Real.rpow_add hw0 _ _).symm
      _ = _ := by congr 1; ring
  rw [he] at hmul
  have hmass : 0 ≤ boxMass (fun i => (primeBin (R i) xi).powersetCard (mult i)) (fun _ => subsetWeight) :=
    Finset.sum_nonneg (fun f _ => weight_nonnegative _ (fun _ => subsetWeight_nonnegative) f)
  exact hraw.trans (mul_le_mul_of_nonneg_right hmul hmass)
end NumberTheoryLean.SubsetBoxBookkeeping



namespace NumberTheoryLean.CanonicalSubsetBox
open _root_.Filter FiniteWeightedChoiceBox SingletonSubsetMass SubsetPrimeBoxMass SubsetBoxBookkeeping
open WrongOwnerBinMass ActualBinOwners ErdosInversePrimeBin ErdosInverseAlignment ErdosCofactorChoices

attribute [local instance] Classical.propDecidable

noncomputable def selectionMass {n : ℕ} (P : Fin n → Finset ℕ) (mult : Fin n → ℕ) : ℝ :=
  ∑ f ∈ selections P mult,(selectionProduct f:ℝ)⁻¹

theorem canonical_points {n : ℕ} (P : Fin n → Finset ℕ) (mult : Fin n → ℕ) :
    points (fun i => (P i).powersetCard (mult i))=selections P mult := by
  ext f
  simp only [points,selections,Fintype.mem_piFinset]

theorem canonical_weight {n : ℕ} (f : Fin n → Finset ℕ) :
    pointWeight (fun _ => subsetWeight) f=(selectionProduct f:ℝ)⁻¹ := subset_box_original_weight f

theorem selectionMass_eq_weighted {n : ℕ} (P : Fin n → Finset ℕ) (mult : Fin n → ℕ) :
    selectionMass P mult=boxMass (fun i => (P i).powersetCard (mult i)) (fun _ => subsetWeight) := by
  rw [selectionMass,boxMass,canonical_points]
  apply Finset.sum_congr rfl
  intro f _hf
  exact (canonical_weight f).symm

theorem canonical_no_nearfull_mass {n : ℕ} (R : Fin n → ℝ) (w c xi eta : ℝ) (mult : Fin n → ℕ)
    (hR : ∀ i,0 < R i) (hw : 1 < w) (hc : 0 < c) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) (S : Finset (Fin n))
    (hsingle : ∀ i ∈ S,mult i=1) (hcount : c*Real.log w ≤ (S.card:ℝ)) (a : ℕ → ℤ) (q : ℚ)
    (hd : ∀ i ∈ S,(((primeBin (R i) xi).filter (aligns a q)).card:ℝ) ≤
      (1-eta)*((primeBin (R i) xi).card:ℝ)) :
    (∑ f ∈ (selections (fun i => primeBin (R i) xi) mult).filter
      (fun f => ∀ i ∈ S,∀ p ∈ f i,aligns a q p),(selectionProduct f:ℝ)⁻¹) ≤
      w^(-(c*eta/2))*selectionMass (fun i => primeBin (R i) xi) mult := by
  have hh := no_nearfull_subset_power R w c xi eta mult hR hw hc hxi0 hxi1 heta0 heta1 S hsingle hcount a q hd
  rw [← selectionMass_eq_weighted] at hh
  simp only [restrictedPoints,canonical_points,canonical_weight] at hh
  exact hh

theorem canonical_wrong_mass {Cs theta A Clen : ℝ} (hCs : 0 ≤ Cs)
    (htheta : 0 < theta) (hA : 0 < A) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,∀ Y xi eta B : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) → theta ≤ xi → xi ≤ 1 →
      Real.log B ≤ 2*Real.log w → ∀ (n : ℕ) (R : Fin n → ℝ) (mult : Fin n → ℕ),
      ((∑ i,mult i):ℝ) ≤ Clen*Real.log B → ∀ (S : Finset (Fin n)),
      (∀ i ∈ S,mult i=1) → (∀ i ∈ S,w^(w^((1/4:ℝ))) ≤ R i) →
      ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      (∑ f ∈ (selections (fun i => primeBin (R i) xi) mult).filter
        (fun f => ∃ i ∈ S,∃ p ∈ f i,p ∈ wrongOwnerPrimes Y w Cs eta (R i) xi a q),
        (selectionProduct f:ℝ)⁻¹) ≤
      w^(-A)*selectionMass (fun i => primeBin (R i) xi) mult := by
  filter_upwards [length_bounded_subset_wrong_mass hCs htheta hA hC] with w hw
  intro Y xi eta B hY hYup hxi hxi1 hcomp n R mult hlen S hsingle hsearch a q hq
  have hh := hw Y xi eta B hY hYup hxi hxi1 hcomp n R mult hlen S hsingle hsearch a q hq
  rw [← selectionMass_eq_weighted] at hh
  simp only [canonical_points,canonical_weight] at hh
  exact hh
end NumberTheoryLean.CanonicalSubsetBox



namespace NumberTheoryLean.SingletonBinSelection
open ErdosCofactorChoices

attribute [local instance] Classical.propDecidable

noncomputable def eraseMultiplicity {n : ℕ} (m : Fin n → ℕ) (i : Fin n) : Fin n → ℕ :=
  fun k => if k=i then 0 else m k
noncomputable def eraseSelection {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) : Fin n → Finset ℕ :=
  fun k => if k=i then ∅ else f k
noncomputable def fillSelection {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) : Fin n → Finset ℕ :=
  Function.update f i {p}

theorem erase_selection_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (f : Fin n → Finset ℕ)
    (hf : f ∈ selections P m) (i : Fin n) : eraseSelection f i ∈ selections P (eraseMultiplicity m i) := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases hki : k=i
  · subst k; simp [eraseSelection,eraseMultiplicity]
  · simpa only [eraseSelection,eraseMultiplicity,ite_eq_right hki] using (mem_selections P m f).mp hf k

theorem erased_coordinate_empty {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P (eraseMultiplicity m i)) : f i=∅ := by
  have hh := ((mem_selections P _ f).mp hf i).2
  simpa [eraseMultiplicity] using hh

theorem fill_selection_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n)
    (hmi : m i=1) (f : Fin n → Finset ℕ) (hf : f ∈ selections P (eraseMultiplicity m i))
    (p : ℕ) (hp : p ∈ P i) : fillSelection f i p ∈ selections P m := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases hki : k=i
  · subst k; simp [fillSelection,hmi,hp]
  · have hh := (mem_selections P _ f).mp hf k
    simpa [fillSelection,eraseMultiplicity,hki] using hh

theorem erase_fill {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) (he : f i=∅) :
    eraseSelection (fillSelection f i p) i=f := by
  funext k
  by_cases hki : k=i
  · subst k; simp [eraseSelection,he]
  · simp [eraseSelection,fillSelection,hki]

theorem fill_erase {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) (he : f i={p}) :
    fillSelection (eraseSelection f i) i p=f := by
  funext k
  by_cases hki : k=i
  · subst k; simp [fillSelection,he]
  · simp [eraseSelection,fillSelection,hki]

theorem singleton_selection_recovery {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i : Fin n) (hmi : m i=1) (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) :
    ∃ p ∈ P i,f i={p} ∧ fillSelection (eraseSelection f i) i p=f := by
  have hi := (mem_selections P m f).mp hf i
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp (hi.2.trans hmi)
  exact ⟨p,hi.1 (by rw [hp]; simp),hp,fill_erase f i p hp⟩
end NumberTheoryLean.SingletonBinSelection



namespace NumberTheoryLean.PartitionedSelections
open ErdosCofactorChoices

attribute [local instance] Classical.propDecidable

noncomputable def restrictMultiplicity {n : ℕ} (m : Fin n → ℕ) (S : Finset (Fin n)) : Fin n → ℕ :=
  fun k => if k∈S then m k else 0
noncomputable def restrictSelection {n : ℕ} (f : Fin n → Finset ℕ) (S : Finset (Fin n)) : Fin n → Finset ℕ :=
  fun k => if k∈S then f k else ∅
noncomputable def joinSelection {n : ℕ} (S : Finset (Fin n)) (f g : Fin n → Finset ℕ) : Fin n → Finset ℕ :=
  fun k => if k∈S then f k else g k

theorem restricted_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P m) (S : Finset (Fin n)) :
    restrictSelection f S ∈ selections P (restrictMultiplicity m S) := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases hk : k∈S
  · simpa only [restrictSelection,restrictMultiplicity,ite_eq_left hk] using (mem_selections P m f).mp hf k
  · simp [restrictSelection,restrictMultiplicity,hk]

theorem restricted_empty {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (S : Finset (Fin n))
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P (restrictMultiplicity m S))
    (k : Fin n) (hk : k∉S) : f k=∅ := by
  have hh := ((mem_selections _ _ _).mp hf k).2
  simpa [restrictMultiplicity,hk] using hh

theorem joined_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (S : Finset (Fin n))
    (f g : Fin n → Finset ℕ) (hf : f ∈ selections P (restrictMultiplicity m S))
    (hg : g ∈ selections P (restrictMultiplicity m Sᶜ)) : joinSelection S f g ∈ selections P m := by
  apply (mem_selections _ _ _).mpr
  intro k
  by_cases hk : k∈S
  · have hh := (mem_selections _ _ _).mp hf k
    simpa [restrictMultiplicity,joinSelection,hk] using hh
  · have hh := (mem_selections _ _ _).mp hg k
    simpa [restrictMultiplicity,joinSelection,hk] using hh

theorem join_restrictions {n : ℕ} (f : Fin n → Finset ℕ) (S : Finset (Fin n)) :
    joinSelection S (restrictSelection f S) (restrictSelection f Sᶜ)=f := by
  funext k
  by_cases hk : k∈S <;> simp [joinSelection,restrictSelection,hk]

theorem restrict_join {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (S : Finset (Fin n))
    (f g : Fin n → Finset ℕ) (hf : f ∈ selections P (restrictMultiplicity m S))
    (hg : g ∈ selections P (restrictMultiplicity m Sᶜ)) :
    restrictSelection (joinSelection S f g) S=f ∧ restrictSelection (joinSelection S f g) Sᶜ=g := by
  constructor <;> funext k
  · by_cases hk : k∈S
    · simp [restrictSelection,joinSelection,hk]
    · simp only [restrictSelection,ite_eq_right hk]
      exact (restricted_empty P m S f hf k hk).symm
  · by_cases hk : k∈S
    · simp only [restrictSelection,Finset.mem_compl,not_true_eq_false,ite_false,hk]
      exact (restricted_empty P m Sᶜ g hg k (by simpa using hk)).symm
    · simp [restrictSelection,joinSelection,hk]
end NumberTheoryLean.PartitionedSelections



namespace NumberTheoryLean.SingletonBinProduct
open ErdosCofactorChoices SingletonBinSelection

attribute [local instance] Classical.propDecidable

theorem filled_product {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) (he : f i=∅) :
    selectionProduct (fillSelection f i p)=p*selectionProduct f := by
  have hp : ∀ k,(∏ q ∈ fillSelection f i p k,q)=(if k=i then p else 1)*(∏ q ∈ f k,q) := by
    intro k
    by_cases hki : k=i
    · subst k; simp [fillSelection,he]
    · simp [fillSelection,hki]
  unfold selectionProduct
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  simp

theorem filled_reciprocal {n : ℕ} (f : Fin n → Finset ℕ) (i : Fin n) (p : ℕ) (he : f i=∅) :
    (selectionProduct (fillSelection f i p):ℝ)⁻¹=(p:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹ := by
  rw [filled_product f i p he,Nat.cast_mul,mul_inv_rev]
  ring

end NumberTheoryLean.SingletonBinProduct



namespace NumberTheoryLean.PartitionedSelectionSums
open ErdosCofactorChoices PartitionedSelections

attribute [local instance] Classical.propDecidable

theorem joined_product {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (S : Finset (Fin n))
    (f g : Fin n → Finset ℕ) (hf : f ∈ selections P (restrictMultiplicity m S))
    (hg : g ∈ selections P (restrictMultiplicity m Sᶜ)) :
    selectionProduct (joinSelection S f g)=selectionProduct f*selectionProduct g := by
  have hpoint : ∀ k,(∏ p ∈ joinSelection S f g k,p)=(∏ p ∈ f k,p)*(∏ p ∈ g k,p) := by
    intro k
    by_cases hk : k∈S
    · have he := restricted_empty P m Sᶜ g hg k (by simpa using hk)
      simp [joinSelection,hk,he]
    · have he := restricted_empty P m S f hf k hk
      simp [joinSelection,hk,he]
  unfold selectionProduct
  simp_rw [hpoint]
  exact Finset.prod_mul_distrib

theorem partitioned_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (S : Finset (Fin n))
    (G : (Fin n → Finset ℕ) → ℝ) :
    (∑ f ∈ selections P m,G f)=
      ∑ f ∈ selections P (restrictMultiplicity m S),∑ g ∈ selections P (restrictMultiplicity m Sᶜ),G (joinSelection S f g) := by
  symm
  rw [← Finset.sum_product' (selections P (restrictMultiplicity m S))
    (selections P (restrictMultiplicity m Sᶜ)) (fun f g => G (joinSelection S f g))]
  apply Finset.sum_bij (fun x _ => joinSelection S x.1 x.2)
  · intro x hx
    exact joined_mem P m S x.1 x.2 (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hx).2
  · intro x hx y hy he
    have hx' := restrict_join P m S x.1 x.2 (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hx).2
    have hy' := restrict_join P m S y.1 y.2 (Finset.mem_product.mp hy).1 (Finset.mem_product.mp hy).2
    exact Prod.ext (hx'.1.symm.trans ((congrArg (fun f => restrictSelection f S) he).trans hy'.1))
      (hx'.2.symm.trans ((congrArg (fun f => restrictSelection f Sᶜ) he).trans hy'.2))
  · intro f hf
    exact ⟨(restrictSelection f S,restrictSelection f Sᶜ),
      Finset.mem_product.mpr ⟨restricted_mem P m f hf S,restricted_mem P m f hf Sᶜ⟩,join_restrictions f S⟩
  · intro x _hx
    rfl

theorem partitioned_weighted_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (S : Finset (Fin n))
    (G : (Fin n → Finset ℕ) → ℝ) :
    (∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*G f)=
      ∑ f ∈ selections P (restrictMultiplicity m S),∑ g ∈ selections P (restrictMultiplicity m Sᶜ),
        ((selectionProduct f:ℝ)⁻¹*(selectionProduct g:ℝ)⁻¹)*G (joinSelection S f g) := by
  rw [partitioned_sum P m S]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro g hg
  rw [joined_product P m S f g hf hg,Nat.cast_mul,mul_inv_rev]
  ring
end NumberTheoryLean.PartitionedSelectionSums



namespace NumberTheoryLean.SingletonBinSum
open ErdosCofactorChoices SingletonBinSelection SingletonBinProduct

attribute [local instance] Classical.propDecidable

theorem singleton_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (hmi : m i=1)
    (G : (Fin n → Finset ℕ) → ℝ) :
    (∑ f ∈ selections P m,G f)=
      ∑ p ∈ P i,∑ f ∈ selections P (eraseMultiplicity m i),G (fillSelection f i p) := by
  symm
  rw [← Finset.sum_product' (P i) (selections P (eraseMultiplicity m i)) (fun p f => G (fillSelection f i p))]
  apply Finset.sum_bij (fun x _ => fillSelection x.2 i x.1)
  · intro x hx
    exact fill_selection_mem P m i hmi x.2 (Finset.mem_product.mp hx).2 x.1 (Finset.mem_product.mp hx).1
  · intro x hx y hy he
    have hpx : fillSelection x.2 i x.1 i={x.1} := by simp [fillSelection]
    have hpy : fillSelection y.2 i y.1 i={y.1} := by simp [fillSelection]
    have hp : x.1=y.1 := by
      have hh := congrFun he i
      rw [hpx,hpy] at hh
      exact Finset.singleton_injective hh
    have hf : x.2=y.2 := by
      have hh := congrArg (fun f => eraseSelection f i) he
      rwa [erase_fill x.2 i x.1 (erased_coordinate_empty P m i x.2 (Finset.mem_product.mp hx).2),
        erase_fill y.2 i y.1 (erased_coordinate_empty P m i y.2 (Finset.mem_product.mp hy).2)] at hh
    exact Prod.ext hp hf
  · intro f hf
    obtain ⟨p,hp,_hfp,he⟩ := singleton_selection_recovery P m i hmi f hf
    exact ⟨(p,eraseSelection f i),Finset.mem_product.mpr ⟨hp,erase_selection_mem P m f hf i⟩,he⟩
  · intro x _
    rfl

theorem singleton_weighted_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (hmi : m i=1)
    (G : (Fin n → Finset ℕ) → ℝ) :
    (∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*G f)=
      ∑ p ∈ P i,∑ f ∈ selections P (eraseMultiplicity m i),
        ((p:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹)*G (fillSelection f i p) := by
  rw [singleton_sum P m i hmi]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro f hf
  rw [filled_reciprocal f i p (erased_coordinate_empty P m i f hf)]
end NumberTheoryLean.SingletonBinSum



namespace NumberTheoryLean.TwoSingletonBins
open ErdosCofactorChoices SingletonBinSelection SingletonBinProduct SingletonBinSum

attribute [local instance] Classical.propDecidable

noncomputable def eraseTwo {n : ℕ} (m : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  eraseMultiplicity (eraseMultiplicity m i) j
noncomputable def fillTwo {n : ℕ} (f : Fin n → Finset ℕ) (i j : Fin n) (p u : ℕ) : Fin n → Finset ℕ :=
  fillSelection (fillSelection f j u) i p

theorem eraseTwo_zero {n : ℕ} (m : Fin n → ℕ) (i j : Fin n) : eraseTwo m i j i=0 ∧ eraseTwo m i j j=0 := by
  simp [eraseTwo,eraseMultiplicity]

theorem eraseTwo_le {n : ℕ} (m : Fin n → ℕ) (i j k : Fin n) : eraseTwo m i j k ≤ m k := by
  simp only [eraseTwo,eraseMultiplicity]
  split_ifs <;> omega

theorem fillTwo_mem {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (hi : m i=1) (hj : m j=1) (f : Fin n → Finset ℕ)
    (hf : f ∈ selections P (eraseTwo m i j)) (p u : ℕ) (hp : p ∈ P i) (hu : u ∈ P j) :
    fillTwo f i j p u ∈ selections P m := by
  have hmj : eraseMultiplicity m i j=1 := by simp [eraseMultiplicity,Ne.symm hij,hj]
  exact fill_selection_mem P m i hi _ (fill_selection_mem P (eraseMultiplicity m i) j hmj f hf u hu) p hp

theorem fillTwo_product {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (f : Fin n → Finset ℕ) (hf : f ∈ selections P (eraseTwo m i j)) (p u : ℕ) :
    selectionProduct (fillTwo f i j p u)=p*u*selectionProduct f := by
  have he := (mem_selections P _ f).mp hf
  have hei : f i=∅ := Finset.card_eq_zero.mp ((he i).2.trans (eraseTwo_zero m i j).1)
  have hej : f j=∅ := Finset.card_eq_zero.mp ((he j).2.trans (eraseTwo_zero m i j).2)
  have hfill : fillSelection f j u i=∅ := by simp [fillSelection,hij,hei]
  rw [fillTwo,filled_product _ i p hfill,filled_product f j u hej]
  ring

theorem two_singleton_weighted_sum {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (hi : m i=1) (hj : m j=1) (G : (Fin n → Finset ℕ) → ℝ) :
    (∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*G f)=
      ∑ p ∈ P i,∑ u ∈ P j,∑ f ∈ selections P (eraseTwo m i j),
        ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(selectionProduct f:ℝ)⁻¹)*G (fillTwo f i j p u) := by
  rw [singleton_weighted_sum P m i hi]
  apply Finset.sum_congr rfl
  intro p _hp
  have hmj : eraseMultiplicity m i j=1 := by simp [eraseMultiplicity,Ne.symm hij,hj]
  have hh := singleton_weighted_sum P (eraseMultiplicity m i) j hmj
    (fun f => (p:ℝ)⁻¹*G (fillSelection f i p))
  calc
    _ = ∑ f ∈ selections P (eraseMultiplicity m i),(selectionProduct f:ℝ)⁻¹*((p:ℝ)⁻¹*G (fillSelection f i p)) := by
      apply Finset.sum_congr rfl
      intro f _
      ring
    _ = _ := by
      rw [hh]
      apply Finset.sum_congr rfl
      intro u _hu
      apply Finset.sum_congr rfl
      intro f _hf
      dsimp only [fillTwo]
      ring
end NumberTheoryLean.TwoSingletonBins


end Erdos970

end OAI
