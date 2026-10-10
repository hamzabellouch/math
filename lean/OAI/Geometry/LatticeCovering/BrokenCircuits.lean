import OAI.Geometry.LatticeCovering.CircuitSums

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace SingleLatticeCovering.BrokenCircuit
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

def minimalObstructions (P : Finset ι → Prop) (A : Finset ι) : Finset (Finset ι) := by
  classical
  exact A.powerset.filter (fun T => ¬P T ∧ ∀ U, U ⊂ T → P U)

lemma mem_minimalObstructions {ι : Type*} [DecidableEq ι] {P : Finset ι → Prop} {A T : Finset ι} :
    T ∈ minimalObstructions P A ↔ T ⊆ A ∧ ¬P T ∧ ∀ U, U ⊂ T → P U := by
  classical
  simp [minimalObstructions]

lemma exists_minimalObstruction {P : Finset ι → Prop} {A S : Finset ι}
    (hS : S ⊆ A) (hP : ¬P S) :
    ∃ T ∈ minimalObstructions P A, T ⊆ S := by
  classical
  obtain ⟨T,hTS,hT,hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun T : Finset ι => ¬P T) S hP
  refine ⟨T, mem_minimalObstructions.mpr ⟨hTS.trans hS,hT,?_⟩,hTS⟩
  intro U hUT
  by_contra hn
  exact hUT.2 (hmin hn hUT.1)

lemma sum_powerset_pow_card {ι : Type*} [DecidableEq ι] (A : Finset ι) (t : ℝ) :
    ∑ S ∈ A.powerset, t^S.card = (1+t)^A.card := by
  simpa only [one_pow, mul_one, add_comm t 1] using
    (Finset.sum_pow_mul_eq_add_pow t (1:ℝ) A)


lemma sum_supersets_pow_card (A T : Finset ι) (hTA : T ⊆ A) (t : ℝ) :
    (∑ S ∈ A.powerset.filter (fun S => T ⊆ S), t^S.card) =
      t^T.card * (1+t)^(A.card-T.card) := by
  classical
  rw [←Finset.card_sdiff_of_subset hTA, ←sum_powerset_pow_card, Finset.mul_sum]
  apply Finset.sum_bij (fun S _ => S \ T)
  · intro S hS
    obtain ⟨hSA,hTS⟩ := Finset.mem_filter.mp hS
    apply Finset.mem_powerset.mpr
    exact Finset.sdiff_subset_sdiff_left T (Finset.mem_powerset.mp hSA)
  · intro S hS U hU he
    have hTS := (Finset.mem_filter.mp hS).2
    have hTU := (Finset.mem_filter.mp hU).2
    calc
      S = (S \ T) ∪ T := (Finset.sdiff_union_of_subset hTS).symm
      _ = (U \ T) ∪ T := congrArg (fun X => X ∪ T) he
      _ = U := Finset.sdiff_union_of_subset hTU
  · intro U hU
    have hUA := Finset.mem_powerset.mp hU
    refine ⟨U ∪ T, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.union_subset (hUA.trans Finset.sdiff_subset) hTA),
      Finset.subset_union_right⟩, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨hx,hxn⟩ := Finset.mem_sdiff.mp hx
      exact (Finset.mem_union.mp hx).resolve_right hxn
    · intro hx
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union.mpr (Or.inl hx), (Finset.mem_sdiff.mp (hUA hx)).2⟩
  · intro S hS
    have hTS := (Finset.mem_filter.mp hS).2
    rw [←Finset.card_sdiff_add_card_eq_card hTS, pow_add, mul_comm]

attribute [local instance] Classical.propDecidable



theorem bad_subset_sum_le (P : Finset ι → Prop) (A : Finset ι) (k : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ S ∈ A.powerset.filter (fun S => S.card ≤ k ∧ ¬P S), t^S.card) ≤
      (1+t)^A.card *
        ∑ T ∈ (minimalObstructions P A).filter (fun T => T.card ≤ k), t^T.card := by
  classical
  let F := (minimalObstructions P A).filter (fun T => T.card ≤ k)
  have hp (S : Finset ι) : 0 ≤ t^S.card := pow_nonneg ht _
  calc
    _ ≤ ∑ S ∈ A.powerset,
        ∑ T ∈ F, if T ⊆ S then t^S.card else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro S hS
      by_cases hb : S.card ≤ k ∧ ¬P S
      · rw [ite_eq_left hb]
        obtain ⟨T,hT,hTS⟩ := exists_minimalObstruction
          (Finset.mem_powerset.mp hS) hb.2
        have hTF : T ∈ F := Finset.mem_filter.mpr
          ⟨hT,(Finset.card_le_card hTS).trans hb.1⟩
        have hh := Finset.single_le_sum
          (fun U (_ : U ∈ F) => show 0 ≤ (if U ⊆ S then t^S.card else 0) by
            split_ifs <;> positivity) hTF
        simpa only [ite_eq_left hTS] using hh
      · rw [ite_eq_right hb]
        exact Finset.sum_nonneg (fun T _ => by split_ifs <;> positivity)
    _ = ∑ T ∈ F, t^T.card * (1+t)^(A.card-T.card) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T hT
      rw [←Finset.sum_filter, sum_supersets_pow_card]
      exact (mem_minimalObstructions.mp (Finset.mem_filter.mp hT).1).1
    _ ≤ ∑ T ∈ F, t^T.card * (1+t)^A.card := by
      apply Finset.sum_le_sum
      intro T hT
      apply mul_le_mul_of_nonneg_left _ (hp T)
      exact pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1+t) (Nat.sub_le _ _)
    _ = _ := by rw [←Finset.sum_mul, mul_comm]




def truncatedFacesPolynomial (P : Finset ι → Prop) (A : Finset ι) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ A.powerset.filter P, if S.card ≤ k then (-1:ℝ)^S.card*t^S.card else 0

def binomialPolynomial (M : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), (M.choose j : ℝ) * (-1:ℝ)^j * t^j

lemma unrestricted_polynomial_eq {ι : Type*} [DecidableEq ι] (A : Finset ι) (t : ℝ) (k : ℕ) :
    truncatedFacesPolynomial (fun _ => True) A t k = binomialPolynomial A.card t k := by
  unfold truncatedFacesPolynomial binomialPolynomial
  rw [Finset.filter_true, Finset.sum_powerset]
  have he (j : ℕ) : (∑ S ∈ Finset.powersetCard j A,
      if S.card ≤ k then (-1:ℝ)^S.card*t^S.card else 0) =
      (A.card.choose j) • (if j ≤ k then (-1:ℝ)^j*t^j else 0) :=
    Finset.sum_powersetCard j A (fun l => if l ≤ k then (-1:ℝ)^l*t^l else 0)
  simp_rw [he]
  simp only [nsmul_eq_mul, mul_ite, mul_zero]
  let f : ℕ → ℝ := fun j => if j ≤ k then (A.card.choose j : ℝ) *
    ((-1:ℝ)^j * t^j) else 0
  change (∑ j ∈ Finset.range (A.card+1), f j) = _
  have hsum : (∑ j ∈ Finset.range (A.card+1), f j) =
      ∑ j ∈ Finset.range (k+1), f j := by
    rcases le_total A.card k with h | h
    · apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h _))
      intro j hj hjn
      have hm : A.card < j := by simp only [Finset.mem_range] at hj hjn; omega
      simp [f, Nat.choose_eq_zero_of_lt hm]
    · symm
      apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h _))
      intro j hj hjn
      have hk : ¬j ≤ k := by simp only [Finset.mem_range] at hj hjn; omega
      simp [f,hk]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j hj
  have hk : j ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  simp only [f,ite_eq_left hk,mul_assoc]

lemma truncated_defect_le_bad_sum (P : Finset ι → Prop) (A : Finset ι) (k : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    |truncatedFacesPolynomial P A t k - binomialPolynomial A.card t k| ≤
      ∑ S ∈ A.powerset.filter (fun S => S.card ≤ k ∧ ¬P S), t^S.card := by
  rw [←unrestricted_polynomial_eq A t k]
  unfold truncatedFacesPolynomial
  rw [Finset.filter_true, Finset.sum_filter, ←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ S ∈ A.powerset,
        |(if P S then (if S.card ≤ k then (-1:ℝ)^S.card*t^S.card else 0) else 0) -
          (if S.card ≤ k then (-1:ℝ)^S.card*t^S.card else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hP : P S <;> by_cases hk : S.card ≤ k <;>
        simp [hP,hk,abs_mul,abs_pow,abs_of_nonneg (pow_nonneg ht S.card)]



theorem truncated_defect_le (P : Finset ι → Prop) (A : Finset ι) (k : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    |truncatedFacesPolynomial P A t k - binomialPolynomial A.card t k| ≤
      (1+t)^A.card *
        ∑ T ∈ (minimalObstructions P A).filter (fun T => T.card ≤ k), t^T.card :=
  (truncated_defect_le_bad_sum P A k ht).trans (bad_subset_sum_le P A k ht)




end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.BrokenCircuit
open scoped BigOperators
open Submodule
variable {ι K V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V]


lemma minimalObstruction_linearIndepOn {v : ι → V} {A T : Finset ι}
    (hT : T ∈ minimalObstructions (NoBrokenCircuit (K := K) v) A) :
    LinearIndepOn K v (T : Set ι) := by
  have hproper := (mem_minimalObstructions.mp hT).2.2
  induction T using Finset.induction_on_min with
  | empty => simp
  | insert a S ha ih =>
    have han : a ∉ S := fun h => (lt_irrefl a (ha a h))
    have hS : NoBrokenCircuit (K := K) v S :=
      hproper S (Finset.ssubset_insert han)
    have hn : v a ∉ Submodule.span K (v '' (S : Set ι)) := by
      have he : S.filter (fun j => a < j) = S := Finset.filter_true_of_mem ha
      simpa only [Active, he] using hS a
    simpa only [Finset.coe_insert] using hS.linearIndepOn.insert hn



theorem minimalObstruction_has_circuit {v : ι → V} {A T : Finset ι}
    (hT : T ∈ minimalObstructions (NoBrokenCircuit (K := K) v) A) :
    ∃ e : ι, (∀ j ∈ T, e < j) ∧ ∃ c : T → K,
      (∀ i, c i ≠ 0) ∧ ∑ i, c i • v i = v e := by
  classical
  obtain ⟨hTA,hN,hproper⟩ := mem_minimalObstructions.mp hT
  simp only [NoBrokenCircuit, not_forall, not_not] at hN
  obtain ⟨e,he⟩ := hN
  have hf : T.filter (fun j => e < j) = T := by
    by_contra hn
    have hss : T.filter (fun j => e < j) ⊂ T :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,hn⟩
    apply hproper _ hss e
    simpa only [Active, Finset.filter_filter, and_self] using he
  have hlt : ∀ j ∈ T, e < j := by
    intro j hj
    have hm : j ∈ T.filter (fun j => e < j) := by rw [hf]; exact hj
    exact (Finset.mem_filter.mp hm).2
  have hm : v e ∈ Submodule.span K (v '' (T : Set ι)) := by
    simpa only [Active,hf] using he
  obtain ⟨c,hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun K).mp hm
  refine ⟨e,hlt,c,?_,hc⟩
  intro i hci
  have hiT : (T.erase i) ⊂ T := Finset.erase_ssubset i.property
  have hP := hproper (T.erase i) hiT
  apply hP e
  have hfe : (T.erase i).filter (fun j => e < j) = T.erase i :=
    Finset.filter_true_of_mem (fun j hj => hlt j (Finset.mem_of_mem_erase hj))
  change v e ∈ Submodule.span K (v '' (↑((T.erase i).filter (fun j => e < j)) : Set ι))
  rw [hfe, ←hc]
  apply Submodule.sum_mem
  intro j hj
  by_cases hji : j = i
  · subst j
    simp [hci]
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨j, Finset.mem_erase.mpr ⟨fun h => hji (Subtype.ext h),j.property⟩,rfl⟩



end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.BrokenCircuit
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {ι τ K : Type*} [LinearOrder ι] [Fintype ι] [Fintype τ] [Field K] [Fintype K]



def finiteCircuitError (v : ι → τ → K) (k : ℕ) : ℝ :=
  (1+(Fintype.card K : ℝ)⁻¹)^(Fintype.card ι) *
    ∑ T ∈ (minimalObstructions (NoBrokenCircuit (K := K) v) Finset.univ).filter
      (fun T => T.card ≤ k), ((Fintype.card K : ℝ)⁻¹)^T.card

lemma nbcPolynomial_defect_bound {ι : Type*} {τ : Type*} {K : Type*} [LinearOrder ι] [Fintype ι] [Fintype τ] [Field K] [Fintype K] (v : ι → τ → K) (k : ℕ) :
    |nbcPolynomial (K := K) v ((Fintype.card K : ℝ)⁻¹) k -
      binomialPolynomial (Fintype.card ι) ((Fintype.card K : ℝ)⁻¹) k| ≤
        finiteCircuitError v k := by
  simpa only [Finset.card_univ, nbcPolynomial, nbcFaces, truncatedFacesPolynomial, finiteCircuitError] using
    (truncated_defect_le (NoBrokenCircuit (K := K) v) Finset.univ k
      (show (0:ℝ) ≤ (Fintype.card K : ℝ)⁻¹ by positivity))




theorem finite_field_void_upper (v : ι → τ → K) (q : ℕ) :
    vectorAverage (fun a : τ → K => avoidanceIndicator v (dotProductBilin K K a)) ≤
      binomialPolynomial (Fintype.card ι) ((Fintype.card K : ℝ)⁻¹) (2*q) +
        finiteCircuitError v (2*q) := by
  have h1 := average_avoidance_even_le v q
  have h2 := (abs_le.mp (nbcPolynomial_defect_bound v (2*q))).2
  linarith

theorem finite_field_void_lower (v : ι → τ → K) (q : ℕ) :
    binomialPolynomial (Fintype.card ι) ((Fintype.card K : ℝ)⁻¹) (2*q+1) -
        finiteCircuitError v (2*q+1) ≤
      vectorAverage (fun a : τ → K => avoidanceIndicator v (dotProductBilin K K a)) := by
  have h1 := average_avoidance_odd_ge v q
  have h2 := (abs_le.mp (nbcPolynomial_defect_bound v (2*q+1))).1
  linarith



end
end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.BrokenCircuit
variable {ι K V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V]
open Submodule
open scoped BigOperators



theorem minimalObstruction_circuit {v : ι → V} {A T : Finset ι}
    (hT : T ∈ minimalObstructions (NoBrokenCircuit (K := K) v) A) :
    ∃ e : ι, e ∉ T ∧ v e ∈ span K (v '' (T : Set ι)) ∧
      ∀ U : Finset ι, U ⊂ insert e T → LinearIndepOn K v (U : Set ι) := by
  classical
  obtain ⟨e,hlt,c,hc,hrel⟩ := minimalObstruction_has_circuit hT
  have he : e ∉ T := fun h => (lt_irrefl e (hlt e h))
  refine ⟨e,he,?_,?_⟩
  · rw [←hrel]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,i.property,rfl⟩)
  · intro U hU
    by_cases heU : e ∈ U
    · have hsub : U.erase e ⊆ T := by
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        exact (Finset.mem_insert.mp (hU.subset (Finset.mem_of_mem_erase hj))).resolve_left hji
      have hss : U.erase e ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
        intro h
        apply hU.ne
        rw [←h,Finset.insert_erase heU]⟩
      have hP := (mem_minimalObstructions.mp hT).2.2 _ hss
      have hfilter : (U.erase e).filter (fun j => e < j) = U.erase e :=
        Finset.filter_true_of_mem (fun j hj => hlt j (hsub hj))
      have hn : v e ∉ span K (v '' (U.erase e : Set ι)) := by
        simpa only [Active,hfilter] using hP e
      have hi := hP.linearIndepOn.insert hn
      simpa only [←Finset.coe_insert,Finset.insert_erase heU] using hi
    · apply (minimalObstruction_linearIndepOn hT).mono
      intro j hj
      exact (Finset.mem_insert.mp (hU.subset hj)).resolve_left (fun h => heU (h ▸ hj))


end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.BrokenCircuit
variable {ι K V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V]
open Submodule



theorem enumerated_circuit {r : ℕ} {v : ι → V} {T : Finset ι} {e : ι}
    (he : e ∉ T) (hspan : v e ∈ span K (v '' (T : Set ι)))
    (hproper : ∀ U : Finset ι, U ⊂ insert e T → LinearIndepOn K v (U : Set ι))
    (b : Fin r ≃ T) :
    let w : Fin (r+1) → ι := Fin.cons e (fun i => (b i).val)
    Function.Injective w ∧ ¬LinearIndependent K (v ∘ w) ∧
      ∀ q : Equiv.Perm (Fin (r+1)),
        LinearIndependent K (fun i : Fin r => v (w (q i.succ))) := by
  classical
  dsimp only
  let w : Fin (r+1) → ι := Fin.cons e (fun i => (b i).val)
  have hw : Function.Injective w := by
    apply Fin.cons_injective_iff.mpr
    refine ⟨?_,Subtype.val_injective.comp b.injective⟩
    intro h
    obtain ⟨i,hi⟩ := h
    exact he (hi ▸ (b i).property)
  have hwmem (i) : w i ∈ insert e T := by
    refine Fin.cases (Finset.mem_insert_self _ _) (fun j => ?_) i
    exact Finset.mem_insert_of_mem (b j).property
  refine ⟨hw,?_,?_⟩
  · intro hli
    have hn := (linearIndependent_finSucc.mp hli).2
    apply hn
    change v e ∈ span K (Set.range (fun i => v ((b i).val)))
    have hr : Set.range (fun i => v ((b i).val)) = v '' (T : Set ι) := by
      ext y
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨b i,(b i).property,rfl⟩
      · rintro ⟨j,hj,rfl⟩
        obtain ⟨i,hi⟩ := b.surjective ⟨j,hj⟩
        exact ⟨i,congrArg (fun z : T => v z.val) hi⟩
    rwa [hr]
  · intro q
    let f : Fin r → ι := fun i => w (q i.succ)
    have hf : Function.Injective f := hw.comp (q.injective.comp (Fin.succ_injective r))
    let U := Finset.univ.image f
    have hsub : U ⊆ insert e T := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      exact hwmem _
    have hnot : w (q 0) ∉ U := by
      intro h
      obtain ⟨i,hi,hf⟩ := Finset.mem_image.mp h
      have heq := q.injective (hw hf)
      exact Fin.succ_ne_zero i heq
    have hss : U ⊂ insert e T := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
      intro h
      exact hnot (h ▸ hwmem (q 0))⟩
    let g : Fin r → (U : Set ι) := fun i => ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
    have hg : Function.Injective g := fun i j h => hf (congrArg Subtype.val h)
    exact (hproper U hss).linearIndependent.comp g hg


end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.PrimeCircuit
open Matrix AffineCircuit CircuitEnumeration RogersPreparation BrokenCircuit
open scoped BigOperators

variable {d r p : ℕ} [Fact p.Prime]

def homogeneousRow (z : Fin d → ℤ) : Fin (d+1) → ZMod p :=
  Fin.cons 1 (fun j => (z j:ZMod p))

lemma integerRows_bound {s d : ℕ} (x : Fin s → Fin d → ℤ) {B : ℕ} (hB : 1 ≤ B)
    (hx : ∀ i j, |x i j| ≤ (B:ℤ)) : ∀ i j, |integerRows x i j| ≤ (B:ℤ) := by
  intro i j
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa [integerRows] using (show (1:ℤ) ≤ B by exact_mod_cast hB)
  · exact hx i j

lemma mapped_integerRows (x : Fin r → Fin d → ℤ) :
    ((integerRows x).map (fun z => (z:ZMod p))).row = fun i => homogeneousRow (p:=p) (x i) := by
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [integerRows,homogeneousRow]



theorem obstruction_factorial_count (S : Finset (Fin d → ℤ)) [LinearOrder S]
    {B : ℕ} (hB : 1 ≤ B) (hS : ∀ z ∈ S, ∀ j, |z j| ≤ (B:ℤ))
    (hp : (r+1).factorial*B^(r+1) < p) :
    let v : S → Fin (d+1) → ZMod p := fun z => homogeneousRow z.val
    let T := (minimalObstructions (NoBrokenCircuit (K:=ZMod p) v) Finset.univ).filter
      (fun T => T.card = r)
    T.card*r.factorial ≤ (circuits S r).card := by
  classical
  dsimp only
  let v : S → Fin (d+1) → ZMod p := fun z => homogeneousRow z.val
  let T := (minimalObstructions (NoBrokenCircuit (K:=ZMod p) v) Finset.univ).filter
    (fun T => T.card = r)
  have hT (U : T) : U.val ∈ minimalObstructions (NoBrokenCircuit (K:=ZMod p) v) Finset.univ :=
    (Finset.mem_filter.mp U.property).1
  choose e he hspan hproper using fun U : T => minimalObstruction_circuit (hT U)
  apply factorial_count_le_map (B:=T) (fun U hU => (Finset.mem_filter.mp hU).2)
    e Subtype.val Subtype.val_injective (circuits S r)
  intro y
  let w : Fin (r+1) → S := orderedCircuit e y
  have hw := enumerated_circuit (he y.1) (hspan y.1) (hproper y.1) y.2
  have hwi : Function.Injective w := hw.1
  apply mem_circuits.mpr
  refine ⟨fun i => (w i).property, ?_⟩
  have hbnd : ∀ i j, |(w i).val j| ≤ (B:ℤ) := fun i j => hS _ (w i).property j
  refine ⟨?_,?_⟩
  · have hi := rowIndependent_mod_iff_rat p (integerRows (fun i => (w i).val))
      (integerRows_bound _ hB hbnd) hp
    rw [mapped_integerRows] at hi
    exact mt hi.mpr hw.2.1
  · intro q
    have hsmall : r.factorial*B^r < p :=
      lt_of_le_of_lt (Nat.mul_le_mul (Nat.factorial_le (by omega)) (Nat.pow_le_pow_right hB (by omega))) hp
    have hi := rowIndependent_mod_iff_rat p
      (integerRows (fun i => (w (q i.succ)).val))
      (integerRows_bound _ hB (fun i j => hbnd (q i.succ) j)) hsmall
    rw [mapped_integerRows] at hi
    exact hi.mp (hw.2.2 q)


end SingleLatticeCovering.PrimeCircuit

namespace SingleLatticeCovering.BrokenCircuit
open Submodule
variable {ι τ K : Type*} [LinearOrder ι] [Field K]


lemma minimalObstruction_two_le {v : ι → τ → K} {j : τ}
    (hv : ∀ i, v i j = 1) (hinj : Function.Injective v) {A T : Finset ι}
    (hT : T ∈ minimalObstructions (NoBrokenCircuit (K:=K) v) A) : 2 ≤ T.card := by
  classical
  obtain ⟨e,he,hspan,hproper⟩ := minimalObstruction_circuit hT
  by_contra hh
  have hc : T.card ≤ 1 := by omega
  obtain hzero | hone := Nat.le_one_iff_eq_zero_or_eq_one.mp hc
  · have hTe : T = ∅ := Finset.card_eq_zero.mp hzero
    rw [hTe,Finset.coe_empty,Set.image_empty,Submodule.span_empty,Submodule.mem_bot] at hspan
    have := congrFun hspan j
    simp [hv] at this
  · obtain ⟨i,hTi⟩ := Finset.card_eq_one.mp hone
    rw [hTi,Finset.coe_singleton,Set.image_singleton,Submodule.mem_span_singleton] at hspan
    obtain ⟨c,hc⟩ := hspan
    have hc1 : c = 1 := by simpa [hv] using congrFun hc j
    rw [hc1,one_smul] at hc
    exact he (by rw [hTi]; exact Finset.mem_singleton.mpr (hinj hc).symm)

end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.PrimeCircuit
open AffineCircuit BrokenCircuit RogersPreparation
variable {d p : ℕ} [Fact p.Prime]

lemma homogeneousRow_injective (S : Finset (Fin d → ℤ)) {B : ℕ}
    (hS : ∀ z ∈ S, ∀ j, |z j| ≤ (B:ℤ)) (hp : 2*B < p) :
    Function.Injective (fun z : S => homogeneousRow (p:=p) z.val) := by
  intro z w h
  apply Subtype.ext
  funext j
  have he := congrFun h j.succ
  change (z.val j:ZMod p) = (w.val j:ZMod p) at he
  have hz : (z.val j-w.val j).natAbs < p := by
    have hb : |z.val j-w.val j| ≤ (2*B:ℕ) :=
      (show |z.val j-w.val j| ≤ |z.val j|+|w.val j| by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (z.val j) 0 (w.val j)).trans (by simpa only [Nat.cast_mul,Nat.cast_ofNat,two_mul,Nat.cast_add] using add_le_add (hS _ z.property j) (hS _ w.property j))
    have hh : |z.val j-w.val j| < (p:ℤ) := hb.trans_lt (by exact_mod_cast hp)
    exact_mod_cast (show ((z.val j-w.val j).natAbs:ℤ) < p by rwa [Int.natCast_natAbs])
  apply sub_eq_zero.mp
  apply (intCast_eq_zero_small p hz).mp
  simpa only [Int.cast_sub,sub_eq_zero] using he

lemma obstruction_two_le (S : Finset (Fin d → ℤ)) [LinearOrder S] {B : ℕ}
    (hS : ∀ z ∈ S, ∀ j, |z j| ≤ (B:ℤ)) (hp : 2*B < p)
    {T : Finset S} (hT : T ∈ minimalObstructions
      (NoBrokenCircuit (K:=ZMod p) (fun z : S => homogeneousRow (p:=p) z.val)) Finset.univ) :
    2 ≤ T.card :=
  minimalObstruction_two_le (j:=0) (fun _ => rfl) (homogeneousRow_injective S hS hp) hT



end SingleLatticeCovering.PrimeCircuit

namespace SingleLatticeCovering.PrimeCircuit
open AffineCircuit BrokenCircuit
open scoped BigOperators
variable {d p k : ℕ} [Fact p.Prime]

lemma sum_pow_card_eq {ι : Type*} [DecidableEq ι] (T : Finset (Finset ι))
    (hT : ∀ U ∈ T, 2 ≤ U.card ∧ U.card ≤ k) (x : ℝ) :
    ∑ U ∈ T, x^U.card = ∑ r ∈ Finset.Icc 2 k, ((T.filter (fun U => U.card=r)).card:ℝ)*x^r := by
  rw [← Finset.sum_fiberwise_of_maps_to (s:=T) (t:=Finset.Icc 2 k) (g:=Finset.card)
    (fun U hU => Finset.mem_Icc.mpr (hT U hU)) (fun U => x^U.card)]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = ∑ U ∈ T.filter (fun U => U.card=r), x^r := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [(Finset.mem_filter.mp hU).2]
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]



theorem finiteCircuitError_le (S : Finset (Fin d → ℤ)) [LinearOrder S]
    {B : ℕ} (hB : 1 ≤ B) (hS : ∀ z ∈ S, ∀ j, |z j| ≤ (B:ℤ))
    (hp2 : 2*B < p) (hpk : (k+1).factorial*B^(k+1) < p) :
    finiteCircuitError (K:=ZMod p) (fun z : S => homogeneousRow (p:=p) z.val) k ≤
      (1+(p:ℝ)⁻¹)^S.card * ∑ r ∈ Finset.Icc 2 k,
        ((circuits S r).card:ℝ)/(p:ℝ)^r/(r.factorial:ℝ) := by
  classical
  let v : S → Fin (d+1) → ZMod p := fun z => homogeneousRow z.val
  let T := (minimalObstructions (NoBrokenCircuit (K:=ZMod p) v) Finset.univ).filter
    (fun U => U.card ≤ k)
  have hcard : ∀ U ∈ T, 2 ≤ U.card ∧ U.card ≤ k := by
    intro U hU
    have hh := Finset.mem_filter.mp hU
    exact ⟨obstruction_two_le S hS hp2 hh.1,hh.2⟩
  change (1+(Fintype.card (ZMod p):ℝ)⁻¹)^(Fintype.card S)*
    (∑ U ∈ T, ((Fintype.card (ZMod p):ℝ)⁻¹)^U.card) ≤ _
  rw [ZMod.card,Fintype.card_coe,sum_pow_card_eq T hcard]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro r hr
  have hrk := (Finset.mem_Icc.mp hr).2
  have hp : (r+1).factorial*B^(r+1) < p :=
    lt_of_le_of_lt (Nat.mul_le_mul (Nat.factorial_le (by omega))
      (Nat.pow_le_pow_right hB (by omega))) hpk
  have hc := obstruction_factorial_count (r:=r) S hB hS hp
  dsimp only at hc
  have hfilter : T.filter (fun U => U.card=r) =
      (minimalObstructions (NoBrokenCircuit (K:=ZMod p) v) Finset.univ).filter
        (fun U => U.card=r) := by
    ext U
    simp only [T,Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · exact fun h => ⟨⟨h.1,h.2 ▸ hrk⟩,h.2⟩
  rw [hfilter]
  have hcR : ((((minimalObstructions (NoBrokenCircuit (K:=ZMod p) v) Finset.univ).filter
      (fun U => U.card=r)).card:ℝ)*(r.factorial:ℝ)) ≤ (circuits S r).card := by
    exact_mod_cast hc
  apply (le_div_iff₀ (by exact_mod_cast r.factorial_pos : (0:ℝ)<(r.factorial:ℝ))).mpr
  rw [div_eq_mul_inv,←inv_pow]
  nlinarith [mul_le_mul_of_nonneg_right hcR (show (0:ℝ) ≤ ((p:ℝ)⁻¹)^r by positivity)]


end SingleLatticeCovering.PrimeCircuit

namespace SingleLatticeCovering.ConvexGrid
open FiniteKernel RealLatticeCount MeasureTheory Measure Filter
open scoped Topology Pointwise

def scaledIntegerPoint {d : ℕ} (t : ℝ) (z : Fin d → ℤ) : Fin d → ℝ := fun j => t⁻¹*(z j:ℝ)

def gridSet {d : ℕ} (J : Set (Fin d → ℝ)) (t : ℝ) : Set (Fin d → ℤ) :=
  {z | scaledIntegerPoint t z ∈ J}

lemma scaledPoint_injective {d : ℕ} {t : ℝ} (ht : t ≠ 0) :
    Function.Injective (scaledIntegerPoint (d:=d) t) := by
  intro z w h
  funext j
  apply Int.cast_injective (α:=ℝ)
  exact mul_left_cancel₀ (inv_ne_zero ht) (congrFun h j)

lemma integerPoint_mem_lattice {d : ℕ} (z : Fin d → ℤ) :
    (fun j => (z j:ℝ)) ∈ integerLattice (Fin d) := by
  apply ((Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ _).mpr
  intro j
  exact ⟨z j,by simp⟩

lemma gridSet_finite {d : ℕ} {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    {t : ℝ} (ht : t ≠ 0) : (gridSet J t).Finite := by
  apply Set.Finite.of_injOn (f:=scaledIntegerPoint t)
    (t:=J ∩ t⁻¹ • (integerLattice (Fin d) : Set (Fin d → ℝ)))
  · intro z hz
    exact ⟨hz,⟨fun j => (z j:ℝ),integerPoint_mem_lattice z,rfl⟩⟩
  · exact (scaledPoint_injective ht).injOn
  · exact GridLimit.finite_scaled_lattice_inter _ hJ ht


def integerGrid {d : ℕ} (J : Set (Fin d → ℝ)) (hJ : IsCompact J) (t : ℝ) : Finset (Fin d → ℤ) := by
  classical
  exact if ht : t ≠ 0 then (gridSet_finite hJ ht).toFinset else ∅

lemma mem_integerGrid {d : ℕ} {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    {t : ℝ} (ht : t ≠ 0) {z : Fin d → ℤ} :
    z ∈ integerGrid J hJ t ↔ scaledIntegerPoint t z ∈ J := by
  classical
  simp only [integerGrid,dite_eq_left ht,Set.Finite.mem_toFinset,gridSet,Set.mem_ofPred_eq]

lemma card_integerGrid {d : ℕ} {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    {t : ℝ} (ht : t ≠ 0) :
    (integerGrid J hJ t).card = Nat.card ↥(J ∩ t⁻¹ • (integerLattice (Fin d) : Set (Fin d → ℝ))) := by
  classical
  let f : (integerGrid J hJ t) → ↥(J ∩ t⁻¹ • (integerLattice (Fin d) : Set (Fin d → ℝ))) :=
    fun z => ⟨scaledIntegerPoint t z.val,
      (mem_integerGrid hJ ht).mp z.property,
      ⟨fun j => (z.val j:ℝ),integerPoint_mem_lattice z.val,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z w h
      exact Subtype.ext (scaledPoint_injective ht (congrArg Subtype.val h))
    · intro y
      obtain ⟨u,hu,hy⟩ := y.property.2
      let z := integerCoordinates (⟨u,hu⟩ : integerLattice (Fin d))
      have he : scaledIntegerPoint t z = y.val := by
        rw [←hy]
        ext j
        simp only [scaledIntegerPoint,Pi.smul_apply,smul_eq_mul]
        rw [integerCoordinates_cast]
      refine ⟨⟨z,(mem_integerGrid hJ ht).mpr (he ▸ y.property.1)⟩,?_⟩
      exact Subtype.ext he
  simpa only [Fintype.card_coe] using (Nat.card_eq_fintype_card (α:=integerGrid J hJ t)).symm.trans
    (Nat.card_congr (Equiv.ofBijective f hf))


theorem normalized_card_limit {d : ℕ} {J : Set (Fin d → ℝ)}
    (hJc : IsCompact J) (hJv : Convex ℝ J) (h0 : 0 ∈ J) :
    Tendsto (fun t : ℝ => ((integerGrid J hJc t).card:ℝ)/t^d) atTop (𝓝 (volume.real J)) := by
  have h := tendsto_convex_grid_count (integerLattice (Fin d)) hJc hJv h0
  simp only [Fintype.card_fin,integerLattice_covolume,div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [card_integerGrid hJc ht.ne']

lemma grid_uniform_bound {d : ℕ} {J : Set (Fin d → ℝ)} (hJ : IsCompact J) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t, 1 ≤ t → ∀ z ∈ integerGrid J hJ t, ∀ j,
      |(z j:ℝ)| ≤ B*t := by
  obtain ⟨B,hBpos,hB⟩ := hJ.isBounded.exists_pos_norm_le
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro t ht z hz j
  have ht0 : 0 < t := by linarith
  have hmem := (mem_integerGrid hJ ht0.ne').mp hz
  have h := (norm_le_pi_norm (scaledIntegerPoint t z) j).trans (hB _ hmem)
  change |t⁻¹*(z j:ℝ)| ≤ B at h
  rw [abs_mul,abs_of_pos (inv_pos.mpr ht0)] at h
  have hh := mul_le_mul_of_nonneg_left h ht0.le
  rw [←mul_assoc,mul_inv_cancel₀ ht0.ne',one_mul] at hh
  exact hh.trans (by nlinarith [le_max_right (1:ℝ) B])



end SingleLatticeCovering.ConvexGrid





noncomputable section

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
