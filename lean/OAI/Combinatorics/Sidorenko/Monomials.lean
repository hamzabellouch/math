import OAI.Combinatorics.Sidorenko.SignMoments

namespace OAI


section

namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section StarMoment
variable {K I J : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty J] {N : ℕ}

noncomputable def starSign (v : I) (k : J → I) (W : I → SymMatrix K N)
    (z : I → (Fin N → K)) (a : I → K) : ℝ :=
  ∏ j, (quadraticChar K (symmetricBorder (W v-W (k j)) (z v-z (k j)) (a v-a (k j))).val.det : ℝ)

omit [Fintype I] [DecidableEq I] [DecidableEq J] [Nonempty J] in
theorem starSign_abs_le (v : I) (k : J → I) (W : I → SymMatrix K N)
    (z : I → (Fin N → K)) (a : I → K) : |starSign v k W z a| ≤ 1 :=
  characterProduct_abs_le _

omit [Fintype I] in
theorem starSign_update_bound (hK : ringChar K≠2) (v : I) (k : J → I)
    (hv : ∀ j, k j≠v) (W : I → SymMatrix K N) (z : I → (Fin N → K)) (a : I → K)
    (hW : goodMinors (fun j => W v-W (k j))) :
    |uniformMean (fun z' => starSign v k W (Function.update z v z') a)| ≤
      Real.sqrt (1/(Fintype.card K : ℝ)) := by
  have he (z' : Fin N → K) : starSign v k W (Function.update z v z') a =
      ∏ j, (quadraticChar K (symmetricBorder (W v-W (k j)) (z'-z (k j)) (a v-a (k j))).val.det : ℝ) := by
    simp only [starSign,Function.update_self,Function.update_of_ne (hv _)]
  simp_rw [he]
  apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
  rw [sq_abs]
  exact schur_sign_moment hK (fun j => W v-W (k j)) hW.1 (fun j => z (k j))
    (fun j => a v-a (k j)) hW.2

omit [Fintype I] in
theorem testedStar_update_bound (hK : ringChar K≠2) (v : I) (k : J → I)
    (hv : ∀ j, k j≠v) (W : I → SymMatrix K N) (z : I → (Fin N → K)) (a : I → K)
    (R : (I → (Fin N → K)) → ℝ) (hR : ∀ z, |R z| ≤ 1)
    (hRi : ∀ z', R (Function.update z v z')=R z) :
    |uniformMean (fun z' => R (Function.update z v z') * starSign v k W (Function.update z v z') a)| ≤
      Real.sqrt (1/(Fintype.card K : ℝ)) +
        (if goodMinors (fun j => W v-W (k j)) then 0 else 1) := by
  simp_rw [hRi]
  rw [uniformMean_mul,abs_mul]
  by_cases hW : goodMinors (fun j => W v-W (k j))
  · rw [ite_eq_left hW,add_zero]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hR z)).trans (starSign_update_bound hK v k hv W z a hW)
  · rw [ite_eq_right hW]
    apply le_trans _ (le_add_of_nonneg_left (Real.sqrt_nonneg _))
    apply (mul_le_of_le_one_left (abs_nonneg _) (hR z)).trans
    exact (abs_uniformMean_le _).trans (uniformMean_bound fun z' => starSign_abs_le v k W _ a)

theorem testedStar_mean_bound (hK : ringChar K≠2) (v : I) (k : J → I)
    (hk : Function.Injective k) (hv : ∀ j, k j≠v) (hN : Fintype.card J ≤ N)
    (R : (I → SymMatrix K N) → (I → (Fin N → K)) → (I → K) → ℝ)
    (hR : ∀ W z a, |R W z a| ≤ 1)
    (hRi : ∀ W z a z', R W (Function.update z v z') a=R W z a) :
    |uniformMean (fun W => uniformMean fun a => uniformMean fun z => R W z a * starSign v k W z a)| ≤
       Real.sqrt (1/(Fintype.card K : ℝ)) + minorBadBound N (Fintype.card J) (Fintype.card K) := by
  have hpoint (W : I → SymMatrix K N) (a : I → K) :
      |uniformMean (fun z => R W z a * starSign v k W z a)| ≤
        Real.sqrt (1/(Fintype.card K : ℝ)) +
          (if goodMinors (fun j => W v-W (k j)) then 0 else 1) := by
    rw [uniformMean_update v]
    apply (abs_uniformMean_le _).trans
    exact uniformMean_bound (fun z => testedStar_update_bound hK v k hv W z a (fun z => R W z a)
      (fun z => hR W z a) (hRi W z a))
  apply (abs_uniformMean_le _).trans
  calc
    _ ≤ uniformMean (fun W : I → SymMatrix K N => Real.sqrt (1/(Fintype.card K : ℝ)) +
        (if goodMinors (fun j => W v-W (k j)) then 0 else 1)) := by
      apply uniformMean_mono
      intro W
      exact (abs_uniformMean_le _).trans (uniformMean_bound (hpoint W))
    _ = Real.sqrt (1/(Fintype.card K : ℝ)) +
        uniformMean (fun M : J → SymMatrix K N => if goodMinors M then 0 else 1) := by
      rw [uniformMean_add,uniformMean_const]
      congr 1
      exact uniformMean_starDifference (K := K) v k hk hv
        (fun M : J → SymMatrix K N => if goodMinors M then 0 else 1)
    _ ≤ _ := add_le_add le_rfl (badMinors_bound (K := K) hN)
end StarMoment
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators

def pairLeft : Fin 33 → Fin 13 := ![0,0,2,0,2,0,1,2,3,1,4,1,3,3,4,1,9,4,8,1,7,10,8,7,8,5,5,5,6,6,6,6,5]
def pairRight : Fin 33 → Fin 13 := ![2,3,3,9,9,1,3,4,4,9,9,10,10,11,11,12,12,8,9,7,10,11,11,12,12,7,10,11,8,11,7,12,6]
theorem pair_endpoints : ∀ e, pairVertices e={pairLeft e,pairRight e} := by decide
theorem pair_endpoints_ne : ∀ e, pairLeft e≠pairRight e := by decide

def pairOther (v : Fin 13) (e : Fin 33) : Fin 13 := if pairLeft e=v then pairRight e else pairLeft e

theorem pairOther_ne (v : Fin 13) (e : Fin 33) (_hv : v∈pairVertices e) : pairOther v e≠v := by
  unfold pairOther
  split_ifs with h
  · simpa only [h] using (pair_endpoints_ne e).symm
  · exact h

theorem pair_vertices_other (v : Fin 13) (e : Fin 33) (hv : v∈pairVertices e) :
    pairVertices e={v,pairOther v e} := by
  rw [pair_endpoints] at hv ⊢
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  unfold pairOther
  split_ifs with h
  · rw [h]
  · rcases hv with h' | h'
    · exact (h h'.symm).elim
    · rw [h']; exact Finset.pair_comm _ _

def selectedIncident (F : Finset (Fin 33)) (v : Fin 13) : Finset (Fin 33) :=
  F.filter (fun e => v∈pairVertices e)

theorem selectedIncident_card (F : Finset (Fin 33)) (v : Fin 13) : (selectedIncident F v).card ≤ 6 := by
  apply le_trans (Finset.card_le_card ?_) (incidentPairs_card_le v)
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩

theorem pairOther_injective (F : Finset (Fin 33)) (v : Fin 13) :
    Function.Injective (fun e : selectedIncident F v => pairOther v e.val) := by
  intro e f h
  dsimp only at h
  apply Subtype.ext
  apply pairVertices_injective
  rw [pair_vertices_other v e.val (Finset.mem_filter.mp e.property).2,
    pair_vertices_other v f.val (Finset.mem_filter.mp f.property).2,h]

section Signs
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
noncomputable def pairSign (X : Fin 13 → SymMatrix K D) (e : Fin 33) : ℝ :=
  quadraticChar K (X (pairLeft e)-X (pairRight e)).val.det

theorem pairSign_abs_le (X : Fin 13 → SymMatrix K D) (e : Fin 33) : |pairSign X e| ≤ 1 := by
  unfold pairSign
  by_cases h : (X (pairLeft e)-X (pairRight e)).val.det=0
  · rw [h]; norm_num
  · rcases quadraticChar_dichotomy (F := K) h with h | h <;> rw [h] <;> norm_num

omit [Fintype K] [DecidableEq K] in
theorem determinant_difference_even (hD : Even D) (A B : SymMatrix K D) :
    (A-B).val.det=(B-A).val.det := by
  have he : A-B= -(B-A) := by abel
  rw [he,Submodule.coe_neg,Matrix.det_neg,Fintype.card_fin,hD.neg_pow,one_pow,one_mul]

theorem pairSign_other (hD : Even D) (X : Fin 13 → SymMatrix K D)
    (v : Fin 13) (e : Fin 33) (hv : v∈pairVertices e) :
    pairSign X e=quadraticChar K (X v-X (pairOther v e)).val.det := by
  rw [pair_endpoints] at hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  unfold pairSign pairOther
  split_ifs with h
  · rw [h]
  · rcases hv with h' | h'
    · exact (h h'.symm).elim
    · rw [h',determinant_difference_even hD]

theorem pairSign_product_abs_le (F : Finset (Fin 33)) (X : Fin 13 → SymMatrix K D) :
    |∏ e∈F, pairSign X e| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun e _ => abs_nonneg _) (fun e _ => pairSign_abs_le X e)
end Signs
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Moment
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {N : ℕ}

noncomputable def nonincidentProduct (F : Finset (Fin 33)) (v : Fin 13)
    (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K) : ℝ :=
  ∏ e∈F\selectedIncident F v, pairSign (fun i => symmetricBorder (W i) (z i) (a i)) e

theorem nonincidentProduct_abs_le (F : Finset (Fin 33)) (v : Fin 13)
    (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K) :
    |nonincidentProduct F v W z a| ≤ 1 := pairSign_product_abs_le _ _

theorem nonincidentProduct_update (F : Finset (Fin 33)) (v : Fin 13)
    (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K)
    (z' : Fin N → K) : nonincidentProduct F v W (Function.update z v z') a=
      nonincidentProduct F v W z a := by
  apply Finset.prod_congr rfl
  intro e he
  obtain ⟨heF,heN⟩ := Finset.mem_sdiff.mp he
  have hv : v∉pairVertices e := by
    intro h
    exact heN (Finset.mem_filter.mpr ⟨heF,h⟩)
  have hl : pairLeft e≠v := by
    intro h; apply hv; rw [pair_endpoints, h]; simp
  have hr : pairRight e≠v := by
    intro h; apply hv; rw [pair_endpoints, h]; simp
  simp only [pairSign,Function.update_of_ne hl,Function.update_of_ne hr]

theorem pairSign_product_split (hN : Even (N+1)) (F : Finset (Fin 33)) (v : Fin 13)
    (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K) :
    (∏ e∈F, pairSign (fun i => symmetricBorder (W i) (z i) (a i)) e)=
      nonincidentProduct F v W z a * starSign v
        (fun e : selectedIncident F v => pairOther v e.val) W z a := by
  have he : starSign v (fun e : selectedIncident F v => pairOther v e.val) W z a=
      ∏ e∈selectedIncident F v, pairSign (fun i => symmetricBorder (W i) (z i) (a i)) e := by
    rw [←Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro e _
    rw [pairSign_other hN _ v e.val (Finset.mem_filter.mp e.property).2]
    rw [symmetricBorder_sub]
  rw [he]
  exact (Finset.prod_sdiff (Finset.filter_subset _ _)).symm

theorem pairSign_moment_bound (hK : ringChar K≠2) (hN : Even (N+1))
    (F : Finset (Fin 33)) (v : Fin 13) (hne : (selectedIncident F v).Nonempty)
    (hc : (selectedIncident F v).card ≤ N) :
    |uniformMean (fun X : Fin 13 → SymMatrix K (N+1) => ∏ e∈F, pairSign X e)| ≤
      Real.sqrt (1/(Fintype.card K : ℝ)) +
        minorBadBound N (selectedIncident F v).card (Fintype.card K) := by
  let : Nonempty (selectedIncident F v) := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  rw [uniformMean_bordered]
  simp_rw [pairSign_product_split hN F v]
  have he (W : Fin 13 → SymMatrix K N) := uniformMean_swap
    (fun z a => nonincidentProduct F v W z a * starSign v
      (fun e : selectedIncident F v => pairOther v e.val) W z a)
  simp_rw [he]
  simpa only [Fintype.card_coe] using testedStar_mean_bound hK v _ (pairOther_injective F v)
    (fun e => pairOther_ne v e.val (Finset.mem_filter.mp e.property).2)
    (by simpa using hc) (nonincidentProduct F v)
    (nonincidentProduct_abs_le F v) (nonincidentProduct_update F v)
end Moment

 theorem minorBadBound_tendsto (N s : ℕ) (h : s<(N-s+1).choose 2) :
    Tendsto (minorBadBound N s) atTop (nhds 0) := by
  have ha : Tendsto (fun q : ℝ => (s : ℝ)*N/q) atTop (nhds 0) := by
    simpa only [mul_zero,div_eq_mul_inv] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul ((s : ℝ)*N)
  have hb : Tendsto (fun q : ℝ => q^s*(2^(N-s)/q^((N-s+1).choose 2))) atTop (nhds 0) := by
    have ht := (inverse_power_tendsto_zero ((N-s+1).choose 2-s) (by omega)).const_mul ((2 : ℝ)^(N-s))
    simp only [mul_zero] at ht
    apply ht.congr' (eventually_atTop.mpr ⟨1,fun q hq => ?_⟩)
    have hq0 : q≠0 := by linarith
    have hn : (N-s+1).choose 2=s+((N-s+1).choose 2-s) := by omega
    rw [hn,pow_add]
    field_simp
    congr 1; omega
  change Tendsto (fun q : ℝ => (s : ℝ)*N/q + q^s*(2^(N-s)/q^((N-s+1).choose 2))) atTop (nhds 0)
  simpa only [add_zero] using ha.add hb

 theorem sign_moment_dimension (N s : ℕ) (hN : 11≤N) (hs : s≤6) :
    s≤N ∧ s<(N-s+1).choose 2 := by
  have hd : 6≤N-s+1 := by omega
  have hc := Nat.choose_le_choose 2 hd
  rw [show (6:ℕ).choose 2=15 by decide] at hc
  omega

theorem pairSign_moment_tendsto (D : ℕ) (hD : Even D) (hbig : 12≤D)
    (F : Finset (Fin 33)) (hF : F.Nonempty) :
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
      ∏ e∈F, pairSign X e)) primeInfinity (nhds 0) := by
  obtain ⟨e,he⟩ := hF
  let v := pairLeft e
  have hi : (selectedIncident F v).Nonempty := by
    refine ⟨e,Finset.mem_filter.mpr ⟨he,?_⟩⟩
    rw [pair_endpoints]; exact Finset.mem_insert_self _ _
  have hn : D=D-1+1 := by omega
  have hn' : Even (D-1+1) := hn ▸ hD
  have hc := sign_moment_dimension (D-1) (selectedIncident F v).card (by omega) (selectedIncident_card F v)
  have ht : Tendsto (fun q : OddPrime => Real.sqrt (1/(q.val : ℝ)) +
      minorBadBound (D-1) (selectedIncident F v).card q.val) primeInfinity (nhds 0) := by
    have ha := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((inverse_power_tendsto_zero 1 (by omega)).comp primeInfinity_real_tendsto)
    simpa only [pow_one,Real.sqrt_zero,add_zero,Function.comp_def] using ha.add
      ((minorBadBound_tendsto (D-1) _ hc.2).comp primeInfinity_real_tendsto)
  apply squeeze_zero_norm (fun q => ?_) ht
  rw [Real.norm_eq_abs]
  conv_lhs => rw [hn]
  simpa only [ZMod.card] using pairSign_moment_bound
    (K := ZMod q.val) (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) hn' F v hi hc.1
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section Product
variable {I : Type*} [DecidableEq I]
omit [DecidableEq I] in
theorem abs_prod_le_pow (s : Finset I) (f : I → ℝ) {C : ℝ} (_hC : 0≤C)
    (hf : ∀ i∈s, |f i|≤C) : |∏ i∈s, f i|≤C^s.card := by
  rw [Finset.abs_prod,←Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hf

theorem product_difference_bound (s : Finset I) (f g : I → ℝ) {C : ℝ} (hC : 1≤C)
    (hf : ∀ i∈s, |f i|≤C) (hg : ∀ i∈s, |g i|≤C) :
    |(∏ i∈s, f i)-(∏ i∈s, g i)| ≤ C^s.card * ∑ i∈s, |f i-g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hC0 : 0≤C := le_trans (by norm_num) hC
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    specialize ih hf' hg'
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.card_insert_of_notMem ha,
      Finset.sum_insert ha,pow_succ]
    calc
      _ = |f a*((∏ i∈s, f i)-(∏ i∈s, g i)) + (f a-g a)*(∏ i∈s, g i)| := by congr 1; ring
      _ ≤ |f a*((∏ i∈s, f i)-(∏ i∈s, g i))| + |(f a-g a)*(∏ i∈s, g i)| := abs_add_le _ _
      _ = |f a| * |(∏ i∈s, f i)-(∏ i∈s, g i)| + |f a-g a| * |∏ i∈s, g i| := by simp only [abs_mul]
      _ ≤ C*(C^s.card*∑ i∈s, |f i-g i|) + |f a-g a| * C^s.card :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self ..)) ih (abs_nonneg _) hC0)
          (mul_le_mul_of_nonneg_left (abs_prod_le_pow s g hC0 hg') (abs_nonneg _))
      _ ≤ _ := by
        have h : |f a-g a| * C^s.card ≤ C*(|f a-g a| * C^s.card) :=
          le_mul_of_one_le_left (mul_nonneg (abs_nonneg _) (pow_nonneg hC0 _)) hC
        nlinarith

theorem product_difference_unit (s : Finset I) (f g : I → ℝ)
    (hf : ∀ i∈s, |f i|≤1) (hg : ∀ i∈s, |g i|≤1) :
    |(∏ i∈s, f i)-(∏ i∈s, g i)| ≤ ∑ i∈s, |f i-g i| := by
  simpa only [one_pow,one_mul] using product_difference_bound s f g (le_refl 1) hf hg
end Product
section Mean
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
omit [Fintype I] [DecidableEq I] in
theorem uniformMean_finset_sum (s : Finset I) (f : I → A → ℝ) :
    uniformMean (fun a => ∑ i∈s, f i a)=∑ i∈s, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm,Finset.sum_div]

theorem uniformMean_pi_product (f : I → A → ℝ) :
    uniformMean (fun x : I → A => ∏ i, f i (x i))=∏ i, uniformMean (f i) := by
  unfold uniformMean
  rw [←Fintype.prod_sum,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,
    Fintype.card_fun,Nat.cast_pow]
end Mean
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Difference
variable {K I W : Type*} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module K W] [Fintype W]
include K in
theorem uniformMean_point_difference (i k : I) (hik : i≠k) (f : W → ℝ) :
    uniformMean (fun X : I → W => f (X i-X k))=uniformMean f := by
  let L : (I → W) →ₗ[K] W :=
    { toFun := fun X => X i-X k
      map_add' := by intros; simp only [Pi.add_apply]; abel
      map_smul' := by intros; simp only [Pi.smul_apply,smul_sub,RingHom.id_apply] }
  have hL : Function.Surjective L := by
    intro w
    refine ⟨Function.update 0 i w,?_⟩
    change (Function.update (0 : I → W) i w) i-(Function.update (0 : I → W) i w) k=w
    simp [Function.update_of_ne hik.symm]
  exact uniformMean_surjective_linear L hL f
end Difference
section Pair
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
noncomputable def pairSingular (X : Fin 13 → SymMatrix K D) (e : Fin 33) : ℝ :=
  if (X (pairLeft e)-X (pairRight e)).val.det=0 then 1 else 0

omit [Fintype K] in
theorem pairSingular_nonneg (X : Fin 13 → SymMatrix K D) (e : Fin 33) : 0≤pairSingular X e := by
  unfold pairSingular; split <;> norm_num

theorem pairSingular_mean (e : Fin 33) :
    uniformMean (fun X : Fin 13 → SymMatrix K D => pairSingular X e)≤(D : ℝ)/Fintype.card K := by
  unfold pairSingular
  rw [uniformMean_point_difference (K := K) _ _ (pair_endpoints_ne e)
    (fun B : SymMatrix K D => if B.val.det=0 then 1 else 0)]
  exact symmetricSingularProb_bound D

def fullTransverse (X : Fin 13 → SymMatrix K D) : Prop :=
  ∀ e : Fin 33, (X (pairLeft e)-X (pairRight e)).val.det≠0

omit [Fintype K] in
theorem nonTransverse_pointwise (X : Fin 13 → SymMatrix K D) :
    (if fullTransverse X then 0 else 1 : ℝ) ≤ ∑ e, pairSingular X e := by
  by_cases h : fullTransverse X
  · rw [ite_eq_left h]; exact Finset.sum_nonneg fun e _ => pairSingular_nonneg X e
  · rw [ite_eq_right h]
    obtain ⟨e,he⟩ := not_forall.mp h
    have he := not_not.mp he
    calc
      (1 : ℝ) = pairSingular X e := by rw [pairSingular,ite_eq_left he]
      _ ≤ _ := Finset.single_le_sum (fun e _ => pairSingular_nonneg X e) (Finset.mem_univ e)

theorem nonTransverse_mean :
    uniformMean (fun X : Fin 13 → SymMatrix K D => if fullTransverse X then 0 else 1) ≤
      33*((D : ℝ)/Fintype.card K) := by
  apply (uniformMean_mono nonTransverse_pointwise).trans
  rw [uniformMean_sum]
  calc
    _ ≤ ∑ _e : Fin 33, (D : ℝ)/Fintype.card K := Finset.sum_le_sum fun e _ => pairSingular_mean e
    _ = _ := by simp

noncomputable def pairBool (X : Fin 13 → SymMatrix K D) (e : Fin 33) : Bool :=
  decide (pairSign X e=1)

def boolSign (b : Bool) : ℝ := if b then 1 else -1
@[simp] theorem boolSign_abs (b : Bool) : |boolSign b|=1 := by cases b <;> norm_num [boolSign]
@[simp] theorem boolSign_sq (b : Bool) : boolSign b^2=1 := by cases b <;> norm_num [boolSign]

theorem pairBool_error (X : Fin 13 → SymMatrix K D) (e : Fin 33) :
    |boolSign (pairBool X e)-pairSign X e| ≤ pairSingular X e := by
  by_cases hz : (X (pairLeft e)-X (pairRight e)).val.det=0
  · have he : pairSign X e=0 := by unfold pairSign; rw [hz]; norm_num
    rw [pairSingular,ite_eq_left hz,he]
    simp
  · have he : pairSign X e=1 ∨ pairSign X e= -1 := by
      unfold pairSign
      rcases quadraticChar_dichotomy (F := K) hz with h | h <;> rw [h] <;> norm_num
    rw [pairSingular,ite_eq_right hz]
    rcases he with he | he <;> norm_num [pairBool,he,boolSign]

theorem pairBool_moment_error (F : Finset (Fin 33)) :
    |uniformMean (fun X : Fin 13 → SymMatrix K D => ∏ e∈F, boolSign (pairBool X e))-
      uniformMean (fun X : Fin 13 → SymMatrix K D => ∏ e∈F, pairSign X e)| ≤
        (F.card : ℝ)*((D : ℝ)/Fintype.card K) := by
  rw [←uniformMean_sub]
  apply (abs_uniformMean_le _).trans
  calc
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K D => ∑ e∈F, pairSingular X e) := by
      apply uniformMean_mono
      intro X
      exact (product_difference_unit F _ _ (by simp) (fun e _ => pairSign_abs_le X e)).trans
        (Finset.sum_le_sum fun e _ => pairBool_error X e)
    _ = ∑ e∈F, uniformMean (fun X : Fin 13 → SymMatrix K D => pairSingular X e) := uniformMean_finset_sum _ _
    _ ≤ ∑ _e∈F, (D : ℝ)/Fintype.card K := Finset.sum_le_sum fun e _ => pairSingular_mean e
    _ = _ := by simp
end Pair

theorem pairBool_moment_tendsto (D : ℕ) (hD : Even D) (hbig : 12≤D)
    (F : Finset (Fin 33)) (hF : F.Nonempty) :
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
      ∏ e∈F, boolSign (pairBool X e))) primeInfinity (nhds 0) := by
  have hm := pairSign_moment_tendsto D hD hbig F hF
  have hb : Tendsto (fun q : OddPrime => (F.card : ℝ)*((D : ℝ)/(q.val : ℝ))) primeInfinity (nhds 0) := by
    simpa only [mul_zero,Function.comp_def,div_eq_mul_inv] using
      (((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp primeInfinity_real_tendsto).const_mul (D : ℝ)).const_mul (F.card : ℝ)
  have he : Tendsto (fun q : OddPrime =>
      uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D => ∏ e∈F, boolSign (pairBool X e))-
      uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D => ∏ e∈F, pairSign X e)) primeInfinity (nhds 0) := by
    apply squeeze_zero_norm (fun q => ?_) hb
    simpa only [Real.norm_eq_abs,ZMod.card] using pairBool_moment_error (K := ZMod q.val) (D := D) F
  simpa only [sub_add_cancel,add_zero] using he.add hm
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Graph
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
noncomputable def fullGraphIntersection (B C : LinearMap.BilinForm K V) :
    (B-C).ker ≃ₗ[K] ↥(B.graph⊓C.graph) where
  toFun x := ⟨(x.val,B x.val),by
    constructor
    · rfl
    · apply (C.mem_graph_iff _).mpr
      exact sub_eq_zero.mp (show B x.val-C x.val=0 from x.property)⟩
  invFun x := ⟨x.val.1,by
    have hb := (B.mem_graph_iff _).mp x.property.1
    have hc := (C.mem_graph_iff _).mp x.property.2
    change B x.val.1-C x.val.1=0
    rw [←hb,←hc,sub_self]⟩
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl ((B.mem_graph_iff _).mp x.property.1).symm
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp

noncomputable def matrixLagrangian {D : ℕ} (M : SymMatrix K D) :
    SymplecticLagrangian (canonicalSymplectic (K := K) (V := Fin D → K)) :=
  ⟨M.val.toBilin'.graph, fullGraph_selforthogonal _ (Matrix.isSymm_toBilin'_iff_isSymm.mpr M.property)⟩

theorem matrixLagrangian_injective (D : ℕ) : Function.Injective (matrixLagrangian (K := K) (D := D)) := by
  intro A B h
  apply Subtype.ext
  apply Matrix.toBilin'.injective
  exact fullGraph_injective (congrArg Subtype.val h)

theorem matrixLagrangian_pair_rank (D : ℕ) (A B : SymMatrix K D) :
    finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian B).val)+(A-B).val.rank=D := by
  have h := ((A-B).val.toBilin').ker.finrank_quotient_add_finrank
  rw [matrix_radical_quotient_rank] at h
  have he := (fullGraphIntersection A.val.toBilin' B.val.toBilin').finrank_eq
  have hf : (A-B).val.toBilin'=A.val.toBilin'-B.val.toBilin' := by rw [Submodule.coe_sub,map_sub]
  rw [hf] at h
  simp only [Module.finrank_pi,Fintype.card_fin] at h
  change finrank K ↥(A.val.toBilin'.graph⊓B.val.toBilin'.graph)+(A-B).val.rank=D
  omega

theorem matrixLagrangian_pair_zero (D : ℕ) (A B : SymMatrix K D) :
    finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian B).val)=0 ↔ (A-B).val.det≠0 := by
  change finrank K ↥(A.val.toBilin'.graph⊓B.val.toBilin'.graph)=0 ↔ (A-B).val.det≠0
  rw [← (fullGraphIntersection A.val.toBilin' B.val.toBilin').finrank_eq]
  have hf : (A-B).val.toBilin'=A.val.toBilin'-B.val.toBilin' := by rw [Submodule.coe_sub,map_sub]
  rw [←hf,Submodule.finrank_eq_zero]
  exact LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.symm.trans
    (Matrix.nondegenerate_toBilin'_iff.trans Matrix.nondegenerate_iff_det_ne_zero)
end Graph
end SidorenkoCounterexample

end

end OAI
