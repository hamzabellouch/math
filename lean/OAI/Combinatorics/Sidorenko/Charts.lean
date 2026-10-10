import OAI.Combinatorics.Sidorenko.Monomials

namespace OAI


section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Mean
variable {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
theorem uniformMean_injection (i : A → B) (hi : Function.Injective i) (f : B → ℝ)
    (hf : ∀ b,0≤f b) : uniformMean (f ∘ i) ≤
      ((Fintype.card B : ℝ)/Fintype.card A)*uniformMean f := by
  classical
  have hs : ∑ a, f (i a) ≤ ∑ b, f b := by
    rw [←Finset.sum_image (fun a _ b _ h => hi h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hf b)
  unfold uniformMean
  dsimp only [Function.comp_def]
  have hn : (Fintype.card B : ℝ)≠0 := by exact_mod_cast (Fintype.card_pos (α := B)).ne'
  have he : ((Fintype.card B : ℝ)/Fintype.card A)*((∑ b,f b)/Fintype.card B)=
      (∑ b,f b)/Fintype.card A := by
    calc
      _ = ((∑ b,f b)/Fintype.card A)*((Fintype.card B : ℝ)/Fintype.card B) := by ring
      _ = _ := by rw [div_self hn,mul_one]
  rw [he]
  exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)
end Mean
section Norm
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def canonicalStratumMass (D r : ℕ) : ℝ :=
  (Nat.card (CenterStratum (K := K) (V := Fin D → K) r) : ℝ)/
    Nat.card (Lagrangian (K := K) (V := Fin D → K))
noncomputable def chartRatio (D : ℕ) : ℝ :=
  (Nat.card (Lagrangian (K := K) (V := Fin D → K)) : ℝ)/
    Fintype.card (SymMatrix K D)

omit [DecidableEq K] in
theorem chartRatio_nonneg (D : ℕ) : 0≤chartRatio (K := K) D := by unfold chartRatio; positivity

omit [DecidableEq K] in
theorem chartRatio_bound (D : ℕ) : chartRatio (K := K) D≤lagrangianConstant D := by
  have hc : (Fintype.card (SymMatrix K D) : ℝ)=(Fintype.card K : ℝ)^((D+1).choose 2) := by
    rw [←Nat.card_eq_fintype_card,symMatrix_card,Nat.cast_pow]
  have hn : (0 : ℝ)<(Fintype.card K : ℝ)^((D+1).choose 2) := by positivity
  unfold chartRatio
  rw [hc]
  apply (div_le_iff₀ hn).mpr
  simpa only [Module.finrank_pi,Fintype.card_fin] using lagrangian_card_upper (K := K) (V := Fin D → K)

omit [DecidableEq K] in
theorem canonicalStratum_card (D r : ℕ) (hr : r≤D) :
    Nat.card (CenterStratum (K := K) (V := Fin D → K) r) =
      Nat.card (DimSubspace K (Fin D → K) (D-r)) * (Fintype.card K)^((D-r+1).choose 2) := by
  have hD : r≤finrank K (Fin D → K) := by simpa only [Module.finrank_pi,Fintype.card_fin] using hr
  have h := vertical_pair_count (K := K) (V := Fin D → K) r hD
  simpa only [Module.finrank_pi,Fintype.card_fin,CenterStratum,DimSubspace] using h

omit [DecidableEq K] in
theorem canonicalLag_card_pos (D : ℕ) : (0 : ℝ)<Nat.card (Lagrangian (K := K) (V := Fin D → K)) := by
  exact lt_of_lt_of_le (by positivity) (lagrangian_card_lower (K := K) (V := Fin D → K))

omit [DecidableEq K] in
theorem canonicalStratumMass_pos (D r : ℕ) (hr : r≤D) : 0<canonicalStratumMass (K := K) D r := by
  have hl := subspace_count_lower (K := K) (V := Fin D → K) (D-r) (by simp)
  have hp : 0<(Nat.card (DimSubspace K (Fin D → K) (D-r)) : ℝ) := lt_of_lt_of_le (by positivity) hl
  unfold canonicalStratumMass
  rw [canonicalStratum_card D r hr,Nat.cast_mul,Nat.cast_pow]
  apply div_pos (mul_pos hp (by positivity))
  exact canonicalLag_card_pos (K := K) D

omit [DecidableEq K] in
theorem canonicalStratumMass_bound (D r : ℕ) (hr : r≤D) :
    canonicalStratumMass (K := K) D r*(Fintype.card K : ℝ)^((r+1).choose 2)≤2^(D-r) := by
  let n : ℝ := Nat.card (Lagrangian (K := K) (V := Fin D → K))
  have hn : 0<n := canonicalLag_card_pos (K := K) D
  have hc : (Nat.card (CenterStratum (K := K) (V := Fin D → K) r) : ℝ)=
      (Nat.card (DimSubspace K (Fin D → K) (D-r)) : ℝ)*(Fintype.card K : ℝ)^((D-r+1).choose 2) := by
    rw [canonicalStratum_card D r hr,Nat.cast_mul,Nat.cast_pow]
  have hu := subspace_count_upper (K := K) (V := Fin D → K) (D-r) (by simp)
  simp only [Module.finrank_pi,Fintype.card_fin,Nat.sub_sub_self hr] at hu
  have he : (D-r)*r+(D-r+1).choose 2+(r+1).choose 2=(D+1).choose 2 := by
    simpa only [Nat.mul_comm] using symmetric_nullity_exponent D r hr
  have hl : (Fintype.card K : ℝ)^((D+1).choose 2)≤n := by
    simpa only [Module.finrank_pi,Fintype.card_fin] using lagrangian_card_lower (K := K) (V := Fin D → K)
  change ((Nat.card (CenterStratum (K := K) (V := Fin D → K) r) : ℝ)/n)*_≤_
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hn).mpr
  rw [hc]
  calc
    _ ≤ (2^(D-r)*(Fintype.card K : ℝ)^((D-r)*r)) *
        (Fintype.card K : ℝ)^((D-r+1).choose 2)*(Fintype.card K : ℝ)^((r+1).choose 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu (by positivity)) (by positivity)
    _ = 2^(D-r)*(Fintype.card K : ℝ)^((D+1).choose 2) := by rw [mul_assoc,mul_assoc,←pow_add,←pow_add,←Nat.add_assoc,he]
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
end Norm

theorem signed_normalization_eventually (r : ℕ) (hr : 0<r) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    ∀ᶠ q : OddPrime in primeInfinity,
      canonicalStratumMass (K := ZMod q.val) (2*r) r /
        layerMass (ZMod q.val) (2*r) r ξ ≤ 4*2^r := by
  have h := (layerMass_tendsto (2*r) r hr (by omega) hξ).eventually (lt_mem_nhds (by norm_num : (1/4 : ℝ)<1/2))
  filter_upwards [h] with q hq
  have he : 2*r-r=r := by omega
  rw [he] at hq
  have hb := canonicalStratumMass_bound (K := ZMod q.val) (2*r) r (by omega)
  rw [he,ZMod.card] at hb
  have hp : (0:ℝ)<(q.val : ℝ)^((r+1).choose 2) := by exact pow_pos (by exact_mod_cast q.property.1.pos) _
  have hd : 0<layerMass (ZMod q.val) (2*r) r ξ := by nlinarith
  apply (div_le_iff₀ hd).mpr
  nlinarith [mul_pos hp hd, pow_pos (by norm_num : (0:ℝ)<2) r]
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Face
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def faceLocal (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 3 → SymMatrix K (2*r)) : ℝ :=
  uniformMean (fun Y => ∏ k∈T, rankKernel K (2*r) r (ξ k) (X k-Y))

@[simp] theorem faceLocal_empty (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)) :
    faceLocal r ∅ ξ X=1 := by simp [faceLocal,uniformMean_const]

theorem faceLocal_singleton (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) (X : Fin 3 → SymMatrix K (2*r)) (k : Fin 3) :
    faceLocal r {k} ξ X=1 := by
  simp only [faceLocal,Finset.prod_singleton]
  rw [uniformMean_subLeft,uniformMean_rankKernel _ _ hr (by omega) hK (hξ k)]

theorem faceLocal_pair (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r))
    (k l : Fin 3) (hkl : k≠l) :
    faceLocal r {k,l} ξ X=pairLocal r (ξ k) (ξ l) (X k-X l) := by
  simp only [faceLocal,Finset.prod_pair hkl,pairLocal]
  have he (Y : SymMatrix K (2*r)) : X l-Y=(X k-Y)-(X k-X l) := by abel
  simp_rw [he]
  exact uniformMean_subLeft (X k) (fun A => rankKernel K (2*r) r (ξ k) A *
    rankKernel K (2*r) r (ξ l) (A-(X k-X l)))

theorem faceLocal_full (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)) :
    faceLocal r Finset.univ ξ X=tripleLocal r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2) := by
  simp only [faceLocal,Fin.prod_univ_three,tripleLocal]
  have h1 (Y : SymMatrix K (2*r)) : X 1-Y=(X 0-Y)-(X 0-X 1) := by abel
  have h2 (Y : SymMatrix K (2*r)) : X 2-Y=(X 0-Y)-(X 0-X 2) := by abel
  simp_rw [h1,h2]
  exact uniformMean_subLeft (X 0) (fun A => rankKernel K (2*r) r (ξ 0) A *
    rankKernel K (2*r) r (ξ 1) (A-(X 0-X 1))*rankKernel K (2*r) r (ξ 2) (A-(X 0-X 2)))

noncomputable def pairPolynomial (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : ℝ :=
  1+(quadraticChar K ((-1 : K)^r) : ℝ)*(quadraticChar K B.val.det : ℝ)*(ξ : ℝ)*(ζ : ℝ)

theorem signs_polynomial (c x ξ ζ : ℤ) (hc : c=1 ∨ c= -1) (hx : x=1 ∨ x= -1)
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) :
    (1+(c : ℝ)*(x : ℝ)*(ξ : ℝ)*(ζ : ℝ))=(if x=c*ξ*ζ then 2 else 0) := by
  rcases hc with rfl|rfl <;> rcases hx with rfl|rfl <;>
    rcases hξ with rfl|rfl <;> rcases hζ with rfl|rfl <;> norm_num

theorem pairPolynomial_eq (r : ℕ) {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1)
    (B : SymMatrix K (2*r)) (hB : B.val.det≠0) :
    pairPolynomial r ξ ζ B=if pairMatch r ξ ζ B then 2 else 0 := by
  have he := signs_polynomial _ _ _ _ (quadraticChar_dichotomy (F := K) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero)))
    (quadraticChar_dichotomy hB) hξ hζ
  unfold pairPolynomial pairMatch
  split_ifs with hm
  · rw [ite_eq_left hm] at he; exact he
  · rw [ite_eq_right hm] at he; exact he

noncomputable def facePolynomial (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 3 → SymMatrix K (2*r)) : ℝ :=
  (if 0∈T ∧ 1∈T then pairPolynomial r (ξ 0) (ξ 1) (X 0-X 1) else 1)*
  (if 0∈T ∧ 2∈T then pairPolynomial r (ξ 0) (ξ 2) (X 0-X 2) else 1)*
  (if 1∈T ∧ 2∈T then pairPolynomial r (ξ 1) (ξ 2) (X 1-X 2) else 1)

def faceTransverse (r : ℕ) (X : Fin 3 → SymMatrix K (2*r)) : Prop :=
  (X 0-X 1).val.det≠0 ∧ (X 0-X 2).val.det≠0 ∧ (X 1-X 2).val.det≠0

theorem facePolynomial_full (r : ℕ) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
    (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X) :
    facePolynomial r Finset.univ ξ X=
      if tripleMatch r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2) then 8 else 0 := by
  unfold facePolynomial
  simp only [Finset.mem_univ,and_self,ite_true]
  rw [pairPolynomial_eq r (hξ 0) (hξ 1) _ hX.1,
    pairPolynomial_eq r (hξ 0) (hξ 2) _ hX.2.1,pairPolynomial_eq r (hξ 1) (hξ 2) _ hX.2.2]
  have he : X 0-X 2-(X 0-X 1)=X 1-X 2 := by abel
  simp only [tripleMatch,he]
  split_ifs <;> norm_num <;> tauto

noncomputable def faceError (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)) : ℝ :=
  pairError r (ξ 0) (ξ 1) (X 0-X 1)+pairError r (ξ 0) (ξ 2) (X 0-X 2)+
    pairError r (ξ 1) (ξ 2) (X 1-X 2)+tripleError r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)

theorem faceError_nonneg (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)) :
    0≤faceError r ξ X := by
  exact add_nonneg (add_nonneg (add_nonneg (pairError_nonneg ..) (pairError_nonneg ..))
    (pairError_nonneg ..)) (tripleError_nonneg ..)

theorem faceLocal_error (hK : ringChar K≠2) (r : ℕ) (hr : 0<r) (T : Finset (Fin 3))
    (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
    (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X) :
    |faceLocal r T ξ X-facePolynomial r T ξ X|≤faceError r ξ X := by
  have he : X 0-X 2-(X 0-X 1)=X 1-X 2 := by abel
  have hfull : (X 0-X 1).val.det≠0 ∧ (X 0-X 2).val.det≠0 ∧
      (X 0-X 2-(X 0-X 1)).val.det≠0 := by simpa only [he,faceTransverse] using hX
  have n01 := pairError_nonneg r (ξ 0) (ξ 1) (X 0-X 1)
  have n02 := pairError_nonneg r (ξ 0) (ξ 2) (X 0-X 2)
  have n12 := pairError_nonneg r (ξ 1) (ξ 2) (X 1-X 2)
  have nt := tripleError_nonneg r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)
  rcases fin3_subsets T with ht|ht|ht|ht|ht|ht|ht|ht
  · subst T; simpa [facePolynomial] using faceError_nonneg r ξ X
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; simpa [facePolynomial] using faceError_nonneg r ξ X
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; simpa [facePolynomial] using faceError_nonneg r ξ X
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; simpa [facePolynomial] using faceError_nonneg r ξ X
  · subst T
    rw [faceLocal_pair r ξ X 0 1 (by decide)]
    simp [facePolynomial, show (2 : Fin 3)≠0 from by decide, show (2 : Fin 3)≠1 from by decide]
    rw [pairPolynomial_eq r (hξ 0) (hξ 1) _ hX.1]
    have hp : pairError r (ξ 0) (ξ 1) (X 0-X 1)=
        |pairLocal r (ξ 0) (ξ 1) (X 0-X 1)-(if pairMatch r (ξ 0) (ξ 1) (X 0-X 1) then 2 else 0)| := by
      rw [pairError,ite_eq_left hX.1]
    unfold faceError; linarith
  · subst T
    rw [faceLocal_pair r ξ X 0 2 (by decide)]
    simp [facePolynomial, show (1 : Fin 3)≠0 from by decide, show (1 : Fin 3)≠2 from by decide]
    rw [pairPolynomial_eq r (hξ 0) (hξ 2) _ hX.2.1]
    have hp : pairError r (ξ 0) (ξ 2) (X 0-X 2)=
        |pairLocal r (ξ 0) (ξ 2) (X 0-X 2)-(if pairMatch r (ξ 0) (ξ 2) (X 0-X 2) then 2 else 0)| := by
      rw [pairError,ite_eq_left hX.2.1]
    unfold faceError; linarith
  · subst T
    rw [faceLocal_pair r ξ X 1 2 (by decide)]
    simp [facePolynomial, show (0 : Fin 3)≠1 from by decide, show (0 : Fin 3)≠2 from by decide]
    rw [pairPolynomial_eq r (hξ 1) (hξ 2) _ hX.2.2]
    have hp : pairError r (ξ 1) (ξ 2) (X 1-X 2)=
        |pairLocal r (ξ 1) (ξ 2) (X 1-X 2)-(if pairMatch r (ξ 1) (ξ 2) (X 1-X 2) then 2 else 0)| := by
      rw [pairError,ite_eq_left hX.2.2]
    unfold faceError; linarith
  · subst T
    rw [faceLocal_full,facePolynomial_full r ξ hξ X hX]
    have hp : tripleError r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)=
        |tripleLocal r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)-
          (if tripleMatch r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2) then 8 else 0)| := by
      rw [tripleError,ite_eq_left hfull]
    unfold faceError; linarith
end Face
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section Boolean
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable def boolMonomial (F : Finset I) (η : I → Bool) : ℝ := ∏ i∈F, boolSign (η i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem boolMonomial_empty (η : I → Bool) : boolMonomial ∅ η=1 := by simp [boolMonomial]
theorem bool_factor (a b : Bool) : 1+boolSign a*boolSign b=if a=b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [boolSign]

omit [DecidableEq I] in
theorem bool_indicator_product (η ε : I → Bool) :
    (if η=ε then 1 else 0 : ℝ) = (2^Fintype.card I : ℝ)⁻¹ *
      ∏ i, (1+boolSign (η i)*boolSign (ε i)) := by
  simp_rw [bool_factor]
  by_cases h : η=ε
  · subst ε
    simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    have hp : (∏ i, (if η i=ε i then 2 else 0 : ℝ))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    rw [hp,mul_zero]

omit [DecidableEq I] in
theorem bool_indicator_expansion (η ε : I → Bool) :
    (if η=ε then 1 else 0 : ℝ) = (2^Fintype.card I : ℝ)⁻¹ *
      ∑ F : Finset I, boolMonomial F η * boolMonomial F ε := by
  rw [bool_indicator_product,Finset.prod_one_add]
  simp only [Finset.powerset_univ,Finset.prod_mul_distrib,boolMonomial]

variable {A : Type*} [Fintype A]
omit [DecidableEq I] in
theorem bool_law_expansion (T : A → I → Bool) (ε : I → Bool) :
    uniformMean (fun a => if T a=ε then 1 else 0)=
      (2^Fintype.card I : ℝ)⁻¹ * ∑ F : Finset I,
        (uniformMean fun a => boolMonomial F (T a))*boolMonomial F ε := by
  simp_rw [bool_indicator_expansion]
  rw [uniformMean_mul,uniformMean_sum]
  simp_rw [uniformMean_mul_right]

theorem uniformMean_test_fibers (T : A → I → Bool) (g : (I → Bool) → ℝ) :
    uniformMean (fun a => g (T a))=
      ∑ ε : I → Bool, g ε * uniformMean (fun a => if T a=ε then 1 else 0) := by
  have he (a : A) : g (T a)=∑ ε : I → Bool, g ε*(if T a=ε then 1 else 0) := by simp
  simp_rw [he]
  rw [uniformMean_sum]
  apply Finset.sum_congr rfl
  intro ε _
  rw [uniformMean_mul]
end Boolean
section Convergence
variable {I Q : Type*} [Fintype I] [DecidableEq I] {l : Filter Q}
  {A : Q → Type*} [∀ q, Fintype (A q)] [∀ q, Nonempty (A q)]

theorem boolean_law_tendsto (T : (q : Q) → A q → I → Bool)
    (h : ∀ F : Finset I, F.Nonempty → Tendsto
      (fun q => uniformMean (fun a => boolMonomial F (T q a))) l (nhds 0))
    (ε : I → Bool) : Tendsto
      (fun q => uniformMean (fun a => if T q a=ε then 1 else 0)) l
        (nhds ((Fintype.card (I → Bool) : ℝ)⁻¹)) := by
  have hm (F : Finset I) : Tendsto
      (fun q => (uniformMean fun a => boolMonomial F (T q a))*boolMonomial F ε) l
        (nhds (if F=∅ then (1:ℝ) else 0)) := by
    by_cases hF : F=∅
    · subst F; simp only [boolMonomial_empty,uniformMean_const,mul_one,↓reduceIte]; exact tendsto_const_nhds
    · simpa only [hF,ite_false,zero_mul] using (h F (Finset.nonempty_iff_ne_empty.mpr hF)).mul_const (boolMonomial F ε)
  have hs := (tendsto_finsetSum Finset.univ (fun F _ => hm F)).const_mul ((2^Fintype.card I : ℝ)⁻¹)
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_one] at hs
  simp only [bool_law_expansion,Fintype.card_fun,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat]
  exact hs

theorem boolean_test_tendsto (T : (q : Q) → A q → I → Bool)
    (h : ∀ F : Finset I, F.Nonempty → Tendsto
      (fun q => uniformMean (fun a => boolMonomial F (T q a))) l (nhds 0))
    (g : (I → Bool) → ℝ) : Tendsto
      (fun q => uniformMean (fun a => g (T q a))) l (nhds (uniformMean g)) := by
  have hm (ε : I → Bool) := (boolean_law_tendsto T h ε).const_mul (g ε)
  have hs := tendsto_finsetSum Finset.univ (fun ε _ => hm ε)
  have he (q : Q) : uniformMean (fun a => g (T q a)) =
      ∑ ε : I → Bool, g ε * uniformMean (fun a => if T q a=ε then 1 else 0) :=
    uniformMean_test_fibers (T q) g
  simp only [he]
  convert hs using 1
  simp only [uniformMean,div_eq_mul_inv,Finset.sum_mul]
end Convergence

theorem pairBool_test_tendsto (D : ℕ) (hD : Even D) (hbig : 12≤D) (g : (Fin 33 → Bool) → ℝ) :
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
      g (pairBool X))) primeInfinity (nhds (uniformMean g)) := by
  have hm (F : Finset (Fin 33)) (hF : F.Nonempty) :
      Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
        boolMonomial F (pairBool X))) primeInfinity (nhds 0) := by
    simpa only [boolMonomial] using pairBool_moment_tendsto D hD hbig F hF
  exact boolean_test_tendsto (I := Fin 33) (Q := OddPrime) (l := primeInfinity)
    (A := fun q : OddPrime => Fin 13 → SymMatrix (ZMod q.val) D)
    (fun (q : OddPrime) (X : Fin 13 → SymMatrix (ZMod q.val) D) => pairBool X) hm g
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Means
variable {K I W : Type*} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module K W] [Fintype W]
include K in
theorem uniformMean_two_differences (v : Fin 3 → I) (hv : Function.Injective v) (f : W → W → ℝ) :
    uniformMean (fun X : I → W => f (X (v 0)-X (v 1)) (X (v 0)-X (v 2)))=
      uniformMean (fun B : W => uniformMean (f B)) := by
  let k : Fin 2 → I := fun j => v j.succ
  have hk : Function.Injective k := hv.comp (Fin.succ_injective 2)
  have hn : ∀ j, k j≠v 0 := fun j => hv.ne (Fin.succ_ne_zero j)
  have he := uniformMean_starDifference (K := K) (W := W) (v 0) k hk hn (fun M => f (M 0) (M 1))
  change uniformMean (fun X : I → W => f (X (v 0)-X (v 1)) (X (v 0)-X (v 2))) =
    uniformMean (fun M : Fin 2 → W => f (M 0) (M 1)) at he
  rw [he,←uniformMean_equiv (finTwoArrowEquiv W).symm,uniformMean_prod]
  rfl
end Means
section Bounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def faceBound (r : ℕ) (ξ : Fin 3 → ℤ) : ℝ := 1+
  pairCoefficient (K := K) r (ξ 0) (ξ 1)+pairCoefficient (K := K) r (ξ 0) (ξ 2)+
  pairCoefficient (K := K) r (ξ 1) (ξ 2)+tripleCoefficient (K := K) r (ξ 0) (ξ 1) (ξ 2)

theorem faceBound_one (r : ℕ) (ξ : Fin 3 → ℤ) : 1≤faceBound (K := K) r ξ := by
  have := pairCoefficient_nonneg (K := K) r (ξ 0) (ξ 1)
  have := pairCoefficient_nonneg (K := K) r (ξ 0) (ξ 2)
  have := pairCoefficient_nonneg (K := K) r (ξ 1) (ξ 2)
  have := tripleCoefficient_nonneg (K := K) r (ξ 0) (ξ 1) (ξ 2)
  unfold faceBound; linarith

theorem faceLocal_nonneg (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 3 → SymMatrix K (2*r)) : 0≤faceLocal r T ξ X := by
  exact uniformMean_nonneg fun Y => Finset.prod_nonneg fun k _ => rankKernel_nonneg ..

theorem faceLocal_bound (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
    (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X) :
    faceLocal r T ξ X≤faceBound (K := K) r ξ := by
  have he : X 0-X 2-(X 0-X 1)=X 1-X 2 := by abel
  have n01 := pairCoefficient_nonneg (K := K) r (ξ 0) (ξ 1)
  have n02 := pairCoefficient_nonneg (K := K) r (ξ 0) (ξ 2)
  have n12 := pairCoefficient_nonneg (K := K) r (ξ 1) (ξ 2)
  have nt := tripleCoefficient_nonneg (K := K) r (ξ 0) (ξ 1) (ξ 2)
  rcases fin3_subsets T with ht|ht|ht|ht|ht|ht|ht|ht
  · subst T; rw [faceLocal_empty]; exact faceBound_one r ξ
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; exact faceBound_one r ξ
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; exact faceBound_one r ξ
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; exact faceBound_one r ξ
  · subst T; rw [faceLocal_pair r ξ X 0 1 (by decide)]
    exact (pairLocal_bound r (ξ 0) (ξ 1) _ hX.1).trans (by unfold faceBound; linarith)
  · subst T; rw [faceLocal_pair r ξ X 0 2 (by decide)]
    exact (pairLocal_bound r (ξ 0) (ξ 2) _ hX.2.1).trans (by unfold faceBound; linarith)
  · subst T; rw [faceLocal_pair r ξ X 1 2 (by decide)]
    exact (pairLocal_bound r (ξ 1) (ξ 2) _ hX.2.2).trans (by unfold faceBound; linarith)
  · subst T; rw [faceLocal_full]
    exact (tripleLocal_bound hK r (hξ 0) (hξ 1) (hξ 2) _ _ hX.1 hX.2.1 (by rw [he]; exact hX.2.2)).trans
      (by unfold faceBound; linarith)

theorem pairPolynomial_abs_le (r : ℕ) {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1)
    (B : SymMatrix K (2*r)) : |pairPolynomial r ξ ζ B|≤2 := by
  by_cases hb : B.val.det=0
  · unfold pairPolynomial; rw [hb]; norm_num
  · rw [pairPolynomial_eq r hξ hζ B hb]; split <;> norm_num

theorem facePolynomial_abs_le (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) (X : Fin 3 → SymMatrix K (2*r)) :
    |facePolynomial r T ξ X|≤8 := by
  have hpair (k l : Fin 3) : |if k∈T ∧ l∈T then pairPolynomial r (ξ k) (ξ l) (X k-X l) else 1|≤2 := by
    split
    · exact pairPolynomial_abs_le r (hξ k) (hξ l) _
    · norm_num
  unfold facePolynomial
  rw [abs_mul,abs_mul]
  have ha := mul_le_mul (hpair 0 1) (hpair 0 2) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  have hb := mul_le_mul ha (hpair 1 2) (abs_nonneg _) (by norm_num : (0:ℝ)≤2*2)
  norm_num only at hb
  exact hb
end Bounds

theorem faceBound_tendsto (r : ℕ) (hr : 0<r) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) :
    Tendsto (fun q : OddPrime => faceBound (K := ZMod q.val) r ξ) primeInfinity (nhds 29) := by
  have h01 := pairCoefficient_tendsto r hr (hξ 0) (hξ 1)
  have h02 := pairCoefficient_tendsto r hr (hξ 0) (hξ 2)
  have h12 := pairCoefficient_tendsto r hr (hξ 1) (hξ 2)
  have ht := tripleCoefficient_tendsto r hr (hξ 0) (hξ 1) (hξ 2)
  simpa only [faceBound,show (1:ℝ)+4+4+4+16=29 by norm_num] using
    (((h01.const_add 1).add h02).add h12).add ht

theorem faceError_mean_tendsto (r : ℕ) (hr : 1<r) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
    (v : Fin 3 → Fin 13) (hv : Function.Injective v) :
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) =>
      faceError r ξ (X ∘ v))) primeInfinity (nhds 0) := by
  have he (q : OddPrime) : uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) =>
      faceError r ξ (X ∘ v)) = uniformMean (pairError (K := ZMod q.val) r (ξ 0) (ξ 1))+
        uniformMean (pairError (K := ZMod q.val) r (ξ 0) (ξ 2))+
        uniformMean (pairError (K := ZMod q.val) r (ξ 1) (ξ 2))+
        uniformMean (fun B => uniformMean (fun C => tripleError (K := ZMod q.val) r (ξ 0) (ξ 1) (ξ 2) B C)) := by
    simp only [faceError,Function.comp_def,uniformMean_add]
    rw [uniformMean_point_difference (K := ZMod q.val) _ _ (hv.ne (by decide)) (pairError r (ξ 0) (ξ 1)),
      uniformMean_point_difference (K := ZMod q.val) _ _ (hv.ne (by decide)) (pairError r (ξ 0) (ξ 2)),
      uniformMean_point_difference (K := ZMod q.val) _ _ (hv.ne (by decide)) (pairError r (ξ 1) (ξ 2)),
      uniformMean_two_differences (K := ZMod q.val) v hv (tripleError r (ξ 0) (ξ 1) (ξ 2))]
  simp only [he]
  have h := (((pairError_tendsto r (by omega) (hξ 0) (hξ 1)).add
    (pairError_tendsto r (by omega) (hξ 0) (hξ 2))).add
    (pairError_tendsto r (by omega) (hξ 1) (hξ 2))).add
    (tripleError_tendsto r hr (hξ 0) (hξ 1) (hξ 2))
  simpa only [add_zero] using h
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section ChartFace
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
abbrev CanonicalLag (D : ℕ) := Lagrangian (K := K) (V := Fin D → K)
instance canonicalDual_finite (D : ℕ) : Finite (Module.Dual K (Fin D → K)) :=
  Finite.of_injective (fun f : Module.Dual K (Fin D → K) => (f : (Fin D → K) → K)) DFunLike.coe_injective
noncomputable def canonicalKernel (D r : ℕ) (A Y : CanonicalLag (K := K) D) : ℝ :=
  if finrank K ↥(A.val⊓Y.val)=r then (canonicalStratumMass (K := K) D r)⁻¹ else 0

omit [Fintype K] [DecidableEq K] in
theorem canonicalKernel_nonneg (D r : ℕ) (A Y : CanonicalLag (K := K) D) :
    0≤canonicalKernel D r A Y := by
  unfold canonicalKernel canonicalStratumMass
  split <;> positivity

theorem rankKernel_chart_bound (r : ℕ) (ξ : ℤ) (A Y : SymMatrix K (2*r)) {C : ℝ}
    (hC : 0≤C) (hξ : canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r ξ≤C) :
    rankKernel K (2*r) r ξ (A-Y) ≤ C*canonicalKernel (2*r) r (matrixLagrangian A) (matrixLagrangian Y) := by
  have hm := canonicalStratumMass_pos (K := K) (2*r) r (by omega)
  unfold rankKernel
  split_ifs with hAY
  · have hrank : (A-Y).val.rank=r := (Finset.mem_filter.mp hAY).2.1
    have hdim := matrixLagrangian_pair_rank (2*r) A Y
    have hi : finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian Y).val)=r := by omega
    rw [canonicalKernel,ite_eq_left hi]
    have he : (layerMass K (2*r) r ξ)⁻¹ =
        (canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r ξ) *
          (canonicalStratumMass (K := K) (2*r) r)⁻¹ := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right hξ (inv_nonneg.mpr hm.le)
  · exact mul_nonneg hC (canonicalKernel_nonneg ..)

omit [Fintype K] [DecidableEq K] in
theorem canonicalKernel_prod (D r : ℕ) (L : Fin 3 → CanonicalLag (K := K) D)
    (T : Finset (Fin 3)) (Y : CanonicalLag (K := K) D) :
    (∏ i∈T, canonicalKernel D r (L i) Y)=
      (if ∀ i∈T,finrank K ↥((L i).val⊓Y.val)=r then 1 else 0)*
        ((canonicalStratumMass (K := K) D r)⁻¹)^T.card := by
  by_cases h : ∀ i∈T,finrank K ↥((L i).val⊓Y.val)=r
  · rw [ite_eq_left h,one_mul]
    calc
      _ = ∏ _i∈T, (canonicalStratumMass (K := K) D r)⁻¹ :=
        Finset.prod_congr rfl (fun i hi => by rw [canonicalKernel,ite_eq_left (h i hi)])
      _ = _ := by rw [Finset.prod_const]
  · rw [ite_eq_right h,zero_mul]
    push Not at h
    obtain ⟨i,hi,hh⟩ := h
    exact Finset.prod_eq_zero hi (by rw [canonicalKernel,ite_eq_right hh])

omit [Fintype K] [DecidableEq K] in
theorem canonicalKernel_mean (D r : ℕ) [Fintype (CanonicalLag (K := K) D)]
    (L : Fin 3 → CanonicalLag (K := K) D) (T : Finset (Fin 3)) :
    uniformMean (fun Y => ∏ i∈T, canonicalKernel D r (L i) Y)=
      activeFaceDensity (canonicalSymplectic (K := K) (V := Fin D → K)) r
        (verticalLagrangian (K := K) (V := Fin D → K)) L T := by
  simp_rw [canonicalKernel_prod]
  rw [uniformMean_mul_right,uniformMean_indicator]
  unfold activeFaceDensity canonicalStratumMass
  simp only [inv_div,Nat.card_eq_fintype_card]
  rfl

theorem faceLocal_chart_bound (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 3 → SymMatrix K (2*r)) {C : ℝ} (hC : 1≤C)
    (hξ : ∀ i∈T, canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r (ξ i)≤C) :
    faceLocal r T ξ X ≤ C^3 * lagrangianConstant (2*r) *
      activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
        (verticalLagrangian (K := K) (V := Fin (2*r) → K)) (matrixLagrangian ∘ X) T := by
  let :=  Fintype.ofFinite (CanonicalLag (K := K) (2*r))
  let : Nonempty (CanonicalLag (K := K) (2*r)) := ⟨verticalLagrangian⟩
  let f (Y : CanonicalLag (K := K) (2*r)) := ∏ i∈T, canonicalKernel (2*r) r (matrixLagrangian (X i)) Y
  have hf (Y) : 0≤f Y := Finset.prod_nonneg (fun i _ => canonicalKernel_nonneg ..)
  have hp (Y : SymMatrix K (2*r)) : (∏ i∈T,rankKernel K (2*r) r (ξ i) (X i-Y))≤C^3*f (matrixLagrangian Y) := by
    calc
      _ ≤ ∏ i∈T,C*canonicalKernel (2*r) r (matrixLagrangian (X i)) (matrixLagrangian Y) :=
        Finset.prod_le_prod₀ (fun _ _ => rankKernel_nonneg ..)
          (fun i hi => rankKernel_chart_bound r (ξ i) (X i) Y (by linarith) (hξ i hi))
      _ = C^T.card*f (matrixLagrangian Y) := by rw [Finset.prod_mul_distrib,Finset.prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC (by have := Finset.card_le_univ T; simpa using this)) (hf _)
  have hi := uniformMean_injection (matrixLagrangian (K := K) (D := 2*r))
    (matrixLagrangian_injective (2*r)) f hf
  have he : ((Fintype.card (CanonicalLag (K := K) (2*r)) : ℝ)/Fintype.card (SymMatrix K (2*r)))=
      chartRatio (K := K) (2*r) := by rw [chartRatio,Nat.card_eq_fintype_card]
  rw [he] at hi
  change faceLocal r T ξ X ≤ _
  calc
    _ ≤ C^3*uniformMean (f ∘ matrixLagrangian) := by
      rw [←uniformMean_mul]; exact uniformMean_mono hp
    _ ≤ C^3*(chartRatio (K := K) (2*r)*uniformMean f) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ C^3*(lagrangianConstant (2*r)*uniformMean f) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (chartRatio_bound (2*r)) (uniformMean_nonneg hf)) (by positivity)
    _ = _ := by rw [show uniformMean f=activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
        (verticalLagrangian (K := K) (V := Fin (2*r) → K)) (matrixLagrangian ∘ X) T from canonicalKernel_mean (2*r) r _ T]; ring
end ChartFace
end SidorenkoCounterexample

end

end OAI
