import OAI.Combinatorics.Sidorenko.Charts

namespace OAI


section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
def slotLeft : Fin 3 → Fin 3 := ![0,0,1]
def slotRight : Fin 3 → Fin 3 := ![1,2,2]
theorem facePair_endpoints : ∀ j k,
    pairLeft (facePair j k)=faceVertex j (slotLeft k) ∧
    pairRight (facePair j k)=faceVertex j (slotRight k) := by decide

theorem modelPair_mem (e : Fin 33) : pairVertices e∈modelPointPairs := by
  have h : ∀ e,∃ j,pairVertices e⊆faces j := by decide
  obtain ⟨j,hj⟩ := h e
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_powersetCard.mpr ⟨hj,pairVertices_card e⟩⟩
theorem face_pairs_image : ∀ j, (faces j).powersetCard 2 =
    Finset.univ.image (fun k => pairVertices (facePair j k)) := by decide
theorem modelPair_all (e : Finset (Fin 13)) (he : e∈modelPointPairs) : ∃ k,pairVertices k=e := by
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp he
  rw [face_pairs_image] at hj
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hj
  exact ⟨facePair j k,hk⟩
noncomputable def pairModelEquiv : Fin 33 ≃ ModelPair :=
  Equiv.ofBijective (fun e => ⟨pairVertices e,modelPair_mem e⟩) ⟨
    fun _ _ h => pairVertices_injective (congrArg Subtype.val h),
    fun e => by obtain ⟨k,hk⟩ := modelPair_all e.val e.property; exact ⟨k,Subtype.ext hk⟩⟩

def faceActive (B : Finset (Fin 13 × Fin 22)) (j : Fin 22) : Finset (Fin 3) :=
  Finset.univ.filter fun k => (faceVertex j k,j)∈B
noncomputable def faceSigns (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ)
    (j : Fin 22) (k : Fin 3) : ℤ := if (faceVertex j k,j)∈B then ξ (faceVertex j k,j) else 1

theorem fullTransverse_face {K : Type*} [Field K] {r : ℕ} (X : Fin 13 → SymMatrix K (2*r))
    (hX : fullTransverse X) (j : Fin 22) : faceTransverse r (X ∘ faceVertex j) := by
  have h (k : Fin 3) := hX (facePair j k)
  simp only [(facePair_endpoints j _).1,(facePair_endpoints j _).2] at h
  exact ⟨h 0,h 1,h 2⟩

noncomputable def boolFacePolynomial (c : ℝ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (j : Fin 22) (η : Fin 33 → Bool) : ℝ :=
  ∏ k : Fin 3, if slotLeft k∈T ∧ slotRight k∈T then
    1+c*boolSign (η (facePair j k))*(ξ (slotLeft k) : ℝ)*(ξ (slotRight k) : ℝ) else 1

section FaceGraph
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
theorem pairBool_eq_sign {D : ℕ} (X : Fin 13 → SymMatrix K D) (hX : fullTransverse X) (e : Fin 33) :
    boolSign (pairBool X e)=pairSign X e := by
  have h := pairBool_error X e
  rw [pairSingular,ite_eq_right (hX e)] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

theorem facePolynomial_bool (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X) (j : Fin 22) :
    facePolynomial r T ξ (X ∘ faceVertex j)=
      boolFacePolynomial (quadraticChar K ((-1 : K)^r)) T ξ j (pairBool X) := by
  unfold boolFacePolynomial
  simp_rw [pairBool_eq_sign X hX,pairSign,(facePair_endpoints j _).1,(facePair_endpoints j _).2]
  simp only [Fin.prod_univ_three,slotLeft,slotRight,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,facePolynomial,pairPolynomial,Function.comp_def]
  rfl
end FaceGraph
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Global
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def configurationProduct (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) : ℝ :=
  ∏ j,faceLocal r (T j) (ξ j) (X ∘ faceVertex j)
theorem configurationProduct_nonneg (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) :
    0≤configurationProduct r T ξ X := Finset.prod_nonneg (fun _ _ => faceLocal_nonneg ..)
noncomputable def matrixSingularTail (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  uniformMean fun X : Fin 13 → SymMatrix K (2*r) =>
    if fullTransverse X then 0 else configurationProduct r T ξ X

def canonicalSingular (D : ℕ) (L : Fin 13 → CanonicalLag (K := K) D) : Prop :=
  ∃ e, finrank K ↥((pairVertices e).inf fun i => (L i).val)≠0

omit [Fintype K] [DecidableEq K] in
theorem canonicalSingular_chart (r : ℕ) (X : Fin 13 → SymMatrix K (2*r)) :
    canonicalSingular (2*r) (matrixLagrangian ∘ X) ↔ ¬fullTransverse X := by
  unfold canonicalSingular fullTransverse
  rw [not_forall]
  apply exists_congr
  intro e
  rw [pair_endpoints,Finset.inf_insert,Finset.inf_singleton]
  exact not_congr (matrixLagrangian_pair_zero (2*r) (X (pairLeft e)) (X (pairRight e)))

noncomputable def canonicalConfiguration (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (L : Fin 13 → CanonicalLag (K := K) (2*r)) : ℝ :=
  ∏ j,activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
    (verticalLagrangian (K := K) (V := Fin (2*r) → K)) (L ∘ faceVertex j) (T j)

omit [Fintype K] [DecidableEq K] in
theorem canonicalConfiguration_nonneg (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (L : Fin 13 → CanonicalLag (K := K) (2*r)) : 0≤canonicalConfiguration r T L :=
  Finset.prod_nonneg (fun _ _ => activeFaceDensity_nonneg ..)

theorem configuration_chart_bound (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) {C : ℝ} (hC : 1≤C)
    (hξ : ∀ j i, canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r (ξ j i)≤C) :
    configurationProduct r T ξ X ≤ (C^3*lagrangianConstant (2*r))^22 *
      canonicalConfiguration r T (matrixLagrangian ∘ X) := by
  calc
    _ ≤ ∏ j : Fin 22, (C^3*lagrangianConstant (2*r))*
      activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
        (verticalLagrangian (K := K) (V := Fin (2*r) → K))
          (matrixLagrangian ∘ (X ∘ faceVertex j)) (T j) :=
      Finset.prod_le_prod₀ (fun _ _ => faceLocal_nonneg ..)
        (fun j _ => faceLocal_chart_bound r (T j) (ξ j) _ hC (fun i _ => hξ j i))
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rfl

omit [DecidableEq K] in
theorem actualSingularTail_uniform (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    [Fintype (CanonicalLag (K := K) (2*r))] :
    actualSingularTail (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
      (verticalLagrangian (K := K) (V := Fin (2*r) → K)) T =
      uniformMean (fun L : Fin 13 → CanonicalLag (K := K) (2*r) =>
        if canonicalSingular (2*r) L then canonicalConfiguration r T L else 0) := by
  have hi : Fintype.ofFinite (Fin 13 → CanonicalLag (K := K) (2*r)) =
      (inferInstance : Fintype (Fin 13 → CanonicalLag (K := K) (2*r))) := Subsingleton.elim _ _
  unfold actualSingularTail uniformMean
  rw [hi]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.card_eq_fintype_card]
  congr 1
  apply Finset.sum_congr rfl
  intro L _
  unfold canonicalSingular canonicalConfiguration
  split_ifs <;> rfl

theorem matrixSingularTail_bound (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) {C : ℝ} (hC : 1≤C)
    (hξ : ∀ j i, canonicalStratumMass (K := K) (2*r) r / layerMass K (2*r) r (ξ j i)≤C) :
    matrixSingularTail (K := K) r T ξ ≤
      ((C^3*lagrangianConstant (2*r))^22*lagrangianConstant (2*r)^13)*
        actualSingularTail (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
          (verticalLagrangian (K := K) (V := Fin (2*r) → K)) T := by
  let := Fintype.ofFinite (CanonicalLag (K := K) (2*r))
  let : Nonempty (CanonicalLag (K := K) (2*r)) := ⟨verticalLagrangian⟩
  let f (L : Fin 13 → CanonicalLag (K := K) (2*r)) :=
    if canonicalSingular (2*r) L then canonicalConfiguration r T L else 0
  have hf (L) : 0≤f L := by dsimp only [f]; split <;> simp only [canonicalConfiguration_nonneg,le_refl]
  have hj : Function.Injective (fun X : Fin 13 → SymMatrix K (2*r) => matrixLagrangian ∘ X) := by
    intro X Y h; funext i; exact matrixLagrangian_injective (2*r) (congrFun h i)
  have hi := uniformMean_injection (fun X : Fin 13 → SymMatrix K (2*r) => matrixLagrangian ∘ X) hj f hf
  have he : ((Fintype.card (Fin 13 → CanonicalLag (K := K) (2*r)) : ℝ)/
      Fintype.card (Fin 13 → SymMatrix K (2*r)))=(chartRatio (K := K) (2*r))^13 := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,chartRatio,Nat.card_eq_fintype_card,div_pow]
  rw [he] at hi
  have hp (X : Fin 13 → SymMatrix K (2*r)) :
      (if fullTransverse X then 0 else configurationProduct r T ξ X)≤
        (C^3*lagrangianConstant (2*r))^22*f (matrixLagrangian ∘ X) := by
    dsimp only [f]
    rw [canonicalSingular_chart]
    by_cases hx : fullTransverse X
    · simp only [hx,ite_true,not_true_eq_false,ite_false,mul_zero,le_refl]
    · simp only [hx,ite_false,not_false_eq_true,ite_true]
      exact configuration_chart_bound r T ξ X hC hξ
  have hC0 : 0≤(C^3*lagrangianConstant (2*r))^22 := by positivity
  calc
    _ ≤ (C^3*lagrangianConstant (2*r))^22*uniformMean (fun X => f (matrixLagrangian ∘ X)) := by
      rw [←uniformMean_mul]; exact uniformMean_mono hp
    _ ≤ (C^3*lagrangianConstant (2*r))^22*(chartRatio (K := K) (2*r)^13*uniformMean f) :=
      mul_le_mul_of_nonneg_left hi hC0
    _ ≤ (C^3*lagrangianConstant (2*r))^22*(lagrangianConstant (2*r)^13*uniformMean f) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (chartRatio_nonneg (2*r)) (chartRatio_bound (2*r)) _) (uniformMean_nonneg hf)) hC0
    _ = _ := by rw [actualSingularTail_uniform,mul_assoc]
end Global

theorem canonicalTail_tendsto (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (hlarge : singularTailThreshold≤2*r) : Tendsto
      (fun q : OddPrime => actualSingularTail (canonicalSymplectic (K := ZMod q.val) (V := Fin (2*r) → ZMod q.val)) r
        (verticalLagrangian (K := ZMod q.val) (V := Fin (2*r) → ZMod q.val)) T)
      primeInfinity (nhds 0) := by
  have ht := (integratedTailMajorant_tendsto_zero (2*r) r (fun j => decide (T j=Finset.univ))
    (singularTailThreshold_large.trans hlarge)).comp primeInfinity_real_tendsto
  apply squeeze_zero' (Eventually.of_forall (fun q => actualSingularTail_nonneg _ r _ T)) _ ht
  filter_upwards [primeInfinity_real_tendsto.eventually (eventually_ge_atTop (4*lagrangianConstant (2*r)))] with q hq
  have h2 : (2 : ZMod q.val)≠0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using q.property.2)
  let : Invertible (2 : ZMod q.val) := invertibleOfNonzero h2
  have hD : 2*(2*r)=finrank (ZMod q.val)
      ((Fin (2*r) → ZMod q.val) × Module.Dual (ZMod q.val) (Fin (2*r) → ZMod q.val)) := by
    rw [Module.finrank_prod,Subspace.dual_finrank_eq,Module.finrank_pi,Fintype.card_fin]; omega
  have h := actualSingularTail_bound
    (canonicalSymplectic (K := ZMod q.val) (V := Fin (2*r) → ZMod q.val))
    canonicalSymplectic_nondegenerate (2*r) hD h2 canonicalSymplectic_alt r rfl hlarge
    (by simpa only [ZMod.card] using hq) verticalLagrangian T
  simpa only [Function.comp_def,ZMod.card] using h

theorem matrixSingularTail_tendsto (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i, ξ j i=1 ∨ ξ j i= -1)
    (hlarge : singularTailThreshold≤2*r) : Tendsto
      (fun q : OddPrime => matrixSingularTail (K := ZMod q.val) r T ξ) primeInfinity (nhds 0) := by
  have hr : 0<r := by have := singularTailThreshold_large; omega
  let C : ℝ := 4*2^r
  have hC : 1≤C := by dsimp [C]; have : 1≤(2:ℝ)^r := one_le_pow₀ (by norm_num); linarith
  have he : ∀ᶠ q : OddPrime in primeInfinity, ∀ j i,
      canonicalStratumMass (K := ZMod q.val) (2*r) r / layerMass (ZMod q.val) (2*r) r (ξ j i)≤C := by
    rw [eventually_all]; intro j; rw [eventually_all]; intro i
    exact signed_normalization_eventually r hr (hξ j i)
  have ht := (canonicalTail_tendsto r T hlarge).const_mul
    ((C^3*lagrangianConstant (2*r))^22*lagrangianConstant (2*r)^13)
  simp only [mul_zero] at ht
  have hn (q : OddPrime) : 0 ≤ matrixSingularTail (K := ZMod q.val) r T ξ := by
    unfold matrixSingularTail
    apply uniformMean_nonneg
    intro X
    split
    · rfl
    · exact configurationProduct_nonneg ..
  apply squeeze_zero' (Eventually.of_forall hn) _ ht
  filter_upwards [he] with q hq
  exact matrixSingularTail_bound r T ξ hC hq
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section GlobalProduct
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def configurationPolynomial (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) : ℝ :=
  ∏ j,facePolynomial r (T j) (ξ j) (X ∘ faceVertex j)
noncomputable def globalBound (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  8+∑ j,faceBound (K := K) r (ξ j)

theorem globalBound_eight (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ) : 8≤globalBound (K := K) r ξ := by
  have h := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin 22)))
    (fun j _ => le_trans (by norm_num : (0:ℝ)≤1) (faceBound_one (K := K) r (ξ j)))
  unfold globalBound; linarith

theorem faceBound_le_global (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ) (j : Fin 22) :
    faceBound (K := K) r (ξ j)≤globalBound (K := K) r ξ := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 22)))
    (fun k _ => le_trans (by norm_num : (0:ℝ)≤1) (faceBound_one (K := K) r (ξ k))) (Finset.mem_univ j)
  unfold globalBound; linarith

theorem configuration_difference_bound (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X) :
    |configurationProduct r T ξ X-configurationPolynomial r T ξ X|≤
      globalBound (K := K) r ξ^22*∑ j,faceError r (ξ j) (X ∘ faceVertex j) := by
  have hC := globalBound_eight (K := K) r ξ
  have h := product_difference_bound Finset.univ
    (fun j => faceLocal r (T j) (ξ j) (X ∘ faceVertex j))
    (fun j => facePolynomial r (T j) (ξ j) (X ∘ faceVertex j)) (by linarith : 1≤globalBound (K := K) r ξ)
    (fun j _ => by
      rw [abs_of_nonneg (faceLocal_nonneg ..)]
      exact (faceLocal_bound hK r hr (T j) (ξ j) (hξ j) _ (fullTransverse_face X hX j)).trans (faceBound_le_global r ξ j))
    (fun j _ => (facePolynomial_abs_le r (T j) (ξ j) (hξ j) _).trans hC)
  simp only [Finset.card_univ,Fintype.card_fin] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
    faceLocal_error hK r hr (T j) (ξ j) (hξ j) _ (fullTransverse_face X hX j))) (by positivity))

noncomputable def transverseDifference (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  uniformMean fun X : Fin 13 → SymMatrix K (2*r) =>
    if fullTransverse X then configurationProduct r T ξ X-configurationPolynomial r T ξ X else 0

theorem transverseDifference_bound (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) :
    |transverseDifference (K := K) r T ξ|≤globalBound (K := K) r ξ^22*
      ∑ j,uniformMean (fun X : Fin 13 → SymMatrix K (2*r) => faceError r (ξ j) (X ∘ faceVertex j)) := by
  calc
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K (2*r) =>
      |if fullTransverse X then configurationProduct r T ξ X-configurationPolynomial r T ξ X else 0|) := abs_uniformMean_le _
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K (2*r) =>
        globalBound (K := K) r ξ^22*∑ j,faceError r (ξ j) (X ∘ faceVertex j)) := by
      apply uniformMean_mono; intro X
      split_ifs with hX
      · exact configuration_difference_bound hK r hr T ξ hξ X hX
      · rw [abs_zero]; exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => faceError_nonneg ..))
    _ = _ := by rw [uniformMean_mul,uniformMean_sum]
end GlobalProduct

theorem globalBound_tendsto (r : ℕ) (hr : 0<r) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) : Tendsto
    (fun q : OddPrime => globalBound (K := ZMod q.val) r ξ) primeInfinity (nhds 646) := by
  have hs := (tendsto_finsetSum Finset.univ (fun j _ => faceBound_tendsto r hr (ξ j) (hξ j))).const_add 8
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  exact hs

theorem transverseDifference_tendsto (r : ℕ) (hr : 1<r)
    (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) : Tendsto
    (fun q : OddPrime => transverseDifference (K := ZMod q.val) r T ξ) primeInfinity (nhds 0) := by
  have he := tendsto_finsetSum Finset.univ (fun j _ =>
    faceError_mean_tendsto r hr (ξ j) (hξ j) (faceVertex j) (faceVertex_injective j))
  simp only [Finset.sum_const_zero] at he
  have ht := ((globalBound_tendsto r (by omega) ξ hξ).pow 22).mul he
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (fun q => ?_) ht
  rw [Real.norm_eq_abs]
  exact transverseDifference_bound (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) r (by omega) T ξ hξ
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
noncomputable def boolConfiguration (c : ℝ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (η : Fin 33 → Bool) : ℝ :=
  ∏ j,boolFacePolynomial c (T j) (ξ j) j η

theorem boolFacePolynomial_abs_le (c : ℝ) (hc : |c|≤1) (T : Finset (Fin 3))
    (ξ : Fin 3 → ℤ) (hξ : ∀ i,ξ i=1 ∨ ξ i= -1) (j : Fin 22) (η : Fin 33 → Bool) :
    |boolFacePolynomial c T ξ j η|≤8 := by
  have hs (i) : |(ξ i : ℝ)|=1 := by rcases hξ i with h|h <;> simp [h]
  have h := abs_prod_le_pow Finset.univ
    (fun k : Fin 3 => if slotLeft k∈T ∧ slotRight k∈T then
      1+c*boolSign (η (facePair j k))*(ξ (slotLeft k) : ℝ)*(ξ (slotRight k) : ℝ) else 1)
    (by norm_num : (0:ℝ)≤2) (fun k _ => by
      split_ifs
      · calc
          _ ≤ |(1:ℝ)|+|c*boolSign (η (facePair j k))*(ξ (slotLeft k) : ℝ)*(ξ (slotRight k) : ℝ)| := abs_add_le _ _
          _ ≤ 2 := by simp only [abs_one,abs_mul,boolSign_abs,hs,mul_one]; linarith
      · norm_num)
  norm_num only [Finset.card_univ,Fintype.card_fin,show (2:ℝ)^3=8 by norm_num] at h
  exact h

theorem boolConfiguration_abs_le (c : ℝ) (hc : |c|≤1) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) (η : Fin 33 → Bool) :
    |boolConfiguration c T ξ η|≤8^22 := by
  simpa only [boolConfiguration,Finset.card_univ,Fintype.card_fin] using
    abs_prod_le_pow Finset.univ (fun j => boolFacePolynomial c (T j) (ξ j) j η)
      (by norm_num : (0:ℝ)≤8) (fun j _ => boolFacePolynomial_abs_le c hc (T j) (ξ j) (hξ j) j η)

section GlobalBool
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem configurationPolynomial_bool (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X) :
    configurationPolynomial r T ξ X=
      boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X) := by
  apply Finset.prod_congr rfl
  intro j _
  exact facePolynomial_bool r (T j) (ξ j) X hX j

noncomputable def boolSingular (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  uniformMean fun X : Fin 13 → SymMatrix K (2*r) => if fullTransverse X then 0 else
    boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X)

theorem boolSingular_bound (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) :
    |boolSingular (K := K) r T ξ|≤8^22*(33*((2*r : ℕ):ℝ)/Fintype.card K) := by
  have hc : |(quadraticChar K ((-1:K)^r) : ℝ)|≤1 := by
    rcases quadraticChar_dichotomy (F := K) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero)) with h|h <;> simp [h]
  calc
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K (2*r) =>
      |if fullTransverse X then 0 else boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X)|) := abs_uniformMean_le _
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K (2*r) =>
      8^22*(if fullTransverse X then 0 else 1)) := by
      apply uniformMean_mono; intro X; split_ifs
      · norm_num
      · simpa only [mul_one] using boolConfiguration_abs_le _ hc T ξ hξ (pairBool X)
    _ = 8^22*uniformMean (fun X : Fin 13 → SymMatrix K (2*r) => if fullTransverse X then 0 else 1) := uniformMean_mul _ _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (nonTransverse_mean (K := K) (D := 2*r)) (by positivity : (0:ℝ)≤8^22)
      simpa only [mul_div_assoc] using h

theorem configuration_mean_identity (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) :
    uniformMean (configurationProduct (K := K) r T ξ)-uniformMean
      (fun X : Fin 13 → SymMatrix K (2*r) => boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X)) =
      transverseDifference (K := K) r T ξ+matrixSingularTail (K := K) r T ξ-boolSingular (K := K) r T ξ := by
  rw [←uniformMean_sub]
  unfold transverseDifference matrixSingularTail boolSingular
  rw [←uniformMean_add,←uniformMean_sub]
  apply uniformMean_congr
  intro X
  by_cases hx : fullTransverse X
  · simp only [hx,ite_true,add_zero,sub_zero,configurationPolynomial_bool r T ξ X hx]
  · simp only [hx,ite_false,zero_add]
end GlobalBool

theorem boolSingular_tendsto (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) : Tendsto
    (fun q : OddPrime => boolSingular (K := ZMod q.val) r T ξ) primeInfinity (nhds 0) := by
  have hd : Tendsto (fun q : OddPrime => (33*((2*r : ℕ):ℝ))/(q.val:ℝ)) primeInfinity (nhds 0) :=
    tendsto_const_nhds.div_atTop primeInfinity_real_tendsto
  have ht := hd.const_mul (8^22 : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (fun q => ?_) ht
  rw [Real.norm_eq_abs]
  simpa only [ZMod.card] using boolSingular_bound (K := ZMod q.val) r T ξ hξ

theorem configuration_bool_tendsto (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1)
    (hlarge : singularTailThreshold≤2*r) : Tendsto
    (fun q : OddPrime => uniformMean (configurationProduct (K := ZMod q.val) r T ξ)-uniformMean
      (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) =>
        boolConfiguration (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)) T ξ (pairBool X))) primeInfinity (nhds 0) := by
  have hr : 1<r := by have := singularTailThreshold_large; omega
  simp_rw [configuration_mean_identity]
  simpa only [add_zero,sub_zero] using
    ((transverseDifference_tendsto r hr T ξ hξ).add (matrixSingularTail_tendsto r T ξ hξ hlarge)).sub
      (boolSingular_tendsto r T ξ hξ)
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators

structure FiniteLaw (A : Type*) [Fintype A] where
  weight : A → ℝ
  nonneg : ∀ a,0≤weight a
  total : ∑ a,weight a=1

namespace FiniteLaw
variable {A B C I : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]
noncomputable def mean (p : FiniteLaw A) (f : A → ℝ) : ℝ := ∑ a,p.weight a*f a

theorem mean_congr (p : FiniteLaw A) {f g : A → ℝ} (h : ∀ a,f a=g a) : p.mean f=p.mean g := by
  unfold mean; exact Finset.sum_congr rfl fun a _ => congrArg (p.weight a*·) (h a)
@[simp] theorem mean_const (p : FiniteLaw A) (c : ℝ) : p.mean (fun _ => c)=c := by
  rw [mean,←Finset.sum_mul,p.total,one_mul]
theorem mean_add (p : FiniteLaw A) (f g : A → ℝ) :
    p.mean (fun a => f a+g a)=p.mean f+p.mean g := by simp only [mean,mul_add,Finset.sum_add_distrib]
theorem mean_sub (p : FiniteLaw A) (f g : A → ℝ) :
    p.mean (fun a => f a-g a)=p.mean f-p.mean g := by simp only [mean,mul_sub,Finset.sum_sub_distrib]
theorem mean_mul (p : FiniteLaw A) (c : ℝ) (f : A → ℝ) :
    p.mean (fun a => c*f a)=c*p.mean f := by unfold mean; rw [Finset.mul_sum]; congr 1; funext a; ring
theorem mean_mul_right (p : FiniteLaw A) (f : A → ℝ) (c : ℝ) :
    p.mean (fun a => f a*c)=p.mean f*c := by unfold mean; rw [Finset.sum_mul]; congr 1; funext a; ring
omit [DecidableEq I] in
theorem mean_sum (p : FiniteLaw A) (f : I → A → ℝ) :
    p.mean (fun a => ∑ i,f i a)=∑ i,p.mean (f i) := by unfold mean; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
omit [Fintype I] [DecidableEq I] in
theorem mean_finset_sum (p : FiniteLaw A) (s : Finset I) (f : I → A → ℝ) :
    p.mean (fun a => ∑ i∈s,f i a)=∑ i∈s,p.mean (f i) := by unfold mean; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
theorem mean_nonneg (p : FiniteLaw A) {f : A → ℝ} (hf : ∀ a,0≤f a) : 0≤p.mean f :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (p.nonneg a) (hf a))
theorem mean_mono (p : FiniteLaw A) {f g : A → ℝ} (h : ∀ a,f a≤g a) : p.mean f≤p.mean g :=
  Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a))
theorem mean_bound (p : FiniteLaw A) {f : A → ℝ} {c : ℝ} (h : ∀ a,f a≤c) : p.mean f≤c := by
  simpa only [mean_const] using p.mean_mono h
theorem abs_mean_le (p : FiniteLaw A) (f : A → ℝ) : |p.mean f|≤p.mean (fun a => |f a|) := by
  calc
    _ ≤ ∑ a,|p.weight a*f a| := Finset.abs_sum_le_sum_abs ..
    _ = _ := by simp only [mean,abs_mul,abs_of_nonneg (p.nonneg _)]

noncomputable def dirac (a : A) : FiniteLaw A where
  weight b := if b=a then 1 else 0
  nonneg b := by split <;> norm_num
  total := by simp
@[simp] theorem mean_dirac (a : A) (f : A → ℝ) : (dirac a).mean f=f a := by simp [mean,dirac]

noncomputable def uniform [Nonempty A] : FiniteLaw A where
  weight _ := (Fintype.card A : ℝ)⁻¹
  nonneg _ := by positivity
  total := by simp [nsmul_eq_mul,ne_of_gt (Fintype.card_pos (α := A))]
theorem mean_uniform [Nonempty A] (f : A → ℝ) : uniform.mean f=uniformMean f := by
  simp only [mean,uniform,uniformMean,div_eq_mul_inv,Finset.sum_mul,mul_comm]

noncomputable def prod (p : FiniteLaw A) (q : FiniteLaw B) : FiniteLaw (A × B) where
  weight x := p.weight x.1*q.weight x.2
  nonneg _ := mul_nonneg (p.nonneg _) (q.nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp_rw [←Finset.mul_sum,q.total,mul_one]; exact p.total
@[simp] theorem mean_prod (p : FiniteLaw A) (q : FiniteLaw B) (f : A × B → ℝ) :
    (p.prod q).mean f=p.mean (fun a => q.mean (fun b => f (a,b))) := by
  unfold mean prod; rw [Fintype.sum_prod_type]; simp_rw [Finset.mul_sum,mul_assoc]

theorem mean_swap (p : FiniteLaw A) (q : FiniteLaw B) (f : A → B → ℝ) :
    p.mean (fun a => q.mean (f a))=q.mean (fun b => p.mean (fun a => f a b)) := by
  simp only [mean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro a _; ring

noncomputable def independent (p : I → FiniteLaw A) : FiniteLaw (I → A) where
  weight x := ∏ i,(p i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (p i).nonneg (x i))
  total := by rw [←Fintype.prod_sum]; simp only [(p _).total,Finset.prod_const_one]

theorem independent_mean_product (p : I → FiniteLaw A) (f : I → A → ℝ) :
    (independent p).mean (fun x => ∏ i,f i (x i))=∏ i,(p i).mean (f i) := by
  simp only [mean,independent,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (p i).weight a*f i a)).symm

theorem mean_map_product (p : I → FiniteLaw A) (f : I → A → ℝ) :
    (∏ i,(p i).mean (f i))=∑ x : I → A,∏ i,(p i).weight (x i)*f i (x i) := by
  simp only [mean,Fintype.prod_sum]

noncomputable def mixture (p q : FiniteLaw A) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) : FiniteLaw A where
  weight a := t*p.weight a+(1-t)*q.weight a
  nonneg a := add_nonneg (mul_nonneg ht (p.nonneg a)) (mul_nonneg (by linarith) (q.nonneg a))
  total := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,p.total,q.total]; ring

theorem mean_mixture (p q : FiniteLaw A) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) (f : A → ℝ) :
    (mixture p q t ht ht1).mean f=t*p.mean f+(1-t)*q.mean f := by
  unfold mean mixture; simp only [add_mul,mul_assoc,Finset.sum_add_distrib,Finset.mul_sum]

noncomputable def map (p : FiniteLaw A) (f : A → B) : FiniteLaw B where
  weight b := ∑ a,if f a=b then p.weight a else 0
  nonneg b := Finset.sum_nonneg (fun a _ => by split <;> simp only [p.nonneg,le_refl])
  total := by rw [Finset.sum_comm]; simpa using p.total

theorem mean_map (p : FiniteLaw A) (f : A → B) (g : B → ℝ) :
    (p.map f).mean g=p.mean (g ∘ f) := by
  simp only [mean,map,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  simp

theorem mean_tendsto {Q : Type*} {l : Filter Q} (p : FiniteLaw A) (f : Q → A → ℝ)
    (g : A → ℝ) (h : ∀ a,Filter.Tendsto (fun q => f q a) l (nhds (g a))) :
    Filter.Tendsto (fun q => p.mean (f q)) l (nhds (p.mean g)) := by
  exact tendsto_finsetSum Finset.univ (fun a _ => (h a).const_mul (p.weight a))
end FiniteLaw
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
section BooleanMoments
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem boolMonomial_asprod (s : Finset K) (η : K → Bool) :
    boolMonomial s η=∏ k,if k∈s then boolSign (η k) else 1 := by
  simp [boolMonomial,Finset.prod_ite_mem]

omit [Fintype K] [DecidableEq K] in
theorem boolMonomial_abs (s : Finset K) (η : K → Bool) : |boolMonomial s η|=1 := by
  simp [boolMonomial,Finset.abs_prod]

theorem boolMonomial_mul (s t : Finset K) (η : K → Bool) :
    boolMonomial s η*boolMonomial t η=boolMonomial (s ∆ t) η := by
  simp_rw [boolMonomial_asprod]
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro k _
  by_cases hs : k∈s <;> by_cases ht : k∈t <;>
    simp only [Finset.mem_symmDiff,hs,ht,not_true_eq_false,not_false_eq_true,
      and_self,and_false,false_and,or_self,true_or,or_true,ite_true,ite_false,one_mul,mul_one]
  exact (pow_two (boolSign (η k))).symm.trans (boolSign_sq (η k))

theorem boolSign_mean : uniformMean boolSign=0 := by
  norm_num [uniformMean,Fintype.sum_bool,boolSign]

theorem boolMonomial_mean (s : Finset K) : uniformMean (boolMonomial s)=if s=∅ then 1 else 0 := by
  rw [uniformMean_congr (boolMonomial_asprod s)]
  rw [uniformMean_pi_product (fun k b => if k∈s then boolSign b else 1)]
  by_cases hs : s=∅
  · simp [hs,uniformMean_const]
  · rw [ite_eq_right hs]
    obtain ⟨k,hk⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp only [hk,ite_true,boolSign_mean]

theorem boolMonomial_orthog (s t : Finset K) :
    uniformMean (fun η => boolMonomial s η*boolMonomial t η)=if s=t then 1 else 0 := by
  simp_rw [boolMonomial_mul,boolMonomial_mean,Finset.symmDiff_eq_empty]

noncomputable def tiltLaw (s : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1) : FiniteLaw (K → Bool) where
  weight η := (Fintype.card (K → Bool):ℝ)⁻¹*(1+a*boolMonomial s η)
  nonneg η := by
    apply mul_nonneg (by positivity)
    have hab : |a*boolMonomial s η|≤1 := by simpa only [abs_mul,boolMonomial_abs,mul_one] using ha
    have := neg_abs_le (a*boolMonomial s η); linarith
  total := by
    simp only [←div_eq_inv_mul]
    rw [←Finset.sum_div]
    change uniformMean (fun η : K → Bool => 1+a*boolMonomial s η)=1
    rw [uniformMean_add,uniformMean_const,uniformMean_mul,boolMonomial_mean,ite_eq_right hs]; ring

theorem tiltLaw_mean (s : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1) (f : (K → Bool) → ℝ) :
    (tiltLaw s hs a ha).mean f=uniformMean (fun η => (1+a*boolMonomial s η)*f η) := by
  unfold FiniteLaw.mean tiltLaw uniformMean
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro η _; ring

theorem tiltLaw_monomial (s t : Finset K) (hs : s≠∅) (a : ℝ) (ha : |a|≤1) :
    (tiltLaw s hs a ha).mean (boolMonomial t)=(if t=∅ then 1 else 0)+a*(if t=s then 1 else 0) := by
  rw [tiltLaw_mean]
  simp_rw [add_mul,one_mul,mul_assoc]
  rw [uniformMean_add,uniformMean_mul,boolMonomial_mean,boolMonomial_orthog]
  simp only [eq_comm (a := s) (b := t)]

abbrev Activation (K : Type*) := Finset K × (K → Bool)
noncomputable def activationPhi (α : Finset K) (z : Activation K) : ℝ :=
  if α⊆z.1 then boolMonomial α z.2 else 0

omit [Fintype K] in
@[simp] theorem activationPhi_empty (z : Activation K) : activationPhi ∅ z=1 := by
  simp [activationPhi]

theorem activationPhi_mul (α β : Finset K) (z : Activation K) :
    activationPhi α z*activationPhi β z=
      if α∪β⊆z.1 then boolMonomial (α ∆ β) z.2 else 0 := by
  unfold activationPhi
  simp only [Finset.union_subset_iff]
  by_cases hα : α⊆z.1 <;> by_cases hβ : β⊆z.1 <;> simp [hα,hβ,boolMonomial_mul]

theorem activationPhi_disjoint (α β : Finset K) (h : Disjoint α β) (z : Activation K) :
    activationPhi α z*activationPhi β z=activationPhi (α∪β) z := by
  rw [activationPhi_mul,Finset.symmDiff_eq_union h]
  rfl

noncomputable def branchLaw (S Γ : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1) : FiniteLaw (Activation K) :=
  (FiniteLaw.dirac S).prod (tiltLaw Γ hΓ a ha)

theorem branchLaw_phi (S Γ α : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1) :
    (branchLaw S Γ hΓ a ha).mean (activationPhi α)=
      if α⊆S then (if α=∅ then 1 else 0)+a*(if α=Γ then 1 else 0) else 0 := by
  unfold branchLaw
  rw [FiniteLaw.mean_prod,FiniteLaw.mean_dirac]
  by_cases hα : α⊆S
  · simp only [activationPhi,hα,ite_true]; exact tiltLaw_monomial Γ α hΓ a ha
  · simp only [activationPhi,hα,ite_false,FiniteLaw.mean_const]

theorem branchLaw_second (S Γ α β : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1) :
    (branchLaw S Γ hΓ a ha).mean (fun z => activationPhi α z*activationPhi β z)=
      if α∪β⊆S then (if α=β then 1 else 0)+a*(if α ∆ β=Γ then 1 else 0) else 0 := by
  unfold branchLaw
  rw [FiniteLaw.mean_prod,FiniteLaw.mean_dirac]
  simp_rw [activationPhi_mul]
  by_cases h : α∪β⊆S
  · simp only [h,ite_true]
    rw [tiltLaw_monomial]
    simp only [Finset.symmDiff_eq_empty]
  · simp only [h,ite_false,FiniteLaw.mean_const]

noncomputable def baseActivation (M Γ : Finset K) (hΓ : Γ≠∅) (a : ℝ) (ha : |a|≤1) : FiniteLaw (Activation K) :=
  FiniteLaw.mixture (branchLaw M Γ hΓ a ha) (branchLaw Γ Γ hΓ (-a) (by simpa using ha))
    (1/2) (by norm_num) (by norm_num)

theorem baseActivation_zero (M Γ α : Finset K) (hΓ : Γ≠∅) (hΓM : Γ⊆M)
    (a : ℝ) (ha : |a|≤1) (hα : α≠∅) : (baseActivation M Γ hΓ a ha).mean (activationPhi α)=0 := by
  unfold baseActivation
  rw [FiniteLaw.mean_mixture,branchLaw_phi,branchLaw_phi]
  by_cases h : α=Γ
  · subst α; simp [hΓ,hΓM]; ring
  · simp [h,hα]

noncomputable def activationMoment (p : FiniteLaw (Activation K)) (α β : Finset K) : ℝ :=
  p.mean (fun z => activationPhi α z*activationPhi β z)

@[simp] theorem activationMoment_empty (p : FiniteLaw (Activation K)) : activationMoment p ∅ ∅=1 := by
  simp [activationMoment]

theorem activationMoment_disjoint (p : FiniteLaw (Activation K))
    (hp : ∀ α,α≠∅ → p.mean (activationPhi α)=0) (α β : Finset K)
    (hd : Disjoint α β) (hn : α∪β≠∅) : activationMoment p α β=0 := by
  unfold activationMoment
  simp_rw [activationPhi_disjoint α β hd]
  exact hp _ hn

theorem baseActivation_moment (M Γ α β : Finset K) (hΓ : Γ≠∅)
    (a : ℝ) (ha : |a|≤1) : activationMoment (baseActivation M Γ hΓ a ha) α β=
    (1/2)*(if α∪β⊆M then (if α=β then 1 else 0)+a*(if α ∆ β=Γ then 1 else 0) else 0)+
    (1/2)*(if α∪β⊆Γ then (if α=β then 1 else 0)-a*(if α ∆ β=Γ then 1 else 0) else 0) := by
  unfold activationMoment baseActivation
  rw [FiniteLaw.mean_mixture,branchLaw_second,branchLaw_second]
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num,neg_mul,←sub_eq_add_neg]
end BooleanMoments
end SidorenkoCounterexample

end

end OAI
