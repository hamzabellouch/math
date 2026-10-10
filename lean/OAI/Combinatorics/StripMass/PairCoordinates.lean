import Mathlib
import OAI.Combinatorics.StripMass.SchurIdentity

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
def pairArrayEquiv (α : Type*) (m : ℕ) : (Fin (m*2) → α) ≃ (Fin m → α × α) :=
  ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl α)).trans
    (Equiv.curry (Fin m) (Fin 2) α)).trans
    (Equiv.piCongrRight (fun _ => finTwoArrowEquiv α))

def pairLeft {m : ℕ} (i : Fin m) : Fin (m*2) := finProdFinEquiv (i, 0)
def pairRight {m : ℕ} (i : Fin m) : Fin (m*2) := finProdFinEquiv (i, 1)

@[simp] lemma pairArrayEquiv_apply {α : Type*} {m : ℕ} (v : Fin (m*2) → α) (i : Fin m) :
    pairArrayEquiv α m v i = (v (pairLeft i), v (pairRight i)) := rfl

lemma pair_wedge_product {n m : ℕ} (v : Fin (m*2) → Vec n) :
    (List.ofFn (fun i : Fin m => ExteriorAlgebra.ι ℂ (v (pairLeft i)) *
      ExteriorAlgebra.ι ℂ (v (pairRight i)))).prod = ExteriorAlgebra.ιMulti ℂ (m*2) v := by
  rw [ExteriorAlgebra.ιMulti_apply, List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  congr 2
  funext i
  simp [List.ofFn_succ, pairLeft, pairRight, finProdFinEquiv, mul_comm, add_comm]

lemma twoForm_pow_expansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (m : ℕ) :
    twoForm A ^ m = (1/2:ℂ)^m • ∑ v : Fin (m*2) → Fin n,
      (∏ k : Fin m, A (v (pairLeft k)) (v (pairRight k))) •
        ExteriorAlgebra.ιMulti ℂ (m*2) (standardBasis n ∘ v) := by
  rw [twoForm_full A hA, smul_pow]
  congr 1
  rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n =>
    A p.1 p.2 • (generator n p.1 * generator n p.2)), sum_pow_list]
  simp_rw [ofFn_smul_prod]
  apply Fintype.sum_equiv (pairArrayEquiv (Fin n) m).symm
  intro p
  have hp : pairArrayEquiv (Fin n) m ((pairArrayEquiv (Fin n) m).symm p) = p :=
    Equiv.apply_symm_apply _ p
  conv_lhs => rw [← hp]
  simp only [pairArrayEquiv_apply, generator]
  congr 1
  exact pair_wedge_product (standardBasis n ∘ (pairArrayEquiv (Fin n) m).symm p)

def permInjectiveEquiv (n : ℕ) : Equiv.Perm (Fin n) ≃
    {v : Fin n → Fin n // Function.Injective v} where
  toFun σ := ⟨σ, σ.injective⟩
  invFun v := Equiv.ofBijective v.val (Finite.injective_iff_bijective.mp v.property)
  left_inv σ := by ext i; rfl
  right_inv v := by ext i; rfl

lemma sum_basis_determinant (n : ℕ) (w : (Fin n → Fin n) → ℂ) :
    (∑ v : Fin n → Fin n, w v * (standardBasis n).det (standardBasis n ∘ v)) =
      ∑ σ : Equiv.Perm (Fin n), w σ * (Equiv.Perm.sign σ : ℂ) := by
  classical
  have hz : (∑ v : {f : Fin n → Fin n // ¬Function.Injective f},
      w v.val * (standardBasis n).det (standardBasis n ∘ v.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have hd : (standardBasis n).det (standardBasis n ∘ v.val) = 0 := by
      apply AlternatingMap.map_eq_zero_of_not_injective
      intro hi
      exact v.property (fun a b hab => hi (by simp only [Function.comp_apply, hab]))
    rw [hd, mul_zero]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun v : Fin n → Fin n => Function.Injective v),
    hz, add_zero]
  apply Fintype.sum_equiv (permInjectiveEquiv n).symm
  intro v
  let σ := (permInjectiveEquiv n).symm v
  change w σ * (standardBasis n).det (standardBasis n ∘ σ) = w σ * _
  rw [AlternatingMap.map_perm, Module.Basis.det_self]
  simp [σ, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]

def pairEntries {m : ℕ} (A : Matrix (Fin (m*2)) (Fin (m*2)) ℂ) : ℂ :=
  ∏ i : Fin m, A (pairLeft i) (pairRight i)

 

theorem pfaffian_permutation_expansion (m : ℕ)
    (A : Matrix (Fin (m*2)) (Fin (m*2)) ℂ) (hA : ∀ i j, A j i = -A i j) :
    pfaffian (m*2) A = ((1/2:ℂ)^m / m.factorial) *
      ∑ σ : Equiv.Perm (Fin (m*2)), (Equiv.Perm.sign σ : ℂ) *
        pairEntries (fun i j => A (σ i) (σ j)) := by
  change topCoord (m*2) (twoForm A ^ ((m*2)/2)) / _ = _
  rw [Nat.mul_div_cancel m (by norm_num : 0 < 2), twoForm_pow_expansion A hA,
    map_smul, map_sum]
  simp only [map_smul, topCoord_wedge, smul_eq_mul]
  rw [sum_basis_determinant]
  unfold pairEntries
  simp only [mul_comm (∏ i : Fin m, _) (Equiv.Perm.sign _ : ℂ)]
  ring

end

 

noncomputable section
open scoped BigOperators
open MeasureTheory Set

@[simp] lemma pairArrayEquiv_symm_left {α : Type*} {m : ℕ} (p : Fin m → α × α) (i : Fin m) :
    (pairArrayEquiv α m).symm p (pairLeft i) = (p i).1 := by
  exact congrArg (fun v => (v i).1) ((pairArrayEquiv α m).apply_symm_apply p)

@[simp] lemma pairArrayEquiv_symm_right {α : Type*} {m : ℕ} (p : Fin m → α × α) (i : Fin m) :
    (pairArrayEquiv α m).symm p (pairRight i) = (p i).2 := by
  exact congrArg (fun v => (v i).2) ((pairArrayEquiv α m).apply_symm_apply p)

def pairArrayMeasurableEquiv (α : Type*) [MeasurableSpace α] (m : ℕ) :
    (Fin (m*2) → α) ≃ᵐ (Fin m → α × α) where
  toEquiv := pairArrayEquiv α m
  measurable_toFun := by
    apply Measurable.of_eval
    intro i
    change Measurable (fun v : Fin (m*2) → α => (v (pairLeft i), v (pairRight i)))
    fun_prop
  measurable_invFun := by
    apply Measurable.of_eval
    intro j
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective j
    fin_cases j
    · change Measurable (fun p => (pairArrayEquiv α m).symm p (pairLeft i))
      simp only [pairArrayEquiv_symm_left]
      fun_prop
    · change Measurable (fun p => (pairArrayEquiv α m).symm p (pairRight i))
      simp only [pairArrayEquiv_symm_right]
      fun_prop

lemma pairArray_preimage_pi {α : Type*} {m : ℕ} (s : Fin (m*2) → Set α) :
    (pairArrayEquiv α m).symm ⁻¹' (univ.pi s) =
      univ.pi (fun i : Fin m => s (pairLeft i) ×ˢ s (pairRight i)) := by
  ext p
  simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_prod]
  constructor
  · intro hp i
    exact ⟨by simpa using hp (pairLeft i), by simpa using hp (pairRight i)⟩
  · intro hp j
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective j
    fin_cases j
    · change (pairArrayEquiv α m).symm p (pairLeft i) ∈ s (pairLeft i)
      simpa using (hp i).1
    · change (pairArrayEquiv α m).symm p (pairRight i) ∈ s (pairRight i)
      simpa using (hp i).2

lemma measurePreserving_pairArray {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) :
    MeasurePreserving (pairArrayMeasurableEquiv α m)
      (Measure.pi (fun _ : Fin (m*2) => μ))
        (Measure.pi (fun _ : Fin m => μ.prod μ)) := by
  suffices hs : MeasurePreserving (pairArrayMeasurableEquiv α m).symm
      (Measure.pi (fun _ : Fin m => μ.prod μ))
        (Measure.pi (fun _ : Fin (m*2) => μ)) from hs.symm
  refine ⟨(pairArrayMeasurableEquiv α m).symm.measurable, ?_⟩
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [MeasurableEquiv.map_apply]
  change (Measure.pi (fun _ : Fin m => μ.prod μ))
    ((pairArrayEquiv α m).symm ⁻¹' univ.pi s) = _
  rw [pairArray_preimage_pi, Measure.pi_pi]
  simp only [Measure.prod_prod]
  have h := finProdFinEquiv.prod_comp (fun i : Fin (m*2) => μ (s i))
  simpa only [Fintype.prod_prod_type, Fin.prod_univ_two, pairLeft, pairRight] using h

lemma integral_pair_product {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) (f : Fin m → α × α → ℂ) :
    (∫ x : Fin (m*2) → α, ∏ i : Fin m, f i (x (pairLeft i), x (pairRight i))
      ∂Measure.pi (fun _ => μ)) = ∏ i, ∫ rs, f i rs ∂μ.prod μ := by
  rw [← integral_fintype_prod_eq_prod f (μ := fun _ : Fin m => μ.prod μ)]
  exact (measurePreserving_pairArray μ m).integral_comp' (fun p => ∏ i, f i (p i))

lemma integrable_pair_product {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) {f : Fin m → α × α → ℂ}
    (hf : ∀ i, Integrable (f i) (μ.prod μ)) :
    Integrable (fun x : Fin (m*2) → α => ∏ i : Fin m,
      f i (x (pairLeft i), x (pairRight i))) (Measure.pi (fun _ => μ)) := by
  exact (measurePreserving_pairArray μ m).integrable_comp_of_integrable
    (Integrable.fintype_prod hf)

lemma prod_pairs {M : Type*} [CommMonoid M] {m : ℕ} (f : Fin (m*2) → M) :
    (∏ i : Fin m, f (pairLeft i) * f (pairRight i)) = ∏ i, f i := by
  simpa only [Fintype.prod_prod_type, Fin.prod_univ_two, pairLeft, pairRight] using
    finProdFinEquiv.prod_comp f

lemma piCongrLeft_const_apply {α : Type*} [MeasurableSpace α] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => α) σ) x = x ∘ σ.symm := by
  ext i
  obtain ⟨j, rfl⟩ := σ.surjective i
  simp [MeasurableEquiv.coe_piCongrLeft]

lemma integral_alternating_times_perm {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {n : ℕ} (F G : (Fin n → α) → ℂ)
    (hF : ∀ σ : Equiv.Perm (Fin n), ∀ x, F (x ∘ σ) = (Equiv.Perm.sign σ : ℂ) * F x)
    (σ : Equiv.Perm (Fin n)) :
    (∫ x, F x * G (x ∘ σ) ∂Measure.pi (fun _ => μ)) =
      (Equiv.Perm.sign σ : ℂ) * ∫ x, F x * G x ∂Measure.pi (fun _ => μ) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin n => μ) σ).integral_comp'
    (fun x => F x * G (x ∘ σ))
  simp only [piCongrLeft_const_apply] at h
  change (∫ x, F (x ∘ σ.symm) * G ((x ∘ σ.symm) ∘ σ) ∂Measure.pi (fun _ => μ)) = _ at h
  have hc (x : Fin n → α) : (x ∘ σ.symm) ∘ σ = x := by ext i; simp
  simp only [hc, hF, Equiv.Perm.sign_symm, mul_assoc, integral_const_mul] at h
  exact h.symm

lemma integrable_alternating_times_perm {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {n : ℕ} (F G : (Fin n → α) → ℂ)
    (hF : ∀ σ : Equiv.Perm (Fin n), ∀ x, F (x ∘ σ) = (Equiv.Perm.sign σ : ℂ) * F x)
    (hi : Integrable (fun x => F x * G x) (Measure.pi (fun _ => μ)))
    (σ : Equiv.Perm (Fin n)) :
    Integrable (fun x => F x * G (x ∘ σ)) (Measure.pi (fun _ => μ)) := by
  apply ((measurePreserving_piCongrLeft (fun _ : Fin n => μ) σ).integrable_comp_emb
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => α) σ).measurableEmbedding).mp
  have hc (x : Fin n → α) : (x ∘ σ.symm) ∘ σ = x := by ext i; simp
  simp only [Function.comp_def, piCongrLeft_const_apply]
  change Integrable (fun x => F (x ∘ σ.symm) * G ((x ∘ σ.symm) ∘ σ)) _
  simp only [hc, hF, mul_assoc]
  exact hi.const_mul _

def evaluationMatrix {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ) (x : Fin n → α) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => φ i (x j)

def doubleIntegrand {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ) (k : α → α → ℂ)
    (i j : Fin n) (rs : α × α) : ℂ := φ i rs.1 * k rs.1 rs.2 * φ j rs.2

def doubleMomentMatrix {α : Type*} [MeasurableSpace α] {n : ℕ} (μ : Measure α)
    (φ : Fin n → α → ℂ) (k : α → α → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∫ rs, doubleIntegrand φ k i j rs ∂μ.prod μ

lemma doubleMomentMatrix_skew {α : Type*} [MeasurableSpace α] {n : ℕ} (μ : Measure α)
    [SigmaFinite μ] (φ : Fin n → α → ℂ) (k : α → α → ℂ)
    (hk : ∀ r s, k s r = -k r s) (i j : Fin n) :
    doubleMomentMatrix μ φ k j i = -doubleMomentMatrix μ φ k i j := by
  unfold doubleMomentMatrix
  rw [← integral_prod_swap (doubleIntegrand φ k j i), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with rs
  simp only [doubleIntegrand, Prod.fst_swap, Prod.snd_swap]
  rw [hk rs.1 rs.2]
  ring

lemma evaluationMatrix_det_perm {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (evaluationMatrix φ (x ∘ σ)).det = (Equiv.Perm.sign σ : ℂ) * (evaluationMatrix φ x).det := by
  exact Matrix.det_permute' σ (evaluationMatrix φ x)

lemma product_doubleIntegrand {α : Type*} {m : ℕ} (φ : Fin (m*2) → α → ℂ)
    (k : α → α → ℂ) (σ : Equiv.Perm (Fin (m*2))) (x : Fin (m*2) → α) :
    (∏ i : Fin m, doubleIntegrand φ k (σ (pairLeft i)) (σ (pairRight i))
      (x (pairLeft i), x (pairRight i))) =
      (∏ i : Fin (m*2), φ (σ i) (x i)) * pairEntries (fun i j => k (x i) (x j)) := by
  unfold doubleIntegrand pairEntries
  rw [← prod_pairs (fun i => φ (σ i) (x i))]
  simp only [Finset.prod_mul_distrib]
  ring

lemma determinant_times_pairs {α : Type*} {m : ℕ} (φ : Fin (m*2) → α → ℂ)
    (k : α → α → ℂ) (x : Fin (m*2) → α) :
    (evaluationMatrix φ x).det * pairEntries (fun i j => k (x i) (x j)) =
      ∑ σ : Equiv.Perm (Fin (m*2)), (Equiv.Perm.sign σ : ℂ) *
        ∏ i : Fin m, doubleIntegrand φ k (σ (pairLeft i)) (σ (pairRight i))
          (x (pairLeft i), x (pairRight i)) := by
  rw [Matrix.det_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [product_doubleIntegrand]
  simp only [evaluationMatrix, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  ring

lemma integrable_determinant_times_pairs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {m : ℕ} (φ : Fin (m*2) → α → ℂ) (k : α → α → ℂ)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ)) :
    Integrable (fun x => (evaluationMatrix φ x).det * pairEntries (fun i j => k (x i) (x j)))
      (Measure.pi (fun _ => μ)) := by
  simp only [determinant_times_pairs]
  exact integrable_finsetSum _ (fun σ _ => (integrable_pair_product μ m (fun i => hi _ _)).const_mul _)

lemma integral_determinant_times_pairs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {m : ℕ} (φ : Fin (m*2) → α → ℂ) (k : α → α → ℂ)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ)) :
    (∫ x, (evaluationMatrix φ x).det * pairEntries (fun i j => k (x i) (x j))
      ∂Measure.pi (fun _ => μ)) =
      ∑ σ : Equiv.Perm (Fin (m*2)), (Equiv.Perm.sign σ : ℂ) *
        pairEntries (fun i j => doubleMomentMatrix μ φ k (σ i) (σ j)) := by
  simp only [determinant_times_pairs]
  rw [integral_finsetSum _ (fun σ _ => (integrable_pair_product μ m (fun i => hi _ _)).const_mul _)]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [integral_const_mul, integral_pair_product]
  rfl

 

theorem deBruijn_even {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) (φ : Fin (m*2) → α → ℂ) (k : α → α → ℂ)
    (hk : ∀ r s, k s r = -k r s)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ)) :
    (∫ x, (evaluationMatrix φ x).det * pfaffian (m*2) (fun i j => k (x i) (x j))
      ∂Measure.pi (fun _ => μ)) =
        (Nat.factorial (m*2) : ℂ) * pfaffian (m*2) (doubleMomentMatrix μ φ k) := by
  let F : (Fin (m*2) → α) → ℂ := fun x => (evaluationMatrix φ x).det
  let G : (Fin (m*2) → α) → ℂ := fun x => pairEntries (fun i j => k (x i) (x j))
  have hF (σ : Equiv.Perm (Fin (m*2))) (x : Fin (m*2) → α) :
      F (x ∘ σ) = (Equiv.Perm.sign σ : ℂ) * F x := evaluationMatrix_det_perm φ σ x
  have hI := integrable_determinant_times_pairs μ φ k hi
  have hII (σ : Equiv.Perm (Fin (m*2))) :
      Integrable (fun x => F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)))
        (Measure.pi (fun _ => μ)) := by
    have h := (integrable_alternating_times_perm μ F G hF hI σ).const_mul (Equiv.Perm.sign σ : ℂ)
    convert h using 1
    ext x
    ring
  have hpoint (x : Fin (m*2) → α) :
      F x * pfaffian (m*2) (fun i j => k (x i) (x j)) =
        ((1/2:ℂ)^m / m.factorial) *
          ∑ σ : Equiv.Perm (Fin (m*2)), F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)) := by
    rw [pfaffian_permutation_expansion m _ (fun i j => hk _ _)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [F, G, Function.comp_def]
    ring
  change (∫ x, F x * pfaffian (m*2) _ ∂Measure.pi (fun _ => μ)) = _
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finsetSum _ (fun σ _ => hII σ)]
  have he (σ : Equiv.Perm (Fin (m*2))) :
      (∫ x, F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)) ∂Measure.pi (fun _ => μ)) =
        ∫ x, F x * G x ∂Measure.pi (fun _ => μ) := by
    calc
      _ = (Equiv.Perm.sign σ : ℂ) * ∫ x, F x * G (x ∘ σ) ∂Measure.pi (fun _ => μ) := by
        rw [← integral_const_mul]
        congr 1
        ext x
        ring
      _ = _ := by
        rw [integral_alternating_times_perm μ F G hF, ← mul_assoc]
        have hs : (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ) = 1 := by
          have hs : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 :=
            congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign σ))
          exact_mod_cast hs
        rw [hs, one_mul]
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    pfaffian_permutation_expansion m _ (doubleMomentMatrix_skew μ φ k hk),
    ← integral_determinant_times_pairs μ φ k hi]
  dsimp [F,G]
  ring


 


lemma borderLinear_eq_topCoord {n : ℕ} (hn : Odd n)
    (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) :
    borderLinear A u = topCoord n (twoForm A ^ (n/2) * ExteriorAlgebra.ι ℂ u) / (n/2).factorial := by
  have hn' : 2*(n/2)+1 = n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hhom : twoForm A ^ (n/2) * ExteriorAlgebra.ι ℂ u ∈
      ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hn'] using SetLike.mul_mem_graded (twoForm_pow_mem A (n/2))
      (show ExteriorAlgebra.ι ℂ u ∈ ExteriorAlgebra.exteriorPower ℂ 1 (Vec n) from by
        simpa only [ExteriorAlgebra.exteriorPower, pow_one] using
          (LinearMap.mem_range_self (ExteriorAlgebra.ι ℂ) u))
  change topCoord (n+1) (ExteriorAlgebra.map (embedMap n) (twoForm A) ^ (n/2) *
    (ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n+1) (Fin.last n))) / _ = _
  rw [← mul_assoc, ← ExteriorAlgebra.map_apply_ι, ← map_pow, ← map_mul,
    topCoord_embed_mul_last _ hhom]

def oddPairEntries {m : ℕ} (A : Matrix (Fin (m*2+1)) (Fin (m*2+1)) ℂ)
    (u : Fin (m*2+1) → ℂ) : ℂ :=
  (∏ k : Fin m, A (pairLeft k).castSucc (pairRight k).castSucc) * u (Fin.last (m*2))

lemma wedge_snoc {n l : ℕ} (v : Fin l → Vec n) (u : Vec n) :
    ExteriorAlgebra.ιMulti ℂ l v * ExteriorAlgebra.ι ℂ u =
      ExteriorAlgebra.ιMulti ℂ (l+1) (Fin.snoc v u) := by
  simp only [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ', List.prod_concat,
    Fin.snoc_castSucc, Fin.snoc_last]

lemma twoForm_pow_mul_expansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) (m : ℕ) :
    twoForm A ^ m * ExteriorAlgebra.ι ℂ u =
      (1/2:ℂ)^m • ∑ v : Fin (m*2+1) → Fin n,
      ((∏ k : Fin m, A (v (pairLeft k).castSucc) (v (pairRight k).castSucc)) *
         u (v (Fin.last (m*2)))) •
        ExteriorAlgebra.ιMulti ℂ (m*2+1) (standardBasis n ∘ v) := by
  rw [twoForm_pow_expansion A hA m, ← generator_expansion n u, smul_mul_assoc,
    Finset.sum_mul]
  simp_rw [Finset.mul_sum, smul_mul_smul_comm, generator, wedge_snoc]
  congr 1
  rw [← Fintype.sum_prod_type (f := fun p : (Fin (m*2) → Fin n) × Fin n =>
    ((∏ k : Fin m, A (p.1 (pairLeft k)) (p.1 (pairRight k)))*u p.2) •
      ExteriorAlgebra.ιMulti ℂ (m*2+1) (Fin.snoc (standardBasis n ∘ p.1) (standardBasis n p.2)))]
  apply Fintype.sum_equiv ((Equiv.prodComm _ _).trans
    (Fin.snocEquiv (fun _ : Fin (m*2+1) => Fin n)))
  intro p
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last]
  congr 1
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Function.comp_def]

 
theorem pfaffian_border_permutation_expansion (m : ℕ)
    (A : Matrix (Fin (m*2+1)) (Fin (m*2+1)) ℂ) (hA : ∀ i j, A j i = -A i j)
    (u : Fin (m*2+1) → ℂ) :
    pfaffian (m*2+2) (border A u) = ((1/2:ℂ)^m / m.factorial) *
      ∑ σ : Equiv.Perm (Fin (m*2+1)), (Equiv.Perm.sign σ : ℂ) *
        oddPairEntries (fun i j => A (σ i) (σ j)) (u ∘ σ) := by
  have hn : Odd (m*2+1) := ⟨m, by omega⟩
  rw [pfaffian_border hn A hA u, borderLinear_eq_topCoord hn,
    show (m*2+1)/2=m by omega, twoForm_pow_mul_expansion A hA u m,
    map_smul, map_sum]
  simp only [map_smul, topCoord_wedge, smul_eq_mul]
  rw [sum_basis_determinant]
  unfold oddPairEntries
  simp only [Function.comp_apply, mul_comm ((∏ i : Fin m, _) * _) (Equiv.Perm.sign _ : ℂ)]
  ring

end
end StripPfaffian

end OAI
