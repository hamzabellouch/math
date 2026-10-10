import OAI.GroupTheory.Kervaire.PhaseDimension

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder

namespace KervaireMixing

section
open Matrix KervaireMatrix KervaireRegular
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

/-- A slot is a disk number, a disk kind, and a position in the cyclic word. -/
abbrev Slot (I K : Type*) := (K ⊕ K) × I

/-- The opposite cyclic orders on positive and negative word disks. -/
def successor (ρ : Equiv.Perm I) : Equiv.Perm (Slot I K) where
  toFun p := match p with
    | (Sum.inl k, i) => (Sum.inl k, ρ i)
    | (Sum.inr k, i) => (Sum.inr k, ρ.symm i)
  invFun p := match p with
    | (Sum.inl k, i) => (Sum.inl k, ρ.symm i)
    | (Sum.inr k, i) => (Sum.inr k, ρ i)
  left_inv p := by rcases p with ⟨k|k,i⟩ <;> simp
  right_inv p := by rcases p with ⟨k|k,i⟩ <;> simp

/-- Coefficient inverses for the signed incidence operator. -/
def labels (ρ : Equiv.Perm I) (a : I → A) : Slot I K → A
  | (Sum.inl _, i) => (a i)⁻¹
  | (Sum.inr _, i) => a (ρ.symm i)

/-- The scalar mixing involution; no group coefficients occur in it. -/
def mixingMatrix (X : Matrix K K ℂ) : Matrix (Slot I K) (Slot I K) ℂ :=
  blockDiagonal fun _ : I => fromBlocks 0 Xᴴ X 0

omit [Fintype I] [Fintype K] in
@[simp] theorem mixingMatrix_star (X : Matrix K K ℂ) :
    star (mixingMatrix (I := I) X) = mixingMatrix X := by
  ext ⟨k,i⟩ ⟨l,j⟩
  rcases k with k | k <;> rcases l with l | l <;>
    by_cases h : i = j <;> simp [mixingMatrix, Matrix.star_apply, blockDiagonal_apply, fromBlocks, eq_comm, h]

@[simp] theorem mixingMatrix_sq (X : Matrix.unitaryGroup K ℂ) :
    mixingMatrix (I := I) (X : Matrix K K ℂ) * mixingMatrix (X : Matrix K K ℂ) = 1 := by
  simp only [mixingMatrix, ← blockDiagonal_mul, fromBlocks_multiply,
    zero_mul, mul_zero, add_zero, zero_add]
  rw [show (X : Matrix K K ℂ)ᴴ * (X : Matrix K K ℂ) = 1 from X.2.1,
    show (X : Matrix K K ℂ) * (X : Matrix K K ℂ)ᴴ = 1 from X.2.2]
  convert (blockDiagonal_one (m := K ⊕ K) (o := I) (α := ℂ)) using 1
  ext ⟨p,i⟩ ⟨q,j⟩
  simp [blockDiagonal_apply, fromBlocks_one, Matrix.one_apply]

theorem mixingMatrix_unitary (X : Matrix.unitaryGroup K ℂ) :
    mixingMatrix (I := I) (X : Matrix K K ℂ) ∈ Matrix.unitaryGroup (Slot I K) ℂ := by
  rw [Unitary.mem_iff, mixingMatrix_star, mixingMatrix_sq]
  exact ⟨rfl,rfl⟩

/-- The coefficient shift S and scalar mixer J in the actual regular Hilbert space. -/
def S (ρ : Equiv.Perm I) (a : I → A) : Operator (Slot I K) A :=
  labelledShift (successor ρ) (labels ρ a)
def J (X : Matrix K K ℂ) : Operator (Slot I K) A := scalarTensor (mixingMatrix X)

omit [Fintype I] [Fintype K] in
theorem S_unitary (ρ : Equiv.Perm I) (a : I → A) :
    S (K := K) ρ a ∈ unitary (Operator (Slot I K) A) := labelledShift_unitary _ _
omit [Group A] in
theorem J_sq (X : Matrix.unitaryGroup K ℂ) :
    J (I := I) (A := A) (X : Matrix K K ℂ) * J (X : Matrix K K ℂ) = 1 := by
  rw [J, ← scalarTensor_mul, mixingMatrix_sq]
  ext f ⟨d,a⟩
  simp [Matrix.one_apply]

omit [Group A] in
theorem J_star (X : Matrix K K ℂ) :
    star (J (I := I) (A := A) X) = J X := by
  rw [J, scalarTensor_star, mixingMatrix_star]

omit [Group A] in
theorem J_unitary (X : Matrix.unitaryGroup K ℂ) :
    J (I := I) (A := A) (X : Matrix K K ℂ) ∈ unitary (Operator (Slot I K) A) := by
  rw [Unitary.mem_iff, J_star, J_sq]
  exact ⟨rfl,rfl⟩

omit [Fintype I] [Fintype K] in
theorem S_commutant (ρ : Equiv.Perm I) (a : I → A) : InCommutant (S (K := K) ρ a) :=
  labelledShift_mem_commutant _ _
theorem J_commutant (X : Matrix K K ℂ) : InCommutant (J (I := I) (A := A) X) :=
  scalarTensor_mem_commutant _

omit [Group A] in
@[simp] theorem scalarTensor_delta (M : Matrix (Slot I K) (Slot I K) ℂ)
    (p q : Slot I K) (x y : A) :
    scalarTensor M (delta (p,x)) (q,y) = if x = y then M q p else 0 := by
  simp [scalarTensor_apply, delta, Pi.single_apply, Prod.mk.injEq, ite_and,
    mul_ite, eq_comm]

/-- The mixed shift exchanges disk kinds, so its unnormalized trace is zero. -/
theorem trace_SJ (ρ : Equiv.Perm I) (a : I → A) (X : Matrix K K ℂ) :
    KervaireMatrix.trace (S ρ a * J (I := I) X) = 0 := by
  rw [KervaireMatrix.trace_apply]
  simp only [inner_delta_left]
  apply Finset.sum_eq_zero
  rintro ⟨k|k,i⟩ _ <;>
    simp only [S, J, mul_apply_eq_comp, labelledShift_apply, scalarTensor_delta]
    <;> simp [successor, mixingMatrix, blockDiagonal_apply, fromBlocks]

/-- The exact corner reversal makes SJ self-adjoint for every mixer X. -/
theorem star_SJ (ρ : Equiv.Perm I) (a : I → A) (X : Matrix K K ℂ) :
    star (S ρ a * J (I := I) X) = S ρ a * J (I := I) X := by
  apply star_eq_of_coefficients
  rintro ⟨⟨k|k,i⟩,x⟩ ⟨⟨l|l,j⟩,y⟩ <;>
    simp only [S, J, mul_apply_eq_comp, labelledShift_apply, scalarTensor_delta]
    <;> simp [labels, successor, mixingMatrix, blockDiagonal_apply, fromBlocks]
  · by_cases h : ρ j = i
    · subst i
      simp only [Equiv.symm_apply_apply, ↓reduceIte, eq_inv_mul_iff_mul_eq]
      split_ifs <;> simp_all
    · have h' : ρ.symm i ≠ j := by intro hh; apply h; rw [← hh, ρ.apply_symm_apply]
      simp [h,h']
  · by_cases h : ρ i = j
    · subst j
      simp only [Equiv.symm_apply_apply, ↓reduceIte, eq_inv_mul_iff_mul_eq]
      split_ifs <;> simp_all
    · have h' : ρ.symm j ≠ i := by intro hh; apply h; rw [← hh, ρ.apply_symm_apply]
      simp [h,h']

end
open Matrix KervaireMatrix KervaireRegular KervaireSpectral
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

/-- The exact phase identity at arbitrary group coefficients. -/
theorem phase_SJ [Nonempty I] [Nonempty K]
    (ρ : Equiv.Perm I) (a : I → A) (X : Matrix.unitaryGroup K ℂ) :
    let _ := isStarNormal_of_mem_unitary
      ((unitary _).mul_mem (S_unitary (K := K) ρ a) (J_unitary (I := I) X))
    KervaireMatrix.phase (S ρ a * J (I := I) (X : Matrix K K ℂ)) =
      (Fintype.card I : ℝ) * Fintype.card K / 2 := by
  have hU := (unitary _).mul_mem (S_unitary (K := K) ρ a) (J_unitary (I := I) X)
  let _ := isStarNormal_of_mem_unitary hU
  have hsq : (S ρ a * J (I := I) (X : Matrix K K ℂ)) ^ 2 = 1 := by
    simpa only [pow_two, star_SJ] using hU.1
  rw [KervaireMatrix.phase, sumPhase_involution _ hU hsq,
    ← trace_eq_vectorSum, KervaireMatrix.trace_one, trace_SJ]
  simp only [Complex.zero_re, sub_zero,
    Slot, Fintype.card_prod, Fintype.card_sum, Nat.cast_mul, Nat.cast_add]
  simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero]
  ring

end KervaireMixing
namespace KervaireCycle
variable {D E B : Type*} [Monoid B]
lemma perm_pow_embedding (σ : Equiv.Perm D) (τ : Equiv.Perm E) (e : E → D)
    (he : ∀ i, σ (e i) = e (τ i)) (n : ℕ) (i : E) :
    (σ^n) (e i) = e ((τ^n) i) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Equiv.Perm.mul_apply,ih,he]
lemma orbitWeight_embedding (σ : Equiv.Perm D) (τ : Equiv.Perm E) (e : E → D)
    (he : ∀ i, σ (e i) = e (τ i)) (b : D → B) (n : ℕ) (i : E) :
    orbitWeight σ b n (e i) = orbitWeight τ (b ∘ e) n i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [orbitWeight_succ,orbitWeight_succ,perm_pow_embedding σ τ e he,ih]; rfl
end KervaireCycle
namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireTraceCalculus KervaireCycle
open scoped Classical
variable {D E A : Type*} [Fintype D] [Fintype E] [Group A]
omit [Fintype E] in
lemma weightedShift_moment (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A) (n : ℕ) (i : D) :
    inner ℂ (delta (i,(1 : A))) ((weightedShift σ u a ^ n) (delta (i,1))) =
      if (σ^n) i = i ∧ orbitWeight σ a n i = 1 then orbitWeight σ u n i else 0 := by
  rw [weightedShift_pow,weightedShift_delta,inner_smul_right,inner_delta_left]
  simp [delta,Pi.single_apply,Prod.mk.injEq,eq_comm]

lemma vectorPhase_cycle_embedding (σ : Equiv.Perm D) (τ : Equiv.Perm E)
    (e : E ↪ D) (he : ∀ i, σ (e i) = e (τ i))
    (u : D → ℂ) (a : D → A) (hu : ∀ i, u i ∈ unitary ℂ) (i : E) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary σ u a hu)
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary τ (u ∘ e) (a ∘ e) (fun j ↦ hu (e j)))
    vectorPhase (weightedShift σ u a) (delta (e i,(1 : A))) =
      vectorPhase (weightedShift τ (u ∘ e) (a ∘ e)) (delta (i,(1 : A))) := by
  apply vectorPhase_eq_of_moments _ _ (weightedShift_unitary σ u a hu)
    (weightedShift_unitary τ (u ∘ e) (a ∘ e) (fun j ↦ hu (e j))) _ _
  intro n
  rw [weightedShift_moment,weightedShift_moment,perm_pow_embedding σ τ e he,
    orbitWeight_embedding σ τ e he,orbitWeight_embedding σ τ e he]
  simp only [EmbeddingLike.apply_eq_iff_eq]

/-- Exact cyclewise decomposition of boundary phase; all circuit words are in A. -/
lemma phase_cycles {Z : Type*} [Fintype Z] (n : Z → ℕ)
    (e : (Σ z, Fin (n z+1)) ≃ D) (σ : Equiv.Perm D)
    (he : ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (u : D → ℂ) (a : D → A) (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary σ u a hu)
    KervaireMatrix.phase (weightedShift σ u a) =
      ∑ z, ((n z : ℝ)/2 + groupPhase
        (orbitWeight (finRotate (n z+1)) (fun i ↦ u (e ⟨z,i⟩)) (n z+1) 0)
        (orbitWeight_mem (unitary ℂ) _ _ (fun i ↦ hu (e ⟨z,i⟩)) _ _)
        (orbitWeight (finRotate (n z+1)) (fun i ↦ a (e ⟨z,i⟩)) (n z+1) 0)) := by
  let _ := isStarNormal_of_mem_unitary (weightedShift_unitary σ u a hu)
  change (∑ i : D, vectorPhase (weightedShift σ u a) (delta (i,(1 : A)))) = _
  rw [← e.sum_comp,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  let ez : Fin (n z+1) ↪ D := ⟨fun i ↦ e ⟨z,i⟩, fun i j h ↦ by
    exact eq_of_heq (Sigma.mk.inj_iff.mp (e.injective h)).2⟩
  have hz (i : Fin (n z+1)) := vectorPhase_cycle_embedding σ (finRotate (n z+1)) ez
    (he z) u a hu i
  let _ := isStarNormal_of_mem_unitary
    (weightedShift_unitary (finRotate (n z+1)) (u ∘ ez) (a ∘ ez) (fun i ↦ hu (ez i)))
  trans KervaireMatrix.phase (weightedShift (finRotate (n z+1)) (u ∘ ez) (a ∘ ez))
  · apply Finset.sum_congr rfl
    intro i _
    exact hz i
  · exact phase_weightedCycle (n z) (u ∘ ez) (a ∘ ez) (fun i ↦ hu (ez i))
end KervaireMatrix

namespace KervaireRegular
open KervaireSpectral KervaireTraceCalculus MeasureTheory
variable {A : Type*} [Group A]

lemma groupPhase_one (z : ℂ) (hz : z ∈ unitary ℂ) :
    groupPhase z hz (1 : A) = KervaireSpectral.phase z := by
  let _ : Nontrivial ℓ²(A, ℂ) := by
    classical
    refine ⟨⟨delta (1 : A), 0, ?_⟩⟩
    intro h
    have hh := congrArg (fun f : ℓ²(A, ℂ) => f 1) h
    simp [delta] at hh
  let _ := isStarNormal_of_mem_unitary (Unitary.smul_mem ⟨z,hz⟩ (leftOperator_unitary (1 : A)))
  change (∫ q : spectrum ℂ (z • leftOperator (1 : A)), KervaireSpectral.phase q
    ∂vectorMeasure (z • leftOperator (1 : A)) (delta 1)) = _
  have he (q : spectrum ℂ (z • leftOperator (1 : A))) : (q : ℂ) = z := by
    have hq : (q : ℂ) ∈ spectrum ℂ (algebraMap ℂ (Operator A) z) := by
      simpa only [Algebra.algebraMap_eq_smul_one,leftOperator_one] using q.property
    simpa only [spectrum.scalar_eq,Set.mem_singleton_iff] using hq
  trans ∫ _q : spectrum ℂ (z • leftOperator (1 : A)),
    KervaireSpectral.phase z * 1 ∂vectorMeasure (z • leftOperator (1 : A)) (delta 1)
  · apply integral_congr_ae
    filter_upwards [] with q
    simp [he q]
  · rw [integral_const_mul,integral_one_vectorMeasure]
    simp [vectorCLM_apply,delta]

lemma groupPhase_rotation_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    groupPhase (scalarRotation (-ε)) (scalarRotation_unitary _) (1 : A) = 1-ε := by
  rw [groupPhase_one]
  rw [show KervaireSpectral.phase (scalarRotation (-ε)) = Int.fract (-ε) from phase_exp_normalized _]
  rw [Int.fract_eq_iff]
  refine ⟨by linarith,by linarith, -1,?_⟩
  norm_num
  ring

/-- The final right-cut limiting argument in the planar component theorem. -/
lemma trivial_of_boundary_inequalities {Z : Type*} [Fintype Z] [Nonempty Z]
    (z₀ : Z) (c : Z → A)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      groupPhase (scalarRotation (((Fintype.card Z : ℝ)-1)*ε)) (scalarRotation_unitary _) (c z₀)
        + ((Fintype.card Z : ℝ)-1)*(1-ε) ≤ (Fintype.card Z : ℝ)-1) :
    c z₀ = 1 := by
  let x : ℕ → ℝ := fun n ↦ 1 / (n+2)
  have hx : Filter.Tendsto x Filter.atTop (nhds 0) := by
    simpa only [x,Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hx0 (n : ℕ) : 0 < x n := by dsimp [x]; positivity
  have hx1 (n : ℕ) : x n < 1 := by dsimp [x]; rw [div_lt_one (by positivity)]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hcard : (0 : ℝ) ≤ (Fintype.card Z : ℝ)-1 := by
    have hc := Fintype.card_pos (α := Z)
    have : (1 : ℝ) ≤ Fintype.card Z := by exact_mod_cast hc
    linarith
  have ht := tendsto_groupPhase_rotation (c z₀)
    (by simpa using hx.const_mul ((Fintype.card Z : ℝ)-1))
    (fun n ↦ mul_nonneg hcard (hx0 n).le)
  have hl : groupPhase 1 (one_mem _) (c z₀) ≤ 0 := by
    apply le_of_tendsto_of_tendsto' ht
      (show Filter.Tendsto (fun n ↦ ((Fintype.card Z : ℝ)-1)*x n) Filter.atTop (nhds 0) by
        simpa using hx.const_mul ((Fintype.card Z : ℝ)-1))
    intro n
    have hn := h (x n) (hx0 n) (hx1 n)
    linarith
  apply (groupPhase_eq_zero_iff _).mp
  exact le_antisymm hl (by
    let _ := isStarNormal_of_mem_unitary
      (Unitary.smul_mem ⟨(1 : ℂ),one_mem _⟩ (leftOperator_unitary (c z₀)))
    unfold groupPhase
    exact vectorPhase_nonneg _ _)
end KervaireRegular

namespace KervaireCycle
open KervaireSpectral
variable {D B : Type*} [CommMonoid B]
lemma orbitWeight_eq_prod (σ : Equiv.Perm D) (b : D → B) (n : ℕ) (i : D) :
    orbitWeight σ b n i = ∏ j ∈ Finset.range n, b ((σ^j) i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [orbitWeight_succ,ih,Finset.prod_range_succ,mul_comm]

lemma orbitWeight_rotate_prod (d : ℕ) [NeZero d] (b : Fin d → B) :
    orbitWeight (finRotate d) b d 0 = ∏ i, b i := by
  rw [orbitWeight_eq_prod,← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  rw [rotate_pow_apply]
  simp

lemma orbitWeight_scalarRotation (d : ℕ) [NeZero d] (γ : Fin d → ℝ) :
    orbitWeight (finRotate d) (fun i ↦ scalarRotation (γ i)) d 0 = scalarRotation (∑ i, γ i) := by
  rw [orbitWeight_rotate_prod]
  exact (map_sum (show ℝ →+ Additive ℂ from
    { toFun := fun x ↦ Additive.ofMul (scalarRotation x)
      map_zero' := scalarRotation_zero
      map_add' := scalarRotation_add }) _ _).symm
end KervaireCycle

namespace KervaireBoundary
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular
open scoped Classical
variable {D Z A : Type*} [Fintype D] [Fintype Z] [Group A]

/-- Summation over the fibers of the explicit boundary-cycle decomposition. -/
lemma divergence_cycle (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D) (γ : D → ℝ) (z : Z) :
    (∑ d, if (e.symm d).1 = z then γ d else 0) = ∑ i, γ (e ⟨z,i⟩) := by
  rw [← e.sum_comp,Fintype.sum_sigma]
  simp

lemma total_cycle_length (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D) :
    (∑ z, (n z : ℝ)) = Fintype.card D - Fintype.card Z := by
  have hc := Fintype.card_congr e
  simp only [Fintype.card_sigma,Fintype.card_fin,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one] at hc
  have hr : (∑ z, (n z : ℝ)) + Fintype.card Z = Fintype.card D := by exact_mod_cast hc
  linarith

/-- Cycle phase specializes to prescribed real boundary fluxes. -/
lemma phase_boundary_cycles (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D)
    (σ : Equiv.Perm D) (he : ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (γ : D → ℝ) (a : D → A) (η : Z → ℝ)
    (hη : ∀ z, (∑ d, if (e.symm d).1 = z then γ d else 0) = η z) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary σ (fun d ↦ scalarRotation (γ d)) a
      (fun d ↦ scalarRotation_unitary (γ d)))
    KervaireMatrix.phase (weightedShift σ (fun d ↦ scalarRotation (γ d)) a) =
      ((Fintype.card D : ℝ) - Fintype.card Z) / 2 +
        ∑ z, groupPhase (scalarRotation (η z)) (scalarRotation_unitary _)
          (orbitWeight (finRotate (n z+1)) (fun i ↦ a (e ⟨z,i⟩)) (n z+1) 0) := by
  let _ := isStarNormal_of_mem_unitary (weightedShift_unitary σ (fun d ↦ scalarRotation (γ d)) a
    (fun d ↦ scalarRotation_unitary (γ d)))
  change KervaireMatrix.phase (weightedShift σ (fun d ↦ scalarRotation (γ d)) a) = _
  rw [phase_cycles n e σ he _ _ (fun d ↦ scalarRotation_unitary (γ d)),Finset.sum_add_distrib,← Finset.sum_div,total_cycle_length n e]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  have hrot : orbitWeight (finRotate (n z+1))
      (fun i ↦ scalarRotation (γ (e ⟨z,i⟩))) (n z+1) 0 = scalarRotation (η z) := by
    rw [orbitWeight_scalarRotation,← divergence_cycle n e γ z,hη z]
  simp only [hrot]
end KervaireBoundary

end

end OAI
