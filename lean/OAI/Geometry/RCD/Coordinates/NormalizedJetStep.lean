import OAI.Geometry.RCD.Coordinates.InverseJetBounds
import OAI.Geometry.RCD.Coordinates.JetStep

namespace OAI

/-!
# The normalized coordinate update

The update is `h + (Dh)⁻ᵀ v`. Inverse-transpose bounds, the bilinear
product estimate, and scalar dyadic contraction control iterated
Fréchet derivatives with one positive parameter for every order.
-/

open Filter
open scoped ContDiff Topology

noncomputable section

namespace RegularPointCoordinates

variable {X F G : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The factorial product bound also holds for smoothness only at the
base point.  Each finite order uses a common open neighborhood. -/
theorem clm_apply_factorialMajorant_bound_at
    {f : X → F →L[ℝ] G} {g : X → F} {x : X}
    {B C D : ℝ} {m : ℕ} (hB : 0 < B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g x)
    (hfbound : ∀ i, i ≤ m → ‖iteratedFDeriv ℝ i f x‖ ≤
      C * factorialMajorant i * jetCoefficientScale B i)
    (hgbound : ∀ i, i ≤ m → ‖iteratedFDeriv ℝ i g x‖ ≤
      D * factorialMajorant i * jetCoefficientScale B i) :
    ‖iteratedFDeriv ℝ m (fun y => f y (g y)) x‖ ≤
      (10 * C * D) * factorialMajorant m * jetCoefficientScale B m := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv, hgv⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨s, hsu, hs, hx⟩ := mem_nhds_iff.mp (inter_mem hu hv)
  have heqF (i : ℕ) : iteratedFDerivWithin ℝ i f s x = iteratedFDeriv ℝ i f x :=
    iteratedFDerivWithin_of_isOpen i hs hx
  have heqG (i : ℕ) : iteratedFDerivWithin ℝ i g s x = iteratedFDeriv ℝ i g x :=
    iteratedFDerivWithin_of_isOpen i hs hx
  have hbound := clm_apply_factorialMajorant_bound hB hC hD
    (hfu.mono (fun y hy => (hsu hy).1)) (hgv.mono (fun y hy => (hsu hy).2))
    hs.uniqueDiffOn hx
    (fun i hi => by simpa only [heqF] using hfbound i hi)
    (fun i hi => by simpa only [heqG] using hgbound i hi)
  rwa [iteratedFDerivWithin_of_isOpen m hs hx] at hbound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Smoothness of the inverse-transpose field is automatic at each
point at which the Jacobian is invertible. -/
theorem contDiffAt_inverseTranspose_field
    {J : X → E →L[ℝ] E} {x : X} {m : ℕ}
    (hJ : ContDiffAt ℝ m J x) (hunit : IsUnit (J x)) :
    ContDiffAt ℝ m (fun y => operatorInverseTranspose (J y)) x := by
  obtain ⟨u, hu⟩ := hunit
  have hi := contDiffAt_ringInverse ℝ (n := (m : ℕ∞ω)) u
  rw [hu] at hi
  exact adjointOperator.contDiff.contDiffAt.comp x (hi.comp x hJ)

omit [CompleteSpace E] in
/-- The source jet bound supplies precisely the Jacobian weight used by
the inverse-majorant theorem, with no enlargement of the base. -/
theorem jacobian_jet_bound_of_source_jet_bound
    {h : E → E} {x : E} {B : ℝ}
    (hbound : ∀ m, 2 ≤ m → ‖iteratedFDeriv ℝ m h x‖ ≤
      B ^ (m - 1) * (m.factorial : ℝ) ^ 3)
    {m : ℕ} (hm : 0 < m) :
    ‖iteratedFDeriv ℝ m (fderiv ℝ h) x‖ ≤
      factorialMajorant m * jetCoefficientScale B m := by
  rw [norm_iteratedFDeriv_fderiv]
  calc
    _ ≤ B ^ ((m + 1) - 1) * ((m + 1).factorial : ℝ) ^ 3 := hbound (m + 1) (by omega)
    _ = _ := by
      simp only [Nat.add_sub_cancel]
      unfold factorialMajorant jetCoefficientScale
      rw [Nat.factorial_succ]
      push_cast
      ring

/-- With explicit Jacobian jets, the actual inverse-transpose update
preserves every normalized jet of order at least two. -/
theorem exists_normalized_jet_step_of_jacobian_bounds
    {A B Cv : ℝ} (hA : 1 ≤ A) (hB : 0 < B) (hCv : 0 ≤ Cv) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (h : E → E) (J : E → E →L[ℝ] E) (v : E → E) (x : E),
      (∀ m : ℕ, ContDiffAt ℝ m h x) →
      (∀ m : ℕ, ContDiffAt ℝ m J x) →
      (∀ m : ℕ, ContDiffAt ℝ m v x) → IsUnit (J x) →
      ‖Ring.inverse (J x)‖ ≤ Real.sqrt A →
      (∀ m, 2 ≤ m → ‖iteratedFDeriv ℝ m h x‖ ≤
        B ^ (m - 1) * (m.factorial : ℝ) ^ 3) →
      (∀ m, 0 < m → ‖iteratedFDeriv ℝ m J x‖ ≤
        factorialMajorant m * jetCoefficientScale B m) →
      (∀ m, ‖iteratedFDeriv ℝ m v x‖ ≤
        epsilon * Cv * factorialMajorant m * jetCoefficientScale B m) →
      ∀ m, 2 ≤ m →
        (2 / (2 : ℝ) ^ m) *
          ‖iteratedFDeriv ℝ m (fun y => h y + operatorInverseTranspose (J y) (v y)) x‖ ≤
        B ^ (m - 1) * (m.factorial : ℝ) ^ 3 := by
  obtain ⟨C, hC0, _, hinverse⟩ :=
    inverseTranspose_iteratedFDeriv_uniform_bound (E := E) (X := E) hA
  have hC : 0 ≤ C := (Real.sqrt_nonneg A).trans hC0
  have htotal : 0 ≤ 10 * C * Cv := mul_nonneg (mul_nonneg (by norm_num) hC) hCv
  obtain ⟨epsilon, hepsilon, hstep⟩ := exists_uniform_scalar_jet_step hB.le htotal
  refine ⟨epsilon, hepsilon, ?_⟩
  intro h J v x hh hJ hv hunit hInv hsource hJacobian hfield m hm
  let K : E → E →L[ℝ] E := fun y => operatorInverseTranspose (J y)
  have hK : ∀ i : ℕ, ContDiffAt ℝ i K x :=
    fun i => contDiffAt_inverseTranspose_field (hJ i) hunit
  have hKbound : ∀ i, ‖iteratedFDeriv ℝ i K x‖ ≤
      C * factorialMajorant i * jetCoefficientScale B i :=
    hinverse B hB J x hJ hunit hInv hJacobian
  have hproduct : ‖iteratedFDeriv ℝ m (fun y => K y (v y)) x‖ ≤
      epsilon * (10 * C * Cv) * B ^ m * factorialMajorant m * (m.factorial : ℝ) := by
    have hp := clm_apply_factorialMajorant_bound_at hB hC
      (mul_nonneg hepsilon.le hCv) (hK m) (hv m)
      (fun i _ => hKbound i) (fun i _ => hfield i)
    calc
      _ ≤ (10 * C * (epsilon * Cv)) * factorialMajorant m * jetCoefficientScale B m := hp
      _ = _ := by unfold jetCoefficientScale; ring
  have hadd : ‖iteratedFDeriv ℝ m (fun y => h y + K y (v y)) x‖ ≤
      ‖iteratedFDeriv ℝ m h x‖ + ‖iteratedFDeriv ℝ m (fun y => K y (v y)) x‖ := by
    rw [show (fun y => h y + K y (v y)) = h + (fun y => K y (v y)) from rfl,
      iteratedFDeriv_add_apply (hh m) ((hK m).clm_apply (hv m))]
    exact norm_add_le _ _
  calc
    _ ≤ (2 / (2 : ℝ) ^ m) *
        (‖iteratedFDeriv ℝ m h x‖ + ‖iteratedFDeriv ℝ m (fun y => K y (v y)) x‖) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ ≤ _ := hstep m _ _ hm (hsource m hm) hproduct

/-- The normalized coordinate update with the genuine derivative field.
There is one positive `epsilon` for all orders, all maps, and all base
points satisfying the stated source and correction jet bounds. -/
theorem exists_normalized_jet_step
    {A B Cv : ℝ} (hA : 1 ≤ A) (hB : 0 < B) (hCv : 0 ≤ Cv) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (h v : E → E) (x : E),
      (∀ m : ℕ, ContDiffAt ℝ m h x) →
      (∀ m : ℕ, ContDiffAt ℝ m v x) → IsUnit (fderiv ℝ h x) →
      ‖Ring.inverse (fderiv ℝ h x)‖ ≤ Real.sqrt A →
      (∀ m, 2 ≤ m → ‖iteratedFDeriv ℝ m h x‖ ≤
        B ^ (m - 1) * (m.factorial : ℝ) ^ 3) →
      (∀ m, ‖iteratedFDeriv ℝ m v x‖ ≤
        epsilon * Cv * factorialMajorant m * jetCoefficientScale B m) →
      ∀ m, 2 ≤ m →
        (2 / (2 : ℝ) ^ m) *
          ‖iteratedFDeriv ℝ m (fun y => h y +
            operatorInverseTranspose (fderiv ℝ h y) (v y)) x‖ ≤
        B ^ (m - 1) * (m.factorial : ℝ) ^ 3 := by
  obtain ⟨epsilon, hepsilon, hstep⟩ :=
    exists_normalized_jet_step_of_jacobian_bounds (E := E) hA hB hCv
  refine ⟨epsilon, hepsilon, ?_⟩
  intro h v x hh hv hunit hInv hsource hfield
  exact hstep h (fderiv ℝ h) v x hh
    (fun m => (hh (m + 1)).fderiv_right (by simp)) hv hunit hInv hsource
    (fun _ hm => jacobian_jet_bound_of_source_jet_bound hsource hm) hfield

/-- The universal inverse constant also controls every finite prefix.
Zero extension beyond the requested order supplies an admissible full
recurrence; it does not assume any derivative bound at higher orders. -/
theorem inverse_jet_finite_uniform_bound {A : ℝ} (hA : 1 ≤ A) :
    ∃ C : ℝ, Real.sqrt A ≤ C ∧ 2 * A ≤ C ∧
      ∀ (B : ℝ), 0 < B → ∀ (N : ℕ) (j k : ℕ → ℝ),
      (∀ q ≤ N, 0 ≤ j q) → (∀ q ≤ N, 0 ≤ k q) → k 0 ≤ Real.sqrt A →
      (∀ q, 0 < q → q ≤ N → j q ≤ factorialMajorant q * jetCoefficientScale B q) →
      (∀ q, 0 < q → q ≤ N → k q ≤ Real.sqrt A *
        ∑ i ∈ Finset.Icc 1 q, (q.choose i : ℝ) * j i * k (q - i)) →
      ∀ q ≤ N, k q ≤ C * factorialMajorant q * jetCoefficientScale B q := by
  obtain ⟨C, hC0, hCA, hC⟩ := inverse_jet_uniform_bound hA
  refine ⟨C, hC0, hCA, ?_⟩
  intro B hB N j k hj hk hkzero hjbound hrec
  let j' : ℕ → ℝ := fun q => if q ≤ N then j q else 0
  let k' : ℕ → ℝ := fun q => if q ≤ N then k q else 0
  have hjnonneg : ∀ q, 0 ≤ j' q := by
    intro q
    by_cases hq : q ≤ N
    · simpa only [j', ite_eq_left hq] using hj q hq
    · simp only [j', ite_eq_right hq, le_refl]
  have hknonneg : ∀ q, 0 ≤ k' q := by
    intro q
    by_cases hq : q ≤ N
    · simpa only [k', ite_eq_left hq] using hk q hq
    · simp only [k', ite_eq_right hq, le_refl]
  have hjbound' : ∀ q, 0 < q → j' q ≤ factorialMajorant q * jetCoefficientScale B q := by
    intro q hqpos
    by_cases hq : q ≤ N
    · simpa only [j', ite_eq_left hq] using hjbound q hqpos hq
    · simp only [j', ite_eq_right hq]
      exact mul_nonneg (factorialMajorant_pos q).le (jetCoefficientScale_pos hB q).le
  have hrec' : ∀ q, 0 < q → k' q ≤ Real.sqrt A *
      ∑ i ∈ Finset.Icc 1 q, (q.choose i : ℝ) * j' i * k' (q - i) := by
    intro q hqpos
    by_cases hq : q ≤ N
    · have hsum : (∑ i ∈ Finset.Icc 1 q, (q.choose i : ℝ) * j' i * k' (q - i)) =
          ∑ i ∈ Finset.Icc 1 q, (q.choose i : ℝ) * j i * k (q - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i ≤ N := (Finset.mem_Icc.mp hi).2.trans hq
        have hsubN : q - i ≤ N := (Nat.sub_le _ _).trans hq
        simp only [j', k', ite_eq_left hiN, ite_eq_left hsubN]
      rw [hsum]
      simpa only [k', ite_eq_left hq] using hrec q hqpos hq
    · simp only [k', ite_eq_right hq]
      apply mul_nonneg (Real.sqrt_nonneg A)
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hjnonneg i)) (hknonneg (q - i))
  have hbound := hC B hB j' k' hknonneg (by simpa [k'] using hkzero) hjbound' hrec'
  intro q hq
  simpa only [k', ite_eq_left hq] using hbound q

/-- Actual inverse-transpose derivatives through a finite order use only
Jacobian derivatives through that same order.  The constant does not
depend on the finite cutoff. -/
theorem inverseTranspose_iteratedFDeriv_finite_uniform_bound {A : ℝ} (hA : 1 ≤ A) :
    ∃ C : ℝ, Real.sqrt A ≤ C ∧ 2 * A ≤ C ∧
      ∀ (B : ℝ), 0 < B → ∀ (N : ℕ) (J : E → E →L[ℝ] E) (x : E),
      ContDiffAt ℝ N J x → IsUnit (J x) → ‖Ring.inverse (J x)‖ ≤ Real.sqrt A →
      (∀ q, 0 < q → q ≤ N → ‖iteratedFDeriv ℝ q J x‖ ≤
        factorialMajorant q * jetCoefficientScale B q) →
      ∀ q ≤ N, ‖iteratedFDeriv ℝ q (fun y => operatorInverseTranspose (J y)) x‖ ≤
        C * factorialMajorant q * jetCoefficientScale B q := by
  obtain ⟨C, hC0, hCA, hC⟩ := inverse_jet_finite_uniform_bound hA
  refine ⟨C, hC0, hCA, ?_⟩
  intro B hB N J x hJ hunit hInv hJacobian q hq
  rw [norm_iteratedFDeriv_inverseTranspose]
  apply hC B hB N (fun i => ‖iteratedFDeriv ℝ i J x‖)
    (fun i => ‖iteratedFDeriv ℝ i (fun y => Ring.inverse (J y)) x‖)
  · exact fun _ _ => norm_nonneg _
  · exact fun _ _ => norm_nonneg _
  · simpa only [norm_iteratedFDeriv_zero] using hInv
  · exact hJacobian
  · intro i hipos hiN
    apply (norm_iteratedFDeriv_ringInverse_le
      (hJ.of_le (by exact_mod_cast hiN)) hunit hipos).trans
    apply mul_le_mul_of_nonneg_right hInv
    apply Finset.sum_nonneg
    intro l _
    positivity
  · exact hq

/-- Finite-order form of the genuine coordinate update.  To preserve
order `m`, only source jets through `m + 1` and correction jets through
`m` are needed.  The positive parameter is independent of `m`. -/
theorem exists_normalized_jet_step_finite
    {A B Cv : ℝ} (hA : 1 ≤ A) (hB : 0 < B) (hCv : 0 ≤ Cv) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (m : ℕ), 2 ≤ m → ∀ (h v : E → E) (x : E),
      ContDiffAt ℝ (m + 1) h x → ContDiffAt ℝ m v x →
      IsUnit (fderiv ℝ h x) → ‖Ring.inverse (fderiv ℝ h x)‖ ≤ Real.sqrt A →
      (∀ q, 2 ≤ q → q ≤ m + 1 → ‖iteratedFDeriv ℝ q h x‖ ≤
        B ^ (q - 1) * (q.factorial : ℝ) ^ 3) →
      (∀ q, q ≤ m → ‖iteratedFDeriv ℝ q v x‖ ≤
        epsilon * Cv * factorialMajorant q * jetCoefficientScale B q) →
      (2 / (2 : ℝ) ^ m) *
        ‖iteratedFDeriv ℝ m (fun y => h y +
          operatorInverseTranspose (fderiv ℝ h y) (v y)) x‖ ≤
        B ^ (m - 1) * (m.factorial : ℝ) ^ 3 := by
  obtain ⟨C, hC0, _, hinverse⟩ :=
    inverseTranspose_iteratedFDeriv_finite_uniform_bound (E := E) hA
  have hC : 0 ≤ C := (Real.sqrt_nonneg A).trans hC0
  have htotal : 0 ≤ 10 * C * Cv := mul_nonneg (mul_nonneg (by norm_num) hC) hCv
  obtain ⟨epsilon, hepsilon, hstep⟩ := exists_uniform_scalar_jet_step hB.le htotal
  refine ⟨epsilon, hepsilon, ?_⟩
  intro m hm h v x hh hv hunit hInv hsource hfield
  let J : E → E →L[ℝ] E := fderiv ℝ h
  let K : E → E →L[ℝ] E := fun y => operatorInverseTranspose (J y)
  have hJ : ContDiffAt ℝ m J x := hh.fderiv_right (by simp)
  have hK : ContDiffAt ℝ m K x := contDiffAt_inverseTranspose_field hJ hunit
  have hJacobian : ∀ q, 0 < q → q ≤ m → ‖iteratedFDeriv ℝ q J x‖ ≤
      factorialMajorant q * jetCoefficientScale B q := by
    intro q hqpos hqm
    rw [norm_iteratedFDeriv_fderiv]
    calc
      _ ≤ B ^ ((q + 1) - 1) * ((q + 1).factorial : ℝ) ^ 3 :=
        hsource (q + 1) (by omega) (by omega)
      _ = _ := by
        simp only [Nat.add_sub_cancel]
        unfold factorialMajorant jetCoefficientScale
        rw [Nat.factorial_succ]
        push_cast
        ring
  have hKbound := hinverse B hB m J x hJ hunit hInv hJacobian
  have hproduct : ‖iteratedFDeriv ℝ m (fun y => K y (v y)) x‖ ≤
      epsilon * (10 * C * Cv) * B ^ m * factorialMajorant m * (m.factorial : ℝ) := by
    have hp := clm_apply_factorialMajorant_bound_at hB hC
      (mul_nonneg hepsilon.le hCv) hK hv hKbound hfield
    calc
      _ ≤ (10 * C * (epsilon * Cv)) * factorialMajorant m * jetCoefficientScale B m := hp
      _ = _ := by unfold jetCoefficientScale; ring
  have hadd : ‖iteratedFDeriv ℝ m (fun y => h y + K y (v y)) x‖ ≤
      ‖iteratedFDeriv ℝ m h x‖ + ‖iteratedFDeriv ℝ m (fun y => K y (v y)) x‖ := by
    rw [show (fun y => h y + K y (v y)) = h + (fun y => K y (v y)) from rfl,
      iteratedFDeriv_add_apply (hh.of_le (by norm_cast; omega)) (hK.clm_apply hv)]
    exact norm_add_le _ _
  calc
    _ ≤ (2 / (2 : ℝ) ^ m) *
        (‖iteratedFDeriv ℝ m h x‖ + ‖iteratedFDeriv ℝ m (fun y => K y (v y)) x‖) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ ≤ _ := hstep m _ _ hm (hsource m hm (by omega)) hproduct

end RegularPointCoordinates

end

end OAI
