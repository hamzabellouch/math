import OAI.Geometry.RCD.Coordinates.FieldEstimates
import OAI.Geometry.RCD.Coordinates.NormalizedJetStep

namespace OAI

/-!
# Higher jets of finite cutoff-affine patch fields

Only two terms survive in a higher product derivative: all derivatives
on the cutoff, or one on the affine factor. Iterated Fréchet derivative
bounds follow from the cutoff jets.
-/

open Finset Filter
open scoped BigOperators ContDiff Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace RegularPointCoordinates

section SinglePatch

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of an affine patch is the fixed patch operator. -/
theorem fderiv_affine_patch (D : E →L[ℝ] F) (c : E) :
    fderiv ℝ (fun y => D (y - c)) = fun _ => D := by
  funext x
  exact ((D.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c))).fderiv

/-- All derivatives of an affine patch above order one vanish. -/
theorem norm_iteratedFDeriv_affine_patch (D : E →L[ℝ] F) (c x : E) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => D (y - c)) x‖ =
      if m = 0 then ‖D (x - c)‖ else if m = 1 then ‖D‖ else 0 := by
  cases m with
  | zero => simp [norm_iteratedFDeriv_zero]
  | succ m =>
    rw [← norm_iteratedFDeriv_fderiv, fderiv_affine_patch]
    cases m with
    | zero => simp [norm_iteratedFDeriv_zero]
    | succ m => simp [iteratedFDeriv_succ_const]

/-- Point-local version of the higher scalar-product bound. -/
theorem norm_iteratedFDeriv_smul_le_at
    {f : E → ℝ} {g : E → F} {x : E} {m : ℕ}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g x) :
    ‖iteratedFDeriv ℝ m (fun y => f y • g y) x‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (m - i) g x‖ := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv, hgv⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨s, hsu, hs, hx⟩ := mem_nhds_iff.mp (inter_mem hu hv)
  have h := norm_iteratedFDerivWithin_smul_le
    (hfu.mono (fun y hy => (hsu hy).1)) (hgv.mono (fun y hy => (hsu hy).2))
    hs.uniqueDiffOn hx le_rfl
  have heqf (q : ℕ) : iteratedFDerivWithin ℝ q f s x = iteratedFDeriv ℝ q f x :=
    iteratedFDerivWithin_of_isOpen q hs hx
  have heqg (q : ℕ) : iteratedFDerivWithin ℝ q g s x = iteratedFDeriv ℝ q g x :=
    iteratedFDerivWithin_of_isOpen q hs hx
  have heqfg : iteratedFDerivWithin ℝ m (fun y => f y • g y) s x =
      iteratedFDeriv ℝ m (fun y => f y • g y) x := iteratedFDerivWithin_of_isOpen m hs hx
  simpa only [heqf, heqg, heqfg] using h

/-- The two surviving terms in a higher cutoff-affine derivative. -/
theorem norm_iteratedFDeriv_cutoff_affine_le
    (D : E →L[ℝ] F) (c x : E) {phi : E → ℝ} {m : ℕ}
    (hphi : ContDiffAt ℝ (m + 1) phi x) :
    ‖iteratedFDeriv ℝ (m + 1) (fun y => phi y • D (y - c)) x‖ ≤
      ‖iteratedFDeriv ℝ (m + 1) phi x‖ * ‖D (x - c)‖ +
      (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m phi x‖ * ‖D‖ := by
  have ha : ContDiffAt ℝ (m + 1) (fun y => D (y - c)) x :=
    D.contDiff.contDiffAt.comp x (contDiffAt_id.sub contDiffAt_const)
  have hp := norm_iteratedFDeriv_smul_le_at hphi ha
  have hz : (∑ i ∈ Finset.range m, ((m + 1).choose i : ℝ) *
      ‖iteratedFDeriv ℝ i phi x‖ *
      ‖iteratedFDeriv ℝ (m + 1 - i) (fun y => D (y - c)) x‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hzero : m + 1 - i ≠ 0 := by omega
    have hone : m + 1 - i ≠ 1 := by omega
    rw [norm_iteratedFDeriv_affine_patch]
    simp only [ite_eq_right hzero, ite_eq_right hone, mul_zero]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, hz] at hp
  simp only [Nat.sub_self, Nat.add_sub_cancel_left, Nat.choose_self,
    Nat.choose_succ_self_right, Nat.cast_one, one_mul, zero_add,
    norm_iteratedFDeriv_affine_patch] at hp
  norm_num only [ite_true, ite_false, Nat.one_ne_zero, zero_ne_one] at hp
  simpa only [add_comm, Nat.cast_add, Nat.cast_one] using hp

/-- Multiplication by a cutoff cannot create derivative support outside
the cutoff support, including at its boundary. -/
theorem iteratedFDeriv_cutoff_affine_eq_zero_of_not_mem_tsupport
    (D : E →L[ℝ] F) (c x : E) (phi : E → ℝ) (m : ℕ)
    (hx : x ∉ tsupport phi) :
    iteratedFDeriv ℝ m (fun y => phi y • D (y - c)) x = 0 := by
  by_contra hne
  apply hx
  exact tsupport_smul_subset_left phi (fun y => D (y - c))
    (support_iteratedFDeriv_subset (𝕜 := ℝ) m hne)

/-- The derivative falling on the affine factor fits in the same
Gevrey-two weight as the term falling wholly on the cutoff. -/
theorem cutoff_affine_gevrey_weight_le {C : ℝ} (hC : 1 ≤ C) (m : ℕ) :
    (m + 1 : ℝ) * C ^ (m + 1) * (m.factorial : ℝ) ^ 2 ≤
      C ^ (m + 2) * ((m + 1).factorial : ℝ) ^ 2 := by
  have hpow : C ^ (m + 1) ≤ C ^ (m + 2) := pow_le_pow_right₀ hC (by omega)
  have hfac : (m + 1 : ℝ) * (m.factorial : ℝ) ^ 2 ≤
      ((m + 1).factorial : ℝ) ^ 2 := by
    rw [Nat.factorial_succ]
    push_cast
    have hm : (m + 1 : ℝ) ≤ (m + 1 : ℝ) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    convert mul_le_mul_of_nonneg_right hm (sq_nonneg (m.factorial : ℝ)) using 1
    ring
  calc
    _ = C ^ (m + 1) * ((m + 1 : ℝ) * (m.factorial : ℝ) ^ 2) := by ring
    _ ≤ C ^ (m + 2) * ((m + 1).factorial : ℝ) ^ 2 :=
      mul_le_mul hpow hfac (by positivity) (by positivity)

/-- A cutoff-affine term obeys a uniform Gevrey-two estimate at every
order, including its value.  The small operator and displacement bounds
are premises; the conclusion is derived from the actual product rule. -/
theorem scaled_cutoff_affine_jet_le
    (D : E →L[ℝ] F) (c x : E) {phi : E → ℝ} {m : ℕ}
    {epsilon r L C : ℝ} (hepsilon : 0 ≤ epsilon) (hr : 0 < r)
    (_hL : 0 ≤ L) (hC : 1 ≤ C) (hD : ‖D‖ ≤ epsilon)
    (hvalue : ‖D (x - c)‖ ≤ epsilon * L * r)
    (hphi : ContDiffAt ℝ m phi x)
    (hcutoff : ∀ q ≤ m, r ^ q * ‖iteratedFDeriv ℝ q phi x‖ ≤
      C ^ (q + 1) * (q.factorial : ℝ) ^ 2) :
    r ^ m * ‖iteratedFDeriv ℝ m (fun y => phi y • D (y - c)) x‖ ≤
      epsilon * r * (L + 1) * C ^ (m + 1) * (m.factorial : ℝ) ^ 2 := by
  have hCzero : 0 ≤ C := zero_le_one.trans hC
  cases m with
  | zero =>
    have hc : ‖phi x‖ ≤ C := by simpa [norm_iteratedFDeriv_zero] using hcutoff 0 (by omega)
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero, norm_smul,
      zero_add, pow_one, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    calc
      _ ≤ C * (epsilon * L * r) := mul_le_mul hc hvalue (norm_nonneg _) hCzero
      _ = epsilon * r * L * C := by ring
      _ ≤ epsilon * r * (L + 1) * C := by gcongr; linarith
  | succ m =>
    have hraw := norm_iteratedFDeriv_cutoff_affine_le D c x hphi
    have htop := hcutoff (m + 1) (by omega)
    have hprev := hcutoff m (by omega)
    have hfirst : r ^ (m + 1) *
        (‖iteratedFDeriv ℝ (m + 1) phi x‖ * ‖D (x - c)‖) ≤
        epsilon * r * L * (C ^ (m + 2) * ((m + 1).factorial : ℝ) ^ 2) := by
      calc
        _ = (r ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) phi x‖) * ‖D (x - c)‖ := by ring
        _ ≤ (C ^ (m + 2) * ((m + 1).factorial : ℝ) ^ 2) * (epsilon * L * r) :=
          mul_le_mul htop hvalue (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hsecond : r ^ (m + 1) *
        ((m + 1 : ℝ) * ‖iteratedFDeriv ℝ m phi x‖ * ‖D‖) ≤
        epsilon * r * (C ^ (m + 2) * ((m + 1).factorial : ℝ) ^ 2) := by
      calc
        _ = (r * (m + 1 : ℝ) * (r ^ m * ‖iteratedFDeriv ℝ m phi x‖)) * ‖D‖ := by
          rw [pow_succ]
          ring
        _ ≤ (r * (m + 1 : ℝ) * (C ^ (m + 1) * (m.factorial : ℝ) ^ 2)) * epsilon :=
          mul_le_mul (mul_le_mul_of_nonneg_left hprev (by positivity)) hD
            (norm_nonneg _) (by positivity)
        _ = epsilon * r * ((m + 1 : ℝ) * C ^ (m + 1) * (m.factorial : ℝ) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (cutoff_affine_gevrey_weight_le hC m)
          (mul_nonneg hepsilon hr.le)
    calc
      _ ≤ r ^ (m + 1) *
          (‖iteratedFDeriv ℝ (m + 1) phi x‖ * ‖D (x - c)‖ +
            (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m phi x‖ * ‖D‖) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ ≤ epsilon * r * L * (C ^ (m + 2) * ((m + 1).factorial : ℝ) ^ 2) +
          epsilon * r * (C ^ (m + 2) * ((m + 1).factorial : ℝ) ^ 2) := by
        rw [mul_add]
        exact add_le_add hfirst hsecond
      _ = _ := by ring

end SinglePatch

section FiniteField

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The finite patch field has the sum of its actual patch derivatives. -/
theorem iteratedFDeriv_patchField (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (x : E) (m : ℕ)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ m (phi j) x) :
    iteratedFDeriv ℝ m (patchField s phi D c) x =
      ∑ j ∈ s, iteratedFDeriv ℝ m (fun y => phi j y • D j (y - c j)) x := by
  apply iteratedFDeriv_fun_sum_apply
  intro j hj
  exact (hphi j hj).smul ((D j).contDiff.contDiffAt.comp x
    (contDiffAt_id.sub contDiffAt_const))

/-- In a positive derivative order, only two cutoff orders are needed. -/
theorem norm_iteratedFDeriv_patchField_le (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (x : E) (m : ℕ)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ (m + 1) (phi j) x) :
    ‖iteratedFDeriv ℝ (m + 1) (patchField s phi D c) x‖ ≤
      ∑ j ∈ s, (‖iteratedFDeriv ℝ (m + 1) (phi j) x‖ * ‖D j (x - c j)‖ +
        (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m (phi j) x‖ * ‖D j‖) := by
  rw [iteratedFDeriv_patchField s phi D c x (m + 1) hphi]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj =>
    norm_iteratedFDeriv_cutoff_affine_le (D j) (c j) x (hphi j hj))

/-- Every higher field jet can be restricted to the active cutoffs. -/
theorem iteratedFDeriv_patchField_eq_active (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (x : E) (m : ℕ)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ m (phi j) x) :
    iteratedFDeriv ℝ m (patchField s phi D c) x =
      iteratedFDeriv ℝ m (patchField (s.filter (fun j => x ∈ tsupport (phi j))) phi D c) x := by
  classical
  rw [iteratedFDeriv_patchField s phi D c x m hphi,
    iteratedFDeriv_patchField _ phi D c x m
      (fun j hj => hphi j (Finset.mem_filter.mp hj).1)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hnot
  have hx : x ∉ tsupport (phi j) := by
    intro hx
    exact hnot (Finset.mem_filter.mpr ⟨hj, hx⟩)
  exact iteratedFDeriv_cutoff_affine_eq_zero_of_not_mem_tsupport (D j) (c j) x (phi j) m hx

/-- Summing the actual patch jets costs only the number of active terms. -/
theorem scaled_patchField_jet_le (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (x : E) (m : ℕ)
    {epsilon r L C : ℝ} (hepsilon : 0 ≤ epsilon) (hr : 0 < r)
    (hL : 0 ≤ L) (hC : 1 ≤ C)
    (hD : ∀ j ∈ s, ‖D j‖ ≤ epsilon)
    (hvalue : ∀ j ∈ s, ‖D j (x - c j)‖ ≤ epsilon * L * r)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ m (phi j) x)
    (hcutoff : ∀ j ∈ s, ∀ q ≤ m,
      r ^ q * ‖iteratedFDeriv ℝ q (phi j) x‖ ≤ C ^ (q + 1) * (q.factorial : ℝ) ^ 2) :
    r ^ m * ‖iteratedFDeriv ℝ m (patchField s phi D c) x‖ ≤
      epsilon * r * (s.card : ℝ) * (L + 1) * C ^ (m + 1) * (m.factorial : ℝ) ^ 2 := by
  rw [iteratedFDeriv_patchField s phi D c x m hphi]
  calc
    _ ≤ r ^ m * ∑ j ∈ s, ‖iteratedFDeriv ℝ m (fun y => phi j y • D j (y - c j)) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ j ∈ s, r ^ m * ‖iteratedFDeriv ℝ m (fun y => phi j y • D j (y - c j)) x‖ :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ _j ∈ s, epsilon * r * (L + 1) * C ^ (m + 1) * (m.factorial : ℝ) ^ 2 :=
      Finset.sum_le_sum fun j hj => scaled_cutoff_affine_jet_le (D j) (c j) x
        hepsilon hr hL hC (hD j hj) (hvalue j hj) (hphi j hj) (hcutoff j hj)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- A fixed base absorbs the overlap and center-displacement constants. -/
def patchJetBase (N L C : ℝ) : ℝ := C * max 1 (N * (L + 1))

theorem patchJetBase_ge_one {N L C : ℝ} (hC : 1 ≤ C) :
    1 ≤ patchJetBase N L C := by
  unfold patchJetBase
  simpa using mul_le_mul hC (le_max_left 1 (N * (L + 1)))
    zero_le_one (zero_le_one.trans hC)

/-- Uniform all-order Gevrey-two field estimate, with base independent
of the derivative order and the size of the ambient net. -/
theorem patchField_scaled_gevrey_two (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (x : E) (m : ℕ)
    {epsilon r L C N : ℝ} (hepsilon : 0 ≤ epsilon) (hr : 0 < r)
    (hL : 0 ≤ L) (hC : 1 ≤ C) (hcard : (s.card : ℝ) ≤ N)
    (hD : ∀ j ∈ s, ‖D j‖ ≤ epsilon)
    (hvalue : ∀ j ∈ s, ‖D j (x - c j)‖ ≤ epsilon * L * r)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ m (phi j) x)
    (hcutoff : ∀ j ∈ s, ∀ q ≤ m,
      r ^ q * ‖iteratedFDeriv ℝ q (phi j) x‖ ≤ C ^ (q + 1) * (q.factorial : ℝ) ^ 2) :
    r ^ m * ‖iteratedFDeriv ℝ m (patchField s phi D c) x‖ ≤
      epsilon * r * (patchJetBase N L C) ^ (m + 1) * (m.factorial : ℝ) ^ 2 := by
  have hM : 1 ≤ max 1 (N * (L + 1)) := le_max_left _ _
  have hcoeff : (s.card : ℝ) * (L + 1) ≤ (max 1 (N * (L + 1))) ^ (m + 1) :=
    ((mul_le_mul_of_nonneg_right hcard (by linarith)).trans (le_max_right _ _)).trans
      (le_self_pow₀ hM (by omega))
  have hweight : (s.card : ℝ) * (L + 1) * C ^ (m + 1) ≤
      (patchJetBase N L C) ^ (m + 1) := by
    unfold patchJetBase
    rw [mul_pow]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcoeff
      (pow_nonneg (zero_le_one.trans hC) _)
  calc
    _ ≤ epsilon * r * (s.card : ℝ) * (L + 1) * C ^ (m + 1) * (m.factorial : ℝ) ^ 2 :=
      scaled_patchField_jet_le s phi D c x m hepsilon hr hL hC hD hvalue hphi hcutoff
    _ = (epsilon * r) * ((s.card : ℝ) * (L + 1) * C ^ (m + 1)) * (m.factorial : ℝ) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hweight (mul_nonneg hepsilon hr.le)) (sq_nonneg _)

/-- The uniform estimate for the full field counts only cutoffs whose
closed supports contain the testing point. -/
theorem patchField_scaled_gevrey_two_active (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (x : E) (m : ℕ)
    {epsilon r L C N : ℝ} (hepsilon : 0 ≤ epsilon) (hr : 0 < r)
    (hL : 0 ≤ L) (hC : 1 ≤ C)
    (hcard : ((s.filter (fun j => x ∈ tsupport (phi j))).card : ℝ) ≤ N)
    (hD : ∀ j ∈ s, x ∈ tsupport (phi j) → ‖D j‖ ≤ epsilon)
    (hvalue : ∀ j ∈ s, x ∈ tsupport (phi j) → ‖D j (x - c j)‖ ≤ epsilon * L * r)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ m (phi j) x)
    (hcutoff : ∀ j ∈ s, x ∈ tsupport (phi j) → ∀ q ≤ m,
      r ^ q * ‖iteratedFDeriv ℝ q (phi j) x‖ ≤ C ^ (q + 1) * (q.factorial : ℝ) ^ 2) :
    r ^ m * ‖iteratedFDeriv ℝ m (patchField s phi D c) x‖ ≤
      epsilon * r * (patchJetBase N L C) ^ (m + 1) * (m.factorial : ℝ) ^ 2 := by
  classical
  rw [iteratedFDeriv_patchField_eq_active s phi D c x m hphi]
  exact patchField_scaled_gevrey_two _ phi D c x m hepsilon hr hL hC hcard
    (fun j hj => hD j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2)
    (fun j hj => hvalue j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2)
    (fun j hj => hphi j (Finset.mem_filter.mp hj).1)
    (fun j hj => hcutoff j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2)

/-- Every repeated directional derivative obeys the same uniform field
bound, with the expected power of the direction norm. -/
theorem patchField_scaled_directional_gevrey_two_active
    (s : Finset ι) (phi : ι → E → ℝ) (D : ι → E →L[ℝ] E)
    (c : ι → E) (x xi : E) (m : ℕ)
    {epsilon r L C N : ℝ} (hepsilon : 0 ≤ epsilon) (hr : 0 < r)
    (hL : 0 ≤ L) (hC : 1 ≤ C)
    (hcard : ((s.filter (fun j => x ∈ tsupport (phi j))).card : ℝ) ≤ N)
    (hD : ∀ j ∈ s, x ∈ tsupport (phi j) → ‖D j‖ ≤ epsilon)
    (hvalue : ∀ j ∈ s, x ∈ tsupport (phi j) → ‖D j (x - c j)‖ ≤ epsilon * L * r)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ m (phi j) x)
    (hcutoff : ∀ j ∈ s, x ∈ tsupport (phi j) → ∀ q ≤ m,
      r ^ q * ‖iteratedFDeriv ℝ q (phi j) x‖ ≤ C ^ (q + 1) * (q.factorial : ℝ) ^ 2) :
    r ^ m * ‖iteratedFDeriv ℝ m (patchField s phi D c) x (fun _ => xi)‖ ≤
      epsilon * r * (patchJetBase N L C) ^ (m + 1) *
        (m.factorial : ℝ) ^ 2 * ‖xi‖ ^ m := by
  have hd : ‖iteratedFDeriv ℝ m (patchField s phi D c) x (fun _ => xi)‖ ≤
      ‖iteratedFDeriv ℝ m (patchField s phi D c) x‖ * ‖xi‖ ^ m := by
    simpa using (iteratedFDeriv ℝ m (patchField s phi D c) x).le_opNorm
      (fun _ => xi)
  calc
    _ ≤ r ^ m * (‖iteratedFDeriv ℝ m (patchField s phi D c) x‖ * ‖xi‖ ^ m) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = (r ^ m * ‖iteratedFDeriv ℝ m (patchField s phi D c) x‖) * ‖xi‖ ^ m := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (patchField_scaled_gevrey_two_active s phi D c x m
        hepsilon hr hL hC hcard hD hvalue hphi hcutoff) (by positivity)

end FiniteField

end RegularPointCoordinates

end

end OAI
