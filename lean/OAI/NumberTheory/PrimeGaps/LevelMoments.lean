import OAI.NumberTheory.PrimeGaps.ProfileVariance

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem levelFunction_weighted (g chi : ℝ → ℝ) {lambda r : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (k : ℝ) (j : ℕ) (t : Fin j → ℝ) :
    Real.sqrt (alpha lambda j) * levelFunction g chi lambda k r j t =
      ((-1:ℝ)^j / Real.sqrt r) * productProfile g k j t * chi (coordinateSum t) := by
  have ha : Real.sqrt (alpha lambda j) ≠ 0 := (Real.sqrt_pos.mpr (alpha_pos hlambda j)).ne'
  have hr0 : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  unfold levelFunction
  field_simp

theorem levelFunction_pair_weighted (g chi : ℝ → ℝ) {lambda k r : ℝ}
    (hlambda : 0 < lambda) (hk : 0 < k) (hr : 0 < r) (j : ℕ) (t : Fin j → ℝ) :
    Real.sqrt (alpha lambda j) *
      (levelFunction g chi lambda k r j t +
        deleteCoordinate (levelFunction g chi lambda k r (j+1)) t) =
      ((-1:ℝ)^j / Real.sqrt r) * productProfile g k j t *
        cancellationBracket g chi lambda k j (coordinateSum t) := by
  rw [mul_add, levelFunction_weighted g chi hlambda hr, levelFunction_delete hk]
  have hr0 : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have ha1 : Real.sqrt (alpha lambda (j+1)) ≠ 0 :=
    (Real.sqrt_pos.mpr (alpha_pos hlambda (j+1))).ne'
  have hratio := sqrt_alpha_succ_ratio hlambda hk j
  unfold cancellationBracket
  rw [← hratio, pow_succ]
  field_simp
  ring

theorem sign_pow_sq (j : ℕ) : ((-1:ℝ)^j)^2 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  simp

theorem levelFunction_sq (g chi : ℝ → ℝ) {lambda r k : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (hk : 0 ≤ k) (j : ℕ) (t : Fin j → ℝ) :
    alpha lambda j * levelFunction g chi lambda k r j t^2 =
      (1/r) * (productDensity (scaledProfileDensity g k) j t * chi (coordinateSum t)^2) := by
  have h := congrArg (fun x : ℝ => x^2) (levelFunction_weighted g chi hlambda hr k j t)
  simp only [mul_pow, div_pow, Real.sq_sqrt (alpha_pos hlambda j).le,
    Real.sq_sqrt hr.le, productProfile_sq g hk, sign_pow_sq] at h
  simpa only [mul_assoc] using h

theorem levelFunction_pair_sq (g chi : ℝ → ℝ) {lambda r k : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (hk : 0 < k) (j : ℕ) (t : Fin j → ℝ) :
    alpha lambda j * (levelFunction g chi lambda k r j t +
      deleteCoordinate (levelFunction g chi lambda k r (j+1)) t)^2 =
      (1/r) * (productDensity (scaledProfileDensity g k) j t *
        cancellationBracket g chi lambda k j (coordinateSum t)^2) := by
  have h := congrArg (fun x : ℝ => x^2) (levelFunction_pair_weighted g chi hlambda hk hr j t)
  simp only [mul_pow, div_pow, Real.sq_sqrt (alpha_pos hlambda j).le,
    Real.sq_sqrt hr.le, productProfile_sq g hk.le, sign_pow_sq] at h
  simpa only [mul_assoc] using h

noncomputable def l2Mass {j : ℕ} (f : (Fin j → ℝ) → ℝ) : ℝ := ∫ t, f t^2

theorem l2Mass_nonneg {j : ℕ} (f : (Fin j → ℝ) → ℝ) : 0 ≤ l2Mass f :=
  integral_nonneg fun t => sq_nonneg (f t)

theorem levelFunction_l2Mass (g chi : ℝ → ℝ) {lambda r k : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (hk : 0 ≤ k) (j : ℕ) :
    alpha lambda j * l2Mass (levelFunction g chi lambda k r j) =
      (1/r) * (∫ t : Fin j → ℝ,
        productDensity (scaledProfileDensity g k) j t * chi (coordinateSum t)^2) := by
  unfold l2Mass
  rw [← integral_const_mul, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (levelFunction_sq g chi hlambda hr hk j))

theorem levelFunction_pair_l2Mass (g chi : ℝ → ℝ) {lambda r k : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (hk : 0 < k) (j : ℕ) :
    alpha lambda j * l2Mass (fun t => levelFunction g chi lambda k r j t +
      deleteCoordinate (levelFunction g chi lambda k r (j+1)) t) =
      (1/r) * (∫ t : Fin j → ℝ, productDensity (scaledProfileDensity g k) j t *
        cancellationBracket g chi lambda k j (coordinateSum t)^2) := by
  unfold l2Mass
  rw [← integral_const_mul, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (levelFunction_pair_sq g chi hlambda hr hk j))

theorem levelFunction_delete_sq (g chi : ℝ → ℝ) {lambda r k : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (hk : 0 < k) (j : ℕ) (t : Fin j → ℝ) :
    alpha lambda j * (deleteCoordinate (levelFunction g chi lambda k r (j+1)) t)^2 =
      (1/r) * (productDensity (scaledProfileDensity g k) j t *
        ((Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) *
          cutoffDeletion g chi k (coordinateSum t))^2) := by
  have heq : Real.sqrt (alpha lambda j) *
      deleteCoordinate (levelFunction g chi lambda k r (j+1)) t =
      - (((-1:ℝ)^j / Real.sqrt r) * productProfile g k j t *
        ((Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) *
          cutoffDeletion g chi k (coordinateSum t))) := by
    calc
      _ = Real.sqrt (alpha lambda j) * (levelFunction g chi lambda k r j t +
        deleteCoordinate (levelFunction g chi lambda k r (j+1)) t) -
        Real.sqrt (alpha lambda j) * levelFunction g chi lambda k r j t := by ring
      _ = _ := by
        rw [levelFunction_pair_weighted g chi hlambda hk hr,
          levelFunction_weighted g chi hlambda hr]
        unfold cancellationBracket
        ring
  have h := congrArg (fun x : ℝ => x^2) heq
  rw [mul_pow, Real.sq_sqrt (alpha_pos hlambda j).le, neg_sq] at h
  have hright : (((-1:ℝ)^j / Real.sqrt r) * productProfile g k j t)^2 =
      (1/r) * productDensity (scaledProfileDensity g k) j t := by
    rw [mul_pow, div_pow, Real.sq_sqrt hr.le, productProfile_sq g hk.le, sign_pow_sq]
  rw [mul_pow, hright] at h
  simpa only [mul_assoc] using h

theorem scaled_cutoffDeletion_bounds {g chi : ℝ → ℝ} {lambda k : ℝ}
    (hlambda : 0 < lambda) (hk : 0 < k) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgn : ∀ u, 0 ≤ g u) (hgi : (∫ u, g u) = Real.sqrt lambda)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (j : ℕ) (hjk : (j:ℝ)+1 ≤ k) (s : ℝ) :
    0 ≤ (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * cutoffDeletion g chi k s ∧
    (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * cutoffDeletion g chi k s ≤ 1 := by
  have hlr : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  have h0 := cutoffDeletion_nonneg hgn hchi0 k s
  have h1 := cutoffDeletion_le_mass hg hgc hchi hgn hchi1 k s
  rw [hgi] at h1
  have ha0 : 0 ≤ Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda := by positivity
  refine ⟨mul_nonneg ha0 h0, ?_⟩
  calc
    _ ≤ (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * Real.sqrt lambda :=
      mul_le_mul_of_nonneg_left h1 ha0
    _ = Real.sqrt (((j:ℝ)+1)/k) := div_mul_cancel₀ _ hlr.ne'
    _ ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using (div_le_one hk).mpr hjk⟩

theorem levelFunction_delete_l2Mass_bound {g chi : ℝ → ℝ} {lambda r k : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (hk : 0 < k)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgn : ∀ u, 0 ≤ g u) (hg2 : (∫ u, g u^2) = 1) (hg1 : (∫ u, g u) = Real.sqrt lambda)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (j : ℕ) (hjk : (j:ℝ)+1 ≤ k) :
    alpha lambda j * l2Mass (deleteCoordinate (levelFunction g chi lambda k r (j+1))) ≤ 1/r := by
  have hp := scaledProfileDensity_continuous hg k
  have hpc := scaledProfileDensity_compact hgc hk.ne'
  have hpi := scaledProfileDensity_integral hk hg2
  have hD := productDensity_integrable hp hpc j
  let P : (Fin j → ℝ) → ℝ := fun t =>
    ((Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * cutoffDeletion g chi k (coordinateSum t))^2
  have hP : Continuous P := by
    apply Continuous.pow
    apply Continuous.const_mul
    exact (cutoffDeletion_continuous hg hgc hchi k).comp (by unfold coordinateSum; fun_prop)
  have hPD : Integrable (fun t : Fin j → ℝ => productDensity (scaledProfileDensity g k) j t * P t) := by
    simpa only [mul_comm] using poly_productDensity_integrable hp hpc hP
  have hv : (∫ t : Fin j → ℝ, productDensity (scaledProfileDensity g k) j t * P t) ≤ 1 := by
    rw [← productDensity_integral hpi j]
    apply integral_mono hPD hD
    intro t
    have hb := scaled_cutoffDeletion_bounds hlambda hk hg hgc hgn hg1 hchi hchi0 hchi1 j hjk (coordinateSum t)
    have hP1 : P t ≤ 1 := by dsimp only [P]; nlinarith
    have hpn : ∀ u, 0 ≤ scaledProfileDensity g k u := fun u => mul_nonneg hk.le (sq_nonneg _)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hP1 (productDensity_nonneg hpn j t)
  have heq : alpha lambda j * l2Mass (deleteCoordinate (levelFunction g chi lambda k r (j+1))) =
      (1/r) * ∫ t : Fin j → ℝ, productDensity (scaledProfileDensity g k) j t * P t := by
    unfold l2Mass
    rw [← integral_const_mul, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (levelFunction_delete_sq g chi hlambda hr hk j))
  rw [heq]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hv (one_div_pos.mpr hr).le

def activeLevels (k r : ℕ) : Finset ℕ := Finset.Icc (k-r+1) k

noncomputable def cancellationFamily (g chi : ℝ → ℝ) (lambda : ℝ) (k r j : ℕ) :
    (Fin j → ℝ) → ℝ :=
  if j ∈ activeLevels k r then levelFunction g chi lambda k r j else 0

noncomputable def familyW (lambda : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), alpha lambda j * l2Mass (f j)

noncomputable def familyV (lambda : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) : ℝ :=
  lambda * ∑ j ∈ Finset.range (k+1), alpha lambda j *
    l2Mass (fun t => f j t + deleteCoordinate (f (j+1)) t)

@[simp] theorem l2Mass_zero (j : ℕ) : l2Mass (0 : (Fin j → ℝ) → ℝ) = 0 := by
  simp [l2Mass]

@[simp] theorem deleteCoordinate_zero (j : ℕ) :
    deleteCoordinate (0 : (Fin (j+1) → ℝ) → ℝ) = 0 := by
  funext t
  simp [deleteCoordinate]

theorem cancellationFamily_of_mem {g chi : ℝ → ℝ} {lambda : ℝ} {k r j : ℕ}
    (hj : j ∈ activeLevels k r) :
    cancellationFamily g chi lambda k r j = levelFunction g chi lambda k r j := ite_eq_left hj

theorem cancellationFamily_of_not_mem {g chi : ℝ → ℝ} {lambda : ℝ} {k r j : ℕ}
    (hj : j ∉ activeLevels k r) : cancellationFamily g chi lambda k r j = 0 := ite_eq_right hj

theorem activeLevels_card {k r : ℕ} (hrk : r ≤ k) : (activeLevels k r).card = r := by
  simp only [activeLevels, Nat.card_Icc]
  omega

theorem activeLevels_subset_range (k r : ℕ) : activeLevels k r ⊆ Finset.range (k+1) := by
  intro j hj
  simp only [activeLevels, Finset.mem_Icc, Finset.mem_range] at *
  omega

theorem cancellationFamily_zero (g chi : ℝ → ℝ) (lambda : ℝ) (k r : ℕ) :
    cancellationFamily g chi lambda k r 0 = 0 := by
  apply cancellationFamily_of_not_mem
  simp [activeLevels]

theorem cancellationFamily_above (g chi : ℝ → ℝ) (lambda : ℝ) (k r : ℕ)
    {j : ℕ} (hj : k < j) : cancellationFamily g chi lambda k r j = 0 := by
  apply cancellationFamily_of_not_mem
  simp only [activeLevels, Finset.mem_Icc, not_and]
  exact fun _ => hj.not_ge

theorem cancellationFamily_W (g chi : ℝ → ℝ) (lambda : ℝ) (k r : ℕ) :
    familyW lambda k (cancellationFamily g chi lambda k r) =
      ∑ j ∈ activeLevels k r, alpha lambda j * l2Mass (levelFunction g chi lambda k r j) := by
  unfold familyW
  calc
    _ = ∑ j ∈ activeLevels k r, alpha lambda j *
      l2Mass (cancellationFamily g chi lambda k r j) := by
      symm
      apply Finset.sum_subset (activeLevels_subset_range k r)
      intro j _ hj
      rw [cancellationFamily_of_not_mem hj, l2Mass_zero, mul_zero]
    _ = _ := Finset.sum_congr rfl fun j hj => by rw [cancellationFamily_of_mem hj]

theorem cancellationFamily_W_bounds {g chi : ℝ → ℝ} {lambda beta : ℝ}
    {k r : ℕ} (hlambda : 0 < lambda) (hr : 0 < r) (hrk : r ≤ k)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ Ioi 0) (hg2 : (∫ u, g u^2) = 1)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (hflat : ∀ s ≤ beta, chi s = 1) (hmu : (∫ u, u*g u^2) < beta) :
    let d := beta - ∫ u, u*g u^2
    let v := ∫ u, (u-∫ v, v*g v^2)^2 * g u^2
    1-v/((k:ℝ)*d^2) ≤ familyW lambda k (cancellationFamily g chi lambda k r) ∧
    familyW lambda k (cancellationFamily g chi lambda k r) ≤ 1 := by
  dsimp only
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast hr
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (lt_of_lt_of_le hr hrk)
  rw [cancellationFamily_W]
  have heq (j : ℕ) := levelFunction_l2Mass g chi hlambda hr0 hk0.le j
  simp_rw [heq, ← Finset.mul_sum]
  have hcard : ((activeLevels k r).card:ℝ) = (r:ℝ) := by rw [activeLevels_card hrk]
  constructor
  · have hb := Finset.sum_le_sum (s := activeLevels k r) (fun j hj =>
      (scaled_cutoff_mass_bounds hk0 hg hgc hgs hg2 hchi hchi0 hchi1 hflat hmu j
        (by exact_mod_cast (Finset.mem_Icc.mp hj).2)).1)
    simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hb
    have h := mul_le_mul_of_nonneg_left hb (one_div_pos.mpr hr0).le
    simpa only [← mul_assoc, one_div_mul_cancel hr0.ne', one_mul] using h
  · have hb := Finset.sum_le_sum (s := activeLevels k r) (fun j hj =>
      (scaled_cutoff_mass_bounds hk0 hg hgc hgs hg2 hchi hchi0 hchi1 hflat hmu j
        (by exact_mod_cast (Finset.mem_Icc.mp hj).2)).2)
    simp only [Finset.sum_const, nsmul_eq_mul, hcard, mul_one] at hb
    have h := mul_le_mul_of_nonneg_left hb (one_div_pos.mpr hr0).le
    simpa only [one_div_mul_cancel hr0.ne'] using h

theorem cancellationFamily_V_split (g chi : ℝ → ℝ) (lambda : ℝ) {k r : ℕ}
    (hr : 0 < r) (hrk : r ≤ k) :
    familyV lambda k (cancellationFamily g chi lambda k r) = lambda *
      (alpha lambda (k-r) * l2Mass (deleteCoordinate (levelFunction g chi lambda k r (k-r+1))) +
       alpha lambda k * l2Mass (levelFunction g chi lambda k r k) +
       ∑ j ∈ Finset.Ioo (k-r) k, alpha lambda j * l2Mass (fun t =>
         levelFunction g chi lambda k r j t +
           deleteCoordinate (levelFunction g chi lambda k r (j+1)) t)) := by
  have hb : k-r < k := by omega
  have hsub : Finset.Icc (k-r) k ⊆ Finset.range (k+1) := by
    intro j hj
    have := (Finset.mem_Icc.mp hj).2
    simpa only [Finset.mem_range] using Nat.lt_succ_of_le this
  let A : ℕ → ℝ := fun j => alpha lambda j * l2Mass (fun t =>
    cancellationFamily g chi lambda k r j t +
      deleteCoordinate (cancellationFamily g chi lambda k r (j+1)) t)
  have hres : ∑ j ∈ Finset.range (k+1), A j = ∑ j ∈ Finset.Icc (k-r) k, A j := by
    symm
    apply Finset.sum_subset hsub
    intro j hj hn
    have h0 : j ∉ activeLevels k r := by
      simp only [activeLevels, Finset.mem_Icc, Finset.mem_range] at *
      omega
    have h1 : j+1 ∉ activeLevels k r := by
      simp only [activeLevels, Finset.mem_Icc, Finset.mem_range] at *
      omega
    simp only [A, cancellationFamily_of_not_mem h0, cancellationFamily_of_not_mem h1,
      deleteCoordinate_zero, Pi.zero_apply, zero_add]
    change alpha lambda j * l2Mass (0 : (Fin j → ℝ) → ℝ) = 0
    rw [l2Mass_zero, mul_zero]
  have hset : Finset.Icc (k-r) k = insert (k-r) (insert k (Finset.Ioo (k-r) k)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]
    omega
  have hn0 : k-r ∉ insert k (Finset.Ioo (k-r) k) := by simp; omega
  have hn1 : k ∉ Finset.Ioo (k-r) k := by simp
  have ha0 : k-r ∉ activeLevels k r := by simp [activeLevels]
  have ha1 : k-r+1 ∈ activeLevels k r := by simp only [activeLevels, Finset.mem_Icc]; omega
  have hak : k ∈ activeLevels k r := by simp only [activeLevels, Finset.mem_Icc]; omega
  have ha2 : k+1 ∉ activeLevels k r := by simp [activeLevels]
  have hbterm : A (k-r) = alpha lambda (k-r) *
      l2Mass (deleteCoordinate (levelFunction g chi lambda k r (k-r+1))) := by
    simp only [A, cancellationFamily_of_not_mem ha0, cancellationFamily_of_mem ha1,
      Pi.zero_apply, zero_add]
  have htterm : A k = alpha lambda k * l2Mass (levelFunction g chi lambda k r k) := by
    simp only [A, cancellationFamily_of_mem hak, cancellationFamily_of_not_mem ha2,
      deleteCoordinate_zero, Pi.zero_apply, add_zero]
  have hmid : ∑ j ∈ Finset.Ioo (k-r) k, A j =
      ∑ j ∈ Finset.Ioo (k-r) k, alpha lambda j * l2Mass (fun t =>
        levelFunction g chi lambda k r j t +
          deleteCoordinate (levelFunction g chi lambda k r (j+1)) t) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : j ∈ activeLevels k r := by
      simp only [activeLevels, Finset.mem_Icc, Finset.mem_Ioo] at *
      omega
    have hj1 : j+1 ∈ activeLevels k r := by
      simp only [activeLevels, Finset.mem_Icc, Finset.mem_Ioo] at *
      omega
    simp only [A, cancellationFamily_of_mem hj0, cancellationFamily_of_mem hj1]
  change lambda * (∑ j ∈ Finset.range (k+1), A j) = _
  rw [hres, hset, Finset.sum_insert hn0, Finset.sum_insert hn1, hbterm, htterm, hmid]
  ring

theorem familyV_nonneg {lambda : ℝ} (hlambda : 0 < lambda) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) : 0 ≤ familyV lambda k f := by
  exact mul_nonneg hlambda.le (Finset.sum_nonneg fun j _ =>
    mul_nonneg (alpha_pos hlambda j).le (l2Mass_nonneg _))

theorem cancellationFamily_V_bound {g chi : ℝ → ℝ} {lambda beta B : ℝ}
    {k r : ℕ} (hlambda : 0 < lambda) (hr : 0 < r) (hrk : r ≤ k)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ Ioi 0) (hgn : ∀ u, 0 ≤ g u)
    (hg2 : (∫ u, g u^2) = 1) (hg1 : (∫ u, g u) = Real.sqrt lambda)
    (hB : ∀ u ∈ Function.support g, u ≤ B) (hB0 : 0 ≤ B)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (hflat : ∀ s ≤ beta, chi s = 1) (hmu : (∫ u, u*g u^2) < beta)
    (hBk : B/(k:ℝ) ≤ (beta - ∫ u, u*g u^2)/2) :
    let d := beta - ∫ u, u*g u^2
    let v := ∫ u, (u-∫ v, v*g v^2)^2 * g u^2
    familyV lambda k (cancellationFamily g chi lambda k r) ≤
      lambda * (2/(r:ℝ) + ((r:ℝ)/k)^2 + 4*v/((k:ℝ)*d^2)) := by
  dsimp only
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast hr
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (lt_of_lt_of_le hr hrk)
  let E := ((r:ℝ)/k)^2 + 4*(∫ u, (u-∫ v, v*g v^2)^2 * g u^2)/
    ((k:ℝ)*(beta-∫ u, u*g u^2)^2)
  have hE : 0 ≤ E := by
    have hv : 0 ≤ ∫ u, (u-∫ v, v*g v^2)^2 * g u^2 :=
      integral_nonneg (fun u : ℝ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    dsimp only [E]
    positivity
  rw [cancellationFamily_V_split g chi lambda hr hrk]
  have hbot := levelFunction_delete_l2Mass_bound hlambda hr0 hk0 hg hgc hgn hg2 hg1
    hchi hchi0 hchi1 (k-r) (by exact_mod_cast (show k-r+1 ≤ k by omega))
  have htop : alpha lambda k * l2Mass (levelFunction g chi lambda k r k) ≤ 1/(r:ℝ) := by
    rw [levelFunction_l2Mass g chi hlambda hr0 hk0.le]
    have hb := (scaled_cutoff_mass_bounds hk0 hg hgc hgs hg2 hchi hchi0 hchi1 hflat hmu k le_rfl).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (one_div_pos.mpr hr0).le
  have hmidpoint (j : ℕ) (hj : j ∈ Finset.Ioo (k-r) k) :
      alpha lambda j * l2Mass (fun t => levelFunction g chi lambda k r j t +
        deleteCoordinate (levelFunction g chi lambda k r (j+1)) t) ≤ (1/(r:ℝ))*E := by
    rw [levelFunction_pair_l2Mass g chi hlambda hr0 hk0]
    apply mul_le_mul_of_nonneg_left _ (one_div_pos.mpr hr0).le
    apply scaled_cancellation_integral_bound hlambda hk0 hr0.le hg hgc hgs hgn hg2 hg1
      hB hB0 hchi hchi0 hchi1 hflat hmu hBk j
    · exact_mod_cast (show j+1 ≤ k from (Finset.mem_Ioo.mp hj).2)
    · have h1 : k ≤ (j+1)+r := by have := (Finset.mem_Ioo.mp hj).1; omega
      have h2 : (k:ℝ) ≤ ((j+1)+r:ℕ) := by exact_mod_cast h1
      push_cast at h2
      linarith
  have hmid := Finset.sum_le_sum hmidpoint
  have hcard : ((Finset.Ioo (k-r) k).card:ℝ) ≤ (r:ℝ) := by
    exact_mod_cast (show (Finset.Ioo (k-r) k).card ≤ r by rw [Nat.card_Ioo]; omega)
  simp only [Finset.sum_const, nsmul_eq_mul] at hmid
  have hmid' : (∑ j ∈ Finset.Ioo (k-r) k, alpha lambda j * l2Mass (fun t =>
      levelFunction g chi lambda k r j t +
        deleteCoordinate (levelFunction g chi lambda k r (j+1)) t)) ≤ E := by
    calc
      _ ≤ ((Finset.Ioo (k-r) k).card:ℝ) * ((1/(r:ℝ))*E) := hmid
      _ ≤ (r:ℝ)*((1/(r:ℝ))*E) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (one_div_pos.mpr hr0).le hE)
      _ = E := by field_simp
  apply mul_le_mul_of_nonneg_left _ hlambda.le
  calc
    _ ≤ 1/(r:ℝ) + 1/(r:ℝ) + E := add_le_add (add_le_add hbot htop) hmid'
    _ = _ := by dsimp only [E]; ring

def SymmetricFunction {j : ℕ} (f : (Fin j → ℝ) → ℝ) : Prop :=
  ∀ (e : Equiv.Perm (Fin j)) (t : Fin j → ℝ), f (t ∘ e) = f t

def positiveSimplex (j : ℕ) (tau : ℝ) : Set (Fin j → ℝ) :=
  {t | (∀ i, 0 < t i) ∧ coordinateSum t < tau}

theorem productProfile_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (productProfile g k j) := by
  unfold productProfile
  fun_prop

theorem levelFunction_smooth {g chi : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hchi : ContDiff ℝ ∞ chi)
    (lambda k r : ℝ) (j : ℕ) : ContDiff ℝ ∞ (levelFunction g chi lambda k r j) := by
  unfold levelFunction
  exact (contDiff_const.mul (productProfile_smooth hg k j)).mul
    (hchi.comp (by unfold coordinateSum; fun_prop))

theorem productProfile_compact {g : ℝ → ℝ} (hg : HasCompactSupport g)
    {k : ℝ} (hk : k ≠ 0) (j : ℕ) : HasCompactSupport (productProfile g k j) := by
  apply productDensity_compact (p := fun u : ℝ => Real.sqrt k * g (k*u))
  exact (hg.comp_smul hk).mul_left

theorem levelFunction_compact {g : ℝ → ℝ} (hg : HasCompactSupport g)
    (chi : ℝ → ℝ) (lambda r : ℝ) {k : ℝ} (hk : k ≠ 0) (j : ℕ) :
    HasCompactSupport (levelFunction g chi lambda k r j) := by
  exact ((productProfile_compact hg hk j).mul_left).mul_right

theorem productProfile_symmetric (g : ℝ → ℝ) (k : ℝ) (j : ℕ) :
    SymmetricFunction (productProfile g k j) := by
  intro e t
  exact Equiv.prod_comp e (fun i => Real.sqrt k * g (k*t i))

theorem coordinateSum_comp_perm {j : ℕ} (e : Equiv.Perm (Fin j)) (t : Fin j → ℝ) :
    coordinateSum (t ∘ e) = coordinateSum t := Equiv.sum_comp e t

theorem levelFunction_symmetric (g chi : ℝ → ℝ) (lambda k r : ℝ) (j : ℕ) :
    SymmetricFunction (levelFunction g chi lambda k r j) := by
  intro e t
  simp only [levelFunction, productProfile_symmetric g k j e t, coordinateSum_comp_perm]

theorem levelFunction_tsupport_subset {g chi : ℝ → ℝ} {lambda k r gamma : ℝ}
    (hchi : ∀ s, gamma ≤ s → chi s = 0) (j : ℕ) :
    tsupport (levelFunction g chi lambda k r j) ⊆
      {t | (∀ i, k*t i ∈ tsupport g) ∧ coordinateSum t ≤ gamma} := by
  apply closure_minimal
  · intro t ht
    have hQ : productProfile g k j t ≠ 0 := by
      intro h
      exact ht (by simp only [levelFunction, h, mul_zero, zero_mul])
    have hc : chi (coordinateSum t) ≠ 0 := by
      intro h
      exact ht (by simp only [levelFunction, h, mul_zero])
    refine ⟨fun i => subset_closure ?_, ?_⟩
    · have h := (Finset.prod_ne_zero_iff.mp hQ) i (Finset.mem_univ i)
      exact fun he => h (by simp [he])
    · exact (lt_of_not_ge fun h => hc (hchi _ h)).le
  · have hc : IsClosed {t : Fin j → ℝ | ∀ i, k*t i ∈ tsupport g} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter (fun i : Fin j =>
        (isClosed_tsupport g).preimage (show Continuous (fun t : Fin j → ℝ => k*t i) by fun_prop))
    have hs : IsClosed {t : Fin j → ℝ | coordinateSum t ≤ gamma} :=
      isClosed_le (show Continuous (fun t : Fin j → ℝ => coordinateSum t) by
        unfold coordinateSum; fun_prop) continuous_const
    exact hc.inter hs

theorem levelFunction_interior_support {g chi : ℝ → ℝ} {lambda k r gamma tau : ℝ}
    (hk : 0 < k) (hgs : tsupport g ⊆ Ioi 0) (hgt : gamma < tau)
    (hchi : ∀ s, gamma ≤ s → chi s = 0) (j : ℕ) :
    tsupport (levelFunction g chi lambda k r j) ⊆ positiveSimplex j tau := by
  intro t ht
  obtain ⟨hc, hs⟩ := levelFunction_tsupport_subset hchi j ht
  refine ⟨fun i => ?_, hs.trans_lt hgt⟩
  exact (mul_pos_iff_of_pos_left hk).mp (hgs (hc i))

theorem cancellationFamily_properties {g chi : ℝ → ℝ} {lambda gamma tau : ℝ}
    {k r : ℕ} (hk : 0 < k) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ Ioi 0) (hchi : ContDiff ℝ ∞ chi)
    (hgt : gamma < tau) (hchiz : ∀ s, gamma ≤ s → chi s = 0) (j : ℕ) :
    ContDiff ℝ ∞ (cancellationFamily g chi lambda k r j) ∧
    HasCompactSupport (cancellationFamily g chi lambda k r j) ∧
    tsupport (cancellationFamily g chi lambda k r j) ⊆ positiveSimplex j tau ∧
    SymmetricFunction (cancellationFamily g chi lambda k r j) := by
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  by_cases hj : j ∈ activeLevels k r
  · rw [cancellationFamily_of_mem hj]
    exact ⟨levelFunction_smooth hg hchi _ _ _ _, levelFunction_compact hgc _ _ _ hk0.ne' _,
      levelFunction_interior_support hk0 hgs hgt hchiz _, levelFunction_symmetric _ _ _ _ _ _⟩
  · rw [cancellationFamily_of_not_mem hj]
    refine ⟨contDiff_const, ?_, ?_, ?_⟩
    · exact HasCompactSupport.zero
    · simp
    · intro e t
      rfl

end LargePrimeGaps

end OAI
