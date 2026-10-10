import Mathlib
import OAI.Analysis.BoxTransport.Geometry

namespace OAI

/-! Localized solenoidal moving fields and their unique global flows. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
noncomputable def derivativeEntry (i j : Fin 3) :
    (SpaceTime →L[ℝ] Space) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.apply ℝ Space) (coordinateDirection (some i)))

@[simp] theorem derivativeEntry_apply (i j : Fin 3) (L : SpaceTime →L[ℝ] Space) :
    derivativeEntry i j L = L (coordinateDirection (some i)) j := rfl

noncomputable def curlLinear : (SpaceTime →L[ℝ] Space) →L[ℝ] Space :=
  ContinuousLinearMap.pi
    ![derivativeEntry 1 2 - derivativeEntry 2 1,
      derivativeEntry 2 0 - derivativeEntry 0 2,
      derivativeEntry 0 1 - derivativeEntry 1 0]

@[simp] theorem curlLinear_apply (L : SpaceTime →L[ℝ] Space) :
    curlLinear L =
      ![L (coordinateDirection (some 1)) 2 - L (coordinateDirection (some 2)) 1,
        L (coordinateDirection (some 2)) 0 - L (coordinateDirection (some 0)) 2,
        L (coordinateDirection (some 0)) 1 - L (coordinateDirection (some 1)) 0] := by
  ext j
  fin_cases j <;> rfl

noncomputable def spatialCurl (A : Field) : Field := fun p => curlLinear (fderiv ℝ A p)

theorem spatial_slice_fderiv {U : Field} (hU : Differentiable ℝ U)
    (t : ℝ) (x : Space) (v : Space) :
    fderiv ℝ (fun y => U (t, y)) x v = fderiv ℝ U (t, x) (0, v) := by
  have hs := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id x)
  have hd := (hU (t, x)).hasFDerivAt.comp x hs
  exact congrArg (fun L : Space →L[ℝ] Space => L v) hd.fderiv

theorem spatialDivergence_eq_full {U : Field} (hU : Differentiable ℝ U)
    (t : ℝ) (x : Space) :
    spatialDivergence U t x =
      ∑ j : Fin 3, (fderiv ℝ U (t, x) (coordinateDirection (some j))) j := by
  unfold spatialDivergence
  apply Finset.sum_congr rfl
  intro j hj
  rw [spatial_slice_fderiv hU]
  rfl

theorem contDiff_spatialCurl {A : Field} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (spatialCurl A) := by
  exact curlLinear.contDiff.comp (hA.fderiv_right (by simp))

theorem hasCompactSupport_spatialCurl {A : Field} (hA : HasCompactSupport A) :
    HasCompactSupport (spatialCurl A) :=
  (hA.fderiv ℝ).comp_left (map_zero curlLinear)

theorem fderiv_spatialCurl {A : Field} (hA : ContDiff ℝ ∞ A)
    (p v : SpaceTime) :
    fderiv ℝ (spatialCurl A) p v = curlLinear (fderiv ℝ (fderiv ℝ A) p v) := by
  have hAd : ContDiff ℝ ∞ (fderiv ℝ A) := hA.fderiv_right (by simp)
  exact congrArg (fun L : SpaceTime →L[ℝ] Space => L v)
    ((curlLinear.hasFDerivAt.comp p
      ((hAd.differentiable (by simp) p).hasFDerivAt)).fderiv)

theorem spatialDivergence_spatialCurl {A : Field} (hA : ContDiff ℝ ∞ A)
    (t : ℝ) (x : Space) : spatialDivergence (spatialCurl A) t x = 0 := by
  rw [spatialDivergence_eq_full ((contDiff_spatialCurl hA).differentiable (by simp))]
  simp only [Fin.sum_univ_three,
    fderiv_spatialCurl hA, curlLinear_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have hsym := hA.contDiffAt.isSymmSndFDerivAt (x := (t, x)) (by simp)
  have h01 := congrArg (fun z : Space => z 2)
    (hsym.eq (coordinateDirection (some 0)) (coordinateDirection (some 1)))
  have h02 := congrArg (fun z : Space => z 1)
    (hsym.eq (coordinateDirection (some 0)) (coordinateDirection (some 2)))
  have h12 := congrArg (fun z : Space => z 0)
    (hsym.eq (coordinateDirection (some 1)) (coordinateDirection (some 2)))
  linarith

theorem spatialCurl_congr_of_eventuallyEq {A B : Field} {p : SpaceTime}
    (h : A =ᶠ[nhds p] B) : spatialCurl A p = spatialCurl B p := by
  unfold spatialCurl
  rw [h.fderiv_eq]

theorem spatialCurl_zero_on_slice {A : Field} (hA : Differentiable ℝ A)
    {t : ℝ} (ht : ∀ x : Space, A (t, x) = 0) (x : Space) :
    spatialCurl A (t, x) = 0 := by
  have hslice : (fun y => A (t, y)) = fun _ => 0 := funext ht
  have hz (j : Fin 3) : fderiv ℝ A (t, x) (coordinateDirection (some j)) = 0 := by
    change fderiv ℝ A (t, x) (0, coordinateVector j) = 0
    rw [← spatial_slice_fderiv hA t x (coordinateVector j), hslice]
    simp
  simp [spatialCurl, hz]

theorem curl_field_properties {A : Field} (hA : ContDiff ℝ ∞ A)
    (hcompact : HasCompactSupport A)
    (htime : ∀ (t : ℝ) (x : Space),
      t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → A (t, x) = 0) :
    ContDiff ℝ ∞ (spatialCurl A) ∧ HasCompactSupport (spatialCurl A) ∧
      (∀ t x, spatialDivergence (spatialCurl A) t x = 0) ∧
      (∀ (t : ℝ) (x : Space), t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
        spatialCurl A (t, x) = 0) := by
  refine ⟨contDiff_spatialCurl hA, hasCompactSupport_spatialCurl hcompact,
    spatialDivergence_spatialCurl hA, ?_⟩
  intro t x ht
  exact spatialCurl_zero_on_slice (hA.differentiable (by simp)) (fun y => htime t y ht) x

noncomputable def potentialComponent (c v l : Space) (i j : Fin 3) (p : SpaceTime) : ℝ :=
  (1 / 2 : ℝ) * (v i * (p.2 j - c j) - v j * (p.2 i - c i)) +
    ((1 / 3 : ℝ) * (l i - l j)) * ((p.2 i - c i) * (p.2 j - c j))

noncomputable def affinePotential (c v l : Space) : Field := fun p =>
  ![potentialComponent c v l 1 2 p, potentialComponent c v l 2 0 p,
    potentialComponent c v l 0 1 p]

open scoped Matrix in

theorem affinePotential_eq_cross (c v l : Space) (p : SpaceTime) :
    affinePotential c v l p =
      (1 / 2 : ℝ) • (v ⨯₃ (p.2 - c)) +
      (1 / 3 : ℝ) • ((fun j => l j * (p.2 j - c j)) ⨯₃ (p.2 - c)) := by
  ext j
  fin_cases j <;>
    simp [affinePotential, potentialComponent, cross_apply] <;> ring

theorem contDiff_affinePotential (c v l : Space) :
    ContDiff ℝ ∞ (affinePotential c v l) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp [affinePotential, potentialComponent] <;> fun_prop

theorem fderiv_potentialComponent (c v l : Space) (i j : Fin 3) (p w : SpaceTime) :
    fderiv ℝ (potentialComponent c v l i j) p w =
      (1 / 2 : ℝ) * (v i * w.2 j - v j * w.2 i) +
        ((1 / 3 : ℝ) * (l i - l j)) *
          ((p.2 i - c i) * w.2 j + (p.2 j - c j) * w.2 i) := by
  let π (j : Fin 3) : SpaceTime →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ Space)
  have hy (j : Fin 3) : HasFDerivAt (fun p : SpaceTime => p.2 j - c j) (π j) p := by
    exact ((π j).hasFDerivAt).sub_const (c j)
  have hd := ((((hy j).const_mul (v i)).sub ((hy i).const_mul (v j))).const_mul
    (1 / 2 : ℝ)).add
      (((hy i).mul (hy j)).const_mul ((1 / 3 : ℝ) * (l i - l j)))
  have hd' : HasFDerivAt (potentialComponent c v l i j) _ p := hd
  have he := congrArg (fun L : SpaceTime →L[ℝ] ℝ => L w) hd'.fderiv
  simpa [π, mul_add] using he

theorem fderiv_affinePotential (c v l : Space) (p w : SpaceTime) :
    fderiv ℝ (affinePotential c v l) p w =
      ![fderiv ℝ (potentialComponent c v l 1 2) p w,
        fderiv ℝ (potentialComponent c v l 2 0) p w,
        fderiv ℝ (potentialComponent c v l 0 1) p w] := by
  have hA := (contDiff_affinePotential c v l).differentiable (by simp)
  have hcoord (i : Fin 3) :
      fderiv ℝ (affinePotential c v l) p w i =
        fderiv ℝ (fun q => affinePotential c v l q i) p w := by
    rw [fderiv_apply (hA p)]
    rfl
  ext j
  fin_cases j
  · exact hcoord 0
  · exact hcoord 1
  · exact hcoord 2

theorem spatialCurl_affinePotential (c v l : Space)
    (htrace : ∑ j : Fin 3, l j = 0) (p : SpaceTime) :
    spatialCurl (affinePotential c v l) p = fun j => v j + l j * (p.2 j - c j) := by
  simp only [Fin.sum_univ_three] at htrace
  have hl2 : l 2 = -l 0 - l 1 := by linarith
  unfold spatialCurl
  rw [curlLinear_apply]
  simp only [fderiv_affinePotential, fderiv_potentialComponent]
  ext j
  fin_cases j <;>
    dsimp [Matrix.cons_val] <;>
    simp [coordinateDirection, coordinateVector, hl2] <;> ring

theorem spatialCurl_cutoff_plateau (c v l : Space)
    (htrace : ∑ j : Fin 3, l j = 0) (χ : SpaceTime → ℝ) (p : SpaceTime)
    (hχ : χ =ᶠ[nhds p] fun _ => 1) :
    spatialCurl (fun q => χ q • affinePotential c v l q) p =
      fun j => v j + l j * (p.2 j - c j) := by
  rw [← spatialCurl_affinePotential c v l htrace p]
  apply spatialCurl_congr_of_eventuallyEq
  filter_upwards [hχ] with q hq
  simp [hq]

theorem spatialCurl_congr_on_slice {A B : Field}
    (hA : Differentiable ℝ A) (hB : Differentiable ℝ B) {t : ℝ}
    (hslice : ∀ x : Space, A (t, x) = B (t, x)) (x : Space) :
    spatialCurl A (t, x) = spatialCurl B (t, x) := by
  have he (j : Fin 3) : fderiv ℝ A (t, x) (coordinateDirection (some j)) =
      fderiv ℝ B (t, x) (coordinateDirection (some j)) := by
    change fderiv ℝ A (t, x) (0, coordinateVector j) =
      fderiv ℝ B (t, x) (0, coordinateVector j)
    rw [← spatial_slice_fderiv hA, ← spatial_slice_fderiv hB, funext hslice]
  simp only [spatialCurl, curlLinear_apply, he]

noncomputable def movingAffinePotential (c v l : ℝ → Space) : Field :=
  fun p => affinePotential (c p.1) (v p.1) (l p.1) p

theorem contDiff_movingAffinePotential {c v l : ℝ → Space}
    (hc : ContDiff ℝ ∞ c) (hv : ContDiff ℝ ∞ v) (hl : ContDiff ℝ ∞ l) :
    ContDiff ℝ ∞ (movingAffinePotential c v l) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;>
    dsimp [movingAffinePotential, affinePotential, potentialComponent] <;> fun_prop

theorem spatialCurl_movingAffinePotential {c v l : ℝ → Space}
    (hc : ContDiff ℝ ∞ c) (hv : ContDiff ℝ ∞ v) (hl : ContDiff ℝ ∞ l)
    (htrace : ∀ t, ∑ j : Fin 3, l t j = 0) (t : ℝ) (x : Space) :
    spatialCurl (movingAffinePotential c v l) (t, x) =
      fun j => v t j + l t j * (x j - c t j) := by
  rw [spatialCurl_congr_on_slice
    ((contDiff_movingAffinePotential hc hv hl).differentiable (by simp))
    ((contDiff_affinePotential (c t) (v t) (l t)).differentiable (by simp))
    (fun _ => rfl), spatialCurl_affinePotential _ _ _ (htrace t)]

noncomputable def movingBoxCutoff (c r : ℝ → Space) (η : ℝ) (p : SpaceTime) : ℝ :=
  ∏ j : Fin 3,
    Real.smoothTransition ((r p.1 j + 2 * η + (p.2 j - c p.1 j)) / η) *
    Real.smoothTransition ((r p.1 j + 2 * η - (p.2 j - c p.1 j)) / η)

theorem contDiff_movingBoxCutoff {c r : ℝ → Space} (η : ℝ)
    (hc : ContDiff ℝ ∞ c) (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (movingBoxCutoff c r η) := by
  unfold movingBoxCutoff
  apply contDiff_prod
  intro j hj
  apply ContDiff.mul <;> apply Real.smoothTransition.contDiff.comp <;> fun_prop

theorem movingBoxCutoff_one {c r : ℝ → Space} {η : ℝ} (hη : 0 < η)
    {p : SpaceTime} (hp : p.2 ∈ realBox (c p.1) (fun j => r p.1 j + η)) :
    movingBoxCutoff c r η p = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  have hleft : 1 ≤ (r p.1 j + 2 * η + (p.2 j - c p.1 j)) / η := by
    apply (le_div_iff₀ hη).mpr
    have := (abs_le.mp (hp j)).1
    linarith
  have hright : 1 ≤ (r p.1 j + 2 * η - (p.2 j - c p.1 j)) / η := by
    apply (le_div_iff₀ hη).mpr
    have := (abs_le.mp (hp j)).2
    linarith
  rw [Real.smoothTransition.one_of_one_le hleft,
    Real.smoothTransition.one_of_one_le hright, mul_one]

theorem movingBoxCutoff_zero {c r : ℝ → Space} {η : ℝ} (hη : 0 < η)
    {p : SpaceTime} (hp : p.2 ∉ openBox (c p.1) (r p.1) (2 * η)) :
    movingBoxCutoff c r η p = 0 := by
  classical
  simp only [openBox, Set.mem_ofPred_eq, not_forall, not_lt] at hp
  obtain ⟨j, hj⟩ := hp
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rcases le_or_gt (p.2 j - c p.1 j) 0 with hleft | hright
  · rw [abs_of_nonpos hleft] at hj
    have hz : Real.smoothTransition
        ((r p.1 j + 2 * η + (p.2 j - c p.1 j)) / η) = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
    rw [hz, zero_mul]
  · rw [abs_of_pos hright] at hj
    have hz : Real.smoothTransition
        ((r p.1 j + 2 * η - (p.2 j - c p.1 j)) / η) = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
    rw [hz, mul_zero]

def movingPlateau (c r : ℝ → Space) (η : ℝ) : Set SpaceTime :=
  {p | p.2 ∈ openBox (c p.1) (r p.1) η}

theorem isOpen_movingPlateau {c r : ℝ → Space} (η : ℝ)
    (hc : Continuous c) (hr : Continuous r) : IsOpen (movingPlateau c r η) := by
  change IsOpen {p : SpaceTime | ∀ j, |p.2 j - c p.1 j| < r p.1 j + η}
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt <;> fun_prop

theorem movingBoxCutoff_eventually_one {c r : ℝ → Space} {η : ℝ}
    (hη : 0 < η) (hc : Continuous c) (hr : Continuous r)
    {p : SpaceTime} (hp : p ∈ movingPlateau c r η) :
    movingBoxCutoff c r η =ᶠ[nhds p] fun _ => 1 := by
  filter_upwards [(isOpen_movingPlateau η hc hr).mem_nhds hp] with q hq
  apply movingBoxCutoff_one hη
  intro j
  exact le_of_lt (hq j)

theorem spatialCurl_localized_movingAffinePotential {c v l r : ℝ → Space} {η : ℝ}
    (hc : ContDiff ℝ ∞ c) (hv : ContDiff ℝ ∞ v) (hl : ContDiff ℝ ∞ l)
    (hr : ContDiff ℝ ∞ r) (hη : 0 < η)
    (htrace : ∀ t, ∑ j : Fin 3, l t j = 0)
    {p : SpaceTime} (hp : p ∈ movingPlateau c r η) :
    spatialCurl (fun q => movingBoxCutoff c r η q • movingAffinePotential c v l q) p =
      fun j => v p.1 j + l p.1 j * (p.2 j - c p.1 j) := by
  rw [← spatialCurl_movingAffinePotential hc hv hl htrace p.1 p.2]
  apply spatialCurl_congr_of_eventuallyEq
  filter_upwards [movingBoxCutoff_eventually_one hη hc.continuous hr.continuous hp]
    with q hq
  rw [hq, one_smul]

noncomputable def localizedPotential (c v l r : ℝ → Space) (η : ℝ) : Field :=
  fun p => movingBoxCutoff c r η p • movingAffinePotential c v l p

theorem contDiff_localizedPotential {c v l r : ℝ → Space} (η : ℝ)
    (hc : ContDiff ℝ ∞ c) (hv : ContDiff ℝ ∞ v)
    (hl : ContDiff ℝ ∞ l) (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (localizedPotential c v l r η) :=
  (contDiff_movingBoxCutoff η hc hr).smul (contDiff_movingAffinePotential hc hv hl)

theorem movingAffinePotential_zero {c v l : ℝ → Space} {t : ℝ}
    (hv : v t = 0) (hl : l t = 0) (x : Space) :
    movingAffinePotential c v l (t, x) = 0 := by
  ext j
  fin_cases j <;> simp [movingAffinePotential, affinePotential, potentialComponent, hv, hl]

theorem hasCompactSupport_localizedPotential {c v l r : ℝ → Space}
    {η t₀ t₁ R : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (hbound : ∀ t ∈ Set.Icc t₀ t₁, ∀ j, |c t j| + r t j + 2 * η ≤ R)
    (htime : ∀ t ∉ Set.Icc t₀ t₁, v t = 0 ∧ l t = 0) :
    HasCompactSupport (localizedPotential c v l r η) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc.prod (isCompact_closedBall (0 : Space) R))
  intro p hp
  have htimep : p.1 ∈ Set.Icc t₀ t₁ := by
    by_contra hn
    have hz := movingAffinePotential_zero (c := c) (htime p.1 hn).1 (htime p.1 hn).2 p.2
    exact hp (by dsimp [localizedPotential]; rw [hz, smul_zero])
  have hbox : p.2 ∈ openBox (c p.1) (r p.1) (2 * η) := by
    by_contra hn
    have hz := movingBoxCutoff_zero (c := c) (r := r) hη hn
    exact hp (by dsimp [localizedPotential]; rw [hz, zero_smul])
  refine ⟨htimep, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  intro j
  rw [Real.norm_eq_abs]
  calc
    |p.2 j| = |(p.2 j - c p.1 j) + c p.1 j| := by congr 1; ring
    _ ≤ |p.2 j - c p.1 j| + |c p.1 j| := abs_add_le _ _
    _ ≤ R := by have := hbox j; have := hbound p.1 htimep j; linarith

noncomputable def familyPotential {n : ℕ}
    (c v l r : Fin n → ℝ → Space) (η : ℝ) : Field :=
  fun p => ∑ i, localizedPotential (c i) (v i) (l i) (r i) η p

theorem contDiff_familyPotential {n : ℕ} {c v l r : Fin n → ℝ → Space} (η : ℝ)
    (hc : ∀ i, ContDiff ℝ ∞ (c i)) (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (hl : ∀ i, ContDiff ℝ ∞ (l i)) (hr : ∀ i, ContDiff ℝ ∞ (r i)) :
    ContDiff ℝ ∞ (familyPotential c v l r η) :=
  ContDiff.sum (fun i _ => contDiff_localizedPotential η (hc i) (hv i) (hl i) (hr i))

theorem hasCompactSupport_familyPotential {n : ℕ} {c v l r : Fin n → ℝ → Space}
    {η t₀ t₁ R : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (hbound : ∀ i t, t ∈ Set.Icc t₀ t₁ → ∀ j, |c i t j| + r i t j + 2 * η ≤ R)
    (htime : ∀ i t, t ∉ Set.Icc t₀ t₁ → v i t = 0 ∧ l i t = 0) :
    HasCompactSupport (familyPotential c v l r η) := by
  have hi (i : Fin n) : HasCompactSupport (localizedPotential (c i) (v i) (l i) (r i) η) :=
    hasCompactSupport_localizedPotential hη hR (hbound i) (htime i)
  have hs := HasCompactSupport.finset_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ => hi i)
  have he : familyPotential c v l r η =
      ∑ i : Fin n, localizedPotential (c i) (v i) (l i) (r i) η := by
    funext p
    exact (Finset.sum_apply p Finset.univ _).symm
  rw [he]
  exact hs

theorem familyPotential_zero {n : ℕ} {c v l r : Fin n → ℝ → Space}
    (η : ℝ) {t : ℝ} (hv : ∀ i, v i t = 0) (hl : ∀ i, l i t = 0) (x : Space) :
    familyPotential c v l r η (t, x) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  change movingBoxCutoff (c i) (r i) η (t, x) • movingAffinePotential (c i) (v i) (l i) (t, x) = 0
  rw [movingAffinePotential_zero (hv i) (hl i), smul_zero]

theorem familyPotential_eq_on_plateau {n : ℕ} {c v l r : Fin n → ℝ → Space}
    {η : ℝ} (hη : 0 < η)
    (hdis : ∀ t, Pairwise fun i j =>
      Disjoint (realBox (c i t) (fun k => r i t k + 2 * η))
        (realBox (c j t) (fun k => r j t k + 2 * η)))
    (i : Fin n) {p : SpaceTime} (hp : p ∈ movingPlateau (c i) (r i) η) :
    familyPotential c v l r η p = movingAffinePotential (c i) (v i) (l i) p := by
  have hx : p.2 ∈ realBox (c i p.1) (fun k => r i p.1 k + 2 * η) := by
    intro k
    have := hp k
    linarith
  rw [familyPotential, Finset.sum_eq_single i]
  · unfold localizedPotential
    rw [movingBoxCutoff_one hη (fun k => (hp k).le), one_smul]
  · intro j hj hji
    have hnot : p.2 ∉ openBox (c j p.1) (r j p.1) (2 * η) := by
      intro hy
      exact Set.disjoint_left.mp (hdis p.1 (Ne.symm hji)) hx (fun k => (hy k).le)
    unfold localizedPotential
    rw [movingBoxCutoff_zero hη hnot, zero_smul]
  · simp

theorem spatialCurl_familyPotential_on_plateau {n : ℕ} {c v l r : Fin n → ℝ → Space}
    {η : ℝ} (hη : 0 < η)
    (hc : ∀ i, ContDiff ℝ ∞ (c i)) (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (hl : ∀ i, ContDiff ℝ ∞ (l i)) (hr : ∀ i, ContDiff ℝ ∞ (r i))
    (htrace : ∀ i t, ∑ k : Fin 3, l i t k = 0)
    (hdis : ∀ t, Pairwise fun i j =>
      Disjoint (realBox (c i t) (fun k => r i t k + 2 * η))
        (realBox (c j t) (fun k => r j t k + 2 * η)))
    (i : Fin n) {p : SpaceTime} (hp : p ∈ movingPlateau (c i) (r i) η) :
    spatialCurl (familyPotential c v l r η) p =
      fun k => v i p.1 k + l i p.1 k * (p.2 k - c i p.1 k) := by
  rw [← spatialCurl_movingAffinePotential (hc i) (hv i) (hl i) (htrace i) p.1 p.2]
  apply spatialCurl_congr_of_eventuallyEq
  filter_upwards [(isOpen_movingPlateau η (hc i).continuous (hr i).continuous).mem_nhds hp]
    with q hq
  exact familyPotential_eq_on_plateau hη hdis i hq

theorem localized_separated_motion {n : ℕ} {c v l r : Fin n → ℝ → Space}
    {η R : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (hc : ∀ i, ContDiff ℝ ∞ (c i)) (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (hl : ∀ i, ContDiff ℝ ∞ (l i)) (hr : ∀ i, ContDiff ℝ ∞ (r i))
    (htrace : ∀ i t, ∑ k : Fin 3, l i t k = 0)
    (hdis : ∀ t, Pairwise fun i j =>
      Disjoint (realBox (c i t) (fun k => r i t k + 2 * η))
        (realBox (c j t) (fun k => r j t k + 2 * η)))
    (hbound : ∀ i t, t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
      ∀ j, |c i t j| + r i t j + 2 * η ≤ R)
    (htime : ∀ i t, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
      v i t = 0 ∧ l i t = 0) :
    ∃ U : Field,
      ContDiff ℝ ∞ U ∧ HasCompactSupport U ∧
      (∀ t x, spatialDivergence U t x = 0) ∧
      (∀ (t : ℝ) x, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → U (t, x) = 0) ∧
      (∀ i (p : SpaceTime), p ∈ movingPlateau (c i) (r i) η →
        U p = fun k => v i p.1 k + l i p.1 k * (p.2 k - c i p.1 k)) := by
  refine ⟨spatialCurl (familyPotential c v l r η), ?_⟩
  have hA := contDiff_familyPotential η hc hv hl hr
  have hcompact := hasCompactSupport_familyPotential hη hR hbound htime
  have htimeA : ∀ (t : ℝ) (x : Space), t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
      familyPotential c v l r η (t, x) = 0 := by
    intro t x ht
    exact familyPotential_zero η (fun i => (htime i t ht).1)
      (fun i => (htime i t ht).2) x
  obtain ⟨hsm, hcp, hdiv, htm⟩ := curl_field_properties hA hcompact htimeA
  exact ⟨hsm, hcp, hdiv, htm,
    fun i _ hp => spatialCurl_familyPotential_on_plateau hη hc hv hl hr htrace hdis i hp⟩

theorem smooth_compact_bounds {U : Field} (hU : ContDiff ℝ ∞ U)
    (hs : HasCompactSupport U) :
    ∃ M K : NNReal, (∀ p, ‖U p‖ ≤ M) ∧ LipschitzWith K U := by
  obtain ⟨M, hM, hMb⟩ := (hs.isCompact_range hU.continuous).isBounded.exists_pos_norm_le
  obtain ⟨K, hK, hKb⟩ := ((hs.fderiv ℝ).isCompact_range
    (hU.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨⟨M, hM.le⟩, ⟨K, hK.le⟩, (fun p => hMb _ ⟨p, rfl⟩), ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hU.differentiable (by simp))
  intro p
  exact hKb _ ⟨p, rfl⟩

theorem globalFlow_of_bounded_lipschitz {U : Field} {M K : NNReal}
    (hcont : Continuous U) (hbound : ∀ p, ‖U p‖ ≤ M)
    (hlip : ∀ t, LipschitzWith K (fun x => U (t, x))) :
    ∃ Φ, IsGlobalFlow U Φ := by
  have localSolution (x : Space) (r : ℝ) (hr : 0 < r) :
      ∃ α : ℝ → Space, α 0 = x ∧
        ∀ t ∈ Set.Ioo (-r) r, HasDerivAt α (U (t, α t)) t := by
    let t₀ : Set.Icc (-r) r := ⟨0, by constructor <;> linarith⟩
    let a : NNReal := M * ⟨r, hr.le⟩
    have hpl : IsPicardLindelof (fun t x => U (t, x)) t₀ x a 0 M K := by
      constructor
      · intro t ht
        exact (hlip t).lipschitzOnWith
      · intro y hy
        exact (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn
      · intro t ht y hy
        exact hbound (t, y)
      · change (M : ℝ) * max (r - 0) (0 - (-r)) ≤ (M : ℝ) * r - 0
        simp
    obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨α, hα0, fun t ht => (hα t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)⟩
  have trajectories (x : Space) :
      ∃ γ : ℝ → Space, γ 0 = x ∧ ∀ t, HasDerivAt γ (U (t, γ t)) t := by
    let Radius := {r : ℝ // 0 < r}
    have hlocal (r : Radius) := localSolution x r.1 r.2
    choose α hα0 hα using hlocal
    have compatibility (r s : Radius) (t : ℝ)
        (htr : t ∈ Set.Ioo (-r.1) r.1) (hts : t ∈ Set.Ioo (-s.1) s.1) :
        α r t = α s t := by
      have hm : 0 < min r.1 s.1 := lt_min r.2 s.2
      have he : Set.EqOn (α r) (α s) (Set.Ioo (-min r.1 s.1) (min r.1 s.1)) := by
        apply ODE_solution_unique_of_mem_Ioo
          (v := fun t x => U (t, x)) (s := fun _ => Set.univ) (K := K)
          (t₀ := 0)
        · intro t ht
          exact (hlip t).lipschitzOnWith
        · exact ⟨neg_neg_of_pos hm, hm⟩
        · intro t ht
          exact ⟨hα r t ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ht.1,
            lt_of_lt_of_le ht.2 (min_le_left _ _)⟩, Set.mem_univ _⟩
        · intro t ht
          exact ⟨hα s t ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) ht.1,
            lt_of_lt_of_le ht.2 (min_le_right _ _)⟩, Set.mem_univ _⟩
        · rw [hα0, hα0]
      apply he
      constructor
      · rw [← max_neg_neg]
        exact max_lt htr.1 hts.1
      · exact lt_min htr.2 hts.2
    let ρ : ℝ → Radius := fun t => ⟨|t| + 1, by positivity⟩
    have hin (t : ℝ) : t ∈ Set.Ioo (-(ρ t).1) (ρ t).1 := by
      have hp := le_abs_self t
      have hn := neg_abs_le t
      change -(|t| + 1) < t ∧ t < |t| + 1
      constructor <;> linarith
    let γ : ℝ → Space := fun t => α (ρ t) t
    have heq (r : Radius) (t : ℝ) (ht : t ∈ Set.Ioo (-r.1) r.1) : γ t = α r t :=
      compatibility (ρ t) r t (hin t) ht
    refine ⟨γ, hα0 (ρ 0), ?_⟩
    intro t
    have hev : γ =ᶠ[nhds t] α (ρ t) := by
      filter_upwards [isOpen_Ioo.mem_nhds (hin t)] with s hs
      exact heq (ρ t) s hs
    exact (hα (ρ t) t (hin t)).congr_of_eventuallyEq hev
  choose γ hγ0 hγ using trajectories
  refine ⟨fun t x => γ x t, (fun x => hγ0 x), (fun t x => hγ x t), ?_⟩
  intro x ν hν0 hν t
  have he : ν = γ x := ODE_solution_unique_univ
    (v := fun t x => U (t, x)) (s := fun _ => Set.univ) (K := K) (t₀ := 0)
    (fun t => (hlip t).lipschitzOnWith)
    (fun t => ⟨hν t, Set.mem_univ _⟩)
    (fun t => ⟨hγ x t, Set.mem_univ _⟩) (hν0.trans (hγ0 x).symm)
  exact congrFun he t

theorem smooth_compact_globalFlow {U : Field} (hU : ContDiff ℝ ∞ U)
    (hs : HasCompactSupport U) : ∃ Φ, IsGlobalFlow U Φ := by
  obtain ⟨M, K, hb, hl⟩ := smooth_compact_bounds hU hs
  apply globalFlow_of_bounded_lipschitz hU.continuous hb
  intro t
  simpa only [mul_one, Function.comp_def] using hl.comp (LipschitzWith.prodMk_left t)

theorem trace_zero_of_determinant_one {d : ℝ → Space} {l : Space} {t : ℝ}
    (hd : ∀ j, HasDerivAt (fun s => d s j) (l j * d t j) t)
    (hdet : ∀ s, ∏ j : Fin 3, d s j = 1) : ∑ j : Fin 3, l j = 0 := by
  have he : (fun s => d s 0 * d s 1 * d s 2) = fun _ => (1 : ℝ) := by
    funext s
    simpa only [Fin.prod_univ_three] using hdet s
  have hp := ((hd 0).mul (hd 1)).mul (hd 2)
  change HasDerivAt (fun s => d s 0 * d s 1 * d s 2) _ t at hp
  rw [he] at hp
  have hz := hp.unique (hasDerivAt_const t (1 : ℝ))
  dsimp only [Pi.mul_apply] at hz
  have ht : d t 0 * d t 1 * d t 2 = 1 := by
    simpa only [Fin.prod_univ_three] using hdet t
  rw [Fin.sum_univ_three]
  calc
    l 0 + l 1 + l 2 = (l 0 + l 1 + l 2) * (d t 0 * d t 1 * d t 2) := by rw [ht, mul_one]
    _ = 0 := by nlinarith only [hz]

def affineTrajectory (c d : ℝ → Space) (a x : Space) (t : ℝ) : Space :=
  fun j => c t j + d t j * (x j - a j)

theorem affineTrajectory_initial {c d : ℝ → Space} {a : Space}
    (hc : c 0 = a) (hd : d 0 = 1) (x : Space) : affineTrajectory c d a x 0 = x := by
  ext j
  simp [affineTrajectory, hc, hd]

theorem hasDerivAt_affineTrajectory {c d : ℝ → Space} {v l : Space} {t : ℝ}
    (hc : HasDerivAt c v t)
    (hd : ∀ j, HasDerivAt (fun s => d s j) (l j * d t j) t) (a x : Space) :
    HasDerivAt (affineTrajectory c d a x)
      (fun j => v j + l j * (affineTrajectory c d a x t j - c t j)) t := by
  apply hasDerivAt_pi.mpr
  intro j
  simpa only [affineTrajectory, add_sub_cancel_left, mul_assoc] using
    (hasDerivAt_pi.mp hc j).fun_add ((hd j).mul_const (x j - a j))

theorem affineTrajectory_in_plateau {c d : ℝ → Space} (a h : Space)
    {η M : ℝ} (hη : 0 < η) (hM : 0 < M)
    (hd : ∀ t j, 0 < d t j) (hdM : ∀ t j, d t j ≤ M)
    {x : Space} (hx : x ∈ openBox a h (η / (2 * M))) (t : ℝ) :
    (t, affineTrajectory c d a x t) ∈
      movingPlateau c (fun s j => d s j * h j) η := by
  have hδ : 0 < η / (2 * M) := div_pos hη (by positivity)
  have hmδ : M * (η / (2 * M)) = η / 2 := by field_simp
  have hp := affine_openBox_control a (c t) h (d t) hδ.le (hd t) (hdM t) hx
  rw [hmδ] at hp
  intro j
  exact (hp j).trans (by linarith)

theorem realizes_supplied_separated_motion {n : ℕ}
    (a h : Fin n → Space) {c v l d : Fin n → ℝ → Space}
    {η M R : ℝ} (hη : 0 < η) (hM : 0 < M) (hR : 0 ≤ R)
    (hc : ∀ i, ContDiff ℝ ∞ (c i)) (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (hl : ∀ i, ContDiff ℝ ∞ (l i)) (hd : ∀ i, ContDiff ℝ ∞ (d i))
    (hc0 : ∀ i, c i 0 = a i) (hd0 : ∀ i, d i 0 = 1)
    (hcv : ∀ i t, HasDerivAt (c i) (v i t) t)
    (hdl : ∀ i t j, HasDerivAt (fun s => d i s j) (l i t j * d i t j) t)
    (hdet : ∀ i t, ∏ j : Fin 3, d i t j = 1)
    (hdpos : ∀ i t j, 0 < d i t j) (hdM : ∀ i t j, d i t j ≤ M)
    (hdis : ∀ t, Pairwise fun i j =>
      Disjoint (realBox (c i t) (fun k => d i t k * h i k + 2 * η))
        (realBox (c j t) (fun k => d j t k * h j k + 2 * η)))
    (hbound : ∀ i t, t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
      ∀ j, |c i t j| + d i t j * h i j + 2 * η ≤ R)
    (htime : ∀ i t, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
      v i t = 0 ∧ l i t = 0) :
    ∃ (U : Field) (Φ : ℝ → Space → Space),
      ContDiff ℝ ∞ U ∧ HasCompactSupport U ∧
      (∀ t x, spatialDivergence U t x = 0) ∧
      (∀ (t : ℝ) x, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → U (t, x) = 0) ∧
      IsGlobalFlow U Φ ∧
      (∀ i, ∃ O : Set Space, IsOpen O ∧ realBox (a i) (h i) ⊆ O ∧
        ∀ x ∈ O, ∀ t, Φ t x = affineTrajectory (c i) (d i) (a i) x t) := by
  let r : Fin n → ℝ → Space := fun i t j => d i t j * h i j
  have hr (i : Fin n) : ContDiff ℝ ∞ (r i) := by
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_pi.mp (hd i) j).mul contDiff_const
  have htrace (i : Fin n) (t : ℝ) : ∑ j : Fin 3, l i t j = 0 :=
    trace_zero_of_determinant_one (hdl i t) (hdet i)
  obtain ⟨U, hUsm, hUcp, hUdiv, hUt, hUplat⟩ :=
    localized_separated_motion hη hR hc hv hl hr htrace hdis hbound htime
  obtain ⟨Φ, hΦ⟩ := smooth_compact_globalFlow hUsm hUcp
  refine ⟨U, Φ, hUsm, hUcp, hUdiv, hUt, hΦ, ?_⟩
  intro i
  have hδ : 0 < η / (2 * M) := div_pos hη (by positivity)
  refine ⟨openBox (a i) (h i) (η / (2 * M)), isOpen_openBox _ _ _,
    realBox_subset_openBox _ _ hδ, ?_⟩
  intro x hx t
  apply Eq.symm
  apply hΦ.2.2 x (affineTrajectory (c i) (d i) (a i) x)
    (affineTrajectory_initial (hc0 i) (hd0 i) x)
  intro s
  have hp := affineTrajectory_in_plateau (c := c i) (a i) (h i) hη hM (hdpos i) (hdM i) hx s
  rw [hUplat i _ hp]
  exact hasDerivAt_affineTrajectory (hcv i s) (hdl i s) (a i) x

theorem contDiff_motion_deriv {c : ℝ → Space} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (deriv c) :=
  (hc.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

noncomputable def diagonalLogVelocity (d : ℝ → Space) (t : ℝ) : Space :=
  fun j => deriv d t j / d t j

theorem contDiff_diagonalLogVelocity {d : ℝ → Space}
    (hd : ContDiff ℝ ∞ d) (hpos : ∀ t j, 0 < d t j) :
    ContDiff ℝ ∞ (diagonalLogVelocity d) := by
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_pi.mp (contDiff_motion_deriv hd) j).div (contDiff_pi.mp hd j)
    (fun t => ne_of_gt (hpos t j))

theorem hasDerivAt_diagonalLogVelocity {d : ℝ → Space}
    (hd : ContDiff ℝ ∞ d) (hpos : ∀ t j, 0 < d t j) (t : ℝ) (j : Fin 3) :
    HasDerivAt (fun s => d s j) (diagonalLogVelocity d t j * d t j) t := by
  rw [diagonalLogVelocity, div_mul_cancel₀ _ (ne_of_gt (hpos t j))]
  exact hasDerivAt_pi.mp ((hd.differentiable (by simp) t).hasDerivAt) j

theorem deriv_zero_outside_interval {f : ℝ → Space} {a b : Space} {u v t : ℝ}
    (hbefore : ∀ s, s ≤ u → f s = a) (hafter : ∀ s, v ≤ s → f s = b)
    (ht : t ∉ Set.Icc u v) : deriv f t = 0 := by
  by_cases hlo : t < u
  · have he : f =ᶠ[nhds t] fun _ => a := by
      filter_upwards [eventually_lt_nhds hlo] with s hs
      exact hbefore s hs.le
    simp [deriv, he.fderiv_eq]
  · have hhi : v < t := by
      by_contra hh
      exact ht ⟨le_of_not_gt hlo, le_of_not_gt hh⟩
    have he : f =ᶠ[nhds t] fun _ => b := by
      filter_upwards [eventually_gt_nhds hhi] with s hs
      exact hafter s hs.le
    simp [deriv, he.fderiv_eq]

theorem realizes_stationary_separated_motion {n : ℕ}
    (a h : Fin n → Space) {c d : Fin n → ℝ → Space}
    {η M R : ℝ} (hη : 0 < η) (hM : 0 < M) (hR : 0 ≤ R)
    (hc : ∀ i, ContDiff ℝ ∞ (c i)) (hd : ∀ i, ContDiff ℝ ∞ (d i))
    (hstart : ∀ i t, t ≤ (1 / 4 : ℝ) → c i t = a i ∧ d i t = 1)
    (hend : ∀ i t, (3 / 4 : ℝ) ≤ t → c i t = c i 1 ∧ d i t = d i 1)
    (hdet : ∀ i t, ∏ j : Fin 3, d i t j = 1)
    (hdpos : ∀ i t j, 0 < d i t j) (hdM : ∀ i t j, d i t j ≤ M)
    (hdis : ∀ t, Pairwise fun i j =>
      Disjoint (realBox (c i t) (fun k => d i t k * h i k + 2 * η))
        (realBox (c j t) (fun k => d j t k * h j k + 2 * η)))
    (hbound : ∀ i t, t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
      ∀ j, |c i t j| + d i t j * h i j + 2 * η ≤ R) :
    ∃ (U : Field) (Φ : ℝ → Space → Space),
      ContDiff ℝ ∞ U ∧ HasCompactSupport U ∧
      (∀ t x, spatialDivergence U t x = 0) ∧
      (∀ (t : ℝ) x, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → U (t, x) = 0) ∧
      IsGlobalFlow U Φ ∧
      (∀ i, ∃ O : Set Space, IsOpen O ∧ realBox (a i) (h i) ⊆ O ∧
        ∀ x ∈ O, ∀ t, Φ t x = affineTrajectory (c i) (d i) (a i) x t) := by
  apply realizes_supplied_separated_motion a h hη hM hR hc
    (fun i => contDiff_motion_deriv (hc i))
    (fun i => contDiff_diagonalLogVelocity (hd i) (hdpos i)) hd
    (fun i => (hstart i 0 (by norm_num)).1)
    (fun i => (hstart i 0 (by norm_num)).2)
    (fun i t => ((hc i).differentiable (by simp) t).hasDerivAt)
    (fun i => hasDerivAt_diagonalLogVelocity (hd i) (hdpos i))
    hdet hdpos hdM hdis hbound
  intro i t ht
  constructor
  · exact deriv_zero_outside_interval (fun s hs => (hstart i s hs).1)
      (fun s hs => (hend i s hs).1) ht
  · have hz := deriv_zero_outside_interval (fun s hs => (hstart i s hs).2)
      (fun s hs => (hend i s hs).2) ht
    ext j
    simp [diagonalLogVelocity, hz]

end BoxTransport.Routing

end

end OAI
