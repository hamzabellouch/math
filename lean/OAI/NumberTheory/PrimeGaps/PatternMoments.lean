import OAI.NumberTheory.PrimeGaps.Detectors

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem box_series_scaled_tendsto {s K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → Fin s → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop, ∀ j,a X j≤K*blockLength lam X) (c : ℂ) :
    Tendsto (fun X : ℕ =>
      (∑ u∈distinctBox (h:=blockLength lam X) (fun j => (a X j:ℤ)),
        (singularSeries (Finset.univ.image (boxTuple (fun j => (a X j:ℤ)) u)):ℂ)*c)/
        (Real.log X:ℂ)^s) atTop (𝓝 ((lam:ℂ)^s*c)) := by
  classical
  let H := blockLength lam
  let az := fun X j => (a X j:ℤ)
  have hL : ∀ᶠ X : ℕ in atTop,0<Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact log_pos_of_two_le hX
  have hHL := blockLength_ratio_tendsto hlam.le
  have hmean : Tendsto (fun X => singularBoxMean (h:=H X) (az X)) atTop (𝓝 1) := by
    apply uniform_singularBoxMean_tendsto s (K:=K+1) (by omega) H az (blockLength_tendsto hlam)
    filter_upwards [ha] with X hX
    exact natural_boxDiameterBound (a X) hX
  have hh := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hHL).pow s).mul
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hmean)
  have hh' := hh.mul_const c
  simp only [Complex.ofReal_one,mul_one] at hh'
  apply hh'.congr'
  filter_upwards [hL,(blockLength_tendsto hlam).eventually_ge_atTop 1] with X hLX hHX
  have hHC : ((H X:ℕ):ℂ)≠0 := by exact_mod_cast (show H X≠0 by dsimp [H]; omega)
  have hLC : (Real.log X:ℂ)≠0 := by exact_mod_cast ne_of_gt hLX
  change (((H X:ℝ)/(Real.log X):ℝ):ℂ)^s * (singularBoxMean (h:=H X) (az X):ℂ)*c = _
  simp only [←Finset.sum_mul,←Complex.ofReal_sum,singularBoxMean,
    Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  dsimp only [az,H]
  dsimp only [H] at hHC
  rw [div_pow]
  field_simp [hHC]

theorem distinctBox_init {s h : ℕ} (a : Fin (s+1) → ℕ) (u : Fin (s+1) → Fin h)
    (hu : u∈distinctBox (fun j => (a j:ℤ))) :
    (fun j : Fin s => u j.castSucc)∈distinctBox (fun j : Fin s => (a j.castSucc:ℤ)) := by
  classical
  simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
  exact hu.comp (Fin.castSucc_injective s)

theorem patternBoxShifts_ne_mark {n s h : ℕ} (p : Fin n → Fin s)
    (a : Fin (s+1) → ℕ) (u : Fin (s+1) → Fin h)
    (hu : u∈distinctBox (fun j => (a j:ℤ))) (i : Fin n) :
    patternBoxShifts p (fun j => a j.castSucc) (fun j => u j.castSucc) i≠
      a (Fin.last s)+(u (Fin.last s):ℕ) := by
  intro he
  have hj : boxTuple (fun j => (a j:ℤ)) u (p i).castSucc=
      boxTuple (fun j => (a j:ℤ)) u (Fin.last s) := by
    dsimp only [patternBoxShifts] at he
    dsimp only [boxTuple]
    exact_mod_cast he
  have hi := (Finset.mem_filter.mp hu).2 hj
  exact Fin.castSucc_ne_last (p i) hi

theorem marked_patternBoxShifts_image {n s h : ℕ} (p : Fin n → Fin s)
    (hp : Function.Surjective p) (a : Fin (s+1) → ℕ) (u : Fin (s+1) → Fin h) :
    insert ((a (Fin.last s)+(u (Fin.last s):ℕ):ℕ):ℤ)
      (Finset.univ.image fun i => (patternBoxShifts p (fun j => a j.castSucc)
        (fun j => u j.castSucc) i:ℤ))=
      Finset.univ.image (boxTuple (fun j => (a j:ℤ)) u) := by
  classical
  rw [patternBoxShifts_image p hp]
  ext x
  simp only [Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (rfl | ⟨j,rfl⟩)
    · exact ⟨Fin.last s,by simp only [boxTuple,Nat.cast_add]⟩
    · exact ⟨j.castSucc,rfl⟩
  · rintro ⟨j,rfl⟩
    cases j using Fin.lastCases with
    | last => left; simp only [boxTuple,Nat.cast_add]
    | cast j => exact Or.inr ⟨j,rfl⟩

theorem marked_box_pattern_limit (hBV : BombieriVinogradov) {n s K : ℕ}
    {lam : ℝ} (hlam : 0<lam) (p : Fin n → Fin s) (hp : Function.Surjective p)
    (a : ℕ → Fin (s+1) → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop, ∀ j,a X j≤K*blockLength lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ u∈distinctBox (h:=blockLength lam X) (fun j => (a X j:ℤ)),
      (average X (fun m => divisorSum X F m
        (patternBoxShifts p (fun j => a X j.castSucc) (fun j => u j.castSucc))*
        theta (m+(a X (Fin.last s)+(u (Fin.last s):ℕ)))):ℂ)/(Real.log X:ℂ)) atTop
      (𝓝 ((lam:ℂ)^(s+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) hF hFs) (shiftFamily (fun i => ((p i).val:ℤ))))) := by
  classical
  let B := shiftFamily (fun i => ((p i).val:ℤ))
  let c := kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
    (fun v => (F v.ofLp:ℂ)) hF hFs) B
  let H := blockLength lam
  let az := fun X j => (a X j:ℤ)
  let f := fun X (u : Fin (s+1) → Fin (H X)) =>
    (average X (fun m => divisorSum X F m
      (patternBoxShifts p (fun j => a X j.castSucc) (fun j => u j.castSucc))*
      theta (m+(a X (Fin.last s)+(u (Fin.last s):ℕ)))):ℂ)/(Real.log X:ℂ)
  let g := fun X (u : Fin (s+1) → Fin (H X)) =>
    (singularSeries (Finset.univ.image (boxTuple (az X) u)):ℂ)*c
  have hD : (0:ℝ)<(K+1:ℕ)*lam := mul_pos (by positivity) hlam
  have hH : ∀ᶠ X : ℕ in atTop, (((K+1)*H X:ℕ):ℝ)≤((K+1:ℕ):ℝ)*lam*(Real.log X)^(1:ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    simpa only [Nat.cast_mul,Real.rpow_one,mul_assoc] using
      mul_le_mul_of_nonneg_left (blockLength_le_mul_log hlam.le hX) (Nat.cast_nonneg (K+1))
  obtain ⟨E,hE,herr⟩ := marked_average_uniform_asymptotic hBV F rho hrho hrhohalf hbudget
    hF hFs M hM hbound B (shiftFamily_nonempty _) s 2 (by omega)
    (surjective_shiftFamily_sign_sum p hp) (fun X => (K+1)*H X) hD hH
  have hL : ∀ᶠ X : ℕ in atTop,0<Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    exact log_pos_of_two_le hX
  have herror : ∀ᶠ X in atTop, ∀ u∈distinctBox (az X),
      ‖(Real.log X:ℂ)^(s+1)*f X u-g X u‖≤E X := by
    filter_upwards [herr,ha,hL,blockLength_densityCutoff_eventually hlam.le (2*(K+1))]
      with X hX haX hLX hcut
    intro u hu
    have hb (j : Fin (s+1)) : a X j+(u j:ℕ)≤(K+1)*H X := by
      have hi := (u j).isLt
      have hh := haX j
      dsimp [H] at hi
      dsimp [H]
      rw [Nat.add_mul,one_mul]
      omega
    have hz := hX (patternBoxShifts p (fun j => a X j.castSucc) (fun j => u j.castSucc))
      (patternBoxShifts_family p _ _ (distinctBox_init (a X) u hu))
      (a X (Fin.last s)+(u (Fin.last s):ℕ)) (hb (Fin.last s))
      (patternBoxShifts_ne_mark p (a X) u hu) ((K+1)*H X)
      (fun i => hb (p i).castSucc) (hb (Fin.last s))
      (by simpa only [Nat.mul_assoc] using hcut)
    rw [marked_patternBoxShifts_image p hp] at hz
    have hLC : (Real.log X:ℂ)≠0 := by exact_mod_cast ne_of_gt hLX
    convert hz using 1
    dsimp [f,g,c,az]
    congr 1
    rw [pow_succ]
    field_simp
  have he := box_sum_errors_tendsto_zero (s+1) H az (fun X => Real.log X) E lam f g
    hL (blockLength_ratio_tendsto hlam.le) hE herror
  have hmain : Tendsto (fun X => (∑ u∈distinctBox (az X),g X u)/(Real.log X:ℂ)^(s+1))
      atTop (𝓝 ((lam:ℂ)^(s+1)*c)) := by
    simpa only [g,az,H,←Finset.sum_mul] using box_series_scaled_tendsto hlam a ha c
  have hh := he.add hmain
  simp only [sub_add_cancel,zero_add] at hh
  exact hh

noncomputable def patternLabels {ι : Type*} [Fintype ι] (r : Setoid ι) :
    ι → Fin (Fintype.card (Quotient r)) :=
  fun i => Fintype.equivFin (Quotient r) (Quotient.mk r i)

theorem patternLabels_surjective {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Function.Surjective (patternLabels r) := by
  intro j
  obtain ⟨i,hi⟩ := Quotient.mk_surjective ((Fintype.equivFin (Quotient r)).symm j)
  refine ⟨i,?_⟩
  simp only [patternLabels,hi,Equiv.apply_symm_apply]

theorem patternTupleEquiv_labels {n : ℕ} (r : Setoid (Fin n)) (h a : ℕ)
    (b : {b // b∈patternClass (α:=Fin h) r}) :
    patternBoxShifts (patternLabels r) (fun _ => a)
      (patternTupleEquiv r h a b).val=(fun i => a+(b.val i:ℕ)) := by
  funext i
  simp only [patternBoxShifts,patternLabels,patternTupleEquiv_apply,Equiv.symm_apply_apply]
  rfl

theorem pattern_sum_average_eq_box {n : ℕ} (r : Setoid (Fin n)) (h a X : ℕ)
    (F : (Fin n → ℝ) → ℝ) :
    (∑ b∈patternClass (α:=Fin h) r,
      (average X (fun m => divisorSum X F m (fun i => a+(b i:ℕ))):ℂ))=
    ∑ u∈distinctBox (s:=Fintype.card (Quotient r)) (h:=h) (fun _ => (a:ℤ)),
      (average X (fun m => divisorSum X F m (patternBoxShifts (patternLabels r) (fun _ => a) u)):ℂ) := by
  classical
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (patternTupleEquiv r h a)
  intro b
  rw [patternTupleEquiv_labels]

theorem unmarked_pattern_limit {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (r : Setoid (Fin (n+1))) (a : ℕ → ℕ)
    (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
      (average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ)) atTop
      (𝓝 ((lam:ℂ)^Fintype.card (Quotient r)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ))))) := by
  have hh := unmarked_box_pattern_limit hlam (patternLabels r) (patternLabels_surjective r)
    (fun X _ => a X) (ha.mono (fun _ h _ => h)) F rho hrho hrho1 hbudget hF hFs M hM hbound
  have he : (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
      (average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ))=
      (fun X : ℕ => ∑ u∈distinctBox (h:=blockLength lam X) (fun _ => (a X:ℤ)),
        (average X (fun m => divisorSum X F m (patternBoxShifts (patternLabels r) (fun _ => a X) u)):ℂ)) := by
    funext X
    exact pattern_sum_average_eq_box r _ _ _ F
  rw [he]
  exact hh

theorem unmarked_labeled_expansion_limit {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M)
    (k : Setoid (Fin (n+1)) → ℂ) :
    Tendsto (fun X : ℕ => ∑ b : Fin (n+1) → Fin (blockLength lam X),
      k (Setoid.ker b)*(average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin (n+1)),k r*((lam:ℂ)^Fintype.card (Quotient r)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ)))))) := by
  classical
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (unmarked_pattern_limit hlam r a ha F rho hrho hrho1 hbudget hF hFs M hM hbound).const_mul (k r))
  apply hh.congr'
  exact Eventually.of_forall (fun X => by
    dsimp only
    calc
      (∑ r : Setoid (Fin (n+1)), k r*∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
        (average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ)) =
        ∑ r : Setoid (Fin (n+1)), ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
          k (Setoid.ker b)*(average X (fun m => divisorSum X F m (fun i => a X+(b i:ℕ))):ℂ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(mem_patternClass r b).mp hb]
      _ = _ := sum_patterns _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl)

def permutedLabels {n : ℕ} (e : Equiv.Perm (Fin n)) : Fin (n+n) → Fin n := Fin.append id e

theorem permutedLabels_fiber_sum {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) {K : Type*} [AddCommMonoid K]
    (w : Fin (n+n) → K) :
    (∑ i∈Finset.univ.filter (fun i => permutedLabels e i=r), w i)=w (r.castAdd n)+w ((e.symm r).natAdd n) := by
  classical
  rw [Finset.sum_filter,Fin.sum_univ_add]
  simp [permutedLabels,←Equiv.eq_symm_apply]

@[simp] theorem permutedLabels_fiber_card {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) :
    (Finset.univ.filter fun i => permutedLabels e i=r).card=2 := by
  simpa using permutedLabels_fiber_sum e r (fun _ => (1:ℕ))

theorem permutedLabels_classical_fiber {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) :
    @Finset.filter (Fin (n+n)) (fun i => permutedLabels e i=r)
      (fun _ => Classical.propDecidable _) Finset.univ =
      Finset.univ.filter (fun i => permutedLabels e i=r) := by
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem permutedLabels_kernel {n : ℕ} (e : Equiv.Perm (Fin n)) (w : Fin (n+n) → ℂ) :
    familyKernel (fiberSubsetFamily (permutedLabels e) Finset.univ) w =
      (∏ i,w i)*(∏ i : Fin n,(w (i.castAdd n)+w ((e.symm i).natAdd n))⁻¹) := by
  rw [familyKernel_small_fibers (permutedLabels e) Finset.univ (fun i => Finset.mem_univ _) (by
    intro r _
    rw [permutedLabels_classical_fiber,permutedLabels_fiber_card])]
  simp only [permutedLabels_classical_fiber,permutedLabels_fiber_card,Finset.filter_true,
    permutedLabels_fiber_sum]

noncomputable def permutedRay {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) : EuclideanSpace ℝ (Fin (n+n)) :=
  EuclideanSpace.single (i.castAdd n) 1+EuclideanSpace.single ((e.symm i).natAdd n) 1

theorem permutedRay_frequency {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) (u : EuclideanSpace ℝ (Fin (n+n))) :
    laplaceFrequency (fourierCoordinateSum (Fin (n+n))) (permutedRay e i) u =
      frequencyW (u (i.castAdd n))+frequencyW (u ((e.symm i).natAdd n)) := by
  unfold permutedRay
  simp only [laplaceFrequency,map_add,inner_add_right,Complex.ofReal_add,
    fourierCoordinateSum_apply]
  simp [frequencyW,EuclideanSpace.inner_single_right]
  ring

theorem permutedRay_positive {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    0<fourierCoordinateSum (Fin (n+n)) (permutedRay e i) := by
  have h := congrArg Complex.re (permutedRay_frequency e i 0)
  simp only [laplaceFrequency_re,Complex.add_re,frequencyW_re] at h
  rw [h]
  norm_num

theorem rayVector_permuted {n : ℕ} (e : Equiv.Perm (Fin n)) (y : Fin n → ℝ) :
    (rayVector (permutedRay e) y).ofLp=Fin.append y (y ∘ e) := by
  classical
  ext i
  cases i using Fin.addCases with
  | left i => simp [rayVector,permutedRay,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,castAdd_ne_addNat_self]
  | right i =>
    have he (x : Fin n) : i=e.symm x ↔ x=e i := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [h]; simp
    simp [rayVector,permutedRay,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,addNat_ne_castAdd_self,he]

theorem permuted_kernelConstant {n : ℕ} (e : Equiv.Perm (Fin n))
    (F : EuclideanSpace ℝ (Fin (n+n)) → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n))) F hF hFs)
      (fiberSubsetFamily (permutedLabels e) Finset.univ) =
      ∫ y, signedDirections (coordinateDirectionList (Fin (n+n))) F (rayVector (permutedRay e) y)
        ∂positiveOrthantMeasure (Fin n) := by
  rw [←sourceFourier_derivative_laplace (fourierCoordinateSum (Fin (n+n)))
    (coordinateDirectionList (Fin (n+n))) F hF hFs (permutedRay e) (permutedRay_positive e)]
  unfold kernelConstant
  apply integral_congr_ae
  filter_upwards [] with u
  rw [contourKernel,permutedLabels_kernel,coordinateDirectionList_multiplier]
  simp only [permutedRay_frequency,mul_assoc]

theorem cumulative_tensor_permuted_kernel {n : ℕ} (e : Equiv.Perm (Fin n)) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau) (hsym : SymmetricFunction f)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n)))
      (fun v => (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) hF hFs)
      (fiberSubsetFamily (permutedLabels e) Finset.univ) = (l2Mass f:ℂ) := by
  rw [permuted_kernelConstant]
  have he : (∫ y, signedDirections (coordinateDirectionList (Fin (n+n)))
      (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
        (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) (rayVector (permutedRay e) y)
      ∂positiveOrthantMeasure (Fin n)) =
      ∫ y, (f y^2:ℂ) ∂positiveOrthantMeasure (Fin n) := by
    apply integral_congr_ae
    rw [positiveOrthantMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
    rw [cumulativeProfile_signed_full (tau+tau) (tensorProfile f f)
      (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs)
      (tensorProfile_tsupport f f hsupp hsupp)]
    · rw [rayVector_permuted,tensorProfile_append,hsym,pow_two]
      simp only [Complex.ofReal_mul]
    · intro i
      rw [rayVector_permuted]
      cases i using Fin.addCases with
      | left i => simpa using (hy i (Set.mem_univ i)).le
      | right i => simpa using (hy (e i) (Set.mem_univ (e i))).le
  rw [he]
  simp_rw [←Complex.ofReal_pow]
  rw [integral_complex_ofReal,positiveOrthantMeasure_eq_restrict]
  congr 1
  unfold l2Mass
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfz : f y=0 := by
    by_contra hne
    exact hy (fun i _ => (hsupp (subset_tsupport f hne)).1 i)
  simp [hfz]

def functionPerm {ι α : Type*} (e : Equiv.Perm ι) : (ι → α) ≃ (ι → α) where
  toFun f := f ∘ e
  invFun f := f ∘ e.symm
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

theorem divisorCoefficient_perm {n X : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : SymmetricFunction F) (e : Equiv.Perm (Fin n)) (d : Fin n → ℕ) :
    divisorCoefficient X F (d ∘ e)=divisorCoefficient X F d := by
  unfold divisorCoefficient
  have he : logCoordinates X (d ∘ e)=(logCoordinates X d) ∘ e := rfl
  rw [he,hF]
  congr 1
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

theorem divisorSum_perm {n X m : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : SymmetricFunction F) (e : Equiv.Perm (Fin n)) (b : Fin n → ℕ) :
    divisorSum X F m (b ∘ e)=divisorSum X F m b := by
  classical
  unfold divisorSum
  symm
  apply Finset.sum_equiv (functionPerm e)
  · intro d
    simp only [Fintype.mem_piFinset,functionPerm,Equiv.coe_fn_mk,Function.comp_apply]
    exact e.surjective.forall
  · intro d _
    exact (divisorCoefficient_perm F hF e d).symm

theorem injective_same_range_perm {n : ℕ} {α : Type*}
    (a b : Fin n → α) (hb : Function.Injective b)
    (hab : Set.range a=Set.range b) : ∃ e : Equiv.Perm (Fin n), b=a ∘ e := by
  classical
  have hs : ∀ i,∃ j,a j=b i := by
    intro i
    have : b i ∈ Set.range a := hab.symm ▸ Set.mem_range_self i
    exact this
  choose e he using hs
  have hei : Function.Injective e := by
    intro i j hij
    apply hb
    rw [←he i,←he j,hij]
  exact ⟨Equiv.ofBijective e ⟨hei,Finite.surjective_of_injective hei⟩,by funext i; exact (he i).symm⟩

noncomputable def weightedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) (m : ℕ) : ℝ :=
  ∑ b : Fin n → Fin h, k (Setoid.ker b)*divisorSum X F m (fun i => a+(b i:ℕ))

noncomputable def tensorCoefficient {n p : ℕ}
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) : Setoid (Fin (n+p)) → ℝ :=
  fun r => k (Setoid.comap (Fin.castAdd p) r)*l (Setoid.comap (Fin.natAdd n) r)

@[simp] theorem append_ker_left {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.castAdd p) (Setoid.ker (Fin.append b c))=Setoid.ker b := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.castAdd p)=Fin.append b c (j.castAdd p) ↔ b i=b j
  simp only [Fin.append_left]

@[simp] theorem append_ker_right {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.natAdd n) (Setoid.ker (Fin.append b c))=Setoid.ker c := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.natAdd n)=Fin.append b c (j.natAdd n) ↔ c i=c j
  simp only [Fin.append_right]

theorem weightedBlock_mul {n p : ℕ} (X h a m : ℕ)
    (F : (Fin n → ℝ) → ℝ) (G : (Fin p → ℝ) → ℝ)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) :
    weightedBlock X h a F k m * weightedBlock X h a G l m =
    weightedBlock X h a (tensorProfile F G) (tensorCoefficient k l) m := by
  classical
  unfold weightedBlock
  rw [Finset.sum_mul_sum,←Finset.sum_product']
  apply Finset.sum_equiv (Fin.appendEquiv n p)
  · intro bc; simp
  intro bc _
  rw [show (Fin.appendEquiv n p) bc=Fin.append bc.1 bc.2 from rfl]
  simp only [tensorCoefficient,append_ker_left,append_ker_right]
  have he : (fun i => a+((Fin.append bc.1 bc.2 i :Fin h):ℕ))=
      Fin.append (fun i => a+(bc.1 i:ℕ)) (fun i => a+(bc.2 i:ℕ)) := by
    funext i
    cases i using Fin.addCases <;> simp
  rw [he,divisorSum_tensor]
  ring

theorem average_weightedBlock (X h a : ℕ) {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) :
    average X (weightedBlock X h a F k)=
    ∑ b : Fin n → Fin h, k (Setoid.ker b)*average X (fun m => divisorSum X F m (fun i => a+(b i:ℕ))) := by
  unfold weightedBlock
  rw [average_finset_sum]
  simp only [average_const_mul]

end LargePrimeGaps

end OAI
