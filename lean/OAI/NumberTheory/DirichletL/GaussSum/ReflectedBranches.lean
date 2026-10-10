import OAI.NumberTheory.DirichletL.CubicSieve.NormalizedMass

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic LocalReflectionBrackets

def reflectedLocalPiece (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (j : ℕ) (e : Fin 3) (n b : O) : ℂ :=
  if j=4 then exceptionalPiece P e n b
  else if e=0 then bracket (actualSextic P hg) j (Ideal.Quotient.mk P (n*b^3)) else 0

def reflectedLocalSize (P : Ideal O) [P.IsMaximal] (j : ℕ) (e : Fin 3) : ℝ :=
  if j=4 then (if e=0 then (rootCard (O ⧸ P))⁻¹ else rootCard (O ⧸ P))
  else if j=0 then (rootCard (O ⧸ P))⁻¹ else 1

def reflectedBranch {ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3) (n b : O) : ℂ :=
  ∏i,reflectedLocalPiece (P i) (hg i) (j i) (e i) n b

theorem bracket_eq_sum_reflectedLocalPiece (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (j : ℕ) (n b : O) :
    bracket (actualSextic P hg) j (Ideal.Quotient.mk P (n*b^3))=
      ∑e : Fin 3, reflectedLocalPiece P hg j e n b := by
  by_cases hj : j=4
  · subst j
    simpa only [reflectedLocalPiece,ite_true] using bracket_four_eq_sum_exceptionalPiece P hg n b
  · simp [reflectedLocalPiece,hj]

theorem prod_bracket_eq_full_branches {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (n b : O) :
    (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (n*b^3)))=
      ∑e : ι→Fin 3,reflectedBranch P hg j e n b := by
  simp_rw [bracket_eq_sum_reflectedLocalPiece]
  simpa only [Fintype.piFinset_univ,reflectedBranch] using
    Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset (Fin 3)))
      (fun i e => reflectedLocalPiece (P i) (hg i) (j i) e n b)

theorem reflectedLocalPiece_norm_le (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (j : ℕ) (e : Fin 3) (n b : O) :
    ‖reflectedLocalPiece P hg j e n b‖≤reflectedLocalSize P j e := by
  have hr : 0<rootCard (O ⧸ P) := rootCard_pos
  by_cases hj4 : j=4
  · subst j
    simpa only [reflectedLocalPiece,reflectedLocalSize,ite_true] using exceptionalPiece_norm_le P e n b
  · by_cases he : e=0
    · rw [reflectedLocalPiece,ite_eq_right hj4,ite_eq_left he,reflectedLocalSize,ite_eq_right hj4]
      by_cases hj0 : j=0
      · subst j
        simpa only [ite_true] using norm_bracket_zero_le (actualSextic P hg) (Ideal.Quotient.mk P (n*b^3))
      · rw [ite_eq_right hj0]
        exact norm_bracket_nonexceptional_le_one _ j hj4 hj0 _
    · simp only [reflectedLocalPiece,ite_eq_right hj4,ite_eq_right he,norm_zero,reflectedLocalSize]
      split_ifs <;> positivity

theorem sqrt_norm_reflectionExtractedDivisor {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) :
    Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ)=
      ∏i,if (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) then rootCard (O ⧸ P i) else 1 := by
  rw [reflectionExtractedDivisor,map_prod,Nat.cast_prod,Real.sqrt_prod]
  · apply Finset.prod_congr rfl
    intro i _
    unfold reflectionExtractedPrime
    split_ifs
    · rw [rootCard_eq_sqrt_absNorm]
    · simp
  · intro i _
    exact Nat.cast_nonneg _

theorem reflectedBranch_norm_bound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) :
    ‖reflectedBranch P hg j e n b‖≤
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ) := by
  have hb : ‖reflectedBranch P hg j e n b‖≤∏i,reflectedLocalSize (P i) (j i) (e i) := by
    rw [reflectedBranch,norm_prod]
    exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      (fun i _ => reflectedLocalPiece_norm_le (P i) (hg i) (j i) (e i) n b)
  apply hb.trans_eq
  rw [sqrt_norm_reflectionExtractedDivisor,sqrt_norm_reflectionExtractedDivisor,
    sqrt_norm_reflectionExtractedDivisor,←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hj4 : j i=4
  · rw [hj4]
    generalize e i=x
    fin_cases x <;> simp [reflectedLocalSize]
  · by_cases hj0 : j i=0
    · simp [reflectedLocalSize,hj0]
    · simp [reflectedLocalSize,hj4,hj0]

theorem reflectionExtractedDivisor_ne_zero {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hP : ∀i,P i≠0) (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) :
    reflectionExtractedDivisor P j e v≠0 := by
  unfold reflectionExtractedDivisor
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  unfold reflectionExtractedPrime
  split_ifs
  · exact hP i
  · exact one_ne_zero

theorem reflectedBranch_normalized_bound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) (U B : ℝ) (hU : 0<U) (hB : 0<B) :
    ‖reflectedBranch P hg j e n b‖ /
      (Real.sqrt ((Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*U)*
        ((Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)*B)) ≤
      1/(Real.sqrt U*B*Real.sqrt ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
        (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ))) := by
  have hn (v : Fin 3) : 0<(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e v
      (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs (v : Fin 3) : 0<Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := Real.sqrt_pos.mpr (hn v)
  have hsu : 0<Real.sqrt U := Real.sqrt_pos.mpr hU
  apply (div_le_div_of_nonneg_right (reflectedBranch_norm_bound P hg j e n b) (by positivity)).trans
  rw [Real.sqrt_mul (hn 1).le,Real.sqrt_mul (hn 0).le]
  have he := Real.sq_sqrt (hn 2).le
  apply le_of_eq
  field_simp [(hs 0).ne', (hs 1).ne', (hs 2).ne', (hn 2).ne', hsu.ne', hB.ne']
  nlinarith

theorem reflectedBranch_divisibility {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (hcop : Pairwise (fun i k => IsCoprime (P i) (P k)))
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) (hne : reflectedBranch P hg j e n b≠0) :
    reflectionExtractedDivisor P j e 1∣Ideal.span {n} ∧
    reflectionExtractedDivisor P j e 2∣Ideal.span {b} ∧
    (∀i,j i=4 → e i=2 → n∉P i) := by
  have hn i : reflectedLocalPiece (P i) (hg i) (j i) (e i) n b≠0 :=
    (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  have hmemn i (hj : j i=4) (he : e i=1) : n∈P i := by
    by_contra hz
    exact hn i (by simp [reflectedLocalPiece,exceptionalPiece,hj,he,hz])
  have hmemb i (hj : j i=4) (he : e i=2) : n∉P i ∧ b∈P i := by
    by_contra hz
    exact hn i (by simp [reflectedLocalPiece,exceptionalPiece,hj,he,hz])
  have hprod (v : Fin 3) (z : O)
      (hz : ∀i,(j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) → z∈P i) :
      reflectionExtractedDivisor P j e v∣Ideal.span {z} := by
    unfold reflectionExtractedDivisor reflectionExtractedPrime
    apply Fintype.prod_dvd_of_coprime
    · intro i k hik
      change IsCoprime (if (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) then P i else 1)
        (if (j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0) then P k else 1)
      by_cases hi : (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0)
      · rw [ite_eq_left hi]
        by_cases hk : (j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0)
        · rw [ite_eq_left hk]
          exact hcop hik
        · rw [ite_eq_right hk]
          exact isCoprime_one_right
      · rw [ite_eq_right hi]
        exact isCoprime_one_left
    · intro i
      split_ifs with hi
      · rw [Ideal.dvd_iff_le,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
        exact hz i hi
      · exact one_dvd _
  refine ⟨hprod 1 n ?_,hprod 2 b ?_,fun i hj he => (hmemb i hj he).1⟩
  · intro i hi
    rcases hi with ⟨hj,he⟩|⟨hj,he⟩
    · exact hmemn i hj he
    · norm_num at he
  · intro i hi
    rcases hi with ⟨hj,he⟩|⟨hj,he⟩
    · exact (hmemb i hj he).2
    · norm_num at he

end

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open MeasureTheory Filter

theorem Vstar_contDiff (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Vstar W) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x=0
  · subst x
    have hz : (Vstar W)=ᶠ[𝓝 (0:ℝ)] (fun _ => (0:ℂ)) := by
      filter_upwards [isOpen_Iio.mem_nhds ha] with y hy
      change y<a at hy
      have hw : W y=0 := by
        by_contra hn
        have hh := (hsupp hn).1
        linarith
      simp only [Vstar,hw,mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_sqrt hx)).mul hW.contDiffAt

theorem Vstar_support (W : ℝ→ℂ) (a b : ℝ)
    (hsupp : Function.support W⊆Set.Icc a b) : Function.support (Vstar W)⊆Set.Icc a b := by
  intro x hx
  apply hsupp
  intro hz
  exact hx (by simp [Vstar,hz])

def vstarSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (Vstar_support W a b hsupp)).toSchwartzMap
    (Vstar_contDiff W a b ha hsupp hW)

@[simp] theorem vstarSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (x : ℝ) :
    vstarSchwartz W a b ha hsupp hW x=Vstar W x := rfl

theorem completed_kernel_log_separation
    {ι : Type*} [Fintype ι] (V : ι→ℝ→ℂ) (slope M : ι→ℝ)
    (hM : ∀i,0≤M i) (hV : ∀i y,V i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (A J : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀y : ι→ℝ,(∏i,V i (y i))*CubicReflectionKernel.paperKernel (Vstar W)
          (R*Real.exp (∑i,slope i*y i))=
        ∫t : ℝ,(∏i,V i (y i)*FourierBridge.logPhase t (slope i*y i))*B t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖B t‖) volume ∧
      (1+R)^A*(∫t : ℝ,(1+‖t‖)^J*‖B t‖)≤C ∧
      (∀t : ℝ,(1+R)^A*(1+‖t‖)^J*‖B t‖≤C) := by
  let S := vstarSchwartz W a b ha hsupp hW
  obtain ⟨s,D,hD,hbound⟩ := CubicReflectionKernel.paperKernel_euler_source_uniform_weighted_bound
    a b ha A (J+(volume : Measure ℝ).integrablePower)
  have hF := CubicReflectionKernel.paperKernel_compact_source_smooth (Vstar W) a b ha
    (Vstar_support W a b hsupp) (Vstar_contDiff W a b ha hsupp hW)
  apply LocalLogFourier.coupled_positive_log_separation_envelope V (CubicReflectionKernel.paperKernel (Vstar W))
    slope M hM hV hF A J (D*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) S) (by positivity)
  intro i hi x hx
  have he : (S : ℝ→ℂ)=Vstar W := rfl
  have hb := hbound S (Vstar_support W a b hsupp) i hi x hx
  rw [he] at hb
  exact hb

end CompletedGauss

namespace InitialMeanSquare
open SecondPassArithmetic

theorem initial_bin_invariant (Z H B R : ℝ) (j : SecondLogIndex)
    (hZ : Z≠0) (hH : H≠0) (hB : B≠0) :
    (secondLogK j*Real.exp 2)*R/(initialLogColumn Z B j*initialLogLabel j)=
      (R/B)*(Z/H)*(H*secondLogK j*B^2/Z^2) := by
  rw [initial_log_mass Z B hB j]
  have hexp : Real.exp 2≠0 := (Real.exp_pos _).ne'
  field_simp

theorem initial_bin_invariant_le (Z H B R c : ℝ) (j : SecondLogIndex)
    (hZ : 0<Z) (hH : 0<H) (hB : 0<B) (hR : R≤c*B) :
    (secondLogK j*Real.exp 2)*R/(initialLogColumn Z B j*initialLogLabel j)≤
      c*(Z/H)*(H*secondLogK j*B^2/Z^2) := by
  rw [initial_bin_invariant Z H B R j hZ.ne' hH.ne' hB.ne']
  have hr : R/B≤c := (div_le_iff₀ hB).mpr hR
  have hk : 0<secondLogK j := normLogScale_pos _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hr (div_nonneg hZ.le hH.le)) (by positivity)

theorem initial_small_radial_admissible (Z B R c σ θ deltaLoss : ℝ) (j : SecondLogIndex)
    (hZ : 1≤Z) (hB : 0<B) (hR : R≤c*B) (hc : 0≤c) (hcZ : c≤Z^deltaLoss)
    (hmargin : deltaLoss+θ≤σ-(1:ℝ)/40)
    (hrad : Z^(1+σ)*secondLogK j*B^2/Z^2≤Z^θ) :
    (secondLogK j*Real.exp 2)*R≤
      initialLogColumn Z B j*initialLogLabel j*Z^(-(1:ℝ)/40) := by
  have hZ0 : 0<Z := by linarith
  have hH : 0<Z^(1+σ) := Real.rpow_pos_of_pos hZ0 _
  have hm : 0 < initialLogColumn Z B j*initialLogLabel j := by
    rw [initial_log_mass Z B hB.ne' j]
    positivity
  have he : Z/Z^(1+σ)=Z^(-σ) := by
    calc
      _ = Z^((1:ℝ)-(1+σ)) := by rw [Real.rpow_sub hZ0,Real.rpow_one]
      _ = _ := by congr 1; ring
  have hb := initial_bin_invariant_le Z (Z^(1+σ)) B R c j hZ0 hH hB hR
  rw [he] at hb
  rw [mul_comm (initialLogColumn Z B j*initialLogLabel j)]
  apply (div_le_iff₀ hm).mp
  apply hb.trans
  calc
    c*Z^(-σ)*(Z^(1+σ)*secondLogK j*B^2/Z^2) ≤ c*Z^(-σ)*Z^θ :=
      mul_le_mul_of_nonneg_left hrad (mul_nonneg hc (Real.rpow_nonneg hZ0.le _))
    _ ≤ Z^deltaLoss*Z^(-σ)*Z^θ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcZ (Real.rpow_nonneg hZ0.le _)) (Real.rpow_nonneg hZ0.le _)
    _ = Z^(deltaLoss-σ+θ) := by rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]; simp only [sub_eq_add_neg]
    _ ≤ Z^(-(1:ℝ)/40) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

end InitialMeanSquare

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups Matrix InnerProductSpace

def hyperbolicEuclideanCoordinates (w : HyperbolicSpace) : EuclideanSpatial :=
  WithLp.toLp 2 (hyperbolicSpatialCoordinates w)

lemma hyperbolicEuclideanCoordinates_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicEuclideanCoordinates (upperPoint z v hv)=WithLp.toLp 2 ![z.re,z.im,v] := by
  simp only [hyperbolicEuclideanCoordinates,hyperbolicSpatialCoordinates,
    hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]

lemma euclideanToHyperbolic_coordinates (w : HyperbolicSpace) :
    euclideanToHyperbolic (hyperbolicEuclideanCoordinates w)=w := by
  have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
  rw [euclideanToHyperbolic_positive _ hp]
  change upperPoint ((hyperbolicSpatialCoordinates w 0:ℂ)+Complex.I*(hyperbolicSpatialCoordinates w 1:ℂ))
    (hyperbolicSpatialCoordinates w 2) hp=w
  simpa only [mul_comm] using hyperbolicSpatialCoordinates_reconstruct w

lemma hyperbolicEuclideanCoordinates_toHyperbolic (p : EuclideanSpatial) (hp : 0<p 2) :
    hyperbolicEuclideanCoordinates (euclideanToHyperbolic p)=p := by
  rw [euclideanToHyperbolic_positive _ hp,hyperbolicEuclideanCoordinates_upperPoint]
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext j
  fin_cases j <;> simp

def euclideanAction (g : SL(2,ℂ)) (p : EuclideanSpatial) : EuclideanSpatial :=
  hyperbolicEuclideanCoordinates (g•euclideanToHyperbolic p)

lemma euclideanAction_positive (g : SL(2,ℂ)) (p : EuclideanSpatial) :
    0<euclideanAction g p 2 := by
  change 0<hyperbolicHeight (g•euclideanToHyperbolic p)
  exact hyperbolicHeight_pos _

lemma euclideanAction_mul (g h : SL(2,ℂ)) :
    euclideanAction (g*h)=euclideanAction g ∘ euclideanAction h := by
  funext p
  simp only [euclideanAction,Function.comp_apply,euclideanToHyperbolic_coordinates,mul_smul]

lemma euclideanAction_translation (b : ℂ) (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanAction (complexTranslation b) p=p+euclideanHorizontalTranslation b := by
  rw [euclideanAction,euclideanToHyperbolic_positive _ hp,complexTranslation_action,
    hyperbolicEuclideanCoordinates_upperPoint]
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext j
  fin_cases j <;> simp [euclideanHorizontalTranslation]

lemma euclideanAction_diagonal (b : ℂ) (hb : b≠0) (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanAction (complexDiagonal b hb) p=euclideanComplexDilation b p := by
  rw [euclideanAction,euclideanToHyperbolic_positive _ hp,complexDiagonal_action,
    hyperbolicEuclideanCoordinates_upperPoint]
  obtain ⟨h0,h1,h2⟩ := euclideanComplexDilation_apply b p
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext j
  fin_cases j
  · simpa [Complex.mul_re] using h0.symm
  · simpa [Complex.mul_im,add_comm] using h1.symm
  · exact h2.symm

lemma euclideanAction_weyl (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanAction complexWeyl p=euclideanWeylAction p := by
  have hn : ‖p‖≠0 := norm_ne_zero_iff.mpr (euclideanUpperHalf_ne_zero p hp)
  have hnc : (‖p‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn
  have hq : 0<euclideanWeylAction p 2 := by
    rw [(euclideanWeylAction_apply p).2.2]
    exact mul_pos (sq_pos_of_ne_zero (one_div_ne_zero hn)) hp
  have h := congrArg hyperbolicEuclideanCoordinates
    (show euclideanToHyperbolic (euclideanWeylAction p)=
      complexWeyl•euclideanToHyperbolic p from by
      rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexWeyl_action]
      obtain ⟨h0,h1,h2⟩ := euclideanWeylAction_apply p
      apply upperPoint_congr
      · rw [h0,h1,euclidean_complex_norm_sq]
        simp only [Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,
          Complex.ofReal_one,Complex.star_def,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
        field_simp
        ; ring
      · rw [h2,euclidean_complex_norm_sq]
        field_simp)
  simpa only [hyperbolicEuclideanCoordinates_toHyperbolic _ hq,euclideanAction] using h.symm

lemma euclideanWeylReflection_norm (u : EuclideanSpatial) : ‖euclideanWeylReflection u‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  obtain ⟨h0,h1,h2⟩ := euclideanWeylReflection_apply u
  simp only [Fin.sum_univ_three,h0,h1,h2,neg_sq]

lemma euclideanComplexDilation_norm (b : ℂ) (u : EuclideanSpatial) :
    ‖euclideanComplexDilation b u‖=Complex.normSq b*‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Complex.normSq_nonneg _) (norm_nonneg _))).mp
  have h : (b^2).re^2+(b^2).im^2=(Complex.normSq b)^2 := by
    simpa [Complex.normSq_apply,sq] using map_pow Complex.normSq b 2
  rw [mul_pow,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  obtain ⟨h0,h1,h2⟩ := euclideanComplexDilation_apply b u
  simp only [Fin.sum_univ_three,h0,h1,h2]
  calc
    _ = ((b^2).re^2+(b^2).im^2)*((u 0)^2+(u 1)^2)+(Complex.normSq b)^2*(u 2)^2 := by ring
    _ = _ := by rw [h]; ring

lemma euclideanInversionDeriv_norm (p u : EuclideanSpatial) :
    ‖euclideanInversionDeriv p u‖=(1/‖p‖)^2*‖u‖ := by
  unfold euclideanInversionDeriv
  rw [_root_.smul_apply,norm_smul,Real.norm_of_nonneg (sq_nonneg _)]
  simp only [LinearIsometryEquiv.coe_coe'',LinearIsometryEquiv.norm_map]

def HyperbolicDifferentialIsometry (g : SL(2,ℂ)) : Prop :=
  ∀p : EuclideanSpatial,0<p 2 → ∃A : EuclideanSpatial→L[ℝ]EuclideanSpatial,
    HasFDerivAt (euclideanAction g) A p ∧
    ∀u,‖A u‖*p 2=‖u‖*euclideanAction g p 2

lemma hyperbolicDifferentialIsometry_mul (g h : SL(2,ℂ))
    (hg : HyperbolicDifferentialIsometry g) (hh : HyperbolicDifferentialIsometry h) :
    HyperbolicDifferentialIsometry (g*h) := by
  intro p hp
  obtain ⟨B,hB,hBn⟩ := hh p hp
  obtain ⟨A,hA,hAn⟩ := hg (euclideanAction h p) (euclideanAction_positive h p)
  refine ⟨A.comp B,?_,?_⟩
  · rw [euclideanAction_mul]
    exact hA.comp p hB
  · intro u
    rw [euclideanAction_mul]
    change ‖A (B u)‖*p 2=‖u‖*euclideanAction g (euclideanAction h p) 2
    apply (mul_right_inj' (euclideanAction_positive h p).ne').mp
    calc
      _ = (‖A (B u)‖*euclideanAction h p 2)*p 2 := by ring
      _ = (‖B u‖*euclideanAction g (euclideanAction h p) 2)*p 2 := by rw [hAn]
      _ = (‖B u‖*p 2)*euclideanAction g (euclideanAction h p) 2 := by ring
      _ = _ := by rw [hBn]; ring

lemma hyperbolicDifferentialIsometry_translation (b : ℂ) :
    HyperbolicDifferentialIsometry (complexTranslation b) := by
  intro p hp
  refine ⟨ContinuousLinearMap.id ℝ _,?_,?_⟩
  · apply ((hasFDerivAt_id p).add_const (euclideanHorizontalTranslation b)).congr_of_eventuallyEq
    filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
      with q hq
    exact euclideanAction_translation b q hq
  · intro u
    rw [euclideanAction_translation b p hp]
    simp [euclideanHorizontalTranslation]

lemma hyperbolicDifferentialIsometry_diagonal (b : ℂ) (hb : b≠0) :
    HyperbolicDifferentialIsometry (complexDiagonal b hb) := by
  intro p hp
  refine ⟨euclideanComplexDilation b,?_,?_⟩
  · apply (euclideanComplexDilation b).hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
      with q hq
    exact euclideanAction_diagonal b hb q hq
  · intro u
    rw [euclideanComplexDilation_norm,euclideanAction_diagonal b hb p hp,
      (euclideanComplexDilation_apply b p).2.2]
    ring

lemma hyperbolicDifferentialIsometry_weyl : HyperbolicDifferentialIsometry complexWeyl := by
  intro p hp
  refine ⟨euclideanWeylReflection.comp (euclideanInversionDeriv p),?_,?_⟩
  · have h := euclideanWeylReflection.hasFDerivAt.comp p
      (euclideanInversion_hasFDerivAt p (euclideanUpperHalf_ne_zero p hp))
    apply h.congr_of_eventuallyEq
    filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
      with q hq
    exact euclideanAction_weyl q hq
  · intro u
    change ‖euclideanWeylReflection (euclideanInversionDeriv p u)‖*p 2=_
    rw [euclideanWeylReflection_norm,euclideanInversionDeriv_norm,euclideanAction_weyl p hp,
      (euclideanWeylAction_apply p).2.2]
    ring

theorem hyperbolicDifferentialIsometry (g : SL(2,ℂ)) : HyperbolicDifferentialIsometry g := by
  by_cases hc : g 1 0=0
  · obtain ⟨ha,hg⟩ := complex_bruhat_zero g hc
    rw [hg]
    exact hyperbolicDifferentialIsometry_mul _ _ (hyperbolicDifferentialIsometry_diagonal _ ha)
      (hyperbolicDifferentialIsometry_translation _)
  · rw [complex_bruhat_nonzero g hc]
    exact hyperbolicDifferentialIsometry_mul _ _
      (hyperbolicDifferentialIsometry_mul _ _
        (hyperbolicDifferentialIsometry_mul _ _ (hyperbolicDifferentialIsometry_translation _)
          (hyperbolicDifferentialIsometry_diagonal _ (inv_ne_zero hc)))
        hyperbolicDifferentialIsometry_weyl)
      (hyperbolicDifferentialIsometry_translation _)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

namespace CubicEisenstein

lemma norm_comp_scaled_isometry (A : EuclideanSpatial→L[ℝ]EuclideanSpatial) (r : ℝ)
    (hr : 0<r) (hA : ∀u,‖A u‖=r*‖u‖) (φ : EuclideanSpatial→L[ℝ]ℝ) :
    ‖φ.comp A‖=r*‖φ‖ := by
  let iso : EuclideanSpatial→ₗᵢ[ℝ]EuclideanSpatial :=
    { toLinearMap := (r⁻¹ • A).toLinearMap
      norm_map' := fun u => by
        change ‖r⁻¹ • A u‖=‖u‖
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),hA]
        field_simp }
  let equiv : EuclideanSpatial≃ₗᵢ[ℝ]EuclideanSpatial :=
    LinearIsometryEquiv.ofSurjective iso ((LinearMap.injective_iff_surjective).mp iso.injective)
  have he : A=r • (equiv : EuclideanSpatial→L[ℝ]EuclideanSpatial) := by
    apply ContinuousLinearMap.ext
    intro u
    change A u=r • (r⁻¹ • A u)
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  rw [he,ContinuousLinearMap.comp_smul,norm_smul,Real.norm_of_nonneg hr.le,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

lemma hyperbolic_cotangent_energy_comp (g : SL(2,ℂ)) (F : EuclideanSpatial→ℝ)
    (p : EuclideanSpatial) (hp : 0<p 2) (hF : DifferentiableAt ℝ F (euclideanAction g p)) :
    (p 2)^2*‖fderiv ℝ (F ∘ euclideanAction g) p‖^2=
      (euclideanAction g p 2)^2*‖fderiv ℝ F (euclideanAction g p)‖^2 := by
  obtain ⟨A,hA,hAn⟩ := hyperbolicDifferentialIsometry g p hp
  rw [(hF.hasFDerivAt.comp p hA).fderiv]
  have hn : ∀u,‖A u‖=(euclideanAction g p 2/p 2)*‖u‖ := by
    intro u
    calc
      ‖A u‖=(‖u‖*euclideanAction g p 2)/p 2 := (eq_div_iff hp.ne').2 (hAn u)
      _ = _ := by ring
  rw [norm_comp_scaled_isometry A _ (div_pos (euclideanAction_positive g p) hp) hn]
  field_simp

def euclideanScalarDirichletDensity (F : EuclideanSpatial→ℝ) (p : EuclideanSpatial) : ℝ :=
  (p 2)^2*‖fderiv ℝ F p‖^2

lemma euclideanScalarDirichletDensity_invariant (g : SL(2,ℂ)) (F : EuclideanSpatial→ℝ)
    (p : EuclideanSpatial) (hp : 0<p 2) (hF : DifferentiableAt ℝ F (euclideanAction g p))
    (hinv : F ∘ euclideanAction g=F) :
    euclideanScalarDirichletDensity F (euclideanAction g p)=euclideanScalarDirichletDensity F p := by
  have h := hyperbolic_cotangent_energy_comp g F p hp hF
  rw [hinv] at h
  exact h.symm

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

namespace CubicEisenstein

lemma hyperbolicEuclideanCoordinates_continuous : Continuous hyperbolicEuclideanCoordinates :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.comp
    hyperbolicSpatialCoordinates_continuous

lemma hyperbolicSpatialChart_toHyperbolic (p : EuclideanSpatial) (hp : 0<p 2) :
    hyperbolicSpatialChart (euclideanToHyperbolic p)=p.ofLp :=
  congrArg WithLp.ofLp (hyperbolicEuclideanCoordinates_toHyperbolic p hp)

lemma euclideanToHyperbolic_contMDiffAt (p : EuclideanSpatial) (hp : 0<p 2) :
    ContMDiffAt 𝓘(ℝ,EuclideanSpatial) 𝓘(ℝ,SpatialCoordinates) ∞ euclideanToHyperbolic p := by
  have ht : p.ofLp∈hyperbolicSpatialChart.target := by
    rw [←hyperbolicSpatialChart_toHyperbolic p hp]
    exact hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have hs : ContMDiffOn 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
      hyperbolicSpatialChart.symm hyperbolicSpatialChart.target := by
    simpa only [hyperbolicSpatial_chartAt] using
      (contMDiffOn_chart_symm (I := 𝓘(ℝ,SpatialCoordinates)) (n := ∞) (x := euclideanToHyperbolic p))
  have hd := (hs.contMDiffAt (hyperbolicSpatialChart.open_target.mem_nhds ht)).comp p
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff.contDiffAt.contMDiffAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
    with q hq
  change euclideanToHyperbolic q=hyperbolicSpatialChart.symm q.ofLp
  rw [←hyperbolicSpatialChart_toHyperbolic q hq,hyperbolicSpatialChart.left_inv (Set.mem_univ _)]

def kernelTestField (f : kernelSmoothTests) (p : EuclideanSpatial) : ℂ :=
  f.1 (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p))

lemma kernelTestField_contDiffAt (f : kernelSmoothTests) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (kernelTestField f) p :=
  (((f.2.1.comp kernelProjection_contMDiff) (euclideanToHyperbolic p)).comp p
    (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

lemma kernelTestField_re_contDiffAt (f : kernelSmoothTests) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun p => (kernelTestField f p).re) p :=
  Complex.reCLM.contDiff.contDiffAt.comp p (kernelTestField_contDiffAt f p hp)

lemma kernelTestField_im_contDiffAt (f : kernelSmoothTests) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun p => (kernelTestField f p).im) p :=
  Complex.imCLM.contDiff.contDiffAt.comp p (kernelTestField_contDiffAt f p hp)

lemma kernelTestField_invariant (f : kernelSmoothTests) (M : globalKubotaKernel) (p : EuclideanSpatial) :
    kernelTestField f (euclideanAction (integralComplexMatrix M) p)=kernelTestField f p := by
  simp only [kernelTestField,euclideanAction,euclideanToHyperbolic_coordinates,integralOrbitProjection_eq]

def kernelTestEnergyDensity (f : kernelSmoothTests) (w : HyperbolicSpace) : ℝ :=
  euclideanScalarDirichletDensity (fun p => (kernelTestField f p).re) (hyperbolicEuclideanCoordinates w)+
  euclideanScalarDirichletDensity (fun p => (kernelTestField f p).im) (hyperbolicEuclideanCoordinates w)

lemma kernelTestEnergyDensity_nonneg (f : kernelSmoothTests) (w : HyperbolicSpace) :
    0≤kernelTestEnergyDensity f w := by
  unfold kernelTestEnergyDensity euclideanScalarDirichletDensity
  positivity

lemma kernelTestEnergyDensity_invariant (f : kernelSmoothTests) (M : globalKubotaKernel) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f (integralComplexMatrix M•w)=kernelTestEnergyDensity f w := by
  have he : hyperbolicEuclideanCoordinates (integralComplexMatrix M•w)=
      euclideanAction (integralComplexMatrix M) (hyperbolicEuclideanCoordinates w) := by
    simp only [euclideanAction,euclideanToHyperbolic_coordinates]
  have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
  unfold kernelTestEnergyDensity
  rw [he]
  congr 1
  · apply euclideanScalarDirichletDensity_invariant _ _ _ hp
    · exact (kernelTestField_re_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp)
    · funext p
      exact congrArg Complex.re (kernelTestField_invariant f M p)
  · apply euclideanScalarDirichletDensity_invariant _ _ _ hp
    · exact (kernelTestField_im_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp)
    · funext p
      exact congrArg Complex.im (kernelTestField_invariant f M p)

def kernelQuotientEnergyDensity (f : kernelSmoothTests) : KernelQuotient→ℝ :=
  Quotient.lift (kernelTestEnergyDensity f) (by
    intro u v huv
    obtain ⟨M,hM⟩ := huv
    rw [←hM]
    exact (kernelTestEnergyDensity_invariant f M u).symm)

lemma kernelTestEnergyDensity_continuous (f : kernelSmoothTests) : Continuous (kernelTestEnergyDensity f) := by
  rw [continuous_iff_continuousAt]
  intro w
  have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
  have hr := (kernelTestField_re_contDiffAt f _ hp).continuousAt_fderiv (by simp)
  have hi := (kernelTestField_im_contDiffAt f _ hp).continuousAt_fderiv (by simp)
  have ht : ContinuousAt (fun p : EuclideanSpatial => p 2) (hyperbolicEuclideanCoordinates w) := by fun_prop
  exact (((ht.pow 2).mul (hr.norm.pow 2)).add ((ht.pow 2).mul (hi.norm.pow 2))).comp
    hyperbolicEuclideanCoordinates_continuous.continuousAt

lemma kernelQuotientEnergyDensity_continuous (f : kernelSmoothTests) : Continuous (kernelQuotientEnergyDensity f) :=
  (kernelTestEnergyDensity_continuous f).quotient_lift _

lemma kernelQuotientEnergyDensity_nonneg (f : kernelSmoothTests) (q : KernelQuotient) :
    0≤kernelQuotientEnergyDensity f q := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelTestEnergyDensity_nonneg f w

lemma kernelQuotientEnergyDensity_support (f : kernelSmoothTests) :
    Function.support (kernelQuotientEnergyDensity f)⊆tsupport f.1 := by
  intro q hq
  by_contra hn
  have hz : f.1=ᶠ[𝓝 q]0 := notMem_tsupport_iff_eventuallyEq.mp hn
  induction q using Quotient.inductionOn with
  | _ w =>
    have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
    have hc := (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt _ hp).continuousAt
    change Tendsto (integralOrbitProjection globalKubotaKernel ∘ euclideanToHyperbolic)
      (𝓝 (hyperbolicEuclideanCoordinates w))
      (𝓝 (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic (hyperbolicEuclideanCoordinates w)))) at hc
    rw [euclideanToHyperbolic_coordinates] at hc
    have hzF : kernelTestField f=ᶠ[𝓝 (hyperbolicEuclideanCoordinates w)]0 := hz.comp_tendsto hc
    have hzr : (fun p => (kernelTestField f p).re)=ᶠ[𝓝 (hyperbolicEuclideanCoordinates w)]0 := by
      filter_upwards [hzF] with p hp
      simp [hp]
    have hzi : (fun p => (kernelTestField f p).im)=ᶠ[𝓝 (hyperbolicEuclideanCoordinates w)]0 := by
      filter_upwards [hzF] with p hp
      simp [hp]
    apply hq
    change kernelTestEnergyDensity f w=0
    simp only [kernelTestEnergyDensity,euclideanScalarDirichletDensity,hzr.fderiv_eq,hzi.fderiv_eq,
      fderiv_zero,Pi.zero_apply,norm_zero,zero_pow (by decide : 2≠0),mul_zero,add_zero]

lemma kernelQuotientEnergyDensity_hasCompactSupport (f : kernelSmoothTests) :
    HasCompactSupport (kernelQuotientEnergyDensity f) :=
  HasCompactSupport.of_support_subset_isCompact f.2.2 (kernelQuotientEnergyDensity_support f)

lemma kernelQuotientEnergyDensity_integrable (f : kernelSmoothTests) :
    Integrable (kernelQuotientEnergyDensity f) (integralQuotientVolume globalKubotaKernel) :=
  (kernelQuotientEnergyDensity_continuous f).integrable_of_hasCompactSupport
    (kernelQuotientEnergyDensity_hasCompactSupport f)

def kernelDirichletEnergy (f : kernelSmoothTests) : ℝ :=
  ∫q,kernelQuotientEnergyDensity f q ∂integralQuotientVolume globalKubotaKernel

lemma kernelDirichletEnergy_nonneg (f : kernelSmoothTests) : 0≤kernelDirichletEnergy f :=
  integral_nonneg (kernelQuotientEnergyDensity_nonneg f)

end CubicEisenstein

end

end OAI
