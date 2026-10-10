import OAI.NumberTheory.DirichletL.CubicSieve.DivisorTargets

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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem columnLog_norm_lower (X M : ℝ) (hX : 0<X) (S : Finset ι)
    (h : -M≤columnLog p X S) : X*Real.exp (-M)≤primeProductNorm p S := by
  have he := Real.exp_le_exp.mpr h
  rw [columnLog,Real.exp_log (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp S) hX)] at he
  simpa only [mul_comm] using (le_div_iff₀ hX).mp he

omit [DecidableEq ι] in
theorem normalized_second_coefficient_sq_le
    (Ψ : O→*ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
    (g : ℝ→ℂ) (G X : ℝ) (hG : ∀t,‖g t‖≤G) (S : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2≤G^2/primeProductNorm p S := by
  have hG0 : 0≤G := (norm_nonneg (g 0)).trans (hG 0)
  have ht := secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (normalizedColumn p (fun A => g (columnLog p X A))) S
  apply (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
  simp only [normalizedColumn,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_pow]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hG _) 2) (sq_nonneg _)

include hp in

omit [DecidableEq ι] in
theorem normalized_second_mass_zero
    (F : Finset ι) (Ψ : O→*ℂ) (m c d : O) (g : ℝ→ℂ)
    (M X : ℝ) (hX : 0<X) (hM : ∀t,g t≠0 → |t|≤M) (hsmall : X*Real.exp M<1) :
    (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)=0 := by
  apply Finset.sum_eq_zero
  intro S hS
  have hz : g (columnLog p X S)=0 := by
    by_contra hn
    have hh := columnLog_norm_upper p hp X M hX S ((le_abs_self _).trans (hM _ hn))
    have ho := primeProductNorm_ge_one p hp S
    linarith
  simp [secondInputCoefficient,normalizedColumn,hz]

include hp in

theorem normalized_second_mass_fixed_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O→*ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
    (g : ℝ→ℂ) (G M X : ℝ) (hX : 0<X)
    (hG : ∀t,‖g t‖≤G) (hM : ∀t,g t≠0 → |t|≤M) :
    (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)≤
      128*Real.exp (2*M)*G^2 := by
  by_cases hsmall : X*Real.exp M<1
  · rw [normalized_second_mass_zero p hp hg F Ψ m c d g M X hX hM hsmall]
    positivity
  have hH : 1≤X*Real.exp M := le_of_not_gt hsmall
  let T := F.powerset.filter (fun S => g (columnLog p X S)≠0)
  have hsub : T⊆boundedPrimeSupports p F (X*Real.exp M) := by
    intro S hS
    obtain ⟨hSF,hSn⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨hSF,columnLog_norm_upper p hp X M hX S
      ((le_abs_self _).trans (hM _ hSn))⟩
  have hcard : (T.card:ℝ)≤128*(X*Real.exp M) := by
    apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    exact boundedPrimeSupports_card p hinj F (X*Real.exp M) hH
  have he : (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d
        (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)=
      ∑S∈T,‖secondInputCoefficient p hg Ψ m c d
        (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hn
    have hz : g (columnLog p X S)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hS,hh⟩)
    simp [secondInputCoefficient,normalizedColumn,hz]
  rw [he]
  calc
    _ ≤ ∑_S∈T,G^2/(X*Real.exp (-M)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply (normalized_second_coefficient_sq_le p hg Ψ hΨ m c d g G X hG S).trans
      have hlo := columnLog_norm_lower p hp X M hX S (abs_le.mp (hM _ (Finset.mem_filter.mp hS).2)).1
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hlo
    _ = (T.card:ℝ)*(G^2/(X*Real.exp (-M))) := by simp
    _ ≤ (128*(X*Real.exp M))*(G^2/(X*Real.exp (-M))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 128*Real.exp (2*M)*G^2 := by
      rw [show 2*M=M+M by ring,Real.exp_add,Real.exp_neg]
      field_simp [hX.ne',Real.exp_ne_zero]

end

theorem full_uniform_normalized_second_mass (g : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O) (X : ℝ),0<X →
      (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d
        (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)≤C := by
  refine ⟨128*Real.exp (2*M)*(SchwartzMap.seminorm ℝ 0 0 g)^2+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj F Ψ hΨ m c d X hX
  exact (normalized_second_mass_fixed_bound p hp hg hinj F Ψ hΨ m c d g _ M X hX
    (fun t => g.norm_le_seminorm ℝ t) hM).trans (by linarith)

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

def globalFirstColumnMass (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) : ℝ :=
  ∑G∈(globalFirstRawPool pool b).powerset,
    ‖secondInputCoefficient p hg Ψ (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) G‖^2

include hp in
theorem globalFirstColumnMass_support (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ,ℂ)) (ell M : ℝ) (hell : 0<ell)
    (hM : ∀t,g t≠0 → |t|≤M) (side : Bool)
    (hmass : globalFirstColumnMass p hg pool b Ψ m g ell side≠0) :
    primeProductNorm p b.common≤ell*Real.exp M ∧
      primeProductNorm p b.firstCommon≤ell*Real.exp M := by
  let a := primeProductNorm p (b.cube.sideDivisor side)
  let c := primeProductNorm p b.common
  let t := primeProductNorm p b.firstCommon
  have ha : 1≤a := primeProductNorm_ge_one p hp _
  have hc : 1≤c := primeProductNorm_ge_one p hp _
  have ht : 1≤t := primeProductNorm_ge_one p hp _
  have hden : 0<a*c*t := by positivity
  have hX : 0<globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon := by
    change 0<ell/(a*c)/t
    positivity
  have hlow : 1≤(globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon)*Real.exp M := by
    by_contra hh
    apply hmass
    exact normalized_second_mass_zero p hp hg (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) g M
      (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon) hX hM (lt_of_not_ge hh)
  have heq : (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon)*Real.exp M=
      ell*Real.exp M/(a*c*t) := by change (ell/(a*c)/t)*Real.exp M=_; ring
  rw [heq] at hlow
  have hb : a*c*t≤ell*Real.exp M := by simpa only [one_mul] using (le_div_iff₀ hden).mp hlow
  constructor
  · change c≤_
    calc
      c=1*c*1 := by ring
      _ ≤ a*c*t := by gcongr
      _ ≤ _ := hb
  · change t≤_
    calc
      t=1*1*t := by ring
      _ ≤ a*c*t := by gcongr
      _ ≤ _ := hb

include hp in
theorem globalFirstColumnMass_zero_off_support (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ,ℂ)) (ell M U : ℝ) (hell : 0<ell)
    (hM : ∀t,g t≠0 → |t|≤M) (hU : ell*Real.exp M≤U) (side : Bool)
    (hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)) :
    globalFirstColumnMass p hg pool b Ψ m g ell side=0 := by
  by_contra hm
  have h := globalFirstColumnMass_support p hp hg pool b Ψ m g ell M hell hM side hm
  exact hoff ⟨h.1.trans hU,h.2.trans hU⟩

include hp in
theorem globalFirstDiagonalCost_eq_supported (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (ell M U : ℝ) (hell : 0<ell) (hM : ∀t,g t≠0 → |t|≤M)
    (hU : ell*Real.exp M≤U) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstDiagonalCost p hg pool s w Ψ m g W ell side Y=
      globalFirstDiagonalCost p hg pool
        (s.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U))
        w Ψ m g W ell side Y := by
  unfold globalFirstDiagonalCost
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro b hb hn
  have hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U) := by
    intro h; exact hn (Finset.mem_filter.mpr ⟨hb,h⟩)
  have hz := globalFirstColumnMass_zero_off_support p hp hg pool b Ψ m g ell M U hell hM hU side hoff
  change globalFirstColumnMass p hg pool b Ψ m g ell side=0 at hz
  change ‖w b‖*(primeProductNorm p b.firstCommon)⁻¹*
    (|Y b| *‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖*globalFirstColumnMass p hg pool b Ψ m g ell side)=0
  rw [hz,mul_zero,mul_zero]

end

theorem globalDiagonalPowers (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ B U : ℝ,1≤B → 1≤U →
      B^(ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2≤C*(B*U)^ε := by
  let k : ℝ := 128*Real.exp 1
  let C := k^2*(1+1/(ε/3))^2
  refine ⟨C,by dsimp [C,k]; positivity,?_⟩
  intro B U hB hU
  have hB0 : 0<B := by linarith
  have hU0 : 0<U := by linarith
  have hη : 0<ε/3 := by positivity
  have hlog := descent_normLogBin_small_power (ε/3) hη U hU
  have hBp : B^(ε/3)*(B^2)^(ε/3)=B^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hB0.le,←Real.rpow_add hB0]
    congr 1
    ring
  have hUp : U^(ε/3)*(U^(ε/3))^2=U^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le,←Real.rpow_add hU0]
    congr 1
    ring
  calc
    _ ≤ B^(ε/3)*(U*B^2)^(ε/3)*(k*((1+1/(ε/3))*U^(ε/3)))^2 := by
      dsimp [k]
      gcongr
    _ = k^2*(1+1/(ε/3))^2*(B^(ε/3)*(B^2)^(ε/3))*(U^(ε/3)*(U^(ε/3))^2) := by
      rw [Real.mul_rpow hU0.le (sq_nonneg B)]
      ring
    _ = C*(B*U)^ε := by rw [hBp,hUp,Real.mul_rpow hB0.le hU0.le]; dsimp [C]; ring

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem globalFirstDiagonalCost_parent_bound (ε : ℝ) (hε : 0<ε)
    (g W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
      (Ψ : O →* ℂ) (m : O) (Γ K ell B F U : ℝ) (side : Bool),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 1≤U → ell*Real.exp M≤U →
      (∀z,‖Ψ z‖≤1) → (∀b∈s,0≤w b ∧ w b≤Γ) → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      globalFirstDiagonalCost p hg pool s
        (fun b => ((w b*globalFirstCoefficient p K ell B F side b : ℝ) : ℂ))
        Ψ m g W ell side (globalFirstPooledRow p K ell B F side)≤
          C*Γ*(ell*B^3*F)*(B*U)^ε := by
  obtain ⟨Cg,hCg,hmass⟩ := full_uniform_normalized_second_mass g M hM
  obtain ⟨Cd,hCd,hcount⟩ := globalFirstData_harmonic_sum (ε/3) (by positivity)
  obtain ⟨Cp,hCp,hpowers⟩ := globalDiagonalPowers ε hε
  let P := Cd*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3
  have hP : 0≤P := by dsimp [P]; positivity
  refine ⟨P*Cp+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj pool s w Ψ m Γ K ell B F U side
    hΓ hK hell hB hF hU hellU hΨ hw hs hb1 hb2
  have hB0 : 0<B := by linarith
  let T := s.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)
  let θ := fun b : GlobalFirstData ι =>
    (1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*
      (1/‖eisEmbedding (∏i∈cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖)
  have ht (b : GlobalFirstData ι) (hb : b∈T) : b∈s := (Finset.mem_filter.mp hb).1
  have hsum := hcount p hp hinj T B U hB hU
    (fun b hb => hs b (ht b hb)) (fun b hb => (Finset.mem_filter.mp hb).2.1)
    (fun b hb => (Finset.mem_filter.mp hb).2.2)
    (fun b hb => hb1 b (ht b hb)) (fun b hb => hb2 b (ht b hb))
  change (∑b∈T,θ b)≤_ at hsum
  rw [globalFirstDiagonalCost_eq_supported p hp hg pool s _ Ψ m g W ell M U hell hM hellU side]
  change globalFirstDiagonalCost p hg pool T _ Ψ m g W ell side _≤_
  have hterm (b : GlobalFirstData ι) (hb : b∈T) :
      ‖((w b*globalFirstCoefficient p K ell B F side b : ℝ) : ℂ)‖*(primeProductNorm p b.firstCommon)⁻¹*
        (|globalFirstPooledRow p K ell B F side b| *‖paperRadialFourier W 0‖*
          globalFirstColumnMass p hg pool b Ψ m g ell side)≤
        (Γ*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3*ell*B^2*F)*θ b := by
    have htpos := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon
    have hcpos := FirstPassCubeLabels.primeProductNorm_pos p hp b.common
    have hapos := FirstPassCubeLabels.primeProductNorm_pos p hp (b.cube.sideDivisor side)
    have hX : 0<globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon := by
      unfold globalFirstBlockColumnScale
      positivity
    have hm := hmass p hp hg hinj (globalFirstRawPool pool b) Ψ hΨ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon) hX
    change globalFirstColumnMass p hg pool b Ψ m g ell side≤Cg at hm
    have hm0 : 0≤globalFirstColumnMass p hg pool b Ψ m g ell side :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hc : 0≤globalFirstCoefficient p K ell B F side b :=
      globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB0 hF _
    have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB0 hF _
    have hwb := hw b (ht b hb)
    have hwΓ := hwb.2
    rw [Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hwb.1 hc),abs_of_pos hY]
    have hsc := globalFirst_diagonal_scalar p hp K ell B F hK hell hB0 hF side b
    have hsc' : globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹≤((Real.exp 1)^3*ell*B^2*F)*θ b := by
      convert hsc using 1 ; dsimp [θ] ; ring
    calc
      _ = (w b*‖paperRadialFourier W 0‖*globalFirstColumnMass p hg pool b Ψ m g ell side)*
          (globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹) := by ring
      _ ≤ (Γ*‖paperRadialFourier W 0‖*Cg)*
          (globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹) := by gcongr
      _ ≤ (Γ*‖paperRadialFourier W 0‖*Cg)*(((Real.exp 1)^3*ell*B^2*F)*θ b) :=
        mul_le_mul_of_nonneg_left hsc' (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (Γ*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3*ell*B^2*F)*(∑b∈T,θ b) := by
      unfold globalFirstDiagonalCost
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    _ ≤ (Γ*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3*ell*B^2*F)*
        (Cd*B^(1+ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = P*Γ*(ell*B^3*F)*
        (B^(ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      dsimp [P]
      ring
    _ ≤ P*Γ*(ell*B^3*F)*(Cp*(B*U)^ε) :=
      mul_le_mul_of_nonneg_left (hpowers B U hB hU) (by positivity)
    _ ≤ (P*Cp+1)*Γ*(ell*B^3*F)*(B*U)^ε := by
      calc
        _ = (P*Cp)*(Γ*(ell*B^3*F)*(B*U)^ε) := by ring
        _ ≤ (P*Cp+1)*(Γ*(ell*B^3*F)*(B*U)^ε) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic LocalReflectionBrackets

theorem bracket_one_eq_quadratic (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (z : O) :
    bracket (actualSextic P hg) 1 (Ideal.Quotient.mk P z)=
      (actualSextic P hg (Ideal.Quotient.mk P z))^3 := by
  simp only [bracket,show (1:ℕ)≠4 by decide,show (1:ℕ)≠0 by decide,↓reduceIte]
  rw [show (1:ℕ)+2=3 by rfl,MulChar.inv_apply_eq_inv',MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]
  by_cases hz : z∈P
  · have he : Ideal.Quotient.mk P z=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
    simp [he]
  · have h6 := canonicalSextic_sixth_power_mask P hg z
    change actualSextic P hg (Ideal.Quotient.mk P (z^6))=_ at h6
    simp only [map_pow,ite_eq_right hz] at h6
    apply inv_eq_of_mul_eq_one_right
    calc
      _ = (actualSextic P hg (Ideal.Quotient.mk P z))^6 := by ring
      _ = 1 := h6

theorem quadratic_value_cube (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (b : O) :
    (actualSextic P hg (Ideal.Quotient.mk P (b^3)))^3=
      (actualSextic P hg (Ideal.Quotient.mk P b))^3 := by
  simp only [map_pow]
  by_cases hb : b∈P
  · have he : Ideal.Quotient.mk P b=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    simp [he]
  · have h6 := canonicalSextic_sixth_power_mask P hg b
    change actualSextic P hg (Ideal.Quotient.mk P (b^6))=_ at h6
    simp only [map_pow,ite_eq_right hb] at h6
    calc
      _ = (actualSextic P hg (Ideal.Quotient.mk P b))^3 *
          (actualSextic P hg (Ideal.Quotient.mk P b))^6 := by ring
      _ = _ := by rw [h6,mul_one]

theorem residual_bracket_cube (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (z n b : O) :
    bracket (actualSextic P hg) 1 (Ideal.Quotient.mk P (z*n*b^3))=
      (actualSextic P hg (Ideal.Quotient.mk P z))^3 *
      (actualSextic P hg (Ideal.Quotient.mk P (n*b)))^3 := by
  rw [bracket_one_eq_quadratic]
  simp only [map_mul,mul_pow]
  rw [quadratic_value_cube]
  ring

theorem residual_bracket_product {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (z n b : O) :
    (∏i,bracket (actualSextic (P i) (hg i)) 1 (Ideal.Quotient.mk (P i) (z*n*b^3)))=
      finiteSexticRow P hg (fun _ => 3) z * finiteSexticRow P hg (fun _ => 3) (n*b) := by
  simp_rw [residual_bracket_cube,Finset.prod_mul_distrib]
  simp only [finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]

end

section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel

theorem powerful_inverse_norm_sum (S : Finset (Ideal O))
    (hS : ∀I∈S,PowerfulIdeal I) :
    (∑I∈S,1/(Ideal.absNorm I:ℝ))≤1048576 := by
  let A := S.image powerfulBase
  let B := S.image squarefreePart
  let pair : Ideal O→Ideal O×Ideal O := fun I => (powerfulBase I,squarefreePart I)
  have ha (I : Ideal O) (hI : I∈A) : I≠0 := by
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (powerfulBase_spec J (hS J hJ)).1
  have hb (I : Ideal O) (hI : I∈B) : I≠0 := by
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (squarefree_squarefreePart J).ne_zero
  have hca : (∑I∈A,1/(Ideal.absNorm I:ℝ)^2)≤1024 :=
    finite_inverse_norm_square_sum A (∑I∈A,(Ideal.absNorm I:ℝ)) ha
      (fun I hI => Finset.single_le_sum (fun J _ => Nat.cast_nonneg _) hI)
  have hcb : (∑I∈B,1/(Ideal.absNorm I:ℝ)^2)≤1024 :=
    finite_inverse_norm_square_sum B (∑I∈B,(Ideal.absNorm I:ℝ)) hb
      (fun I hI => Finset.single_le_sum (fun J _ => Nat.cast_nonneg _) hI)
  have hinj : Set.InjOn pair S := by
    intro I hI J hJ he
    exact powerfulBase_injective_on_fiber I J (hS I hI) (hS J hJ)
      (congrArg Prod.snd he) (congrArg Prod.fst he)
  have hsub : S.image pair ⊆ A×ˢB := by
    intro p hp
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hI,Finset.mem_image_of_mem _ hI⟩
  calc
    _ ≤ ∑I∈S,1/(Ideal.absNorm (powerfulBase I):ℝ)^2 *
        (1/(Ideal.absNorm (squarefreePart I):ℝ)^2) := by
      apply Finset.sum_le_sum
      intro I hI
      have hni := (powerfulBase_spec I (hS I hI)).2
      have hb1 : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (fun hz => (squarefree_squarefreePart I).ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
      have ha0 : 0<(Ideal.absNorm (powerfulBase I):ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero
          (fun hz => (powerfulBase_spec I (hS I hI)).1 (Ideal.absNorm_eq_zero_iff.mp hz))
      have he : (Ideal.absNorm I:ℝ)=(Ideal.absNorm (powerfulBase I):ℝ)^2*
          (Ideal.absNorm (squarefreePart I):ℝ)^3 := by
        have h := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) hni
        simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using h.symm
      rw [he,one_div,one_div,one_div,←mul_inv]
      exact inv_anti₀ (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by decide)) (sq_nonneg _))
    _ = ∑p∈S.image pair,1/(Ideal.absNorm p.1:ℝ)^2 * (1/(Ideal.absNorm p.2:ℝ)^2) := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑p∈A×ˢB,1/(Ideal.absNorm p.1:ℝ)^2 * (1/(Ideal.absNorm p.2:ℝ)^2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑I∈A,1/(Ideal.absNorm I:ℝ)^2)*(∑I∈B,1/(Ideal.absNorm I:ℝ)^2) := by
      rw [Finset.sum_product,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro I _
      rw [Finset.mul_sum]
    _ ≤ 1024*1024 := mul_le_mul hca hcb (by positivity) (by norm_num)
    _ = _ := by norm_num

end

open ActualEisensteinCubic UniqueFactorizationMonoid

theorem prime_square_dvd_powerful (I P : Ideal O) (hI : PowerfulIdeal I)
    (hP : Prime P) (hd : P∣I) : P^2∣I := by
  have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI.1).mpr ⟨hP,hd⟩
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero 2 hP.ne_zero) hI.1).mpr
  rw [normalizedFactors_pow,normalizedFactors_irreducible hP.irreducible,normalize_eq]
  apply Multiset.le_iff_count.mpr
  intro Q
  by_cases hQP : Q=P
  · subst Q
    simpa using hI.2 P hm
  · simp [hQP]

theorem nonresidual_prime_square_dvd (I Q P : Ideal O) (hI : I≠0) (hP : Prime P)
    (hd : P∣I) (hr : ¬P∣rowResidualPart I Q) :
    P^2∣rowPowerfulPart I*(rowMaskPart I Q)^2 := by
  have hh : P∣rowPowerfulPart I*rowMaskPart I Q := by
    rw [←row_powerful_mask_residual_product I Q hI] at hd
    exact (hP.dvd_mul.mp hd).resolve_right hr
  rcases hP.dvd_mul.mp hh with ha|ht
  · exact dvd_mul_of_dvd_left (prime_square_dvd_powerful _ _ (rowPowerfulPart_powerful I) hP ha) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ht 2) _

def nonresidualGain (I P : Ideal O) : Ideal O := if P∣I then P^2 else P

theorem nonresidual_gain_product_dvd {ι : Type*} [Fintype ι]
    (I Q : Ideal O) (hI : I≠0) (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) :
    (∏i,nonresidualGain I (P i)) ∣ rowPowerfulPart I*(rowMaskPart I Q)^2*Q := by
  apply Fintype.prod_dvd_of_coprime
  · intro i j hij
    change IsCoprime (nonresidualGain I (P i)) (nonresidualGain I (P j))
    unfold nonresidualGain
    by_cases hi : P i∣I
    · rw [ite_eq_left hi]
      by_cases hj : P j∣I
      · rw [ite_eq_left hj]
        exact (hcop hij).pow
      · rw [ite_eq_right hj]
        exact (hcop hij).pow_left
    · rw [ite_eq_right hi]
      by_cases hj : P j∣I
      · rw [ite_eq_left hj]
        exact (hcop hij).pow_right
      · rw [ite_eq_right hj]
        exact hcop hij
  · intro i
    have hp : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
    by_cases hi : P i∣I
    · rw [nonresidualGain,ite_eq_left hi]
      exact dvd_mul_of_dvd_left (nonresidual_prime_square_dvd I Q (P i) hI hp hi (hres i)) Q
    · rw [nonresidualGain,ite_eq_right hi]
      exact dvd_mul_of_dvd_right ((hp.dvd_mul.mp (hpool i)).resolve_left hi) _

open ActualEisensteinCubic UniqueFactorizationMonoid

def completedLocalExponent (I F P : Ideal O) : ℕ :=
  ((normalizedFactors I).count P+4*(if P∣F then 1 else 0))%6

def reflectionExtractedPrime (P : Ideal O) (j : ℕ) (e v : Fin 3) : Ideal O :=
  if (j=4 ∧ e=v) ∨ (j=0 ∧ v=0) then P else 1

def reflectionExtractedDivisor {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) : Ideal O :=
  ∏i,reflectionExtractedPrime (P i) (j i) (e i) v

def reflectionConductorCost {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (j : ι→ℕ) (e : ι→Fin 3) : ℝ :=
  (Ideal.absNorm (∏i,P i):ℝ)^2/
    ((Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
     (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
     (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)^4)

def reflectionLocalCost (q : ℝ) (j : ℕ) (e : Fin 3) : ℝ :=
  if j=4 then (if e=2 then 1/q^2 else q)
  else if j=0 then q else q^2

theorem reflectionConductorCost_eq_prod {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hP : ∀i,P i≠0) (j : ι→ℕ) (e : ι→Fin 3) :
    reflectionConductorCost P j e=∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (j i) (e i) := by
  have hn i : (Ideal.absNorm (P i):ℝ)≠0 := by
    exact_mod_cast (fun hz => hP i (Ideal.absNorm_eq_zero_iff.mp hz))
  simp only [reflectionConductorCost,reflectionExtractedDivisor,map_prod,Nat.cast_prod,
    ←Finset.prod_pow,←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hj4 : j i=4
  · rw [hj4]
    generalize he : e i=v
    fin_cases v <;> simp [reflectionExtractedPrime,reflectionLocalCost] <;> field_simp
  · by_cases hj0 : j i=0
    · simp [reflectionExtractedPrime,reflectionLocalCost,hj0]
      field_simp
    · simp [reflectionExtractedPrime,reflectionLocalCost,hj4,hj0]

theorem reflectionLocalCost_nonneg (q : ℝ) (hq : 0≤q) (j : ℕ) (e : Fin 3) :
    0≤reflectionLocalCost q j e := by
  unfold reflectionLocalCost
  split_ifs <;> positivity

theorem reflectionLocalCost_le_square (q : ℝ) (hq : 1≤q) (j : ℕ) (e : Fin 3) :
    reflectionLocalCost q j e≤q^2 := by
  have hq0 : 0<q := by linarith
  have hq2 : 1≤q^2 := one_le_pow₀ hq
  unfold reflectionLocalCost
  split_ifs
  · exact (div_le_one (by positivity)).mpr hq2 |>.trans hq2
  · nlinarith
  · nlinarith
  · rfl

theorem reflectionLocalCost_le_single (q : ℝ) (hq : 1≤q) (j : ℕ) (e : Fin 3)
    (hj : j=0 ∨ j=4) : reflectionLocalCost q j e≤q := by
  have hq0 : 0<q := by linarith
  rcases hj with rfl|rfl
  · simp [reflectionLocalCost]
  · simp only [reflectionLocalCost,ite_true]
    split_ifs
    · exact ((div_le_one (by positivity)).mpr (one_le_pow₀ hq)).trans hq
    · rfl

theorem completedLocalExponent_of_not_dvd (I F P : Ideal O) (hI : I≠0) (_hP : Prime P)
    (hn : ¬P∣I) : completedLocalExponent I F P=0 ∨ completedLocalExponent I F P=4 := by
  have hm : P∉normalizedFactors I := by
    intro h
    exact hn ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mp h).2
  simp only [completedLocalExponent,Multiset.count_eq_zero.mpr hm,zero_add]
  split_ifs <;> norm_num

theorem reflectionLocalCost_le_gain (I F P : Ideal O) (hI : I≠0) (hP : Prime P) (e : Fin 3) :
    reflectionLocalCost (Ideal.absNorm P:ℝ) (completedLocalExponent I F P) e≤
      (Ideal.absNorm (nonresidualGain I P):ℝ) := by
  have hq : 1≤(Ideal.absNorm P:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  by_cases hd : P∣I
  · rw [nonresidualGain,ite_eq_left hd,map_pow,Nat.cast_pow]
    exact reflectionLocalCost_le_square _ hq _ _
  · rw [nonresidualGain,ite_eq_right hd]
    exact reflectionLocalCost_le_single _ hq _ _ (completedLocalExponent_of_not_dvd I F P hI hP hd)

theorem reflectionConductorCost_bound {ι : Type*} [Fintype ι]
    (I F Q : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) (e : ι→Fin 3) :
    reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e≤
      (Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ)^2*(Ideal.absNorm Q:ℝ) := by
  rw [reflectionConductorCost_eq_prod P (fun i => NeZero.ne (P i))]
  have hfirst : (∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (completedLocalExponent I F (P i)) (e i))≤
      (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ) := by
    rw [map_prod,Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun i _ => reflectionLocalCost_nonneg _ (Nat.cast_nonneg _) _ _)
      (fun i _ => reflectionLocalCost_le_gain I F (P i) hI (Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance) (e i))
  apply hfirst.trans
  have hd := nonresidual_gain_product_dvd I Q hI P hcop hpool hres
  have hN : 0<Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hne := mul_ne_zero (mul_ne_zero (rowPowerfulPart_ne_zero I)
      (pow_ne_zero 2 (squarefreeMaskPart_ne_zero (rowSimplePart I) Q))) hQ
    exact hne (Ideal.absNorm_eq_zero_iff.mp hz)
  have hb := Nat.le_of_dvd hN (map_dvd Ideal.absNorm hd)
  have hr : (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ)≤
      (Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q):ℝ) := by exact_mod_cast hb
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hr

end CompletedGauss

end

end OAI
