import OAI.NumberTheory.DirichletL.Dictionary.InverseRawRadial
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawFiberSource
import OAI.NumberTheory.DirichletL.Descent.Basic

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseMarkedPadding
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialPhysicalSlots
open InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialConjugateEnergy
open HeckeDetectorPhysicalSelection ConcreteTraceCRT CanonicalQuadraticSieve ActualEisensteinCubic
local notation "O" => HeckeFamily.O

def radialMajorant : 𝓢(ℝ,ℂ) :=
  Classical.choose DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant

theorem radialMajorant_compact : HasCompactSupport (radialMajorant : ℝ→ℂ) :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).1

theorem radialMajorant_nonneg (x : ℝ) : 0≤(radialMajorant x).re :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.1 x

theorem radialMajorant_one (x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) : radialMajorant x=1 :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.2 x hx

theorem compact_radial_summable (Φ : 𝓢(ℝ,ℂ))
    (hΦ : HasCompactSupport (Φ : ℝ→ℂ)) (Y : ℝ) (hY : 0<Y) (f : O→ℂ) :
    Summable (fun u : O=>radialWeight Φ Y u*‖f u‖^2) := by
  obtain ⟨B,hB⟩ := hΦ.isBounded.exists_norm_le
  let R := ShortDraftLatticeCount.rowNormBall ⌈B*Y⌉₊
  apply (hasSum_sum_of_ne_finset_zero (s:=R) ?_).summable
  intro u hu
  have hz : Φ (‖eisEmbedding u‖^2/Y)=0 := by
    by_contra hn
    have hb := hB _ (subset_tsupport Φ hn)
    have hnB : (Ideal.absNorm (Ideal.span {u}):ℝ)≤B*Y := by
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) hY.le)] at hb
      rw [eisEmbedding_norm_sq_eq_absNorm_span] at hb
      exact (div_le_iff₀ hY).mp hb
    apply hu
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    exact_mod_cast hnB.trans (Nat.le_ceil (B*Y))
  simp [radialWeight,hz]

theorem radialMajorant_summable (Y : ℝ) (hY : 0<Y) (f : O→ℂ) :
    Summable (fun u : O=>radialWeight radialMajorant Y u*‖f u‖^2) :=
  compact_radial_summable radialMajorant radialMajorant_compact Y hY f

theorem finite_source_le_smoothed {Row : Type*} (rows : Finset Row)
    (row : Row→O) (hinj : Function.Injective row) (f : O→ℂ)
    (Y : ℝ) (hY : 0<Y)
    (hrows : ∀u∈rows,((Ideal.span {row u}).absNorm:ℝ)≤Y) :
    (∑u∈rows,‖f (row u)‖^2)≤smoothedEnergy radialMajorant Y f := by
  have he (u : Row) (hu : u∈rows) :
      ‖f (row u)‖^2=radialWeight radialMajorant Y (row u)*‖f (row u)‖^2 := by
    have hn : ‖eisEmbedding (row u)‖^2/Y∈Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hY.le,?_⟩
      apply (div_le_one hY).mpr
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    simp [radialWeight,radialMajorant_one _ hn]
  calc
    _=∑u∈rows,radialWeight radialMajorant Y (row u)*‖f (row u)‖^2 :=
      Finset.sum_congr rfl he
    _=∑u∈rows.image row,radialWeight radialMajorant Y u*‖f u‖^2 := by
      rw [Finset.sum_image (fun a _ b _ hab=>hinj hab)]
    _≤∑'u : O,radialWeight radialMajorant Y u*‖f u‖^2 :=
      (radialMajorant_summable Y hY f).sum_le_tsum _
        (fun u _=>mul_nonneg (radialMajorant_nonneg _) (sq_nonneg _))
    _=smoothedEnergy radialMajorant Y f := rfl

variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def selectedSource (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (u : O) : ℂ :=
  ∑p∈Fintype.piFinset (fun s:selected=>
      livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
    (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
      fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
    originalTotalPolynomial
      ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
      (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
      (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
      U F.r (∑s:selected,F.widths s) u

omit [NeZero M] in
theorem selectedSource_norm (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0<U) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s))
    (u : FreeRow) (hu : u∈F.rows) :
    ‖polynomial (F.family u F.label) true W (U^F.r) σ t*F.physicalProduct selected u‖=
      ‖selectedSource F selected W σ t bW u.val‖ :=
  DetectorDictionaryInverseRawFiberSource.fiber_physical_norm_initial
    F selected W σ t bW lower hU hW hV hlarge u hu

omit [NeZero M] in
theorem selectedSource_summable
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW Y : ℝ) (hY : 0<Y) :
    Summable (fun u : O=>radialWeight radialMajorant Y u*
      ‖selectedSource F selected W σ t bW u‖^2) :=
  radialMajorant_summable Y hY _

omit [NeZero M] in
theorem selectedSource_energy
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0<U) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ t*
      F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖selectedSource F selected W σ t bW u.val‖^2 :=
  DetectorDictionaryInverseRawFiberSource.fiber_physical_energy_initial
    F selected W σ t bW lower hU hW hV hlarge

omit [NeZero M] in
theorem fiber_physical_le_padded_smoothed
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW ρ : ℝ) (lower : Slot→ℝ)
    (hU : 1≤U) (hρ : 0≤ρ) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ t*
      F.physicalProduct selected u‖^2)≤
      smoothedEnergy radialMajorant (U^(1+ρ)) (selectedSource F selected W σ t bW) := by
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hpad : U≤U^(1+ρ) := by
    calc
      U=U^(1:ℝ) := (Real.rpow_one U).symm
      _≤U^(1+ρ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  calc
    _=∑u∈F.rows,‖selectedSource F selected W σ t bW u.val‖^2 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [selectedSource_norm F selected W σ t bW lower hU0 hW hV hlarge u hu]
    _≤_ := finite_source_le_smoothed F.rows (fun u : FreeRow=>u.val)
      Subtype.val_injective _ _ (Real.rpow_pos_of_pos hU0 _)
      (fun u hu=>(F.row_norm u hu).trans hpad)

omit [NeZero M] in
theorem fiber_inverse_le_padded_smoothed
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (n : ℕ) (σ t ρ : ℝ) (lower : Slot→ℝ)
    (hU : 1≤U) (hρ : 0≤ρ)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) (U^F.r) σ t*
      F.physicalProduct selected u‖^2)≤
      smoothedEnergy radialMajorant (U^(1+ρ))
        (selectedSource F selected ((HeckeDetectorRowwisePolynomial.logProfile^[n])
          F.inverseProfile) σ t (9/4)) :=
  fiber_physical_le_padded_smoothed F selected _ σ t (9/4) ρ lower hU hρ
    (DetectorDictionaryInverseRawFiberSource.fiber_inverse_log_upper F n) hV hlarge

theorem fixed_padding_margins (r z ρ : ℝ) (hρ : 0≤ρ)
    (hfirst : r+2*z<1) (hsecond : 2*r+8*z<3) :
    r+2*z≤(1+ρ)-ρ ∧ 2*r+8*z≤3*(1+ρ)-3*ρ ∧
      InverseMoment.MarkedMargins (1+ρ) r z ρ := by
  unfold InverseMoment.MarkedMargins
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

omit [NeZero M] in
theorem fiber_padding_margins
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (ρ : ℝ) (hρ : 0≤ρ)
    (hfirst : F.r+2*(∑s∈selected,F.widths s)<1)
    (hsecond : 2*F.r+8*(∑s∈selected,F.widths s)<3) :
    F.r+2*(∑s∈selected,F.widths s)≤(1+ρ)-ρ ∧
      2*F.r+8*(∑s∈selected,F.widths s)≤3*(1+ρ)-3*ρ ∧
      InverseMoment.MarkedMargins (1+ρ) F.r (∑s∈selected,F.widths s) ρ :=
  fixed_padding_margins _ _ ρ hρ hfirst hsecond

theorem padded_output_budget (U C ρ loss εm : ℝ) (hU : 1≤U) (hC : 0≤C)
    (hbudget : ρ+loss≤εm) : C*U^(1+ρ+loss)≤C*U^(1+εm) := by
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_le hU (by linarith)

end SevenEighths.DetectorDictionaryInverseMarkedPadding

end

end OAI
