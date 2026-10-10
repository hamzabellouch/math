import OAI.NumberTheory.DirichletL.Hecke.PrimePowers
import OAI.NumberTheory.DirichletL.PrimeLogProfile

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Set
namespace SevenEighths.HeckePrimeAnnular
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def annulusSet (b D : ℝ) : Finset (Ideal O) := idealsUpTo ⌊max 1 b*D⌋₊

def annularWeight (W : ℝ→ℂ) (D σ freq : ℝ) (I : Ideal O) : ℂ :=
  W ((I.absNorm : ℝ)/D)*(((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-shift σ freq)

def primePolynomial (χ : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ I∈(annulusSet b D).filter Prime,
    idealCoeff χ I*annularWeight W D σ freq I

theorem annular_support (W : ℝ→ℂ) (a b D : ℝ) (ha : 0<a) (hD : 0<D)
    (hWs : Function.support W⊆Icc a b) (I : Ideal O)
    (hw : W ((I.absNorm : ℝ)/D)≠0) : I∈annulusSet b D := by
  have hs := hWs hw
  apply mem_idealsUpTo.mpr
  constructor
  · have hnorm : 0<(I.absNorm : ℝ) := by
      have := (le_div_iff₀ hD).mp hs.1
      nlinarith
    exact_mod_cast hnorm
  · have hn := (div_le_iff₀ hD).mp hs.2
    exact Nat.le_floor (hn.trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le))

theorem log_polynomial_eq_finite (χ : Character) (W : ℝ→ℂ) (a b D σ freq : ℝ)
    (ha : 0<a) (hD : 0<D) (hWs : Function.support W⊆Icc a b)
    (hlarge : 2*(|Real.log a|+|Real.log b|)+1≤Real.log D) :
    HeckePrimeDyadic.polynomial χ (PrimeLogProfile.profile W (1/Real.log D)) D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑ I∈annulusSet b D,
        (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I := by
  rw [PrimeLogProfile.profile_eq_log_division W a b D ha hWs hD hlarge]
  unfold HeckePrimeDyadic.polynomial
  congr 1
  have he : (fun I : NonzeroIdeal => HeckePrimeDyadic.summand χ
      (fun y => W y/(Real.log (D*y) : ℂ)) D σ freq I) =
      fun I : NonzeroIdeal => (HeckePrimePowers.logWeight I.val : ℂ)*
        idealCoeff χ I.val*annularWeight W D σ freq I.val := by
    funext I
    unfold HeckePrimeDyadic.summand HeckePrimeDyadic.coefficient annularWeight
    dsimp only [HeckePrimePowers.logWeight, HeckeDyadic.norm]
    rw [mul_div_cancel₀ _ hD.ne']
    simp only [Complex.ofReal_div]
    ring
  rw [he]
  calc
    _ = ∑' I : Ideal O, (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I := by
      apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | I≠0})
        (f := fun I : Ideal O => (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I)
      intro I hI hzero
      subst I
      exact hI (by simp [HeckePrimePowers.logWeight])
    _ = _ := by
      apply tsum_eq_sum
      intro I hI
      have hw : W ((I.absNorm : ℝ)/D)=0 := by
        by_contra hh
        exact hI (annular_support W a b D ha hD hWs I hh)
      simp [annularWeight,hw]

theorem fixed_profile_norm_bound (W : ℝ→ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0<a) :
    ∃ B : ℝ, 0<B ∧ ∀ σ∈Icc lo hi, ∀ y∈Icc a b, ‖W y‖*y^(-σ)≤B := by
  let K : Set (ℝ×ℝ) := Icc lo hi ×ˢ Icc a b
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun p : ℝ×ℝ => ‖W p.2‖*p.2^(-p.1)) K := by
    apply (hW.comp continuous_snd).norm.continuousOn.mul
    exact continuous_snd.continuousOn.rpow continuous_fst.neg.continuousOn
      (fun p hp => Or.inl (ne_of_gt (ha.trans_le hp.2.1)))
  obtain ⟨M,hM⟩ := hK.bddAbove_image hc
  refine ⟨|M|+1,by positivity,?_⟩
  intro σ hσ y hy
  exact (hM (Set.mem_image_of_mem _ (show (σ,y)∈K from ⟨hσ,hy⟩))).trans
    (by linarith [le_abs_self M])

theorem extraction_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character) (W : ℝ→ℂ) (a b D σ freq B : ℝ),
      0<a → 1≤D → Function.support W⊆Icc a b →
      2*(|Real.log a|+|Real.log b|)+1≤Real.log D → 0≤B →
      (∀ y∈Icc a b, ‖W y‖*y^(-σ)≤B) →
      ‖HeckePrimeDyadic.polynomial χ (PrimeLogProfile.profile W (1/Real.log D)) D σ freq -
        primePolynomial χ W b D σ freq‖≤
        C*(max 1 b)^((1/2 : ℝ)+ε)*D^ε*B := by
  obtain ⟨C,hC,herr⟩ := HeckePrimePowers.prime_extraction_error ε hε
  refine ⟨C,hC,?_⟩
  intro χ W a b D σ freq B ha hD hWs hlarge hB hWbound
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hX : 1≤max 1 b*D := hD.trans (le_mul_of_one_le_left hDp.le (le_max_left _ _))
  have hnorm (I : Ideal O) (hI : I∈annulusSet b D) : (I.absNorm : ℝ)≤max 1 b*D := by
    exact (Nat.cast_le.mpr (mem_idealsUpTo.mp hI).2).trans
      (Nat.floor_le (by positivity))
  have hw (I : Ideal O) (_hI : I∈annulusSet b D) : ‖annularWeight W D σ freq I‖≤B := by
    by_cases hz : W ((I.absNorm : ℝ)/D)=0
    · simpa [annularWeight,hz] using hB
    · have hs := hWs hz
      have hy : 0<(I.absNorm : ℝ)/D := ha.trans_le hs.1
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy]
      simpa only [Complex.neg_re,shift_re] using hWbound _ hs
  have hb := herr χ (annulusSet b D) (annularWeight W D σ freq) (max 1 b*D) B
    hX hB hnorm hw
  have hn : ‖(D : ℂ)^(-(1/2 : ℂ))‖=D^(-(1/2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hDp]
    norm_num
  rw [log_polynomial_eq_finite χ W a b D σ freq ha hDp hWs hlarge,
    primePolynomial,←mul_sub,norm_mul,hn]
  calc
    _ ≤ D^(-(1/2 : ℝ))*(C*(max 1 b*D)^(1/2+ε)*B) := by
      exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hDp.le _)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0≤max 1 b) hDp.le]
      have he : D^(-(1/2 : ℝ))*D^(1/2+ε)=D^ε := by
        rw [←Real.rpow_add hDp]
        congr 1
        ring
      calc
        _ = C*(max 1 b)^(1/2+ε)*(D^(-(1/2 : ℝ))*D^(1/2+ε))*B := by ring
        _ = _ := by rw [he]

end SevenEighths.HeckePrimeAnnular

end

end OAI
