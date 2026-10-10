import OAI.NumberTheory.DirichletL.Inversion.InitialDetectorSource
import OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawRadial
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialConjugateEnergy CanonicalQuadraticSieve
open ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O

theorem exists_raw_radial_majorant :
    ∃Φ : 𝓢(ℝ,ℂ),HasCompactSupport (Φ:ℝ→ℂ) ∧
      (∀x,0≤(Φ x).re) ∧ (∀x∈Set.Icc (0:ℝ) 1,Φ x=1) := by
  have hsub : Set.Icc (0:ℝ) 1⊆Set.Ioo (-1) 2 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v : ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv : ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf : ContDiff ℝ ∞ f).pow 2)
  have hsupp : Function.support v⊆Set.Icc (-1) 2 := by
    intro x hx
    have hn : x∈Function.support f := by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  have hvc:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

private theorem admissible_one : Admissible (1:Ideal O) := by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

theorem finite_raw_le_initial_smoothed (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀x,0≤(Φ x).re) (hone : ∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data : RowData) (W : ℝ→ℂ) (b Z r σ t H : ℝ)
    (hZ : 0<Z) (hH : 0<H) (hW : ∀x,W x≠0 → x≤b)
    (rows : Finset NonzeroElement)
    (hrows : ∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H) :
    (∑u∈rows,‖polynomial (data.character u) true W (Z^r) σ t‖^2)≤
      smoothedEnergy Φ H
        (originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter Supported)
          1 (fixedBase data.η data.m data.f) (fun _=>1)
          (twistedProfile W σ t) Z r 0) := by
  let S:=(ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*b⌉₊).filter Supported
  let f:=originalTotalPolynomial S 1 (fixedBase data.η data.m data.f) (fun _=>1)
    (twistedProfile W σ t) Z r 0
  have hsum : Summable (fun u:O=>radialWeight Φ H u*‖f u‖^2) :=
    (original_smoothed_overlap_triangle S admissible_one
      (fun n hn _=>(Finset.mem_filter.mp hn).2) (fixedBase data.η data.m data.f)
      (fun _=>1) (twistedProfile W σ t) hZ r 0 (fun _=>0) Φ (fun x _=>hΦ x) hH).1
  have he (u : NonzeroElement) (hu : u∈rows) :
      ‖polynomial (data.character u) true W (Z^r) σ t‖^2=
        radialWeight Φ H u.val*‖f u.val‖^2 := by
    have hn : ‖eisEmbedding u.val‖^2/H∈Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hH.le,?_⟩
      apply (div_le_one hH).mpr
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    rw [character_eq_initial data u W Z r σ t b hZ hW]
    change ‖f u.val‖^2=(Φ (‖eisEmbedding u.val‖^2/H)).re*‖f u.val‖^2
    rw [hone _ hn,Complex.one_re,one_mul]
  calc
    _=∑u∈rows,radialWeight Φ H u.val*‖f u.val‖^2:=Finset.sum_congr rfl he
    _=∑u∈rows.image Subtype.val,radialWeight Φ H u*‖f u‖^2:=by
      rw [Finset.sum_image (fun a _ b _ hab=>Subtype.val_injective hab)]
    _≤∑'u:O,radialWeight Φ H u*‖f u‖^2:=hsum.sum_le_tsum _
      (fun u _=>mul_nonneg (hΦ _) (sq_nonneg _))
    _= _:=rfl

end SevenEighths.DetectorDictionaryInverseRawRadial

end

end OAI
