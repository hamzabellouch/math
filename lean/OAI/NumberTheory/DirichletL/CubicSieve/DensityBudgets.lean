import OAI.NumberTheory.DirichletL.Eisenstein.CoordinateLaplacian

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace SecondPassArithmetic

section

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy_from_canonical_state)

def canonicalDensityConstant (E : ℝ) (J : ℕ) (t : ℝ) : ℝ :=
  6*E*(1+‖t‖)^(2*J)*(∫s : ℝ,firstLogDensity 0 s)^3

theorem canonicalDensityConstant_nonneg (E : ℝ) (hE : 0≤E) (J : ℕ) (t : ℝ) :
    0≤canonicalDensityConstant E J t := by
  have hi : 0≤∫s : ℝ,firstLogDensity 0 s :=
    integral_nonneg (fun s=>FirstPassCubeLabels.firstLogDensity_nonneg 0 s)
  unfold canonicalDensityConstant
  positivity

theorem globalFirstQuantitativeBudget_state_bound (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃ Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (windows : Fin 7 → ℝ → ℂ)
      (C Cd Ct Γ E oldHeight K ell B F M H U Z θ A₀ Vmax : ℝ) (N J Ntail : ℕ),
      0≤C → 0≤Γ → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0 → |t|≤A₀) → (∀t,windows 6 t≠0 → |t|≤A₀) →
      (∀u,‖Ψ u‖≤1) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (let source := globalQuantitativeSource p pool blocks K ell B F M H U side
       ∀a : RayCharacter×RayCharacter,∀r : FirstCoreIndex,
       ∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),
       ∀ray : SecondRayIndex,∀q∈globalBinTriples p source side j,
       let Ψmode := firstCoreTwist side (if side then a.1 else a.2) Ψ r
       ∀s : ℝ,
       (canonicalLogEnergy p hp hcop hg pool (normHeightTwist (secondRayMinus Ψmode ray) s)
         (fixedTripleMask m q) (globalCanonicalLabels p source side q j)
         (orientedLogProfile true (windows 5)) (globalPooledColumnScale ell j)
         (globalLogRep j 8*Real.exp 1)≤
         E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2*(1+‖s‖)^(2*J)) ∧
       (canonicalLogEnergy p hp hcop hg pool (normHeightTwist (secondRayPlus Ψmode ray) s)
         (fixedTripleMask m q) (globalCanonicalLabels p source side q j)
         (orientedLogProfile false (windows 6)) (globalPooledColumnScale ell j)
         (globalLogRep j 8*Real.exp 1)≤
         E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2*(1+‖s‖)^(2*J))) →
      globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ oldHeight) m windows
        C Cd Ct Γ ε K ell B F M H U (N+1) (2*J) Ntail side ≤
        (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*((ell*B^3)*F)*
          ((B*U)^ε*(Cd+Ct*globalFirstTailFactor K ell B F U H Ntail)+
           C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
             (canonicalDensityConstant E J oldHeight*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N))) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstQuantitativeBudget_canonical_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj pool blocks side Ψ m windows C Cd Ct Γ E oldHeight K ell B F M H U Z θ A₀ Vmax N J Ntail
    hC hΓ hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hb₁ hb₂ he
  apply hbound p hp hcop hg hc hinj pool blocks side (normHeightTwist Ψ oldHeight) m windows
    C Cd Ct Γ (canonicalDensityConstant E J oldHeight) K ell B F M H U Z θ A₀ Vmax N J Ntail
    hC hΓ (canonicalDensityConstant_nonneg E hE J oldHeight) hU hK hell hB hF hH
    hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂
    (fun u=>(normHeightTwist_norm_le Ψ oldHeight u).trans (hΨ u)) hb₁ hb₂
  dsimp only
  intro a r j hj ray q hq
  rw [firstCoreTwist_normHeight,secondRayMinus_normHeight,secondRayPlus_normHeight]
  let source := globalQuantitativeSource p pool blocks K ell B F M H U side
  have hk : ∀x∈source,x.source.frequency≠0 :=
    fun x hx=>globalQuantitativeSource_frequency_ne_zero p pool blocks K ell B F M H U side x hx
  have hkc : 0<globalLogRep j 8*Real.exp 1 := mul_pos (globalLogRep_pos j 8) (Real.exp_pos 1)
  have hs := he a r j hj ray q hq
  have hd := densityChildEnergy_from_canonical_state p hp hcop hg pool
    (secondRayMinus (firstCoreTwist side (if side then a.1 else a.2) Ψ r) ray)
    (secondRayPlus (firstCoreTwist side (if side then a.1 else a.2) Ψ r) ray)
    (fixedTripleMask m q) (globalArithmeticTargets p source side q j)
    (globalCanonicalLabels p source side q j) (windows 5) (windows 6)
    (globalPooledColumnScale ell j) (globalPooledLabelScale j) (globalLogRep j 8*Real.exp 1)
    E oldHeight oldHeight J (globalPooledColumnScale_pos ell hell j) hkc hE
    (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩)
    (fun z hz=>(globalArithmeticTargets_bounds p hp source side q j hk z hz).2.2)
    (globalArithmeticTargets_nonzero p source side q j hk)
    (fun t=>(hs t).1) (fun t=>(hs t).2)
  exact hd.trans_eq (by unfold canonicalDensityConstant; rw [two_mul,pow_add]; ring)

end

open ActualEisensteinCubic ConcreteTraceCRT

def canonicalRankMass (Z : ℝ) (r : ℕ) : ℝ :=
  Real.exp (3*((3000-r:ℕ):ℝ))*Z^2

theorem canonicalRankMass_initial (Z : ℝ) (r : ℕ) : Z^2≤canonicalRankMass Z r := by
  have he : 1≤Real.exp (3*((3000-r:ℕ):ℝ)) := Real.one_le_exp (by positivity)
  simpa only [one_mul,canonicalRankMass] using mul_le_mul_of_nonneg_right he (sq_nonneg Z)

theorem canonicalRankMass_step (Z : ℝ) (r s : ℕ) (hr : r≤3000) (hs : s+1≤r) :
    Real.exp 3*canonicalRankMass Z r≤canonicalRankMass Z s := by
  have hn : 3000-r+1≤3000-s := by omega
  have hn' : ((3000-r:ℕ):ℝ)+1≤((3000-s:ℕ):ℝ) := by exact_mod_cast hn
  unfold canonicalRankMass
  rw [←mul_assoc,←Real.exp_add]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg Z)

theorem canonicalRankMass_child (Z X F X' F' : ℝ) (r s : ℕ)
    (hr : r≤3000) (hs : s+1≤r) (hparent : X*F≤canonicalRankMass Z r)
    (hchild : X'*F'≤Real.exp 3*(X*F)) : X'*F'≤canonicalRankMass Z s :=
  hchild.trans ((mul_le_mul_of_nonneg_left hparent (Real.exp_pos _).le).trans
    (canonicalRankMass_step Z r s hr hs))

theorem canonicalRankMass_global (Z : ℝ) (hZ : Real.exp 9000≤Z) (r : ℕ) :
    canonicalRankMass Z r≤Z^3 := by
  have hn : ((3000-r:ℕ):ℝ)≤3000 := by exact_mod_cast (Nat.sub_le 3000 r)
  have he : Real.exp (3*((3000-r:ℕ):ℝ))≤Z :=
    (Real.exp_le_exp.mpr (by linarith)).trans hZ
  calc
    canonicalRankMass Z r ≤ Z*Z^2 := mul_le_mul_of_nonneg_right he (sq_nonneg Z)
    _ = Z^3 := by ring

theorem lowerCubeBin_transfer_mass (X B F : ℝ) (hB : B≠0) :
    (X/B^3)*(Real.exp 1*B)^3*F=Real.exp 3*(X*F) := by
  have he : (Real.exp 1)^3=Real.exp 3 := by
    rw [show (3:ℝ)=1+1+1 by norm_num,Real.exp_add,Real.exp_add]
    ring
  rw [mul_pow,←he]
  field_simp

theorem lowerCubeBin_energy_normalization (ell B F : ℝ) (hell : 0<ell) (hB : 0<B) :
    (ell*B^3)*((B*Real.sqrt ell)^2)⁻¹*
      (ell*(Real.exp 1*B)^2*F)*(ell*(Real.exp 1*B)^3*F)=
      Real.exp 5*((ell*B^3)*F)^2 := by
  have he : (Real.exp 1)^5=Real.exp 5 := by
    rw [show (5:ℝ)=1+1+1+1+1 by norm_num]
    simp only [Real.exp_add]
    ring
  rw [mul_pow,Real.sq_sqrt hell.le]
  simp only [mul_pow]
  rw [←he]
  field_simp

theorem canonical_live_scale_bounds (Z X F : ℝ) (r : ℕ)
    (hZ : Real.exp 9000≤Z) (hX : 1≤X) (hF : 1≤F)
    (hmass : X*F≤canonicalRankMass Z r) : X≤Z^3 ∧ F≤Z^3 := by
  have hm := hmass.trans (canonicalRankMass_global Z hZ r)
  constructor <;> nlinarith

theorem canonical_small_or_live (Z X F K : ℝ) (r : ℕ) (m : ActualEisensteinCubic.O)
    (hZ : Real.exp 9000≤Z) (_hX : 0<X) (hF : 1≤F) (hK : 0≤K) (hm : m≠0)
    (hmass : X*F≤canonicalRankMass Z r) (hinv : K*‖eisEmbedding m‖^2≤X*F) :
    K≤F ∨ (1<X ∧ X≤Z^3 ∧ F≤Z^3) := by
  by_cases hx : X≤1
  · exact Or.inl (smallColumn_row_le_label m hm X F K hx (by linarith) hK hinv)
  · have hl := lt_of_not_ge hx
    exact Or.inr ⟨hl,canonical_live_scale_bounds Z X F r hZ hl.le hF hmass⟩

def canonicalPoolCutoff (Bsupport Z : ℝ) : ℕ := ⌈Bsupport*Z^3⌉₊

theorem canonicalPoolCutoff_covers (Bsupport b Z X : ℝ)
    (hB : 0≤Bsupport) (hb : b≤Bsupport) (hX : 0≤X) (hXZ : X≤Z^3) :
    b*X≤(canonicalPoolCutoff Bsupport Z:ℝ) := by
  calc
    b*X ≤ Bsupport*X := mul_le_mul_of_nonneg_right hb hX
    _ ≤ Bsupport*Z^3 := mul_le_mul_of_nonneg_left hXZ hB
    _ ≤ _ := Nat.le_ceil _

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

def rowFamilyEnergy (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) (K : ℝ) : ℝ :=
  (∑ I ∈ labels, nonzeroRowMajorantSum (P I) K).re

theorem rowFamilyEnergy_eq_sum (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ)
    (K : ℝ) (hK : 0 < K) :
    rowFamilyEnergy labels P K =
      ∑ I ∈ labels, ∑ z ∈ (firstFrequencyDisk (2*K)).erase 0,
        (rowMajorant (‖eisEmbedding z‖^2/K)).re * ‖P I z‖^2 := by
  unfold rowFamilyEnergy
  simp only [nonzeroRowMajorantSum_exact_disk _ K hK, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem rowFamilyEnergy_nonneg (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ)
    (K : ℝ) (hK : 0 < K) : 0 ≤ rowFamilyEnergy labels P K := by
  rw [rowFamilyEnergy_eq_sum labels P K hK]
  exact Finset.sum_nonneg (fun I hI => Finset.sum_nonneg
    (fun z hz => mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)))

theorem rowFamilyEnergy_integral_polynomial
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (K : ℝ) (hK : 0 < K)
    (b : ℝ → ℂ) (φ : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℝ → ℂ) (d : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖*(1+|t|)^d))
    (hφ : ∀ I z, Integrable (fun t => b t*φ I z t))
    (hbound : ∀ t, rowFamilyEnergy labels (fun I z => φ I z t) K ≤ E*(1+|t|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ∫ t : ℝ, b t*φ I z t) K ≤
      E*(∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 := by
  let R := (firstFrequencyDisk (2*K)).erase 0
  let w : ActualEisensteinCubic.O → ℝ := fun z => Real.sqrt ((rowMajorant (‖eisEmbedding z‖^2/K)).re)
  have hw (z : ActualEisensteinCubic.O) : 0 ≤ w z := Real.sqrt_nonneg _
  have hw2 (z : ActualEisensteinCubic.O) : (w z)^2 = (rowMajorant (‖eisEmbedding z‖^2/K)).re :=
    Real.sq_sqrt (rowMajorant_nonneg _)
  have hsum (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) :
      (∑ x : labels × R, ‖(w x.2.val : ℂ)*P x.1.val x.2.val‖^2) = rowFamilyEnergy labels P K := by
    rw [rowFamilyEnergy_eq_sum labels P K hK]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_coe_sort (s := labels)
      (f := fun I : Ideal ActualEisensteinCubic.O => ∑ z : R, ‖(w z.val : ℂ)*P I z.val‖^2)]
    apply Finset.sum_congr rfl
    intro I hI
    rw [Finset.sum_coe_sort (s := R) (f := fun z : ActualEisensteinCubic.O => ‖(w z : ℂ)*P I z‖^2)]
    apply Finset.sum_congr rfl
    intro z hz
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw z),mul_pow,hw2]
  let ψ : labels × R → ℝ → ℂ := fun x t => (w x.2.val : ℂ)*φ x.1.val x.2.val t
  have hψ (x : labels × R) : Integrable (fun t => b t*ψ x t) := by
    convert (hφ x.1.val x.2.val).const_mul (w x.2.val : ℂ) using 1
    funext t
    dsimp only [ψ]
    ring
  have hψbound (t : ℝ) : (∑ x : labels × R, ‖ψ x t‖^2) ≤ E*(1+|t|)^(2*d) := by
    change (∑ x : labels × R, ‖(w x.2.val : ℂ)*φ x.1.val x.2.val t‖^2) ≤ _
    rw [hsum (fun I z => φ I z t)]
    exact hbound t
  have hi (x : labels × R) :
      (∫ t : ℝ, b t*ψ x t) = (w x.2.val : ℂ)*(∫ t : ℝ, b t*φ x.1.val x.2.val t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [ψ]
    ring
  have hm := finite_integral_energy_polynomial b ψ d E hE hb hψ hψbound
  simp_rw [hi] at hm
  rwa [hsum (fun I z => ∫ t : ℝ, b t*φ I z t)] at hm

theorem rowFamilyEnergy_const_mul (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ)
    (K : ℝ) (hK : 0 < K) (c : ℂ) :
    rowFamilyEnergy labels (fun I z => c*P I z) K = ‖c‖^2*rowFamilyEnergy labels P K := by
  simp only [rowFamilyEnergy_eq_sum _ _ K hK, norm_mul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem canonicalSmoothedEnergy_eq_rowFamilyEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (H : Finset ι → ℂ) (K : ℝ) :
    canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K =
      rowFamilyEnergy labels (fun I z => fixedChildRow p hp hcop hg pool Ψ m H (idealGenerator I) z) K := rfl

end
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem separated_canonical_integrable
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (b V : 𝓢(ℝ,ℂ)) (B ell : ℝ) :
    Integrable (fun ξ : ℝ => b ξ *
      reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient β n B ξ)
        Ψ m f (fun T => frequencyTwist V ξ (columnLog p ell T)) z) := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z
  have hi := reopening_finite_sum_integrable Q pool.powerset β A n (primeProductNorm p) B ell b V
  convert hi using 1
  funext ξ
  rw [reopenedCanonicalRow_integrand p hp hcop hg]
  rfl

theorem separated_canonical_family_energy
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ) (n : (ι →₀ ℕ) → ℝ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (b V : 𝓢(ℝ,ℂ))
    (B ell K E : ℝ) (d : ℕ) (hB : 0 < B) (hell : 0 < ell) (hK : 0 < K) (hE : 0 ≤ E)
    (hbound : ∀ ξ : ℝ,
      rowFamilyEnergy labels (fun I z =>
        reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z) K ≤
        E*(1+|ξ|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, b ξ *
        reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z) K ≤
      (B^2*ell)⁻¹ * E*(∫ ξ : ℝ, ‖b ξ‖*(1+|ξ|)^d)^2 := by
  have hb : Integrable (fun ξ : ℝ => ‖b ξ‖*(1+|ξ|)^d) := by
    simpa only [Real.norm_eq_abs,mul_comm] using weighted_schwartz_integrable b d
  have hφ (I : Ideal ActualEisensteinCubic.O) (z : ActualEisensteinCubic.O) : Integrable (fun ξ : ℝ => b ξ *
      reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
        Ψ m (idealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z) :=
    separated_canonical_integrable p hp hcop hg pool Q (β I) n Ψ m (idealGenerator I) z b V B ell
  have hm := rowFamilyEnergy_integral_polynomial labels K hK b
    (fun I z ξ => reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
      Ψ m (idealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z)
    d E hE hb hφ hbound
  have hn : ‖((B*Real.sqrt ell : ℝ) : ℂ)⁻¹‖^2 = (B^2*ell)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (mul_pos hB (Real.sqrt_pos.mpr hell)),inv_pow,mul_pow,Real.sq_sqrt hell.le]
  rw [rowFamilyEnergy_const_mul labels _ K hK, hn]
  convert mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (B^2*ell)⁻¹) using 1 ; ring

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

theorem rowFamilyEnergy_bound_sum {κ : Type*}
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (bins : Finset κ) (K : ℝ) (hK : 0 < K)
    (P A : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) (B : κ → Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) (c N : ℝ)
    (hbound : ∀ I ∈ labels, ∀ z ∈ (firstFrequencyDisk (2*K)).erase 0,
      ‖P I z‖^2 ≤ c*(‖A I z‖^2 + N*∑ j ∈ bins, ‖B j I z‖^2)) :
    rowFamilyEnergy labels P K ≤
      c*(rowFamilyEnergy labels A K + N*∑ j ∈ bins, rowFamilyEnergy labels (B j) K) := by
  let R := (firstFrequencyDisk (2*K)).erase 0
  let w : ActualEisensteinCubic.O → ℝ := fun z => (rowMajorant (‖eisEmbedding z‖^2/K)).re
  have hswap : (∑ I ∈ labels, ∑ z ∈ R, w z*∑ j ∈ bins, ‖B j I z‖^2) =
      ∑ j ∈ bins, rowFamilyEnergy labels (B j) K := by
    simp_rw [Finset.mul_sum]
    calc
      _ = ∑ I ∈ labels, ∑ j ∈ bins, ∑ z ∈ R, w z*‖B j I z‖^2 :=
        Finset.sum_congr rfl (fun I hI => Finset.sum_comm)
      _ = ∑ j ∈ bins, ∑ I ∈ labels, ∑ z ∈ R, w z*‖B j I z‖^2 := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun j hj => (rowFamilyEnergy_eq_sum labels (B j) K hK).symm)
  rw [rowFamilyEnergy_eq_sum labels P K hK]
  calc
    _ ≤ ∑ I ∈ labels, ∑ z ∈ R,
        (c*(w z*‖A I z‖^2) + c*N*(∑ j ∈ bins, w z*‖B j I z‖^2)) := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro z hz
      calc
        _ ≤ w z*(c*(‖A I z‖^2 + N*∑ j ∈ bins, ‖B j I z‖^2)) :=
          mul_le_mul_of_nonneg_left (hbound I hI z hz) (rowMajorant_nonneg _)
        _ = _ := by rw [← Finset.mul_sum]; ring
    _ = c*(rowFamilyEnergy labels A K + N*∑ j ∈ bins, rowFamilyEnergy labels (B j) K) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hswap, ← rowFamilyEnergy_eq_sum labels A K hK]
      ring

theorem outsideCanonicalRow_family_binned_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ K : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hK : 0 < K)
    (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    rowFamilyEnergy labels (fun I z => outsideCanonicalRow S D hbad Ψ m (idealGenerator I) z W X) K ≤
      2*X*(rowFamilyEnergy labels (fun I z =>
        shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K +
        (cubeLogRange b X).card * ∑ j ∈ cubeLogRange b X,
          rowFamilyEnergy labels (fun I z =>
            outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m (idealGenerator I) z W X H₀) K) := by
  apply rowFamilyEnergy_bound_sum labels (cubeLogRange b X) K hK
  intro I hI z hz
  exact outsideCanonicalRow_binned_energy S D hbad hSp Ψ m (idealGenerator I) z W hWc
    b X H₀ hb hX hW hD

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

theorem outsideCanonicalBin_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X H₀ K E : ℝ) (d : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell) (hK : 0 < K) (hE : 0 ≤ E)
    (hn : ∀ v ∈ Q, B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, rowFamilyEnergy labels (fun I z =>
      reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n B ξ) Ψ m (idealGenerator I)
        (fun T => frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) K ≤
      E*(1+|ξ|)^(2*d)) →
    rowFamilyEnergy labels (fun I z =>
      outsideCanonicalBin S D hbad Q Ψ m (idealGenerator I) z W X H₀) K ≤
      (B^2*ell)⁻¹ * E *
        (∫ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by
  dsimp only
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  let β := fun I v => reopenedCubeCoefficient H₀
    (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
  let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
  intro hbound
  have hrows : (fun I z => outsideCanonicalBin S D hbad Q Ψ m (idealGenerator I) z W X H₀) =
      (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ *
          reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
            (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
            (separatedCubeCoefficient (β I) n B ξ) Ψ m (idealGenerator I)
            (fun T => frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) := by
    funext I z
    exact outsideCanonicalBin_separated S D hbad Q Ψ m (idealGenerator I) z W a b ha hs hW V hV
      B ell X H₀ hB hell hX hn hn'
  rw [hrows]
  exact separated_canonical_family_energy (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q labels β n Ψ m
    (reopeningCoefficient W a b ha hs hW) V B ell K E d hB hell hK hE hbound

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (primeProduct)

theorem canonicalProgress_large (Z : ℝ) (hZ : Real.exp 9000≤Z) :
    Real.exp 4≤Z^((1:ℝ)/1000) := by
  have hh := Real.rpow_le_rpow (Real.exp_pos 9000).le hZ (by norm_num : (0:ℝ)≤1/1000)
  rw [Real.rpow_def_of_pos (Real.exp_pos 9000), Real.log_exp] at hh
  norm_num at hh
  exact (Real.exp_le_exp.mpr (by norm_num : (4:ℝ)≤9)).trans hh

theorem paddedCanonicalRatio (K M R Z η : ℝ) (hM : 0<M) (hZ : 0<Z) :
    Z^η*((K/Z^η)*R/(Real.exp 3*M))=(K*R/M)/Real.exp 3 := by
  field_simp

def canonicalRankMargin (σ η : ℝ) (r : ℕ) : ℝ :=
  σ-η*((3000-r:ℕ):ℝ)

theorem canonicalRankMargin_lower (σ η : ℝ) (hη : 0≤η) (r : ℕ) :
    σ-3000*η≤canonicalRankMargin σ η r := by
  have hn : ((3000-r:ℕ):ℝ)≤3000 := by exact_mod_cast (Nat.sub_le 3000 r)
  unfold canonicalRankMargin
  nlinarith

theorem canonicalRankMargin_step (σ η : ℝ) (hη : 0≤η) (r s : ℕ)
    (hr : r≤3000) (hs : s+1≤r) :
    canonicalRankMargin σ η s+η≤canonicalRankMargin σ η r := by
  have hn : 3000-r+1≤3000-s := by omega
  have hn' : ((3000-r:ℕ):ℝ)+1≤((3000-s:ℕ):ℝ) := by exact_mod_cast hn
  unfold canonicalRankMargin
  nlinarith

theorem canonicalRatio_exp_loss (K M R : ℝ) (hM : 0<M) :
    K*R/(Real.exp 3*M)=(K*R/M)/Real.exp 3 := by
  field_simp

theorem canonicalRankMargin_padding (Z σ η a : ℝ) (r s : ℕ)
    (hZ : 1<Z) (hη : 0≤η) (hr : r≤3000) (hs : s+1≤r)
    (ha : 0≤a) (hbound : a≤Z^(-canonicalRankMargin σ η r)) :
    Z^η*(a/Real.exp 3)≤Z^(-canonicalRankMargin σ η s) := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hmargin := canonicalRankMargin_step σ η hη r s hr hs
  calc
    Z^η*(a/Real.exp 3) ≤ Z^η*a :=
      mul_le_mul_of_nonneg_left (div_le_self ha (Real.one_le_exp (by norm_num)))
        (Real.rpow_nonneg hZ0.le _)
    _ ≤ Z^η*Z^(-canonicalRankMargin σ η r) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hZ0.le _)
    _ = Z^(η-canonicalRankMargin σ η r) := by
      rw [sub_eq_add_neg,Real.rpow_add hZ0]
    _ ≤ Z^(-canonicalRankMargin σ η s) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem fixedTripleMask_ne_zero_of_bin (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j) (m : ActualEisensteinCubic.O) (hm : m≠0) :
    fixedTripleMask m q≠0 := by
  obtain ⟨x,hx,hqx⟩ := Finset.mem_image.mp hq
  have ht := globalSecondFixedTriple_nonzero p hp x
  rw [←hqx]
  unfold fixedTripleMask
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hm
    (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht.1))
    (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht.2.1))
    (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht.2.2)

include hp in

theorem canonical_retained_scale_closure
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (Z σ η X B F K : ℝ) (m : ActualEisensteinCubic.O)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hX : 0<X) (hB : 0<B) (hF : 1≤F) (hK : 1≤K) (hm : m≠0)
    (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hstart : K≤Z^3) (hmass : X*F≤canonicalRankMass Z (fixedDepthRank Z K))
    (hinv : K*‖eisEmbedding m‖^2≤(X*F)*Z^(-σ))
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale (K/Z^η) (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    0<X' ∧ 1≤F' ∧ 1≤K' ∧
      fixedDepthRank Z K'+1≤fixedDepthRank Z K ∧ K'≤Z^3 ∧
      X'*F'≤canonicalRankMass Z (fixedDepthRank Z K') ∧
      K'*‖eisEmbedding (fixedTripleMask m q)‖^2≤(X'*F')*Z^(-σ) ∧
      fixedTripleMask m q≠0 ∧
      (∀I∈globalCanonicalLabels p source side q j,
        I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤F') := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hF0 : 0<F := zero_lt_one.trans_le hF
  have hBup : 0<Real.exp 1*B := mul_pos (Real.exp_pos _) hB
  have hell : 0<X/B^3 := div_pos hX (pow_pos hB 3)
  have hKpad : 0<K/Z^η := div_pos hK0 (Real.rpow_pos_of_pos hZ0 _)
  have hKle : K/Z^η≤K := div_le_self hK0.le (Real.one_le_rpow hZ.le hη)
  have hlarge : Real.exp 4≤(Real.exp 1*B)*F := (canonicalProgress_large Z hZbig).trans hprogress
  obtain ⟨hXc,hFc,hKc,hMc,hsmall,hrank,hrank0,hratio,hlabels⟩ :=
    globalRetained_canonical_geometry p hp source side q j hq Z η K (K/Z^η)
      (X/B^3) (Real.exp 1*B) F m hZ hηsmall hK0 hKpad hKle hell hBup hF
      hprogress hlarge hstart hk hb₁ hb₂ hretained
  have hMc' : globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j≤Real.exp 3*(X*F) := by
    simpa only [lowerCubeBin_transfer_mass X B F hB.ne'] using hMc
  have hratio' : globalLogRep j 8*Real.exp 1*‖eisEmbedding (fixedTripleMask m q)‖^2/
      (globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j)≤Z^(-σ) := by
    rw [lowerCubeBin_transfer_mass X B F hB.ne',paddedCanonicalRatio K (X*F)
      (‖eisEmbedding m‖^2) Z η (mul_pos hX hF0) hZ0] at hratio
    apply hratio.trans
    apply (div_le_self (div_nonneg (mul_nonneg hK0.le (sq_nonneg _)) (mul_pos hX hF0).le)
      (Real.one_le_exp (by norm_num))).trans
    exact (div_le_iff₀ (mul_pos hX hF0)).mpr (by simpa only [mul_comm] using hinv)
  refine ⟨hXc,hFc,hKc,hrank,?_,?_,?_,fixedTripleMask_ne_zero_of_bin p hp source side q j hq m hm,
    globalCanonicalLabels_bounds p hp source side q j hk⟩
  · exact hsmall.trans ((div_le_self hK0.le
      (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤1/1000))).trans hstart)
  · exact canonicalRankMass_child Z X F _ _ _ _ hrank0 hrank hmass hMc'
  · exact (div_le_iff₀ (mul_pos hXc (zero_lt_one.trans_le hFc))).mp hratio' |>.trans_eq (by ring)

include hp in

theorem canonical_retained_unpadded_closure
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (Z σ η X B F K : ℝ) (m : ActualEisensteinCubic.O)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hX : 0<X) (hB : 0<B) (hF : 1≤F) (hK : 1≤K) (hm : m≠0)
    (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hstart : K≤Z^3) (hmass : X*F≤canonicalRankMass Z (fixedDepthRank Z K))
    (hinv : K*‖eisEmbedding m‖^2≤
      (X*F)*Z^(-canonicalRankMargin σ η (fixedDepthRank Z K)))
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale K (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    0<X' ∧ 1≤F' ∧ 1≤K' ∧
      fixedDepthRank Z K'+1≤fixedDepthRank Z K ∧ K'≤Z^3 ∧
      X'*F'≤canonicalRankMass Z (fixedDepthRank Z K') ∧
      K'*‖eisEmbedding (fixedTripleMask m q)‖^2≤
        (X'*F')*Z^(-canonicalRankMargin σ η (fixedDepthRank Z K')) ∧
      fixedTripleMask m q≠0 ∧
      (∀I∈globalCanonicalLabels p source side q j,
        I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤F') := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hF0 : 0<F := zero_lt_one.trans_le hF
  have hBup : 0<Real.exp 1*B := mul_pos (Real.exp_pos _) hB
  have hell : 0<X/B^3 := div_pos hX (pow_pos hB 3)
  have hlarge : Real.exp 4≤(Real.exp 1*B)*F := (canonicalProgress_large Z hZbig).trans hprogress
  obtain ⟨hXc,hFc,hKc,hMc,hsmall,hrank,hrank0,hratio,hlabels⟩ :=
    globalRetained_canonical_geometry p hp source side q j hq Z η K K
      (X/B^3) (Real.exp 1*B) F m hZ hηsmall hK0 hK0 le_rfl hell hBup hF
      hprogress hlarge hstart hk hb₁ hb₂ hretained
  have hMc' : globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j≤Real.exp 3*(X*F) := by
    simpa only [lowerCubeBin_transfer_mass X B F hB.ne'] using hMc
  have hparent : K*‖eisEmbedding m‖^2/(X*F)≤
      Z^(-canonicalRankMargin σ η (fixedDepthRank Z K)) :=
    (div_le_iff₀ (mul_pos hX hF0)).mpr (by simpa only [mul_comm] using hinv)
  have hratio' : globalLogRep j 8*Real.exp 1*‖eisEmbedding (fixedTripleMask m q)‖^2/
      (globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j)≤
      Z^(-canonicalRankMargin σ η (fixedDepthRank Z (globalLogRep j 8*Real.exp 1))) := by
    rw [lowerCubeBin_transfer_mass X B F hB.ne',canonicalRatio_exp_loss K (X*F)
      (‖eisEmbedding m‖^2) (mul_pos hX hF0)] at hratio
    exact hratio.trans (canonicalRankMargin_padding Z σ η _ _ _ hZ hη hrank0 hrank
      (div_nonneg (mul_nonneg hK0.le (sq_nonneg _)) (mul_pos hX hF0).le) hparent)
  refine ⟨hXc,hFc,hKc,hrank,?_,?_,?_,fixedTripleMask_ne_zero_of_bin p hp source side q j hq m hm,
    globalCanonicalLabels_bounds p hp source side q j hk⟩
  · exact hsmall.trans ((div_le_self hK0.le
      (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤1/1000))).trans hstart)
  · exact canonicalRankMass_child Z X F _ _ _ _ hrank0 hrank hmass hMc'
  · exact (div_le_iff₀ (mul_pos hXc (zero_lt_one.trans_le hFc))).mp hratio' |>.trans_eq (by ring)

end SecondPassArithmetic

end

end OAI
