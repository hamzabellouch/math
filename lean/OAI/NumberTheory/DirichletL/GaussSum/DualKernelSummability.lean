import OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion

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

namespace CompletedGauss
open scoped BigOperators Classical ContDiff
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

lemma nonzeroDualIdeal_norm_pos (I : NonzeroDualIdeal) :
    0<(Ideal.absNorm I.val:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

lemma nonzeroDualIdeal_inv_pow_summable (n : ℕ) (hn : 1<n) :
    Summable (fun I : NonzeroDualIdeal => ((Ideal.absNorm I.val:ℝ)^n)⁻¹) := by
  have hs := (CubicEisenstein.fullIdealWeight_summable_norm (n:ℂ)
    (by exact_mod_cast hn)).subtype (fun I : Ideal Eis => I≠0)
  apply hs.congr
  intro I
  simp only [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right I.property,
    Complex.cpow_neg,Complex.cpow_natCast,norm_inv,norm_pow,Complex.norm_natCast]

def rawDualKernelTerm (V : ℝ→ℂ) (scale ρ q : ℝ)
    (β : ℕ→Ideal Eis→Ideal Eis→ℂ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℂ :=
  β x.1 x.2.1.val x.2.2.val * CubicReflectionKernel.paperKernel V
    (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)

lemma rawDualKernel_inverse_square (scale ρ q : ℝ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ =
      (scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹) := by
  simp only [mul_pow,mul_inv_rev,←pow_mul,←inv_pow]
  ring

theorem rawDualKernelTerm_summable_norm
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (scale ρ q B : ℝ) (hscale : 0<scale) (hρ : 0<ρ) (hq : 1<q)
    (hB : 0≤B) (β : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hβ : ∀m,∀I J : NonzeroDualIdeal,‖β m I.val J.val‖≤B) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖rawDualKernelTerm V scale ρ q β x‖) := by
  obtain ⟨C,hC,hdec⟩:=CubicReflectionKernel.paperKernel_euler_power_decay
    V a b ha hsupp hV 2 0
  have hq6 : 1<q^6 := one_lt_pow₀ hq (by norm_num)
  have hg : Summable (fun m : ℕ => ((q^6)⁻¹)^m) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).mpr hq6)
  have hi := nonzeroDualIdeal_inv_pow_summable 2 (by norm_num)
  have hj := nonzeroDualIdeal_inv_pow_summable 6 (by norm_num)
  have hij := hi.mul_of_nonneg hj (fun I=>by positivity) (fun J=>by positivity)
  have hs := hg.mul_of_nonneg hij (fun m=>by positivity) (fun IJ=>by positivity)
  have hmajor := hs.mul_left (B*C*(scale^2*ρ^6)⁻¹)
  apply hmajor.of_nonneg_of_le (fun _=>norm_nonneg _)
  intro x
  have hn:=nonzeroDualIdeal_norm_pos x.2.1
  have hb:=nonzeroDualIdeal_norm_pos x.2.2
  have hx : 0<scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3 := by positivity
  have hk := (hdec _ hx).2
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hk
  norm_num only [Nat.cast_ofNat] at hk
  have hr : (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^(-(2:ℝ))=
      ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ := by
    rw [Real.rpow_neg hx.le,Real.rpow_two]
  rw [hr,rawDualKernel_inverse_square] at hk
  calc
    _ = ‖β x.1 x.2.1.val x.2.2.val‖*
        ‖CubicReflectionKernel.paperKernel V
          (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)‖ := by
        rw [rawDualKernelTerm,norm_mul]
    _ ≤ B*(C*((scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹))) :=
      mul_le_mul (hβ x.1 x.2.1 x.2.2) hk (norm_nonneg _) hB
    _ = _ := by ring

end

section
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

lemma canonical_dual_kernel_argument (K Y ρ q : ℝ) (i : ℕ×ℕ×ℕ)
    (k n b : Ideal Eis) (hK : 0<K) (hk : k≠0) (hn : n≠0) (hb : b≠0) :
    (Y⁻¹*(ramifiedScale ρ q i.1)^3*((2:ℝ)^i.2.1)^3*(2:ℝ)^i.2.2)*
      Real.exp (-2*Real.log ((Ideal.absNorm k:ℝ)/K)+
        Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2)+
        3*Real.log ((Ideal.absNorm b:ℝ)/(2:ℝ)^i.2.1)) =
    (Y⁻¹*(K/(Ideal.absNorm k:ℝ))^2)*(ρ*q^i.1)^3*
      (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 := by
  rw [positive_log_scale_identity _ _ _ _ _ _ _
    (nonzeroDualIdeal_norm_pos ⟨k,hk⟩) (nonzeroDualIdeal_norm_pos ⟨n,hn⟩)
    (nonzeroDualIdeal_norm_pos ⟨b,hb⟩) hK (by positivity) (by positivity)]
  unfold ramifiedScale
  field_simp

def canonicalRawBranchCoefficient {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (ρ q : ℝ)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→ℂ) (k : Ideal Eis)
    (m : ℕ) (n b : Ideal Eis) : ℂ :=
  σ m*quadraticRow k (primaryGenerator (n*b))*
    reflectedDyadicCoefficient P hg j e (η m) (ramifiedScale ρ q m) n b

lemma canonicalRawBranchCoefficient_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (ρ q : ℝ) (hρ : 0<ρ) (hq : 1≤q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m,‖σ m‖≤1) (k : Ideal Eis) (m : ℕ) (n b : NonzeroDualIdeal) :
    ‖canonicalRawBranchCoefficient P hg j e ρ q η σ k m n.val b.val‖≤1/ρ := by
  have hn:=norm_at_least_one n.val n.property
  have hb:=norm_at_least_one b.val b.property
  have hr:=ramifiedScale_pos ρ q hρ (lt_of_lt_of_le zero_lt_one hq) m
  have hc:=reflectedDyadicCoefficient_norm P hg j e (η m) (ramifiedScale ρ q m) 1 1
    hr (by norm_num) (by norm_num) n.val b.val n.property b.property (hη m n b)
    (by linarith) (by linarith)
  have hdiv (v : Fin 3) : 1≤(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) :=
    norm_at_least_one _ (reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e v)
  have hroot : 1≤Real.sqrt ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [hdiv 0,hdiv 2]
  have hrho : ρ≤ramifiedScale ρ q m := by
    exact le_mul_of_one_le_right hρ.le (one_le_pow₀ hq)
  have hden := hrho.trans (le_mul_of_one_le_right hr.le hroot)
  simp only [Real.sqrt_one,one_mul] at hc
  have hcoeff:=hc.trans (div_le_div_of_nonneg_left (by norm_num) hρ hden)
  rw [canonicalRawBranchCoefficient,norm_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) (hσ m)).trans (quadraticRow_norm_le_one _ _))).trans hcoeff

theorem reflectedBranchBlock_canonical {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (K Y ρ q : ℝ)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→idealRange K→ℂ)
    (i : ℕ×ℕ×ℕ) (k : idealRange K) (hK : 0<K)
    (hk : K/2≤(Ideal.absNorm k.val:ℝ)) :
    reflectedBranchBlock P hg j e W K Y ρ q
      (fun l=>dualIdealDyad l.2.2) (fun l=>dualIdealDyad l.2.1)
      (fun l=>η l.1) (fun l=>σ l.1) i k =
    ∑n : dualIdealDyad i.2.2, ∑b : dualIdealDyad i.2.1,
      rawDualKernelTerm (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k.val:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η (fun m=>σ m k) k.val)
        (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
          ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) := by
  have hkm:=mem_idealRange.mp k.property
  have hwk:=completedShellWindow_log (Ideal.absNorm k.val:ℝ) K
    (nonzeroDualIdeal_norm_pos ⟨k.val,hkm.1.1⟩) hK hk hkm.2
  simp only [reflectedBranchBlock,completedSmoothDyadicBlock,Finset.mul_sum]
  rw [←Finset.sum_coe_sort (dualIdealDyad i.2.2)]
  apply Finset.sum_congr rfl
  intro n _
  rw [←Finset.sum_coe_sort (dualIdealDyad i.2.1)]
  apply Finset.sum_congr rfl
  intro b _
  have hn:=dualIdealDyad_bounds _ n.val n.property
  have hb:=dualIdealDyad_bounds _ b.val b.property
  have hwn:=completedShellWindow_log (Ideal.absNorm n.val:ℝ) ((2:ℝ)^i.2.2)
    (nonzeroDualIdeal_norm_pos ⟨n.val,hn.1⟩) (by positivity) hn.2.1 hn.2.2
  have hwb:=completedShellWindow_log (Ideal.absNorm b.val:ℝ) ((2:ℝ)^i.2.1)
    (nonzeroDualIdeal_norm_pos ⟨b.val,hb.1⟩) (by positivity) hb.2.1 hb.2.2
  rw [hwk,hwn,hwb,canonical_dual_kernel_argument K Y ρ q i k.val n.val b.val hK hkm.1.1 hn.1 hb.1]
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient]
  ring

theorem canonicalRawBranch_summable_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (K Y ρ q : ℝ) (hK : 0<K) (hY : 0<Y) (hρ : 0<ρ) (hq : 1<q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m,‖σ m‖≤1) (k : Ideal Eis) (hk : k≠0) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖rawDualKernelTerm (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η σ k) x‖) := by
  have hkn:=nonzeroDualIdeal_norm_pos ⟨k,hk⟩
  exact rawDualKernelTerm_summable_norm (Vstar W) a b ha (Vstar_support W a b hsupp)
    (Vstar_contDiff W a b ha hsupp hW) _ ρ q (1/ρ) (by positivity) hρ hq (by positivity)
    _ (fun m n b=>canonicalRawBranchCoefficient_norm P hg j e ρ q hρ hq.le η σ hη hσ k m n b)

theorem canonical_reflected_series {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (K Y ρ q : ℝ) (hK : 0<K) (hY : 0<Y) (hρ : 0<ρ) (hq : 1<q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→idealRange K→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m k,‖σ m k‖≤1) (k : idealRange K)
    (hk : K/2≤(Ideal.absNorm k.val:ℝ)) :
    (∑'i : ℕ×ℕ×ℕ, reflectedBranchBlock P hg j e W K Y ρ q
      (fun l=>dualIdealDyad l.2.2) (fun l=>dualIdealDyad l.2.1)
      (fun l=>η l.1) (fun l=>σ l.1) i k) =
    ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      rawDualKernelTerm (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k.val:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η (fun m=>σ m k) k.val) x := by
  have hs:=canonicalRawBranch_summable_norm P hg j e W a b ha hsupp hW K Y ρ q
    hK hY hρ hq η (fun m=>σ m k) hη (fun m=>hσ m k) k.val
    (mem_idealRange.mp k.property).1.1
  rw [tsum_dualIdealDyads _ hs.of_norm]
  apply tsum_congr
  intro i
  exact reflectedBranchBlock_canonical P hg j e W K Y ρ q η σ i k hK hk

end

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

namespace ReflectedBranchData

def withCanonicalCuspArray {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hσ : ∀m k,‖σ m k‖≤1) : ReflectedBranchData levelBound K I F Q :=
  { d with
    nColumns := fun i=>dualIdealDyad i.2.2
    bColumns := fun i=>dualIdealDyad i.2.1
    nBounds := fun i n hn=>dualIdealDyad_bounds i.2.2 n hn
    bBounds := fun i b hb=>dualIdealDyad_bounds i.2.1 b hb
    amplitude := fun i=>η i.1
    amplitude_bound := fun i n hn b hb=>hη i.1
      ⟨n,((mem_dualIdealDyad _ _).mp hn).1⟩ ⟨b,((mem_dualIdealDyad _ _).mp hb).1⟩
    rowPhase := fun i=>σ i.1
    rowPhase_bound := fun i k=>hσ i.1 k }

def rawValue {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ := by
  letI : ∀p : d.primes,p.val.IsMaximal:=d.maximal
  exact ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
    rawDualKernelTerm (Vstar W)
      ((completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes=>p.val) d.label)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k.val:ℝ))^2) ρ q
      (canonicalRawBranchCoefficient (fun p : d.primes=>p.val) d.good
        (fun p=>completedLocalExponent I F p.val) d.label ρ q η (fun m=>σ m k) k.val) x

theorem withCanonicalCuspArray_value {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hσ : ∀m k,‖σ m k‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X ρ q : ℝ) (hX : 0<X) (hρ : 0<ρ) (hq : 1<q)
    (hK : 0<completedResidualScale K I Q)
    (k : idealRange (completedResidualScale K I Q))
    (hk : completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    (d.withCanonicalCuspArray η hη σ hσ).value W X ρ q k =
      d.rawValue η σ W X ρ q k := by
  let : ∀p : d.primes,p.val.IsMaximal:=d.maximal
  have hn (J : Ideal Eis) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) :=
    nonzeroDualIdeal_norm_pos ⟨J,hJ⟩
  have hprod:=hn (∏p : d.primes,p.val)
    (Finset.prod_ne_zero_iff.mpr (fun p _=>NeZero.ne p.val))
  have hd:=hn _ (reflectionExtractedDivisor_ne_zero (fun p : d.primes=>p.val)
    (fun p=>NeZero.ne p.val) (fun p=>completedLocalExponent I F p.val) d.label 1)
  have he:=hn _ (reflectionExtractedDivisor_ne_zero (fun p : d.primes=>p.val)
    (fun p=>NeZero.ne p.val) (fun p=>completedLocalExponent I F p.val) d.label 2)
  have hy : 0<completedBranchScale K (X/d.levelScale) I F Q
      (fun p : d.primes=>p.val) d.label := by
    unfold completedBranchScale
    have hl:=d.levelScale_pos
    positivity
  exact canonical_reflected_series (fun p : d.primes=>p.val) d.good
    (fun p=>completedLocalExponent I F p.val) d.label W a b ha hsupp hW
    (completedResidualScale K I Q)
    (completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes=>p.val) d.label)
    ρ q hK hy hρ hq η σ hη hσ k hk

def restrictRows {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (sector : idealRange (completedResidualScale K I Q)→Prop) :
    ReflectedBranchData levelBound K I F Q :=
  { d with
    rowPhase := fun i k=>if sector k then d.rowPhase i k else 0
    rowPhase_bound := by
      intro i k
      split_ifs
      · exact d.rowPhase_bound i k
      · simp }

theorem restrictRows_value {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (sector : idealRange (completedResidualScale K I Q)→Prop)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) :
    (d.restrictRows sector).value W X ρ q k =
      if sector k then d.value W X ρ q k else 0 := by
  by_cases hk:sector k
  · simp only [value,restrictRows,reflectedBranchBlock,ite_eq_left hk]
    rfl
  · simp only [value,restrictRows,reflectedBranchBlock,ite_eq_right hk,zero_mul,tsum_zero]

theorem sum_restrictRows_selected {ι : Type*} [Fintype ι] [DecidableEq ι]
    {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ι→ReflectedBranchData levelBound K I F Q)
    (sector : idealRange (completedResidualScale K I Q)→ι)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) :
    (∑s : ι,((d s).restrictRows (fun k=>sector k=s)).value W X ρ q k)=
      (d (sector k)).value W X ρ q k := by
  calc
    _ = ((d (sector k)).restrictRows (fun k'=>sector k'=sector k)).value W X ρ q k := by
      apply Finset.sum_eq_single (sector k)
      · intro s _ hs
        rw [restrictRows_value,ite_eq_right (Ne.symm hs)]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    _ = _ := by rw [restrictRows_value,ite_eq_left rfl]

end ReflectedBranchData

end CompletedGauss

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance ramifiedFrequencyUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma ramifiedFrequencyChar_neg_unit (k:Eis) (u:Eisˣ) (n:ℕ) :
    ramifiedFrequencyChar k (-u) n=ramifiedFrequencyChar k u n := by
  ext x
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  have hp:lambda^2∣(1+3*d)-1:=by
    rw [add_sub_cancel_left]
    exact dvd_mul_of_dvd_left lambda_sq_dvd_three d
  rw [ramifiedFrequencyChar_mk,ramifiedFrequencyChar_mk,Units.val_neg,neg_mul,
    symbol_neg_numerator _ _ hp]

lemma arithmeticResidueSum_neg_unit (h:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    arithmeticResidueSum (-h) (u.val*lambda^n)=
      arithmeticResidueSum h ((-u).val*lambda^n) := by
  by_cases hd:u.val*lambda^n∣3*(-h)
  · obtain ⟨k,hk⟩:=hd
    have hk':3*h=((-u).val*lambda^n)*k:=by
      simp only [Units.val_neg]
      linear_combination -hk
    rw [ramified_arithmetic_character_test (-h) k u n hn hk,
      ramified_arithmetic_character_test h k (-u) n hn hk',ramifiedFrequencyChar_neg_unit]
  · have hl:arithmeticResidueSum (-h) (u.val*lambda^n)=0:=by
      by_contra he
      exact hd (ramified_arithmetic_support (-h) u n hn he)
    have hr:arithmeticResidueSum h ((-u).val*lambda^n)=0:=by
      by_contra he
      obtain ⟨k,hk⟩:=ramified_arithmetic_support h (-u) n hn he
      apply hd
      refine ⟨k,?_⟩
      simp only [Units.val_neg] at hk
      linear_combination -hk
    rw [hl,hr]

lemma principalResidueTerm_neg (h:Eis) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (-h) u n=principalResidueTerm h (-u) n := by
  unfold principalResidueTerm
  rw [arithmeticResidueSum_neg_unit h u (n+2) (by omega)]
  congr 2
  simp only [Units.val_neg]
  ring

lemma principalArithmeticResidue_neg (h:Eis) :
    principalArithmeticResidue (-h)=principalArithmeticResidue h := by
  by_cases hh:h=0
  · rw [hh,neg_zero]
  let N:=max (ramifiedFrequencyBound (-h)+1) (ramifiedFrequencyBound h+1)
  rw [principalArithmeticResidue_eq_sum (-h) (neg_ne_zero.mpr hh) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum h hh N (le_max_right _ _)]
  apply congrArg (fun z:ℂ=>z/((9*Real.sqrt 3/2:ℝ):ℂ))
  simp_rw [principalResidueTerm_neg]
  exact Fintype.sum_equiv (Equiv.neg Eisˣ)
    (fun u=>∑n∈Finset.range N,principalResidueTerm h (-u) n)
    (fun u=>∑n∈Finset.range N,principalResidueTerm h u n) (fun _=>rfl)

theorem sourceArithmeticResidue_neg (h:Eis) :
    sourceArithmeticResidue (-h)=sourceArithmeticResidue h := by
  have hU:unramifiedGaussResidue (-(9*h))=unramifiedGaussResidue (9*h):=by
    have he:=unramifiedGaussResidue_of_initial_relation (-(9*h)) (9*h) 0
      (fun _=>1) (fun _=>0) (fun _ _=>analyticAt_const) (fun _ _=>analyticAt_const)
      continuousAt_const continuousAt_const
      (fun s hs hi=>by simpa only [one_mul,zero_mul,add_zero] using unramifiedCubicGaussSeries_neg s (9*h))
    simpa only [one_mul,zero_mul,add_zero] using he
  simp only [sourceArithmeticResidue,cuspFrequency_neg,
    AddChar.map_neg_eq_inv,inv_eq_one,principalArithmeticResidue_neg,
    mul_neg,hU]

lemma cubicBesselNormalizer_neg (h:Eis) : cubicBesselNormalizer (-h)=cubicBesselNormalizer h := by
  simp only [cubicBesselNormalizer,cuspFrequency_neg,norm_neg]

theorem sourceResidualFourierCoefficient_neg (h:Eis) :
    sourceResidualFourierCoefficient (-h)=sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,sourceResidualFourierCoefficient,
    cubicBesselNormalizer_neg,sourceArithmeticResidue_neg]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceRayPhase_eq_one_iff_coordinate (h:Eis) :
    ShortDraftTrace.breveE (cuspFrequency h)=1 ↔
      (3:ℤ)∣(ActualEisensteinCoordinates.coords h).2 := by
  have he:ShortDraftTrace.breveE (cuspFrequency h)=
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        3 (by norm_num) (Ideal.Quotient.mk _ h):=by
    rw [eisTraceModChar,IdealGaussCRT.traceModChar_mk]
    unfold cuspFrequency
    simp only [map_ofNat]
  rw [he,trace_third_coordinate]
  simpa only [pow_zero,one_mul,Nat.cast_zero,zero_add] using
    omega3_pow_exp_eq_one_iff 0 (ActualEisensteinCoordinates.coords h).2

lemma primary_or_negative_primary_of_source_mask (h:Eis) (h3:¬(3:Eis)∣h)
    (hphase:ShortDraftTrace.breveE (cuspFrequency h)=1) :
    lambda^2∣h-1 ∨ lambda^2∣(-h)-1 := by
  let a:ℤ:=(ActualEisensteinCoordinates.coords h).1
  let b:ℤ:=(ActualEisensteinCoordinates.coords h).2
  have heval:h=(a:Eis)+(b:Eis)*omega:=
    (ActualEisensteinCoordinates.eval_coords h).symm
  obtain ⟨B,hB⟩:=(sourceRayPhase_eq_one_iff_coordinate h).mp hphase
  have hBc:(b:Eis)=3*(B:Eis):=by exact_mod_cast hB
  have ha:¬(3:ℤ)∣a:=by
    rintro ⟨A,hA⟩
    apply h3
    refine ⟨(A:Eis)+(B:Eis)*omega,?_⟩
    have hAc:(a:Eis)=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hAc,hBc]
    ring
  have hcases:(3:ℤ)∣a-1 ∨ (3:ℤ)∣a+1:=by omega
  rcases hcases with ⟨A,hA⟩|⟨A,hA⟩
  · left
    apply lambda_sq_dvd_three.trans
    refine ⟨(A:Eis)+(B:Eis)*omega,?_⟩
    have hAc:(a:Eis)-1=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hBc]
    linear_combination hAc
  · right
    apply lambda_sq_dvd_three.trans
    refine ⟨-((A:Eis)+(B:Eis)*omega),?_⟩
    have hAc:(a:Eis)+1=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hBc]
    linear_combination -hAc

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceFourier_supported_three_of_base_zero (hC:infinityCoefficientScalar=0)
    (h:Eis) (h3:¬(3:Eis)∣h) : sourceResidualFourierCoefficient h=0 := by
  by_cases hm:ShortDraftTrace.breveE (cuspFrequency h)=1
  · rcases primary_or_negative_primary_of_source_mask h h3 hm with hh|hh
    · exact sourceFourier_primary_zero_of_base_zero hC h hh
    · rw [←sourceResidualFourierCoefficient_neg h]
      exact sourceFourier_primary_zero_of_base_zero hC (-h) hh
  · simp only [sourceResidualFourierCoefficient,sourceArithmeticResidue,ite_eq_right hm,mul_zero]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem infinityCoefficientScalar_ne_zero : infinityCoefficientScalar≠0 := by
  intro hC
  obtain ⟨h,h3,hn⟩:=exists_source_coefficient_not_three
  exact hn (sourceFourier_supported_three_of_base_zero hC h h3)

lemma sourceResidualFourierCoefficient_one_ne_zero : sourceResidualFourierCoefficient 1≠0 := by
  intro h
  exact infinityCoefficientScalar_ne_zero (by simp only [infinityCoefficientScalar,h,star_zero])

lemma sourceArithmeticResidue_one_ne_zero : sourceArithmeticResidue 1≠0 := by
  intro h
  exact sourceResidualFourierCoefficient_one_ne_zero (by rw [sourceResidualFourierCoefficient,h,mul_zero])

theorem normalized_infinityCoefficient_squarefree_cube (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I) :
    infinityCoefficientScalar⁻¹*
      star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))=
      (‖eisEmbedding (primaryGenerator J)‖:ℂ)*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  rw [infinityCoefficient_squarefree_cube I J hI hJ hsq]
  simp only [←mul_assoc,inv_mul_cancel₀ infinityCoefficientScalar_ne_zero,one_mul]

end CubicEisenstein

end

end OAI
