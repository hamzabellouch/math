import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Tactic
import OAI.NumberTheory.PiExponent.Jets.CotangentGeneration
import OAI.NumberTheory.PiExponent.Jets.IntrinsicLength
import OAI.NumberTheory.PiExponent.Jets.JetGeometry

namespace OAI

namespace PiExponentApprox.TransverseMultiplicity

noncomputable section

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

def RectIndex (n : σ → ℕ) := {d : σ →₀ ℕ // ∀ i, d i < n i}

def rectangularIdeal (n : σ → ℕ) : Ideal (MvPowerSeries σ K) where
  carrier := {f | ∀ d, (∀ i, d i < n i) → coeff d f = 0}
  zero_mem' := by intro d hd; exact map_zero _
  add_mem' := by
    intro f g hf hg d hd
    rw [map_add, hf d hd, hg d hd, zero_add]
  smul_mem' := by
    intro a f hf d hd
    change coeff d (a * f) = 0
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ab hab
    have heq : ab.1 + ab.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hb : ∀ i, ab.2 i < n i := by
      intro i
      have hdi := hd i
      rw [← heq, Finsupp.add_apply] at hdi
      omega
    rw [hf ab.2 hb, mul_zero]

def rectangularPacket (n : σ → ℕ) :
    MvPowerSeries σ K →ₗ[K] (RectIndex n → K) where
  toFun f d := coeff d.val f
  map_add' f g := by ext d; exact map_add _ _ _
  map_smul' a f := by ext d; exact map_smul _ _ _

omit [DecidableEq σ] in
theorem rectangularPacket_surjective (n : σ → ℕ) :
    Function.Surjective (rectangularPacket (K := K) n) := by
  classical
  intro packet
  let f : MvPowerSeries σ K := fun d =>
    if hd : ∀ i, d i < n i then packet ⟨d, hd⟩ else 0
  refine ⟨f, ?_⟩
  funext d
  change (if hd : ∀ i, d.val i < n i then packet ⟨d.val, hd⟩ else 0) = packet d
  simp only [dite_eq_left d.property]
  exact congrArg packet (Subtype.ext rfl)

def rectangularQuotientCoefficients (n : σ → ℕ) :
    (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) →ₗ[K] (RectIndex n → K) :=
  Submodule.liftQ ((rectangularIdeal (K := K) n).restrictScalars K)
    (rectangularPacket n) (by
      intro f hf
      change rectangularPacket n f = 0
      funext d
      exact hf d.val d.property)

omit [Fintype σ] in
@[simp] theorem rectangularQuotientCoefficients_mk (n : σ → ℕ)
    (f : MvPowerSeries σ K) (d : RectIndex n) :
    rectangularQuotientCoefficients (K := K) n (Ideal.Quotient.mk (rectangularIdeal (K := K) n) f) d =
      coeff d.val f := rfl

theorem rectangularQuotientCoefficients_bijective (n : σ → ℕ) :
    Function.Bijective (rectangularQuotientCoefficients (K := K) n) := by
  constructor
  · intro a b hab
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    intro d hd
    have hc := congrFun hab (⟨d, hd⟩ : RectIndex n)
    change coeff d f = coeff d g at hc
    rw [map_sub, hc, sub_self]
  · intro packet
    obtain ⟨f, hf⟩ := rectangularPacket_surjective (K := K) n packet
    exact ⟨Ideal.Quotient.mk (rectangularIdeal (K := K) n) f, hf⟩

def rectangularQuotientEquiv (n : σ → ℕ) :
    (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) ≃ₗ[K] (RectIndex n → K) :=
  LinearEquiv.ofBijective (rectangularQuotientCoefficients n)
    (rectangularQuotientCoefficients_bijective n)

def rectIndexEquiv (n : σ → ℕ) : RectIndex n ≃ (∀ i, Fin (n i)) where
  toFun d i := ⟨d.val i, d.property i⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm (fun i => (a i).val), by
    intro i
    exact (a i).isLt⟩
  left_inv d := by
    apply Subtype.ext
    exact Finsupp.ext fun i => rfl
  right_inv a := by
    funext i
    apply Fin.ext
    rfl

instance rectIndexFintype (n : σ → ℕ) : Fintype (RectIndex n) :=
  Fintype.ofEquiv (∀ i, Fin (n i)) (rectIndexEquiv n).symm

theorem card_rectIndex (n : σ → ℕ) : Fintype.card (RectIndex n) = ∏ i, n i := by
  rw [Fintype.card_congr (rectIndexEquiv n), Fintype.card_pi]
  simp only [Fintype.card_fin]

instance rectangularQuotientFinite (n : σ → ℕ) :
    Module.Finite K (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) :=
  Module.Finite.equiv (rectangularQuotientEquiv n).symm

theorem finrank_rectangularQuotient (n : σ → ℕ) :
    Module.finrank K (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) = ∏ i, n i := by
  rw [(rectangularQuotientEquiv (K := K) n).finrank_eq,
    Module.finrank_fintype_fun_eq_card, card_rectIndex]

def rectangularAugmentation (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) →+* K :=
  Ideal.Quotient.lift (rectangularIdeal (K := K) n)
    (constantCoeff : MvPowerSeries σ K →+* K) (by
    intro f hf
    change coeff 0 f = 0
    exact hf 0 hn)

omit [Fintype σ] in
@[simp] theorem rectangularAugmentation_mk (n : σ → ℕ) (hn : ∀ i, 0 < n i)
    (f : MvPowerSeries σ K) :
    rectangularAugmentation (K := K) n hn
      (Ideal.Quotient.mk (rectangularIdeal (K := K) n) f) = constantCoeff f := rfl

omit [Fintype σ] in
@[simp] theorem rectangularAugmentation_algebraMap (n : σ → ℕ) (hn : ∀ i, 0 < n i)
    (a : K) : rectangularAugmentation (K := K) n hn
      (algebraMap K (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) a) = a := by
  change constantCoeff (C a : MvPowerSeries σ K) = a
  exact constantCoeff_C a

omit [Fintype σ] in
theorem rectangularQuotient_isLocal (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    IsLocalRing (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) := by
  let := (rectangularAugmentation (K := K) n hn).domain_nontrivial
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (rectangularIdeal (K := K) n))
    Ideal.Quotient.mk_surjective

theorem ordinaryIdeal_le_rectangularIdeal (n : σ → ℕ) :
    PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) (1 + ∑ i, n i) ≤
      rectangularIdeal (K := K) n := by
  intro f hf d hd
  apply (PiExponent.JetGeometry.mem_weightedIdeal_iff _ _ f).mp hf d
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum]
  have hsum : (∑ i, d i) ≤ ∑ i, n i :=
    Finset.sum_le_sum fun i _ => Nat.le_of_lt (hd i)
  omega

omit [Fintype σ] [DecidableEq σ] in
theorem ordinaryOneIdeal_eq_constantKernel :
    (PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) 1 :
      Ideal (MvPowerSeries σ K)) = RingHom.ker constantCoeff := by
  ext f
  change (1 : ℕ∞) ≤ f.order ↔ constantCoeff f = 0
  exact one_le_order_iff_constCoeff_eq_zero

omit [Fintype σ] in
theorem rectangularAugmentation_ker_eq_map (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    RingHom.ker (rectangularAugmentation (K := K) n hn) =
      Ideal.map (Ideal.Quotient.mk (rectangularIdeal (K := K) n))
        (PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) 1) := by
  rw [ordinaryOneIdeal_eq_constantKernel]
  let q := Ideal.Quotient.mk (rectangularIdeal (K := K) n)
  have hker : Ideal.comap q (RingHom.ker (rectangularAugmentation (K := K) n hn)) =
      RingHom.ker (constantCoeff : MvPowerSeries σ K →+* K) := by
    ext f
    rfl
  rw [← hker, Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective]

theorem rectangularAugmentation_ker_pow (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    (RingHom.ker (rectangularAugmentation (K := K) n hn)) ^ (1 + ∑ i, n i) = ⊥ := by
  rw [rectangularAugmentation_ker_eq_map, ← Ideal.map_pow]
  apply le_antisymm _ bot_le
  calc
    _ ≤ Ideal.map (Ideal.Quotient.mk (rectangularIdeal (K := K) n))
          (PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) (1 + ∑ i, n i)) := by
      apply Ideal.map_mono
      simpa only [Nat.mul_one] using
        PiExponent.JetGeometry.ideal_pow_le_weightedIdeal (R := K) (fun _ : σ => 1)
          (PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) 1) 1 le_rfl (1 + ∑ i, n i)
    _ ≤ Ideal.map (Ideal.Quotient.mk (rectangularIdeal (K := K) n))
          (rectangularIdeal (K := K) n) :=
      Ideal.map_mono (ordinaryIdeal_le_rectangularIdeal n)
    _ = ⊥ := Ideal.map_quotient_self _

theorem length_rectangularQuotient (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    Module.length (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n)
      (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) = (∏ i, n i : ℕ) := by
  let := (rectangularAugmentation (K := K) n hn).domain_nontrivial
  let := rectangularQuotient_isLocal (K := K) n hn
  rw [PiExponentJets.W24.ring_length_eq_finrank_of_augmentation
    (rectangularAugmentation (K := K) n hn)
    (rectangularAugmentation_algebraMap n hn), finrank_rectangularQuotient]

def rectangularTaylorFactor {A : Type*} [CommRing A] (n : σ → ℕ)
    (I : Ideal A) (tau : A →+* MvPowerSeries σ K)
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0) :
    (A ⧸ I) →+* (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (rectangularIdeal (K := K) n)).comp tau)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hvanish a ha))

omit [Fintype σ] in
@[simp] theorem rectangularTaylorFactor_mk {A : Type*} [CommRing A]
    (n : σ → ℕ) (I : Ideal A) (tau : A →+* MvPowerSeries σ K)
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0)
    (a : A) : rectangularTaylorFactor n I tau hvanish (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (rectangularIdeal (K := K) n) (tau a) := rfl

theorem rectangular_length_le_of_residue_cotangent
    {A C : Type*} [CommRing A] [CommRing C] [Algebra C A]
    (n : σ → ℕ) (hn : ∀ i, 0 < n i)
    [Algebra C (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n)]
    (P : Ideal A)
    (f : A →ₐ[C] (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n))
    (rho : A →+* K) (hrho : Function.Surjective rho)
    (hcomm : (rectangularAugmentation (K := K) n hn).comp f.toRingHom = rho)
    (hf : P ≤ (RingHom.ker (rectangularAugmentation (K := K) n hn)).comap f)
    (hCot : Function.Surjective
      (Ideal.mapCotangent P (RingHom.ker (rectangularAugmentation (K := K) n hn)) f hf)) :
    (∏ i, n i : ℕ) ≤ Module.length A A := by
  have hlength := PiExponentJets.W24.length_le_of_residue_cotangent_map
    P (RingHom.ker (rectangularAugmentation (K := K) n hn)) f hf
    rho (rectangularAugmentation (K := K) n hn) hrho hcomm rfl hCot
    (1 + ∑ i, n i) (rectangularAugmentation_ker_pow n hn)
  rw [length_rectangularQuotient n hn] at hlength
  exact hlength

theorem rectangular_quotient_length_le_of_residue_cotangent
    {A C : Type*} [CommRing A] [CommRing C] [Algebra C A]
    (n : σ → ℕ) (hn : ∀ i, 0 < n i)
    [Algebra C (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n)]
    (P I : Ideal A)
    (f : A →ₐ[C] (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n))
    (rho : A →+* K) (hrho : Function.Surjective rho)
    (hcomm : (rectangularAugmentation (K := K) n hn).comp f.toRingHom = rho)
    (hf : P ≤ (RingHom.ker (rectangularAugmentation (K := K) n hn)).comap f)
    (hCot : Function.Surjective
      (Ideal.mapCotangent P (RingHom.ker (rectangularAugmentation (K := K) n hn)) f hf))
    (hI : I ≤ RingHom.ker f.toRingHom) :
    (∏ i, n i : ℕ) ≤ Module.length A (A ⧸ I) := by
  let B := MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n
  have hs := PiExponentJets.W24.algHom_surjective_of_residue_cotangent
    P (RingHom.ker (rectangularAugmentation (K := K) n hn)) f hf
    rho (rectangularAugmentation (K := K) n hn) hrho hcomm rfl hCot
    (1 + ∑ i, n i) (rectangularAugmentation_ker_pow n hn)
  let g : (A ⧸ I) →+* B := Ideal.Quotient.lift I f.toRingHom hI
  have hg : Function.Surjective g :=
    Ideal.Quotient.lift_surjective_of_surjective I hI hs
  let : Algebra (A ⧸ I) B := g.toAlgebra
  have hg' : Function.Surjective (algebraMap (A ⧸ I) B) := hg
  have hlength : Module.length B B ≤ Module.length (A ⧸ I) (A ⧸ I) := by
    rw [← Module.length_eq_of_surjective (M := B) hg']
    exact Module.length_le_of_surjective (Algebra.linearMap (A ⧸ I) B) hg'
  rw [Module.length_eq_of_surjective (R := A ⧸ I) (M := A ⧸ I)
    (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap A (A ⧸ I)))]
  rw [length_rectangularQuotient n hn] at hlength
  exact hlength

def rectangularTaylorAlgHom {A : Type*} [CommRing A] [Algebra ℚ A] [Algebra ℚ K]
    (n : σ → ℕ) (tau : A →+* MvPowerSeries σ K) :
    A →ₐ[ℚ] (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) :=
  ((Ideal.Quotient.mk (rectangularIdeal (K := K) n)).comp tau).toRatAlgHom

omit [Fintype σ] in
@[simp] theorem rectangularTaylorAlgHom_apply {A : Type*}
    [CommRing A] [Algebra ℚ A] [Algebra ℚ K]
    (n : σ → ℕ) (tau : A →+* MvPowerSeries σ K) (a : A) :
    rectangularTaylorAlgHom n tau a =
      Ideal.Quotient.mk (rectangularIdeal (K := K) n) (tau a) := rfl

omit [Fintype σ] in
theorem rectangularTaylorAlgHom_augmentation {A : Type*}
    [CommRing A] [Algebra ℚ A] [Algebra ℚ K]
    (n : σ → ℕ) (hn : ∀ i, 0 < n i) (tau : A →+* MvPowerSeries σ K)
    (rho : A →+* K) (hconstant : ∀ a, constantCoeff (tau a) = rho a) :
    (rectangularAugmentation (K := K) n hn).comp
      (rectangularTaylorAlgHom n tau).toRingHom = rho := by
  ext a
  exact hconstant a

omit [Fintype σ] in
theorem rectangularTaylorAlgHom_maps_residueIdeal {A : Type*}
    [CommRing A] [Algebra ℚ A] [Algebra ℚ K]
    (n : σ → ℕ) (hn : ∀ i, 0 < n i) (tau : A →+* MvPowerSeries σ K)
    (rho : A →+* K) (hconstant : ∀ a, constantCoeff (tau a) = rho a)
    (P : Ideal A) (hP : P ≤ RingHom.ker rho) :
    P ≤ (RingHom.ker (rectangularAugmentation (K := K) n hn)).comap
      (rectangularTaylorAlgHom n tau) := by
  intro a ha
  change constantCoeff (tau a) = 0
  rw [hconstant]
  exact hP ha

theorem rectangularTaylor_length_lower {A : Type*}
    [CommRing A] [Algebra ℚ A] [Algebra ℚ K]
    (n : σ → ℕ) (hn : ∀ i, 0 < n i) (tau : A →+* MvPowerSeries σ K)
    (rho : A →+* K) (hrho : Function.Surjective rho)
    (hconstant : ∀ a, constantCoeff (tau a) = rho a)
    (P I : Ideal A) (hP : P ≤ RingHom.ker rho)
    (hCot : Function.Surjective
      (Ideal.mapCotangent P (RingHom.ker (rectangularAugmentation (K := K) n hn))
        (rectangularTaylorAlgHom n tau)
        (rectangularTaylorAlgHom_maps_residueIdeal n hn tau rho hconstant P hP)))
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0) :
    (∏ i, n i : ℕ) ≤ Module.length A (A ⧸ I) := by
  apply rectangular_quotient_length_le_of_residue_cotangent n hn P I
    (rectangularTaylorAlgHom n tau) rho hrho
    (rectangularTaylorAlgHom_augmentation n hn tau rho hconstant)
    (rectangularTaylorAlgHom_maps_residueIdeal n hn tau rho hconstant P hP) hCot
  intro a ha
  change Ideal.Quotient.mk (rectangularIdeal (K := K) n) (tau a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hvanish a ha)

def localizedTaylorMap {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a)) :
    L →+* MvPowerSeries σ K :=
  IsLocalization.lift (M := M) (S := L) (g := tau) (fun s : M => by
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    rw [hconstant]
    exact (IsLocalization.map_units L s).map rho)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem localizedTaylorMap_algebraMap {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a)) (a : A) :
    localizedTaylorMap M tau rho hconstant (algebraMap A L a) = tau a := by
  simp only [localizedTaylorMap, IsLocalization.lift_eq]

omit [Fintype σ] [DecidableEq σ] in
theorem localizedTaylorMap_constant {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a)) :
    (constantCoeff : MvPowerSeries σ K →+* K).comp
      (localizedTaylorMap M tau rho hconstant) = rho := by
  apply IsLocalization.ringHom_ext M
  ext a
  simp only [RingHom.comp_apply, localizedTaylorMap_algebraMap]
  exact hconstant a

omit [Fintype σ] [DecidableEq σ] in
theorem linearCoefficient_mul (i : σ) (f g : MvPowerSeries σ K) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g +
      constantCoeff g * coeff (Finsupp.single i 1) f := by
  have h (p : MvPowerSeries σ K) :
      constantCoeff (MvPowerSeries.pderiv i p) = coeff (Finsupp.single i 1) p := by
    rw [← coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
    simp
  rw [← h, (MvPowerSeries.pderiv i).leibniz]
  simp only [smul_eq_mul, map_add, map_mul, h]

omit [Fintype σ] [DecidableEq σ] in
theorem localizedTaylorMap_linearCoefficient {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a))
    (i : σ) (d : L → K)
    (hd : ∀ x y, d (x * y) = rho x * d y + rho y * d x)
    (ha : ∀ a, coeff (Finsupp.single i 1) (tau a) = d (algebraMap A L a))
    (x : L) :
    coeff (Finsupp.single i 1) (localizedTaylorMap M tau rho hconstant x) = d x := by
  obtain ⟨a, s, hs⟩ := IsLocalization.exists_mk'_eq M x
  have heq : x * algebraMap A L s = algebraMap A L a :=
    (IsLocalization.mk'_eq_iff_eq_mul.mp hs).symm
  have hc0 (y : L) :
      constantCoeff (localizedTaylorMap M tau rho hconstant y) = rho y :=
    RingHom.congr_fun (localizedTaylorMap_constant M tau rho hconstant) y
  have hc := congrArg
    (fun y => coeff (Finsupp.single i 1) (localizedTaylorMap M tau rho hconstant y)) heq
  rw [map_mul, linearCoefficient_mul, hc0, hc0,
    localizedTaylorMap_algebraMap, localizedTaylorMap_algebraMap, ha, ha] at hc
  have hd' := hd x (algebraMap A L s)
  rw [heq] at hd'
  have he : rho (algebraMap A L s) *
      coeff (Finsupp.single i 1) (localizedTaylorMap M tau rho hconstant x) =
        rho (algebraMap A L s) * d x := by
    exact add_left_cancel (hc.trans hd')
  exact mul_left_cancel₀ ((IsLocalization.map_units L s).map rho).ne_zero he

omit [Fintype σ] in
theorem localizedTaylorMap_ideal_le {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a))
    (n : σ → ℕ) (I : Ideal A)
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0) :
    I.map (algebraMap A L) ≤
      (rectangularIdeal (K := K) n).comap (localizedTaylorMap M tau rho hconstant) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change localizedTaylorMap M tau rho hconstant (algebraMap A L a) ∈ rectangularIdeal n
  rw [localizedTaylorMap_algebraMap]
  exact hvanish a ha

def localizedRectangularTaylorFactor {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a))
    (n : σ → ℕ) (I : Ideal A)
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0) :
    (L ⧸ I.map (algebraMap A L)) →+*
      (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) :=
  rectangularTaylorFactor n (I.map (algebraMap A L))
    (localizedTaylorMap M tau rho hconstant)
    (localizedTaylorMap_ideal_le M tau rho hconstant n I hvanish)

omit [Fintype σ] in
@[simp] theorem localizedRectangularTaylorFactor_mk {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a))
    (n : σ → ℕ) (I : Ideal A)
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0) (a : A) :
    localizedRectangularTaylorFactor M tau rho hconstant n I hvanish
      (Ideal.Quotient.mk (I.map (algebraMap A L)) (algebraMap A L a)) =
        Ideal.Quotient.mk (rectangularIdeal (K := K) n) (tau a) := by
  change Ideal.Quotient.mk (rectangularIdeal (K := K) n)
    (localizedTaylorMap M tau rho hconstant (algebraMap A L a)) = _
  rw [localizedTaylorMap_algebraMap]

end
end PiExponentApprox.TransverseMultiplicity

end OAI
