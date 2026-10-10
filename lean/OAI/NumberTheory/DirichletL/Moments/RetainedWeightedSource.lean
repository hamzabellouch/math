import OAI.NumberTheory.DirichletL.Moments.OriginalReflectionApproximation
import OAI.NumberTheory.DirichletL.Moments.ReflectedNormalization
import OAI.NumberTheory.DirichletL.Moments.ReflectionWeightedEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentRetainedWeightedSource
open HeckeFamily CenteredMomentNaturalPrimitive CenteredMomentReflectionDeletion
open CenteredMomentReflectionMass CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectedNormalization
open CenteredMomentReflectedAnnuli CenteredMomentReflectedTruncation
open CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

abbrev sourcePrimes (χ ψ : Character) := redundantSet χ.modulus ψ.modulus

def dualScale (χ ψ : Character) (X : ℝ)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) : ℝ :=
  (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D.val,P):ℝ)/(X*norm H.val)

lemma dualScale_pos (χ ψ : Character) (X : ℝ) (hX : 0<X)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
    0<dualScale χ ψ X D H := by
  have hD : (∏P∈D.val,P : Ideal O)≠0 := Finset.prod_ne_zero_iff.mpr (fun P hP=>
    (redundantSet_prime χ.modulus ψ.modulus P ((Finset.mem_powerset.mp D.property) hP)).ne_zero)
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hd : 0<(Ideal.absNorm (∏P∈D.val,P):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  exact div_pos (mul_pos hQ hd) (mul_pos hX (CenteredMomentReflectionDeletion.norm_pos H.val))

def retainedColumn (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) (hX : 0<X)
    (B n : ℕ) (P : ℂ) (a : Index (sourcePrimes χ ψ)) : ℂ :=
  if a.2∈retainedAnnuli R (dualScale χ ψ X a.1.1 a.1.2)
      (dualScale_pos χ ψ X hX a.1.1 a.1.2) then
    HeckeDyadic.polynomial χ.inverse false
      (normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale a.2) t)
      (dyadicScale a.2*dualScale χ ψ X a.1.1 a.1.2) 0 0 * P
  else 0

lemma retainedColumn_zero (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) (hX : 0<X)
    (B n : ℕ) (P : ℂ) (a : Index (sourcePrimes χ ψ))
    (ha : a.2∉retainedAnnuli R (dualScale χ ψ X a.1.1 a.1.2)
      (dualScale_pos χ ψ X hX a.1.1 a.1.2)) :
    retainedColumn χ ψ W X R t hX B n P a=0 := by
  simp only [retainedColumn,ite_eq_right ha]

theorem finiteAnnularColumn_normalized (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
    finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
      R (dualScale χ ψ X D H)*P =
    (((1+‖t‖)^n:ℝ):ℂ)*∑'k : ℤ,(annularMass B k:ℂ)*
      retainedColumn χ ψ W X R t hX B n P ((D,H),k) := by
  rw [finiteAnnularColumn,dite_eq_left (dualScale_pos χ ψ X hX D H),
    tsum_eq_sum (s:=retainedAnnuli R (dualScale χ ψ X D H) (dualScale_pos χ ψ X hX D H))
      (fun k hk=>by simp only [retainedColumn,ite_eq_right hk,mul_zero]),
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [retainedColumn,ite_eq_left hk,actual_annular_normalization]
  ring

theorem retainedOriginal_eq_weighted (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (hs : Summable (fun a : Index (sourcePrimes χ ψ)=>
      ‖signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
        retainedColumn χ ψ W X R t hX B n P a‖)) :
    retainedOriginal χ ψ W X R t*P =
      (((1+‖t‖)^n:ℝ):ℂ)*∑'a : Index (sourcePrimes χ ψ),
        signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
          retainedColumn χ ψ W X R t hX B n P a := by
  rw [signed_series_reindex ψ ψ.inverse (sourcePrimes χ ψ) B _ hs]
  change (∑D∈(sourcePrimes χ ψ).powerset,∑'H : SmoothIdeal (sourcePrimes χ ψ),
    coefficient ψ ψ.inverse (sourcePrimes χ ψ) D H*
      finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
        R ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)))*P = _
  rw [←Finset.sum_coe_sort (sourcePrimes χ ψ).powerset,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  rw [←tsum_mul_right,←tsum_mul_left]
  apply tsum_congr
  intro H
  change (coefficient ψ ψ.inverse (sourcePrimes χ ψ) D.val H*
    finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
      R (dualScale χ ψ X D H))*P = _
  rw [mul_assoc,finiteAnnularColumn_normalized χ ψ W X R t hX B n P D H]
  simp only [mul_assoc,tsum_mul_left]
  ring

theorem retainedOriginal_fiber_summable (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (hs : Summable (fun a : Index (sourcePrimes χ ψ)=>
      ‖signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
        retainedColumn χ ψ W X R t hX B n P a‖))
    (D : (sourcePrimes χ ψ).powerset) :
    Summable (fun H : SmoothIdeal (sourcePrimes χ ψ)=>
      ‖(coefficient ψ ψ.inverse (sourcePrimes χ ψ) D.val H*
        finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
          R (dualScale χ ψ X D H))*P‖) := by
  have hh := ((hs.of_norm.prod.prod_factor D).mul_left (((1+‖t‖)^n:ℝ):ℂ)).norm
  apply hh.congr
  intro H
  congr 1
  rw [mul_assoc,finiteAnnularColumn_normalized χ ψ W X R t hX B n P D H]
  simp only [signedWeight,mul_assoc,tsum_mul_left]
  ring

theorem actual_retained_weighted_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(χ ψ : ι→Character)(W : ι→ℝ→ℂ)(X R t : ι→ℝ)
        (hX : ∀i,0<X i)(B : ι→ℕ)(n : ℕ)(P : ι→ℂ),
      (∀i,2≤B i) → ∀(T Rcap E : ℝ),0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀a : ∀i,Index (sourcePrimes (χ i) (ψ i)),
        (∑i,‖retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) (a i)‖^2)≤E) →
      (∀i,Summable (fun a : Index (sourcePrimes (χ i) (ψ i))=>
        ‖signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*
          retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) a‖)) ∧
      (∀i,retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i =
        (((1+‖t i‖)^n:ℝ):ℂ)*∑'a : Index (sourcePrimes (χ i) (ψ i)),
          signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*
            retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) a) ∧
      (∀i,∀D : (sourcePrimes (χ i) (ψ i)).powerset,
        Summable (fun H : SmoothIdeal (sourcePrimes (χ i) (ψ i))=>
          ‖(coefficient (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) D.val H*
            finiteAnnularColumn (χ i).inverse
              (paperRadialFourier (CompletedHeight.normTwistedSource (W i) (t i)))
              (R i) (dualScale (χ i) (ψ i) (X i) D H))*P i‖)) ∧
      (∑i,‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖^2) ≤
        C*Rcap^ε*(1+T)^(2*n)*E := by
  obtain ⟨C,hC,hbound⟩ := actual_reflection_energy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ ψ W X R t hX B n P hB T Rcap E hT ht hRcap hcap hselection
  let f (i : ι) := retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i)
  have he := hbound (fun i=>sourcePrimes (χ i) (ψ i))
    (fun i=>redundantSet_prime (χ i).modulus (ψ i).modulus) ψ (fun i=>(ψ i).inverse)
    B hB Rcap E hRcap hcap f hselection
  have hid (i : ι) := retainedOriginal_eq_weighted (χ i) (ψ i) (W i) (X i) (R i) (t i)
    (hX i) (B i) n (P i) (he.1 i)
  refine ⟨he.1,hid,?_,?_⟩
  · intro i D
    exact retainedOriginal_fiber_summable (χ i) (ψ i) (W i) (X i) (R i) (t i)
      (hX i) (B i) n (P i) (he.1 i) D
  · let z (i : ι) := ∑'a : Index (sourcePrimes (χ i) (ψ i)),
        signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*f i a
    have hn (i : ι) :
        ‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖=(1+‖t i‖)^n*‖z i‖ := by
      rw [hid i,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    have hp (i : ι) : (1+‖t i‖)^n≤(1+T)^n :=
      pow_le_pow_left₀ (by positivity) (by linarith [ht i]) n
    calc
      (∑i,‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖^2)
          = ∑i,((1+‖t i‖)^n*‖z i‖)^2 := by simp_rw [hn]
      _ ≤ ∑i,((1+T)^n*‖z i‖)^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _)) 2
      _ = ((1+T)^n)^2*∑i,‖z i‖^2 := by simp only [mul_pow,Finset.mul_sum]
      _ ≤ ((1+T)^n)^2*(C*Rcap^ε*E) := mul_le_mul_of_nonneg_left he.2 (sq_nonneg _)
      _ = C*Rcap^ε*(1+T)^(2*n)*E := by rw [←pow_mul,Nat.mul_comm n 2];ring

end SevenEighths.CenteredMomentRetainedWeightedSource

end

end OAI
