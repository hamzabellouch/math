import OAI.NumberTheory.DirichletL.Moments.FirstSecondLossParameters
import OAI.NumberTheory.DirichletL.Moments.FirstMixedMainError

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentSuccessorPaidParameters
open CenteredMomentFirstSecondLossParameters

def edge (epsChild epsRemove delta epsilon delta1 delta2 theta kappa mesh : ℝ) : ℝ :=
  epsChild+epsRemove+2*delta+epsilon+delta2+delta1/6+kappa*mesh+7*theta/3

def exceptional (sigma deltafr epsilon delta B theta : ℝ) : ℝ :=
  3*sigma+5*deltafr/6+2*epsilon+2*delta+2*(5*B+1)*theta

def diagonal (sigma delta reserve epsilon A : ℝ) : ℝ :=
  2*sigma+delta+reserve+epsilon*A

lemma paid_normalization (Z shortening allowance paid : ℝ) (hZ : 0<Z) :
    Z^(-shortening-allowance)*Z^(shortening+paid)=Z^(paid-allowance) := by
  rw [←Real.rpow_add hZ]
  congr 1
  ring

lemma paid_normalization_with_ratio (Z shortening allowance paid ratio : ℝ)
    (hZ : 0<Z) :
    Z^(-shortening-allowance)*(Z^(shortening+paid)*ratio^((1:ℝ)/6))=
      Z^(paid-allowance)*ratio^((1:ℝ)/6) := by
  rw [←mul_assoc,paid_normalization Z shortening allowance paid hZ]

theorem actual_paid_error_reference
    (ρ υ : HeckeFamily.Character) (χ : RayFourExpansion.RayCharacter)
    (p : HeckeFamily.O) (hp : p≠0) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (Z V C allowance paid : ℝ) (hZ : 1<Z) (hV : 0<V) (hC : 0<C)
    (hυ : υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter ρ χ)
      CenteredMomentSecondHeightFamily.fixedBadMask p
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent n)) :
    (V/C)*CenteredMomentAmplificationErrorEnergy.localErrorCost p n*
      (υ.modulus.absNorm:ℝ)*(V/C/(CenteredMomentSectorLocalization.normValue p)^(n+1))*
      Z^(CenteredMomentFirstAmplificationChoice.errorRemoval p Z (n+1)+paid)/
      ((ρ.modulus.absNorm:ℝ)*(V/C)^2*Z^allowance)≤
      CenteredMomentFirstSourceConductorCaps.rayCost*Z^(paid-allowance) := by
  have hh:=CenteredMomentFirstMixedMainError.actual_main_error_reference
    ρ υ χ p hp n hn Z V C allowance
    (Z^(CenteredMomentFirstAmplificationChoice.errorRemoval p Z (n+1)+paid))
    hZ hV hC (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hυ
  apply hh.trans_eq
  rw [mul_assoc,paid_normalization Z _ allowance paid (zero_lt_one.trans hZ)]

lemma declared_parent_deficit (actual declared loss : ℝ) (h : actual≤declared) :
    actual+(declared-actual)/6+loss≤declared+loss := by linarith

lemma paired_declared_parent (actual declared left right loss : ℝ)
    (h : actual≤declared)
    (hl : left≤(declared-actual)/6+loss)
    (hr : right≤(declared-actual)/6+loss) :
    actual+(left+right)/2≤declared+loss := by linarith

lemma mesh_cost (kappa reserve : ℝ) (hk : 0≤kappa) (hr : 0≤reserve) :
    kappa*(reserve/(kappa+1))≤reserve := by
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0<kappa+1)).mpr
  nlinarith

theorem simultaneous_parameters (Mcap B kappa epsilonTarget : ℝ)
    (hM : 0≤Mcap) (hB : 0≤B) (hk : 0≤kappa) (he : 0<epsilonTarget) :
    ∃ sigma reserve mesh : ℝ,
      0<sigma ∧ sigma≤1 ∧ sigma≤epsilonTarget/1000 ∧
      0<reserve ∧ 0<mesh ∧ mesh≤reserve ∧ kappa*mesh≤reserve ∧
      20*reserve≤sigma/2 ∧
      Mcap<(depth Mcap sigma:ℝ)*sigma/2 ∧
      (∀ epsChild epsRemove delta epsilon delta1 delta2 theta,
        epsChild≤reserve → epsRemove≤reserve → delta≤reserve → epsilon≤reserve →
        delta1≤reserve → delta2≤reserve → theta≤reserve →
        (depth Mcap sigma:ℝ)*edge epsChild epsRemove delta epsilon delta1 delta2 theta kappa mesh
          ≤epsilonTarget/16) ∧
      (∀ deltafr epsilon delta theta,
        deltafr≤reserve → epsilon≤reserve → delta≤reserve → theta≤reserve →
        exceptional sigma deltafr epsilon delta B theta≤epsilonTarget/16) ∧
      (∀ delta other epsilon A,
        delta≤reserve → other≤reserve → 0≤epsilon → epsilon≤reserve → A≤Mcap →
        diagonal sigma delta other epsilon A≤epsilonTarget/16) := by
  let sigma : ℝ := min 1 (epsilonTarget/1000)
  have hs : 0<sigma := lt_min (by norm_num) (by positivity)
  have hs1 : sigma≤1 := min_le_left _ _
  have hse : sigma≤epsilonTarget/1000 := min_le_right _ _
  let n := depth Mcap sigma
  let L : ℝ := (n:ℝ)+Mcap+10*B+30
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hL : 0<L := by dsimp [L]; positivity
  let reserve : ℝ := min (sigma/100) (epsilonTarget/(1000*L))
  have hr : 0<reserve := lt_min (by positivity) (by positivity)
  have hrs : reserve≤sigma/100 := min_le_left _ _
  have hre : reserve≤epsilonTarget/(1000*L) := min_le_right _ _
  have hbudget : reserve*(1000*L)≤epsilonTarget := (le_div_iff₀ (by positivity)).mp hre
  have hnres : (n:ℝ)*reserve≤epsilonTarget/1000 := by
    have hx : (n:ℝ)*reserve≤L*reserve := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr.le
    nlinarith
  have hbRes : (10*B+20)*reserve≤epsilonTarget/1000 := by
    have hx : (10*B+20)*reserve≤L*reserve := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr.le
    nlinarith
  have hmRes : (Mcap+2)*reserve≤epsilonTarget/1000 := by
    have hx : (Mcap+2)*reserve≤L*reserve := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr.le
    nlinarith
  let mesh : ℝ := reserve/(kappa+1)
  have hm : 0<mesh := by dsimp [mesh]; positivity
  have hmr : mesh≤reserve := by
    dsimp [mesh]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hkm : kappa*mesh≤reserve := mesh_cost kappa reserve hk hr.le
  refine ⟨sigma,reserve,mesh,hs,hs1,hse,hr,hm,hmr,hkm,by linarith,
    depth_covers Mcap sigma hs,?_,?_,?_⟩
  · intro ec er d e d1 d2 t hec her hd he hd1 hd2 ht
    have hedge : edge ec er d e d1 d2 t kappa mesh≤10*reserve := by
      unfold edge
      linarith
    have hp := mul_le_mul_of_nonneg_left hedge hn
    change (n:ℝ)*edge ec er d e d1 d2 t kappa mesh≤epsilonTarget/16
    nlinarith
  · intro df e d t hdf he hd ht
    have htheta : 2*(5*B+1)*t≤2*(5*B+1)*reserve :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    unfold exceptional
    nlinarith
  · intro d other e A hd ho he0 he hA
    have hmul : e*A≤reserve*Mcap := (mul_le_mul_of_nonneg_left hA he0).trans
      (mul_le_mul_of_nonneg_right he hM)
    unfold diagonal
    nlinarith

end SevenEighths.CenteredMomentSuccessorPaidParameters

end

end OAI
