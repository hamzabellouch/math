import OAI.NumberTheory.DirichletL.Moments.PrimeGlobal
import OAI.NumberTheory.DirichletL.Hecke.PrimeScale

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.CenteredMomentPrimeHeight
open HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDyadic HeckeZeroSupremum
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem ray_prime_bounded_scale (W : ℝ→ℂ) (A B lo hi D : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : Continuous W) (_hD : 1≤D) :
    ∃C : ℝ,0<C ∧ ∀(χ : Character)(P σ freq : ℝ),1≤P → P≤D → lo≤σ → σ≤hi →
      ‖rayPrimePolynomial M H χ W B P σ freq‖≤C := by
  obtain ⟨Cw,hCw,hprofile⟩ := fixed_profile_norm_bound W hW A B lo hi hA
  let S := annulusSet B D
  refine ⟨((S.card:ℝ)+1)*Cw,by positivity,?_⟩
  intro χ P σ freq hP hPD hσ hσhi
  have hp : 0<P := zero_lt_one.trans_le hP
  have hsub : (annulusSet B P).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H)⊆S := by
    intro I hI
    have hi := ConcretePrimeRowBridge.mem_idealsUpTo.mp (Finset.mem_filter.mp hI).1
    apply ConcretePrimeRowBridge.mem_idealsUpTo.mpr
    exact ⟨hi.1,hi.2.trans (Nat.floor_mono (mul_le_mul_of_nonneg_left hPD (le_trans zero_le_one (le_max_left _ _))))⟩
  have hn (I : Ideal O) : ‖idealCoeff χ I*annularWeight W P σ freq I‖≤Cw := by
    have hc := idealCoeff_norm_le_one χ I
    apply (show ‖idealCoeff χ I*annularWeight W P σ freq I‖≤‖annularWeight W P σ freq I‖ by
      rw [norm_mul];exact mul_le_of_le_one_left (norm_nonneg _) hc).trans
    by_cases hz : W ((I.absNorm:ℝ)/P)=0
    · simp [annularWeight,hz,hCw.le]
    · have hs := hWs hz
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hA.trans_le hs.1)]
      simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσ,hσhi⟩ _ hs
  have hpow : ‖(P:ℂ)^(-(1/2:ℂ))‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
    norm_num only [Complex.neg_re,show ((1/2:ℂ).re)=1/2 by norm_num]
    exact Real.rpow_le_one_of_one_le_of_nonpos hP (by norm_num)
  unfold rayPrimePolynomial
  rw [norm_mul]
  calc
    _ ≤ ‖∑ I∈(annulusSet B P).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H),
        idealCoeff χ I*annularWeight W P σ freq I‖ := mul_le_of_le_one_left (norm_nonneg _) hpow
    _ ≤ ∑ I∈(annulusSet B P).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H),Cw :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun I _=>hn I))
    _ ≤ ∑ _I∈S,Cw := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>hCw.le)
    _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul];nlinarith

lemma lifted_scale_power (Z T D P κ loss : ℝ) (hZ : 0<Z) (hT : 0<T) (hD : D≠0)
    (hU : 1<(Z*T)^D) (hP : 0<P) :
    ((Z*T)^D)^(κ*Real.logb ((Z*T)^D) P+2*(loss/(2*D)))=
      P^κ*Z^loss*T^loss := by
  have hu : 0<(Z*T)^D := zero_lt_one.trans hU
  rw [Real.rpow_add hu]
  have hs : ((Z*T)^D)^(κ*Real.logb ((Z*T)^D) P)=P^κ := by
    rw [mul_comm κ,Real.rpow_mul hu.le,Real.rpow_logb hu (ne_of_gt hU) hP]
  rw [hs,←Real.rpow_mul (mul_pos hZ hT).le]
  have he : D*(2*(loss/(2*D)))=loss := by field_simp
  rw [he,Real.mul_rpow hZ.le hT.le]
  ring

theorem ray_prime_all_height_large (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (_hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧ ∀ Z P : ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀χ : Character,(χ.modulus.absNorm:ℝ)≤Z^Lmod →
      (∀θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).residue≠1) →
    ∀σ freq : ℝ,lo≤σ → σ≤hi →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log P →
      ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C*P^κ*Z^loss*(3+|freq|)^loss := by
  let d := max Lmod Lslot+2
  have hd : 0<d := by dsimp [d];have := le_max_left Lmod Lslot;linarith
  have hd1 : 1≤d := by dsimp [d];have := le_max_left Lmod Lslot;linarith
  have hmd : Lmod+1≤d := by dsimp [d];have := le_max_left Lmod Lslot;linarith
  have hsd : Lslot≤d := by dsimp [d];have := le_max_right Lmod Lslot;linarith
  let eps := loss/(2*d)
  have heps : 0<eps := by dsimp [eps];positivity
  let e := min (eps/32) (1/2000)
  have he : 0<e := lt_min (by positivity) (by norm_num)
  have he' : e<1/1000 := (min_le_right _ _).trans_lt (by norm_num)
  have hbudget : 8*e*1+eps/2≤eps := by have := min_le_left (eps/32) (1/2000);dsimp [e];linarith
  obtain ⟨C,hC,hbound⟩ := CenteredMomentPrimeGlobal.ray_prime_global_squared M H hH W A B hA hWs hW
    1 d 1 eps e (eps/2) (4/d) lo hi κ (by norm_num) hd.le (by norm_num) heps he he'
    (by positivity) (by positivity) hbudget hbeta hκ
  let Z₀ := max 2 (M.absNorm:ℝ)
  refine ⟨C,Z₀,hC,lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (le_max_left _ _),?_⟩
  intro Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi hlarge
  have hz2 : 2≤Z := (le_max_left _ _).trans hZ
  have hz : 0<Z := by linarith
  have hz1 : 1≤Z := by linarith
  have hMZ : (M.absNorm:ℝ)≤Z := (le_max_right _ _).trans hZ
  let T := 3+|freq|
  let Zt := Z*T
  let U := Zt^d
  have hT3 : 3≤T := by dsimp [T];linarith [abs_nonneg freq]
  have hT : 0<T := by linarith
  have hzt6 : 6≤Zt := by dsimp [Zt];nlinarith
  have hzt : 0<Zt := by linarith
  have hzt1 : 1≤Zt := by linarith
  have hZzt : Z≤Zt := by dsimp [Zt];nlinarith
  have hTzt : T≤Zt := by dsimp [Zt];nlinarith
  have hztU : Zt≤U := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hzt1 hd1
  have hU : 1<U := by linarith
  have hUp : 0<U := by linarith
  have hPU : P≤U := hPcap.trans ((Real.rpow_le_rpow_of_exponent_le hz1 hsd).trans
    (Real.rpow_le_rpow hz.le hZzt hd.le))
  let r := Real.logb U P
  have hr : 0≤r := Real.logb_nonneg hU hP
  have hr1 : r≤1 := (Real.logb_le_iff_le_rpow hU (zero_lt_one.trans_le hP)).mpr
    (by simpa only [Real.rpow_one] using hPU)
  have hPr : U^r=P := Real.rpow_logb hUp (ne_of_gt hU) (zero_lt_one.trans_le hP)
  have hQ (θ : RayQuotient.Characters M H) : ((twistedFamily M H hH χ θ).modulus.absNorm:ℝ)≤U := by
    have ht : ((twistedFamily M H hH χ θ).modulus.absNorm:ℝ)≤(χ.modulus.absNorm:ℝ)*M.absNorm := by
      exact_mod_cast HeckePrimeScale.twisted_modulus_bound M H hH χ θ
    apply ht.trans
    calc
      _ ≤ Z^Lmod*Z := mul_le_mul hχ hMZ (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _)
      _ = Z^(Lmod+1) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ Z^d := Real.rpow_le_rpow_of_exponent_le hz1 hmd
      _ ≤ U := Real.rpow_le_rpow hz.le hZzt hd.le
  have hheight : (3+2*Zt)^2≤U^(4/d) := by
    have heq : U^(4/d)=Zt^(4:ℝ) := by
      dsimp [U]
      rw [←Real.rpow_mul hzt.le]
      congr 1
      field_simp
    rw [heq,Real.rpow_ofNat]
    have hb : 3+2*Zt≤Zt^2 := by nlinarith
    calc
      _ ≤ (Zt^2)^2 := pow_le_pow_left₀ (by positivity) hb 2
      _ = _ := by ring
  have hb := hbound Zt d hzt1 hd.le le_rfl (by linarith : 2≤Zt^d)
    (by simpa only [Real.rpow_one] using (show (2:ℝ)<Zt by linarith)) χ hn 0 r σ freq hr hr1 hσ hσhi
    (by change _≤Real.log (U^r);rw [hPr];exact hlarge) hQ
    (by norm_num only [Nat.mul_zero,Nat.zero_add,Nat.cast_ofNat,Real.rpow_one];dsimp [T] at hTzt;linarith)
    (by simpa only [Nat.mul_zero,Nat.zero_add,Nat.cast_ofNat,Real.rpow_one] using hheight)
  change ‖rayPrimePolynomial M H χ W B (U^r) σ freq‖^2≤C*U^(κ*r+2*eps) at hb
  rw [hPr] at hb
  apply hb.trans_eq
  dsimp only [U,Zt,r,eps,T]
  rw [lifted_scale_power Z (3+|freq|) d P κ loss hz hT hd.ne' hU (zero_lt_one.trans_le hP)]
  ring

theorem ray_prime_all_height_squared (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧ ∀ Z P : ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀χ : Character,(χ.modulus.absNorm:ℝ)≤Z^Lmod →
      (∀θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).residue≠1) →
    ∀σ freq : ℝ,lo≤σ → σ≤hi →
      ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C*(1+|freq|)^degree*Z^loss*P^κ := by
  obtain ⟨Cbig,Z₀,hCbig,hZ₀,hbig⟩ := ray_prime_all_height_large M H hH W A B hA hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  let K := 2*(|Real.log A|+|Real.log B|)+1
  have hK : 0≤K := by dsimp [K];positivity
  obtain ⟨Csmall,hCs,hsmall⟩ := ray_prime_bounded_scale M H W A B lo hi (Real.exp K) hA hWs hW.continuous
    (Real.one_le_exp hK)
  let degree := ⌈loss⌉₊
  let C0 := Cbig+Csmall^2
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0*(3:ℝ)^degree,Z₀,by positivity,hZ₀,?_⟩
  intro Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi
  have hz1 : 1≤Z := hZ₀.le.trans hZ
  have hκ0 : 0≤κ := by linarith
  have hpκ : 1≤P^κ := Real.one_le_rpow hP hκ0
  have hzloss : 1≤Z^loss := Real.one_le_rpow hz1 hloss.le
  have htbase : 1≤3+|freq| := by linarith [abs_nonneg freq]
  have htloss : 1≤(3+|freq|)^loss := Real.one_le_rpow htbase hloss.le
  have hbase : ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C0*P^κ*Z^loss*(3+|freq|)^loss := by
    by_cases hlarge : K≤Real.log P
    · exact (hbig Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi hlarge).trans
        (by dsimp [C0];gcongr; nlinarith [sq_nonneg Csmall])
    · have hPD : P≤Real.exp K := by
        have he := Real.exp_le_exp.mpr (le_of_not_ge hlarge)
        simpa only [Real.exp_log (zero_lt_one.trans_le hP)] using he
      have hb := pow_le_pow_left₀ (norm_nonneg _) (hsmall χ P σ freq hP hPD hσ hσhi) 2
      apply hb.trans
      calc
        Csmall^2 ≤ C0 := by dsimp [C0];linarith
        _ ≤ C0*P^κ := le_mul_of_one_le_right hC0.le hpκ
        _ ≤ C0*P^κ*Z^loss := le_mul_of_one_le_right (by positivity) hzloss
        _ ≤ _ := le_mul_of_one_le_right (by positivity) htloss
  have hheight : (3+|freq|)^loss≤(3:ℝ)^degree*(1+|freq|)^degree := by
    calc
      _ ≤ (3+|freq|)^(degree:ℝ) := Real.rpow_le_rpow_of_exponent_le htbase (Nat.le_ceil loss)
      _ = (3+|freq|)^degree := Real.rpow_natCast _ _
      _ ≤ (3*(1+|freq|))^degree := pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg freq]) _
      _ = _ := mul_pow _ _ _
  apply hbase.trans
  calc
    _ ≤ C0*P^κ*Z^loss*((3:ℝ)^degree*(1+|freq|)^degree) :=
      mul_le_mul_of_nonneg_left hheight (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentPrimeHeight
end

end OAI
