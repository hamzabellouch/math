import OAI.NumberTheory.Jacobsthal.Estimates.HypotheticalPairRows
import OAI.NumberTheory.Jacobsthal.Sieve.ClosedEulerIndividualUpper
import OAI.NumberTheory.Jacobsthal.Sieve.TagPrimeSieveLower

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosStoppedArithmetic
open NumberTheoryLean ErdosPrimeInputs.MertensStrong ReferenceProductsBasics ReferenceMertens


theorem eventual_closed_euler_lower_scale (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ P : ℝ in atTop,1 < P ∧
      (1-eps)*primeProduct P ≤ Real.exp (-Real.eulerMascheroniConstant)/Real.log P := by
  have hn := normalization_tendsto_one.eventually (lt_mem_nhds (by linarith : 1-eps < (1 : ℝ)))
  filter_upwards [hn,eventually_gt_atTop (1 : ℝ)] with P hn hP
  have hlog := Real.log_pos hP
  have hV := actual_primeProduct_pos P
  have hnorm : 1-eps ≤ Real.exp (-Real.eulerMascheroniConstant)/(Real.log P*primeProduct P) := hn.le
  have hh := (le_div_iff₀ (mul_pos hlog hV)).mp hnorm
  refine ⟨hP,?_⟩
  apply (le_div_iff₀ hlog).mpr
  nlinarith

theorem stopped_pair_coefficient (N J H D L V E S : ℝ)
    (hN : 0 ≤ N) (hJ : 0 ≤ J) (hD : 0 < D) (hL : 0 < L)
    (hV : 0 ≤ V) (hE : 0 ≤ E) (hS : 0 < S) (hSup : S ≤ (111/50 : ℝ))
    (hH : (999/1000 : ℝ)*D*J ≤ H)
    (hNorm : (999/1000 : ℝ)*V ≤ E/L) :
    (39/100 : ℝ)*N*J*V ≤
      ((999/1000 : ℝ)*H/(S*L))*((19/20 : ℝ)*N/D)*(E*(939/1000 : ℝ)) := by
  let a : ℝ := 999/1000
  let b : ℝ := 19/20
  let c : ℝ := 939/1000
  have hConst : (39/100 : ℝ) ≤ (a^3*b*c)/(111/50 : ℝ) := by norm_num [a,b,c]
  have hHJ : a*J ≤ H/D := by
    apply (le_div_iff₀ hD).mpr
    dsimp [a]
    nlinarith
  have hNorm' : a*V ≤ E/L := hNorm
  have hEL : 0 ≤ E/L := div_nonneg hE hL.le
  calc
    _ ≤ ((a^3*b*c)/(111/50 : ℝ))*(N*J*V) := by
      have hh := mul_le_mul_of_nonneg_right hConst (mul_nonneg (mul_nonneg hN hJ) hV)
      nlinarith only [hh]
    _ = (a^2*b*c*N*J*(a*V))/(111/50 : ℝ) := by ring
    _ ≤ (a^2*b*c*N*J*(E/L))/(111/50 : ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNorm'
        (by dsimp [a,b,c];positivity)) (by norm_num)
    _ ≤ (a^2*b*c*N*J*(E/L))/S :=
      div_le_div_of_nonneg_left (by dsimp [a,b,c];positivity) hS hSup
    _ = (a*b*c*N*(a*J)*(E/L))/S := by ring
    _ ≤ (a*b*c*N*(H/D)*(E/L))/S := by
      have hh := mul_le_mul_of_nonneg_left hHJ (show 0 ≤ a*b*c*N by dsimp [a,b,c];positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh hEL) hS.le
    _ = _ := by
      dsimp [a,b,c]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

end ErdosStoppedArithmetic

end

section

open _root_.Filter
namespace ErdosStoppedArithmetic
open Erdos970Dependency.SiegelWalfisz Erdos970.EulerWeightedLower
  NumberTheoryLean.ReferenceProductsBasics ErdosPrimeInputs.MertensStrong

attribute [local instance] Classical.propDecidable

theorem moving_subbin_pair_lower (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ,0 < K ∧ ∀ rho : ℝ,1 < rho → ∃ w0 : ℝ,4 ≤ w0 ∧
      ∀ w : ℝ,w0 ≤ w → ∀ P s x y : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      203/100 ≤ s → s ≤ 219/100 →
      ∀ D : ℕ,0 < D → (999/1000 : ℝ)*(D : ℝ)*P^s ≤ y-x →
      max |x| |y| ≤ 2*w^(Cs+2)*P^s →
      ∀ (E T : Finset ℕ) (good : ℕ → ℤ → Prop),E ⊆ primesThrough P →
      (∀ d ∈ supportedIntegers E ⌊P^(95/100 : ℝ)⌋₊,∀ m ∈ primeMultiplesIn d P x y,
        ((19/20 : ℝ)*(T.card : ℝ)/(D : ℝ))*paperWeight E d ≤
          ((T.filter (fun p => good p m)).card : ℝ)) →
      (39/100 : ℝ)*(T.card : ℝ)*P^s*primeProduct P ≤
        ((admissiblePairs T ((supportedIntegers E ⌊P^(95/100 : ℝ)⌋₊).biUnion
          (fun d => primeMultiplesIn d P x y)) good).card : ℝ) := by
  obtain ⟨K,hK,hPairs⟩ := moving_weighted_pair_lower Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho hrho
  obtain ⟨wS,hwS,hS⟩ := hPairs rho hrho (1/1000) (by norm_num) (by norm_num)
  obtain ⟨P0,hP0⟩ := eventually_atTop.mp (eventual_closed_euler_lower_scale (1/1000) (by norm_num))
  obtain ⟨wG,hwG⟩ := eventually_atTop.mp ((exponential_log_cube_tendsto hK).eventually_ge_atTop (max 2 P0))
  refine ⟨max wS wG,hwS.trans (le_max_left _ _),?_⟩
  intro w hw P s x y hPlower hPupper hs hsupper D hD hCommon hHeight E T good hE hTag
  have hLarge : max 2 P0 ≤ P := (hwG w ((le_max_right _ _).trans hw)).trans hPlower
  have hP2 : 2 ≤ P := (le_max_left _ _).trans hLarge
  have hP : 1 < P := by linarith
  have hPpos : 0 < P := by linarith
  have hPs : 0 < P^s := Real.rpow_pos_of_pos hPpos _
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hWidth : P^s/2 ≤ y-x := by
    have hh := mul_le_mul_of_nonneg_right hD1 (show 0 ≤ (999/1000 : ℝ)*P^s by positivity)
    nlinarith
  have hB : 0 ≤ (19/20 : ℝ)*(T.card : ℝ)/(D : ℝ) := by positivity
  have hResult := hS w ((le_max_left _ _).trans hw) P s x y hPlower hPupper hs hsupper
    hWidth hHeight E T good ((19/20 : ℝ)*(T.card : ℝ)/(D : ℝ)) hE hB hTag
  have hNorm := (hP0 P ((le_max_right _ _).trans hLarge)).2
  have heps : (1 : ℝ)-1/1000=999/1000 := by norm_num
  have hweight : (94/100 : ℝ)-1/1000=939/1000 := by norm_num
  rw [heps] at hNorm
  rw [heps,hweight] at hResult
  have hCoeff := stopped_pair_coefficient (T.card : ℝ) (P^s) (y-x) (D : ℝ) (Real.log P)
    (primeProduct P) (Real.exp (-Real.eulerMascheroniConstant)) (s+1/50)
    (Nat.cast_nonneg _) hPs.le hDr (Real.log_pos hP) (actual_primeProduct_pos P).le
    (Real.exp_pos _).le (by linarith) (by linarith) hCommon hNorm
  exact hCoeff.trans hResult

end ErdosStoppedArithmetic

end


namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  Erdos970.EulerWeightedLower ErdosUnitLifts
  NumberTheoryLean.ReferenceProductsBasics ErdosPrimeInputs.MertensStrong

attribute [local instance] Classical.propDecidable

def actualTagGood (P : ℝ) (r : ℚ) (q : ℕ) (a : ℕ → ℕ) (p : ℕ) (m : ℤ) : Prop :=
  (r.den : ℤ) ∣ r.num+(q : ℤ)*m*p ∧
    ∀ t ∈ smallPrimeSet P,
      (actualN r.den r.num ((q : ℤ)*m) p : ZMod t) ≠ (a t : ℤ)

theorem unaligned_subset_primesThrough (P : ℝ) (D : ℕ) (A : ℤ) (residue : ℕ → ℤ) :
    unalignedPrimes P D A residue ⊆ primesThrough P := by
  intro t ht
  obtain ⟨htp,htP⟩ := (mem_smallPrimeSet P t).mp (Finset.mem_filter.mp ht).1
  have hP0 : 0 ≤ P := (Nat.cast_nonneg t).trans htP.le
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Ioc.mpr ⟨htp.pos,(Nat.le_floor_iff hP0).mpr htP.le⟩,htp⟩

theorem actual_restricted_weight (P : ℝ) (D : ℕ) (A : ℤ) (residue : ℕ → ℤ) (d : ℕ) :
    paperWeight (unalignedPrimes P D A residue) d =
      eulerWeight (restrictedPrimes P D A residue d) := rfl

theorem actual_tag_filter (P R V : ℝ) (r : ℚ) (q : ℕ) (a : ℕ → ℕ) (m : ℤ) :
    (intervalPrimes R V 1 0).filter (fun p => actualTagGood P r q a p m) =
      actualSurvivorPrimes P R V r.den r.num ((q : ℤ)*m) (fun t => (a t : ℤ)) := by
  ext p
  simp only [actualTagGood,actualSurvivorPrimes,Finset.mem_filter,Int.cast_natCast]

theorem actual_tag_original_tests (P : ℝ) (r : ℚ) (q p : ℕ) (a : ℕ → ℕ) (m : ℤ)
    (h : actualTagGood P r q a p m) :
    (r.den : ℤ) ∣ r.num+((p*q : ℕ) : ℤ)*m ∧
      ∀ t ∈ smallPrimeSet P,
        ¬Int.ModEq (t : ℤ) ((r.num+((p*q : ℕ) : ℤ)*m)/(r.den : ℤ)) (a t : ℤ) := by
  have he : r.num+((p*q : ℕ) : ℤ)*m = r.num+(q : ℤ)*m*p := by push_cast;ring
  rw [he]
  refine ⟨h.1,?_⟩
  intro t ht hh
  exact h.2 t ht ((ZMod.intCast_eq_intCast_iff _ _ t).mpr hh)

theorem moving_subbin_actual_pair_lower (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → 0 < xi →
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P s x y R V : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      203/100 ≤ s → s ≤ 219/100 →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
      ∀ r : ℚ,(r.den : ℝ) ≤ w^Cs → ∀ q : ℕ,∀ a : ℕ → ℕ,
      (∀ t ∈ smallPrimeSet P,q.Coprime t) →
      (999/1000 : ℝ)*(r.den : ℝ)*P^s ≤ y-x →
      max |x| |y| ≤ 2*w^(Cs+2)*P^s →
      (39/100 : ℝ)*((intervalPrimes R V 1 0).card : ℝ)*P^s*primeProduct P ≤
        ((admissiblePairs (intervalPrimes R V 1 0)
          ((supportedIntegers (unalignedPrimes P r.den r.num (fun t => (a t : ℤ)))
            ⌊P^(95/100 : ℝ)⌋₊).biUnion (fun d => primeMultiplesIn d P x y))
          (actualTagGood P r q a)).card : ℝ) := by
  obtain ⟨K,hK,hPair⟩ := moving_subbin_pair_lower Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho xi hrho hxi
  obtain ⟨wP,hwP,hP⟩ := hPair rho hrho
  obtain ⟨wT,_hwT,hT⟩ := tag_prime_sieve_lower Cs K rho xi (1/20) hCs hK hrho hxi (by norm_num)
  refine ⟨max wP wT,hwP.trans (le_max_left _ _),?_⟩
  intro w hw P s x y R V hPl hPu hs hsU hR hVlo hVhi r hD q a hq hLength hHeight
  apply hP w ((le_max_left _ _).trans hw) P s x y hPl hPu hs hsU r.den r.den_pos
    hLength hHeight _ _ _ (unaligned_subset_primesThrough P r.den r.num _)
  intro d hd m hm
  have hd' := Finset.mem_filter.mp hd
  obtain ⟨ell,hell,hellP,hAbs⟩ := prime_multiple_natAbs d P x y m hm
  have hh := hT w P R V ((le_max_right _ _).trans hw) hPl hPu hR hVlo hVhi
    r.den r.den_pos hD r.num r.reduced (fun t => (a t : ℤ)) q d ell m hq
    (Finset.mem_Icc.mp hd'.1).1 hd'.2 hell hellP hAbs
  rw [actual_tag_filter,actual_restricted_weight]
  convert hh using 1
  ring

end ErdosStoppedArithmetic


end Erdos970

end OAI
