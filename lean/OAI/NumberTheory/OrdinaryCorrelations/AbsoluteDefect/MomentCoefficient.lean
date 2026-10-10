import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicCofactorMellin
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicCoefficientEnergy
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeWindow
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Surviving
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.HalfLeLogTwo

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryNarrowGrid OrdinaryDirichletMeanSquare
open OrdinarySparseLargeValues OrdinaryExponentialBudgets Finset
attribute [local irreducible] E F mesh binQ binStart binWidth binLog amplifier

noncomputable def momentCoefficient : ℝ := 12*Real.exp (1+1/4)*gaussianConstant+10

lemma momentCoefficient_nonneg : 0≤ momentCoefficient := by
  unfold momentCoefficient gaussianConstant
  positivity

lemma bin_dyadic {q r R : ℕ} (hq : 0<q) {i : ℕ×ℕ} (hi : i∈grid q r R) :
    primeBin i⊆Ioc (lower i) (2*lower i) := by
  intro p hp
  rcases mem_filter.mp hp with ⟨hp,hprime⟩
  refine mem_Ioc.mpr ⟨(mem_Ioc.mp hp).1,(mem_Ioc.mp hp).2.trans ?_⟩
  have hij : q ≤ i.2 := (mem_Ico.mp (mem_product.mp hi).2).1
  unfold lower upper
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (2^i.1) (show i.2+1≤2*i.2 by omega)

theorem terminal_bin_sparse {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) {B H s j R Kr K X : ℕ}
    (hR : 0<R) (hH : 16*R≤2^H) (hKr : 64*R≤2^Kr)
    (hK : 16*(R:ℝ)*(1+momentCoefficient)≤(2:ℝ)^K)
    (hB : H+4*s+2*Kr+K+70≤B)
    (hX : (2^(F B s j))^(64*R)≤X)
    (hnext : X<(2^(F B s (j+1)))^(64*R))
    {i : ℕ×ℕ} (hi : i∈grid (binQ B H s j) (binStart B H s j) (binWidth B s j))
    (S : Finset ℝ) (hsep : (S : Set ℝ).Pairwise (fun t u=>1≤|t-u|))
    (hheight : ∀t∈S,|t|≤(X:ℝ)) :
    (S.filter (fun t => threshold H j (binLog B H s j i)<‖primeMellin f χ (primeBin i) t‖)).card^R≤X := by
  classical
  let T := S.filter (fun t => threshold H j (binLog B H s j i)<‖primeMellin f χ (primeBin i) t‖)
  let N := lower i
  let k := Nat.log (2*N) X
  have hB0 : H+10≤B := by omega
  have hrange := bin_log_range (B:=B) (H:=H) (s:=s) (j:=j) hB0 hi
  have hbnds := bin_lower_bounds (B:=B) (H:=H) (s:=s) (j:=j) hi
  have hEp := E_pos B s j
  have hN : 2^(E B s j)≤N := (Nat.pow_le_pow_right (by omega) hrange.1).trans hbnds.1
  have hN2 : 2≤N := (show 2≤2^(E B s j) from
    (by simpa using Nat.pow_le_pow_right (by omega : 1≤(2:ℕ)) (by omega : 1≤E B s j))).trans hN
  have hF2 : 2≤2^(F B s j) := by
    simpa using Nat.pow_le_pow_right (by omega : 1≤(2:ℕ)) (show 1≤F B s j from F_pos B s j)
  have hNQ : N≤2^(F B s j) := by
    exact (lower_le_upper i).trans (hbnds.2.trans (Nat.pow_le_pow_right (by omega) (by omega)))
  have hXp : 0<X := lt_of_lt_of_le (by positivity : 0<(2^(F B s j))^(64*R)) hX
  have hk : 4*R≤k := terminal_moment_lower hR hF2 (by omega) hNQ hX
  have hk' : k<64*R*2^(3*j+2*s+22) := terminal_moment_upper hXp hN hnext
  have hlo : (2*(N:ℝ))^k≤(X:ℝ) := by exact_mod_cast Nat.pow_log_le_self (2*N) hXp.ne'
  have hup : (X:ℝ)≤(2*(N:ℝ))^(k+1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by omega : 1<2*N) X).le
  have hm : momentBase k≤Real.exp (momentCoefficient*((k:ℝ)+1)^2) := by
    exact moment_weight_bound (by unfold gaussianConstant; positivity) k
  have hsize := terminal_moment_size (by linarith only [momentBase_one_le k]) hm hK hB hKr hk' hN
  have hthreshold := threshold_moment (j:=j) hH hbnds.1
  have hh := dyadic_prime_large_values_sparse hN2 (by exact_mod_cast hXp)
    (threshold_pos H j (binLog B H s j i)) hR hk hlo hup hsize hthreshold (primeBin i)
    (fun p hp => (mem_filter.mp hp).2) (bin_dyadic (by unfold binQ; positivity) hi)
    (fun p => characterModulation f χ p/(p:ℂ)) (fun p hp => prime_coefficient_norm hf χ p)
    T (fun t ht => hheight t (mem_filter.mp ht).1)
    (hsep.mono (by exact_mod_cast (filter_subset _ _ : T⊆S)))
    (fun t ht => (mem_filter.mp ht).2.le)
  exact_mod_cast hh

open OrdinaryFrequencyChain

theorem terminal_bad_sparse {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) {B H s j r Kr K X : ℕ}
    (hr : 0<r) (hH : 16*(4*r)≤2^H) (hKr : 64*(4*r)≤2^Kr)
    (hK : 16*((4*r:ℕ):ℝ)*(1+momentCoefficient)≤(2:ℝ)^K)
    (hB : H+4*s+2*Kr+K+70≤B) (hB' : 2*H+s+30≤B)
    (hX : (2^(F B s j))^(64*(4*r))≤X)
    (hnext : X<(2^(F B s (j+1)))^(64*(4*r)))
    (S : Finset ℝ) (hsep : (S : Set ℝ).Pairwise (fun t u=>1≤|t-u|))
    (hheight : ∀t∈S,|t|≤(X:ℝ)) :
    (S.filter (fun t => ¬∀i∈grid (binQ B H s j) (binStart B H s j) (binWidth B s j),
      ‖primeMellin f χ (primeBin i) t‖≤threshold H j (binLog B H s j i))).card^(2*r)≤X := by
  classical
  let I := grid (binQ B H s j) (binStart B H s j) (binWidth B s j)
  let T := fun i => S.filter (fun t => threshold H j (binLog B H s j i)<‖primeMellin f χ (primeBin i) t‖)
  have hh := sparse_union I T X (2*r) (by omega)
    (by simpa only [show 2*(2*r)=4*r by omega] using terminal_grid_card (R:=4*r) hB' hX)
    (fun i hi => by
      simpa only [show 2*(2*r)=4*r by omega] using
        terminal_bin_sparse hf χ (by omega : 0<4*r) hH hKr hK hB hX hnext hi S hsep hheight)
  apply le_trans (Nat.pow_le_pow_left (card_le_card ?_) _) hh
  intro t ht
  rcases mem_filter.mp ht with ⟨ht,hn⟩
  push Not at hn
  obtain ⟨i,hi,hbad⟩ := hn
  exact mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨ht,hbad⟩⟩

end OrdinaryChainScales

end

end OAI
