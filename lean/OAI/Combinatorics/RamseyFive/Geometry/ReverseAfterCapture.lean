import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OptionComposition
import OAI.Combinatorics.RamseyFive.Geometry.TwoPublicCaps
import OAI.Combinatorics.RamseyFive.Entropy.TwoCapCost

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem reverse_after_capture {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (M ε : ℝ) (p : Law (Option (Finset (ℙ K (Dual K V)))))
    (hp : p none≤ε) (hgood : ∀W,0<p (some W)→ValidCap T UT M W)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences S T≤(9:ℝ)/10*S.card*T.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card)≤n) :
    let MA := (320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^(d+1)/T.card
    let next := nextCapLaw S U T UT hT n (Nat.card K) MA M
    let out := optionCompose p next
    out none≤ε+Real.exp (-(Nat.card K:ℝ)) ∧
    (∀Z,0<out (some Z)→ValidCap S U MA Z) := by
  dsimp only
  let MA := (320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^(d+1)/T.card
  let next := nextCapLaw S U T UT hT n (Nat.card K) MA M
  have hnext (W) (hW : 0<p (some W)) : next (some W) none≤Real.exp (-(Nat.card K:ℝ)) := by
    have hv := hgood W hW
    dsimp only [next,nextCapLaw]
    rw [dite_eq_left hv]
    apply publicCapLaw_failure _ _ _ _ _ (hv.source_nonempty hT) _ Finset.inter_subset_right
    exact geometric_validation_mass hdim hd hq S U hS hSU T (T∩W)
      (hv.source_nonempty hT) Finset.inter_subset_left ((9:ℝ)/10)
      (by norm_num) (by norm_num) hv.2.2 hsparse n hn hlen
  refine ⟨optionCompose_failure p next ε _ (Real.exp_pos _).le hp hnext,?_⟩
  intro Z hZ
  obtain ⟨W,hW,hWZ⟩ := optionCompose_positive p next Z hZ
  have hv := hgood W hW
  dsimp only [next,nextCapLaw] at hWZ
  rw [dite_eq_left hv] at hWZ
  exact publicCapLaw_positive _ _ _ _ _ _ _ _ _ _ hWZ

lemma source_product_to_cap (Q s t b C : ℝ) (hs : 0 ≤ s) (ht : 0<t) (hC : 0≤C)
    (hp : Q*Real.exp (-b)≤ s*t) : C*Q/t≤ s*(C*Real.exp b) := by
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos b).le
  have he : Real.exp (-b)*Real.exp b=1 := by rw [←Real.exp_add];simp
  have hq : Q≤ s*t*Real.exp b := by simpa only [mul_assoc,he,mul_one] using hh
  apply (div_le_iff₀ ht).mpr
  have hmul := mul_le_mul hq (le_refl C) hC
    (mul_nonneg (mul_nonneg hs ht.le) (Real.exp_pos b).le)
  nlinarith only [hmul]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma reverse_capture_cost (T UT W : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P : ℝ) (hv : ValidCap T UT ((T.card:ℝ)*Real.exp P) W) (q : ℝ) (hq : 1≤q) (n : ℕ) :
    Real.log (uniformCutoff q (T∩W) W n)≤Real.log (2*q)-Real.log ((9:ℝ)/10)+
      (n:ℝ)*(P-Real.log ((9:ℝ)/10)) := by
  have hC := hv.source_nonempty hT
  have hW := hC.mono Finset.inter_subset_right
  have hu := uniformCutoff_log q hq (T∩W) W hC hW Finset.inter_subset_right n
  have hr := capture_log_ratio T.card ((9:ℝ)/10) W.card (T∩W).card P
    (by exact_mod_cast hT.card_pos) (by norm_num) (by exact_mod_cast hW.card_pos)
    (by exact_mod_cast hC.card_pos) hv.2.2 hv.2.1
  have hm := mul_le_mul_of_nonneg_left hr (show (0:ℝ)≤n by positivity)
  linarith

end SharpRamseyFive.ProjectiveIncidence

end OAI
