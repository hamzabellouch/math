import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ArithmeticTangentBasis
import OAI.GroupTheory.SimpleAmenable.Homology.WindowEnclosureChains

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section UniformPropagationBounds

theorem conjugate_eq_label (z : CutRing) :
    conjugate z = ordinary z - (endpointLabel z : ℝ) * Real.sqrt 5 := by
  have h := (eq_div_iff (by positivity : Real.sqrt 5 ≠ 0)).mp (endpointLabel_embedding z)
  linarith

theorem contracted_transverse_label (l : CutRing) (hl : |conjugate l| < 1/1000)
    {C : ℝ} (_hC : 0 ≤ C) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ d : CutRing,
      |(endpointLabel d : ℝ)| ≤ 6*(n:ℝ)/5 →
      |ordinary d| ≤ 2*C/(n:ℝ) → |(endpointLabel (l*d) : ℝ)| < (n:ℝ)/10 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 100 (2*C*|(endpointLabel l : ℝ)|))
  have hNpos : 1 ≤ N := by
    have : (100:ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
    exact_mod_cast (by linarith : (1:ℝ) ≤ N)
  refine ⟨N,hNpos,fun n hn d hd hd' => ?_⟩
  have hnr : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hn100 : (100:ℝ) < n := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hN) hnr
  have hn0 : (0:ℝ) < n := by linarith
  have hsmall : |(endpointLabel l : ℝ)| * (2*C/(n:ℝ)) < 1 := by
    rw [← mul_div_assoc,div_lt_one hn0]
    nlinarith [lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hnr]
  have hb := endpointLabel_mul_bound l d hd hd'
  have hc : |conjugate l| *(6*(n:ℝ)/5) < (1/1000)*(6*(n:ℝ)/5) :=
    mul_lt_mul_of_pos_right hl (by positivity)
  linarith

theorem tangent_displacement_embeddings (d : CutRing) {A B : ℝ}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (n : ℕ) (hn : 1 ≤ n)
    (hd : |ordinary d| ≤ A/(n:ℝ))
    (hq : |(endpointLabel d : ℝ)| ≤ B*(n:ℝ)) :
    |ordinary d| + |conjugate d| ≤ (2*A+3*B)*(n:ℝ) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hdn : |ordinary d| ≤ A*(n:ℝ) := by
    calc
      _ ≤ A/(n:ℝ) := hd
      _ ≤ A := div_le_self hA hn1
      _ ≤ A*(n:ℝ) := le_mul_of_one_le_right hA hn1
  have hs : Real.sqrt 5 ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hc : |conjugate d| ≤ A*(n:ℝ)+3*B*(n:ℝ) := by
    rw [conjugate_eq_label]
    calc
      _ ≤ |ordinary d| + |(endpointLabel d : ℝ) * Real.sqrt 5| := abs_sub _ _
      _ = |ordinary d| + |(endpointLabel d : ℝ)| * Real.sqrt 5 := by
        rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg 5)]
      _ ≤ A*(n:ℝ) + (B*(n:ℝ))*3 := by gcongr
      _ = _ := by ring
  linarith

theorem tangent_chain_uniform (l u v : CutRing) (huv : u*v = 1)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ d : CutRing,
      |ordinary d| ≤ A/(n:ℝ) → |(endpointLabel d : ℝ)| ≤ B*(n:ℝ) →
      ∃ w : List CutRing,
        w.sum = d ∧
        (∀ e ∈ w, e = u ∨ e = -u ∨ e = cutTau*u ∨ e = -(cutTau*u)) ∧
        (w.length : ℝ) ≤ K*(n:ℝ) ∧
        (∀ k : ℕ, |ordinary (w.take k).sum| ≤
          A/(n:ℝ)+(|ordinary u|+|ordinary (cutTau*u)|)) ∧
        ∀ k : ℕ, |(endpointLabel (w.take k).sum : ℝ)| +
          |(endpointLabel (l*(w.take k).sum) : ℝ)| ≤ K*(n:ℝ) := by
  let M := 4*(|ordinary v|+|conjugate v|+1)
  let L := M*(2*A+3*B)
  let H := |(endpointLabel u : ℝ)|+|(endpointLabel (cutTau*u) : ℝ)|
  let σ := |ordinary u|+|ordinary (cutTau*u)|
  let J := L*H + |conjugate l| *(L*H) + |(endpointLabel l : ℝ)| *(A+σ)
  let K := L+J+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hL : 0 ≤ L := mul_nonneg hM (by positivity)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨K,by dsimp [K]; positivity,fun n hn d hd hq => ?_⟩
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by positivity
  have he := tangent_displacement_embeddings d hA hB n hn hd hq
  obtain ⟨w,hw,hm,hlen,hwalk,hlab⟩ := tangent_chain u v huv d
  have hsize : M*(|ordinary d|+|conjugate d|) ≤ L*(n:ℝ) := by
    calc
      _ ≤ M*((2*A+3*B)*(n:ℝ)) := mul_le_mul_of_nonneg_left he hM
      _ = _ := by dsimp [L]; ring
  have hkL : L ≤ K := by dsimp [K]; linarith
  have hkJ : J ≤ K := by dsimp [K]; linarith
  have ho : ∀ k : ℕ, |ordinary (w.take k).sum| ≤ A/(n:ℝ)+σ := by
    intro k
    have hb := hwalk k
    have hleft : -|ordinary d| ≤ min 0 (ordinary d) :=
      le_min (by linarith [abs_nonneg (ordinary d)]) (neg_abs_le _)
    have hright : max 0 (ordinary d) ≤ |ordinary d| :=
      max_le (abs_nonneg _) (le_abs_self _)
    apply abs_le.mpr
    constructor <;> linarith [hd]
  refine ⟨w,hw,hm,(hlen.trans hsize).trans (mul_le_mul_of_nonneg_right hkL hn0),ho,?_⟩
  intro k
  have hx : |(endpointLabel (w.take k).sum : ℝ)| ≤ (L*H)*(n:ℝ) := by
    calc
      _ ≤ (M*(|ordinary d|+|conjugate d|))*H := hlab k
      _ ≤ (L*(n:ℝ))*H := mul_le_mul_of_nonneg_right hsize hH
      _ = _ := by ring
  have ho' : |ordinary (w.take k).sum| ≤ (A+σ)*(n:ℝ) := by
    calc
      _ ≤ A/(n:ℝ)+σ := ho k
      _ ≤ A+σ := add_le_add (div_le_self hA hn1) le_rfl
      _ ≤ (A+σ)*(n:ℝ) := le_mul_of_one_le_right (add_nonneg hA hσ) hn1
  have hy := endpointLabel_mul_bound l (w.take k).sum hx ho'
  calc
    _ ≤ (L*H)*(n:ℝ) +
        (|conjugate l| *((L*H)*(n:ℝ)) + |(endpointLabel l : ℝ)| *((A+σ)*(n:ℝ))) :=
      add_le_add hx hy
    _ = J*(n:ℝ) := by dsimp [J]; ring
    _ ≤ K*(n:ℝ) := mul_le_mul_of_nonneg_right hkJ hn0

end UniformPropagationBounds

section OldWindowBridgeGeometry

theorem short_window_scale (n : ℕ) (hn : 160 ≤ n) :
    1 ≤ n/8 ∧ 1 ≤ (n/8)/2 ∧ (n:ℝ)/9 ≤ (n/8:ℕ) ∧
      (n:ℝ)/20 ≤ ((n/8)/2:ℕ) ∧
      (n/8:ℕ) + ((n/8)/2:ℕ) ≤ n/4 := by
  have h₁ := Nat.mod_add_div n 8
  have h₂ := Nat.mod_lt n (by norm_num : 0 < 8)
  have h₃ := Nat.mod_add_div (n/8) 2
  have h₄ := Nat.mod_lt (n/8) (by norm_num : 0 < 2)
  have h₅ := Nat.mod_add_div n 4
  have h₆ := Nat.mod_lt n (by norm_num : 0 < 4)
  have ha : n ≤ 9*(n/8) := by omega
  have hb : n ≤ 20*((n/8)/2) := by omega
  refine ⟨by omega,by omega,?_,?_,by omega⟩
  · have : (n:ℝ) ≤ 9*(n/8:ℕ) := by exact_mod_cast ha
    linarith
  · have : (n:ℝ) ≤ 20*((n/8)/2:ℕ) := by exact_mod_cast hb
    linarith

theorem short_window_path {K : ℝ} (_hK : 0 ≤ K) (n : ℕ) (hn : 160 ≤ n)
    (p q : ℤ) (hpq : ((q-p).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) :
    ∃ T : ℕ, ∃ w : ℕ → ℤ,
      w 0 = p ∧ w T = q ∧ (T:ℝ) ≤ 20*(K+2) ∧
      (∀ i, |w (i+1)-w i| ≤ (((n/8)/2:ℕ):ℤ)) ∧
      ∀ i, min p q ≤ w i ∧ w i ≤ max p q := by
  obtain ⟨_,hS,_,hSn,_⟩ := short_window_scale n hn
  obtain ⟨T,w,h₀,hT,hbound,hstep,hrange⟩ := integer_window_path p q ((n/8)/2) hS
  refine ⟨T,w,h₀,hT,?_,hstep,hrange⟩
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hS0 : (0:ℝ) < ((n/8)/2:ℕ) := by exact_mod_cast hS
  have hdiv : (((q-p).natAbs / ((n/8)/2):ℕ):ℝ) ≤ 20*(K+1) := by
    have hmul : (((q-p).natAbs / ((n/8)/2):ℕ):ℝ) * ((n/8)/2:ℕ) ≤
        ((q-p).natAbs:ℝ) := by exact_mod_cast Nat.div_mul_le_self (q-p).natAbs ((n/8)/2)
    have hfloor : (0:ℝ) ≤ (((q-p).natAbs / ((n/8)/2):ℕ):ℝ) := by positivity
    nlinarith
  have hb : (T:ℝ) ≤ (((q-p).natAbs / ((n/8)/2):ℕ):ℝ)+1 := by exact_mod_cast hbound
  linarith

theorem old_window_bridge_geometry {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (B : ℕ) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ p q : ℤ,
      ((q-p).natAbs:ℝ) ≤ (K+1)*(n:ℝ) → ∀ a b : ℝ, a ≤ b →
      ∃ T : ℕ, ∃ w : ℕ → ℤ, ∃ u v : ℕ → CutRing,
        w 0 = p ∧ w T = q ∧ (T:ℝ) ≤ 20*(K+2) ∧
        (∀ i, (w i ≤ endpointLabel (u i) ∧ endpointLabel (u i) < w i+(n/8:ℕ)) ∧
          (w i ≤ endpointLabel (v i) ∧ endpointLabel (v i) < w i+(n/8:ℕ))) ∧
        (∀ i, |w (i+1)-w i| + (n/8:ℕ) + (2*B:ℕ) < (n:ℤ)) ∧
        (∀ i, Set.Icc a b ⊆ Set.Ioo (ordinary (u i)) (ordinary (v i))) ∧
        (∀ i, Set.Icc (ordinary (u i)) (ordinary (v i)) ⊆
          Set.Ioo (ordinary (u (i+1))) (ordinary (v (i+1)))) ∧
        ∀ i, i ≤ T → Set.Icc (ordinary (u i)) (ordinary (v i)) ⊆
          Set.Ioo (a-δ) (b+δ) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 160 (max (40*(B:ℝ))
    ((20*(K+2)+1)*201*9/δ)))
  have hN160 : 160 ≤ N := by
    have : (160:ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
    exact_mod_cast (le_of_lt this)
  refine ⟨N,hN160,fun n hn p q hpq a b hab => ?_⟩
  have hn160 : 160 ≤ n := hN160.trans hn
  have hnr : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnB : 40*(B:ℝ) < n := lt_of_lt_of_le
    (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hN) hnr
  have hnδ : (20*(K+2)+1)*201*9/δ < (n:ℝ) := lt_of_lt_of_le
    (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hN) hnr
  obtain ⟨hL,_,hLn,_,hLS⟩ := short_window_scale n hn160
  obtain ⟨T,w,h₀,hT,hbound,hstep,hrange⟩ := short_window_path hK n hn160 p q hpq
  obtain ⟨u,v,hlabel,hinc,hnest,herror⟩ := window_enclosure_chain (n/8) hL w a b hab
  refine ⟨T,w,u,v,h₀,hT,hbound,hlabel,?_,hinc,hnest,?_⟩
  · intro i
    have hBn : 40*B < n := by exact_mod_cast hnB
    have hspan : (n/8)+((n/8)/2)+2*B < n := by omega
    have hspan' : ((n/8:ℕ):ℤ)+(((n/8)/2:ℕ):ℤ)+(2*B:ℕ) < (n:ℤ) := by exact_mod_cast hspan
    linarith [hstep i]
  · intro i hi x hx
    have hiT : (i:ℝ) ≤ T := by exact_mod_cast hi
    have hL0 : (0:ℝ) < (n/8:ℕ) := by exact_mod_cast hL
    have hb₀ : 0 ≤ 20*(K+2)+1 := by linarith
    have he : ((i:ℝ)+1)*201/(n/8:ℕ) < δ := by
      apply (div_lt_iff₀ hL0).mpr
      have hd : (20*(K+2)+1)*201*9 < (n:ℝ)*δ := (div_lt_iff₀ hδ).mp hnδ
      nlinarith
    exact ⟨by linarith [(herror i).1,hx.1],by linarith [(herror i).2,hx.2]⟩

end OldWindowBridgeGeometry

end SimpleAmenable
end
end

end OAI
