import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.LatticeCounting

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section WindowEnclosureGeometry

theorem coordinate_window_brackets (n : ℕ) (hn : 1 ≤ n) (q : ℤ) (t : ℝ) :
    ∃ u v : CutRing,
      (q ≤ endpointLabel u ∧ endpointLabel u < q+n) ∧
      (q ≤ endpointLabel v ∧ endpointLabel v < q+n) ∧
      t-201/(n:ℝ) ≤ ordinary u ∧ ordinary u < t ∧
      t < ordinary v ∧ ordinary v ≤ t+201/(n:ℝ) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨u,hu₁,hu₂,hu⟩ := coordinate_window_net n hn q (t-101/(n:ℝ))
  obtain ⟨v,hv₁,hv₂,hv⟩ := coordinate_window_net n hn q (t+101/(n:ℝ))
  have hpos : 0 < 1/(n:ℝ) := div_pos zero_lt_one hn'
  rcases abs_le.mp hu with ⟨huL,huR⟩
  rcases abs_le.mp hv with ⟨hvL,hvR⟩
  refine ⟨u,v,⟨hu₁,hu₂⟩,⟨hv₁,hv₂⟩,?_,?_,?_,?_⟩ <;>
    simp only [div_eq_mul_inv,one_mul] at * <;> linarith

theorem coordinate_window_enclosure (n : ℕ) (hn : 1 ≤ n) (q : ℤ) (a b : ℝ)
    (hab : a ≤ b) :
    ∃ u v : CutRing,
      (q ≤ endpointLabel u ∧ endpointLabel u < q+n) ∧
      (q ≤ endpointLabel v ∧ endpointLabel v < q+n) ∧
      Set.Icc a b ⊆ Set.Ioo (ordinary u) (ordinary v) ∧
      a-201/(n:ℝ) ≤ ordinary u ∧ ordinary u < ordinary v ∧
      ordinary v ≤ b+201/(n:ℝ) := by
  obtain ⟨u,_,hu,_,huL,huR,_,_⟩ := coordinate_window_brackets n hn q a
  obtain ⟨_,v,_,hv,_,_,hvL,hvR⟩ := coordinate_window_brackets n hn q b
  refine ⟨u,v,hu,hv,?_,huL,lt_trans huR (lt_of_le_of_lt hab hvL),hvR⟩
  intro x hx
  exact ⟨lt_of_lt_of_le huR hx.1,lt_of_le_of_lt hx.2 hvL⟩

theorem integer_window_path (p q : ℤ) (S : ℕ) (hS : 1 ≤ S) :
    ∃ T : ℕ, ∃ w : ℕ → ℤ,
      w 0 = p ∧ w T = q ∧
      T ≤ (q-p).natAbs / S + 1 ∧
      (∀ i, |w (i+1)-w i| ≤ (S:ℤ)) ∧
      ∀ i, min p q ≤ w i ∧ w i ≤ max p q := by
  suffices h : ∀ p q : ℤ, p ≤ q →
      ∃ T : ℕ, ∃ w : ℕ → ℤ,
        w 0 = p ∧ w T = q ∧ T ≤ (q-p).natAbs / S + 1 ∧
        (∀ i, |w (i+1)-w i| ≤ (S:ℤ)) ∧
        ∀ i, p ≤ w i ∧ w i ≤ q by
    by_cases hpq : p ≤ q
    · obtain ⟨T,w,h₀,hT,hb,hs,hw⟩ := h p q hpq
      exact ⟨T,w,h₀,hT,hb,hs,fun i => by simpa [hpq] using hw i⟩
    · have hqp : q ≤ p := le_of_not_ge hpq
      obtain ⟨T,w,h₀,hT,hb,hs,hw⟩ := h (-p) (-q) (by omega)
      refine ⟨T,fun i => -w i,by simp [h₀],by simp [hT],?_,?_,?_⟩
      · have he : -q - -p = -(q-p) := by ring
        rw [he,Int.natAbs_neg] at hb
        exact hb
      · intro i
        simpa only [neg_sub_neg,abs_sub_comm] using hs i
      · intro i
        simp only [min_eq_right hqp,max_eq_left hqp]
        constructor <;> linarith [(hw i).1,(hw i).2]
  intro p q hpq
  let D := (q-p).toNat
  have hD : (D:ℤ) = q-p := Int.toNat_of_nonneg (by omega)
  let T := D/S+1
  let w : ℕ → ℤ := fun i => p + (min (i*S) D : ℕ)
  have hTS : D ≤ T*S := by
    have hd : D/S*S ≤ D := Nat.div_mul_le_self D S
    have hr : D%S < S := Nat.mod_lt D (by omega)
    have he := Nat.mod_add_div D S
    rw [Nat.mul_comm S (D/S)] at he
    dsimp [T]
    rw [Nat.add_mul,Nat.one_mul]
    omega
  refine ⟨T,w,by simp [w],?_,?_,?_,?_⟩
  · simp only [w,Nat.min_eq_right hTS]
    omega
  · dsimp [T,D]
    have he : (q-p).toNat = (q-p).natAbs := by
      have ha := Int.natAbs_of_nonneg (show 0 ≤ q-p by omega)
      omega
    rw [he]
  · intro i
    have ha : min (i*S) D ≤ min ((i+1)*S) D :=
      min_le_min_right D (Nat.mul_le_mul_right S (by omega))
    have hb : min ((i+1)*S) D ≤ min (i*S) D + S := by
      by_cases hi : i*S ≤ D
      · rw [Nat.min_eq_left hi,Nat.add_mul,Nat.one_mul]
        exact min_le_left _ _
      · rw [Nat.min_eq_right (le_of_not_ge hi)]
        omega
    change |(p+(min ((i+1)*S) D : ℕ):ℤ) - (p+(min (i*S) D : ℕ))| ≤ S
    rw [add_sub_add_left_eq_sub,abs_of_nonneg (by exact sub_nonneg.mpr (by exact_mod_cast ha) :
      (0:ℤ) ≤ (min ((i+1)*S) D : ℕ) - (min (i*S) D : ℕ))]
    apply sub_le_iff_le_add.mpr
    have hb' : ((min ((i+1)*S) D : ℕ):ℤ) ≤ ((min (i*S) D : ℕ):ℤ) + (S:ℤ) := by
      exact_mod_cast hb
    simpa only [add_comm] using hb'
  · intro i
    dsimp [w]
    have hi := min_le_right (i*S) D
    constructor <;> omega

end WindowEnclosureGeometry

end SimpleAmenable
end
end

end OAI
