import OAI.NumberTheory.Ostmann.Characters.RichShellSelectionTree

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters

theorem harmonic_density_increment (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ M h : ℕ, 2 ≤ M ∧ ∃ c₁ Kmin : ℝ, 0 < c₁ ∧ 0 < Kmin ∧
      ∀ (K0 : ℕ), Kmin ≤ (K0:ℝ) → ∀ (E : Finset ℕ), (∀ p ∈ E, p.Prime) →
      ∀ a : ℝ, 0 ≤ a →
      d*(5*(K0:ℝ)*(M:ℝ)^h) ≤ harmonicIntervalMass E a (a+5*(K0:ℝ)*(M:ℝ)^h) →
      ∃ j : ℕ, j ≤ h ∧ ∃ U : ℝ, a ≤ U ∧ U+5*((K0*M^j:ℕ):ℝ) ≤ a+5*(K0:ℝ)*(M:ℝ)^h ∧
        ∀ v : ℝ, U ≤ v → v+ε*((K0*M^j:ℕ):ℝ) ≤ U+5*((K0*M^j:ℕ):ℝ) →
          c₁*ε*((K0*M^j:ℕ):ℝ) ≤ harmonicIntervalMass E v (v+ε*((K0*M^j:ℕ):ℝ)) := by
  obtain ⟨C,hC,hcap⟩ := harmonicIntervalMass_mertens
  obtain ⟨M,hM⟩ := exists_nat_gt (max 2 (10/ε))
  have hM2 : 2 ≤ M := by have := (le_max_left _ _).trans_lt hM; exact_mod_cast this.le
  have hMpos : 0 < M := by omega
  have hMr : (0:ℝ)<M := by exact_mod_cast hMpos
  have hwide : 10 < ε*(M:ℝ) := by
    have := (le_max_right _ _).trans_lt hM
    exact (div_lt_iff₀ hε).mp this |>.trans_eq (mul_comm _ _)
  let η : ℝ := d/(2*(M:ℝ))
  have hη : 0 < η := div_pos hd (by positivity)
  have hbudget : 2*(M:ℝ)*η = d := by dsimp [η]; field_simp
  obtain ⟨h,hh⟩ := exists_nat_gt (2/η)
  have hdepth : 2 < d+((h+1:ℕ):ℝ)*η := by
    have := (div_lt_iff₀ hη).mp hh
    push_cast
    nlinarith
  let c₁ : ℝ := 5*d/(2*(M:ℝ)*ε)
  have hc₁ : 0 < c₁ := div_pos (by positivity) (by positivity)
  refine ⟨M,h,hM2,c₁,C*(M:ℝ)+1,hc₁,by positivity,?_⟩
  intro K0 hK E hE a ha hmass
  have hK0 : (0:ℝ)<K0 := by nlinarith
  let W : ℝ := 5*(K0:ℝ)*(M:ℝ)^h
  have hW : 0 < W := by dsimp [W]; positivity
  have hmin : C*(M:ℝ)^(h+1) ≤ W := by
    dsimp [W]
    rw [pow_succ]
    nlinarith [pow_pos hMr h]
  let f : List (Fin M) → ℝ := fun w =>
    harmonicIntervalMass E (shellTreeLeft M a W w)
      (shellTreeLeft M a W w+shellTreeWidth M W w) / shellTreeWidth M W w
  have hfroot : d ≤ f [] := by
    dsimp only [f,shellTreeLeft]
    rw [shellTreeWidth_nil]
    exact (le_div_iff₀ hW).mpr hmass
  have hfsum (w : List (Fin M)) (_ : w.length ≤ h) : ∑ i, f (i::w) = (M:ℝ)*f w :=
    harmonic_density_children hMpos E a W hW w
  have hfbound (w : List (Fin M)) (hw : w.length ≤ h+1) : f w ≤ 2 := by
    have hb := shellTree_bounds hMpos a W hW w
    have hp := shellTreeWidth_pos hMpos hW w
    have hm := shellTreeWidth_ge (by omega : 1 ≤ M) W C hC.le hmin w hw
    have hx := hcap E hE (shellTreeLeft M a W w)
      (shellTreeLeft M a W w+shellTreeWidth M W w) (ha.trans hb.1) (by linarith)
    change harmonicIntervalMass E _ _ / shellTreeWidth M W w ≤ 2
    apply (div_le_iff₀ hp).mpr
    linarith
  obtain ⟨w,hw,hdw,hchildren⟩ := density_tree_good_node M h f d η 2 hd hη.le
    hbudget.le hdepth hfroot hfsum hfbound
  let j := h-w.length
  have hj : j ≤ h := Nat.sub_le _ _
  have hwidth : shellTreeWidth M W w = 5*((K0*M^j:ℕ):ℝ) := by
    have he : h = w.length+j := by dsimp [j]; omega
    unfold shellTreeWidth W
    rw [he,pow_add]
    simp only [Nat.cast_mul,Nat.cast_pow]
    field_simp
  let U := shellTreeLeft M a W w
  have hb := shellTree_bounds hMpos a W hW w
  refine ⟨j,hj,U,hb.1,by rw [← hwidth]; exact hb.2,?_⟩
  intro v hv hvend
  let k : ℝ := ((K0*M^j:ℕ):ℝ)
  have hk : 0 < k := by
    dsimp only [k]
    rw [Nat.cast_mul,Nat.cast_pow]
    exact mul_pos hK0 (pow_pos hMr j)
  let r : ℝ := 5*k/(M:ℝ)
  have hr : 0 < r := div_pos (by positivity) hMr
  have hMrid : (M:ℝ)*r = 5*k := by dsimp [r]; field_simp
  have htwo : v+2*r ≤ v+ε*k := by
    have hrb : 2*r ≤ ε*k := by
      calc
        2*r = 10*k/(M:ℝ) := by dsimp [r]; ring
        _ ≤ ε*k := (div_le_iff₀ hMr).mpr (by nlinarith)
    linarith
  obtain ⟨i,hi,hvi,hiv⟩ := exists_whole_grid_cell M U r v (v+ε*k) hr hv htwo
    (by rw [hMrid]; exact hvend)
  have hh := hchildren ⟨i,hi⟩
  have hcw : shellTreeWidth M W (⟨i,hi⟩::w) = r := by
    rw [shellTreeWidth_cons,hwidth]
  have hcl : shellTreeLeft M a W (⟨i,hi⟩::w) = U+(i:ℝ)*r := by
    simp only [shellTreeLeft,hwidth]
    rfl
  change d/2 ≤ harmonicIntervalMass E _ _ / shellTreeWidth M W (⟨i,hi⟩::w) at hh
  rw [hcw,hcl] at hh
  have hlow := (le_div_iff₀ hr).mp hh
  have he : U+(i:ℝ)*r+r = U+((i:ℝ)+1)*r := by ring
  rw [he] at hlow
  calc
    c₁*ε*k = (d/2)*r := by dsimp [c₁,r]; field_simp
    _ ≤ harmonicIntervalMass E (U+(i:ℝ)*r) (U+((i:ℝ)+1)*r) := hlow
    _ ≤ harmonicIntervalMass E v (v+ε*k) := harmonicIntervalMass_mono E hvi hiv

end Ostmann.Characters

end

end OAI
