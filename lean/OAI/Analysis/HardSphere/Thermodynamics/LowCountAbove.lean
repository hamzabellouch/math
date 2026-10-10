import Mathlib
import OAI.Analysis.HardSphere.Orbitals.CenteredCell

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.CellOrbital
theorem scaled_joint_low_counts_above (Amin : ℝ) : ∃ α₀ ell D₀ Q : ℝ,
    Amin≤α₀ ∧ 0<α₀ ∧ 0<ell ∧ 0<D₀ ∧ 0<Q ∧
    ∀ (S : Type) [DecidableEq S] (n : ℕ) (L : Length) (D α : ℝ),
      2≤n → 1 ≤ L.val → D=(n:ℝ)/L.val^3 → D₀ ≤ D →
      α₀/2 ≤ α → α ≤ 2*α₀ →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ (c : S → Torus L), (∀ z v, z≠v → 1 ≤ dist (c z) (c v)) →
    ∀ A : Finset S, ‖(joint n L c (ell*D) A).onScalar g.1‖^2 ≤ (Q/D^2)^A.card := by
  obtain ⟨C,B,E,G,hC,hB,hE,hG,hjoint⟩ := joint_low_counts
  let b : ℝ := 1/(128*Real.sqrt 3)
  have hb : 0<b := by dsimp [b]; positivity
  let α₀ := max (max 1 Amin) (8*C*E/b)
  have hα₀ : 0<α₀ := zero_lt_one.trans_le ((le_max_left 1 Amin).trans (le_max_left _ _))
  have hCE : C*E ≤ b*α₀/8 := by
    have hh := (div_le_iff₀ hb).mp (le_max_right (max 1 Amin) (8*C*E/b))
    dsimp [α₀]
    nlinarith
  let ell := min 1 (b/(16*C*B))
  have hell : 0<ell := lt_min zero_lt_one (by positivity)
  have hCB : 16*C*B*ell ≤ b := by
    have hh := (le_div_iff₀ (by positivity : 0<16*C*B)).mp (min_le_right 1 (b/(16*C*B)))
    dsimp [ell]
    nlinarith
  let D₀ : ℝ := max (2/ell) (max (200*α₀) (max 1 (128*C*B*ell*α₀^3)))+1
  have hD₀ : 0<D₀ := by
    have hh : (2/ell) ≤ D₀-1 := by dsimp [D₀]; linarith [le_max_left (2/ell) (max (200*α₀) (max 1 (128*C*B*ell*α₀^3)))]
    have hh' : 0<2/ell := by positivity
    linarith
  let Q := 8*G/(ell^2*b*α₀)
  have hQ : 0<Q := by dsimp [Q]; positivity
  refine ⟨α₀,ell,D₀,Q,(le_max_right 1 Amin).trans (le_max_left _ _),hα₀,hell,hD₀,hQ,?_⟩
  intro S _ n L D α hn hL hDN hDD hαl hαu g hg c hc A
  have hD : 0<D := hD₀.trans_le hDD
  have hα : 0<α := (by positivity : 0<α₀/2).trans_le hαl
  have hD2 : 2/ell ≤ D := by
    have hh := le_max_left (2/ell) (max (200*α₀) (max 1 (128*C*B*ell*α₀^3)))
    dsimp [D₀] at hDD
    linarith
  have hDr : 200*α₀ ≤ D := by
    have hh := (le_max_left (200*α₀) (max 1 (128*C*B*ell*α₀^3))).trans
      (le_max_right (2/ell) (max (200*α₀) (max 1 (128*C*B*ell*α₀^3))))
    dsimp [D₀] at hDD
    linarith
  have hD1 : 1 ≤ D := by
    have hh := (le_max_left 1 (128*C*B*ell*α₀^3)).trans
      ((le_max_right (200*α₀) (max 1 (128*C*B*ell*α₀^3))).trans
        (le_max_right (2/ell) (max (200*α₀) (max 1 (128*C*B*ell*α₀^3)))))
    dsimp [D₀] at hDD
    linarith
  have hDS : 128*C*B*ell*α₀^3 ≤ D^2 := by
    have hh := (le_max_right 1 (128*C*B*ell*α₀^3)).trans
      ((le_max_right (200*α₀) (max 1 (128*C*B*ell*α₀^3))).trans
        (le_max_right (2/ell) (max (200*α₀) (max 1 (128*C*B*ell*α₀^3)))))
    dsimp [D₀] at hDD
    nlinarith
  have hh : 2 ≤ ell*D := by have ht := (div_le_iff₀ hell).mp hD2; nlinarith
  let k := ⌈2*(ell*D)⌉₊
  let m := ⌊ell*D⌋₊
  have hk : 2*(ell*D) ≤ (k:ℝ) := Nat.le_ceil _
  have hku : (k:ℝ) ≤ 2*(ell*D)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hmu : (m:ℝ) ≤ ell*D := Nat.floor_le (by positivity)
  have hml : ell*D/2 ≤ (m:ℝ) := by
    have ht := Nat.lt_floor_add_one (ell*D)
    dsimp [m]
    linarith
  have hkm : (k:ℝ)+(m:ℝ) ≤ 4*ell*D := by linarith
  have hr : 0<α/D := by positivity
  have hrd : α/D ≤ 1/100 := (div_le_iff₀ hD).mpr (by linarith)
  have hcst : C*(E+B*((k:ℝ)+(m:ℝ))*(α/D)) ≤ b*α/2 := by
    have hcost : C*B*((k:ℝ)+(m:ℝ))*(α/D) ≤ 4*C*B*ell*α := by
      calc
        _ ≤ C*B*(4*ell*D)*(α/D) := by gcongr
        _ = _ := by field_simp
    have hCEa : C*E ≤ b*α/4 := by nlinarith only [hCE,mul_le_mul_of_nonneg_left hαl hb.le]
    have hCBa : 4*C*B*ell*α ≤ b*α/4 := by nlinarith only [mul_le_mul_of_nonneg_right hCB hα.le]
    nlinarith only [hcost,hCEa,hCBa]
  have hsmall : C*B*((k:ℝ)+(m:ℝ))*(α/D)^3 ≤ 1/4 := by
    calc
      _ ≤ C*B*(4*ell*D)*((2*α₀)/D)^3 := by gcongr
      _ = (32*C*B*ell*α₀^3)/D^2 := by field_simp; ring
      _ ≤ 1/4 := (div_le_iff₀ (sq_pos_of_pos hD)).mpr (by nlinarith only [hDS])
  have hel := hg.energy_per_particle_lower hr hn
  have haD : (α/D)*((n:ℝ)/L.val^3)=α := by rw [← hDN]; exact div_mul_cancel₀ _ hD.ne'
  rw [haD] at hel
  change b*α ≤ energy g/(n:ℝ) at hel
  let γ := (m:ℝ)*(energy g/(n:ℝ)-C*(E+B*((k:ℝ)+(m:ℝ))*(α/D)))
  have hgap : b*α/2 ≤ energy g/(n:ℝ)-C*(E+B*((k:ℝ)+(m:ℝ))*(α/D)) := by linarith
  have hγlow : ell*D*b*α₀/8 ≤ γ := by
    calc
      _ ≤ (ell*D/2)*(b*α/2) := by
        nlinarith only [mul_le_mul_of_nonneg_left hαl (by positivity : 0 ≤ ell*D*b/4)]
      _ ≤ _ := mul_le_mul hml hgap (by positivity) (by positivity)
  have hγ : 0<γ := (by positivity : 0<ell*D*b*α₀/8).trans_le hγlow
  have hj := hjoint S n L (α/D) hr hrd (by omega) (by linarith) g hg c hc k m (ell*D)
    (by positivity) hk hsmall hγ A
  apply hj.trans
  apply pow_le_pow_left₀ (by positivity)
  change G/((ell*D)*γ) ≤ Q/D^2
  have hd : ell^2*D^2*b*α₀/8 ≤ (ell*D)*γ := by
    nlinarith only [mul_le_mul_of_nonneg_left hγlow (by positivity : 0 ≤ ell*D)]
  calc
    _ ≤ G/(ell^2*D^2*b*α₀/8) := div_le_div_of_nonneg_left hG.le (by positivity) hd
    _ = _ := by dsimp [Q]; field_simp

theorem scaled_low_count_probability_above (Amin : ℝ) : ∃ α₀ ell D₀ Q : ℝ,
    Amin≤α₀ ∧ 0<α₀ ∧ 0<ell ∧ 0<D₀ ∧ 0<Q ∧
    ∀ (S : Type) [DecidableEq S] (n : ℕ) (L : Length) (D α : ℝ),
      2≤n → 1 ≤ L.val → D=(n:ℝ)/L.val^3 → D₀ ≤ D →
      α₀/2 ≤ α → α ≤ 2*α₀ →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ (c : S → Torus L), (∀ z v, z≠v → 1 ≤ dist (c z) (c v)) →
    ∀ A : Finset S,
      groundPositionLaw n L g {X | ∀ s∈A, count L (1/100) (c s) X < ell*D} ≤
        ENNReal.ofReal ((Q/D^2)^A.card) := by
  obtain ⟨α₀,ell,D₀,Q,hAmin,hα,hell,hD₀,hQ,hs⟩ := scaled_joint_low_counts_above Amin
  refine ⟨α₀,ell,D₀,Q,hAmin,hα,hell,hD₀,hQ,?_⟩
  intro S _ n L D α hn hL hDN hDD hαl hαu g hg c hc A
  have hh : 0<ell*D := mul_pos hell (hD₀.trans_le hDD)
  apply (groundPositionLaw_le_joint hh c A g _ ?_ (fun X hX s hs ↦ (hX s hs).le)).trans
  · exact ENNReal.ofReal_le_ofReal (hs S n L D α hn hL hDN hDD hαl hαu g hg c hc A)
  · simpa only [Set.ofPred_forall] using Finset.measurableSet_biInter A (fun s _ ↦ measurableSet_lt
      (count_continuous (n:=n) L (1/100) (c s)).measurable
      (show Measurable (fun _ : Configuration n L ↦ ell*D) from measurable_const))

theorem scaled_centered_low_counts_above (Amin : ℝ) : ∃ α₀ ell D₀ Q : ℝ,
    Amin≤α₀ ∧ 0<α₀ ∧ 0<ell ∧ 0<D₀ ∧ 0<Q ∧
    ∀ (S : Type) [DecidableEq S] (n : ℕ) (L : Length) (D α : ℝ),
      2≤n → 1 ≤ L.val → D=(n:ℝ)/L.val^3 → D₀ ≤ D →
      α₀/2 ≤ α → α ≤ 2*α₀ →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ (c : S → Torus L), (∀ z v, z≠v → 1 ≤ dist (c z) (c v)) →
    ∀ A : Finset S,
      groundPositionLaw n L g {X | ∀ s∈A, (centeredCount L (c s) X:ℝ) < ell*D} ≤
        ENNReal.ofReal ((Q/D^2)^A.card) := by
  obtain ⟨α₀,ell,D₀,Q,hAmin,hα,hell,hD₀,hQ,hs⟩ := scaled_low_count_probability_above Amin
  refine ⟨α₀,ell,D₀,Q,hAmin,hα,hell,hD₀,hQ,?_⟩
  intro S _ n L D α hn hL hDN hDD hαl hαu g hg c hc A
  apply (measure_mono (show {X : Configuration n L | ∀ s∈A, (centeredCount L (c s) X:ℝ)<ell*D} ⊆
      {X | ∀ s∈A, count L (1/100) (c s) X<ell*D} from ?_)).trans
      (hs S n L D α hn hL hDN hDD hαl hαu g hg c hc A)
  intro X hX s hs
  exact (count_le_centeredCount L (c s) X).trans_lt (hX s hs)

theorem grid_low_count_probability_above (Amin : ℝ) : ∃ α₀ ell D₀ Q : ℝ,
    Amin≤α₀ ∧ 0<α₀ ∧ 0<ell ∧ 0<D₀ ∧ 0<Q ∧
    ∀ (K n : ℕ) (L : Length) (D α : ℝ),
      1≤K → L.val=(K:ℝ) → D=(n:ℝ)/L.val^3 → D₀ ≤ D →
      α₀/2 ≤ α → α ≤ 2*α₀ →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ A : Finset (Fin 3 → Fin K),
      groundPositionLaw n L g {X | ∀ s∈A, (centeredCount L (gridCenter L s) X:ℝ) < ell*D} ≤
        ENNReal.ofReal ((Q/D^2)^A.card) := by
  obtain ⟨α₀,ell,D₀,Q,hAmin,hα,hell,hD₀,hQ,hs⟩ := scaled_centered_low_counts_above Amin
  refine ⟨α₀,ell,max D₀ 2,Q,hAmin,hα,hell,lt_of_lt_of_le hD₀ (le_max_left _ _),hQ,?_⟩
  intro K n L D α hK hLK hDN hDD hαl hαu g hg A
  have hL : 1 ≤ L.val := by rw [hLK]; exact_mod_cast hK
  have hD : 2 ≤ D := (le_max_right D₀ 2).trans hDD
  have hn : 2≤n := by
    have hp : 1 ≤ L.val^3 := one_le_pow₀ hL
    have hmul : 2*L.val^3 ≤ (n:ℝ) := by
      rw [hDN] at hD
      exact (le_div_iff₀ (by positivity)).mp hD
    have hn' : (2:ℝ)≤(n:ℝ) := by linarith
    exact_mod_cast hn'
  exact hs (Fin 3 → Fin K) n L D α hn hL hDN ((le_max_left D₀ 2).trans hDD) hαl hαu
    g hg (gridCenter L) (gridCenter_separated hLK) A

end HardSphere.CellOrbital

end
end

end

end OAI
