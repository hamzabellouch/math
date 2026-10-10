import OAI.Computability.MeanPayoff.Labeller

namespace OAI

namespace MeanPayoff.Label

theorem transformed_ne_zero (G : Game) (e : Fin G.m) : transformed G e ≠ 0 := by
  have hn : (0 : ℤ) < G.n := by exact_mod_cast G.positive
  unfold transformed
  by_cases hw : 0 ≤ G.weight e
  · have h := mul_nonneg (show (0 : ℤ) ≤ G.n + 1 by omega) hw
    omega
  · have hw' : G.weight e ≤ -1 := by omega
    have h := mul_le_mul_of_nonneg_left hw' (show (0 : ℤ) ≤ G.n+1 by omega)
    nlinarith only [h, hn]

def sourceWeight (G : Game) : ℕ :=
  Finset.univ.sup (fun e : Fin G.m => (transformed G e).natAbs)

theorem weightBound_eq_source (G : Game) : weightBound G = (sourceWeight G : ℤ) := by
  obtain ⟨e, _⟩ := G.total ⟨0, G.positive⟩
  have hpos : 0 < (transformed G e).natAbs := Int.natAbs_pos.mpr (transformed_ne_zero G e)
  have hle : (transformed G e).natAbs ≤ sourceWeight G :=
    Finset.le_sup (f := fun e : Fin G.m => (transformed G e).natAbs) (Finset.mem_univ e)
  have hW : (1 : ℤ) ≤ sourceWeight G := by exact_mod_cast (show 1 ≤ sourceWeight G by omega)
  exact max_eq_right hW

def initialExponent (G : Game) : ℕ := Nat.clog 2 (64*(G.n+1)*(sourceWeight G+1))

def initialWidth (G : Game) : ℤ := 2^(initialExponent G)

theorem initialWidth_ge (G : Game) :
    64*((G.n : ℤ)+1)*(weightBound G+1) ≤ initialWidth G := by
  rw [weightBound_eq_source]
  have h : 64*(G.n+1)*(sourceWeight G+1) ≤ (2 : ℕ)^(initialExponent G) :=
    Nat.le_pow_clog (by decide : 1 < 2) _
  have h' := Int.ofNat_le.mpr h
  push_cast only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] at h'
  exact h'

theorem initialExponent_least (G : Game) {d : ℕ}
    (h : 64*((G.n : ℤ)+1)*(weightBound G+1) ≤ (2 : ℤ)^d) :
    initialExponent G ≤ d := by
  rw [weightBound_eq_source] at h
  apply Nat.clog_le_of_le_pow
  exact_mod_cast h

theorem initialWidth_large (G : Game) : 32*G.n*weightBound G ≤ initialWidth G := by
  have hn : (0 : ℤ) < G.n := by exact_mod_cast G.positive
  have hw := weightBound_positive G
  have h := initialWidth_ge G
  nlinarith only [hn, hw, h]

theorem wide_winning_iff (G : Game) {D : ℤ} (hD : topWidth G ≤ D)
    {h : Vec (Fin G.n)}
    (hh : Subsolution (operator G) (fun _ => 0) (fun _ => D) h ∧
      Supersolution (operator G) (fun _ => 0) (fun _ => D) h) (i : Fin G.n) :
    Winning G i ↔ D-G.n*weightBound G ≤ h i := by
  have hn : (0 : ℤ) < G.n := by exact_mod_cast G.positive
  have hw := weightBound_positive G
  have hnw : 0 < (G.n : ℤ)*weightBound G := mul_pos hn hw
  obtain ⟨z, hz, _⟩ := box_solution_exists_unique G (fun _ => 0)
    (fun _ => topWidth G) (fun _ => by dsimp [topWidth]; positivity)
  have hzsub : Subsolution (operator G) (fun _ => 0) (fun _ => D) z :=
    ⟨⟨hz.1.1.1, fun j => (hz.1.1.2 j).trans hD⟩, hz.1.2⟩
  have hlow := box_comparison G hzsub hh.2
  have hzsuper : Supersolution (operator G) (fun _ => 0) (fun _ => D)
      (shift z (D-topWidth G)) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro j
      have h := hz.2.1.1 j
      dsimp [shift]
      linarith only [h, hD]
    · intro j
      have h := hz.2.1.2 j
      dsimp [shift]
      linarith only [h]
    · intro j hj
      have hj' : z j < topWidth G := by
        change z j + (D-topWidth G) < D at hj
        linarith only [hj]
      have h := hz.2.2 j hj'
      rw [(operator_laws G).translation]
      change operator G z j + (D-topWidth G) ≤ z j + (D-topWidth G)
      omega
  have hhigh := box_comparison G hh.1 hzsuper
  have hhalf : topWidth G / 2 = 4*G.n*weightBound G := by
    unfold topWidth
    rw [show 8 * (G.n : ℤ) * weightBound G = (4 * G.n * weightBound G) * 2 by ring]
    omega
  rw [winning_iff_high G hz i, hhalf]
  constructor
  · intro hi
    rcases solution_near_boundary G (le_of_lt hw) (transformed_le_bound G) hh i with hl | hr
    · have h := hlow i
      nlinarith only [hi, hl, h, hnw]
    · exact hr
  · intro hi
    have h := hhigh i
    dsimp [shift, topWidth] at h
    nlinarith only [hi, h, hnw]

def uniformMass (G : Game) : Fin G.n → ℚ := fun _ => 1/(G.n : ℚ)

theorem uniformMass_pos (G : Game) : ∀ i, 0 < uniformMass G i := by
  intro i
  dsimp [uniformMass]
  have h : (0 : ℚ) < G.n := by exact_mod_cast G.positive
  positivity

theorem uniformMass_le_one (G : Game) (S : Finset (Fin G.n)) : mass (uniformMass G) S ≤ 1 := by
  have h := mass_mono (fun i => le_of_lt (uniformMass_pos G i)) (Finset.subset_univ S)
  have hn : (G.n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.positive)
  have hm : mass (uniformMass G) Finset.univ = 1 := by
    simp [mass, uniformMass, hn]
  exact h.trans_eq hm

theorem labels_correct_of_large_width (G : Game) {D : ℤ}
    (hlarge : 32*G.n*weightBound G ≤ D) {labels : Fin G.n → Bool}
    (good : Good (operator G) (fun _ => 0) D
      (uniformMass G) (uniformMass G) labels) :
    ∀ i, labels i = true ↔ Winning G i := by
  have hn : (0 : ℤ) < G.n := by exact_mod_cast G.positive
  have hw := weightBound_positive G
  have hnw : 0 < (G.n : ℤ)*weightBound G := mul_pos hn hw
  have hD : topWidth G ≤ D := by dsimp [topWidth]; nlinarith only [hlarge, hnw]
  obtain ⟨h, hh, _⟩ := box_solution_exists_unique G (fun _ => 0)
    (fun _ => D) (fun _ => by nlinarith only [hlarge, hnw])
  have hs : shift (fun _ : Fin G.n => 0) D = (fun _ => D) := funext (fun _ => zero_add D)
  have hx : MaxWitness (operator G) (fun _ => 0) D (uniformMass G) h := by
    unfold MaxWitness
    rw [hs]
    exact ⟨hh.1, uniformMass_le_one G _⟩
  have hy : MinWitness (operator G) (fun _ => 0) D (uniformMass G) h := by
    unfold MinWitness
    rw [hs]
    exact ⟨hh.2, uniformMass_le_one G _⟩
  intro i
  rw [wide_winning_iff G hD hh i]
  constructor
  · intro hi
    rcases solution_near_boundary G (le_of_lt hw) (transformed_le_bound G) hh i with hl | hr
    · have hc : MinClaim (fun _ => 0) D h i := by
        dsimp [MinClaim]
        nlinarith only [hl, hlarge]
      have hf := good.2 h hy i hc
      simp [hi] at hf
    · exact hr
  · intro hi
    apply good.1 h hx i
    dsimp [MaxClaim]
    nlinarith only [hi, hlarge]

theorem main_labels_correct (G : Game) {labels : Fin G.n → Bool}
    (good : Good (operator G) (fun _ => 0) (initialWidth G)
      (uniformMass G) (uniformMass G) labels) :
    ∀ i, labels i = true ↔ Winning G i :=
  labels_correct_of_large_width G (initialWidth_large G) good

def mainLabels (G : Game) : Fin G.n → Bool :=
  (labeller G (fun _ => 0) (initialExponent G) (uniformMass G) (uniformMass G)
    (uniformMass_pos G) (uniformMass_pos G)).val

theorem mainLabels_correct (G : Game) (i : Fin G.n) : mainLabels G i = true ↔ Winning G i :=
  main_labels_correct G (labeller_good G _ _ _ _ _ _) i

end MeanPayoff.Label

end OAI
