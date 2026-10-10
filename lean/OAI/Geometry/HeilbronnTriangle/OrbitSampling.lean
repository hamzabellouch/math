import OAI.Geometry.HeilbronnTriangle.OrbitUniform
import OAI.Geometry.HeilbronnTriangle.IntegerSampling

namespace OAI


noncomputable section

namespace Problem355.OrbitSampling

def orbitFinset (G : Type*) {X : Type*} [Group G] [MulAction G X] [Fintype X]
    (x : X) : Finset X := by
  classical
  exact Finset.univ.filter (fun y => y ∈ MulAction.orbit G x)

 theorem mem_orbitFinset {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    (x y : X) : y ∈ orbitFinset G x ↔ y ∈ MulAction.orbit G x := by
  classical
  simp [orbitFinset]

 theorem orbitFinset_nonempty {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    (x : X) : (orbitFinset G x).Nonempty := by
  exact ⟨x, (mem_orbitFinset x x).mpr (MulAction.mem_orbit_self x)⟩

 theorem card_orbitFinset {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    (x : X) : (orbitFinset G x).card = Nat.card (MulAction.orbit G x) := by
  classical
  simp only [orbitFinset, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem uniform_pushforward {G X : Type*} [Group G] [Fintype G]
    [MulAction G X] [Fintype X] (x y : X) :
    LiftingProbability.pushforwardMass (fun _ : G => 1 / (Nat.card G : ℝ))
      (fun g => g • x) y = LiftingProbability.mainMass (orbitFinset G x) y := by
  classical
  have hsum : LiftingProbability.pushforwardMass (fun _ : G => 1 / (Nat.card G : ℝ))
      (fun g => g • x) y =
      ∑ g : G, if g • x = y then 1 / (Nat.card G : ℝ) else 0 := by
    unfold LiftingProbability.pushforwardMass
    apply Finset.sum_congr rfl
    intro g hg
    by_cases h : g • x = y
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hsum]
  by_cases hy : y ∈ MulAction.orbit G x
  · rw [OrbitUniform.uniform_mass_of_mem_orbit x y hy]
    have hym := (mem_orbitFinset x y).mpr hy
    simp [LiftingProbability.mainMass, hym, card_orbitFinset]
  · rw [OrbitUniform.uniform_mass_of_not_mem_orbit x y hy]
    have hym : y ∉ orbitFinset G x := mt (mem_orbitFinset x y).mp hy
    simp [LiftingProbability.mainMass, hym]

abbrev MainGroup (h : ℕ) := Matrix.SpecialLinearGroup (Fin 3) (ZMod h)

theorem sl_averaged_columns_eq_liftedMass {Ω : Type*} [Fintype Ω]
    (h q L : ℕ) [NeZero h] [NeZero q] (shift : Fin 3 → ℤ)
    (C : Fin 3 → Fin 3 → ZMod h) (w : Ω → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q)) (s : ℕ)
    (x : Fin 3 → IntegerSampling.Box (L * (h * q)) 3 shift) :
    (∑ G : MainGroup h, (1 / (Nat.card (MainGroup h) : ℝ)) *
      ∑ ω, w ω * ∏ i,
        IntegerSampling.columnLaw h q L shift ((G • C) i) (V ω) s (x i)) =
      LiftingProbability.liftedMass
        (fun x i => IntegerSampling.residue h (x i))
        (fun x i => IntegerSampling.residue q (x i))
        (orbitFinset (MainGroup h) C) w V s (L ^ 9) x := by
  classical
  exact LiftingProbability.averaged_columns_eq_liftedMass
    (IntegerSampling.residue h) (IntegerSampling.residue q)
    (fun G : MainGroup h => G • C) (fun _ => 1 / (Nat.card (MainGroup h) : ℝ))
    w V (orbitFinset (MainGroup h) C) s L (uniform_pushforward C) x

theorem sl_action_transpose (h : ℕ) (G : MainGroup h)
    (C : Fin 3 → Fin 3 → ZMod h) :
    Matrix.transpose (G • C) = G.val * Matrix.transpose C := by
  ext i j
  rfl

theorem sl_action_det (h : ℕ) (G : MainGroup h)
    (C : Fin 3 → Fin 3 → ZMod h) :
    Matrix.det (Matrix.transpose (G • C)) = Matrix.det (Matrix.transpose C) := by
  rw [sl_action_transpose, Matrix.det_mul, G.property, one_mul]

def integralMatrix {N : ℕ} {shift : Fin 3 → ℤ}
    (x : Fin 3 → IntegerSampling.Box N 3 shift) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => (x j i).val

theorem integralMatrix_reduction_of_mem_orbit (h q L : ℕ) [NeZero h]
    (shift : Fin 3 → ℤ) (C : Fin 3 → Fin 3 → ZMod h)
    (x : Fin 3 → IntegerSampling.Box (L * (h * q)) 3 shift)
    (hx : (fun i => IntegerSampling.residue h (x i)) ∈ orbitFinset (MainGroup h) C) :
    ∃ G : MainGroup h, (integralMatrix x).map (Int.cast : ℤ → ZMod h) =
      G.val * Matrix.transpose C := by
  obtain ⟨G, hG⟩ := (mem_orbitFinset C _).mp hx
  refine ⟨G, ?_⟩
  change Matrix.transpose (fun i => IntegerSampling.residue h (x i)) = G.val * Matrix.transpose C
  rw [← hG, sl_action_transpose]

theorem sl_exact_lifting_identity {Ω : Type*} [Fintype Ω]
    (h q L : ℕ) [NeZero h] [NeZero q] (hL : 0 < L) (shift : Fin 3 → ℤ)
    (C : Fin 3 → Fin 3 → ZMod h) (w : Ω → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q)) (s : ℕ) (hs : 0 < s)
    (E : Finset (Fin 3 → IntegerSampling.Box (L * (h * q)) 3 shift)) :
    (∑ x ∈ E, ∑ G : MainGroup h, (1 / (Nat.card (MainGroup h) : ℝ)) *
      ∑ ω, w ω * ∏ i,
        IntegerSampling.columnLaw h q L shift ((G • C) i) (V ω) s (x i)) =
      (h : ℝ) ^ 9 / ((L * (h * q) : ℕ) ^ 9 * ((orbitFinset (MainGroup h) C).card : ℝ)) *
        ∑ x ∈ E.filter (fun x =>
          (fun i => IntegerSampling.residue h (x i)) ∈ orbitFinset (MainGroup h) C),
          LiftingProbability.auxiliaryWeight q s w V
            (fun i => IntegerSampling.residue q (x i)) := by
  classical
  simp_rw [sl_averaged_columns_eq_liftedMass]
  exact LiftingProbability.exact_lifting_identity _ _ _ (orbitFinset_nonempty C)
    w V s h q L hs (Nat.pos_of_ne_zero (NeZero.ne h))
    (Nat.pos_of_ne_zero (NeZero.ne q)) hL E

end Problem355.OrbitSampling

end

end OAI
