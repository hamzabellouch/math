import OAI.Probability.RadialTransition.CellMoments

namespace OAI

universe uI uX uY uZ

noncomputable section


open MeasureTheory Filter Set

open scoped ContDiff BigOperators NNReal ENNReal

namespace RadialTransition

section AbstractCells
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}

def cellHamiltonian (U : ∀ i, X i → ℝ) (W : ∀ i j, X i → X j → ℝ)
    (x : ∀ i, X i) : ℝ :=
  ∑ i, U i (x i) + (1/2:ℝ) * ∑ i, ∑ j, if i = j then 0 else W i j (x i) (x j)

lemma double_sum_update (w : ∀ i j, X i → X j → ℝ)
    (hdiag : ∀ i a b, w i i a b = 0)
    (hsym : ∀ i j a b, w i j a b = w j i b a)
    (x : ∀ i, X i) (k : I) (s t : X k) :
    (∑ i, ∑ j, w i j (Function.update x k s i) (Function.update x k s j)) -
      (∑ i, ∑ j, w i j (Function.update x k t i) (Function.update x k t j)) =
      2 * ∑ j, (w k j s (x j) - w k j t (x j)) := by
  have hpoint (i j : I) :
      w i j (Function.update x k s i) (Function.update x k s j) -
        w i j (Function.update x k t i) (Function.update x k t j) =
      (if i = k then w k j s (x j) - w k j t (x j) else 0) +
      (if j = k then w i k (x i) s - w i k (x i) t else 0) := by
    by_cases hi : i = k
    · subst i
      by_cases hj : j = k
      · subst j; simp [hdiag]
      · simp [hj, Function.update_of_ne]
    · by_cases hj : j = k
      · subst j; simp [hi, Function.update_of_ne]
      · simp [hi, hj, Function.update_of_ne]
  simp_rw [← Finset.sum_sub_distrib, hpoint, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  conv_lhs => arg 2; arg 2; intro i; rw [hsym i k (x i) s, hsym i k (x i) t]
  ring

lemma cellHamiltonian_update (U : ∀ i, X i → ℝ) (W : ∀ i j, X i → X j → ℝ)
    (vac : ∀ i, X i) (hU0 : ∀ i, U i (vac i) = 0)
    (hW0 : ∀ i j a, W i j (vac i) a = 0)
    (hsym : ∀ i j a b, W i j a b = W j i b a)
    (x : ∀ i, X i) (k : I) (s : X k) :
    cellHamiltonian U W (Function.update x k s) -
      cellHamiltonian U W (Function.update x k (vac k)) =
      U k s + ∑ j, if k = j then 0 else W k j s (x j) := by
  let w (i j : I) (a : X i) (b : X j) := if i = j then 0 else W i j a b
  have hwsym (i j : I) (a : X i) (b : X j) : w i j a b = w j i b a := by
    dsimp [w]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h, hsym i j a b]
  have hh := double_sum_update w (by simp [w]) hwsym x k s (vac k)
  have hu : (∑ i, U i (Function.update x k s i)) -
      (∑ i, U i (Function.update x k (vac k) i)) = U k s := by
    rw [← Finset.sum_sub_distrib]
    have he (i : I) : U i (Function.update x k s i) - U i (Function.update x k (vac k) i) =
        if i = k then U k s else 0 := by
      by_cases hi : i = k
      · subst i; simp [hU0]
      · simp [hi, Function.update_of_ne]
    simp_rw [he]
    simp
  have hz (j : I) : w k j (vac k) (x j) = 0 := by simp [w, hW0]
  simp only [hz, sub_zero] at hh
  change (∑ i, U i (Function.update x k s i)) + 1/2 * (∑ i, ∑ j, w i j _ _) -
      ((∑ i, U i (Function.update x k (vac k) i)) + 1/2 * (∑ i, ∑ j, w i j _ _)) = _
  dsimp only [w] at hh
  linarith

lemma cellHamiltonian_stable (U : ∀ i, X i → ℝ) (W : ∀ i j, X i → X j → ℝ)
    (n : ∀ i, X i → ℝ) (_hn : ∀ i x, 0 ≤ n i x)
    (J : I → I → ℝ) (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    {D B : ℝ} (_hD : 0 ≤ D) (hrow : ∀ i, ∑ j, J i j ≤ D)
    (hU : ∀ i a, D * (n i a)^2 - B * n i a - J i i/2 * (n i a)^2 ≤ U i a)
    (hW : ∀ i j a b, -J i j * n i a * n j b ≤ W i j a b)
    (x : ∀ i, X i) :
    D/2 * ∑ i, (n i (x i))^2 - B * ∑ i, n i (x i) ≤ cellHamiltonian U W x := by
  have hb := symmetric_row_quadratic J (fun i => n i (x i)) D hJ hJsym hrow
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hU i (x i))
  have hw := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => show
      (if i = j then 0 else -J i j * n i (x i) * n j (x j)) ≤
      (if i = j then 0 else W i j (x i) (x j)) from by split_ifs; rfl; exact hW i j _ _))
  have hsplit : (∑ i, ∑ j, J i j * n i (x i) * n j (x j)) =
      (∑ i, J i i * (n i (x i))^2) +
      ∑ i, ∑ j, if i = j then 0 else J i j * n i (x i) * n j (x j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have he (j : I) : J i j * n i (x i) * n j (x j) =
        (if i = j then J i j * n i (x i) * n j (x j) else 0) +
        (if i = j then 0 else J i j * n i (x i) * n j (x j)) := by split_ifs <;> simp
    calc
      _ = ∑ j, ((if i = j then J i j * n i (x i) * n j (x j) else 0) +
          (if i = j then 0 else J i j * n i (x i) * n j (x j))) :=
        Finset.sum_congr rfl (fun j _ => he j)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        congr 1
        ring
  have hwneg : (∑ i, ∑ j, if i = j then 0 else -J i j * n i (x i) * n j (x j)) =
      -(∑ i, ∑ j, if i = j then 0 else J i j * n i (x i) * n j (x j)) := by
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hwneg] at hw
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hu
  have hd : (∑ i, J i i / 2 * (n i (x i))^2) = (1/2:ℝ) * ∑ i, J i i * (n i (x i))^2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hd] at hu
  unfold cellHamiltonian
  linarith

end AbstractCells

section PairCells
variable {X : Type uX} {Y : Type uY} {Z : Type uZ}

def pairWithin (v : X → X → ℝ) (s : ParticleState X) : ℝ := by
  classical
  exact (1/2:ℝ) * ∑ i : Fin s.1, ∑ j : Fin s.1, if i = j then 0 else v (s.2 i) (s.2 j)

def pairBetween (v : X → Y → ℝ) (s : ParticleState X) (t : ParticleState Y) : ℝ :=
  ∑ i : Fin s.1, ∑ j : Fin t.1, v (s.2 i) (t.2 j)

@[simp] theorem pairWithin_vacuum (v : X → X → ℝ) : pairWithin v particleVacuum = 0 := by
  change (1/2:ℝ) * (∑ i : Fin 0, ∑ j : Fin 0, if i = j then 0 else v (Fin.elim0 i) (Fin.elim0 j)) = 0
  rw [Fin.sum_univ_zero, mul_zero]

@[simp] theorem pairBetween_vacuum (v : X → Y → ℝ) (t : ParticleState Y) :
    pairBetween v particleVacuum t = 0 := by
  change (∑ i : Fin 0, ∑ j : Fin t.1, v (Fin.elim0 i) (t.2 j)) = 0
  rw [Fin.sum_univ_zero]

theorem pairBetween_symm (v : X → Y → ℝ) (w : Y → X → ℝ)
    (hv : ∀ x y, v x y = w y x) (s : ParticleState X) (t : ParticleState Y) :
    pairBetween v s t = pairBetween w t s := by
  unfold pairBetween
  simp_rw [hv]
  exact Finset.sum_comm

lemma continuous_particle_prod [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : ParticleState X → ParticleState Y → Z}
    (hf : ∀ m n, Continuous (fun p : (Fin m → X) × (Fin n → Y) => f ⟨m,p.1⟩ ⟨n,p.2⟩)) :
    Continuous (Function.uncurry f) := by
  let e := Homeomorph.sigmaProdDistrib (X := fun m : ℕ => Fin m → X) (Y := ParticleState Y)
  have h : Continuous (fun q : Σ m : ℕ, (Fin m → X) × ParticleState Y =>
      f ⟨q.1,q.2.1⟩ q.2.2) := by
    apply continuous_sigma
    intro m
    let e' := Homeomorph.sigmaProdDistrib (X := fun n : ℕ => Fin n → Y) (Y := Fin m → X)
    have h' : Continuous (fun q : Σ n : ℕ, (Fin n → Y) × (Fin m → X) =>
        f ⟨m,q.2.2⟩ ⟨q.1,q.2.1⟩) := by
      apply continuous_sigma
      intro n
      exact (hf m n).comp continuous_swap
    exact (h'.comp e'.continuous).comp continuous_swap
  exact h.comp e.continuous

lemma continuous_pairWithin [TopologicalSpace X] (v : X → X → ℝ)
    (hv : Continuous (Function.uncurry v)) : Continuous (pairWithin v) := by
  apply continuous_sigma
  intro n
  change Continuous (fun a : Fin n → X => (1/2:ℝ) *
    ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else v (a i) (a j))
  apply continuous_const.mul
  apply continuous_finsetSum _
  intro i _
  apply continuous_finsetSum _
  intro j _
  split_ifs
  · exact continuous_const
  · exact hv.comp (show Continuous (fun a : Fin n → X => (a i, a j)) from
      (continuous_apply i).prodMk (continuous_apply j))

lemma continuous_pairBetween [TopologicalSpace X] [TopologicalSpace Y] (v : X → Y → ℝ)
    (hv : Continuous (Function.uncurry v)) : Continuous (Function.uncurry (pairBetween v)) := by
  apply continuous_particle_prod
  intro m n
  change Continuous (fun p : (Fin m → X) × (Fin n → Y) =>
    ∑ i : Fin m, ∑ j : Fin n, v (p.1 i) (p.2 j))
  apply continuous_finsetSum _
  intro i _
  apply continuous_finsetSum _
  intro j _
  exact hv.comp (show Continuous (fun p : (Fin m → X) × (Fin n → Y) => (p.1 i, p.2 j)) from
    ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply j).comp continuous_snd))

lemma pairBetween_lower (v : X → Y → ℝ) {J : ℝ} (hv : ∀ x y, -J ≤ v x y)
    (s : ParticleState X) (t : ParticleState Y) :
    -J * particleCount s * particleCount t ≤ pairBetween v s t := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hv (s.2 i) (t.2 j)))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    pairBetween, particleCount, mul_comm, mul_left_comm] using hh

lemma pairWithin_perturb_lower (v w : X → X → ℝ) {J : ℝ} (hJ : 0 ≤ J)
    (hv : ∀ x y, w x y - J ≤ v x y) (s : ParticleState X) :
    pairWithin w s - J/2 * (particleCount s : ℝ)^2 ≤ pairWithin v s := by
  classical
  have hp (i j : Fin s.1) :
      (if i = j then 0 else w (s.2 i) (s.2 j)) - J ≤
        (if i = j then 0 else v (s.2 i) (s.2 j)) := by
    split_ifs
    · linarith
    · exact hv _ _
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hh
  unfold pairWithin particleCount
  nlinarith

lemma pairWithin_core {t J : ℝ} (ht : 0 ≤ t) (hJ : 0 ≤ J)
    (pos : X → Position) (hdiam : ∀ x y, dist (pos x) (pos y) ≤ 1)
    (v : X → X → ℝ) (hv : ∀ x y, corePotential t (nndist (pos x) (pos y)) - J ≤ v x y)
    (s : ParticleState X) :
    t^2/8 * (particleCount s : ℝ)^2 - t^2/2 * particleCount s -
      J/2 * (particleCount s : ℝ)^2 ≤ pairWithin v s := by
  have hh := pairWithin_perturb_lower v (fun x y => corePotential t (nndist (pos x) (pos y))) hJ hv s
  have hc := core_ordered_lower_small_diameter ht (fun i : Fin s.1 => pos (s.2 i))
    (fun i j => hdiam _ _)
  simp only [Fintype.card_fin, ne_eq, ite_not] at hc
  dsimp only [pairWithin, corePotential, particleCount] at hh
  change (1/2:ℝ) * (∑ i : Fin s.1, ∑ j : Fin s.1,
    if i = j then 0 else coreReal t (dist (pos (s.2 i)) (pos (s.2 j)))) - _ ≤ _ at hh
  dsimp only [particleCount, pairWithin]
  linarith

end PairCells

section PhysicalCells
variable {I : Type uI} [Fintype I] [DecidableEq I] {X : I → Type uX}
  [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

def pairCellEnergy (v : ∀ i j, X i → X j → ℝ) (x : ∀ i, ParticleState (X i)) : ℝ :=
  cellHamiltonian (fun i => pairWithin (v i i)) (fun i j => pairBetween (v i j)) x

omit [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
  [∀ i, SecondCountableTopology (X i)] in
lemma continuous_pairCellEnergy (v : ∀ i j, X i → X j → ℝ)
    (hv : ∀ i j, Continuous (Function.uncurry (v i j))) : Continuous (pairCellEnergy v) := by
  unfold pairCellEnergy cellHamiltonian
  apply Continuous.add
  · exact continuous_finsetSum _ (fun i _ => (continuous_pairWithin _ (hv i i)).comp (continuous_apply i))
  · apply continuous_const.mul
    apply continuous_finsetSum _
    intro i _
    apply continuous_finsetSum _
    intro j _
    split_ifs
    · exact continuous_const
    · exact (continuous_pairBetween _ (hv i j)).comp
        (show Continuous (fun x : ∀ i, ParticleState (X i) => (x i, x j)) from
          (continuous_apply i).prodMk (continuous_apply j))

theorem pairCell_exponential_moment [Nonempty I]
    (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)]
    (pos : ∀ i, X i → Position) (hdiam : ∀ i x y, dist (pos i x) (pos i y) ≤ 1)
    {t β V z : ℝ} (ht : 0 < t) (hβ : 0 < β) (hV : 0 ≤ V)
    (hvol : ∀ i, (ν i univ).toReal ≤ V)
    (v : ∀ i j, X i → X j → ℝ) (hv : ∀ i j, Continuous (Function.uncurry (v i j)))
    (hvsym : ∀ i j x y, v i j x y = v j i y x)
    (J : I → I → ℝ) (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ (t^2/8)/8)
    (hintra : ∀ i x y, corePotential t (nndist (pos i x) (pos i y)) - J i i ≤ v i i x y)
    (hcross : ∀ i j x y, -J i j ≤ v i j x y) :
    ∀ i, (∫ x, Real.exp (β*(t^2/8)/4 * (cellN i x)^2)
      ∂boltzmannMeasure (Measure.pi (fun j => particleBase (ν j) z))
        (fun x => β * pairCellEnergy v x)) ≤
      Real.exp (16/15 * V * Real.exp (z+β*(t^2/2))) := by
  let D := t^2/8
  let B := t^2/2
  have hD : 0 < D := by dsimp [D]; positivity
  let U (i : I) := pairWithin (v i i)
  let W (i j : I) := pairBetween (v i j)
  have hU (i : I) (s : ParticleState (X i)) :
      D * (particleCount s : ℝ)^2 - B * particleCount s - J i i/2*(particleCount s : ℝ)^2 ≤ U i s :=
    pairWithin_core ht.le (hJ i i) (pos i) (hdiam i) (v i i) (hintra i) s
  have hW (i j : I) (s : ParticleState (X i)) (r : ParticleState (X j)) :
      -J i j * particleCount s * particleCount r ≤ W i j s r :=
    pairBetween_lower (v i j) (hcross i j) s r
  have hrowD (i : I) : ∑ j, J i j ≤ D := (hrow i).trans (by dsimp [D]; nlinarith [sq_nonneg t])
  have hH (x : ∀ i, ParticleState (X i)) :
      D/2 * ∑ i, (cellN i x)^2 - B * ∑ i, cellN i x ≤ pairCellEnergy v x := by
    exact cellHamiltonian_stable U W (fun _ s => particleCount s) (fun _ _ => Nat.cast_nonneg _)
      J hJ hJsym hD.le hrowD hU hW x
  let θ (i j : I) := if i = j then 0 else 8*J i j/D
  have hθ (i j : I) : 0 ≤ θ i j := by
    dsimp [θ]
    split_ifs
    · rfl
    · exact div_nonneg (mul_nonneg (by norm_num) (hJ i j)) hD.le
  have hθrow (i : I) : ∑ j, θ i j ≤ 1 := by
    have hle : ∑ j, θ i j ≤ 8/D * ∑ j, J i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      dsimp [θ]
      split_ifs
      · exact mul_nonneg (div_nonneg (by norm_num) hD.le) (hJ i j)
      · exact le_of_eq (by ring)
    refine hle.trans ?_
    calc
      _ ≤ 8/D * (D/8) := mul_le_mul_of_nonneg_left (hrow i) (by positivity)
      _ = 1 := by field_simp
  have hcond (i : I) (x : ∀ j, ParticleState (X j)) (s : ParticleState (X i)) :
      D/2 * (particleCount s : ℝ)^2 - B*particleCount s -
        (particleCount s : ℝ)*(D/8 * ∑ j, θ i j * cellN j x) ≤
      pairCellEnergy v (Function.update x i s) -
        pairCellEnergy v (Function.update x i particleVacuum) := by
    rw [pairCellEnergy, pairCellEnergy,
      cellHamiltonian_update _ _ (fun _ => particleVacuum) (by simp)
        (by simp) (fun k j a b => pairBetween_symm _ _ (hvsym k j) a b)]
    have hJi : J i i ≤ D :=
      (Finset.single_le_sum (fun j _ => hJ i j) (Finset.mem_univ i)).trans (hrowD i)
    have hu := hU i s
    have hsq := mul_nonneg (sub_nonneg.mpr hJi) (sq_nonneg (particleCount s : ℝ))
    have hw := Finset.sum_le_sum (s := Finset.univ) (fun j _ => show
      (if i = j then 0 else -J i j * particleCount s * particleCount (x j)) ≤
        (if i = j then 0 else pairBetween (v i j) s (x j)) from by
          split_ifs; rfl; exact hW i j s (x j))
    have he : (∑ j, if i = j then 0 else -J i j * particleCount s * particleCount (x j)) =
        -(particleCount s : ℝ) * (D/8 * ∑ j, θ i j * cellN j x) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [θ, cellN]
      split_ifs
      · ring
      · field_simp
    rw [he] at hw
    dsimp [U] at hu
    linarith
  apply uniform_cell_exponential_moment ν z (D := β*D) (B := β*B)
    (E := fun x => β * pairCellEnergy v x)
    (mul_pos hβ hD) hV hvol θ hθ (by simp [θ]) hθrow
    (measurable_const.mul (continuous_pairCellEnergy v hv).measurable)
  · intro x
    have hh := mul_le_mul_of_nonneg_left (hH x) hβ.le
    convert hh using 1; first | rfl | ring
  · intro i x s
    have hh := mul_le_mul_of_nonneg_left (hcond i x s) hβ.le
    convert hh using 1 <;> first | rfl | ring

end PhysicalCells
end RadialTransition

end

end OAI
