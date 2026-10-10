import OAI.Probability.ThorpShuffle.Main

namespace OAI

noncomputable section
open scoped BigOperators
open Filter

namespace Revealed
open Thorp
open scoped Classical

def outside (d : ℕ) : Position d → Position (d + 1) := fun x => Fin.cons true x

def freeLabel (d : ℕ) : Position d → Position (d + 1) := fun x => Fin.cons false x

lemma freeLabel_injective (d : ℕ) : Function.Injective (freeLabel d) := by
  intro x y h
  exact congrArg Fin.tail h

def imageRank {α β : Type*} [Fintype α] [LinearOrder β]
    (f : α → β) (hf : Function.Injective f) : α ≃ Fin (Fintype.card α) := by
  classical
  let e := Equiv.ofInjective f hf
  exact e.trans (Fintype.orderIsoFinOfCardEq (Set.range f)
    (Fintype.card_congr e).symm).toEquiv.symm

def freeRank (d : ℕ) (g : State (d + 1)) : Position d ≃ Fin (2 ^ d) :=
  (imageRank (fun x => toLex (g (freeLabel d x)))
    (by intro x y h; exact congrArg Fin.tail (g.injective h))).trans
      (finCongr (by simp [Position]))

def layoutPath (d : ℕ) (g₀ : State d) :
    (t : ℕ) → History d t → Fin (t + 1) → State d
  | 0, _ => fun _ => g₀
  | t + 1, ω => Fin.snoc (layoutPath d g₀ t (Fin.init ω)) (run d (t + 1) ω * g₀)

abbrev Environment (d t : ℕ) := Fin (t + 1) → Position d → Position (d + 1)

def outsidePaths (d t : ℕ) (g₀ : State (d + 1))
    (ω : History (d + 1) t) : Environment d t :=
  fun s x => layoutPath (d + 1) g₀ t ω s (outside d x)

def slotPermutation (d t : ℕ) (g₀ : State (d + 1))
    (ω : History (d + 1) t) : Equiv.Perm (Fin (2 ^ d)) :=
  (freeRank d g₀).symm.trans (freeRank d (run (d + 1) t ω * g₀))

def environmentMass (d t : ℕ) (g₀ : State (d + 1)) : Environment d t → ℝ :=
  fairMass (outsidePaths d t g₀)

def conditionalLaw (d t : ℕ) (g₀ : State (d + 1))
    (e : Environment d t) (g : Equiv.Perm (Fin (2 ^ d))) : ℝ :=
  fairMass (fun ω : History (d + 1) t =>
    (outsidePaths d t g₀ ω, slotPermutation d t g₀ ω)) (e, g) /
      environmentMass d t g₀ e

def expectedTV (d t : ℕ) (g₀ : State (d + 1)) : ℝ :=
  ∑ e, environmentMass d t g₀ e *
    tv (conditionalLaw d t g₀ e)
      (fun _ => 1 / (Nat.factorial (2 ^ d) : ℝ))

def worstConditionalTV (d t : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (expectedTV d t)

def twoHalfL : ℕ := 2 ^ 23

def twoHalfP : ℝ := 1 - 1 / (((2 : ℕ) : ℝ) * (twoHalfL : ℝ))

def twoHalfC : ℝ :=
  -(1 / ((8 : ℕ) : ℝ)) *
    Real.logb ((2 : ℕ) : ℝ) ((3 + twoHalfP) / ((4 : ℕ) : ℝ))

def twoHalfB : ℕ := ⌈((10 : ℕ) : ℝ) / twoHalfC⌉₊

end Revealed

namespace Thorp.Conditional
open scoped Classical

def exposedPath {ι : Type*} (d : ℕ) (e : ι → Position d) :
    (t : ℕ) → History d t → Fin (t + 1) → ι → Position d
  | 0, _ => fun _ => e
  | t + 1, ω => Fin.snoc (exposedPath d e t (Fin.init ω)) (run d (t + 1) ω ∘ e)

@[simp] lemma exposedPath_last {ι : Type*} (d t : ℕ) (e : ι → Position d)
    (ω : History d t) : exposedPath d e t ω (Fin.last t) = run d t ω ∘ e := by
  cases t with
  | zero => simp [exposedPath, run_zero]
  | succ t => exact Fin.snoc_last _ _

@[simp] lemma exposedPath_snoc {ι : Type*} (d t : ℕ) (e : ι → Position d)
    (ω : History d t) (c : Coins d) :
    exposedPath d e (t + 1) (Fin.snoc ω c) =
      Fin.snoc (exposedPath d e t ω) ((step d c * run d t ω) ∘ e) := by
  simp only [exposedPath, Fin.init_snoc, run_snoc]

theorem flow_path_joint_identity {ι : Type*} (d : ℕ) (v : RawState (d + 1))
    (e : ι → Position (d + 1)) (he : ∀ i, v.free (e i) = false)
    (t : ℕ) (f : (Fin (t + 1) → ι → Position (d + 1)) → Position (d + 1) → ℝ) :
    mean (fun ω : History (d + 1) t =>
      ∑ x, v.weight x * f (exposedPath (d + 1) e t ω) (run (d + 1) t ω x)) =
    mean (fun ω : History (d + 1) t =>
      ∑ y, (rawIterate d v t ω).weight y * f (exposedPath (d + 1) e t ω) y) := by
  induction t with
  | zero => simp only [run_zero, rawIterate]; rfl
  | succ t ih =>
    let F (p : Fin (t + 1) → ι → Position (d + 1)) (x : Position (d + 1)) : ℝ :=
      mean (fun c : Coins (d + 1) =>
        f (Fin.snoc p ((step (d + 1) c) ∘ p (Fin.last t))) (step (d + 1) c x))
    have hleft :
        mean (fun ω : History (d + 1) (t + 1) =>
          ∑ x, v.weight x * f (exposedPath (d + 1) e (t + 1) ω)
            (run (d + 1) (t + 1) ω x)) =
        mean (fun ω : History (d + 1) t =>
          ∑ x, v.weight x * F (exposedPath (d + 1) e t ω) (run (d + 1) t ω x)) := by
      rw [mean_history_succ]
      apply mean_congr
      intro ω
      simp only [run_snoc, exposedPath_snoc]
      rw [mean_sum]
      simp_rw [mean_const_mul]
      simp only [F, exposedPath_last]
      rfl
    have hright :
        mean (fun ω : History (d + 1) (t + 1) =>
          ∑ y, (rawIterate d v (t + 1) ω).weight y *
            f (exposedPath (d + 1) e (t + 1) ω) y) =
        mean (fun ω : History (d + 1) t =>
          ∑ y, (rawIterate d v t ω).weight y * F (exposedPath (d + 1) e t ω) y) := by
      rw [mean_history_succ]
      apply mean_congr
      intro ω
      simp only [exposedPath_snoc, rawIterate_snoc]
      change mean (fun c : Position d → Bool =>
        ∑ y, physicalFlow d (rawIterate d v t ω).free (rawIterate d v t ω).weight c y *
          f (Fin.snoc (exposedPath (d + 1) e t ω)
            ((step (d + 1) c) ∘ ((run (d + 1) t ω) ∘ e))) y) = _
      rw [physicalFlow_joint d (rawIterate d v t ω).free (rawIterate d v t ω).weight
        ((run (d + 1) t ω) ∘ e) (by
          intro i
          simp only [Function.comp_apply, rawIterate_free, Equiv.symm_apply_apply]
          exact he i) (fun e' y => f (Fin.snoc (exposedPath (d + 1) e t ω) e') y)]
      rw [mean_sum]
      simp_rw [mean_const_mul]
      simp only [F, exposedPath_last]
      rfl
    exact hleft.trans ((ih F).trans hright.symm)

end Thorp.Conditional

namespace Thorp.Conditional
open scoped Classical

theorem halfDensity_after_step_sixteen (d : ℕ) (v : RawState (d + 1))
    (c : Coins (d + 1)) (h : Bool)
    (hm : Fintype.card (Position (d + 1)) ≤ 16 * freeCount v.free)
    (hc : freeCount v.free ≤ 4 * pairHalfCount (v.free ∘ (splitPosition d).symm) c h) :
    (1 / 32 : ℝ) ≤ startHalfDensity d (rawNext d v c) h := by
  unfold startHalfDensity
  rw [halfCount_after_step]
  have hn : Fintype.card (Position (d + 1)) = 2 * Fintype.card (Position d) := by
    simp [Fintype.card_pi, Fintype.card_bool, Fintype.card_fin, pow_succ, Nat.mul_comm]
  rw [hn] at hm
  have hm' : (2 : ℝ) * Fintype.card (Position d) ≤ 16 * (freeCount v.free : ℝ) := by
    exact_mod_cast hm
  have hc' : (freeCount v.free : ℝ) ≤
      4 * (pairHalfCount (v.free ∘ (splitPosition d).symm) c h : ℝ) := by exact_mod_cast hc
  apply (le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := Position d))).mpr
  nlinarith

theorem expectedNoise_dimension_sixteen (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * freeCount v.free) :
    expectedNoise (d + 1) v (d + 2) ≤ (31 / 32 : ℝ) * expectedEnergy (d + 1) v (d + 2) +
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
  let B := v.free ∘ (splitPosition (d + 1)).symm
  let bad (c : Coins (d + 2)) : Prop :=
    4 * pairHalfCount B c false < pairFreeCount B ∨
    4 * pairHalfCount B c true < pairFreeCount B
  have hlocal (c : Coins (d + 2)) :
      expectedNoise (d + 1) (nextState (d + 1) v c) (d + 1) ≤
      (31 / 32 : ℝ) * expectedEnergy (d + 1) (nextState (d + 1) v c) (d + 1) +
        (if bad c then 1 else 0) := by
    by_cases hc : bad c
    · rw [ite_eq_left hc]
      have hle := expectedNoise_le_energy (d + 1) (nextState (d + 1) v c) (d + 1)
      have hone := expectedEnergy_le_one (d + 1) (nextState (d + 1) v c) (d + 1)
      linarith
    · rw [ite_eq_right hc, add_zero]
      have hb (h : Bool) : (1 / 32 : ℝ) ≤
          startHalfDensity (d + 1) (nextState (d + 1) v c).raw h := by
        apply halfDensity_after_step_sixteen (d + 1) v.raw c h hm
        have hf : ¬ 4 * pairHalfCount B c false < freeCount v.free := by
          simpa only [B, pairFreeCount_physical] using not_or.mp hc |>.1
        have ht : ¬ 4 * pairHalfCount B c true < freeCount v.free := by
          simpa only [B, pairFreeCount_physical] using not_or.mp hc |>.2
        change freeCount v.free ≤ 4 * pairHalfCount B c h
        cases h
        · exact Nat.le_of_not_gt hf
        · exact Nat.le_of_not_gt ht
      convert noise_bound_balanced_state d (nextState (d + 1) v c) (1 / 32) hb using 1; norm_num
  have hmean := mean_le_mean hlocal
  rw [mean_add, mean_const_mul, ← expectedNoise_first, ← expectedEnergy_first] at hmean
  have hbad := pair_both_half_balance B
  have hbad' : mean (fun c : Coins (d + 2) => if bad c then (1 : ℝ) else 0) ≤
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
    change mean (fun c : Position (d + 1) → Bool => if bad c then (1 : ℝ) else 0) ≤ _
    simpa only [bad, B, pairFreeCount_physical] using hbad
  exact hmean.trans (add_le_add (le_refl _) hbad')

theorem expectedNoise_bound_sixteen (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * freeCount v.free)
    (s : ℕ) (hs : d + 2 ≤ s) :
    expectedNoise (d + 1) v s ≤ (31 / 32 : ℝ) * expectedEnergy (d + 1) v s +
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Nat.add_comm (d + 2) a, expectedNoise_add, expectedEnergy_add]
  have he := mean_le_mean (fun ω : History (d + 2) a =>
    expectedNoise_dimension_sixteen d (iterateState (d + 1) v a ω)
      (by simpa only [iterateState_freeCount] using hm))
  simpa only [iterateState_freeCount, mean_add, mean_const_mul, mean_const] using he

lemma sixteen_density_geometric_choice : (63 / 64 : ℝ) ^ 398 ≤ (1 / 2 : ℝ) ^ 8 := by
  have h : (63 / 64 : ℝ) ^ 199 ≤ 1 / 16 := by norm_num
  calc
    _ = ((63 / 64 : ℝ) ^ 199) ^ 2 := by rw [← pow_mul]
    _ ≤ (1 / 16 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    _ = _ := by norm_num

theorem expectedEnergy_decay_sixteen (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * freeCount v.free) (t : ℕ) :
    expectedEnergy (d + 1) v t ≤
      (63 / 64 : ℝ) ^ t / (63 / 64 : ℝ) ^ (2 * (d + 2)) +
        64 * (9 / 10 : ℝ) ^ freeCount v.free := by
  have he := scalar_decay (d + 2) (expectedEnergy (d + 1) v)
    (expectedNoise (d + 1) v) (1 / 32) (63 / 64)
    (2 * (9 / 10 : ℝ) ^ freeCount v.free)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by positivity) (expectedEnergy_le_one (d + 1) v)
    (expectedEnergy_recurrence (d + 1) v)
    (by intro s hs; convert expectedNoise_bound_sixteen d v hm s hs using 1; norm_num) t
  convert he using 1; ring

theorem expectedEnergy_400 (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * freeCount v.free) :
    expectedEnergy (d + 1) v (400 * (d + 2)) ≤
      (1 / 2 : ℝ) ^ (8 * (d + 2)) + 64 * (9 / 10 : ℝ) ^ freeCount v.free := by
  have he := expectedEnergy_decay_sixteen d v hm (400 * (d + 2))
  have hp : (63 / 64 : ℝ) ^ (400 * (d + 2)) / (63 / 64 : ℝ) ^ (2 * (d + 2)) =
      (63 / 64 : ℝ) ^ (398 * (d + 2)) := by
    have hn : 400 * (d + 2) = 398 * (d + 2) + 2 * (d + 2) := by omega
    rw [hn, pow_add, mul_div_cancel_right₀ _ (by positivity)]
  rw [hp] at he
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (63 / 64) ^ 398)
    sixteen_density_geometric_choice (d + 2)
  rw [← pow_mul, ← pow_mul] at hpow
  exact he.trans (add_le_add hpow (le_refl _))

theorem centeredPoint_energy_400 (d : ℕ) (B : Position (d + 2) → Bool)
    (tag : Position (d + 2)) (ht : B tag = true)
    (hm : Fintype.card (Position (d + 2)) ≤ 16 * freeCount B) :
    expectedEnergy (d + 1) (initialState (d + 2) B tag ht) (400 * (d + 2)) ≤
      (1 / 2 : ℝ) ^ (8 * (d + 2)) + 64 * (9 / 10 : ℝ) ^ freeCount B :=
  expectedEnergy_400 d _ hm

end Thorp.Conditional

namespace Thorp.Fourier
open scoped Classical InnerProductSpace
variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]

def realProduct : (n : ℕ) → (Fin n → G → ℝ) → G → ℝ
  | 0, _ => fun g => if g = 1 then 1 else 0
  | n + 1, ν => realConv (ν (Fin.last n)) (realProduct n (Fin.init ν))

lemma realProduct_nonneg (n : ℕ) (ν : Fin n → G → ℝ) (hν : ∀ i g, 0 ≤ ν i g) :
    ∀ g, 0 ≤ realProduct n ν g := by
  induction n with
  | zero => intro g; simp only [realProduct]; split_ifs <;> norm_num
  | succ n ih => exact realConv_nonneg _ _ (hν _) (ih _ (fun i => hν i.castSucc))

lemma realProduct_sum (n : ℕ) (ν : Fin n → G → ℝ) (hν : ∀ i, ∑ g, ν i g = 1) :
    ∑ g, realProduct n ν g = 1 := by
  induction n with
  | zero => simp [realProduct]
  | succ n ih => rw [realProduct, realConv_sum, hν, ih (Fin.init ν) (fun i => hν i.castSucc), mul_one]

lemma realConv_character (χ : G →* ℂ) (μ ν : G → ℝ) :
    (∑ g, (realConv μ ν g : ℂ) * χ g) =
      (∑ g, (μ g : ℂ) * χ g) * (∑ g, (ν g : ℂ) * χ g) := by
  simp only [realConv, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  have he := Equiv.sum_comp (Equiv.mulLeft h)
    (fun g => (μ h : ℂ) * (ν (h⁻¹ * g) : ℂ) * χ g)
  change (∑ g, (μ h : ℂ) * (ν (h⁻¹ * (h * g)) : ℂ) * χ (h * g)) = _ at he
  simp only [inv_mul_cancel_left, map_mul] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  ring

lemma realProduct_character_bound (χ : G →* ℂ) (n : ℕ) (ν : Fin n → G → ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hb : ∀ i, ‖∑ g, (ν i g : ℂ) * χ g‖ ≤ η) :
    ‖∑ g, (realProduct n ν g : ℂ) * χ g‖ ≤ η ^ n := by
  induction n with
  | zero => simp [realProduct, apply_ite (fun x : ℝ => (x : ℂ)), ite_mul]
  | succ n ih =>
    rw [realProduct, realConv_character, norm_mul, pow_succ']
    exact mul_le_mul (hb _) (ih _ (fun i => hb i.castSucc)) (norm_nonneg _) hη

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [finiteDimensional_ℂ_E : FiniteDimensional ℂ E]

lemma realProduct_transform_norm (ρ : Representation ℂ G E) (n : ℕ)
    (ν : Fin n → G → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hν : ∀ i v, ‖integrated ρ (fun g => (ν i g : ℂ)) v‖ ^ 2 ≤ R * ‖v‖ ^ 2)
    (v : E) :
    ‖integrated ρ (fun g => (realProduct n ν g : ℂ)) v‖ ^ 2 ≤ R ^ n * ‖v‖ ^ 2 := by
  let retained_finiteDimensional_ℂ_E := finiteDimensional_ℂ_E
  induction n with
  | zero =>
    have he : (fun g : G => (realProduct 0 ν g : ℂ)) = delta := by
      funext g; simp only [realProduct, delta]; split_ifs <;> norm_num
    rw [he, integrated_delta]
    simp
  | succ n ih =>
    rw [realProduct, integrated_realConv, Module.End.mul_apply, pow_succ' R n, mul_assoc]
    exact (hν (Fin.last n) _).trans (mul_le_mul_of_nonneg_left (ih (Fin.init ν) (fun i => hν i.castSucc)) hR)

lemma realProduct_hsSq (ρ : Representation ℂ G E) (n : ℕ)
    (ν : Fin n → G → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hν : ∀ i v, ‖integrated ρ (fun g => (ν i g : ℂ)) v‖ ^ 2 ≤ R * ‖v‖ ^ 2) :
    hsSq (integrated ρ (fun g => (realProduct n ν g : ℂ))) ≤
      (Module.finrank ℂ E : ℝ) * R ^ n := by
  unfold hsSq
  calc
    _ ≤ ∑ i, R ^ n * ‖stdOrthonormalBasis ℂ E i‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => realProduct_transform_norm ρ n ν R hR hν _)
    _ = _ := by simp [(stdOrthonormalBasis ℂ E).norm_eq_one, mul_comm]

lemma Family.eight_sequence_transform_bound (F : Family H) (ρ : Representation ℂ G E)
    [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hd : 0 < Module.finrank ℂ E) (ψ : (Fin 8 → H) →* G)
    (ν : Fin 8 → G → ℝ) (B : ℝ)
    (hν : ∀ j g, 0 ≤ ν j g) (h1 : ∀ j, ∑ g, ν j g = 1) (hB : 0 ≤ B)
    (hcoset : ∀ j i g, ∑ h, ν j (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card H : ℝ) / Fintype.card G) :
    (Module.finrank ℂ E : ℝ) * hsSq (integrated ρ (fun g => (realProduct 8 ν g : ℂ))) ≤
      (8 * B * F.reciprocalSum)^8 * ((Module.finrank ℂ E : ℝ)^2)⁻¹ := by
  let S : ℝ := ∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ 8 ≤ Module.finrank ℂ E), (F.degree b : ℝ)^2
  let R : ℝ := 8 * B * S / Module.finrank ℂ E
  have hD : (0 : ℝ) < Module.finrank ℂ E := by exact_mod_cast hd
  have hR : 0 ≤ R := by dsimp [R, S]; positivity
  have hA (j : Fin 8) (v : E) : ‖integrated ρ (fun g => (ν j g : ℂ)) v‖ ^ 2 ≤ R * ‖v‖ ^ 2 := by
    simpa only [R, S, Fintype.card_fin, Nat.cast_ofNat] using
      F.integrated_norm_sq ρ hu (Nat.ne_of_gt hd) ψ (ν j) B (hν j) (h1 j) hB (by
        intro i g
        convert hcoset j i g using 1
        apply Finset.sum_congr rfl
        intro h _
        congr 4
        exact Subsingleton.elim _ _) v
  calc
    _ ≤ (Module.finrank ℂ E : ℝ) * ((Module.finrank ℂ E : ℝ) * R^8) :=
      mul_le_mul_of_nonneg_left (realProduct_hsSq ρ 8 ν R hR hA) hD.le
    _ = (Module.finrank ℂ E : ℝ)^2 * R^8 := by ring
    _ ≤ _ := eight_degree_bound _ hD B S F.reciprocalSum (F.low_degree_sq _)

end Thorp.Fourier

namespace Thorp.Fourier
variable {G : Type} [Group G] [Fintype G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma centered_probability_trivial (ρ : Representation ℂ G E) (hρ : ∀ g v, ρ g v = v)
    (ν : G → ℝ) (h1 : ∑ g, ν g = 1) :
    integrated ρ (fun g => ((ν g - (Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ)) = 0 := by
  rw [integrated_real_sub]
  have htr (g : G) (v : E) : ρ g v = (1 : ℂ) • v := by simpa using hρ g v
  rw [integrated_scalar ρ (fun _ => 1) htr, integrated_scalar ρ (fun _ => 1) htr]
  simp only [mul_one, ← Complex.ofReal_sum, h1, Complex.ofReal_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [Complex.ofReal_inv, Complex.ofReal_natCast, Fintype.card_ne_zero]

lemma centered_probability_character (ρ : Representation ℂ G E) (χ : G → ℂ)
    (hρ : ∀ g v, ρ g v = χ g • v) (hχ : ∑ g, χ g = 0) (ν : G → ℝ) :
    integrated ρ (fun g => ((ν g - (Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ)) =
      (∑ g, (ν g : ℂ) * χ g) • LinearMap.id := by
  rw [integrated_real_sub, integrated_scalar ρ χ hρ, integrated_scalar ρ χ hρ]
  simp only [← Finset.mul_sum, hχ, mul_zero, zero_smul, sub_zero]

end Thorp.Fourier

namespace Thorp.Specht
open scoped Classical
open Thorp.Fourier
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nontrivial α]

theorem permutation_eight_sequence_bound (hn : 16 ≤ Fintype.card α)
    (ψ : (Fin 8 → Equiv.Perm β) →* Equiv.Perm α) (ν : Fin 8 → Equiv.Perm α → ℝ) (B : ℝ)
    (hν : ∀ j g, 0 ≤ ν j g) (h1 : ∀ j, ∑ g, ν j g = 1) (hB : 0 ≤ B)
    (hcoset : ∀ j i g, ∑ h, ν j (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card (Equiv.Perm β) : ℝ) / Fintype.card (Equiv.Perm α)) :
    (∑ g, |realProduct 8 ν g - (Fintype.card (Equiv.Perm α) : ℝ)⁻¹|)^2 ≤
      2 * ‖∑ g, (realProduct 8 ν g : ℂ) * complexSign g‖^2 +
        (8 * B * (permutationFamily β).reciprocalSum)^8 * exceptionalReciprocalSum (Fintype.card α) := by
  let F := permutationFamily α
  let H := permutationFamily β
  let bias : ℝ := ‖∑ g, (realProduct 8 ν g : ℂ) * complexSign g‖^2
  let K : ℝ := (8 * B * H.reciprocalSum)^8
  let f : Equiv.Perm α → ℝ := fun g => realProduct 8 ν g - (Fintype.card (Equiv.Perm α) : ℝ)⁻¹
  have hp (p : F.Index) :
      (F.degree p : ℝ) * hsSq (integrated (F.rep p) (fun g => (f g : ℂ))) ≤
        if defect p = 0 then bias else K * inverseDegree p := by
    by_cases hz : defect p = 0
    · rw [ite_eq_left hz]
      obtain ⟨hd, htr | hsign⟩ := permutation_exceptional_action (α:=α) p hz
      · have hh := centered_probability_trivial (F.rep p) htr (realProduct 8 ν) (realProduct_sum _ _ h1)
        change integrated (F.rep p) (fun g => (f g : ℂ)) = 0 at hh
        rw [hh]
        simp only [hsSq, LinearMap.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
          Finset.sum_const_zero, mul_zero]
        exact pow_nonneg (norm_nonneg _) _
      · have hh := centered_probability_character (F.rep p) complexSign hsign (complexSign_sum (α:=α)) (realProduct 8 ν)
        change integrated (F.rep p) (fun g => (f g : ℂ)) = _ at hh
        rw [hh, hsSq_scalar]
        change (F.degree p : ℝ) * ((F.degree p : ℝ) * ‖∑ g, (realProduct 8 ν g : ℂ) * complexSign g‖^2) ≤ bias
        rw [show F.degree p = 1 from hd]
        simp only [Nat.cast_one, one_mul]
        exact le_rfl
    · rw [ite_eq_right hz]
      have hgt : 1 < Module.finrank ℂ (F.Space p) := degree_gt_one p hn (Nat.pos_of_ne_zero hz)
      have hu := integrated_uniform_real (F.rep p) hgt
      have he : integrated (F.rep p) (fun g => (f g : ℂ)) =
          integrated (F.rep p) (fun g => (realProduct 8 ν g : ℂ)) := by
        rw [show (fun g => (f g : ℂ)) = (fun g => ((realProduct 8 ν g - (Fintype.card (Equiv.Perm α) : ℝ)⁻¹ : ℝ) : ℂ)) from rfl,
          integrated_real_sub, hu, sub_zero]
      rw [he]
      exact H.eight_sequence_transform_bound (F.rep p) (F.unitary p) (by omega) ψ ν B hν h1 hB hcoset
  have hs : (∑ p : NShape (Fintype.card α), if defect p = 0 then bias else K * inverseDegree p) =
      (Fintype.card {p : NShape (Fintype.card α) // defect p = 0} : ℝ) * bias +
        K * exceptionalReciprocalSum (Fintype.card α) := by
    rw [show (Fintype.card {p : NShape (Fintype.card α) // defect p = 0} : ℝ) * bias =
      ∑ p : NShape (Fintype.card α), if defect p = 0 then bias else 0 by rw [← Finset.sum_filter]; simp [Fintype.card_subtype],
      exceptionalReciprocalSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hz : defect p = 0
    · simp only [hz, lt_self_iff_false, ↓reduceIte, mul_zero, add_zero]
    · simp only [hz, Nat.pos_of_ne_zero hz, ↓reduceIte, zero_add]
  have hc : (Fintype.card {p : NShape (Fintype.card α) // defect p = 0} : ℝ) ≤ 2 := by
    exact_mod_cast exceptional_count (Fintype.card α)
  calc
    _ ≤ ∑ p, (F.degree p : ℝ) * hsSq (integrated (F.rep p) (fun g => (f g : ℂ))) := F.l1_sq_le_parseval f
    _ ≤ ∑ p : NShape (Fintype.card α), if defect p = 0 then bias else K * inverseDegree p :=
      Finset.sum_le_sum (fun p _ => hp p)
    _ = _ := hs
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg _) _)) le_rfl

end Thorp.Specht

namespace Thorp.Conditional
open scoped Classical

theorem tagged_path_deviation_identity {ι : Type*} (d : ℕ)
    (B : Position (d + 1) → Bool) (tag : Position (d + 1)) (ht : B tag = true)
    (e : ι → Position (d + 1)) (he : ∀ i, B (e i) = false)
    (t : ℕ) (f : (Fin (t + 1) → ι → Position (d + 1)) → Position (d + 1) → ℝ) :
    mean (fun ω : History (d + 1) t =>
      f (exposedPath (d + 1) e t ω) (run (d + 1) t ω tag) -
        (1 / (freeCount B : ℝ)) *
          (∑ y, if B ((run (d + 1) t ω).symm y) then f (exposedPath (d + 1) e t ω) y else 0)) =
    mean (fun ω : History (d + 1) t =>
      ∑ y, (iterateState d (initialState (d + 1) B tag ht) t ω).weight y *
        f (exposedPath (d + 1) e t ω) y) := by
  have hh := flow_path_joint_identity d (initialState (d + 1) B tag ht).raw e he t f
  simp_rw [← iterateState_raw] at hh
  change (mean (fun ω : History (d + 1) t => ∑ x,
    (initialState (d + 1) B tag ht).weight x * f (exposedPath (d + 1) e t ω) (run (d + 1) t ω x))) = _ at hh
  change _ = mean (fun ω : History (d + 1) t => ∑ y,
    (iterateState d (initialState (d + 1) B tag ht) t ω).raw.weight y * f (exposedPath (d + 1) e t ω) y)
  rw [← hh]
  apply mean_congr
  intro ω
  change _ = ∑ x, centeredPoint B tag x * f (exposedPath (d + 1) e t ω) (run (d + 1) t ω x)
  rw [centeredPoint_test]
  congr 2
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp (run (d + 1) t ω)
      (fun y => if B ((run (d + 1) t ω).symm y) then f (exposedPath (d + 1) e t ω) y else 0)).symm

theorem tagged_path_deviation_bound {ι : Type*} (d : ℕ)
    (B : Position (d + 1) → Bool) (tag : Position (d + 1)) (ht : B tag = true)
    (e : ι → Position (d + 1)) (he : ∀ i, B (e i) = false)
    (t : ℕ) (f : (Fin (t + 1) → ι → Position (d + 1)) → Position (d + 1) → ℝ)
    (hf : ∀ e' y, |f e' y| ≤ 1) :
    |mean (fun ω : History (d + 1) t =>
      f (exposedPath (d + 1) e t ω) (run (d + 1) t ω tag) -
        (1 / (freeCount B : ℝ)) *
          (∑ y, if B ((run (d + 1) t ω).symm y) then f (exposedPath (d + 1) e t ω) y else 0))| ≤
    Real.sqrt ((Fintype.card (Position (d + 1)) : ℝ) *
      expectedEnergy d (initialState (d + 1) B tag ht) t) := by
  rw [tagged_path_deviation_identity d B tag ht e he]
  exact mean_weighted_test_le _ _ (fun ω y => hf _ y)

end Thorp.Conditional

namespace Thorp.Conditional
open scoped Classical

def avoid {ι α : Type*} (e : ι → α) : α → Bool := fun x => decide (∀ i, e i ≠ x)

@[simp] lemma avoid_exposed {ι α : Type*} (e : ι → α) (i : ι) :
    avoid e (e i) = false := by simp [avoid]

lemma avoid_perm {ι α : Type*} (e : ι → α) (g : Equiv.Perm α) (x : α) :
    avoid (g ∘ e) x = avoid e (g.symm x) := by
  simp [avoid, ← g.eq_symm_apply]

lemma avoid_equiv_left {ι α β : Type*} (L : Sum ι α ≃ β) {k : ℕ}
    (e : Fin k → α) (i : ι) :
    avoid (Sum.elim (fun j => L (.inl j)) (fun j => L (.inr (e j)))) (L (.inl i)) = false := by
  exact avoid_exposed (Sum.elim (fun j => L (.inl j)) (fun j => L (.inr (e j)))) (Sum.inl i)

lemma avoid_equiv_right {ι α β : Type*} [DecidableEq α] (L : Sum ι α ≃ β) {k : ℕ}
    (e : Fin k → α) (a : α) :
    avoid (Sum.elim (fun j => L (.inl j)) (fun j => L (.inr (e j)))) (L (.inr a)) = freeOf e a := by
  simp [avoid, freeOf, Sum.forall]

lemma freeCount_avoid_equiv {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    [DecidableEq α] (L : Sum ι α ≃ β) {k : ℕ} (e : Fin k → α) :
    freeCount (avoid (Sum.elim (fun i => L (.inl i)) (fun j => L (.inr (e j))))) =
      freeCount (freeOf e) := by
  apply Nat.cast_injective (R := ℝ)
  rw [← sum_free_indicator, ← sum_free_indicator]
  rw [← Equiv.sum_comp L]
  simp only [Fintype.sum_sum_type, avoid_equiv_left, Bool.false_eq_true, ↓reduceIte,
    Finset.sum_const_zero, avoid_equiv_right, zero_add]

def pathComplete {ι α : Type*} [Fintype α] {t k : ℕ}
    (f : (Fin (t + 1) → ι → α) → (Fin (k + 1) → α) → ℝ)
    (p : Fin (t + 1) → ι → α) (z : Fin k → α) : ℝ :=
  let B := avoid (Sum.elim (p (Fin.last t)) z)
  (1 / (freeCount B : ℝ)) * ∑ y, if B y then f p (Fin.snoc z y) else 0

lemma pathComplete_bound {ι α : Type*} [Fintype α] {t k : ℕ}
    (f : (Fin (t + 1) → ι → α) → (Fin (k + 1) → α) → ℝ)
    (hf : ∀ p z, |f p z| ≤ 1) (p : Fin (t + 1) → ι → α) (z : Fin k → α) :
    |pathComplete f p z| ≤ 1 := by
  let B := avoid (Sum.elim (p (Fin.last t)) z)
  change |(1 / (freeCount B : ℝ)) * ∑ y, if B y then f p (Fin.snoc z y) else 0| ≤ 1
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (freeCount B : ℝ))]
  have hs : |∑ y, if B y then f p (Fin.snoc z y) else 0| ≤ freeCount B := by
    calc
      _ ≤ ∑ y, |if B y then f p (Fin.snoc z y) else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, if B y then (1 : ℝ) else 0 := Finset.sum_le_sum (fun y _ => by
        cases h : B y <;> simp only [Bool.false_eq_true, ↓reduceIte, abs_zero,
          le_refl] ; exact hf _ _)
      _ = _ := sum_free_indicator _
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 1 / (freeCount B : ℝ))
  by_cases hz : freeCount B = 0
  · simp [hz]
  · have hn : (freeCount B : ℝ) ≠ 0 := by exact_mod_cast hz
    simpa [hn] using hh

lemma exposedPath_comp {ι κ : Type*} (d : ℕ) (e : ι → Position d) (a : κ → ι)
    (t : ℕ) (ω : History d t) :
    (fun s => exposedPath d e t ω s ∘ a) = exposedPath d (e ∘ a) t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext s j
    refine Fin.lastCases ?_ (fun i => ?_) s
    · simp [exposedPath, Function.comp_def]
    · simpa only [exposedPath, Fin.snoc_castSucc, Function.comp_apply] using
        congrFun (congrFun (ih (Fin.init ω)) i) j

end Thorp.Conditional

namespace Thorp.Conditional
open scoped Classical

lemma pathComplete_equiv {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    [DecidableEq α] (L : Sum ι α ≃ β) {t k : ℕ}
    (f : (Fin (t + 1) → ι → β) → (Fin (k + 1) → β) → ℝ)
    (p : Fin (t + 1) → ι → β) (hp : p (Fin.last t) = fun i => L (.inl i))
    (e : Fin k → α) :
    pathComplete f p (fun j => L (.inr (e j))) =
      (1 / (freeCount (freeOf e) : ℝ)) *
        ∑ a, if freeOf e a then f p (Fin.snoc (fun j => L (.inr (e j))) (L (.inr a))) else 0 := by
  unfold pathComplete
  dsimp only
  rw [hp, freeCount_avoid_equiv]
  congr 1
  rw [← Equiv.sum_comp L]
  simp only [Fintype.sum_sum_type, avoid_equiv_left, Bool.false_eq_true, ↓reduceIte,
    Finset.sum_const_zero, avoid_equiv_right, zero_add]

lemma uniform_path_completion {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    [DecidableEq α] (L : Sum ι α ≃ β) {t k : ℕ}
    (f : (Fin (t + 1) → ι → β) → (Fin (k + 1) → β) → ℝ)
    (p : Fin (t + 1) → ι → β) (hp : p (Fin.last t) = fun i => L (.inl i))
    (e : Fin k → α) (tag : α) (ht : freeOf e tag = true) :
    mean (fun σ : Equiv.Perm α =>
      f p (Fin.snoc (fun j => L (.inr (σ (e j)))) (L (.inr (σ tag))))) =
    mean (fun σ : Equiv.Perm α => pathComplete f p (fun j => L (.inr (σ (e j))))) := by
  have hh := uniform_tagged_completion e tag ht
    (fun z y => f p (Fin.snoc (fun j => L (.inr (z j))) (L (.inr y))))
  refine hh.trans ?_
  apply mean_congr
  intro σ
  simpa only [freeCount_perm, Function.comp_apply] using
    (pathComplete_equiv L f p hp (σ ∘ e)).symm

def splitPath {ι α : Type*} {d : ℕ} (L : Sum ι α ≃ Position d)
    (t : ℕ) (ω : History d t) : Fin (t + 1) → ι → Position d :=
  exposedPath d (fun i => L (.inl i)) t ω

def splitTuple {ι α : Type*} {d k : ℕ} (L : Sum ι α ≃ Position d)
    (t : ℕ) (ω : History d t) (e : Fin k → α) : Fin k → Position d :=
  fun j => run d t ω (L (.inr (e j)))

lemma splitTuple_snoc {ι α : Type*} {d k : ℕ} (L : Sum ι α ≃ Position d)
    (t : ℕ) (ω : History d t) (e : Fin k → α) (a : α) :
    splitTuple L t ω (Fin.snoc e a) = Fin.snoc (splitTuple L t ω e) (run d t ω (L (.inr a))) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [splitTuple]

lemma splitPath_last {ι α : Type*} {d : ℕ} (L : Sum ι α ≃ Position d)
    (t : ℕ) (ω : History d t) :
    splitPath L t ω (Fin.last t) = fun i => run d t ω (L (.inl i)) := exposedPath_last _ _ _ _

end Thorp.Conditional

namespace Thorp.Conditional
open scoped Classical

lemma splitPath_completion_error {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (d : ℕ) (L : Sum ι α ≃ Position (d + 1)) {k : ℕ} (e : Fin k → α)
    (tag : α) (ht : freeOf e tag = true) (t : ℕ)
    (f : (Fin (t + 1) → ι → Position (d + 1)) → (Fin (k + 1) → Position (d + 1)) → ℝ)
    (hf : ∀ p z, |f p z| ≤ 1) :
    |mean (fun ω : History (d + 1) t => f (splitPath L t ω) (splitTuple L t ω (Fin.snoc e tag))) -
      mean (fun ω : History (d + 1) t => pathComplete f (splitPath L t ω) (splitTuple L t ω e))| ≤
    Real.sqrt ((Fintype.card (Position (d + 1)) : ℝ) *
      expectedEnergy d (initialState (d + 1)
        (avoid (Sum.elim (fun i => L (.inl i)) (fun j => L (.inr (e j))))) (L (.inr tag))
        (by rwa [avoid_equiv_right])) t) := by
  let z : Sum ι (Fin k) → Position (d + 1) :=
    Sum.elim (fun i => L (.inl i)) (fun j => L (.inr (e j)))
  let B := avoid z
  let F (p : Fin (t + 1) → Sum ι (Fin k) → Position (d + 1)) (y : Position (d + 1)) :=
    f (fun s i => p s (.inl i)) (Fin.snoc (fun j => p (Fin.last t) (.inr j)) y)
  have hh := tagged_path_deviation_bound d B (L (.inr tag))
    (by exact (avoid_equiv_right L e tag).trans ht) z (avoid_exposed z) t F
    (fun p y => hf _ _)
  have ho (ω : History (d + 1) t) :
      (fun s i => exposedPath (d + 1) z t ω s (.inl i)) = splitPath L t ω :=
    exposedPath_comp (d + 1) z Sum.inl t ω
  have he (ω : History (d + 1) t) :
      (fun j => exposedPath (d + 1) z t ω (Fin.last t) (.inr j)) = splitTuple L t ω e := by
    rw [exposedPath_last]
    rfl
  have hF (ω : History (d + 1) t) (y : Position (d + 1)) :
      F (exposedPath (d + 1) z t ω) y = f (splitPath L t ω) (Fin.snoc (splitTuple L t ω e) y) := by
    change f _ _ = _
    rw [ho, he]
  have hB (ω : History (d + 1) t) (y : Position (d + 1)) :
      B ((run (d + 1) t ω).symm y) =
        avoid (Sum.elim (splitPath L t ω (Fin.last t)) (splitTuple L t ω e)) y := by
    rw [splitPath_last]
    have hz : Sum.elim (fun i => run (d + 1) t ω (L (.inl i))) (splitTuple L t ω e) =
        (run (d + 1) t ω) ∘ z := by
      funext i
      cases i <;> rfl
    rw [hz]
    exact (avoid_perm z (run (d + 1) t ω) y).symm
  have hcount (ω : History (d + 1) t) :
      freeCount (avoid (Sum.elim (splitPath L t ω (Fin.last t)) (splitTuple L t ω e))) = freeCount B := by
    rw [splitPath_last]
    change freeCount (avoid (Sum.elim (fun i => (L.trans (run (d + 1) t ω)) (.inl i))
      (fun j => (L.trans (run (d + 1) t ω)) (.inr (e j))))) = _
    rw [freeCount_avoid_equiv, show freeCount B = freeCount (freeOf e) from freeCount_avoid_equiv L e]
  simp_rw [hF, hB] at hh
  rw [← mean_sub]
  convert hh using 1
  congr 1
  apply mean_congr
  intro ω
  rw [splitTuple_snoc]
  congr 1
  exact congrArg (fun n : ℕ => (1 / (n : ℝ)) *
    ∑ y, if avoid (Sum.elim (splitPath L t ω (Fin.last t)) (splitTuple L t ω e)) y then
      f (splitPath L t ω) (Fin.snoc (splitTuple L t ω e) y) else 0) (hcount ω)

end Thorp.Conditional

namespace Thorp.Conditional
open scoped Classical

lemma uniform_splitTuple_completion {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    {d : ℕ} (L : Sum ι α ≃ Position d) {k : ℕ} (e : Fin (k + 1) → α)
    (he : Function.Injective e) (t : ℕ) (ω : History d t)
    (f : (Fin (t + 1) → ι → Position d) → (Fin (k + 1) → Position d) → ℝ) :
    mean (fun σ : Equiv.Perm α => f (splitPath L t ω) (splitTuple L t ω (σ ∘ e))) =
      mean (fun σ : Equiv.Perm α => pathComplete f (splitPath L t ω) (splitTuple L t ω (σ ∘ Fin.init e))) := by
  have ht : freeOf (Fin.init e) (e (Fin.last k)) = true := by
    apply (freeOf_true _ _).mpr
    intro i hi
    exact Fin.castSucc_ne_last i (he hi)
  have hh := uniform_path_completion (L.trans (run d t ω)) f (splitPath L t ω)
    (splitPath_last L t ω) (Fin.init e) (e (Fin.last k)) ht
  convert hh using 1
  · apply mean_congr
    intro σ
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [splitTuple, Fin.init_def]
  · rfl

theorem splitTuple_test_400 {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (d m : ℕ) (hm : Fintype.card (Position (d + 2)) ≤ 16 * m)
    (L : Sum ι α ≃ Position (d + 2)) (k : ℕ) (hk : k + m ≤ Fintype.card α)
    (e : Fin k → α) (he : Function.Injective e)
    (f : (Fin (400 * (d + 2) + 1) → ι → Position (d + 2)) → (Fin k → Position (d + 2)) → ℝ)
    (hf : ∀ p z, |f p z| ≤ 1) :
    |mean (fun ω : History (d + 2) (400 * (d + 2)) =>
        f (splitPath L _ ω) (splitTuple L _ ω e)) -
      mean (fun ω : History (d + 2) (400 * (d + 2)) =>
        mean (fun σ : Equiv.Perm α => f (splitPath L _ ω) (splitTuple L _ ω (σ ∘ e))))| ≤
    (k : ℝ) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m)) := by
  induction k with
  | zero =>
    have hz (ω : History (d + 2) (400 * (d + 2))) (σ : Equiv.Perm α) :
        splitTuple L _ ω (σ ∘ e) = splitTuple L _ ω e := Subsingleton.elim _ _
    simp_rw [hz, mean_const]
    simp
  | succ k ih =>
    have he0 : Function.Injective (Fin.init e) := by
      intro i j hij
      exact Fin.castSucc_inj.mp (he hij)
    have ht : freeOf (Fin.init e) (e (Fin.last k)) = true := by
      apply (freeOf_true _ _).mpr
      intro i hi
      exact Fin.castSucc_ne_last i (he hi)
    let B := avoid (Sum.elim (fun i => L (.inl i)) (fun j => L (.inr (Fin.init e j))))
    have htag : B (L (.inr (e (Fin.last k)))) = true := (avoid_equiv_right _ _ _).trans ht
    have hcount : m ≤ freeCount B := by
      rw [show freeCount B = freeCount (freeOf (Fin.init e)) from freeCount_avoid_equiv L (Fin.init e),
        freeCount_freeOf _ he0]
      omega
    have henergy := centeredPoint_energy_400 d B (L (.inr (e (Fin.last k)))) htag (by omega)
    have hpower : (9 / 10 : ℝ) ^ freeCount B ≤ (9 / 10 : ℝ) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcount
    have hz := splitPath_completion_error (d + 1) L (Fin.init e) (e (Fin.last k)) ht
      (400 * (d + 2)) f hf
    rw [Fin.snoc_init_self] at hz
    have hestimate :
        Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
          expectedEnergy (d + 1) (initialState (d + 2) B (L (.inr (e (Fin.last k)))) htag)
            (400 * (d + 2))) ≤
        Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
          ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m)) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact henergy.trans (by linarith)
    have hnext := ih (by omega) (Fin.init e) he0 (pathComplete f) (pathComplete_bound f hf)
    simp_rw [uniform_splitTuple_completion L e he _ _ f]
    have htri := abs_sub_le
      (mean (fun ω : History (d + 2) (400 * (d + 2)) => f (splitPath L _ ω) (splitTuple L _ ω e)))
      (mean (fun ω : History (d + 2) (400 * (d + 2)) => pathComplete f (splitPath L _ ω) (splitTuple L _ ω (Fin.init e))))
      (mean (fun ω : History (d + 2) (400 * (d + 2)) =>
        mean (fun σ : Equiv.Perm α => pathComplete f (splitPath L _ ω) (splitTuple L _ ω (σ ∘ Fin.init e)))))
    have hz' := hz.trans hestimate
    push_cast
    nlinarith

end Thorp.Conditional

namespace Thorp.Conditional
open scoped Classical

theorem splitTuple_joint_tv_400 {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (d m : ℕ) (hm : Fintype.card (Position (d + 2)) ≤ 16 * m)
    (L : Sum ι α ≃ Position (d + 2)) (k : ℕ) (hk : k + m ≤ Fintype.card α)
    (e : Fin k → α) (he : Function.Injective e) :
    tv (fairMass (fun ω : History (d + 2) (400 * (d + 2)) =>
        (splitPath L _ ω, splitTuple L _ ω e)))
      (fairMass (fun a : History (d + 2) (400 * (d + 2)) × Equiv.Perm α =>
        (splitPath L _ a.1, splitTuple L _ a.1 (a.2 ∘ e)))) ≤
    (k : ℝ) / 2 * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m)) := by
  have hh := fairMass_tv_le_of_test
    (fun ω : History (d + 2) (400 * (d + 2)) => (splitPath L _ ω, splitTuple L _ ω e))
    (fun a : History (d + 2) (400 * (d + 2)) × Equiv.Perm α =>
        (splitPath L _ a.1, splitTuple L _ a.1 (a.2 ∘ e)))
    ((k : ℝ) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m))) (by
      intro f hf
      rw [mean_prod]
      exact splitTuple_test_400 d m hm L k hk e he (fun p z => f (p, z)) (fun p z => hf _))
  convert hh using 1 ; first | rfl | ring

end Thorp.Conditional

namespace Revealed.Split
open scoped Classical
variable {ι α β : Type*}

lemma perm_preserves_right (g : Equiv.Perm (Sum ι α))
    (hg : ∀ i, g (.inl i) = .inl i) (a : α) : ∃ b, g (.inr a) = .inr b := by
  cases h : g (.inr a) with
  | inl i =>
    have hh := g.injective (h.trans (hg i).symm)
    exact False.elim (Sum.inr_ne_inl hh)
  | inr b => exact ⟨b, rfl⟩

def rightPart (g : Equiv.Perm (Sum ι α)) (hg : ∀ i, g (.inl i) = .inl i) : Equiv.Perm α :=
  Equiv.ofBijective (fun a => (perm_preserves_right g hg a).choose) (by
    constructor
    · intro a b h
      apply Sum.inr_injective
      apply g.injective
      rw [(perm_preserves_right g hg a).choose_spec,
        (perm_preserves_right g hg b).choose_spec]
      exact congrArg Sum.inr h
    · intro b
      obtain ⟨x, hx⟩ := g.surjective (.inr b)
      cases x with
      | inl i => rw [hg i] at hx; exact False.elim (Sum.inl_ne_inr hx)
      | inr a =>
        refine ⟨a, ?_⟩
        apply Sum.inr_injective
        exact (perm_preserves_right g hg a).choose_spec.symm.trans hx)

lemma rightPart_spec (g : Equiv.Perm (Sum ι α)) (hg : ∀ i, g (.inl i) = .inl i) (a : α) :
    g (.inr a) = .inr (rightPart g hg a) := (perm_preserves_right g hg a).choose_spec

def relative (L M : Sum ι α ≃ β) (h : ∀ i, L (.inl i) = M (.inl i)) : Equiv.Perm α :=
  rightPart (L.trans M.symm) (fun i => by simp only [Equiv.trans_apply, h, Equiv.symm_apply_apply])

lemma relative_spec (L M : Sum ι α ≃ β) (h : ∀ i, L (.inl i) = M (.inl i)) (a : α) :
    M (.inr (relative L M h a)) = L (.inr a) := by
  have hh := rightPart_spec (L.trans M.symm) (fun i => by simp only [Equiv.trans_apply, h, Equiv.symm_apply_apply]) a
  exact (congrArg M hh).symm.trans (M.apply_symm_apply _)

lemma relative_self (L : Sum ι α ≃ β) (h : ∀ i, L (.inl i) = L (.inl i)) : relative L L h = 1 := by
  ext a
  apply Sum.inr_injective
  apply L.injective
  exact relative_spec L L h a

lemma relative_unique (L M : Sum ι α ≃ β) (h : ∀ i, L (.inl i) = M (.inl i))
    (g : Equiv.Perm α) (hg : ∀ a, M (.inr (g a)) = L (.inr a)) : relative L M h = g := by
  ext a
  apply Sum.inr_injective
  apply M.injective
  exact (relative_spec L M h a).trans (hg a).symm

lemma relative_factor (L M : Sum ι α ≃ β) (h : ∀ i, L (.inl i) = M (.inl i)) :
    (Equiv.sumCongr (Equiv.refl ι) (relative L M h)).trans M = L := by
  ext x
  cases x with
  | inl i => exact (h i).symm
  | inr a => exact relative_spec L M h a

lemma relative_pre (L M : Sum ι α ≃ β) (h : ∀ i, L (.inl i) = M (.inl i)) (g : Equiv.Perm α) :
    relative ((Equiv.sumCongr (Equiv.refl ι) g).trans L) M h = relative L M h * g := by
  apply relative_unique
  intro a
  exact relative_spec L M h (g a)

lemma relative_post (L M : Sum ι α ≃ β) (h : ∀ i, L (.inl i) = M (.inl i)) (W : Equiv.Perm β) :
    relative (L.trans W) (M.trans W) (fun i => congrArg W (h i)) = relative L M h := by
  apply relative_unique
  intro a
  exact congrArg W (relative_spec L M h a)

abbrev Outside (ι α β : Type*) := {o : ι → β // ∃ L : Sum ι α ≃ β, ∀ i, L (.inl i) = o i}

def outside (L : Sum ι α ≃ β) : Outside ι α β := ⟨fun i => L (.inl i), ⟨L, fun _ => rfl⟩⟩

def sectionFrame (o : Outside ι α β) : Sum ι α ≃ β := o.property.choose

lemma sectionFrame_spec (o : Outside ι α β) (i : ι) : sectionFrame o (.inl i) = o.val i :=
  o.property.choose_spec i

@[simp] lemma outside_sectionFrame (o : Outside ι α β) : outside (sectionFrame o) = o := by
  apply Subtype.ext
  funext i
  exact sectionFrame_spec o i

@[simp] lemma outside_pre (L : Sum ι α ≃ β) (g : Equiv.Perm α) :
    outside ((Equiv.sumCongr (Equiv.refl ι) g).trans L) = outside L := by
  rfl

def assignment (L : Sum ι α ≃ β) : Equiv.Perm α :=
  relative L (sectionFrame (outside L)) (fun i => (sectionFrame_spec (outside L) i).symm)

lemma assignment_factor (L : Sum ι α ≃ β) :
    (Equiv.sumCongr (Equiv.refl ι) (assignment L)).trans (sectionFrame (outside L)) = L :=
  relative_factor _ _ _

@[simp] lemma assignment_sectionFrame (o : Outside ι α β) : assignment (sectionFrame o) = 1 := by
  unfold assignment
  simp only [outside_sectionFrame]
  exact relative_self _ _

lemma assignment_pre (L : Sum ι α ≃ β) (g : Equiv.Perm α) :
    assignment ((Equiv.sumCongr (Equiv.refl ι) g).trans L) = assignment L * g := by
  unfold assignment
  exact relative_pre _ _ _ _

def nextOutside (o : Outside ι α β) (W : Equiv.Perm β) : Outside ι α β :=
  outside ((sectionFrame o).trans W)

def increment (o : Outside ι α β) (W : Equiv.Perm β) : Equiv.Perm α :=
  assignment ((sectionFrame o).trans W)

lemma outside_post (L : Sum ι α ≃ β) (W : Equiv.Perm β) :
    outside (L.trans W) = nextOutside (outside L) W := by
  apply Subtype.ext
  funext i
  exact congrArg W (sectionFrame_spec (outside L) i).symm

lemma assignment_post (L : Sum ι α ≃ β) (W : Equiv.Perm β) :
    assignment (L.trans W) = increment (outside L) W * assignment L := by
  conv_lhs => rw [← assignment_factor L]
  rw [Equiv.trans_assoc, assignment_pre]
  rfl

end Revealed.Split

namespace Revealed.Split
open scoped Classical
variable {ι α β : Type*}

def frameFor (fallback : Sum ι α ≃ β) (o : ι → β) : Sum ι α ≃ β :=
  if h : ∃ L : Sum ι α ≃ β, ∀ i, L (.inl i) = o i then sectionFrame ⟨o, h⟩ else fallback

@[simp] lemma frameFor_outside (fallback L : Sum ι α ≃ β) :
    frameFor fallback (outside L).val = sectionFrame (outside L) := by
  unfold frameFor
  rw [dite_eq_left (outside L).property]

def indexRight [Nonempty α] (L : Sum ι α ≃ β) (x : β) : α :=
  match L.symm x with | .inl _ => Classical.arbitrary α | .inr a => a

@[simp] lemma indexRight_apply [Nonempty α] (L : Sum ι α ≃ β) (a : α) :
    indexRight L (L (.inr a)) = a := by simp [indexRight]

lemma indexRight_assignment [Nonempty α] (L : Sum ι α ≃ β) (a : α) :
    indexRight (sectionFrame (outside L)) (L (.inr a)) = assignment L a := by
  rw [← relative_spec L (sectionFrame (outside L)) (fun i => (sectionFrame_spec (outside L) i).symm) a]
  exact indexRight_apply _ _

lemma indexRight_tuple [Nonempty α] {k : ℕ} (L : Sum ι α ≃ β)
    (W : Equiv.Perm β) (a : Fin k → α) :
    (fun j => indexRight (frameFor L (fun i => W (L (.inl i)))) (W (L (.inr (a j))))) =
      assignment (L.trans W) ∘ a := by
  funext j
  have hframe := frameFor_outside L (L.trans W)
  dsimp only [outside, Equiv.trans_apply] at hframe
  rw [hframe]
  exact indexRight_assignment (L.trans W) (a j)

end Revealed.Split

namespace Thorp.Conditional
open scoped Classical
open Revealed.Split

lemma mean_perm_comp {α Z : Type*} [Fintype α] [DecidableEq α] (ρ : Equiv.Perm α)
    (e : Z → α) (f : (Z → α) → ℝ) :
    mean (fun σ : Equiv.Perm α => f (ρ ∘ (σ ∘ e))) =
      mean (fun σ : Equiv.Perm α => f (σ ∘ e)) :=
  mean_equiv (Equiv.mulLeft ρ) (fun σ : Equiv.Perm α => f (σ ∘ e))

theorem assignmentTuple_test_400 {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [Nonempty α]
    (d m : ℕ) (hm : Fintype.card (Position (d + 2)) ≤ 16 * m)
    (L : Sum ι α ≃ Position (d + 2)) (k : ℕ) (hk : k + m ≤ Fintype.card α)
    (e : Fin k → α) (he : Function.Injective e)
    (f : (Fin (400 * (d + 2) + 1) → ι → Position (d + 2)) → (Fin k → α) → ℝ)
    (hf : ∀ p z, |f p z| ≤ 1) :
    |mean (fun ω : History (d + 2) (400 * (d + 2)) =>
        f (splitPath L _ ω) ((assignment (L.trans (run (d + 2) _ ω))) ∘ e)) -
      mean (fun ω : History (d + 2) (400 * (d + 2)) =>
        mean (fun σ : Equiv.Perm α => f (splitPath L _ ω) (σ ∘ e)))| ≤
    (k : ℝ) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m)) := by
  let T := 400 * (d + 2)
  let F (p : Fin (T + 1) → ι → Position (d + 2)) (z : Fin k → Position (d + 2)) : ℝ :=
    f p (fun j => indexRight (frameFor L (p (Fin.last T))) (z j))
  have hh := splitTuple_test_400 d m hm L k hk e he F (fun p z => hf _ _)
  have hF (ω : History (d + 2) T) (a : Fin k → α) :
      F (splitPath L T ω) (splitTuple L T ω a) =
        f (splitPath L T ω) (assignment (L.trans (run (d + 2) T ω)) ∘ a) := by
    dsimp only [F, splitTuple]
    rw [splitPath_last, indexRight_tuple]
  dsimp only [T] at hF
  simp_rw [hF] at hh
  have hu (ω : History (d + 2) T) :
      mean (fun σ : Equiv.Perm α => f (splitPath L T ω)
        (assignment (L.trans (run (d + 2) T ω)) ∘ (σ ∘ e))) =
      mean (fun σ : Equiv.Perm α => f (splitPath L T ω) (σ ∘ e)) :=
    mean_perm_comp (assignment (L.trans (run (d + 2) T ω))) e (f (splitPath L T ω))
  dsimp only [T] at hu
  simp_rw [hu] at hh
  exact hh

end Thorp.Conditional

namespace Revealed.Disintegration
open scoped Classical
open Thorp
variable {E G : Type*} [fintype_E : Fintype E] [Fintype G] [nonempty_G : Nonempty G]

def marginal (μ : E × G → ℝ) (e : E) : ℝ := ∑ g, μ (e, g)

def conditional (μ : E × G → ℝ) (e : E) (g : G) : ℝ :=
  if marginal μ e = 0 then (Fintype.card G : ℝ)⁻¹ else μ (e, g) / marginal μ e

lemma marginal_nonneg (μ : E × G → ℝ) (hμ : ∀ x, 0 ≤ μ x) (e : E) :
    0 ≤ marginal μ e := by
  let retained_fintype_E := fintype_E
  let retained_nonempty_G := nonempty_G
  exact Finset.sum_nonneg (fun g _ => hμ (e, g))

lemma point_le_marginal (μ : E × G → ℝ) (hμ : ∀ x, 0 ≤ μ x) (e : E) (g : G) :
    μ (e, g) ≤ marginal μ e := by
  let retained_fintype_E := fintype_E
  let retained_nonempty_G := nonempty_G
  exact Finset.single_le_sum (fun x _ => hμ (e, x)) (Finset.mem_univ g)

lemma conditional_nonneg (μ : E × G → ℝ) (hμ : ∀ x, 0 ≤ μ x) (e : E) (g : G) :
    0 ≤ conditional μ e g := by
  unfold conditional
  split_ifs
  · positivity
  · exact div_nonneg (hμ _) (marginal_nonneg μ hμ e)

lemma conditional_sum (μ : E × G → ℝ) (e : E) : ∑ g, conditional μ e g = 1 := by
  let retained_fintype_E := fintype_E
  by_cases h : marginal μ e = 0
  · simp only [conditional, ite_eq_left h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  · simp only [conditional, ite_eq_right h, ← Finset.sum_div]
    exact div_self h

lemma marginal_mul_conditional (μ : E × G → ℝ) (hμ : ∀ x, 0 ≤ μ x) (e : E) (g : G) :
    marginal μ e * conditional μ e g = μ (e, g) := by
  unfold conditional
  split_ifs with h
  · have hz : μ (e, g) = 0 := le_antisymm ((point_le_marginal μ hμ e g).trans h.le) (hμ _)
    rw [h, hz, zero_mul]
  · exact mul_div_cancel₀ _ h

lemma marginal_sum (μ : E × G → ℝ) : ∑ e, marginal μ e = ∑ x, μ x := by
  let retained_nonempty_G := nonempty_G
  simp only [marginal, Fintype.sum_prod_type]

lemma marginal_fairMass {Ω : Type*} [Fintype Ω] (a : Ω → E) (b : Ω → G) :
    marginal (fairMass (fun ω => (a ω, b ω))) = fairMass a := by
  let retained_fintype_E := fintype_E
  let retained_nonempty_G := nonempty_G
  funext e
  unfold marginal fairMass
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  simp [Prod.mk.injEq, ite_and]

lemma fairMass_prod {Ω Ω' X Y : Type*} [Fintype Ω] [Fintype Ω']
    (a : Ω → X) (b : Ω' → Y) (x : X) (y : Y) :
    fairMass (fun z : Ω × Ω' => (a z.1, b z.2)) (x, y) = fairMass a x * fairMass b y := by
  unfold fairMass
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, Prod.mk.injEq]
  rw [div_mul_div_comm, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω' _
  split_ifs <;> simp_all

lemma tv_joint_scaled {Y : Type*} [Fintype Y] (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (μ ν : E → Y → ℝ) :
    tv (fun a : E × Y => p a.1 * μ a.1 a.2) (fun a => p a.1 * ν a.1 a.2) =
      ∑ e, p e * tv (μ e) (ν e) := by
  simp only [tv, Fintype.sum_prod_type, ← mul_sub, abs_mul, abs_of_nonneg (hp _),
    ← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma average_tv_eq (μ : E × G → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ν : E → G → ℝ) :
    (∑ e, marginal μ e * tv (conditional μ e) (ν e)) =
      tv μ (fun a : E × G => marginal μ a.1 * ν a.1 a.2) := by
  rw [← tv_joint_scaled (marginal μ) (marginal_nonneg μ hμ)]
  congr 1
  funext a
  exact marginal_mul_conditional μ hμ a.1 a.2

end Revealed.Disintegration

namespace Revealed.Disintegration
open scoped Classical
open Thorp
variable {E G Y : Type*} [fintype_E : Fintype E] [Fintype G] [fintype_Y : Fintype Y] [nonempty_G : Nonempty G]

lemma push_preserve_first (μ : E × G → ℝ) (f : G → Y) (e : E) (y : Y) :
    Trim.push μ (fun a => (a.1, f a.2)) (e, y) = ∑ g, if f g = y then μ (e, g) else 0 := by
  let retained_fintype_Y := fintype_Y
  let retained_nonempty_G := nonempty_G
  simp only [Trim.push, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp

lemma marginal_mul_push (μ : E × G → ℝ) (hμ : ∀ x, 0 ≤ μ x) (f : G → Y) (e : E) (y : Y) :
    marginal μ e * Trim.push (conditional μ e) f y = ∑ g, if f g = y then μ (e, g) else 0 := by
  let retained_fintype_Y := fintype_Y
  rw [Trim.push, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  split_ifs
  · exact marginal_mul_conditional μ hμ e g
  · exact mul_zero _

lemma projection_tv_eq (μ : E × G → ℝ) (hμ : ∀ x, 0 ≤ μ x) (f : G → Y) (u : G → ℝ) :
    (∑ e, marginal μ e * tv (Trim.push (conditional μ e) f) (Trim.push u f)) =
      tv (Trim.push μ (fun a => (a.1, f a.2)))
        (fun a : E × Y => marginal μ a.1 * Trim.push u f a.2) := by
  rw [← tv_joint_scaled (marginal μ) (marginal_nonneg μ hμ)]
  congr 1
  funext a
  rw [push_preserve_first, marginal_mul_push μ hμ]

lemma conditional_projection_le_of_test {Ω : Type*} [Fintype Ω]
    (a : Ω → E) (b : Ω → G) (r : G → Y) (C : ℝ)
    (h : ∀ f : E × Y → ℝ, (∀ z, |f z| ≤ 1) →
      |Conditional.mean (fun ω => f (a ω, r (b ω))) -
        Conditional.mean (fun ω => Conditional.mean (fun g : G => f (a ω, r g)))| ≤ C) :
    (∑ e, marginal (fairMass (fun ω => (a ω, b ω))) e *
      tv (Trim.push (conditional (fairMass (fun ω => (a ω, b ω))) e) r) (fairMass r)) ≤ C / 2 := by
  have hh := Conditional.fairMass_tv_le_of_test
    (fun ω : Ω => (a ω, r (b ω))) (fun z : Ω × G => (a z.1, r z.2)) C (by
      intro f hf
      rw [Conditional.mean_prod]
      exact h f hf)
  have hu : Trim.push (fun _ : G => (Fintype.card G : ℝ)⁻¹) r = fairMass r := by
    rw [Trim.uniform_eq_fairMass_id, Trim.push_fairMass]
    rfl
  have hp := projection_tv_eq (fairMass (fun ω => (a ω, b ω))) (fairMass_nonneg _) r
    (fun _ : G => (Fintype.card G : ℝ)⁻¹)
  rw [hu] at hp
  rw [hp, Trim.push_fairMass, marginal_fairMass]
  simp_rw [← fairMass_prod a r]
  exact hh

end Revealed.Disintegration

namespace Thorp.Conditional
open scoped Classical
open Revealed.Split Revealed.Disintegration

def frameJoint {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] {d : ℕ}
    (L : Sum ι α ≃ Position d) (t : ℕ) :
    (Fin (t + 1) → ι → Position d) × Equiv.Perm α → ℝ :=
  fairMass (fun ω : History d t => (splitPath L t ω, assignment (L.trans (run d t ω))))

def frameKernel {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] {d : ℕ}
    (L : Sum ι α ≃ Position d) (t : ℕ) :
    (Fin (t + 1) → ι → Position d) → Equiv.Perm α → ℝ := conditional (frameJoint L t)

lemma frameJoint_nonneg {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] {d : ℕ}
    (L : Sum ι α ≃ Position d) (t : ℕ) (x) : 0 ≤ frameJoint L t x := fairMass_nonneg _ _

lemma frameKernel_nonneg {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] {d : ℕ}
    (L : Sum ι α ≃ Position d) (t : ℕ) (p g) : 0 ≤ frameKernel L t p g :=
  conditional_nonneg _ (frameJoint_nonneg L t) p g

lemma frameKernel_sum {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] {d : ℕ}
    (L : Sum ι α ≃ Position d) (t : ℕ) (p) : ∑ g, frameKernel L t p g = 1 :=
  conditional_sum _ p

lemma frameKernel_tuple_bound {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    [Nonempty α] {d t k : ℕ} (L : Sum ι α ≃ Position d) (e : Fin k → α) (C : ℝ)
    (h : ∀ (f : (Fin (t + 1) → ι → Position d) → (Fin k → α) → ℝ),
      (∀ p z, |f p z| ≤ 1) →
      |mean (fun ω : History d t => f (splitPath L t ω) (assignment (L.trans (run d t ω)) ∘ e)) -
        mean (fun ω : History d t => mean (fun g : Equiv.Perm α => f (splitPath L t ω) (g ∘ e)))| ≤ C) :
    (∑ p, marginal (frameJoint L t) p *
      tv (Trim.push (frameKernel L t p) (fun g : Equiv.Perm α => g ∘ e))
        (fairMass (fun g : Equiv.Perm α => g ∘ e))) ≤ C / 2 := by
  exact conditional_projection_le_of_test
    (fun ω : History d t => splitPath L t ω)
    (fun ω : History d t => assignment (L.trans (run d t ω)))
    (fun g : Equiv.Perm α => g ∘ e) C (fun f hf => h (fun p z => f (p,z)) (fun p z => hf _))

theorem frameKernel_marginal_400 {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [Nonempty α]
    (d m : ℕ) (hm : Fintype.card (Position (d + 2)) ≤ 16 * m)
    (L : Sum ι α ≃ Position (d + 2)) (k : ℕ) (hk : k + m ≤ Fintype.card α)
    (e : Fin k → α) (he : Function.Injective e) :
    (∑ p, marginal (frameJoint L (400 * (d + 2))) p *
      tv (Trim.push (frameKernel L (400 * (d + 2)) p) (fun g : Equiv.Perm α => g ∘ e))
        (fairMass (fun g : Equiv.Perm α => g ∘ e))) ≤
    (k : ℝ) / 2 * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m)) := by
  have hh := frameKernel_tuple_bound L e
    ((k : ℝ) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 64 * (9 / 10 : ℝ) ^ m)))
    (assignmentTuple_test_400 d m hm L k hk e he)
  exact hh.trans_eq (by ring)

end Thorp.Conditional

end

end OAI
