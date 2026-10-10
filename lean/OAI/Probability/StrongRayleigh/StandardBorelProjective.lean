import Mathlib

namespace OAI

universe u_1

noncomputable section

open MeasureTheory ProbabilityTheory Finset Preorder

namespace Problem336AdditiveD139.StandardBorelProjective

variable {E : Type u_1} [MeasurableSpace E]

def splitPrefix (n : ℕ) : ((Iic (n + 1)) → E) ≃ᵐ (((Iic n) → E) × E) where
  toFun x := (frestrictLe₂ (π := fun _ : ℕ => E) (Nat.le_succ n) x, x ⟨n + 1, mem_Iic.mpr le_rfl⟩)
  invFun p i := if h : i.1 ≤ n then p.1 ⟨i.1, mem_Iic.mpr h⟩ else p.2
  left_inv x := by
    funext i
    dsimp
    split_ifs with hi
    · rfl
    · congr 1
      apply Subtype.ext
      change n + 1 = i.1
      have := mem_Iic.mp i.2
      omega
  right_inv p := by
    apply Prod.ext
    · funext i
      change (if h : i.1 ≤ n then p.1 ⟨i.1, mem_Iic.mpr h⟩ else p.2) = p.1 i
      rw [dite_eq_left (mem_Iic.mp i.2)]
    · simp
  measurable_toFun := by
    exact (measurable_frestrictLe₂ (X := fun _ : ℕ => E) (Nat.le_succ n)).prodMk
      (measurable_pi_apply (⟨n + 1, mem_Iic.mpr le_rfl⟩ : Iic (n + 1)))
  measurable_invFun := by
    apply Measurable.of_eval
    intro i
    dsimp
    split_ifs
    · exact measurable_fst.eval
    · exact measurable_snd

@[simp] theorem splitPrefix_comp_frestrictLe (n : ℕ) :
    (splitPrefix (E := E) n) ∘ frestrictLe (π := fun _ : ℕ => E) (n + 1) =
      fun x : ℕ → E => (frestrictLe (π := fun _ : ℕ => E) n x, x (n + 1)) := by
  funext x
  apply Prod.ext
  · funext i; rfl
  · rfl

theorem map_prefix_compProd_eq_map_pair
    (κ : (n : ℕ) → Kernel ((Iic n) → E) E) [∀ n, IsMarkovKernel (κ n)]
    (P₀ : ProbabilityMeasure ((Iic (0 : ℕ)) → E)) (n : ℕ) :
    ((Kernel.traj κ 0) ∘ₘ (P₀ : Measure _)).map (frestrictLe (π := fun _ : ℕ => E) n) ⊗ₘ κ n =
      ((Kernel.traj κ 0) ∘ₘ (P₀ : Measure _)).map
        (fun x : ℕ → E => (frestrictLe (π := fun _ : ℕ => E) n x, x (n + 1))) := by
  rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ (by fun_prop),
    Kernel.traj_map_frestrictLe, Measure.comp_assoc, Measure.map_comp _ _ (by fun_prop)]
  congr with x₀ : 1
  rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod,
    Kernel.map_apply _ (by fun_prop), Kernel.partialTraj_compProd_eq_map_traj zero_le]

theorem exists_probabilityMeasure_prefix [StandardBorelSpace E] [Nonempty E]
    (P : (n : ℕ) → ProbabilityMeasure ((Iic n) → E))
    (hP : ∀ n, (P (n + 1) : Measure _).map (frestrictLe₂ (π := fun _ : ℕ => E) (Nat.le_succ n)) =
      (P n : Measure _)) :
    ∃ μ : ProbabilityMeasure (ℕ → E),
      ∀ n, (μ : Measure _).map (frestrictLe (π := fun _ : ℕ => E) n) = (P n : Measure _) := by
  let R (n : ℕ) : ProbabilityMeasure (((Iic n) → E) × E) :=
    (P (n + 1)).map (splitPrefix n)
  let κ (n : ℕ) : Kernel ((Iic n) → E) E := (R n : Measure _).condKernel
  let hκ : ∀ n, IsMarkovKernel (κ n) := fun n => by dsimp [κ]; infer_instance
  let μ : ProbabilityMeasure (ℕ → E) :=
    ⟨(Kernel.traj κ 0) ∘ₘ (P 0 : Measure _), inferInstance⟩
  have hR (n : ℕ) : (R n : Measure (((Iic n) → E) × E)).fst =
      (P n : Measure ((Iic n) → E)) := by
    change ((P (n + 1) : Measure ((Iic (n + 1)) → E)).map (splitPrefix (E := E) n)).map Prod.fst = _
    rw [Measure.map_map measurable_fst (splitPrefix n).measurable]
    exact hP n
  refine ⟨μ, ?_⟩
  intro n
  induction n with
  | zero =>
      change ((Kernel.traj κ 0) ∘ₘ (P 0 : Measure _)).map (frestrictLe (π := fun _ : ℕ => E) 0) = _
      rw [Measure.map_comp _ _ (measurable_frestrictLe 0),
        Kernel.traj_map_frestrictLe, Kernel.partialTraj_self]
      simp
  | succ n ih =>
      apply MeasurableEquiv.map_measurableEquiv_injective (splitPrefix n)
      rw [Measure.map_map (splitPrefix n).measurable (measurable_frestrictLe _),
        splitPrefix_comp_frestrictLe]
      change ((Kernel.traj κ 0) ∘ₘ (P 0 : Measure _)).map
        (fun x : ℕ → E => (frestrictLe (π := fun _ : ℕ => E) n x, x (n + 1))) = (R n : Measure _)
      rw [← map_prefix_compProd_eq_map_pair κ (P 0) n]
      change (μ : Measure _).map (frestrictLe (π := fun _ : ℕ => E) n) ⊗ₘ κ n = (R n : Measure _)
      rw [ih, ← hR n]
      exact (R n : Measure (((Iic n) → E) × E)).disintegrate (κ n)

end Problem336AdditiveD139.StandardBorelProjective

end

end OAI
