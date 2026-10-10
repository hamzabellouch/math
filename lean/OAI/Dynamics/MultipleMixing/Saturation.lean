import OAI.Dynamics.MultipleMixing.Arrays

namespace OAI

namespace Rokhlin

open MeasureTheory ProbabilityTheory
universe u

open MeasureTheory ProbabilityTheory Finset Function Filter Preorder
open scoped ENNReal

namespace SequentialLimit


section

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, StandardBorelSpace (X n)] [∀ n, Nonempty (X n)]
  (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
  (θ : ∀ n, X (n + 1) → X n) (hθ : ∀ n, Measurable (θ n))

noncomputable def step (n : ℕ) : Kernel (X n) (X (n + 1)) :=
  condDistrib id (θ n) (μ (n + 1))

instance step_markov (n : ℕ) : IsMarkovKernel (step μ θ n) := by
  dsimp [step]
  infer_instance

noncomputable def transition (n : ℕ) : Kernel (∀ i : Finset.Iic n, X i) (X (n + 1)) :=
  (step μ θ n).comap (fun x => x ⟨n, by simp⟩) (by fun_prop)

instance transition_markov (n : ℕ) : IsMarkovKernel (transition μ θ n) := by
  dsimp [transition]
  infer_instance

noncomputable def law : Measure (∀ n, X n) := Kernel.trajMeasure (μ 0) (transition μ θ)

instance law_probability : IsProbabilityMeasure (law μ θ) := by
  dsimp [law]
  infer_instance

lemma hasCondDistrib_step (n : ℕ) :
    HasCondDistrib (fun x : ∀ n, X n => x (n + 1)) (fun x => x n)
      (step μ θ n) (law μ θ) := by
  have h : HasCondDistrib (fun x : ∀ n, X n => x (n + 1))
      (frestrictLe n) (transition μ θ n) (law μ θ) :=
    ⟨by fun_prop, Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm⟩
  exact h.comp_right

lemma map_zero : (law μ θ).map (fun x => x 0) = μ 0 := by
  have hrestrict : (law μ θ).map (frestrictLe 0) =
      (μ 0).map (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => X i)).symm := by
    rw [law, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  have h := congrArg (fun ρ => ρ.map (fun x : ∀ i : Finset.Iic 0, X i => x ⟨0, by simp⟩)) hrestrict
  erw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  change (law μ θ).map (fun x => x 0) = (μ 0).map id at h
  simpa only [Measure.map_id] using h

variable (hp : ∀ n, (μ (n + 1)).map (θ n) = μ n)

include hθ hp

lemma map_eval (n : ℕ) : (law μ θ).map (fun x => x n) = μ n := by
  induction n with
  | zero => exact map_zero μ θ
  | succ n ih =>
    have h := congrArg Measure.snd (hasCondDistrib_step μ θ n).map_eq
    rw [Measure.snd_map_prodMk (by fun_prop) (by fun_prop), Measure.snd_compProd, ih] at h
    rw [← hp n, step, condDistrib_comp_map (hθ n).aemeasurable aemeasurable_id,
      Measure.map_id] at h
    exact h

lemma map_pair (n : ℕ) :
    (law μ θ).map (fun x => (x n, x (n + 1))) =
      (μ (n + 1)).map (fun x => (θ n x, x)) := by
  rw [(hasCondDistrib_step μ θ n).map_eq, map_eval μ θ hθ hp n,
    ← hp n, step, compProd_map_condDistrib (hθ n).aemeasurable aemeasurable_id]
  rfl

lemma ae_compatible (n : ℕ) : ∀ᵐ x ∂law μ θ, θ n (x (n + 1)) = x n := by
  have h : ∀ᵐ p ∂(law μ θ).map (fun x => (x n, x (n + 1))), θ n p.2 = p.1 := by
    rw [map_pair μ θ hθ hp n]
    exact (ae_map_iff (by fun_prop) (measurableSet_eq_fun ((hθ n).comp measurable_snd) measurable_fst)).mpr (Filter.Eventually.of_forall (by simp))
  exact (ae_map_iff (by fun_prop) (measurableSet_eq_fun ((hθ n).comp measurable_snd) measurable_fst)).mp h

lemma ae_all_compatible : ∀ᵐ x ∂law μ θ, ∀ n, θ n (x (n + 1)) = x n := by
  simpa only [ae_all_iff] using fun n => ae_compatible μ θ hθ hp n

theorem exists_law : ∃ ρ : Measure (∀ n, X n), IsProbabilityMeasure ρ ∧
    (∀ n, ρ.map (fun x => x n) = μ n) ∧
    (∀ᵐ x ∂ρ, ∀ n, θ n (x (n + 1)) = x n) :=
  ⟨law μ θ, inferInstance, map_eval μ θ hθ hp, ae_all_compatible μ θ hθ hp⟩

end
section


variable {X : ℕ → Type*}
    (θ : ∀ n, X (n + 1) → X n)

def bond {n m : ℕ} (h : n ≤ m) : X m → X n :=
  Nat.leRecOn (C := fun j => X j → X n) h (fun {j} f => f ∘ θ j) id

@[simp] lemma bond_self (n : ℕ) : bond θ (le_refl n) = id := by
  exact Nat.leRecOn_self _

lemma bond_succ {n m : ℕ} (h : n ≤ m) :
    bond θ (h.trans (Nat.le_succ m)) = bond θ h ∘ θ m := by
  exact Nat.leRecOn_succ h _

variable [∀ n, MeasurableSpace (X n)]

lemma measurable_bond (hθ : ∀ n, Measurable (θ n)) {n m : ℕ} (h : n ≤ m) :
    Measurable (bond θ h) := by
  induction m, h using Nat.le_induction with
  | base => simp only [bond_self]; exact measurable_id
  | succ m h ih => rw [bond_succ]; exact ih.comp (hθ m)

omit [∀ n, MeasurableSpace (X n)] in
lemma bond_apply_of_compatible {x : ∀ n, X n}
    (hx : ∀ n, θ n (x (n + 1)) = x n) {n m : ℕ} (h : n ≤ m) :
    bond θ h (x m) = x n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih => rw [bond_succ]; simpa only [Function.comp_apply, hx m] using ih

lemma map_restrict_of_compatible (hθ : ∀ n, Measurable (θ n))
    {ρ : Measure (∀ n, X n)}
    (hc : ∀ᵐ x ∂ρ, ∀ n, θ n (x (n + 1)) = x n)
    (I : Finset ℕ) (m : ℕ) (hm : ∀ i ∈ I, i ≤ m) :
    ρ.map I.restrict = (ρ.map (fun x => x m)).map
      (fun x (i : I) => bond θ (hm i i.2) x) := by
  rw [Measure.map_map (Measurable.of_eval (fun (i : I) =>
    measurable_bond θ hθ (hm i i.2))) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [hc] with x hx
  funext i
  exact (bond_apply_of_compatible θ hx (hm i i.2)).symm

theorem unique_of_compatible (hθ : ∀ n, Measurable (θ n))
    {ρ σ : Measure (∀ n, X n)} [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hρ : ∀ᵐ x ∂ρ, ∀ n, θ n (x (n + 1)) = x n)
    (hσ : ∀ᵐ x ∂σ, ∀ n, θ n (x (n + 1)) = x n)
    (hmap : ∀ n, ρ.map (fun x => x n) = σ.map (fun x => x n)) : ρ = σ := by
  let P (I : Finset ℕ) := σ.map I.restrict
  have hP : ∀ I, IsFiniteMeasure (P I) := fun I => by
    dsimp [P]; infer_instance
  let := hP
  have hρP : IsProjectiveLimit ρ P := by
    intro I
    rw [map_restrict_of_compatible θ hθ hρ I (I.sup id)
      (fun i hi => Finset.le_sup (f := id) hi),
      hmap (I.sup id)]
    exact (map_restrict_of_compatible θ hθ hσ I (I.sup id)
      (fun i hi => Finset.le_sup (f := id) hi)).symm
  exact hρP.unique (fun _ => rfl)


end


variable {X Y : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    [∀ n, MeasurableSpace (Y n)] [∀ n, StandardBorelSpace (Y n)]
    {ρ : Measure (∀ n, X n)} {σ : Measure (∀ n, Y n)}
    [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    {θ : ∀ n, X (n + 1) → X n} {ψ : ∀ n, Y (n + 1) → Y n}
    (hψ : ∀ n, Measurable (ψ n))
    (f : ∀ n, X n → Y n) (hf : ∀ n, Measurable (f n))

include hψ hf

theorem map_coordinatewise
    (hρ : ∀ᵐ x ∂ρ, ∀ n, θ n (x (n + 1)) = x n)
    (hσ : ∀ᵐ y ∂σ, ∀ n, ψ n (y (n + 1)) = y n)
    (hc : ∀ n, ∀ᵐ x ∂ρ.map (fun x => x (n + 1)),
      ψ n (f (n + 1) x) = f n (θ n x))
    (hm : ∀ n, (ρ.map (fun x => x n)).map (f n) = σ.map (fun y => y n)) :
    ρ.map (fun x n => f n (x n)) = σ := by
  have hF : Measurable (fun (x : ∀ n, X n) n => f n (x n)) :=
    Measurable.of_eval (fun n => (hf n).comp (measurable_pi_apply n))
  have hc' : ∀ᵐ x ∂ρ, ∀ n, ψ n (f (n + 1) (x (n + 1))) =
      f n (θ n (x (n + 1))) := by
    rw [ae_all_iff]
    intro n
    exact ae_of_ae_map (measurable_pi_apply (n + 1)).aemeasurable (hc n)
  refine unique_of_compatible ψ hψ ?_ hσ ?_
  · apply ae_map_iff hF.aemeasurable ?_ |>.mpr
    · filter_upwards [hρ, hc'] with x hx hcx n
      rw [hcx n, hx n]
    · simpa only [Set.ofPred_forall, Function.comp_def] using MeasurableSet.iInter (fun n =>
        measurableSet_eq_fun ((hψ n).comp (measurable_pi_apply (n + 1)))
          (measurable_pi_apply n))
  · intro n
    rw [Measure.map_map (measurable_pi_apply n) hF,
      ← hm n, Measure.map_map (hf n) (by fun_prop)]
    rfl


end SequentialLimit

namespace InverseSystems

section
open Rokhlin.SequentialLimit

variable {X : ℕ → Type*}

abbrev Path (θ : ∀ n, X (n + 1) → X n) :=
  {x : ∀ n, X n // ∀ n, θ n (x (n + 1)) = x n}

def eval (θ : ∀ n, X (n + 1) → X n) (n : ℕ) : Path θ → X n := fun x => x.val n

@[fun_prop] lemma measurable_eval {θ : ∀ n, X (n + 1) → X n}
    [∀ n, MeasurableSpace (X n)] (n : ℕ) : Measurable (eval θ n) :=
  (measurable_pi_apply n).comp measurable_subtype_coe

variable [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
  (θ : ∀ n, X (n + 1) → X n) (hθ : ∀ n, Measurable (θ n))

include hθ in
lemma measurableSet_path : MeasurableSet {x : ∀ n, X n | ∀ n, θ n (x (n + 1)) = x n} := by
  simpa only [Set.ofPred_forall, Function.comp_def] using MeasurableSet.iInter (fun n =>
    measurableSet_eq_fun ((hθ n).comp (measurable_pi_apply (n + 1))) (measurable_pi_apply n))

include hθ in
lemma standardBorel_path : StandardBorelSpace (Path θ) :=
  (measurableSet_path θ hθ).standardBorel

variable [∀ n, Nonempty (X n)] (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
  (hp : ∀ n, (μ (n + 1)).map (θ n) = μ n)

noncomputable def law : Measure (Path θ) :=
  (SequentialLimit.law μ θ).comap Subtype.val

include hθ hp in
lemma law_probability : IsProbabilityMeasure (law θ μ) := by
  apply (MeasurableEmbedding.subtype_coe (measurableSet_path θ hθ)).isProbabilityMeasure_comap
  filter_upwards [ae_all_compatible μ θ hθ hp] with x hx
  exact ⟨⟨x, hx⟩, rfl⟩

include hθ hp in
lemma map_val_law : (law θ μ).map Subtype.val = SequentialLimit.law μ θ := by
  exact (map_comap_subtype_coe (measurableSet_path θ hθ)
    (SequentialLimit.law μ θ)).trans
    (Measure.restrict_eq_self_of_ae_mem (ae_all_compatible μ θ hθ hp))

include hθ hp in
lemma map_eval_law (n : ℕ) : (law θ μ).map (eval θ n) = μ n := by
  change (law θ μ).map ((fun x : ∀ n, X n => x n) ∘ Subtype.val) = _
  rw [← Measure.map_map (measurable_pi_apply n) measurable_subtype_coe,
    map_val_law θ hθ μ hp, map_eval μ θ hθ hp]

include hθ hp in
lemma nonempty_path : Nonempty (Path θ) := by
  let := law_probability θ hθ μ hp
  exact nonempty_of_isProbabilityMeasure (law θ μ)

omit [∀ n, Nonempty (X n)] in
include hθ in
lemma unique {ρ σ : Measure (Path θ)} [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hmap : ∀ n, ρ.map (eval θ n) = σ.map (eval θ n)) : ρ = σ := by
  apply (MeasurableEmbedding.subtype_coe (measurableSet_path θ hθ)).map_injective
  apply unique_of_compatible θ hθ
  · exact (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_path θ hθ)).mpr (Filter.Eventually.of_forall Subtype.property)
  · exact (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_path θ hθ)).mpr (Filter.Eventually.of_forall Subtype.property)
  · intro n
    rw [Measure.map_map (measurable_pi_apply n) measurable_subtype_coe,
      Measure.map_map (measurable_pi_apply n) measurable_subtype_coe]
    exact hmap n

section Map
variable {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)] [∀ n, StandardBorelSpace (Y n)]
    {ψ : ∀ n, Y (n + 1) → Y n}
    (f : ∀ n, X n → Y n)
    (hc : ∀ n x, ψ n (f (n + 1) x) = f n (θ n x))

def map : Path θ → Path ψ := fun x =>
  ⟨fun n => f n (x.val n), fun n => by rw [hc, x.property]⟩

omit [∀ n, StandardBorelSpace (X n)] [∀ n, Nonempty (X n)]
  [∀ n, StandardBorelSpace (Y n)] in
@[fun_prop] lemma measurable_map (hf : ∀ n, Measurable (f n)) : Measurable (map θ f hc) :=
  (Measurable.of_eval (fun n => (hf n).comp (measurable_eval n))).subtype_mk

omit [∀ n, StandardBorelSpace (X n)] [∀ n, Nonempty (X n)]
  [∀ n, StandardBorelSpace (Y n)] [∀ n, MeasurableSpace (X n)]
  [∀ n, MeasurableSpace (Y n)] in
lemma eval_map (n : ℕ) : eval ψ n ∘ map θ f hc = f n ∘ eval θ n := rfl

variable [∀ n, Nonempty (Y n)] (ν : ∀ n, Measure (Y n)) [∀ n, IsProbabilityMeasure (ν n)]
    (hψ : ∀ n, Measurable (ψ n)) (hpψ : ∀ n, (ν (n + 1)).map (ψ n) = ν n)

include hθ hp hψ hpψ in
lemma map_law (hf : ∀ n, Measurable (f n)) (hm : ∀ n, (μ n).map (f n) = ν n) :
    (law θ μ).map (map θ f hc) = law ψ ν := by
  let := law_probability θ hθ μ hp
  let := law_probability ψ hψ ν hpψ
  apply unique ψ hψ
  intro n
  rw [Measure.map_map (measurable_eval n) (measurable_map θ f hc hf), eval_map,
    ← Measure.map_map (hf n) (measurable_eval n),
    map_eval_law θ hθ μ hp, hm, map_eval_law ψ hψ ν hpψ]

end Map

variable (T : ∀ n, X n ≃ᵐ X n)
    (hc : ∀ n x, θ n (T (n + 1) x) = T n (θ n x))

def time : Path θ ≃ᵐ Path θ where
  toFun := map θ (fun n => T n) hc
  invFun := map θ (fun n => (T n).symm) (fun n x => by
    apply (T n).injective
    rw [← hc, (T (n + 1)).apply_symm_apply, (T n).apply_symm_apply])
  left_inv x := Subtype.ext (by funext n; exact (T n).symm_apply_apply _)
  right_inv x := Subtype.ext (by funext n; exact (T n).apply_symm_apply _)
  measurable_toFun := (Measurable.of_eval (fun n =>
    (T n).measurable.comp (measurable_eval n))).subtype_mk
  measurable_invFun := (Measurable.of_eval (fun n =>
    (T n).symm.measurable.comp (measurable_eval n))).subtype_mk

include hθ hp in
lemma time_preserving (hT : ∀ n, MeasurePreserving (T n) (μ n) (μ n)) :
    MeasurePreserving (time θ T hc) (law θ μ) (law θ μ) :=
  ⟨(time θ T hc).measurable, map_law θ hθ μ hp _ hc μ hθ hp
    (fun n => (T n).measurable) (fun n => (hT n).map_eq)⟩

end


variable {X : ℕ → Type*} {J : Type*} [∀ n, MeasurableSpace (X n)]
  (θ : ∀ n, X (n + 1) → X n)

def arrayBond (n : ℕ) : (J → X (n + 1)) → (J → X n) := fun y j => θ n (y j)

def transpose : Path (X := fun n => J → X n) (arrayBond θ) ≃ᵐ (J → Path θ) where
  toFun y j := ⟨fun n => y.val n j, fun n => congrFun (y.property n) j⟩
  invFun y := ⟨fun n j => (y j).val n, fun n => funext (fun j => (y j).property n)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := Measurable.of_eval (fun _ =>
    (Measurable.of_eval (fun n => (measurable_pi_apply _).comp
      (measurable_eval n))).subtype_mk)
  measurable_invFun := (Measurable.of_eval (fun n => Measurable.of_eval
    (fun j => (measurable_eval n).comp (measurable_pi_apply j)))).subtype_mk

lemma transpose_eval (n : ℕ) :
    (fun (y : J → Path θ) j => eval θ n (y j)) ∘ transpose (J := J) θ =
      eval (X := fun n => J → X n) (arrayBond θ) n := rfl

variable [Countable J] [∀ n, StandardBorelSpace (X n)]
  (hθ : ∀ n, Measurable (θ n))

include hθ in
lemma array_unique {ρ σ : Measure (J → Path θ)} [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hm : ∀ n, ρ.map (fun y j => eval θ n (y j)) =
      σ.map (fun y j => eval θ n (y j))) : ρ = σ := by
  apply (transpose (J := J) θ).symm.measurableEmbedding.map_injective
  apply unique (X := fun n => J → X n) (arrayBond θ) (fun n => Measurable.of_eval (fun _ =>
    (hθ n).comp (measurable_pi_apply _)))
  intro n
  rw [Measure.map_map (measurable_eval n) (transpose θ).symm.measurable,
    Measure.map_map (measurable_eval n) (transpose θ).symm.measurable]
  exact hm n

variable [∀ n, Nonempty (X n)] (ρ : ∀ n, Measure (J → X n))
  [∀ n, IsProbabilityMeasure (ρ n)]
  (hp : ∀ n, (ρ (n + 1)).map (fun y j => θ n (y j)) = ρ n)

noncomputable def arrayLaw : Measure (J → Path θ) :=
  (law (X := fun n => J → X n) (arrayBond θ) ρ).map (transpose θ)

include hθ hp in
lemma arrayLaw_probability : IsProbabilityMeasure (arrayLaw θ ρ) := by
  let := law_probability (X := fun n => J → X n) (arrayBond θ)
    (fun n => Measurable.of_eval (fun _ => (hθ n).comp (measurable_pi_apply _))) ρ hp
  exact (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (transpose θ).measurable.aemeasurable

include hθ hp in
lemma arrayLaw_map_eval (n : ℕ) :
    (arrayLaw θ ρ).map (fun y j => eval θ n (y j)) = ρ n := by
  have hm : Measurable (fun (y : J → Path θ) j => eval θ n (y j)) :=
    Measurable.of_eval (fun j =>
      (measurable_eval n).comp (measurable_pi_apply j))
  rw [arrayLaw, Measure.map_map hm (transpose θ).measurable]
  change (law (X := fun s => J → X s) (arrayBond θ) ρ).map
    (eval (X := fun s => J → X s) (arrayBond θ) n) = ρ n
  exact map_eval_law (X := fun n => J → X n) (arrayBond θ) (fun n => Measurable.of_eval (fun _ =>
    (hθ n).comp (measurable_pi_apply _))) ρ hp n

variable {K : Type*} [Countable K]

omit [∀ n, Nonempty (X n)] in
include hθ in
lemma array_pi_unique {ρ σ : Measure (K → J → Path θ)}
    [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hm : ∀ n, ρ.map (fun y k j => eval θ n (y k j)) =
      σ.map (fun y k j => eval θ n (y k j))) : ρ = σ := by
  let e := (MeasurableEquiv.curry K J (Path θ)).symm
  apply e.measurableEmbedding.map_injective
  apply array_unique θ hθ
  intro n
  have hn := congrArg (Measure.map (MeasurableEquiv.curry K J (X n)).symm) (hm n)
  have hd : Measurable (fun (y : K → J → Path θ) k j => eval θ n (y k j)) :=
    Measurable.of_eval (fun k => Measurable.of_eval (fun j =>
      (measurable_eval n).comp ((measurable_pi_apply j).comp (measurable_pi_apply k))))
  have hf : Measurable (fun (y : K × J → Path θ) j => eval θ n (y j)) :=
    Measurable.of_eval (fun j =>
      (measurable_eval n).comp (measurable_pi_apply j))
  rw [Measure.map_map (MeasurableEquiv.curry K J (X n)).symm.measurable hd,
    Measure.map_map (MeasurableEquiv.curry K J (X n)).symm.measurable hd] at hn
  rw [Measure.map_map hf e.measurable, Measure.map_map hf e.measurable]
  exact hn


end InverseSystems

namespace ArrayObjects.Object
open Rokhlin.InverseSystems
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

structure Tower (base : InitialLaws I X T) where
  stage : ℕ → Object I base
  step : ∀ n, Extension (stage n) (stage (n + 1))

namespace Tower
variable (D : Tower base)

abbrev yBond (s : ℕ) : (D.stage (s + 1)).Y → (D.stage s).Y := (D.step s).state
abbrev uBond (s : ℕ) : (D.stage (s + 1)).U → (D.stage s).U := (D.step s).parameter

lemma measurable_yBond (s : ℕ) : Measurable (D.yBond s) := (D.step s).measurable_state
lemma measurable_uBond (s : ℕ) : Measurable (D.uBond s) := (D.step s).measurable_parameter

noncomputable abbrev stateSpace : StandardSpace where
  α := Path (X := fun s => (D.stage s).Y) D.yBond
  measurableSpace := inferInstance
  standardBorel := standardBorel_path (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond
  nonempty := nonempty_path (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond
    (fun s => (D.stage s).localLaw) (fun s => (D.step s).localLaw_map)

noncomputable abbrev parameterSpace : StandardSpace where
  α := Path (X := fun s => (D.stage s).U) D.uBond
  measurableSpace := inferInstance
  standardBorel := standardBorel_path (X := fun s => (D.stage s).U) D.uBond D.measurable_uBond
  nonempty := nonempty_path (X := fun s => (D.stage s).U) D.uBond D.measurable_uBond
    (fun s => (D.stage s).parameter) (fun s => (D.step s).parameter_map)

def timeState : D.stateSpace ≃ᵐ D.stateSpace :=
  InverseSystems.time (X := fun s => (D.stage s).Y) D.yBond (fun s => (D.stage s).timeY)
    (fun s x => congrFun (D.step s).time_state x)

def timeParameter : D.parameterSpace ≃ᵐ D.parameterSpace :=
  InverseSystems.time (X := fun s => (D.stage s).U) D.uBond (fun s => (D.stage s).timeU)
    (fun s x => congrFun (D.step s).time_parameter x)

abbrev proj (s : ℕ) : D.stateSpace → (D.stage s).Y := InverseSystems.eval (X := fun s => (D.stage s).Y) D.yBond s
abbrev pproj (s : ℕ) : D.parameterSpace → (D.stage s).U := InverseSystems.eval (X := fun s => (D.stage s).U) D.uBond s

@[fun_prop] lemma measurable_proj (s : ℕ) : Measurable (D.proj s) := InverseSystems.measurable_eval s
@[fun_prop] lemma measurable_pproj (s : ℕ) : Measurable (D.pproj s) := InverseSystems.measurable_eval s

def x : D.stateSpace → X := (D.stage 0).x ∘ D.proj 0

def par : D.stateSpace → D.parameterSpace :=
  InverseSystems.map (X := fun s => (D.stage s).Y)
    (Y := fun s => (D.stage s).U) D.yBond (ψ := D.uBond) (fun s => (D.stage s).par)
    (fun s y => (congrFun (D.step s).state_par y).symm)

@[fun_prop] lemma measurable_x : Measurable D.x :=
  (D.stage 0).measurable_x.comp (D.measurable_proj 0)

@[fun_prop] lemma measurable_par : Measurable D.par :=
  InverseSystems.measurable_map (X := fun s => (D.stage s).Y)
    (Y := fun s => (D.stage s).U) (ψ := D.uBond) D.yBond _ _ (fun s => (D.stage s).measurable_par)

lemma time_x : D.x ∘ D.timeState = T ∘ D.x := by
  funext y
  exact congrFun (D.stage 0).time_x (D.proj 0 y)

lemma time_par : D.par ∘ D.timeState = D.timeParameter ∘ D.par := by
  funext y
  apply Subtype.ext
  funext s
  exact congrFun (D.stage s).time_par (D.proj s y)

lemma x_stage (s : ℕ) : (D.stage s).x ∘ D.proj s = D.x := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [← ih]
    funext y
    change (D.stage (s + 1)).x (y.val (s + 1)) = (D.stage s).x (y.val s)
    rw [← y.property s]
    exact (congrFun (D.step s).state_x (y.val (s + 1))).symm

lemma par_stage (s : ℕ) : (D.stage s).par ∘ D.proj s = D.pproj s ∘ D.par := rfl

lemma array_coherent (n s : ℕ) :
    ((D.stage (s + 1)).law n).map (fun y v => D.yBond s (y v)) = (D.stage s).law n :=
  (D.step s).laws n

noncomputable def arrayLaw (n : ℕ) : Measure (Arr I D.stateSpace n) :=
  InverseSystems.arrayLaw (X := fun s => (D.stage s).Y) D.yBond (fun s => (D.stage s).law n)

instance arrayLaw_probability (n : ℕ) : IsProbabilityMeasure (D.arrayLaw n) :=
  InverseSystems.arrayLaw_probability (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond
    (fun s => (D.stage s).law n) (D.array_coherent n)

lemma array_marginal (n s : ℕ) : (D.arrayLaw n).map (amap (D.proj s) n) =
    (D.stage s).law n :=
  InverseSystems.arrayLaw_map_eval (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond
    (fun s => (D.stage s).law n) (D.array_coherent n) s

lemma array_over_base (n : ℕ) : (D.arrayLaw n).map (amap D.x n) = base.law n := by
  rw [← (D.stage 0).over_base n, ← D.array_marginal n 0,
    Measure.map_map (measurable_amap (D.stage 0).measurable_x n)
      (measurable_amap (D.measurable_proj 0) n)]
  rfl

lemma array_invariant (n : ℕ) :
    MeasurePreserving (amap D.timeState n) (D.arrayLaw n) (D.arrayLaw n) := by
  refine ⟨measurable_amap D.timeState.measurable n, ?_⟩
  apply InverseSystems.array_unique (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond
  intro s
  change ((D.arrayLaw n).map (amap D.timeState n)).map (amap (D.proj s) n) =
    (D.arrayLaw n).map (amap (D.proj s) n)
  rw [Measure.map_map (measurable_amap (D.measurable_proj s) n)
    (measurable_amap D.timeState.measurable n)]
  change (D.arrayLaw n).map (amap (D.stage s).timeY n ∘ amap (D.proj s) n) = _
  rw [← Measure.map_map (measurable_amap (D.stage s).timeY.measurable n)
    (measurable_amap (D.measurable_proj s) n), D.array_marginal,
    (D.stage s).invariant n |>.map_eq]

lemma array_consistent (n : ℕ) (a : Fin (n + 1)) (i : I) :
    (D.arrayLaw (n + 1)).map (plane n a i) = D.arrayLaw n := by
  apply InverseSystems.array_unique (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond
  intro s
  change ((D.arrayLaw (n + 1)).map (plane n a i)).map (amap (D.proj s) n) =
    (D.arrayLaw n).map (amap (D.proj s) n)
  rw [Measure.map_map (measurable_amap (D.measurable_proj s) n) (measurable_plane n a i)]
  change (D.arrayLaw (n + 1)).map (plane n a i ∘ amap (D.proj s) (n + 1)) = _
  rw [← Measure.map_map (measurable_plane n a i)
    (measurable_amap (D.measurable_proj s) (n + 1)), D.array_marginal,
    (D.stage s).consistent, D.array_marginal]

lemma array_proper (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) :
    (D.arrayLaw (n + 1)).map (planes n J) = Measure.pi (fun _ : J => D.arrayLaw n) := by
  apply InverseSystems.array_pi_unique (X := fun s => (D.stage s).Y)
    D.yBond D.measurable_yBond
  intro s
  change ((D.arrayLaw (n + 1)).map (planes n J)).map
    (fun y j => amap (D.proj s) n (y j)) = _
  have hm : Measurable (fun (y : J → Arr I D.stateSpace n) j =>
      amap (D.proj s) n (y j)) := Measurable.of_eval (fun j =>
    (measurable_amap (D.measurable_proj s) n).comp (measurable_pi_apply j))
  rw [Measure.map_map hm (measurable_planes n J)]
  change (D.arrayLaw (n + 1)).map (planes n J ∘ amap (D.proj s) (n + 1)) = _
  rw [← Measure.map_map (measurable_planes n J)
    (measurable_amap (D.measurable_proj s) (n + 1)), D.array_marginal,
    (D.stage s).proper n J hJ]
  change Measure.pi (fun _ : J => (D.stage s).law n) =
    (Measure.pi (fun _ : J => D.arrayLaw n)).map (fun y j => amap (D.proj s) n (y j))
  rw [Measure.pi_map_pi (fun _ => (measurable_amap (D.measurable_proj s) n).aemeasurable)]
  simp only [D.array_marginal]

noncomputable def localLaw : Measure D.stateSpace :=
  (D.arrayLaw 0).map (zeroEquiv I D.stateSpace)

instance localLaw_probability : IsProbabilityMeasure D.localLaw :=
  (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (zeroEquiv I D.stateSpace).measurable.aemeasurable

lemma localLaw_marginal (s : ℕ) : D.localLaw.map (D.proj s) = (D.stage s).localLaw := by
  rw [localLaw, Measure.map_map (D.measurable_proj s) (zeroEquiv I D.stateSpace).measurable]
  change (D.arrayLaw 0).map (zeroEquiv I (D.stage s).Y ∘ amap (D.proj s) 0) = _
  rw [← Measure.map_map (zeroEquiv I (D.stage s).Y).measurable
    (measurable_amap (D.measurable_proj s) 0), D.array_marginal]
  rfl

lemma local_indep_stage (s : ℕ) : IndepFun D.x (D.pproj s ∘ D.par) D.localLaw := by
  have h : IndepFun ((D.stage s).x ∘ D.proj s)
      ((D.stage s).par ∘ D.proj s) D.localLaw := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro A B hA hB
    have he := (D.stage s).local_independent.measure_inter_preimage_eq_mul A B hA hB
    change (D.stage s).localLaw _ = (D.stage s).localLaw _ * (D.stage s).localLaw _ at he
    rw [← D.localLaw_marginal s,
      Measure.map_apply (D.measurable_proj s)
        (((D.stage s).measurable_x hA).inter ((D.stage s).measurable_par hB)),
      Measure.map_apply (D.measurable_proj s) ((D.stage s).measurable_x hA),
      Measure.map_apply (D.measurable_proj s) ((D.stage s).measurable_par hB)] at he
    exact he
  rwa [D.x_stage s, D.par_stage s] at h

lemma parameter_comap :
    MeasurableSpace.comap D.par (inferInstance : MeasurableSpace D.parameterSpace) =
      ⨆ s, MeasurableSpace.comap (D.pproj s ∘ D.par)
        (inferInstance : MeasurableSpace (D.stage s).U) := by
  change MeasurableSpace.comap D.par
    (MeasurableSpace.comap Subtype.val MeasurableSpace.pi) = _
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp]
  rfl

lemma parameter_comap_mono : Monotone (fun s =>
    MeasurableSpace.comap (D.pproj s ∘ D.par)
      (inferInstance : MeasurableSpace (D.stage s).U)) := by
  apply monotone_nat_of_le_succ
  intro s
  have he : D.pproj s ∘ D.par = D.uBond s ∘ (D.pproj (s + 1) ∘ D.par) := by
    funext y
    exact ((D.par y).property s).symm
  rw [he, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (D.measurable_uBond s).comap_le

lemma local_independent : IndepFun D.x D.par D.localLaw := by
  rw [IndepFun_iff_Indep]
  apply Indep.symm
  rw [D.parameter_comap]
  apply indep_iSup_of_monotone
  · intro s
    exact (D.local_indep_stage s).symm
  · intro s
    exact ((D.measurable_pproj s).comp D.measurable_par).comap_le
  · exact D.measurable_x.comap_le
  · exact D.parameter_comap_mono

end Tower
end ArrayObjects.Object

open MeasureTheory Filter
open scoped BigOperators Topology

namespace ConditionalLimits

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (𝒢 : ι → Filtration ℕ ‹MeasurableSpace Ω›)
    (f : ι → Ω → ℝ)

theorem product_identity
    (h : ∀ᶠ n in atTop,
      μ[(fun x => ∏ i, f i x) | ℱ n] =ᵐ[μ]
        (fun x => ∏ i, μ[f i | 𝒢 i n] x)) :
    μ[(fun x => ∏ i, f i x) | ⨆ n, ℱ n] =ᵐ[μ]
      (fun x => ∏ i, μ[f i | ⨆ n, 𝒢 i n] x) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have he : ∀ᵐ x ∂μ, ∀ n, N ≤ n →
      μ[(fun x => ∏ i, f i x) | ℱ n] x = ∏ i, μ[f i | 𝒢 i n] x := by
    rw [ae_all_iff]
    intro n
    by_cases hn : N ≤ n
    · exact (hN n hn).mono (fun _ hx _ => hx)
    · exact Filter.Eventually.of_forall (by simp [hn])
  have hG : ∀ᵐ x ∂μ, ∀ i, Tendsto (fun n => μ[f i | 𝒢 i n] x) atTop
      (𝓝 (μ[f i | ⨆ n, 𝒢 i n] x)) := by
    rw [ae_all_iff]
    exact fun i => tendsto_ae_condExp (ℱ := 𝒢 i) (f i)
  filter_upwards [tendsto_ae_condExp (ℱ := ℱ) (fun x => ∏ i, f i x), hG, he]
    with x hF hG hx
  apply tendsto_nhds_unique hF
  exact (tendsto_finsetProd _ (fun i _ => hG i)).congr'
    (eventually_atTop.mpr ⟨N, fun n hn => (hx n hn).symm⟩)

end ConditionalLimits

namespace ConditionalProducts
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {U Ω ι : Type*} {Y : ι → Type*}
  [MeasurableSpace U] [MeasurableSpace Ω] [Fintype ι]
  [∀ i, MeasurableSpace (Y i)] [∀ i, StandardBorelSpace (Y i)]

lemma kernel_ae_eq_of_boxes (ν : Measure U) [IsFiniteMeasure ν]
    (κ η : Kernel U (∀ i, Y i)) [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : ∀ s : ∀ i, Set (Y i), (∀ i, MeasurableSet (s i)) →
      (fun p => κ p (Set.pi Set.univ s)) =ᵐ[ν] (fun p => η p (Set.pi Set.univ s))) :
    κ =ᵐ[ν] η := by
  apply Kernel.ae_eq_of_compProd_eq
  let D : Set (Set (∀ i, Y i)) :=
    Set.pi Set.univ '' Set.pi Set.univ (fun i => {s : Set (Y i) | MeasurableSet s})
  let C : Set (Set (U × (∀ i, Y i))) :=
    Set.image2 (· ×ˢ ·) {s : Set U | MeasurableSet s} D
  have hgen : MeasurableSpace.generateFrom C = (inferInstance : MeasurableSpace (U × (∀ i, Y i))) :=
    generateFrom_eq_prod MeasurableSpace.generateFrom_measurableSet generateFrom_pi
      isCountablySpanning_measurableSet
      (IsCountablySpanning.pi (fun _ => isCountablySpanning_measurableSet))
  refine Measure.ext_of_generateFrom_of_iUnion C (fun _ => Set.univ) hgen.symm
    (MeasurableSpace.isPiSystem_measurableSet.prod isPiSystem_pi) (by
      exact Set.iUnion_const (s := Set.univ)) ?_
    (fun _ => measure_ne_top _ _) ?_
  · intro _
    refine ⟨Set.univ, MeasurableSet.univ, Set.univ, ?_, by simp⟩
    exact ⟨fun _ => Set.univ, fun _ _ => MeasurableSet.univ, by simp⟩
  · rintro _ ⟨A, hA, _, ⟨s, hs, rfl⟩, rfl⟩
    have hS : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi
      (fun i => hs i (Set.mem_univ i))
    rw [Measure.compProd_apply_prod hA hS, Measure.compProd_apply_prod hA hS]
    exact lintegral_congr_ae ((h s (fun i => hs i (Set.mem_univ i))).filter_mono
      ae_restrict_le)

variable [∀ i, Nonempty (Y i)]

lemma condDistrib_product_of_indicator
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → U) (O : Ω → ∀ i, Y i) (hE : Measurable E) (hO : Measurable O)
    (κ : ∀ i, Kernel U (Y i)) [∀ i, IsMarkovKernel (κ i)]
    (h : ∀ s : ∀ i, Set (Y i), (∀ i, MeasurableSet (s i)) →
      μ⟦O ⁻¹' Set.pi Set.univ s | MeasurableSpace.comap E inferInstance⟧ =ᵐ[μ]
        (fun ω => ∏ i, (κ i (E ω)).real (s i))) :
    condDistrib O E μ =ᵐ[μ.map E] FiniteKernel.pi κ := by
  apply kernel_ae_eq_of_boxes
  intro s hs
  have hS : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  have he := (condDistrib_ae_eq_condExp (μ := μ) hE hO hS).trans (h s hs)
  apply (ae_map_iff hE.aemeasurable ?_).mpr
  · filter_upwards [he] with ω hω
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    simpa only [Measure.real, FiniteKernel.pi_apply, Measure.pi_pi, ENNReal.toReal_prod]
      using hω
  · exact measurableSet_eq_fun ((condDistrib O E μ).measurable_coe hS)
      ((FiniteKernel.pi κ).measurable_coe hS)

end ConditionalProducts

open MeasureTheory ProbabilityTheory
namespace ConditionalPullback
variable {Ω Z U B : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  [MeasurableSpace U] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]

lemma indicator (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → Z) (p : Z → U) (o : Z → B)
    (hf : Measurable f) (hp : Measurable p) (ho : Measurable o)
    (S : Set B) (hS : MeasurableSet S) :
    μ⟦(o ∘ f) ⁻¹' S | MeasurableSpace.comap (p ∘ f) inferInstance⟧ =ᵐ[μ]
      ((μ.map f)⟦o ⁻¹' S | MeasurableSpace.comap p inferInstance⟧ ∘ f) := by
  have hk := condDistrib_map (ν := μ) hp.aemeasurable ho.aemeasurable hf.aemeasurable
  have hk' := ae_of_ae_map (hp.comp hf).aemeasurable hk
  have hc := condDistrib_ae_eq_condExp (μ := μ) (hp.comp hf) (ho.comp hf) hS
  have hc' := ae_of_ae_map hf.aemeasurable
    (condDistrib_ae_eq_condExp (μ := μ.map f) hp ho hS)
  filter_upwards [hk', hc, hc'] with ω hω h1 h2
  exact h1.symm.trans ((congrArg (fun ν : Measure B => ν.real S) hω).symm.trans h2)

end ConditionalPullback

namespace ArrayObjects.Object
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

lemma indicator_product (M : Object I base) (n : ℕ) (J : Finset I)
    (hJ : J ≠ Finset.univ) (S : J → Set (Arr I M.Y n))
    (hS : ∀ j, MeasurableSet (S j)) :
    (M.law (n + 1))⟦planes n J ⁻¹' Set.pi Set.univ S |
      MeasurableSpace.comap (amap M.par (n + 1)) inferInstance⟧ =ᵐ[M.law (n + 1)]
    (fun y => ∏ j : J, ((M.law (n + 1))⟦plane n (Fin.last n) (j : I) ⁻¹' S j |
      MeasurableSpace.comap (amap M.par n ∘ plane n (Fin.last n) (j : I)) inferInstance⟧) y) := by
  have hk := ae_of_ae_map (measurable_amap M.measurable_par (n + 1)).aemeasurable
    (M.conditional n J hJ)
  have hc := condDistrib_ae_eq_condExp (μ := M.law (n + 1))
    (measurable_amap M.measurable_par (n + 1)) (measurable_planes n J)
    (MeasurableSet.univ_pi hS)
  have hj : ∀ j : J,
      (fun y => (condDistrib (id : Arr I M.Y n → Arr I M.Y n)
        (amap M.par n) (M.law n) (amap M.par n (plane n (Fin.last n) (j : I) y))).real (S j))
        =ᵐ[M.law (n + 1)]
      (M.law (n + 1))⟦plane n (Fin.last n) (j : I) ⁻¹' S j |
        MeasurableSpace.comap (amap M.par n ∘ plane n (Fin.last n) (j : I)) inferInstance⟧ := by
    intro j
    have hlocal := condDistrib_ae_eq_condExp (μ := M.law n)
      (measurable_amap M.measurable_par n) measurable_id (hS j)
    have hpull := Rokhlin.ConditionalPullback.indicator (M.law (n + 1))
      (plane n (Fin.last n) (j : I)) (amap M.par n) id (measurable_plane _ _ _)
      (measurable_amap M.measurable_par n) measurable_id (S j) (hS j)
    rw [M.consistent] at hpull
    have hpres : MeasurePreserving (plane n (Fin.last n) (j : I))
        (M.law (n + 1)) (M.law n) := ⟨measurable_plane _ _ _, M.consistent _ _ _⟩
    exact (hpres.quasiMeasurePreserving.ae_eq_comp hlocal).trans hpull.symm
  have hall := ae_all_iff.mpr hj
  filter_upwards [hk, hc, hall] with y hk hc hj
  rw [← hc, hk]
  simp only [Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact hj j

end ArrayObjects.Object

namespace InverseSystems
variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  (θ : ∀ n, X (n + 1) → X n)
  {Ω J : Type*} (F : Ω → J → Path θ)

lemma comap_array_path :
    MeasurableSpace.comap F (inferInstance : MeasurableSpace (J → Path θ)) =
      ⨆ s, MeasurableSpace.comap (fun ω j => eval θ s (F ω j))
        (inferInstance : MeasurableSpace (J → X s)) := by
  change MeasurableSpace.comap F
    (⨆ j, MeasurableSpace.comap (Function.eval j)
      (MeasurableSpace.comap Subtype.val MeasurableSpace.pi)) = _
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rw [iSup_comm]
  rfl

lemma comap_array_path_mono (hθ : ∀ n, Measurable (θ n)) :
    Monotone (fun s => MeasurableSpace.comap (fun ω j => eval θ s (F ω j))
      (inferInstance : MeasurableSpace (J → X s))) := by
  apply monotone_nat_of_le_succ
  intro s
  have he : (fun ω j => eval θ s (F ω j)) =
      (fun y j => θ s (y j)) ∘ (fun ω j => eval θ (s + 1) (F ω j)) := by
    funext ω j
    exact ((F ω j).property s).symm
  rw [he, ← MeasurableSpace.comap_comp]
  apply MeasurableSpace.comap_mono
  exact (Measurable.of_eval (fun j => (hθ s).comp (measurable_pi_apply j))).comap_le
end InverseSystems

namespace ArrayObjects.Object.Tower

section
open MeasureTheory ProbabilityTheory Rokhlin.InverseSystems Filter
open scoped BigOperators Topology
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T} (D : Tower base)

lemma stage_indicator_product (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ)
    (t : ℕ) (S : J → Set (Arr I (D.stage t).Y n))
    (hS : ∀ j, MeasurableSet (S j)) :
    (D.arrayLaw (n + 1))⟦(planes n J ∘ amap (D.proj t) (n + 1)) ⁻¹' Set.pi Set.univ S |
      MeasurableSpace.comap (amap (D.stage t).par (n + 1) ∘ amap (D.proj t) (n + 1))
        inferInstance⟧ =ᵐ[D.arrayLaw (n + 1)]
    (fun y => ∏ j : J, ((D.arrayLaw (n + 1))⟦
      (plane n (Fin.last n) (j : I) ∘ amap (D.proj t) (n + 1)) ⁻¹' S j |
      MeasurableSpace.comap (amap (D.stage t).par n ∘ plane n (Fin.last n) (j : I) ∘
        amap (D.proj t) (n + 1)) inferInstance⟧) y) := by
  have hp : MeasurePreserving (amap (D.proj t) (n + 1))
      (D.arrayLaw (n + 1)) ((D.stage t).law (n + 1)) :=
    ⟨measurable_amap (D.measurable_proj t) _, D.array_marginal _ _⟩
  have hs := hp.quasiMeasurePreserving.ae_eq_comp ((D.stage t).indicator_product n J hJ S hS)
  have hh := Rokhlin.ConditionalPullback.indicator (D.arrayLaw (n + 1))
    (amap (D.proj t) (n + 1)) (amap (D.stage t).par (n + 1)) (planes n J)
    (measurable_amap (D.measurable_proj t) _) (measurable_amap (D.stage t).measurable_par _)
    (measurable_planes n J) (Set.pi Set.univ S) (MeasurableSet.univ_pi hS)
  rw [D.array_marginal] at hh
  have hl := fun j : J => Rokhlin.ConditionalPullback.indicator (D.arrayLaw (n + 1))
    (amap (D.proj t) (n + 1))
    (amap (D.stage t).par n ∘ plane n (Fin.last n) (j : I)) (plane n (Fin.last n) (j : I))
    (measurable_amap (D.measurable_proj t) _)
    ((measurable_amap (D.stage t).measurable_par n).comp (measurable_plane _ _ _))
    (measurable_plane _ _ _) (S j) (hS j)
  simp only [D.array_marginal] at hl
  have hall := ae_all_iff.mpr hl
  filter_upwards [hs, hh, hall] with y hs hh hl
  rw [hh, hs]
  apply Finset.prod_congr rfl
  intro j _
  exact (hl j).symm

def parameterFiltration {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (E : Ω → Arr I D.parameterSpace n) (hE : Measurable E) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq s := MeasurableSpace.comap (amap (D.pproj s) n ∘ E) inferInstance
  mono' := InverseSystems.comap_array_path_mono (X := fun s => (D.stage s).U) D.uBond E D.measurable_uBond
  le' s := ((measurable_amap (D.measurable_pproj s) n).comp hE).comap_le

lemma parameterFiltration_iSup {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (E : Ω → Arr I D.parameterSpace n) (hE : Measurable E) :
    (⨆ s, D.parameterFiltration n E hE s) = MeasurableSpace.comap E inferInstance :=
  (InverseSystems.comap_array_path (X := fun s => (D.stage s).U) D.uBond E).symm


lemma proj_bond {s t : ℕ} (h : s ≤ t) :
    D.proj s = SequentialLimit.bond (X := fun s => (D.stage s).Y) D.yBond h ∘ D.proj t := by
  funext y
  exact (SequentialLimit.bond_apply_of_compatible (X := fun s => (D.stage s).Y) D.yBond y.property h).symm

lemma indicator_box {Ω ι : Type*} {Z : ι → Type*} [Fintype ι]
    (O : Ω → ∀ j, Z j) (S : ∀ j, Set (Z j)) :
    (O ⁻¹' Set.pi Set.univ S).indicator (fun _ => (1 : ℝ)) =
      (fun y => ∏ j, ((fun y => O y j) ⁻¹' S j).indicator (fun _ => (1 : ℝ)) y) := by
  classical
  funext y
  simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  rw [Finset.prod_boole]
  simp

lemma limit_indicator_product (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ)
    (s : ℕ) (S : J → Set (Arr I (D.stage s).Y n))
    (hS : ∀ j, MeasurableSet (S j)) :
    (D.arrayLaw (n + 1))⟦(planes n J ∘ amap (D.proj s) (n + 1)) ⁻¹' Set.pi Set.univ S |
      MeasurableSpace.comap (amap D.par (n + 1)) inferInstance⟧ =ᵐ[D.arrayLaw (n + 1)]
    (fun y => ∏ j : J, ((D.arrayLaw (n + 1))⟦
      (plane n (Fin.last n) (j : I) ∘ amap (D.proj s) (n + 1)) ⁻¹' S j |
      MeasurableSpace.comap (amap D.par n ∘ plane n (Fin.last n) (j : I)) inferInstance⟧) y) := by
  let ℱ := D.parameterFiltration (n + 1) (amap D.par (n + 1))
    (measurable_amap D.measurable_par (n + 1))
  let 𝒢 := fun j : J => D.parameterFiltration n (amap D.par n ∘ plane n (Fin.last n) (j : I))
    ((measurable_amap D.measurable_par n).comp (measurable_plane _ _ _))
  let f := fun j : J => ((plane n (Fin.last n) (j : I) ∘ amap (D.proj s) (n + 1)) ⁻¹' S j).indicator
    (fun _ => (1 : ℝ))
  have hF : (⨆ t, ℱ t) = MeasurableSpace.comap (amap D.par (n + 1)) inferInstance :=
    D.parameterFiltration_iSup _ _ _
  have hG : ∀ j : J, (⨆ t, 𝒢 j t) =
      MeasurableSpace.comap (amap D.par n ∘ plane n (Fin.last n) (j : I)) inferInstance :=
    fun _ => D.parameterFiltration_iSup _ _ _
  have hx : (fun y => ∏ j, f j y) =
      ((planes n J ∘ amap (D.proj s) (n + 1)) ⁻¹' Set.pi Set.univ S).indicator
        (fun _ => (1 : ℝ)) := (indicator_box _ _).symm
  have hh : ∀ᶠ t in atTop, (D.arrayLaw (n + 1))[(fun y => ∏ j, f j y) | ℱ t] =ᵐ[D.arrayLaw (n + 1)]
      (fun y => ∏ j, (D.arrayLaw (n + 1))[f j | 𝒢 j t] y) := by
    refine eventually_atTop.mpr ⟨s, fun t ht => ?_⟩
    let b := SequentialLimit.bond (X := fun s => (D.stage s).Y) D.yBond ht
    have hb : Measurable b := SequentialLimit.measurable_bond (X := fun s => (D.stage s).Y) D.yBond D.measurable_yBond ht
    let S' : J → Set (Arr I (D.stage t).Y n) := fun j => amap b n ⁻¹' S j
    have hS' : ∀ j, MeasurableSet (S' j) := fun j => (measurable_amap hb n) (hS j)
    have he := D.stage_indicator_product n J hJ t S' hS'
    have ho : (planes n J ∘ amap (D.proj t) (n + 1)) ⁻¹' Set.pi Set.univ S' =
        (planes n J ∘ amap (D.proj s) (n + 1)) ⁻¹' Set.pi Set.univ S := by
      rw [D.proj_bond ht]
      rfl
    have ho' : ∀ j : J,
        (plane n (Fin.last n) (j : I) ∘ amap (D.proj t) (n + 1)) ⁻¹' S' j =
        (plane n (Fin.last n) (j : I) ∘ amap (D.proj s) (n + 1)) ⁻¹' S j := by
      intro j
      rw [D.proj_bond ht]
      rfl
    rw [ho] at he
    simp_rw [ho'] at he
    rw [hx]
    exact he
  have h := Rokhlin.ConditionalLimits.product_identity (D.arrayLaw (n + 1)) ℱ 𝒢 f hh
  rw [hF, hx] at h
  simp only [hG] at h
  exact h


end

open MeasureTheory ProbabilityTheory Rokhlin.InverseSystems
open scoped BigOperators
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T} (D : Tower base)

lemma conditional_observation (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) (s : ℕ) :
    condDistrib (planes n J ∘ amap (D.proj s) (n + 1)) (amap D.par (n + 1))
      (D.arrayLaw (n + 1)) =ᵐ[(D.arrayLaw (n + 1)).map (amap D.par (n + 1))]
    FiniteKernel.pi (fun j : J =>
      (condDistrib (amap (D.proj s) n) (amap D.par n) (D.arrayLaw n)).comap
        (plane n (Fin.last n) (j : I)) (measurable_plane _ _ _)) := by
  apply Rokhlin.ConditionalProducts.condDistrib_product_of_indicator
    (D.arrayLaw (n + 1)) (amap D.par (n + 1))
    (planes n J ∘ amap (D.proj s) (n + 1))
    (measurable_amap D.measurable_par _) ((measurable_planes n J).comp
      (measurable_amap (D.measurable_proj s) _))
  intro S hS
  have h := D.limit_indicator_product n J hJ s S hS
  have hj : ∀ j : J,
      (D.arrayLaw (n + 1))⟦
        (plane n (Fin.last n) (j : I) ∘ amap (D.proj s) (n + 1)) ⁻¹' S j |
        MeasurableSpace.comap (amap D.par n ∘ plane n (Fin.last n) (j : I)) inferInstance⟧
        =ᵐ[D.arrayLaw (n + 1)]
      (fun y => (condDistrib (amap (D.proj s) n) (amap D.par n) (D.arrayLaw n)
        (amap D.par n (plane n (Fin.last n) (j : I) y))).real (S j)) := by
    intro j
    have hpull := Rokhlin.ConditionalPullback.indicator (D.arrayLaw (n + 1))
      (plane n (Fin.last n) (j : I)) (amap D.par n) (amap (D.proj s) n)
      (measurable_plane _ _ _) (measurable_amap D.measurable_par _)
      (measurable_amap (D.measurable_proj s) _) (S j) (hS j)
    rw [D.array_consistent] at hpull
    have hl := condDistrib_ae_eq_condExp (μ := D.arrayLaw n)
      (measurable_amap D.measurable_par _) (measurable_amap (D.measurable_proj s) _) (hS j)
    have hpres : MeasurePreserving (plane n (Fin.last n) (j : I))
        (D.arrayLaw (n + 1)) (D.arrayLaw n) :=
      ⟨measurable_plane _ _ _, D.array_consistent _ _ _⟩
    exact hpull.trans (hpres.quasiMeasurePreserving.ae_eq_comp hl).symm
  have hall := ae_all_iff.mpr hj
  filter_upwards [h, hall] with y h hj
  rw [h]
  apply Finset.prod_congr rfl
  intro j _
  exact hj j

lemma parameter_plane_preserving (n : ℕ) (i : I) :
    MeasurePreserving (plane n (Fin.last n) i)
      ((D.arrayLaw (n + 1)).map (amap D.par (n + 1)))
      ((D.arrayLaw n).map (amap D.par n)) := by
  refine ⟨measurable_plane _ _ _, ?_⟩
  rw [Measure.map_map (measurable_plane _ _ _) (measurable_amap D.measurable_par _),
    plane_amap, ← Measure.map_map (measurable_amap D.measurable_par _)
      (measurable_plane _ _ _), D.array_consistent]

local instance : StandardBorelSpace D.stateSpace := D.stateSpace.standardBorel
local instance : Nonempty D.stateSpace := D.stateSpace.nonempty

lemma conditional (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) :
    condDistrib (planes n J) (amap D.par (n + 1)) (D.arrayLaw (n + 1))
      =ᵐ[(D.arrayLaw (n + 1)).map (amap D.par (n + 1))]
    (fun p => Measure.pi (fun j : J =>
      condDistrib (id : Arr I D.stateSpace n → Arr I D.stateSpace n)
        (amap D.par n) (D.arrayLaw n) (plane n (Fin.last n) (j : I) p))) := by
  have hs : ∀ s : ℕ, ∀ᵐ p ∂(D.arrayLaw (n + 1)).map (amap D.par (n + 1)),
      (condDistrib (planes n J) (amap D.par (n + 1)) (D.arrayLaw (n + 1)) p).map
        (fun y (j : J) => amap (D.proj s) n (y j)) =
      (Measure.pi (fun j : J =>
        condDistrib (id : Arr I D.stateSpace n → Arr I D.stateSpace n)
          (amap D.par n) (D.arrayLaw n) (plane n (Fin.last n) (j : I) p))).map
        (fun y (j : J) => amap (D.proj s) n (y j)) := by
    intro s
    have hf : Measurable (fun (y : J → Arr I D.stateSpace n) j => amap (D.proj s) n (y j)) :=
      Measurable.of_eval (fun j => (measurable_amap (D.measurable_proj s) n).comp
        (measurable_pi_apply j))
    have hleft := condDistrib_comp (mβ := inferInstance) (μ := D.arrayLaw (n + 1))
      (measurable_amap D.measurable_par (n + 1)).aemeasurable
      (measurable_planes n J).aemeasurable hf
    have hright : condDistrib (amap (D.proj s) n) (amap D.par n) (D.arrayLaw n)
        =ᵐ[(D.arrayLaw n).map (amap D.par n)]
      (condDistrib (id : Arr I D.stateSpace n → Arr I D.stateSpace n)
        (amap D.par n) (D.arrayLaw n)).map (amap (D.proj s) n) := by
      exact condDistrib_comp (μ := D.arrayLaw n) (measurable_amap D.measurable_par n).aemeasurable
        (Y := (id : Arr I D.stateSpace n → Arr I D.stateSpace n)) aemeasurable_id
        (measurable_amap (D.measurable_proj s) n)
    have hall : ∀ᵐ p ∂(D.arrayLaw (n + 1)).map (amap D.par (n + 1)), ∀ j : J,
        condDistrib (amap (D.proj s) n) (amap D.par n) (D.arrayLaw n)
          (plane n (Fin.last n) (j : I) p) =
        (condDistrib id (amap D.par n) (D.arrayLaw n)
          (plane n (Fin.last n) (j : I) p)).map (amap (D.proj s) n) := by
      rw [ae_all_iff]
      intro j
      have he := (D.parameter_plane_preserving n (j : I)).quasiMeasurePreserving.ae_eq_comp hright
      filter_upwards [he] with p hp
      simpa only [Function.comp_apply, Kernel.map_apply _ (measurable_amap (D.measurable_proj s) n)] using hp
    filter_upwards [hleft, D.conditional_observation n J hJ s, hall] with p hl ho hr
    have hcomm : (fun (y : J → Arr I D.stateSpace n) (j : J) =>
        amap (D.proj s) n (y j)) ∘ planes n J =
      planes n J ∘ amap (D.proj s) (n + 1) := rfl
    rw [← Kernel.map_apply _ hf, ← hl, hcomm, ho, FiniteKernel.pi_apply,
      Measure.pi_map_pi (fun _ => (measurable_amap (D.measurable_proj s) n).aemeasurable)]
    congr 1
    funext j
    exact hr j
  have hall := ae_all_iff.mpr hs
  filter_upwards [hall] with p hp
  exact InverseSystems.array_pi_unique (X := fun s => (D.stage s).Y)
    D.yBond D.measurable_yBond hp

noncomputable def limit : Object I base where
  Y := D.stateSpace
  U := D.parameterSpace
  timeY := D.timeState
  timeU := D.timeParameter
  x := D.x
  par := D.par
  measurable_x := D.measurable_x
  measurable_par := D.measurable_par
  time_x := D.time_x
  time_par := D.time_par
  law := D.arrayLaw
  probability := D.arrayLaw_probability
  invariant := D.array_invariant
  over_base := D.array_over_base
  consistent := D.array_consistent
  proper := D.array_proper
  conditional := D.conditional
  local_independent := D.local_independent

noncomputable def projection (s : ℕ) : Extension (D.stage s) D.limit where
  state := D.proj s
  parameter := D.pproj s
  measurable_state := D.measurable_proj s
  measurable_parameter := D.measurable_pproj s
  time_state := rfl
  time_parameter := rfl
  state_x := D.x_stage s
  state_par := D.par_stage s
  laws := fun n => D.array_marginal n s


end ArrayObjects.Object.Tower

namespace ArrayObjects.Object
open scoped ENNReal
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

structure Test (M : Object I base) where
  level : ℕ
  kind : DataKind I
  vector : Lp ℂ 2 (M.law (level + 1))

namespace Test
variable {M N P : Object I base}

noncomputable def pull (F : Test M) (e : Extension M N) : Test N :=
  ⟨F.level, F.kind, e.pull (F.level + 1) F.vector⟩

noncomputable def energy (F : Test M) : ℝ := ‖M.project F.level F.kind F.vector‖

lemma energy_pull_le (F : Test M) (e : Extension M N) :
    (F.pull e).energy ≤ ‖F.vector‖ := by
  exact (N.project_norm_le _ _ _).trans_eq ((e.pull (F.level + 1)).norm_map F.vector)

lemma energy_mono (F : Test M) (e : Extension M N) : F.energy ≤ (F.pull e).energy :=
  e.project_norm_mono _ _ _

lemma pull_comp (F : Test M) (e : Extension M N) (f : Extension N P) :
    F.pull (e.comp f) = (F.pull e).pull f := by
  simp only [pull, Extension.pull_comp]
  rfl

lemma exists_near_max (F : Test M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : Object I base) (e : Extension M N),
      ∀ (P : Object I base) (f : Extension M P), (F.pull f).energy < (F.pull e).energy + ε := by
  let R : Set ℝ := {r | ∃ (N : Object I base) (e : Extension M N), (F.pull e).energy = r}
  have hR : R.Nonempty := ⟨(F.pull (Extension.refl M)).energy, M, Extension.refl M, rfl⟩
  have hRb : BddAbove R := ⟨‖F.vector‖, by
    rintro r ⟨N, e, rfl⟩
    exact F.energy_pull_le e⟩
  obtain ⟨r, ⟨N, e, hr⟩, hlt⟩ :=
    exists_lt_of_lt_csSup hR (show sSup R - ε < sSup R by linarith)
  refine ⟨N, e, fun P f => ?_⟩
  have hc : (F.pull f).energy ≤ sSup R := le_csSup hRb ⟨P, f, rfl⟩
  linarith

end Test
end ArrayObjects.Object

open MeasureTheory
open scoped ENNReal
section

lemma eq_of_finite_stage_Lp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsFiniteMeasure (ν n)]
    (π : ∀ n, Ω → X n) (hπ : ∀ n, MeasurePreserving (π n) μ (ν n))
    (hmono : Monotone (fun n => MeasurableSpace.comap (π n) inferInstance))
    (hgen : mΩ = ⨆ n, MeasurableSpace.comap (π n) inferInstance)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : Lp ℂ 2 μ →L[ℂ] E)
    (hAB : ∀ n F, A (Lp.compMeasurePreserving (π n) (hπ n) F) =
      B (Lp.compMeasurePreserving (π n) (hπ n) F)) : A = B := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let C : Set (Set Ω) := {s | ∃ n, MeasurableSet[MeasurableSpace.comap (π n) inferInstance] s}
  have hCalg : IsSetAlgebra C := by
    refine ⟨⟨0, @MeasurableSet.empty Ω (MeasurableSpace.comap (π 0) inferInstance)⟩, ?_, ?_⟩
    · rintro s ⟨n, hs⟩; exact ⟨n, hs.compl⟩
    · rintro s t ⟨n, hs⟩ ⟨k, ht⟩
      exact ⟨max n k, ((hmono (le_max_left n k)) _ hs).union
        ((hmono (le_max_right n k)) _ ht)⟩
  have hCgen : mΩ = MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · rw [hgen]
      refine iSup_le fun n => ?_
      intro s hs
      exact MeasurableSpace.measurableSet_generateFrom ⟨n, hs⟩
    · apply MeasurableSpace.generateFrom_le
      rintro s ⟨n, hs⟩
      exact (hπ n).measurable.comap_le _ hs
  have hCdense := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ hCalg hCgen
  have hclosed : IsClosed {F : Lp ℂ 2 μ | A F = B F} :=
    isClosed_eq A.continuous B.continuous
  have hCeq (c : ℂ) :
      {indicatorConstLp 2 (hCdense.measurable s hs) hμs c |
        (s : Set Ω) (hs : s ∈ C) (hμs : μ s ≠ ∞)} ⊆ {F | A F = B F} := by
    rintro _ ⟨s, ⟨n, t, ht, rfl⟩, hμs, rfl⟩
    exact hAB n (indicatorConstLp 2 ht (measure_ne_top (ν n) t) c)
  have hall (F : Lp ℂ 2 μ) : A F = B F := by
    apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (fun F => A F = B F)
    · intro c s hs hμs
      have hmem := hCdense.indicatorConstLp_subset_closure (p := 2) c ⟨s, hs, hμs.ne, rfl⟩
      exact (closure_minimal (hCeq c) hclosed) hmem
    · intro f g hf hg hfg hF hG
      simp only [map_add, hF, hG]
    · exact hclosed
  exact ContinuousLinearMap.ext hall
end

namespace ArrayObjects.Object
open scoped ENNReal Topology
open Filter
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

namespace Extension
@[ext] lemma ext {M N : Object I base} {e f : Extension M N}
    (hs : e.state = f.state) (hp : e.parameter = f.parameter) : e = f := by
  cases e; cases f; cases hs; cases hp; rfl
end Extension

namespace Tower
lemma projection_step (D : Tower base) (n : ℕ) :
    (D.step n).comp (D.projection (n + 1)) = D.projection n := by
  apply Extension.ext
  · funext y; exact y.property n
  · funext p; exact p.property n

lemma projection_fields_mono (D : Tower base) (n : ℕ) :
    Monotone (fun i => MeasurableSpace.comap (amap (D.projection i).state n)
      (inferInstance : MeasurableSpace (Arr I (D.stage i).Y n))) := by
  exact InverseSystems.comap_array_path_mono (X := fun i => (D.stage i).Y)
    D.yBond (id : Arr I D.stateSpace n → Arr I D.stateSpace n) D.measurable_yBond

lemma projection_fields_generate (D : Tower base) (n : ℕ) :
    (inferInstance : MeasurableSpace (Arr I D.limit.Y n)) =
      ⨆ i, MeasurableSpace.comap (amap (D.projection i).state n)
        (inferInstance : MeasurableSpace (Arr I (D.stage i).Y n)) := by
  have h := (InverseSystems.comap_array_path (X := fun i => (D.stage i).Y)
      D.yBond (id : Arr I D.stateSpace n → Arr I D.stateSpace n))
  rw [MeasurableSpace.comap_id] at h
  exact h
end Tower

namespace Saturating

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

def origin (n : ℕ) : ℕ := (Nat.unpair (Nat.unpair n).1).1
def testIndex (n : ℕ) : ℕ := (Nat.unpair (Nat.unpair n).1).2
lemma origin_le (n : ℕ) : origin n ≤ n :=
  (Nat.unpair_left_le _).trans (Nat.unpair_left_le n)
@[simp] lemma origin_pair (i j r : ℕ) : origin (Nat.pair (Nat.pair i j) r) = i := by
  simp [origin]
@[simp] lemma testIndex_pair (i j r : ℕ) : testIndex (Nat.pair (Nat.pair i j) r) = j := by
  simp [testIndex]

instance : Nonempty (DataKind I) := ⟨.parameter⟩
noncomputable def keys : ℕ → ℕ × DataKind I × ℕ :=
  (exists_surjective_nat (ℕ × DataKind I × ℕ)).choose
lemma keys_surjective : Function.Surjective (keys (I := I)) :=
  (exists_surjective_nat (ℕ × DataKind I × ℕ)).choose_spec

noncomputable def dense (M : Object I base) (n : ℕ) : ℕ → Lp ℂ 2 (M.law (n + 1)) :=
  TopologicalSpace.denseSeq (Lp ℂ 2 (M.law (n + 1)))
lemma dense_range (M : Object I base) (n : ℕ) : DenseRange (dense M n) :=
  TopologicalSpace.denseRange_denseSeq _

noncomputable def listed (M : Object I base) (j : ℕ) : Test M :=
  let k := keys (I := I) j
  ⟨k.1, k.2.1, dense M k.1 k.2.2⟩

lemma listed_key (M : Object I base) (n : ℕ) (d : DataKind I) (r j : ℕ)
    (hj : keys j = (n, d, r)) :
    listed M j = ⟨n, d, dense M n r⟩ := by
  unfold listed
  rw [hj]

structure Bank where
  obj : Object I base
  tests : ℕ → ℕ → Test obj

namespace Bank
noncomputable def seed (M : Object I base) : Bank (base := base) :=
  ⟨M, fun _ => listed M⟩

noncomputable def focus (b : Bank (base := base)) (n : ℕ) : Test b.obj :=
  b.tests (origin n) (testIndex n)

noncomputable def nextObj (b : Bank (base := base)) (n : ℕ) : Object I base :=
  (b.focus n |>.exists_near_max (1 / ((n : ℝ) + 1)) (by positivity)).choose

noncomputable def nextMap (b : Bank (base := base)) (n : ℕ) : Extension b.obj (b.nextObj n) :=
  (b.focus n |>.exists_near_max (1 / ((n : ℝ) + 1)) (by positivity)).choose_spec.choose

lemma near (b : Bank (base := base)) (n : ℕ) (P : Object I base) (f : Extension b.obj P) :
    ((b.focus n).pull f).energy < ((b.focus n).pull (b.nextMap n)).energy +
      1 / ((n : ℝ) + 1) :=
  (b.focus n |>.exists_near_max (1 / ((n : ℝ) + 1)) (by positivity)).choose_spec.choose_spec P f

noncomputable def next (b : Bank (base := base)) (n : ℕ) : Bank (base := base) :=
  ⟨b.nextObj n, fun i j => if i = n + 1 then listed (b.nextObj n) j
    else (b.tests i j).pull (b.nextMap n)⟩
end Bank

noncomputable def sequence (M : Object I base) : ℕ → Bank (base := base)
  | 0 => Bank.seed M
  | n + 1 => (sequence M n).next n

noncomputable abbrev tower (M : Object I base) : Tower base where
  stage n := (sequence M n).obj
  step n := (sequence M n).nextMap n

lemma tests_birth (M : Object I base) (i j : ℕ) :
    (sequence M i).tests i j = listed ((tower M).stage i) j := by
  cases i with
  | zero => rfl
  | succ i => simp [sequence, Bank.next, tower]

lemma tests_transport (M : Object I base) {i n : ℕ} (hi : i ≤ n) (j : ℕ) :
    (sequence M (n + 1)).tests i j =
      ((sequence M n).tests i j).pull ((tower M).step n) := by
  simp [sequence, Bank.next, show i ≠ n + 1 by omega, tower]

lemma tests_limit (M : Object I base) {i n : ℕ} (hi : i ≤ n) (j : ℕ) :
    ((sequence M n).tests i j).pull ((tower M).projection n) =
      (listed ((tower M).stage i) j).pull ((tower M).projection i) := by
  induction n, hi using Nat.le_induction with
  | base => rw [tests_birth]
  | succ n hn ih =>
    rw [tests_transport M hn, ← Test.pull_comp, Tower.projection_step, ih]

lemma listed_maximal (M : Object I base) (i j : ℕ) (P : Object I base)
    (f : Extension (tower M).limit P) :
    (((listed ((tower M).stage i) j).pull ((tower M).projection i)).pull f).energy ≤
      ((listed ((tower M).stage i) j).pull ((tower M).projection i)).energy := by
  let E := (listed ((tower M).stage i) j).pull ((tower M).projection i)
  have h (r : ℕ) : (E.pull f).energy ≤ E.energy + 1 / ((r : ℝ) + 1) := by
    let n := Nat.pair (Nat.pair i j) r
    have hi : i ≤ n := by simpa [n] using origin_le (Nat.pair (Nat.pair i j) r)
    have hn : r ≤ n := Nat.right_le_pair _ _
    have hnear := (sequence M n).near n P (((tower M).projection n).comp f)
    have hfocus : (sequence M n).focus n = (sequence M n).tests i j := by
      simp [Bank.focus, n]
    rw [hfocus, Test.pull_comp, tests_limit M hi j] at hnear
    have hmono := (Test.energy_mono ((sequence M n).tests i j |>.pull ((tower M).step n))
      ((tower M).projection (n + 1)))
    rw [← Test.pull_comp, Tower.projection_step, tests_limit M hi j] at hmono
    have hε : 1 / ((n : ℝ) + 1) ≤ 1 / ((r : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
    change (E.pull f).energy < _ at hnear
    change _ ≤ E.energy at hmono
    change (E.pull f).energy ≤ _
    have heq : (sequence M n).nextMap n = (tower M).step n := rfl
    rw [heq] at hnear
    exact hnear.le.trans (add_le_add hmono hε)
  exact ge_of_tendsto (by simpa using
    (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
      Tendsto (fun r : ℕ => E.energy + 1 / ((r : ℝ) + 1)) atTop (𝓝 (E.energy + 0))))
    (Eventually.of_forall h)

lemma listed_project_eq (M : Object I base) (i j : ℕ) (P : Object I base)
    (f : Extension (tower M).limit P) :
    let G := (listed ((tower M).stage i) j).pull ((tower M).projection i)
    P.project G.level G.kind (f.pull (G.level + 1) G.vector) =
      f.pull (G.level + 1) ((tower M).limit.project G.level G.kind G.vector) := by
  intro G
  apply f.project_eq_of_norm_le
  exact listed_maximal M i j P f

lemma finite_stage_project_eq (M : Object I base) (i n : ℕ) (d : DataKind I)
    (P : Object I base) (f : Extension (tower M).limit P)
    (F : Lp ℂ 2 (((tower M).stage i).law (n + 1))) :
    P.project n d (f.pull (n + 1) (((tower M).projection i).pull (n + 1) F)) =
      f.pull (n + 1) ((tower M).limit.project n d
        (((tower M).projection i).pull (n + 1) F)) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  refine (dense_range _ n).induction_on F
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro r
  obtain ⟨j, hj⟩ := keys_surjective (I := I) (n, d, r)
  have h := listed_project_eq M i j P f
  rw [listed_key _ n d r j hj] at h
  exact h

lemma tower_saturated (M : Object I base) : (tower M).limit.IsSaturated := by
  intro P f n d F
  let A : Lp ℂ 2 ((tower M).limit.law (n + 1)) →L[ℂ] Lp ℂ 2 (P.law (n + 1)) :=
    (P.project n d).comp (f.pull (n + 1)).toContinuousLinearMap
  let B : Lp ℂ 2 ((tower M).limit.law (n + 1)) →L[ℂ] Lp ℂ 2 (P.law (n + 1)) :=
    (f.pull (n + 1)).toContinuousLinearMap.comp ((tower M).limit.project n d)
  have heq : A = B := eq_of_finite_stage_Lp ((tower M).limit.law (n + 1))
    (fun i => ((tower M).stage i).law (n + 1))
    (fun i => amap ((tower M).projection i).state (n + 1))
    (fun i => ((tower M).projection i).measurePreserving (n + 1))
    ((tower M).projection_fields_mono (n + 1))
    ((tower M).projection_fields_generate (n + 1))
    A B (fun i v => finite_stage_project_eq M i n d P f v)
  exact DFunLike.congr_fun heq F

theorem exists_saturated_extension (M : Object I base) :
    ∃ (N : Object I base), Nonempty (Extension M N) ∧ N.IsSaturated :=
  ⟨(tower M).limit, ⟨(tower M).projection 0⟩, tower_saturated M⟩

end Saturating
end ArrayObjects.Object

end Rokhlin

end OAI
