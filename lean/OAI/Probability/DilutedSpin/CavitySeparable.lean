import OAI.Probability.DilutedSpin.AveragedRootBounds
import OAI.Probability.DilutedSpin.CavityAllocation
import OAI.Probability.DilutedSpin.IntegralError
import OAI.Probability.DilutedSpin.RootMapLaw
import OAI.Probability.DilutedSpin.UpperInsertion

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N k p : ℕ} [NeZero N]

noncomputable def cavityArrayEnergy (theta : X → InteractionSample p) (field : Y → ℝ)
    (E : (Fin N → Spin) → ℝ) (j : Fin k → Fin (p-1) → Fin N)
    (z : (Fin k → X) × Y) : (Fin N → Spin) → ℝ :=
  fun σ => E σ+cavitySiteEnergy (fun a => theta (z.1 a)) (field z.2) (fun a => σ (j a.1 a.2))

omit [NeZero N] in
lemma measurable_cavityArrayEnergy (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    (E : (Fin N → Spin) → ℝ) (j : Fin k → Fin (p-1) → Fin N) :
    Measurable (cavityArrayEnergy theta field E j) := by
  apply Measurable.of_eval
  intro σ
  unfold cavityArrayEnergy cavitySiteEnergy
  apply measurable_const.add
  apply Measurable.log
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro ε _
  apply Measurable.exp
  apply ((hh.comp measurable_snd).mul_const _).add
  exact Finset.measurable_sum _ (fun a _ => (hθ _).comp ((measurable_pi_apply a).comp measurable_fst))

noncomputable def cavityArrayValue (ξ : Measure Y) (theta : X → InteractionSample p)
    (field : Y → ℝ) (F : ((Fin N → Spin) → ℝ) → ℝ) (E : (Fin N → Spin) → ℝ)
    (z : Fin k → X) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (p-1) → Fin N)).expect
    (fun j => ∫ h,F (cavityArrayEnergy theta field E j (z,h)) ∂ξ)

lemma measurable_cavityArrayValue (ξ : Measure Y) [SFinite ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) (E : (Fin N → Spin) → ℝ) :
    Measurable (cavityArrayValue (k := k) ξ theta field F E) := by
  apply FiniteLaw.measurable_expect
  intro j
  exact (hF.measurable.comp (measurable_cavityArrayEnergy theta field hθ hh E j)).stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace X] in
lemma cavityArrayValue_bound (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    {H C B : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hθ : ∀ x,‖(theta x).1‖ ≤ C) (hh : ∀ y,|field y| ≤ H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : ∀ v,|F v| ≤ ‖v‖+B)
    (E : (Fin N → Spin) → ℝ) (z : Fin k → X) :
    |cavityArrayValue ξ theta field F E z| ≤ ‖E‖+H+C*k+B := by
  apply FiniteLaw.abs_expect_le
  intro j
  apply abs_integral_le_bound
  intro h
  apply (hF _).trans
  apply add_le_add _ le_rfl
  exact PhysicalRoot.cavitySiteEnergy_norm_bound (fun a => theta (z a)) (field h)
    (fun a => j a.1 a.2) E hH hC (fun _ => hθ _) (hh h)

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [Fintype Λ] [NeZero N] in
lemma path_proj_fst (l : ℕ)
    (y : FinitePath (Fin N → CavityState Ω Λ p (l+1)) n) (i : Fin N) :
    FinitePath.proj n (pathMap (fun a s => (a s).1) n y) i=
      pathFst n (FinitePath.proj n y i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] [NeZero N] in
lemma path_proj_join (l : ℕ) (c : RootPath (Fin N) l)
    (y : FinitePath (Fin N → CavityState Ω Λ p l) n) (i : Fin N) :
    FinitePath.proj n (pathMap (cavityProject l) n (pathMap (cavityJoin l c) n y)) i=
      pathMap (cavityProject l) n (FinitePath.proj n y i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (cavityProject_join l c y.1 i) (ih y.2)

noncomputable def singleBlockEnergy (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ)
    (r : Fin p → R) (z : InteractionSample p)
    (y : FinitePath (CavityState Ω Λ p (l+1)) n) : ℝ :=
  mixedEnergy z (fun a => decide (a=j))
    (fun _ => V (pathMap (cavityProject l) n (pathFst n y)))
    (fun a => x (r a) (pathMap (fun b : Fin p → Λ => b a) n (pathSnd n y)))

noncomputable def allocatedEnergy (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (s : Fin N) :
    (l : ℕ) → RootPath (Fin p → R) l → RootPath (Fin N) l →
      RootPath (InteractionSample p) l → (FinitePath Ω n → ℝ) →
        FinitePath (CavityState Ω Λ p l) n → ℝ
  | 0,_,_,_,f,y => f y
  | l+1,r,c,z,f,y => allocatedEnergy V x j s l r.2 c.2 z.2 f (pathFst n y)+
      if c.1=s then singleBlockEnergy V x j l r.1 z.1 y else 0

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma cavityEnergy_join (V : Fin N → FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p)
    (l : ℕ) (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : Fin N → FinitePath Ω n → ℝ)
    (y : FinitePath (Fin N → CavityState Ω Λ p l) n) :
    cavityEnergy (fun y s => V s (FinitePath.proj n y s)) x j l r i z
      (fun y => ∑ s,f s (FinitePath.proj n y s))
      (pathMap (cavityJoin l (rootMap (fun a => a j) l i)) n y)=
      ∑ s,allocatedEnergy (V s) x j s l r (rootMap (fun a => a j) l i) z (f s)
        (FinitePath.proj n y s) := by
  induction l with
  | zero =>
    change (∑ s,f s (FinitePath.proj n (pathMap id n y) s))=∑ s,f s (FinitePath.proj n y s)
    rw [pathMap_id]
  | succ l ih =>
    simp only [cavityEnergy,allocatedEnergy,rootMap,pathFst_cavityJoin]
    rw [ih]
    simp only [path_proj_fst,Finset.sum_add_distrib]
    congr 1
    unfold mixedTreeEnergy
    rw [mixedEnergy_single]
    simp only [pathFst_cavityJoin,pathSnd_cavityJoin,path_proj_join,path_proj_fst]
    simp only [singleBlockEnergy]
    rw [Finset.sum_eq_single (i.1 j)]
    · simp only [ite_true]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

omit [Fintype R] [NeZero N] in
lemma cavityRoot_separable (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : Fin N → FinitePath Ω n → ℝ) :
    cavityRoot (KernelTower.pi n T) U (fun y s => V s (FinitePath.proj n y s)) x m j l r i z
      (fun y => ∑ s,f s (FinitePath.proj n y s))=
      ∑ s,backwardLog n (cavityTower (T s) U l r) m
        (allocatedEnergy (V s) x j s l r (rootMap (fun a => a j) l i) z (f s)) := by
  unfold cavityRoot
  rw [← backwardLog_of_projects n (cavityJoin_projects T U l r (rootMap (fun a => a j) l i))]
  simp_rw [cavityEnergy_join]
  exact backwardLog_pi_sum _ _ _ _

end DilutedSpinGlass.PrescribedTree

end

end OAI
