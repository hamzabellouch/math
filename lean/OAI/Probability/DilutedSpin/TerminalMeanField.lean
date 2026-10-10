import OAI.Probability.DilutedSpin.TerminalMeanCavity
import OAI.Probability.DilutedSpin.TowerTerminalPad
import OAI.Probability.DilutedSpin.UpperTrial

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I Y : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] {A : I → Type} [∀ i,Fintype (A i)] {N J k p L : ℕ}

noncomputable def fieldEnergy (field : Y → ℝ) (h : RootPath Y N) (σ : Fin N → Spin) : ℝ :=
  ∑ i,field (rootArray N h i)*spin (σ i)

lemma measurable_fieldEnergy (field : Y → ℝ) (hh : Measurable field) :
    Measurable (fieldEnergy (N := N) field) := by
  apply Measurable.of_eval
  intro σ
  exact Finset.measurable_sum _ (fun i _ => (hh.comp (measurable_rootArray N i)).mul_const _)

omit [MeasurableSpace Y] in
lemma fieldEnergy_bound (field : Y → ℝ) {H : ℝ} (hh : ∀ y,|field y|≤H)
    (h : RootPath Y N) (σ : Fin N → Spin) : |fieldEnergy field h σ|≤H*N := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i : Fin N,H := Finset.sum_le_sum (fun _ _ => by
      rw [abs_mul,abs_spin,mul_one]; exact hh _)
    _ = _ := by simp [mul_comm]

omit [MeasurableSpace Y] in
lemma fieldEnergy_norm (field : Y → ℝ) {H : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (h : RootPath Y N) : ‖fieldEnergy field h‖≤H*N := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hH (Nat.cast_nonneg N))).mpr
  intro σ
  simpa only [Real.norm_eq_abs] using fieldEnergy_bound field hh h σ

omit [MeasurableSpace Y] in
lemma fieldEnergy_cons (field : Y → ℝ) (h : Y×RootPath Y N) (σ : Fin (N+1) → Spin) :
    fieldEnergy field h σ=field h.1*spin (σ 0)+fieldEnergy field h.2 (fun i => σ i.succ) := by
  simp [fieldEnergy,Fin.sum_univ_succ,rootArray]

lemma terminalMean_field_integrable [NeZero J]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (field : Y → ℝ) (hhm : Measurable field) (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {H D : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    Integrable (fun h => terminalMean ν s Q m ψ site (E+fieldEnergy field h)) (rootLaw N (fun _ => ξ)) := by
  apply Integrable.of_bound
    ((terminalMean_lipschitz ν s Q m hm ψ site hf).continuous.measurable.comp
      (measurable_const.add (measurable_fieldEnergy field hhm))).aestronglyMeasurable
    (‖E‖+H*N+D*s)
  filter_upwards [] with h
  change |terminalMean ν s Q m ψ site (E+fieldEnergy field h)|≤_
  calc
    _ ≤ ‖E+fieldEnergy field h‖+D*s := terminalMean_bound ν s Q m hm ψ site _ hf
    _ ≤ (‖E‖+‖fieldEnergy field h‖)+D*s := by have := norm_add_le E (fieldEnergy field h); linarith
    _ ≤ _ := by have := fieldEnergy_norm field hH hh h; linarith

lemma averagedEnergyRoot_mark_projection [NeZero N]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (field : Y → ℝ) (hhm : Measurable field) (E : (Fin (N+1) → Spin) → ℝ)
    {H D : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s (fun i : I×Fin (N+1) => Q i.1)
      m field (locatedFactor ψ) E-
      (∫ h,terminalMean ν s Q m ψ Fin.succ (E+fieldEnergy field h) ∂rootLaw (N+1) (fun _ => ξ))|≤
        2*D*s/(N+1) := by
  let : IsProbabilityMeasure (rootLaw (N+1) (fun _ => ξ)) := rootLawProbability _ _
  rw [averagedEnergyRoot_eq_terminalMean]
  change |(∫ h,terminalMean ν s Q m ψ id (E+fieldEnergy field h) ∂rootLaw (N+1) (fun _ => ξ))-
    (∫ h,terminalMean ν s Q m ψ Fin.succ (E+fieldEnergy field h) ∂rootLaw (N+1) (fun _ => ξ))|≤_
  rw [← integral_sub (terminalMean_field_integrable ξ ν s Q m hm ψ field hhm id E hH hh hf)
    (terminalMean_field_integrable ξ ν s Q m hm ψ field hhm Fin.succ E hH hh hf)]
  exact abs_integral_le_bound (fun _ => terminalMean_mark_projection ν s Q m hm ψ _ hf)

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass
open scoped BigOperators
namespace FiniteLaw
variable {ι κ Ω : Type} [Fintype ι] [Fintype κ] [Fintype Ω] [DecidableEq ι] [DecidableEq κ]
lemma expect_pi_curry (Q : ι → κ → FiniteLaw Ω) (f : (ι×κ → Ω) → ℝ) :
    (pi (fun i => pi (Q i))).expect (fun x => f (fun z => x z.1 z.2))=
      (pi (fun z : ι×κ => Q z.1 z.2)).expect f := by
  classical
  symm
  unfold expect
  apply Fintype.sum_equiv (Equiv.curry ι κ Ω)
  intro x
  simp only [pi,Equiv.curry_apply,Function.curry,Fintype.prod_prod_type]

end FiniteLaw
namespace KernelTower
variable {ι κ Ω : Type} [Fintype ι] [Fintype κ] [Fintype Ω] [DecidableEq ι] [DecidableEq κ]
lemma pi_curry_projects (n : ℕ) (T : ι → κ → KernelTower Ω n) :
    Projects (fun x : ι → κ → Ω => fun z : ι×κ => x z.1 z.2) n
      (pi n (fun i => pi n (T i))) (pi n (fun z : ι×κ => T z.1 z.2)) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨FiniteLaw.expect_pi_curry (fun i j => (T i j).1),fun a => ih (fun i j => (T i j).2 (a i j))⟩

lemma pi_injective_projects (e : ι → κ) (he : Function.Injective e) (n : ℕ) (T : κ → KernelTower Ω n) :
    Projects (fun x : κ → Ω => fun i => x (e i)) n
      (pi n T) (pi n (fun i => T (e i))) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨FiniteLaw.expect_pi_injective (fun j => (T j).1) e he,fun a => ih (fun j => (T j).2 (a j))⟩

lemma pi_rect_castSucc_projects (n k q : ℕ) (T : Fin k → Fin (q+1) → KernelTower Ω n) :
    Projects (fun x : Fin k → Fin (q+1) → Ω => fun z : Fin k×Fin q => x z.1 z.2.castSucc) n
      (pi n (fun i => piTower n (T i)))
      (piTower n (fun z : Fin k×Fin q => T z.1 z.2.castSucc)) := by
  simp only [piTower_eq_pi]
  exact (pi_curry_projects n T).comp n
    (pi_injective_projects (fun z : Fin k×Fin q => (z.1,z.2.castSucc))
      (by
        intro a b h
        apply Prod.ext
        · exact congrArg (fun z : Fin k×Fin (q+1) => z.1) h
        · exact (Fin.castSucc_injective q) (congrArg (fun z : Fin k×Fin (q+1) => z.2) h)) n _)
end KernelTower
end DilutedSpinGlass

end

end OAI
