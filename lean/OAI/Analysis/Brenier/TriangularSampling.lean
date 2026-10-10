import OAI.Analysis.Brenier.TriangularRecursion

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem358

/-- Appending the last coordinate identifies a finite product law with a product of
its prefix law and its last-coordinate law. -/
theorem measurePreserving_finSnoc {X : Type*} [MeasurableSpace X]
    (n : ℕ) (η : Measure X) [SigmaFinite η] :
    MeasurePreserving (fun p : (Fin n → X) × X => Fin.snoc p.1 p.2)
      ((Measure.pi fun _ : Fin n => η).prod η)
      (Measure.pi fun _ : Fin (n + 1) => η) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => η)
    (Fin.last n)).symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X)
      (Fin.last n))
  have hh := h.comp (Measure.measurePreserving_swap
    (μ := Measure.pi fun _ : Fin n => η) (ν := η))
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last,
    Fin.snocEquiv, Function.comp_def] using hh

/-- Splitting the prefix and last coordinate preserves a finite product law. -/
theorem measurePreserving_finInitLast {X : Type*} [MeasurableSpace X]
    (n : ℕ) (η : Measure X) [SigmaFinite η] :
    MeasurePreserving (fun x : Fin (n + 1) → X => (Fin.init x, x (Fin.last n)))
      (Measure.pi fun _ : Fin (n + 1) => η)
      ((Measure.pi fun _ : Fin n => η).prod η) := by
  have h := Measure.measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => η) (Fin.last n))
  simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.removeNth,
    Function.comp_def, Fin.init] using h

end Problem358

end

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Problem358

namespace TriangularSampling

variable {A B X Y : Type*}
  [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- A measurable triangular sampler has the prescribed dependent-product law
when its prefix has the prescribed law and its last coordinate has the
prescribed conditional law almost everywhere. -/
theorem map_prod_eq_compProd
    (μ : Measure A) (η : Measure B) (ρ : Measure X) (κ : Kernel X Y)
    [SFinite μ] [SFinite η] [SFinite ρ] [IsSFiniteKernel κ]
    (F : A → X) (G : A × B → Y)
    (hF : Measurable F) (hG : Measurable G)
    (hbase : Measure.map F μ = ρ)
    (hfiber : ∀ᵐ a ∂μ, Measure.map (fun b => G (a, b)) η = κ (F a)) :
    Measure.map (fun p : A × B => (F p.1, G p)) (μ.prod η) = ρ ⊗ₘ κ := by
  ext s hs
  have hpair : Measurable (fun p : A × B => (F p.1, G p)) :=
    (hF.comp measurable_fst).prodMk hG
  rw [Measure.map_apply hpair hs, Measure.prod_apply (hs.preimage hpair),
    Measure.compProd_apply hs, ← hbase,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hF]
  apply lintegral_congr_ae
  filter_upwards [hfiber] with a ha
  change η ((fun b => G (a, b)) ⁻¹' (Prod.mk (F a) ⁻¹' s)) =
    κ (F a) (Prod.mk (F a) ⁻¹' s)
  have hGa : Measurable (fun b : B => G (a, b)) :=
    hG.comp measurable_prodMk_left
  have hsa : MeasurableSet (Prod.mk (F a) ⁻¹' s) :=
    measurable_prodMk_left hs
  rw [← ha]
  exact (Measure.map_apply hGa hsa).symm

/-- Splitting a finite product at its last coordinate preserves its product law. -/
theorem map_init_last_pi {Z : Type*} [MeasurableSpace Z]
    (η : Measure Z) [SigmaFinite η] (n : ℕ) :
    Measure.map (fun s : Fin (n + 1) → Z => (Fin.init s, s (Fin.last n)))
      (Measure.pi (fun _ : Fin (n + 1) => η)) =
      (Measure.pi (fun _ : Fin n => η)).prod η := by
  have h := Measure.measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => η) (Fin.last n))
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply,
    Fin.insertNthEquiv_symm_apply, Fin.removeNth_last, Prod.swap_prod_mk] using h.map_eq

/-- The last-coordinate induction step for the law of a finite triangular sampler. -/
theorem map_snoc_pi_eq
    (n : ℕ) (η : Measure B) [SigmaFinite η]
    (ρ : Measure (Fin n → Y)) (κ : Kernel (Fin n → Y) Y)
    [SFinite ρ] [IsSFiniteKernel κ]
    (F : (Fin n → B) → (Fin n → Y)) (G : (Fin n → B) × B → Y)
    (hF : Measurable F) (hG : Measurable G)
    (hbase : Measure.map F (Measure.pi (fun _ : Fin n => η)) = ρ)
    (hfiber : ∀ᵐ a ∂Measure.pi (fun _ : Fin n => η),
      Measure.map (fun b => G (a, b)) η = κ (F a)) :
    Measure.map (fun s : Fin (n + 1) → B =>
      Fin.snoc (F (Fin.init s)) (G (Fin.init s, s (Fin.last n))))
      (Measure.pi (fun _ : Fin (n + 1) => η)) =
      Measure.map (fun p : (Fin n → Y) × Y => (Fin.snoc p.1 p.2 : Fin (n + 1) → Y)) (ρ ⊗ₘ κ) := by
  let μ := Measure.pi (fun _ : Fin n => η)
  have hsplit : Measurable (fun s : Fin (n + 1) → B =>
      (Fin.init s, s (Fin.last n))) :=
    (measurable_pi_iff.2 fun i => measurable_pi_apply i.castSucc).prodMk
      (measurable_pi_apply (Fin.last n))
  have hsnoc : Measurable (fun p : (Fin n → Y) × Y => (Fin.snoc p.1 p.2 : Fin (n + 1) → Y)) := by
    apply measurable_pi_iff.2
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using
        (measurable_snd : Measurable (fun p : (Fin n → Y) × Y => p.2))
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (measurable_pi_apply j).comp
          (measurable_fst : Measurable (fun p : (Fin n → Y) × Y => p.1))
  have hpair : Measurable (fun p : (Fin n → B) × B => (F p.1, G p)) :=
    (hF.comp measurable_fst).prodMk hG
  have htotal : Measurable (fun p : (Fin n → B) × B =>
      (Fin.snoc (F p.1) (G p) : Fin (n + 1) → Y)) := by
    simpa only [Function.comp_def] using hsnoc.comp hpair
  calc
    _ = Measure.map (fun p : (Fin n → B) × B => (Fin.snoc (F p.1) (G p) : Fin (n + 1) → Y))
        (μ.prod η) := by
      rw [show μ.prod η = Measure.map
        (fun s : Fin (n + 1) → B => (Fin.init s, s (Fin.last n)))
        (Measure.pi (fun _ : Fin (n + 1) => η)) from
          (map_init_last_pi η n).symm]
      rw [Measure.map_map htotal hsplit]
      rfl
    _ = Measure.map (fun p : (Fin n → Y) × Y => (Fin.snoc p.1 p.2 : Fin (n + 1) → Y))
        (Measure.map (fun p : (Fin n → B) × B => (F p.1, G p)) (μ.prod η)) := by
      rw [Measure.map_map hsnoc hpair]
      rfl
    _ = _ := by
      rw [map_prod_eq_compProd μ η ρ κ F G hF hG hbase hfiber]

end TriangularSampling

end Problem358

namespace Problem358.TriangularSampling

/-- Successive conditional quantiles sample a consistent family of prefix laws.
The conditional law is needed only almost everywhere under the prescribed
prefix law, so values of a quantile outside its valid prefix domain are irrelevant. -/
theorem map_sample_pi_eq
    (Q : TriangularRecursion.ConditionalFamily)
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (η : Measure ℝ) [SigmaFinite η]
    (ρ : (n : ℕ) → Measure (Fin n → ℝ))
    (κ : (n : ℕ) → Kernel (Fin n → ℝ) ℝ)
    [∀ n, SFinite (ρ n)] [∀ n, IsSFiniteKernel (κ n)]
    (hzero : ρ 0 = Measure.pi (fun _ : Fin 0 => η))
    (hstep : ∀ n, ρ (n + 1) =
      Measure.map (fun p : (Fin n → ℝ) × ℝ =>
        (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ)) (ρ n ⊗ₘ κ n))
    (hfiber : ∀ n, ∀ᵐ x ∂ρ n, Measure.map (Q n x) η = κ n x) :
    ∀ n, Measure.map (TriangularRecursion.sample Q n)
      (Measure.pi (fun _ : Fin n => η)) = ρ n := by
  intro n
  induction n with
  | zero =>
      change Measure.map id (Measure.pi (fun _ : Fin 0 => η)) = ρ 0
      rw [Measure.map_id]
      exact hzero.symm
  | succ n ih =>
      have hF := TriangularRecursion.measurable_sample Q hQ n
      have hG : Measurable (fun p : (Fin n → ℝ) × ℝ =>
          Q n (TriangularRecursion.sample Q n p.1) p.2) := by
        simpa only [Function.comp_def] using
          (hQ n).comp ((hF.comp measurable_fst).prodMk measurable_snd)
      have hf : ∀ᵐ a ∂Measure.pi (fun _ : Fin n => η),
          Measure.map (Q n (TriangularRecursion.sample Q n a)) η =
            κ n (TriangularRecursion.sample Q n a) := by
        exact ae_of_ae_map (p := fun x : Fin n → ℝ => Measure.map (Q n x) η = κ n x)
          hF.aemeasurable (by rw [ih]; exact hfiber n)
      rw [hstep n]
      exact map_snoc_pi_eq n η (ρ n) (κ n) (TriangularRecursion.sample Q n)
        (fun p => Q n (TriangularRecursion.sample Q n p.1) p.2) hF hG ih hf

/-- A finite-dimensional version: only the first `N` disintegration identities
and conditional laws are required. No consistency beyond the desired dimension
is assumed. -/
theorem map_sample_pi_eq_of_steps
    (N : ℕ) (Q : TriangularRecursion.ConditionalFamily)
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (η : Measure ℝ) [SigmaFinite η]
    (ρ : (n : ℕ) → Measure (Fin n → ℝ))
    (κ : (n : ℕ) → Kernel (Fin n → ℝ) ℝ)
    (hρ : ∀ n ≤ N, SFinite (ρ n))
    (hκ : ∀ n < N, IsSFiniteKernel (κ n))
    (hzero : ρ 0 = Measure.pi (fun _ : Fin 0 => η))
    (hstep : ∀ n < N, ρ (n + 1) =
      Measure.map (fun p : (Fin n → ℝ) × ℝ =>
        (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ)) (ρ n ⊗ₘ κ n))
    (hfiber : ∀ n < N, ∀ᵐ x ∂ρ n, Measure.map (Q n x) η = κ n x) :
    Measure.map (TriangularRecursion.sample Q N)
      (Measure.pi (fun _ : Fin N => η)) = ρ N := by
  have hall : ∀ n ≤ N, Measure.map (TriangularRecursion.sample Q n)
      (Measure.pi (fun _ : Fin n => η)) = ρ n := by
    intro n
    induction n with
    | zero =>
        intro _
        change Measure.map id (Measure.pi (fun _ : Fin 0 => η)) = ρ 0
        rw [Measure.map_id]
        exact hzero.symm
    | succ n ih =>
        intro hn
        have hn' : n < N := by omega
        have ih' := ih hn'.le
        let := hρ n hn'.le
        let := hκ n hn'
        have hF := TriangularRecursion.measurable_sample Q hQ n
        have hG : Measurable (fun p : (Fin n → ℝ) × ℝ =>
            Q n (TriangularRecursion.sample Q n p.1) p.2) := by
          simpa only [Function.comp_def] using
            (hQ n).comp ((hF.comp measurable_fst).prodMk measurable_snd)
        have hf : ∀ᵐ a ∂Measure.pi (fun _ : Fin n => η),
            Measure.map (Q n (TriangularRecursion.sample Q n a)) η =
              κ n (TriangularRecursion.sample Q n a) := by
          exact ae_of_ae_map (p := fun x : Fin n → ℝ => Measure.map (Q n x) η = κ n x)
            hF.aemeasurable (by rw [ih']; exact hfiber n hn')
        rw [hstep n hn']
        exact map_snoc_pi_eq n η (ρ n) (κ n) (TriangularRecursion.sample Q n)
          (fun p => Q n (TriangularRecursion.sample Q n p.1) p.2) hF hG ih' hf
  exact hall N le_rfl

end Problem358.TriangularSampling

end

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace Problem358

/-- Law induction for triangular samplers with explicit conditional laws. -/
theorem map_triangular_recursion
    {X : Type*} [MeasurableSpace X] (η : Measure X) [SigmaFinite η]
    (ν : (n : ℕ) → Measure (Fin n → X))
    (κ : (n : ℕ) → Kernel (Fin n → X) X)
    [∀ n, SFinite (ν n)] [∀ n, IsSFiniteKernel (κ n)]
    (F : (n : ℕ) → (Fin n → X) → (Fin n → X))
    (G : (n : ℕ) → ((Fin n → X) × X) → X)
    (hF : ∀ n, Measurable (F n)) (hG : ∀ n, Measurable (G n))
    (hzero : Measure.map (F 0) (Measure.pi fun _ : Fin 0 => η) = ν 0)
    (hrecursion : ∀ n s t,
      F (n + 1) (Fin.snoc s t) = Fin.snoc (F n s) (G n (s, t)))
    (htarget : ∀ n, ν (n + 1) =
      Measure.map (fun p : (Fin n → X) × X => Fin.snoc p.1 p.2) (ν n ⊗ₘ κ n))
    (hfiber : ∀ n, ∀ᵐ s ∂(Measure.pi fun _ : Fin n => η),
      Measure.map (fun t => G n (s, t)) η = κ n (F n s)) :
    ∀ n, Measure.map (F n) (Measure.pi fun _ : Fin n => η) = ν n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    let append : ((Fin n → X) × X) → (Fin (n + 1) → X) :=
      fun p => Fin.snoc p.1 p.2
    let pair : ((Fin n → X) × X) → ((Fin n → X) × X) :=
      fun p => (F n p.1, G n p)
    have happend : Measurable append := (measurePreserving_finSnoc n η).measurable
    have hpair : Measurable pair := ((hF n).comp measurable_fst).prodMk (hG n)
    have heq : F (n + 1) ∘ append = append ∘ pair := by
      funext p
      exact hrecursion n p.1 p.2
    have hsource := (measurePreserving_finSnoc n η).map_eq
    change Measure.map append ((Measure.pi fun _ : Fin n => η).prod η) = _ at hsource
    rw [← hsource, Measure.map_map (hF (n + 1)) happend, heq,
      ← Measure.map_map happend hpair]
    have hlaw := TriangularSampling.map_prod_eq_compProd
      (Measure.pi fun _ : Fin n => η) η (ν n) (κ n)
      (F n) (G n) (hF n) (hG n) ih (hfiber n)
    change Measure.map pair _ = _ at hlaw
    rw [hlaw]
    exact (htarget n).symm

end Problem358

namespace Problem358.TriangularRecursion

/-- The law of the recursive sampler follows from conditional laws valid almost
 everywhere under the desired prefix law. No pointwise law on null prefixes is needed. -/
theorem map_sample_of_conditional_laws
    (η : Measure ℝ) [SigmaFinite η]
    (Q : ConditionalFamily)
    (ν : (n : ℕ) → Measure (Fin n → ℝ))
    (κ : (n : ℕ) → Kernel (Fin n → ℝ) ℝ)
    [∀ n, SFinite (ν n)] [∀ n, IsSFiniteKernel (κ n)]
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (hzero : (Measure.pi fun _ : Fin 0 => η) = ν 0)
    (htarget : ∀ n, ν (n + 1) =
      Measure.map (fun p : (Fin n → ℝ) × ℝ => Fin.snoc p.1 p.2) (ν n ⊗ₘ κ n))
    (hfiber : ∀ n, ∀ᵐ x ∂ν n, Measure.map (Q n x) η = κ n x) :
    ∀ n, Measure.map (sample Q n) (Measure.pi fun _ : Fin n => η) = ν n := by
  intro n
  induction n with
  | zero => simpa [sample] using hzero
  | succ n ih =>
    let append : ((Fin n → ℝ) × ℝ) → (Fin (n + 1) → ℝ) :=
      fun p => Fin.snoc p.1 p.2
    let G : ((Fin n → ℝ) × ℝ) → ℝ :=
      fun p => Q n (sample Q n p.1) p.2
    let pair : ((Fin n → ℝ) × ℝ) → ((Fin n → ℝ) × ℝ) :=
      fun p => (sample Q n p.1, G p)
    have hF := measurable_sample Q hQ
    have hG : Measurable G :=
      (hQ n).comp (((hF n).comp measurable_fst).prodMk measurable_snd)
    have hpair : Measurable pair := ((hF n).comp measurable_fst).prodMk hG
    have happend : Measurable append := (measurePreserving_finSnoc n η).measurable
    have heq : sample Q (n + 1) ∘ append = append ∘ pair := by
      funext p
      exact sample_snoc Q n p.1 p.2
    have hpull : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => η),
        Measure.map (fun t => G (s, t)) η = κ n (sample Q n s) := by
      change ∀ᵐ s ∂(Measure.pi fun _ : Fin n => η),
        Measure.map (Q n (sample Q n s)) η = κ n (sample Q n s)
      apply ae_of_ae_map (p := fun x => Measure.map (Q n x) η = κ n x)
        (hF n).aemeasurable
      rw [ih]
      exact hfiber n
    have hsource := (measurePreserving_finSnoc n η).map_eq
    change Measure.map append ((Measure.pi fun _ : Fin n => η).prod η) = _ at hsource
    rw [← hsource, Measure.map_map (hF (n + 1)) happend, heq,
      ← Measure.map_map happend hpair]
    have hlaw := TriangularSampling.map_prod_eq_compProd
      (Measure.pi fun _ : Fin n => η) η (ν n) (κ n)
      (sample Q n) G (hF n) hG ih hpull
    change Measure.map pair _ = _ at hlaw
    rw [hlaw]
    exact (htarget n).symm

/-- The empty-prefix base law is automatic for probability laws. -/
theorem empty_prefix_law (η : Measure ℝ) [IsProbabilityMeasure η]
    (ν : Measure (Fin 0 → ℝ)) [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : Fin 0 => η) = ν := by
  let x : Fin 0 → ℝ := fun i => Fin.elim0 i
  have heq (μ : Measure (Fin 0 → ℝ)) [IsProbabilityMeasure μ] :
      μ = Measure.dirac x := by
    calc
      μ = Measure.map id μ := Measure.map_id.symm
      _ = Measure.map (fun _ => x) μ := Measure.map_congr
        (Filter.Eventually.of_forall fun y => Subsingleton.elim y x)
      _ = Measure.dirac x := by simp [Measure.map_const]
  exact (heq _).trans (heq ν).symm

/-- Probability-prefix form of the triangular sampling law. -/
theorem map_sample_probability
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (Q : ConditionalFamily)
    (ν : (n : ℕ) → Measure (Fin n → ℝ))
    (κ : (n : ℕ) → Kernel (Fin n → ℝ) ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] [∀ n, IsSFiniteKernel (κ n)]
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (htarget : ∀ n, ν (n + 1) =
      Measure.map (fun p : (Fin n → ℝ) × ℝ => Fin.snoc p.1 p.2) (ν n ⊗ₘ κ n))
    (hfiber : ∀ n, ∀ᵐ x ∂ν n, Measure.map (Q n x) η = κ n x) :
    ∀ n, Measure.map (sample Q n) (Measure.pi fun _ : Fin n => η) = ν n :=
  map_sample_of_conditional_laws η Q ν κ hQ (empty_prefix_law η (ν 0)) htarget hfiber

end Problem358.TriangularRecursion

end

noncomputable section
open MeasureTheory

namespace Problem358.TriangularRecursion

/-- Couple two triangular samplers by using the same independent scalar inputs. -/
def jointPlan (η : Measure ℝ) (Q R : ConditionalFamily) (n : ℕ) :
    Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
  Measure.map (fun s => (sample Q n s, sample R n s))
    (Measure.pi fun _ : Fin n => η)

/-- The joint sampler is measurable whenever both conditional families are measurable. -/
theorem measurable_jointSample (Q R : ConditionalFamily)
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (hR : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => R n p.1 p.2)) (n : ℕ) :
    Measurable (fun s => (sample Q n s, sample R n s)) :=
  (measurable_sample Q hQ n).prodMk (measurable_sample R hR n)

/-- The common-parameter joint law is a probability measure. -/
theorem isProbabilityMeasure_jointPlan (η : Measure ℝ) [IsProbabilityMeasure η]
    (Q R : ConditionalFamily)
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (hR : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => R n p.1 p.2)) (n : ℕ) :
    IsProbabilityMeasure (jointPlan η Q R n) :=
  (Measure.isProbabilityMeasure_map_iff
    (measurable_jointSample Q R hQ hR n).aemeasurable).mpr inferInstance

/-- Its first marginal is exactly the first sampler law. -/
theorem map_fst_jointPlan (η : Measure ℝ) (Q R : ConditionalFamily)
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (hR : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => R n p.1 p.2)) (n : ℕ) :
    Measure.map Prod.fst (jointPlan η Q R n) =
      Measure.map (sample Q n) (Measure.pi fun _ : Fin n => η) := by
  rw [jointPlan, Measure.map_map measurable_fst (measurable_jointSample Q R hQ hR n)]
  rfl

/-- Its second marginal is exactly the second sampler law. -/
theorem map_snd_jointPlan (η : Measure ℝ) (Q R : ConditionalFamily)
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (hR : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => R n p.1 p.2)) (n : ℕ) :
    Measure.map Prod.snd (jointPlan η Q R n) =
      Measure.map (sample R n) (Measure.pi fun _ : Fin n => η) := by
  rw [jointPlan, Measure.map_map measurable_snd (measurable_jointSample Q R hQ hR n)]
  rfl

/-- Taking the midpoint of the coupling is exactly the recursively decomposed midpoint law. -/
theorem map_midpoint_jointPlan (η : Measure ℝ) (Q R : ConditionalFamily)
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (hR : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => R n p.1 p.2)) (n : ℕ) :
    Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (1 / 2 : ℝ) • p.1 + (1 / 2 : ℝ) • p.2) (jointPlan η Q R n) =
      Measure.map (midpoint Q R n) (Measure.pi fun _ : Fin n => η) := by
  rw [jointPlan, Measure.map_map (by fun_prop) (measurable_jointSample Q R hQ hR n)]
  congr 1
  funext s i
  simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, midpoint]
  ring

/-- A fixed-depth coupling certificate needs only the two measurable full samplers
 and their laws, so it also applies to finite-depth conditional families. -/
theorem jointPlan_spec_of_laws (η : Measure ℝ) [IsProbabilityMeasure η]
    (Q R : ConditionalFamily) (n : ℕ)
    {ν μ : Measure (Fin n → ℝ)}
    (hQ : Measurable (sample Q n)) (hR : Measurable (sample R n))
    (hν : Measure.map (sample Q n) (Measure.pi fun _ : Fin n => η) = ν)
    (hμ : Measure.map (sample R n) (Measure.pi fun _ : Fin n => η) = μ) :
    IsProbabilityMeasure (jointPlan η Q R n) ∧
      Measure.map Prod.fst (jointPlan η Q R n) = ν ∧
      Measure.map Prod.snd (jointPlan η Q R n) = μ ∧
      Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (1 / 2 : ℝ) • p.1 + (1 / 2 : ℝ) • p.2) (jointPlan η Q R n) =
        Measure.map (midpoint Q R n) (Measure.pi fun _ : Fin n => η) := by
  have hp := hQ.prodMk hR
  refine ⟨(Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance, ?_, ?_, ?_⟩
  · rw [jointPlan, Measure.map_map measurable_fst hp]
    exact hν
  · rw [jointPlan, Measure.map_map measurable_snd hp]
    exact hμ
  · rw [jointPlan, Measure.map_map (by fun_prop) hp]
    congr 1
    funext s i
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, midpoint]
    ring

end Problem358.TriangularRecursion

end

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Problem358.TriangularRecursion

/-- Measurability only requires the conditional samplers used before the given depth. -/
theorem measurable_sample_upto (Q : ConditionalFamily) (d : ℕ)
    (hQ : ∀ k, k < d → Measurable (fun p : (Fin k → ℝ) × ℝ => Q k p.1 p.2)) :
    ∀ n, n ≤ d → Measurable (sample Q n) := by
  intro n
  induction n with
  | zero => intro _; exact measurable_id
  | succ n ih =>
    intro hn
    have hp : Measurable (fun s : Fin (n+1) → ℝ => sample Q n (Fin.init s)) := by
      apply (ih (Nat.le_of_succ_le hn)).comp
      apply Measurable.of_eval
      intro i
      exact measurable_pi_apply i.castSucc
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [sample_last, Function.comp_def] using
        (hQ n (Nat.lt_of_succ_le hn)).comp
          (hp.prodMk (measurable_pi_apply (Fin.last n)))
    · simpa only [sample, Fin.snoc_castSucc, Function.comp_def] using
        (measurable_pi_apply j).comp hp

/-- Finite-depth sampling law: no regularity or law hypotheses are imposed beyond d. -/
theorem map_sample_of_conditional_laws_upto
    (η : Measure ℝ) [SigmaFinite η] (Q : ConditionalFamily) (d : ℕ)
    (ν : (n : ℕ) → Measure (Fin n → ℝ))
    (κ : (n : ℕ) → Kernel (Fin n → ℝ) ℝ)
    (hν : ∀ n, n ≤ d → SFinite (ν n))
    (hκ : ∀ n, n < d → IsSFiniteKernel (κ n))
    (hQ : ∀ n, n < d → Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (hzero : (Measure.pi fun _ : Fin 0 => η) = ν 0)
    (htarget : ∀ n, n < d → ν (n + 1) =
      Measure.map (fun p : (Fin n → ℝ) × ℝ => Fin.snoc p.1 p.2) (ν n ⊗ₘ κ n))
    (hfiber : ∀ n, n < d → ∀ᵐ x ∂ν n, Measure.map (Q n x) η = κ n x) :
    ∀ n, n ≤ d → Measure.map (sample Q n) (Measure.pi fun _ : Fin n => η) = ν n := by
  intro n
  induction n with
  | zero => intro _; simpa [sample] using hzero
  | succ n ih =>
    intro hn
    have hnle : n ≤ d := Nat.le_of_succ_le hn
    have hnlt : n < d := Nat.lt_of_succ_le hn
    have hind := ih hnle
    let := hν n hnle
    let := hκ n hnlt
    let append : ((Fin n → ℝ) × ℝ) → (Fin (n + 1) → ℝ) :=
      fun p => Fin.snoc p.1 p.2
    let G : ((Fin n → ℝ) × ℝ) → ℝ :=
      fun p => Q n (sample Q n p.1) p.2
    let pair : ((Fin n → ℝ) × ℝ) → ((Fin n → ℝ) × ℝ) :=
      fun p => (sample Q n p.1, G p)
    have hF := measurable_sample_upto Q d hQ n hnle
    have hFsucc := measurable_sample_upto Q d hQ (n+1) hn
    have hG : Measurable G :=
      (hQ n hnlt).comp ((hF.comp measurable_fst).prodMk measurable_snd)
    have hpair : Measurable pair := (hF.comp measurable_fst).prodMk hG
    have happend : Measurable append := (measurePreserving_finSnoc n η).measurable
    have heq : sample Q (n + 1) ∘ append = append ∘ pair := by
      funext p
      exact sample_snoc Q n p.1 p.2
    have hpull : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => η),
        Measure.map (fun t => G (s, t)) η = κ n (sample Q n s) := by
      change ∀ᵐ s ∂(Measure.pi fun _ : Fin n => η),
        Measure.map (Q n (sample Q n s)) η = κ n (sample Q n s)
      apply ae_of_ae_map (p := fun x => Measure.map (Q n x) η = κ n x) hF.aemeasurable
      rw [hind]
      exact hfiber n hnlt
    have hsource := (measurePreserving_finSnoc n η).map_eq
    change Measure.map append ((Measure.pi fun _ : Fin n => η).prod η) = _ at hsource
    rw [← hsource, Measure.map_map hFsucc happend, heq,
      ← Measure.map_map happend hpair]
    have hlaw := TriangularSampling.map_prod_eq_compProd
      (Measure.pi fun _ : Fin n => η) η (ν n) (κ n)
      (sample Q n) G hF hG hind hpull
    change Measure.map pair _ = _ at hlaw
    rw [hlaw]
    exact (htarget n hnlt).symm

/-- Probability-law form with the empty-prefix base case discharged automatically. -/
theorem map_sample_probability_upto
    (η : Measure ℝ) [IsProbabilityMeasure η] (Q : ConditionalFamily) (d : ℕ)
    (ν : (n : ℕ) → Measure (Fin n → ℝ))
    (κ : (n : ℕ) → Kernel (Fin n → ℝ) ℝ)
    (hν : ∀ n, n ≤ d → IsProbabilityMeasure (ν n))
    (hκ : ∀ n, n < d → IsSFiniteKernel (κ n))
    (hQ : ∀ n, n < d → Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (htarget : ∀ n, n < d → ν (n + 1) =
      Measure.map (fun p : (Fin n → ℝ) × ℝ => Fin.snoc p.1 p.2) (ν n ⊗ₘ κ n))
    (hfiber : ∀ n, n < d → ∀ᵐ x ∂ν n, Measure.map (Q n x) η = κ n x) :
    ∀ n, n ≤ d → Measure.map (sample Q n) (Measure.pi fun _ : Fin n => η) = ν n := by
  have hs : ∀ n, n ≤ d → SFinite (ν n) := by
    intro n hn
    let := hν n hn
    infer_instance
  let := hν 0 (Nat.zero_le d)
  exact map_sample_of_conditional_laws_upto η Q d ν κ hs hκ hQ
    (empty_prefix_law η (ν 0)) htarget hfiber

/-- Pointwise valid-prefix preservation also needs conditional data only below d. -/
theorem sample_mem_domains_upto (Q : ConditionalFamily) (d : ℕ)
    (D : (n : ℕ) → Set (Fin n → ℝ))
    (hzero : ∀ x, x ∈ D 0)
    (hstep : ∀ n, n < d → ∀ x, x ∈ D n → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      Fin.snoc x (Q n x t) ∈ D (n+1)) :
    ∀ n, n ≤ d → ∀ s, (∀ i, s i ∈ Set.Ioo (0 : ℝ) 1) → sample Q n s ∈ D n := by
  intro n
  induction n with
  | zero => intro _ s _; exact hzero s
  | succ n ih =>
    intro hn s hs
    exact hstep n (Nat.lt_of_succ_le hn) (sample Q n (Fin.init s))
      (ih (Nat.le_of_succ_le hn) (Fin.init s) (fun i => hs i.castSucc))
      (s (Fin.last n)) (hs (Fin.last n))

end Problem358.TriangularRecursion

end

end OAI
