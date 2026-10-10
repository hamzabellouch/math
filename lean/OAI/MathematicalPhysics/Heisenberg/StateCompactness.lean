import OAI.MathematicalPhysics.Heisenberg.ThermodynamicDynamics

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

namespace Heisenberg
instance quasiLocalClosed (d ℓ : ℕ) : IsClosed (quasiLocalAlgebra d ℓ : Set (SpinOperator d ℓ)) :=
  StarSubalgebra.isClosed_topologicalClosure _

theorem countable_monoidClosure {M : Type*} [Monoid M] {s : Set M}
    (hs : s.Countable) : (Submonoid.closure s : Set M).Countable := by
  have : Countable s := hs.to_subtype
  let f : List s → M := fun l => (l.map Subtype.val).prod
  apply (Set.countable_range f).mono
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem x hx => exact ⟨[⟨x, hx⟩], by simp [f]⟩
  | one => exact ⟨[], rfl⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨l, rfl⟩ := ihx
    obtain ⟨k, rfl⟩ := ihy
    exact ⟨l ++ k, by simp [f]⟩

instance quasiLocalSeparable (d ℓ : ℕ) : TopologicalSpace.SeparableSpace (QuasiLocal d ℓ) := by
  let s : Set (SpinOperator d ℓ) := {A | ∃ x a b, A = matrixUnit d ℓ x a b}
  have hs : s.Countable := by
    have h := Set.countable_range (fun p : Site d × Level ℓ × Level ℓ =>
      matrixUnit d ℓ p.1 p.2.1 p.2.2)
    apply h.mono
    rintro A ⟨x, a, b, rfl⟩
    exact ⟨⟨x,a,b⟩, rfl⟩
  have hu : (s ∪ star s).Countable := hs.union (by simpa only [Set.image_star] using hs.image star)
  have hsep := (countable_monoidClosure hu).isSeparable.span (R := ℂ)
  have hadj : TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set (SpinOperator d ℓ)) := by
    change TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set (SpinOperator d ℓ))
    rw [StarAlgebra.adjoin_eq_span]
    exact hsep
  have hc : TopologicalSpace.IsSeparable (quasiLocalAlgebra d ℓ : Set (SpinOperator d ℓ)) := by
    change TopologicalSpace.IsSeparable ((StarAlgebra.adjoin ℂ s).topologicalClosure : Set (SpinOperator d ℓ))
    rw [StarSubalgebra.topologicalClosure_coe]
    exact hadj.closure
  exact hc.separableSpace

open scoped ComplexOrder

theorem positive_norm_bound {E : Type*} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (φ : E →L[ℂ] ℂ) (hn : φ 1 = 1)
    (hpos : ∀ B, 0 ≤ φ (star B * B)) : ‖φ‖ ≤ 4 := by
  have hp : ∀ A : E, 0 ≤ A → 0 ≤ φ A := by
    intro A hA
    obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
    exact hpos B
  let f : E →ₚ[ℂ] ℂ :=
    { φ.toLinearMap with
      monotone' := by
        intro A B h
        change φ A ≤ φ B
        have h' := hp (B - A) (sub_nonneg.mpr h)
        simpa only [map_sub, sub_nonneg] using h' }
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  obtain ⟨x, hx, hnorm, hA⟩ := CStarAlgebra.exists_sum_four_nonneg A
  conv_lhs => rw [hA, map_sum]
  calc
    ‖∑ i : Fin 4, φ (Complex.I ^ (i : ℕ) • x i)‖ ≤
        ∑ i : Fin 4, ‖φ (Complex.I ^ (i : ℕ) • x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
      have hi := PositiveLinearMap.norm_apply_le_of_nonneg f (x i) (hx i)
      change ‖φ (x i)‖ ≤ ‖φ 1‖ * ‖x i‖ at hi
      simpa only [hn, norm_one, one_mul] using hi.trans
        (by simpa only [hn, norm_one, one_mul] using hnorm i)
    _ = 4 * ‖A‖ := by simp

theorem state_norm_bound {d ℓ : ℕ} (ω : State d ℓ) : ‖ω.functional‖ ≤ 4 := by
  let : PartialOrder (QuasiLocal d ℓ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (QuasiLocal d ℓ) := CStarAlgebra.spectralOrderedRing _
  exact positive_norm_bound ω.functional ω.normalized
    (fun B => ⟨(ω.positive B).2, by simpa using (ω.positive B).1.symm⟩)

open Filter in
theorem bounded_functionals_subsequence {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace.SeparableSpace E]
    (φ : ℕ → E →L[ℂ] ℂ) (C : ℝ) (hb : ∀ n, ‖φ n‖ ≤ C) :
    ∃ ψ : E →L[ℂ] ℂ, ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ A : E, Tendsto (fun n => φ (κ n) A) atTop (nhds (ψ A)) := by
  let u : ℕ → WeakDual ℂ E := fun n => WeakDual.toStrongDual.symm (φ n)
  have hu : ∀ n, u n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C := by
    intro n
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      u, LinearEquiv.apply_symm_apply] using hb n
  obtain ⟨ψ, _, κ, hκ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℂ E 0 C hu
  exact ⟨WeakDual.toStrongDual ψ, κ, hκ,
    fun A => (WeakDual.eval_continuous A).tendsto ψ |>.comp hlim⟩

open Filter in

theorem state_subsequence {d ℓ : ℕ} (ω : ℕ → State d ℓ) :
    ∃ η : State d ℓ, ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ A : QuasiLocal d ℓ, Tendsto (fun n => (ω (κ n)).functional A)
        atTop (nhds (η.functional A)) := by
  obtain ⟨ψ, κ, hκ, hA⟩ := bounded_functionals_subsequence
    (fun n => (ω n).functional) 4 (fun n => state_norm_bound (ω n))
  have hn : ψ 1 = 1 := by
    have h := hA 1
    simp only [(ω _).normalized] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hp (A : QuasiLocal d ℓ) : (ψ (star A * A)).im = 0 ∧ 0 ≤ (ψ (star A * A)).re := by
    constructor
    · have h := Complex.continuous_im.tendsto _ |>.comp (hA (star A * A))
      change Tendsto (fun n => ((ω (κ n)).functional (star A * A)).im) atTop
        (nhds ((ψ (star A * A)).im)) at h
      simp only [((ω _).positive A).1] at h
      exact tendsto_nhds_unique h tendsto_const_nhds
    · exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp (hA (star A * A)))
        (Filter.Eventually.of_forall fun n => ((ω (κ n)).positive A).2)
  exact ⟨⟨ψ, hn, hp⟩, κ, hκ, hA⟩

open scoped InnerProductSpace

def operatorInclusion (d ℓ : ℕ) : QuasiLocal d ℓ →L[ℂ] SpinOperator d ℓ :=
  (quasiLocalAlgebra d ℓ).toSubalgebra.toSubmodule.subtypeL

def vectorFunctional {d ℓ : ℕ} (v : SpinHilbert d ℓ) : QuasiLocal d ℓ →L[ℂ] ℂ :=
  (innerSL ℂ v).comp ((ContinuousLinearMap.apply ℂ (SpinHilbert d ℓ) v).comp
    (operatorInclusion d ℓ))

@[simp] theorem vectorFunctional_apply {d ℓ : ℕ} (v : SpinHilbert d ℓ)
    (A : QuasiLocal d ℓ) : vectorFunctional v A = ⟪v, (A : SpinOperator d ℓ) v⟫_ℂ := rfl

def vectorState {d ℓ : ℕ} (v : SpinHilbert d ℓ) (hv : ‖v‖ = 1) : State d ℓ where
  functional := vectorFunctional v
  normalized := by
    change ⟪v, v⟫_ℂ = 1
    rw [inner_self_eq_norm_sq_to_K, hv]
    norm_num
  positive A := by
    have h : vectorFunctional v (star A * A) =
        ⟪(A : SpinOperator d ℓ) v, (A : SpinOperator d ℓ) v⟫_ℂ := by
      change ⟪v, (star (A : SpinOperator d ℓ)) ((A : SpinOperator d ℓ) v)⟫_ℂ = _
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    rw [h]
    exact ⟨inner_self_im (𝕜 := ℂ) _, inner_self_nonneg (𝕜 := ℂ)⟩

def configVector {d ℓ : ℕ} (c : Configuration d ℓ) : SpinHilbert d ℓ :=
  lp.single 2 c 1

@[simp] theorem norm_configVector {d ℓ : ℕ} (c : Configuration d ℓ) :
    ‖configVector c‖ = 1 := by
  simp [configVector, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

@[simp] theorem vectorFunctional_configVector {d ℓ : ℕ} (c : Configuration d ℓ)
    (A : QuasiLocal d ℓ) : vectorFunctional (configVector c) A =
      (A : SpinOperator d ℓ) (configVector c) c := by
  simp [vectorFunctional_apply, configVector, lp.inner_single_left]

abbrev FiniteConfiguration {d : ℕ} (ℓ : ℕ) (F : Finset (Site d)) := F → Level ℓ

def extendConfig {d ℓ : ℕ} (F : Finset (Site d)) (c : FiniteConfiguration ℓ F) :
    Configuration d ℓ :=
  Finsupp.onFinset F (fun x => if hx : x ∈ F then c ⟨x,hx⟩ else 0)
    (by intro x; contrapose!; simp_all)

@[simp] theorem extendConfig_apply {d ℓ : ℕ} (F : Finset (Site d))
    (c : FiniteConfiguration ℓ F) (x : Site d) :
    extendConfig F c x = if hx : x ∈ F then c ⟨x,hx⟩ else 0 := by
  rfl

def finiteTraceFunctional (d ℓ : ℕ) (F : Finset (Site d)) : QuasiLocal d ℓ →L[ℂ] ℂ :=
  (Fintype.card (FiniteConfiguration ℓ F) : ℂ)⁻¹ •
    ∑ c : FiniteConfiguration ℓ F, vectorFunctional (configVector (extendConfig F c))

@[simp] theorem finiteTraceFunctional_apply (d ℓ : ℕ) (F : Finset (Site d))
    (A : QuasiLocal d ℓ) : finiteTraceFunctional d ℓ F A =
    (Fintype.card (FiniteConfiguration ℓ F) : ℂ)⁻¹ *
      ∑ c : FiniteConfiguration ℓ F, (A : SpinOperator d ℓ)
        (configVector (extendConfig F c)) (extendConfig F c) := by
  simp only [finiteTraceFunctional, smul_apply, sum_apply, smul_eq_mul,
    vectorFunctional_configVector]

def finiteTraceState (d ℓ : ℕ) (F : Finset (Site d)) : State d ℓ where
  functional := finiteTraceFunctional d ℓ F
  normalized := by
    have hcard : (Fintype.card (FiniteConfiguration ℓ F) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have h (c : FiniteConfiguration ℓ F) :
        vectorFunctional (configVector (extendConfig F c)) 1 = 1 :=
      (vectorState _ (norm_configVector _)).normalized
    simp only [finiteTraceFunctional, smul_apply, sum_apply, h, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact inv_mul_cancel₀ hcard
  positive A := by
    have h (c : FiniteConfiguration ℓ F) :=
      (vectorState (configVector (extendConfig F c)) (norm_configVector _)).positive A
    change ((finiteTraceFunctional d ℓ F) (star A * A)).im = 0 ∧
      0 ≤ ((finiteTraceFunctional d ℓ F) (star A * A)).re
    simp only [finiteTraceFunctional, smul_apply,
      sum_apply, smul_eq_mul]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.mul_re, sub_zero]
    rw [Complex.im_sum, Complex.re_sum]
    constructor
    · convert mul_zero ((Fintype.card (FiniteConfiguration ℓ F) : ℝ)⁻¹) using 1
      congr 1
      apply Finset.sum_eq_zero
      intro c _
      exact (h c).1
    · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun c _ => (h c).2)

@[simp] theorem configVector_apply {d ℓ : ℕ} (c z : Configuration d ℓ) :
    configVector c z = if z = c then 1 else 0 := by
  simp only [configVector, lp.single_apply, Pi.single_apply, eq_comm]

@[simp] theorem matrixUnit_configVector {d ℓ : ℕ} (x : Site d) (a b : Level ℓ)
    (c : Configuration d ℓ) : matrixUnit d ℓ x a b (configVector c) =
      if c x = b then configVector (c.update x a) else 0 := by
  ext z
  simp only [matrixUnit_apply, configVector_apply]
  by_cases hc : c x = b
  · simp only [hc, ite_true, configVector_apply]
    by_cases hz : z x = a
    · simp only [hz, ite_true]
      have hh : z.update x b = c ↔ z = c.update x a := by
        constructor
        · intro he
          have hh := congrArg (fun q : Configuration d ℓ => q.update x a) he
          simpa only [Finsupp.update_idem, ← hz, Finsupp.update_self] using hh
        · rintro rfl
          simp [← hc]
      simp only [hh]
    · have hne : z ≠ c.update x a := by
        intro he
        have hh := congrArg (fun q : Configuration d ℓ => q x) he
        simp only [Finsupp.update_apply, ite_true] at hh
        exact hz hh
      simp [hz, hne]
  · simp only [hc, ite_false, lp.coeFn_zero, Pi.zero_apply]
    have hne : z.update x b ≠ c := by
      intro he
      have hh := congrArg (fun q : Configuration d ℓ => q x) he
      simp only [Finsupp.update_apply, ite_true] at hh
      exact hc hh.symm
    simp [hne]

def finiteConfigPerm {d ℓ : ℕ} {F : Finset (Site d)} (x : F)
    (σ : Equiv.Perm (Level ℓ)) : Equiv.Perm (FiniteConfiguration ℓ F) where
  toFun c := Function.update c x (σ (c x))
  invFun c := Function.update c x (σ.symm (c x))
  left_inv c := by ext y; by_cases h : y = x <;> simp [h]
  right_inv c := by ext y; by_cases h : y = x <;> simp [h]

@[simp] theorem extendConfig_perm {d ℓ : ℕ} {F : Finset (Site d)} (x : F)
    (σ : Equiv.Perm (Level ℓ)) (c : FiniteConfiguration ℓ F) :
    extendConfig F (finiteConfigPerm x σ c) =
      (extendConfig F c).update x (σ (c x)) := by
  ext y
  by_cases h : y = x
  · subst y
    simp [extendConfig_apply, finiteConfigPerm, Finsupp.update_apply, x.property]
  · by_cases hy : y ∈ F
    · have hn : (⟨y, hy⟩ : F) ≠ x := fun he => h (congrArg Subtype.val he)
      simp [extendConfig_apply, finiteConfigPerm,
        Finsupp.update_apply, hy, h, hn]
    · simp [extendConfig_apply, Finsupp.update_apply, hy, h]

theorem finiteTraceFunctional_cyclic_unit {d ℓ : ℕ} (F : Finset (Site d))
    {x : Site d} (hx : x ∈ F) (a b : Level ℓ) (A : QuasiLocal d ℓ) :
    finiteTraceFunctional d ℓ F (localUnit d ℓ x a b * A) =
      finiteTraceFunctional d ℓ F (A * localUnit d ℓ x a b) := by
  simp only [finiteTraceFunctional_apply]
  congr 1
  let e := finiteConfigPerm (⟨x,hx⟩ : F) (Equiv.swap a b)
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro c _
  change (matrixUnit d ℓ x a b) ((A : SpinOperator d ℓ)
      (configVector (extendConfig F (e c)))) (extendConfig F (e c)) =
    (A : SpinOperator d ℓ) ((matrixUnit d ℓ x a b)
      (configVector (extendConfig F c))) (extendConfig F c)
  rw [matrixUnit_apply, matrixUnit_configVector]
  have hext : extendConfig F (e c) = (extendConfig F c).update x
      (Equiv.swap a b (c ⟨x,hx⟩)) := extendConfig_perm _ _ _
  have hcx : extendConfig F c x = c ⟨x,hx⟩ := by simp [hx]
  rw [hext]
  simp only [Finsupp.update_apply, ite_true, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, hcx]
  by_cases hc : c ⟨x,hx⟩ = b
  · simp only [hc, ite_true, Equiv.swap_apply_right, Finsupp.update_idem]
    rw [← hc, ← hcx, Finsupp.update_self]
  · simp only [hc, ite_false, map_zero, lp.coeFn_zero, Pi.zero_apply]

theorem cyclic_adjoin {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]
    [StarRing E] [StarModule ℂ E] (φ : E →L[ℂ] ℂ) (s : Set E)
    (h : ∀ a ∈ s, (∀ b, φ (a*b) = φ (b*a)) ∧
      (∀ b, φ (star a*b) = φ (b*star a)))
    {a : E} (ha : a ∈ StarAlgebra.adjoin ℂ s) :
    (∀ b, φ (a*b) = φ (b*a)) ∧ (∀ b, φ (star a*b) = φ (b*star a)) := by
  let P : E → Prop := fun a => ∀ b, φ (a*b) = φ (b*a)
  have mulP (a c : E) (ha : P a) (hc : P c) : P (a*c) := by
    intro b
    calc
      φ ((a*c)*b) = φ (a*(c*b)) := by rw [mul_assoc]
      _ = φ ((c*b)*a) := ha _
      _ = φ (c*(b*a)) := by rw [mul_assoc]
      _ = φ ((b*a)*c) := hc _
      _ = φ (b*(a*c)) := by rw [mul_assoc]
  have addP (a c : E) (ha : P a) (hc : P c) : P (a+c) := by
    intro b
    simp only [add_mul, mul_add, map_add, ha b, hc b]
  change P a ∧ P (star a)
  induction ha using StarAlgebra.adjoin_induction with
  | mem a ha => exact h a ha
  | algebraMap z =>
    constructor <;> intro b <;>
      simp [Algebra.algebraMap_eq_smul_one]
  | add a c ha hc iha ihc =>
    exact ⟨addP a c iha.1 ihc.1, by rw [star_add]; exact addP _ _ iha.2 ihc.2⟩
  | mul a c ha hc iha ihc =>
    exact ⟨mulP a c iha.1 ihc.1, by rw [star_mul]; exact mulP _ _ ihc.2 iha.2⟩
  | star a ha iha => exact ⟨iha.2, by simpa only [star_star] using iha.1⟩

theorem cyclic_of_cyclic_units {d ℓ : ℕ} (φ : QuasiLocal d ℓ →L[ℂ] ℂ)
    (h : ∀ x a b A, φ (localUnit d ℓ x a b * A) = φ (A * localUnit d ℓ x a b)) :
    ∀ A B, φ (A*B) = φ (B*A) := by
  intro A B
  have hd : DenseRange ((↑) : localCore d ℓ → QuasiLocal d ℓ) :=
    denseRange_subtype_val.mpr (localCore_dense d ℓ)
  refine hd.induction_on (p := fun C => φ (C*B) = φ (B*C)) A ?_ ?_
  · exact isClosed_eq (φ.continuous.comp (continuous_id.mul continuous_const))
      (φ.continuous.comp (continuous_const.mul continuous_id))
  · intro a
    apply (cyclic_adjoin φ _ ?_ a.property).1
    rintro C ⟨x,a,b,rfl⟩
    exact ⟨h x a b, by simpa only [star_localUnit] using h x b a⟩

theorem exists_tracial_state (d ℓ : ℕ) :
    ∃ τ : State d ℓ, ∀ A B, τ.functional (A*B) = τ.functional (B*A) := by
  obtain ⟨τ,κ,hκ,hlim⟩ := state_subsequence (fun n => finiteTraceState d ℓ (box d n))
  refine ⟨τ, cyclic_of_cyclic_units τ.functional ?_⟩
  intro x a b A
  have he : ∀ᶠ n : ℕ in Filter.atTop,
      (finiteTraceState d ℓ (box d (κ n))).functional (localUnit d ℓ x a b*A) =
      (finiteTraceState d ℓ (box d (κ n))).functional (A*localUnit d ℓ x a b) := by
    filter_upwards [hκ.tendsto_atTop.eventually (eventually_mem_box x)] with n hn
    exact finiteTraceFunctional_cyclic_unit _ hn a b A
  exact tendsto_nhds_unique (hlim _) ((hlim _).congr' (Filter.EventuallyEq.symm he))

theorem positive_norm_le_four_one {E : Type*} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (φ : E →L[ℂ] ℂ)
    (hpos : ∀ B, 0 ≤ φ (star B * B)) : ‖φ‖ ≤ 4 * ‖φ 1‖ := by
  have hp : ∀ A : E, 0 ≤ A → 0 ≤ φ A := by
    intro A hA
    obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
    exact hpos B
  let f : E →ₚ[ℂ] ℂ :=
    { φ.toLinearMap with
      monotone' := by
        intro A B h
        change φ A ≤ φ B
        have h' := hp (B - A) (sub_nonneg.mpr h)
        simpa only [map_sub, sub_nonneg] using h' }
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro A
  obtain ⟨x, hx, hnorm, hA⟩ := CStarAlgebra.exists_sum_four_nonneg A
  conv_lhs => rw [hA, map_sum]
  calc
    ‖∑ i : Fin 4, φ (Complex.I ^ (i : ℕ) • x i)‖ ≤
        ∑ i : Fin 4, ‖φ (Complex.I ^ (i : ℕ) • x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖φ 1‖ * ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
      exact (PositiveLinearMap.norm_apply_le_of_nonneg f (x i) (hx i)).trans
        (mul_le_mul_of_nonneg_left (hnorm i) (norm_nonneg _))
    _ = (4 * ‖φ 1‖) * ‖A‖ := by simp; ring

def sandwichFunctional {E : Type*} [CStarAlgebra E] (φ : E →L[ℂ] ℂ) (B : E) :
    E →L[ℂ] ℂ := φ.comp (ContinuousLinearMap.mulLeftRight ℂ E (star B) B)

@[simp] theorem sandwichFunctional_apply {E : Type*} [CStarAlgebra E]
    (φ : E →L[ℂ] ℂ) (B A : E) : sandwichFunctional φ B A = φ (star B * A * B) := rfl

theorem sandwichFunctional_positive {E : Type*} [CStarAlgebra E]
    (φ : E →L[ℂ] ℂ) (hpos : ∀ B, 0 ≤ φ (star B * B)) (B A : E) :
    0 ≤ sandwichFunctional φ B (star A*A) := by
  simpa only [sandwichFunctional_apply, star_mul, mul_assoc] using hpos (A*B)

theorem sandwich_one_pos {E : Type*} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (φ : E →L[ℂ] ℂ) (hn : φ 1 = 1)
    (hpos : ∀ B, 0 ≤ φ (star B * B)) {B : E} (hB : IsUnit B) :
    0 < (sandwichFunctional φ B 1).re := by
  have hp := hpos B
  simp only [sandwichFunctional_apply, mul_one]
  apply lt_of_le_of_ne hp.1
  intro hz
  have hzero : φ (star B * B) = 0 := by
    apply Complex.ext
    · exact hz.symm
    · exact hp.2.symm
  have hnorm := positive_norm_le_four_one (sandwichFunctional φ B)
    (sandwichFunctional_positive φ hpos B)
  have hzfun : sandwichFunctional φ B = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [sandwichFunctional_apply, mul_one, hzero, norm_zero, mul_zero] using hnorm
  obtain ⟨u, rfl⟩ := hB
  have hh := congrArg (fun f : E →L[ℂ] ℂ => f (star (↑u⁻¹ : E) * (↑u⁻¹ : E))) hzfun
  simp only [sandwichFunctional_apply, zero_apply] at hh
  have hc : star (↑u : E) * (star (↑u⁻¹ : E) * (↑u⁻¹ : E)) * ↑u = 1 := by
    calc
      _ = star ((↑u⁻¹ : E) * ↑u) * ((↑u⁻¹ : E) * ↑u) := by rw [star_mul]; simp only [mul_assoc]
      _ = 1 := by simp
  rw [hc, hn] at hh
  exact one_ne_zero hh

def sandwichState {d ℓ : ℕ} (ω : State d ℓ) (B : QuasiLocal d ℓ) (hB : IsUnit B) :
    State d ℓ := by
  let : PartialOrder (QuasiLocal d ℓ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (QuasiLocal d ℓ) := CStarAlgebra.spectralOrderedRing _
  have hp : ∀ C, 0 ≤ ω.functional (star C * C) :=
    fun C => ⟨(ω.positive C).2, by simpa using (ω.positive C).1.symm⟩
  have hZ := sandwich_one_pos ω.functional ω.normalized hp hB
  let Z := (sandwichFunctional ω.functional B 1).re
  refine ⟨((Z : ℂ)⁻¹) • sandwichFunctional ω.functional B, ?_, ?_⟩
  · change (Z : ℂ)⁻¹ * sandwichFunctional ω.functional B 1 = 1
    have hz : sandwichFunctional ω.functional B 1 = (Z : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [sandwichFunctional_apply, mul_one, Complex.ofReal_im] using (ω.positive B).1
    rw [hz]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hZ))
  · intro A
    change (((Z : ℂ)⁻¹) * sandwichFunctional ω.functional B (star A*A)).im = 0 ∧ _
    have hA := sandwichFunctional_positive ω.functional hp B A
    have hi : 0 ≤ ((Z : ℂ)⁻¹) := by
      rw [← Complex.ofReal_inv]
      exact ⟨le_of_lt (inv_pos.mpr hZ), by simp⟩
    have hh := mul_nonneg hi hA
    exact ⟨hh.2.symm, hh.1⟩

def gibbsDensity {d ℓ : ℕ} (K : QuasiLocal d ℓ) (β : ℝ) : QuasiLocal d ℓ :=
  NormedSpace.exp (((-β : ℝ) : ℂ) • K)

def gibbsHalf {d ℓ : ℕ} (K : QuasiLocal d ℓ) (β : ℝ) : QuasiLocal d ℓ :=
  NormedSpace.exp (((-β/2 : ℝ) : ℂ) • K)

lemma star_gibbsHalf {d ℓ : ℕ} {K : QuasiLocal d ℓ} (hK : IsSelfAdjoint K) (β : ℝ) :
    star (gibbsHalf K β) = gibbsHalf K β := by
  rw [gibbsHalf, NormedSpace.star_exp, star_smul, hK]
  simp

lemma gibbsHalf_sq {d ℓ : ℕ} (K : QuasiLocal d ℓ) (β : ℝ) :
    gibbsHalf K β * gibbsHalf K β = gibbsDensity K β := by
  unfold gibbsHalf gibbsDensity
  rw [← NormedSpace.exp_add_of_commute (Commute.refl _), ← add_smul]
  congr 2
  push_cast
  ring

def gibbsState {d ℓ : ℕ} (τ : State d ℓ) (K : QuasiLocal d ℓ) (β : ℝ) : State d ℓ :=
  sandwichState τ (gibbsHalf K β) (NormedSpace.isUnit_exp _)

theorem gibbs_normalization_pos {d ℓ : ℕ} (τ : State d ℓ) {K : QuasiLocal d ℓ}
    (hK : IsSelfAdjoint K) (β : ℝ) : 0 < (τ.functional (gibbsDensity K β)).re := by
  let : PartialOrder (QuasiLocal d ℓ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (QuasiLocal d ℓ) := CStarAlgebra.spectralOrderedRing _
  have hp : ∀ C, 0 ≤ τ.functional (star C*C) :=
    fun C => ⟨(τ.positive C).2, by simpa using (τ.positive C).1.symm⟩
  have h := sandwich_one_pos τ.functional τ.normalized hp
    (NormedSpace.isUnit_exp (((-β/2 : ℝ) : ℂ) • K))
  change 0 < (τ.functional (star (gibbsHalf K β) * gibbsHalf K β)).re at h
  simpa only [star_gibbsHalf hK, gibbsHalf_sq] using h

theorem gibbsState_apply {d ℓ : ℕ} (τ : State d ℓ)
    (hτ : ∀ A B, τ.functional (A*B) = τ.functional (B*A))
    {K : QuasiLocal d ℓ} (hK : IsSelfAdjoint K) (β : ℝ) (A : QuasiLocal d ℓ) :
    (gibbsState τ K β).functional A =
      ((τ.functional (gibbsDensity K β)).re : ℂ)⁻¹ *
        τ.functional (gibbsDensity K β * A) := by
  change ((sandwichFunctional τ.functional (gibbsHalf K β) 1).re : ℂ)⁻¹ *
    sandwichFunctional τ.functional (gibbsHalf K β) A = _
  simp only [sandwichFunctional_apply, mul_one, star_gibbsHalf hK, gibbsHalf_sq]
  congr 1
  rw [hτ (_*A), ← mul_assoc, gibbsHalf_sq]

theorem exists_gibbs_states (d ℓ : ℕ) :
    ∃ τ : State d ℓ, (∀ A B, τ.functional (A*B) = τ.functional (B*A)) ∧
      ∀ (K : QuasiLocal d ℓ), IsSelfAdjoint K → ∀ β : ℝ,
        0 < (τ.functional (gibbsDensity K β)).re ∧
        ∃ ω : State d ℓ, ∀ A, ω.functional A =
          ((τ.functional (gibbsDensity K β)).re : ℂ)⁻¹ *
            τ.functional (gibbsDensity K β*A) := by
  obtain ⟨τ,hτ⟩ := exists_tracial_state d ℓ
  refine ⟨τ,hτ,fun K hK β => ⟨gibbs_normalization_pos τ hK β, gibbsState τ K β, ?_⟩⟩
  exact gibbsState_apply τ hτ hK β

end Heisenberg
end

end OAI
