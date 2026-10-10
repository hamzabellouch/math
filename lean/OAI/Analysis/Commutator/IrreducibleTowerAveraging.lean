import Mathlib
import OAI.Analysis.Commutator.NormalRelativeCommutant
import OAI.Analysis.Commutator.MatrixExpectationNested

namespace OAI

noncomputable section

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.IrreducibleTowerAveraging

open TracialGNS NormalGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ}, n ≤ m → (stage n).range ≤ (stage m).range)

def stageUnitaries : Submonoid (unitary M) where
  carrier := {u | ∃ n, (u:M) ∈ (stage n).range}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro u v ⟨n,hn⟩ ⟨m,hm⟩
    exact ⟨max n m, (stage (max n m)).range.mul_mem
      (hmono (Nat.le_max_left _ _) hn) (hmono (Nat.le_max_right _ _) hm)⟩

def orbit (a : M) : Set τ.GNS :=
  Set.range (fun u : stageUnitaries M stage hmono =>
    algebraVector τ ((u.val:M)*a*star (u.val:M)))

omit [∀ n, Nonempty (ι n)] in
lemma orbit_self (a : M) : algebraVector τ a ∈ orbit M τ stage hmono a := by
  refine ⟨1,?_⟩
  simp

omit [∀ n, Nonempty (ι n)] in
lemma conjugation_orbit (a : M) (u : stageUnitaries M stage hmono) :
    ∀ x∈orbit M τ stage hmono a,
      conjugation τ hτ u.val x∈orbit M τ stage hmono a := by
  rintro x ⟨v,rfl⟩
  refine ⟨u*v,?_⟩
  simp only [algebraVector_apply,conjugation_coe,Submonoid.coe_mul,
    star_mul,mul_assoc]

omit [∀ n, Nonempty (ι n)] in
lemma hull_bounded (hnormal : BoundedWOTContinuous M τ) (a : M) (ha : ‖a‖≤1) :
    closedConvexHull ℝ (orbit M τ stage hmono a) ⊆
      {x : τ.GNS | ∃ b : M, ‖b‖≤1 ∧ algebraVector τ b=x} := by
  apply closedConvexHull_min _ (NormalRelativeCommutant.vector_unitball_convex M τ)
    (vector_unitball_isClosed M τ hnormal)
  rintro x ⟨u,rfl⟩
  refine ⟨(u.val:M)*a*star (u.val:M),?_,rfl⟩
  have hn : ‖(u.val:M)*a*star (u.val:M)‖=‖a‖ := by
    exact (CStarRing.norm_mul_coe_unitary _ (star u.val)).trans
      (CStarRing.norm_coe_unitary_mul u.val a)
  rwa [hn]

include hτ in
omit [∀ n, Nonempty (ι n)] in
lemma hull_trace (a : M) :
    ∀ x∈closedConvexHull ℝ (orbit M τ stage hmono a), inner ℂ (vacuum τ) x=τ a := by
  apply closedConvexHull_min
  · rintro x ⟨u,rfl⟩
    change inner ℂ (vacuum τ) (algebraVector τ ((u.val:M)*a*star (u.val:M)))=τ a
    rw [inner_vacuum_algebraVector,hτ,←mul_assoc]
    rw [u.val.property.1,one_mul]
  · exact (convex_singleton (τ a)).linear_preimage
      ((innerSL ℂ (vacuum τ)).toLinearMap.restrictScalars ℝ)
  · exact isClosed_eq (continuous_const.inner continuous_id) continuous_const

include hτ in
omit [∀ n, Nonempty (ι n)] in
theorem scalar_mem_hull
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
      ∃ c : ℂ, b=algebraMap ℂ M c)
    (a : M) (ha : ‖a‖≤1) :
    (τ a) • vacuum τ ∈ closedConvexHull ℝ (orbit M τ stage hmono a) := by
  obtain ⟨z,hz,hfix⟩ := ConvexIsometry.exists_fixed
    (closedConvexHull ℝ (orbit M τ stage hmono a))
    ⟨algebraVector τ a,subset_closedConvexHull (orbit_self M τ stage hmono a)⟩
    isClosed_closedConvexHull convex_closedConvexHull
  obtain ⟨b,_,hb⟩ := hull_bounded M τ stage hmono hnormal a ha hz
  have hcomm (n : ℕ) (x : Matrix (ι n) (ι n) ℂ) : stage n x*b=b*stage n x := by
    apply NormalRelativeCommutant.commutes_of_fixed M τ hτ (stage n) b hfaith _ x
    intro u
    let v : stageUnitaries M stage hmono :=
      ⟨NormalRelativeCommutant.liftedUnitary M (stage n) u, n, ⟨u,rfl⟩⟩
    rw [hb]
    exact hfix _ (ConvexIsometry.maps_closedConvexHull _ _
      (conjugation_orbit M τ hτ stage hmono a v))
  obtain ⟨c,hc⟩ := hirr b hcomm
  have htc : τ b=c := by
    rw [hc,Algebra.algebraMap_eq_smul_one,map_smul,hone,smul_eq_mul,mul_one]
  have hta : τ b=τ a := by
    rw [←inner_vacuum_algebraVector,hb]
    exact hull_trace M τ hτ stage hmono a z hz
  have hz' : z=(τ a) • vacuum τ := by
    rw [←hb,hc,Algebra.algebraMap_eq_smul_one,map_smul,←hta,htc]
    rfl
  rwa [hz'] at hz

section SingleStage

variable {A I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (ρ : A →ₚ[ℂ] ℂ)
  (hρ : ∀ a b : A, ρ (a*b)=ρ (b*a))

include hρ in
omit [Nonempty I] in
lemma vector_expectation_conjugation (u : unitary A) (hu : (u:A)∈φ.range) (a : A) :
    algebraVector ρ (expectation φ ((u:A)*a*star (u:A)))=
      algebraVector ρ (expectation φ a) := by
  apply (algebraVector_dense ρ).eq_of_inner_left ℂ
  intro b
  rw [inner_symm φ ρ hρ,inner_symm φ ρ hρ,inner_algebraVector,inner_algebraVector]
  obtain ⟨v,hv⟩ := hu
  change φ v=(u:A) at hv
  have hc : (u:A)*expectation φ b=expectation φ b*(u:A) := by
    rw [←hv]
    exact commutes φ b v
  simp only [star_mul,star_star]
  have he : star (u:A)*expectation φ b*(u:A)=expectation φ b := by
    rw [mul_assoc,←hc,←mul_assoc,u.property.1,one_mul]
  calc
    _ = ρ ((u:A)*(star a*(star (u:A)*expectation φ b))) := by
      simp only [mul_assoc]
    _ = ρ ((star a*(star (u:A)*expectation φ b))*(u:A)) := hρ _ _
    _ = ρ (star a*(star (u:A)*expectation φ b*(u:A))) := by
      simp only [mul_assoc]
    _ = _ := by rw [he]

end SingleStage

def eventualFiber (a : M) : Set τ.GNS :=
  {v | ∃ b : M, algebraVector τ b=v ∧ ∀ᶠ n in atTop,
    algebraVector τ (expectation (stage n) b)=algebraVector τ (expectation (stage n) a)}

omit [∀ n, Nonempty (ι n)] in
lemma eventualFiber_convex (a : M) : Convex ℝ (eventualFiber M τ stage a) := by
  rintro x ⟨b,rfl,hb⟩ y ⟨c,rfl,hc⟩ r s _ _ hrs
  have hvec (t : ℝ) (d : M) :
      algebraVector τ (t • d) = t • algebraVector τ d := by
    rw [← Complex.coe_smul, (algebraVector τ).map_smul, Complex.coe_smul]
  have hexp (n : ℕ) (t : ℝ) (d : M) :
      expectation (stage n) (t • d) = t • expectation (stage n) d := by
    rw [← Complex.coe_smul, (expectation (stage n)).map_smul, Complex.coe_smul]
  refine ⟨r • b+s • c,?_,?_⟩
  · simp only [map_add, hvec]
  · filter_upwards [hb,hc] with n hn kn
    simp only [map_add, hexp, hvec, hn, kn, ←add_smul, hrs, one_smul]

include hτ in
omit [∀ n, Nonempty (ι n)] in
lemma orbit_subset_eventualFiber (a : M) :
    orbit M τ stage hmono a ⊆ eventualFiber M τ stage a := by
  rintro x ⟨u,rfl⟩
  refine ⟨(u.val:M)*a*star (u.val:M),rfl,?_⟩
  obtain ⟨N,hN⟩ := u.property
  filter_upwards [eventually_ge_atTop N] with n hn
  exact vector_expectation_conjugation (stage n) τ hτ u.val (hmono hn hN) a

include hτ hmono in
theorem expectation_tendsto
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
      ∃ c : ℂ, b=algebraMap ℂ M c)
    (a : M) (ha : ‖a‖≤1) :
    Tendsto (fun n => algebraVector τ (expectation (stage n) a)) atTop
      (𝓝 ((τ a) • vacuum τ)) := by
  have hh := scalar_mem_hull M τ hτ stage hmono hnormal hfaith hone hirr a ha
  rw [closedConvexHull_eq_closure_convexHull] at hh
  have hf : convexHull ℝ (orbit M τ stage hmono a) ⊆ eventualFiber M τ stage a :=
    convexHull_min (orbit_subset_eventualFiber M τ hτ stage hmono a)
      (eventualFiber_convex M τ stage a)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨v,hv,hd⟩ := Metric.mem_closure_iff.mp hh ε hε
  obtain ⟨b,hb,hba⟩ := hf hv
  filter_upwards [hba] with n hn
  rw [dist_comm] at hd
  have hvac : algebraVector τ ((τ a) • (1:M)) = (τ a) • vacuum τ :=
    (algebraVector τ).map_smul (τ a) 1
  have hsub : algebraVector τ (b-(τ a) • (1:M)) =
      algebraVector τ b - (τ a) • vacuum τ := by
    rw [(algebraVector τ).map_sub b ((τ a) • (1:M)), hvac]
  have hsmall : ‖algebraVector τ (b-(τ a) • (1:M))‖<ε := by
    simpa only [dist_eq_norm, hsub, hb] using hd
  have he : algebraVector τ (expectation (stage n) (b-(τ a) • (1:M)))=
      algebraVector τ (expectation (stage n) a)-(τ a) • vacuum τ := by
    have hexp : expectation (stage n) (b-(τ a) • (1:M)) =
        expectation (stage n) b - (τ a) • (1:M) :=
      ((expectation (stage n)).map_sub b ((τ a) • (1:M))).trans
        (congrArg (fun d : M => expectation (stage n) b - d)
          (fixes_scalar (stage n) (τ a)))
    have hvec : algebraVector τ (expectation (stage n) b - (τ a) • (1:M)) =
        algebraVector τ (expectation (stage n) b) - (τ a) • vacuum τ :=
      ((algebraVector τ).map_sub (expectation (stage n) b) ((τ a) • (1:M))).trans
        (congrArg (fun v : τ.GNS => algebraVector τ (expectation (stage n) b) - v) hvac)
    exact (congrArg (algebraVector τ) hexp).trans
      (hvec.trans (congrArg (fun v : τ.GNS => v - (τ a) • vacuum τ) hn))
  rw [dist_eq_norm,←he]
  exact (norm_vector_le (stage n) τ hτ _).trans_lt hsmall

include hτ hmono in
theorem expectation_tendsto_any
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
      ∃ c : ℂ, b=algebraMap ℂ M c)
    (a : M) :
    Tendsto (fun n => algebraVector τ (expectation (stage n) a)) atTop
      (𝓝 ((τ a) • vacuum τ)) := by
  let c : ℝ := ‖a‖+1
  have hc : 0<c := by dsimp [c]; positivity
  have hci : 0≤c⁻¹ := le_of_lt (inv_pos.mpr hc)
  have hb : ‖c⁻¹ • a‖≤1 := by
    rw [norm_smul,Real.norm_of_nonneg hci]
    exact (inv_mul_le_one₀ hc).mpr (by dsimp [c]; linarith)
  have h := expectation_tendsto M τ hτ stage hmono hnormal hfaith hone hirr
    (c⁻¹ • a) hb
  have h' := tendsto_const_nhds.smul h (c:=c)
  simpa only [LinearMap.map_smul_of_tower,PositiveLinearMap.map_smul_of_tower,
    ←smul_assoc,smul_smul,smul_eq_mul,mul_inv_cancel₀ (ne_of_gt hc),one_smul] using h'

end Kadison.IrreducibleTowerAveraging

end

end OAI
